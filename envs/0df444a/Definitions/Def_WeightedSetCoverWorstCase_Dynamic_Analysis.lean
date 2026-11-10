-- Prove2me | Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Analysis
-- name    : WeightedSetCoverWorstCase_Dynamic_Analysis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:29:28.597651+00:00
-- url     : https://prove2.me/theorems/7e3d3a90-4a35-46a6-9843-e1a602128061
-- title:
--   Analysis objects: time-unit indices, ADV, switch domains, critical events and synthetic levels
-- statement:
--   Objects read off a run $(c,ev)$; the algorithm does not maintain them. `unitIdx ev N` is the number of time units completed by events $0..N$ (the index $t$ of the unit ending at $N$). `advCount ev a b` $=|\mathrm{ADV}|$ for the updates among events $a+1..b$. `RunningIn st r`: the thread with identity $r$ is in the pool.
--
--   For a thread $T_k$ about to terminate, $\mathrm{Switch}^B_k=((U^B_k)^-\setminus(\mathrm{Supp}^B_k)^-)\cap(U^F_{\le k})^-$ (`switchSet`), with its $i$-active/passive parts w.r.t. the buffer levels (`bufActle`, `bufPassle`).
--
--   §12.1 at a fixed time unit $t$ ending at event $N_t$: the critical threads are those running at $t$; $T_{k_1}$ the highest, activated at event $A_1$; $p_{\mathrm{uni}}$ after an event is the synchronization pointer of the lowest critical thread then running; $\tau^\star(q)$ (`tauStar`) is the first event of $[A_1,N_t]$ after which $p_{\mathrm{uni}}\le q$; $X^\star(q)$ (`xStar`) is the initial domain of the thread activated there, or the unfrozen set just after the greedy selection there. The synthetic level $\ell^B(e)$ (`synLevel`) is (12.13) for elements frozen by a critical thread at $t$ (the pointer of the critical thread that froze it first, kept through later ownership changes), (12.14) for elements of $(\neg\mathrm{Fr}^B_{k_1})^t$ frozen by none (the pointer at $t$ of the lowest critical thread with $e$ unfrozen).
--
--   **Formalization Note.** Where the paper leaves $\ell^B$ undefined, `synLevel` is $L+1$, and `xStar` is $\emptyset$ when $\tau^\star(q)$ is undefined.
--
--   `EndUnit c ev N` marks the scheduler check immediately after a unit, including termination of an exhausted thread (Algorithm 9, lines 11–13). Its post-state is the completed-unit snapshot. The preceding `crit true` counts the unit; it is not the observation boundary. Thus finished tail threads are absent from the critical pool, as required in the proof of Claim 12.10 (PDF 62).
-- source:
--   Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), Fully Dynamic Weighted Set Cover: Worst-Case Recourse and Update Time, STOC 2027 submission, supplied PDF sha256 28a86be41fbea2451c118c89c7385500105ced4b59ab5e66110721ebf0909337, §8 notation p. 33 (PDF 36); §10.1 p. 39 (PDF 42); §11 notation p. 45 (PDF 48); §12.1 pp. 51–53 (PDF 54–56)

import Mathlib
import Definitions.Def_DynSetCover_Instance
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Problem
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Algorithm

namespace WeightedSetCoverWorstCase.Dynamic

/-!
# Analysis objects: time units, `ADV`, switch domains, critical events, synthetic levels

Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), §8 notation p. 33 (PDF 36), §10.1 p. 39
(PDF 42), §11 notation p. 45 (PDF 48), §12.1 pp. 51–53 (PDF 54–56).

All objects are read off a run `(c, ev)` of the algorithm (`IsRun`): `c i` is the state before event
`i`, `c (i+1)` the state just after it. The event `crit true` finishes the critical work of a time unit. The completed-unit snapshot
is taken after the following termination check (Algorithm 9, lines 11–13), including immediate
termination of an exhausted thread, and before the next activation. This is the convention used
in §12.1 and the tail case of the proof of Claim 12.10 (PDF 62).
None of these objects is maintained by the algorithm.
-/

variable {inst : Instance}

/-- Event `N` completes the scheduler check following a time unit. Its post-state is the
completed-unit snapshot: an exhausted active thread has already terminated. -/
def EndUnit (c : ℕ → AlgState inst) (ev : ℕ → Ev) (N : ℕ) : Prop :=
  (∃ count, (c N).mode = .check count) ∧ (ev N = .terminate ∨ ev N = .control)

/-- The number of time units whose critical work has finished by events `0, …, N`.
At an `EndUnit c ev N` boundary this is the index of the completed unit. -/
def unitIdx (ev : ℕ → Ev) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter fun i => ev i = .crit true).card

/-- `|ADV[a, b]|`: the number of adversarial updates among the events `a+1, …, b` (with
multiplicity: every update is one event). -/
def advCount (ev : ℕ → Ev) (a b : ℕ) : ℕ :=
  ((Finset.Ioc a b).filter fun i => ev i = .update).card

/-- The thread with identity `r` is running (active or suspended) in the state `st`. -/
def RunningIn (st : AlgState inst) (r : ℕ) : Prop := ∃ T ∈ st.pool, T.tid = r

namespace Thread

variable {m : ℕ} (T : Thread m)

/-- Elements of `X` of buffer level `≤ i`, w.r.t. `(ℓ^B_k, ℘ℓ^B_k)`. -/
def bufUle (X : Finset ℕ) (i : ℕ) : Finset ℕ := X.filter fun v => T.lvl v ≤ i

/-- `i`-active elements of `X` w.r.t. the buffer levels: `ℓ^B_k(e) ≤ i < ℘ℓ^B_k(e)`. -/
def bufActle (X : Finset ℕ) (i : ℕ) : Finset ℕ := X.filter fun v => T.lvl v ≤ i ∧ i < T.plvl v

/-- `i`-passive elements of `X` w.r.t. the buffer levels. -/
def bufPassle (X : Finset ℕ) (i : ℕ) : Finset ℕ := T.bufUle X i \ T.bufActle X i

end Thread

/-- `Switch^B_k = ((U^B_k)⁻ ∖ (Supp^B_k)⁻) ∩ (U^F_{≤k})⁻` for the thread `T = T_k` in the state `st`
immediately before its termination (§11, p. 45). -/
def switchSet (st : AlgState inst) (T : Thread inst.m) : Finset ℕ :=
  (T.U \ T.supp) ∩ st.fgUle T.idx

section Critical

/-!
## The extended background solution at a fixed time unit (§12.1)

Fix a run `(c, ev)` and an event `Nt` ending a time unit `t` (state `c (Nt+1)`). The critical
threads are the threads running at `t`. `T_{k₁}` is the highest of them; `A₁` is the event that
activated it. For an event `i ∈ [A₁, Nt]`, `p_uni` after `i` is the synchronization pointer of the
lowest critical thread running just after `i`. `τ⋆(q)` is the first event in `[A₁, Nt]` after which
`p_uni ≤ q` (a drop by activation or by greedy); `j⋆(q)` is then the active thread just after it,
and `X⋆(q)` is its initial domain `U^B_{j⋆(q)}` (drop by activation) or its unfrozen set just after
the greedy selection (drop by greedy).
-/

variable (c : ℕ → AlgState inst) (ev : ℕ → Ev) (Nt : ℕ)

/-- The identities of the critical threads (running at the end of time unit `t`). -/
def critTids : List ℕ := (c (Nt + 1)).pool.map fun T => T.tid

/-- The critical threads running in the state `st`, in increasing index order. -/
def critIn (st : AlgState inst) : List (Thread inst.m) :=
  st.pool.filter fun T => decide (T.tid ∈ critTids c Nt)

/-- The highest critical thread `T_{k₁}`. -/
def topCrit : Option (Thread inst.m) := (c (Nt + 1)).pool.getLast?

/-- Event `i` activates the thread with identity `r`. -/
def ActivatesAt (r i : ℕ) : Prop :=
  ev i = .activate ∧ (c (i + 1)).pool.head?.map (fun T => T.tid) = some r

open Classical in
/-- `A₁`: the event activating `T_{k₁}`. -/
noncomputable def actFirst : Option ℕ :=
  match topCrit c Nt with
  | none => none
  | some T => if h : ∃ i, ActivatesAt c ev T.tid i then some (Nat.find h) else none

/-- `p_uni` just after event `i`: the synchronization pointer of the lowest critical thread
running then. -/
def puniAfter (i : ℕ) : Option ℕ := (critIn c Nt (c (i + 1))).head?.map fun T => T.p

open Classical in
/-- `τ⋆(q)`: the first event of `[A₁, Nt]` after which `p_uni ≤ q`, if any. -/
noncomputable def tauStar (q : ℕ) : Option ℕ :=
  match actFirst c ev Nt with
  | none => none
  | some A₁ =>
    if h : ∃ i, A₁ ≤ i ∧ i ≤ Nt ∧ ∃ p, puniAfter c Nt i = some p ∧ p ≤ q then some (Nat.find h)
    else none

/-- `X⋆(q)` (empty when `τ⋆(q)` is undefined). -/
noncomputable def xStar (q : ℕ) : Finset ℕ :=
  match tauStar c ev Nt q with
  | none => ∅
  | some τ =>
    match (c (τ + 1)).pool with
    | T :: _ => if ev τ = .activate then T.U else if ev τ = .select then T.unfrozen else ∅
    | [] => ∅

/-- `v` is frozen by some critical thread in the state `st`. -/
def FrozenCrit (st : AlgState inst) (v : ℕ) : Prop := ∃ T ∈ critIn c Nt st, v ∈ T.fr

open Classical in
/-- The synthetic level `ℓ^B(e)` of (12.13)–(12.14). For `e ∈ Fr^t_all` (frozen by a critical thread
at `t`): the synchronization pointer, just after the first event after which `e` is frozen by a
critical thread, of the (lowest) critical thread freezing it. For `e ∈ (¬Fr^B_{k₁})^t ∖ Fr^t_all`:
the pointer at `t` of the lowest critical thread with `e` unfrozen. Otherwise (where the paper leaves
`ℓ^B` undefined) the value `L + 1`. -/
noncomputable def synLevel (ε : ℝ) (v : ℕ) : ℕ :=
  if hv : FrozenCrit c Nt (c (Nt + 1)) v then
    have h : ∃ i, i ≤ Nt ∧ FrozenCrit c Nt (c (i + 1)) v := ⟨Nt, le_rfl, hv⟩
    match (critIn c Nt (c (Nat.find h + 1))).find? (fun T => decide (v ∈ T.fr)) with
    | some T => T.p
    | none => Lpar inst ε + 1
  else
    match topCrit c Nt with
    | some T₁ =>
      if v ∈ T₁.unfrozen then
        match (critIn c Nt (c (Nt + 1))).find? (fun T => decide (v ∈ T.unfrozen)) with
        | some T => T.p
        | none => Lpar inst ε + 1
      else Lpar inst ε + 1
    | none => Lpar inst ε + 1

end Critical

end WeightedSetCoverWorstCase.Dynamic


