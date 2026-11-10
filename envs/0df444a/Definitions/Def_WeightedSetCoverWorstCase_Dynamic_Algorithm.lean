-- Prove2me | Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Algorithm
-- name    : WeightedSetCoverWorstCase_Dynamic_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:28:36.698636+00:00
-- url     : https://prove2.me/theorems/5bbd5fa8-72ea-4247-aca2-139b69bda1e4
-- title:
--   The algorithm of Part II: foreground, threads, Algorithms 1–9 as a transition relation
-- statement:
--   The state (`AlgState`) holds the **foreground** $(U^F,\ell^F,\wp\ell^F,C^F,\mathrm{cov}^F)$, the **thread pool** in increasing index order (the head is the active thread, the others suspended), the alive versions, the base element of each version, and the control state of Algorithm 9 and the updates still to come. A **thread** $T_k$ carries its domain $U^B_k=\mathrm{Fr}^B_k\sqcup\neg\mathrm{Fr}^B_k$, supported elements $\mathrm{Supp}^B_k$, buffer copies $C^B_k$, buffer levels and passive levels, pointers $p_k,g_k$, the elements not yet scanned by preprocessing (preprocessing phase iff nonempty), the coverage of its current greedy copy, its index and a serial identity `tid`. Versions are natural numbers in insertion order (every reinsertion is a new version).
--
--   `Step ε st ev st'` is one event, exactly as on pp. 25–32: Algorithm 5 (`insertOp`, with a cheapest set $s_e$ and $i_e=\lfloor\log_{1+\varepsilon}(1/c_{s_e})\rfloor$, processing threads from the highest index down) or Algorithm 6 (`deleteOp`) when idle, consuming the next update and setting count $=\lceil\sigma\rceil$; the loop of Algorithm 9: activation of the largest dirty $k<j$ unless the active thread is in its tail (Algorithms 7 and 1), a time unit on the active thread (Algorithm 8: one critical operation, or all remaining ones in a tail $1\le|\neg\mathrm{Fr}_k|\le10/\varepsilon$), termination when $\neg\mathrm{Fr}_k=\emptyset$ (Algorithm 4), and the exit when count $=0$ and the active thread is not in its tail. Critical operations are a preprocessing scan (Algorithm 2) and the freezing of one element of the current greedy copy (Algorithm 3); a greedy selection is its own event. The foreground removal rule (a copy of $C^F$ whose coverage elements are all dead or frozen by some thread is removed) runs after every freezing and deletion. All choices the paper leaves free are free in the relation. Costs are the normalized `ncost`.
--
--   `IsRun inst ε ups c ev`: $c_0$ is the empty state with input `ups` (updates of base elements, from the empty live set) and every $c_i\to c_{i+1}$ is a `Step` with event `ev i`. The output is $C^F+C^B$ (`outCopies`); `optAlive` is the minimum cost (original costs) of a cover of the alive base elements.
--
--   **Formalization Note.** A defensive constructor `unitDone` makes the relation total; it fires only in states where a time unit has nothing left to do, which a unit never reaches (it starts with $\neg\mathrm{Fr}\ne\emptyset$ and ends when it becomes empty). An inserted element in a preprocessing thread is queued for scanning, as in §13 (footnote 9 allows either).
--
--   For Lemma 10.1, `IsStreamRun` supplies an indefinitely continued input stream, loading only its next update whenever the scheduler becomes idle. `LegalStream` requires each finite prefix to be legal. No fairness, completion or thread-termination premise is imposed.
-- source:
--   Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), Fully Dynamic Weighted Set Cover: Worst-Case Recourse and Update Time, STOC 2027 submission, supplied PDF sha256 28a86be41fbea2451c118c89c7385500105ced4b59ab5e66110721ebf0909337, §7, pp. 23–32 (PDF 26–35), Algorithms 1–9

import Mathlib
import Definitions.Def_DynSetCover_Instance
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Problem

namespace WeightedSetCoverWorstCase.Dynamic

/-!
# The dynamic algorithm of Part II (Algorithms 1–9) as a transition relation

Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), §7, pp. 23–32 (PDF 26–35).

Element versions are natural numbers: the `v`-th insertion creates version `v` (§6.1: every
reinsertion is a brand-new version). `base v` is the base element of version `v`; a set `s`
contains `v` iff it contains `base v`.

The state holds the foreground hierarchical partial covering `(U^F, ℓ^F, ℘ℓ^F, C^F, cov^F)`
(§7.1), the thread pool sorted by increasing index (the head is the active thread, §7.2.2), the set
of alive versions (`Dead = U ∖ Alive`), and the scheduler's control state (Algorithm 9).
Each thread `T_k` carries `U^B_k = Fr^B_k ⊔ ¬Fr^B_k`, `Supp^B_k`, its buffer copies `C^B_k`
(with coverages and levels), `ℓ^B_k`, `℘ℓ^B_k`, the pointers `p_k`, `g_k`, the set of elements not
yet scanned by its preprocessing (preprocessing phase ⇔ it is nonempty), the coverage of its current
greedy copy (rebuild phase), its index `k` and a serial identity `tid` (two runs of the same index
are different threads).

The algorithm is computed with the normalised costs `ncost` (§6.1 places all costs in `[1/C, 1]`).

`Step ε st ev st'` is one event of the algorithm. Events: an adversarial update (Algorithm 5 or 6,
only when the scheduler is idle, consuming the next input update), one activation (Algorithm 1
called from Algorithm 7), one critical operation (a preprocessing scan, Algorithm 2, or the freezing
of one element of the current greedy copy, Algorithm 3), a greedy selection (Algorithm 3, line 2–3),
a termination (Algorithm 4), or a control step of Algorithm 9. `crit true` marks the critical
operation that ends a time unit (Algorithm 8: one critical operation outside tails; in a tail, the
operation that empties `¬Fr`).

The paper leaves four choices free, and the relation allows every choice: which pending element
is scanned next, which element of the current greedy copy is frozen next, which maximiser of
`|s ∩ ¬Fr_k| / c_s` is selected, and which cheapest set containing an inserted element is used.
Every statement about the algorithm quantifies over all runs, hence over all ways of resolving them.
-/

/-- A set copy whose coverage consists of element versions. -/
abbrev VCopy (m : ℕ) := Copy m ℕ

/-- A thread `T_k` and its buffer (§7.2.3). -/
structure Thread (m : ℕ) where
  /-- the index `k` -/
  idx : ℕ
  /-- a serial identity, distinct for every activation -/
  tid : ℕ
  /-- the domain `U^B_k` -/
  U : Finset ℕ
  /-- the frozen part `Fr^B_k` (the unfrozen part is `U ∖ fr`) -/
  fr : Finset ℕ
  /-- the supported elements `Supp^B_k` -/
  supp : Finset ℕ
  /-- the buffer solution `C^B_k` (a multiset of copies with coverages and levels) -/
  C : List (VCopy m)
  /-- the buffer levels `ℓ^B_k` (meaningful on frozen elements) -/
  lvl : ℕ → ℕ
  /-- the buffer passive levels `℘ℓ^B_k` -/
  plvl : ℕ → ℕ
  /-- the synchronization pointer `p_k` -/
  p : ℕ
  /-- the greedy pointer `g_k` -/
  g : ℕ
  /-- the elements of `U^B_k` not yet scanned by preprocessing (Algorithm 2) -/
  pending : Finset ℕ
  /-- the coverage of the current greedy copy (rebuild phase, Algorithm 3 line 4) -/
  cur : Finset ℕ

namespace Thread

variable {m : ℕ}

/-- `¬Fr^B_k = U^B_k ∖ Fr^B_k`. -/
def unfrozen (T : Thread m) : Finset ℕ := T.U \ T.fr

/-- Remove version `v` from the instance of `T` (Algorithm 6, line 16). -/
def removeV (T : Thread m) (v : ℕ) : Thread m :=
  { T with U := T.U.erase v, fr := T.fr.erase v, pending := T.pending.erase v }

end Thread

/-- The foreground solution `(U^F, ℓ^F, ℘ℓ^F, C^F, cov^F)` (§7.1); `Alive^F = U^F ∩ alive`. -/
structure Foreground (m : ℕ) where
  U : Finset ℕ
  lvl : ℕ → ℕ
  plvl : ℕ → ℕ
  C : List (VCopy m)

/-- The control state of Algorithm 9. `top c`: at line 3 with `count = c`; `unit c b`: inside a
time unit (Algorithm 8), `b` = it is a tail unit; `check c`: at line 11 after a time unit. -/
inductive Mode
  | idle
  | top (count : ℕ)
  | unit (count : ℕ) (tail : Bool)
  | check (count : ℕ)

/-- The full state of the algorithm, including the not-yet-processed input updates. -/
structure AlgState (inst : Instance) where
  fg : Foreground inst.m
  /-- the running threads, sorted by increasing index; the head is the active thread -/
  pool : List (Thread inst.m)
  /-- the alive versions -/
  alive : Finset ℕ
  /-- the base element of each created version -/
  base : ℕ → Option (Fin inst.u)
  /-- the current version of each live base element -/
  liveVer : Fin inst.u → ℕ
  nextVer : ℕ
  nextTid : ℕ
  mode : Mode
  /-- the adversarial updates still to come -/
  rest : List (Update inst.u)

/-- The kind of an event of the algorithm. -/
inductive Ev
  | idle
  | update
  | control
  | activate
  | terminate
  | select
  | crit (unitEnd : Bool)
  deriving DecidableEq

/-- `⌈σ⌉`: Algorithm 9 performs time units while `count > 0`, `count` starting at `σ`. -/
noncomputable def budget (inst : Instance) (ε : ℝ) : ℕ := ⌈sigma inst ε⌉₊

/-- The level `i_e = ⌊log_{1+ε}(1/c_{s_e})⌋` of an insertion covered by `s_e` (Algorithm 5). -/
noncomputable def insLevel (inst : Instance) (ε : ℝ) (s : Fin inst.m) : ℕ :=
  (flog (1 + ε) (1 / ncost inst s)).toNat

namespace AlgState

variable {inst : Instance} (st : AlgState inst)

/-- Version `v` belongs to input set `s`. -/
def InSet (s : Fin inst.m) (v : ℕ) : Prop := ∃ x ∈ inst.S s, st.base v = some x

instance (s : Fin inst.m) (v : ℕ) : Decidable (st.InSet s v) := by unfold InSet; infer_instance

/-- `X ∩ s`. -/
def inter (X : Finset ℕ) (s : Fin inst.m) : Finset ℕ := X.filter (st.InSet s)

/-- `v` is frozen by some running thread. -/
def FrozenBySome (v : ℕ) : Prop := ∃ T ∈ st.pool, v ∈ T.fr

instance (v : ℕ) : Decidable (st.FrozenBySome v) := by unfold FrozenBySome; infer_instance

/-- The foreground removal rule (Algorithms 2, 3, 6): remove every copy of `C^F` whose coverage
contains `v` and whose coverage elements are all dead or frozen by some thread. -/
def fgRemove (v : ℕ) : AlgState inst :=
  { st with fg := { st.fg with C := st.fg.C.filter (fun c =>
      !decide (v ∈ c.cov ∧ ∀ w ∈ c.cov, w ∉ st.alive ∨ st.FrozenBySome w)) } }

/-- `U^F_{≤k}`. -/
def fgUle (k : ℕ) : Finset ℕ := st.fg.U.filter fun v => st.fg.lvl v ≤ k

/-- `Act^F_{≤k}`. -/
def fgActle (k : ℕ) : Finset ℕ := st.fg.U.filter fun v => st.fg.lvl v ≤ k ∧ k < st.fg.plvl v

/-- `Pass^F_{≤k} = U^F_{≤k} ∖ Act^F_{≤k}`. -/
def fgPassle (k : ℕ) : Finset ℕ := st.fgUle k \ st.fgActle k

/-- `Alive^F = U^F ∩ Alive`. -/
def fgAlive : Finset ℕ := st.fg.U.filter fun v => v ∈ st.alive

/-- Replace the active (head) thread. -/
def withHead (T : Thread inst.m) : AlgState inst := { st with pool := T :: st.pool.tail }

/-- `v` lies in the coverage of a copy of an upper-level thread `T_i`, `i > k`. -/
def CoveredAbove (k v : ℕ) : Prop := ∃ T ∈ st.pool, k < T.idx ∧ ∃ c ∈ T.C, v ∈ c.cov

instance (k v : ℕ) : Decidable (st.CoveredAbove k v) := by unfold CoveredAbove; infer_instance

/-- Algorithm 2, one critical operation of the active thread `T`: scan `v`. -/
def scanOp (T : Thread inst.m) (v : ℕ) : AlgState inst :=
  let T1 : Thread inst.m := { T with
    plvl := Function.update T.plvl v (max (st.fg.plvl v) (T.idx + 1)),
    pending := T.pending.erase v }
  if st.CoveredAbove T.idx v then
    (st.withHead { T1 with fr := insert v T1.fr, supp := insert v T1.supp,
                           lvl := Function.update T1.lvl v T1.g }).fgRemove v
  else st.withHead T1

/-- The greedy key `|s ∩ ¬Fr_k| / c_s`. -/
noncomputable def ratio (T : Thread inst.m) (s : Fin inst.m) : ℝ :=
  ((st.inter T.unfrozen s).card : ℝ) / ncost inst s

/-- `s` maximises the greedy key (Algorithm 3, line 2). -/
def IsGreedy (T : Thread inst.m) (s : Fin inst.m) : Prop := ∀ s', st.ratio T s' ≤ st.ratio T s

/-- Algorithm 3, line 3: insert the greedy copy `s` with coverage `s ∩ ¬Fr_k`,
`g_k ← min{g_k, ⌊log_{1+ε}(|cov|/c_s)⌋}`, `ℓ(s) ← g_k`, `p_k ← min{p_k, g_k}`. -/
noncomputable def selectOp (ε : ℝ) (T : Thread inst.m) (s : Fin inst.m) : AlgState inst :=
  let cov := st.inter T.unfrozen s
  let g' := min T.g (flog (1 + ε) ((cov.card : ℝ) / ncost inst s)).toNat
  st.withHead { T with C := T.C ++ [⟨s, cov, g'⟩], g := g', p := min T.p g', cur := cov }

/-- Algorithm 3, lines 5–8, one critical operation: freeze `v` at level `g_k`. -/
def freezeOp (T : Thread inst.m) (v : ℕ) : AlgState inst :=
  (st.withHead { T with fr := insert v T.fr, lvl := Function.update T.lvl v T.g }).fgRemove v

/-- `v ∈ ¬Fr^B_j` for the active thread `T_j`, or `true` if the pool is empty (`¬Fr_{L+1} = U`). -/
def inParentUnfrozen (v : ℕ) : Bool :=
  match st.pool with
  | T :: _ => decide (v ∈ T.unfrozen)
  | [] => true

/-- The index `j` of the active thread, or `L + 1` if the pool is empty. -/
noncomputable def jIdx (ε : ℝ) : ℕ :=
  match st.pool with
  | T :: _ => T.idx
  | [] => Lpar inst ε + 1

/-- The synchronization pointer `p_j` of the active thread, or `L + 1`. -/
noncomputable def pPar (ε : ℝ) : ℕ :=
  match st.pool with
  | T :: _ => T.p
  | [] => Lpar inst ε + 1

/-- Algorithm 1: activate `T_k` below the active thread (or from an empty pool). -/
noncomputable def activateOp (ε : ℝ) (k : ℕ) : AlgState inst :=
  let UB := st.fg.U.filter fun v => v ∈ st.alive ∧ st.fg.lvl v ≤ k ∧ st.inParentUnfrozen v = true
  let supp := st.fg.U.filter fun v => st.fg.lvl v ≤ k ∧ ∃ T ∈ st.pool, k < T.idx ∧ v ∈ T.fr
  let T : Thread inst.m :=
    { idx := k, tid := st.nextTid, U := UB, fr := ∅, supp := supp, C := [],
      lvl := fun _ => 0, plvl := fun _ => 0, p := min (k + 1) (st.pPar ε), g := k + 1,
      pending := UB, cur := ∅ }
  { st with pool := T :: st.pool, nextTid := st.nextTid + 1 }

/-- The active thread is in its tail: `|¬Fr_j| ≤ 10/ε`. -/
def ActiveInTail (ε : ℝ) : Prop :=
  match st.pool with
  | T :: _ => (T.unfrozen.card : ℝ) ≤ 10 / ε
  | [] => False

/-- Algorithm 7, line 5: level `k` is `ε`-dirty, `|Pass^F_{≤k}| > ε|Act^F_{≤k}|`, or its part
unfrozen by the active thread is, `|¬Fr_j ∩ Pass^F_{≤k}| > ε|¬Fr_j ∩ Act^F_{≤k}|`. -/
def Dirty (ε : ℝ) (k : ℕ) : Prop :=
  ε * ((st.fgActle k).card : ℝ) < ((st.fgPassle k).card : ℝ) ∨
    ε * (((st.fgActle k).filter fun v => st.inParentUnfrozen v = true).card : ℝ) <
      (((st.fgPassle k).filter fun v => st.inParentUnfrozen v = true).card : ℝ)

/-- Algorithm 7 activates `T_k`: the active thread (if any) is not in its tail, and `k` is the
largest dirty index in `[0, j-1]`. -/
def IsActTarget (ε : ℝ) (k : ℕ) : Prop :=
  ¬ st.ActiveInTail ε ∧ k < st.jIdx ε ∧ st.Dirty ε k ∧
    ∀ k', k < k' → k' < st.jIdx ε → ¬ st.Dirty ε k'

/-- Algorithm 7 returns without activating. -/
def NoActTarget (ε : ℝ) : Prop := st.ActiveInTail ε ∨ ∀ k < st.jIdx ε, ¬ st.Dirty ε k

/-- Algorithm 4: terminate the active thread `T` (with `st.pool = T :: Ts`). Step 1 lifts the
supported elements to level `k+1`; step 2 replaces every remaining element of `U^F_{≤k}` by its
buffer levels if it is in `U^B_k` and removes it otherwise; then `C^F ← C^F + C^B_k`. -/
def terminateOp (T : Thread inst.m) (Ts : List (Thread inst.m)) : AlgState inst :=
  let k := T.idx
  let lvl1 : ℕ → ℕ := fun v => if v ∈ T.supp then k + 1 else st.fg.lvl v
  let plvl1 : ℕ → ℕ := fun v => if v ∈ T.supp then max (st.fg.plvl v) (k + 1) else st.fg.plvl v
  { st with
    fg := { U := st.fg.U.filter fun v => ¬ lvl1 v ≤ k ∨ v ∈ T.U
            lvl := fun v => if v ∈ st.fg.U ∧ lvl1 v ≤ k ∧ v ∈ T.U then T.lvl v else lvl1 v
            plvl := fun v => if v ∈ st.fg.U ∧ lvl1 v ≤ k ∧ v ∈ T.U then T.plvl v else plvl1 v
            C := st.fg.C ++ T.C }
    pool := Ts }

/-- `s` is a cheapest set containing the base element `x` (Algorithm 5, line 1). -/
def IsCheapest (x : Fin inst.u) (s : Fin inst.m) : Prop :=
  x ∈ inst.S s ∧ ∀ s', x ∈ inst.S s' → ncost inst s ≤ ncost inst s'

end AlgState

/-- Algorithm 5, lines 5–18: process the running threads from the highest to the lowest index
(the list is given in decreasing order). The flag is `covered`. Returns the updated threads and
the final flag. -/
def insDown {m : ℕ} (i v : ℕ) (se : Fin m) : List (Thread m) → Bool → List (Thread m) × Bool
  | [], cov => ([], cov)
  | T :: Ts, cov =>
    if T.idx < i then (T :: Ts, cov)
    else if cov then
      let r := insDown i v se Ts true
      ({ T with supp := insert v T.supp } :: r.1, r.2)
    else if T.pending.Nonempty then
      let r := insDown i v se Ts false
      ({ T with U := insert v T.U, pending := insert v T.pending,
                plvl := Function.update T.plvl v (T.idx + 1) } :: r.1, r.2)
    else if T.g ≤ i then
      let r := insDown i v se Ts true
      ({ T with C := T.C ++ [⟨se, {v}, i⟩], U := insert v T.U, fr := insert v T.fr,
                plvl := Function.update T.plvl v i, lvl := Function.update T.lvl v i } :: r.1, r.2)
    else
      let r := insDown i v se Ts false
      ({ T with U := insert v T.U, plvl := Function.update T.plvl v T.g } :: r.1, r.2)

namespace AlgState

variable {inst : Instance} (st : AlgState inst)

/-- Algorithm 5: adversarial insertion of the base element `x`, covered if necessary by the
cheapest set `se`. The new version is `nextVer`. In the preprocessing case the new element is also
queued for scanning (§13; footnote 9: scanning it changes nothing but its time). -/
noncomputable def insertOp (ε : ℝ) (x : Fin inst.u) (se : Fin inst.m) : AlgState inst :=
  let v := st.nextVer
  let i := insLevel inst ε se
  let r := insDown i v se st.pool.reverse false
  let st1 : AlgState inst :=
    { st with
      fg := { st.fg with U := insert v st.fg.U, lvl := Function.update st.fg.lvl v i,
                         plvl := Function.update st.fg.plvl v i }
      alive := insert v st.alive
      base := Function.update st.base v (some x)
      liveVer := Function.update st.liveVer x v
      nextVer := v + 1
      pool := r.1.reverse }
  if r.2 then st1 else { st1 with fg := { st1.fg with C := st1.fg.C ++ [⟨se, {v}, i⟩] } }

/-- Algorithm 6, lines 7–14, for the thread `T` owning the copy `c` with `v ∈ cov(c)`
(`aliveNow` is the alive set after the deletion). -/
def ownerUpdate (aliveNow : Finset ℕ) (T : Thread inst.m) (c : VCopy inst.m) (v : ℕ) :
    Thread inst.m :=
  let T1 : Thread inst.m :=
    if v ∈ T.unfrozen then { T with fr := insert v T.fr, lvl := Function.update T.lvl v c.lvl }
    else T
  let T2 : Thread inst.m := { T1 with plvl := Function.update T1.plvl v (T1.lvl v) }
  if ∀ w ∈ c.cov, w ∉ aliveNow then { T2 with C := T2.C.erase c } else T2

/-- Algorithm 6: adversarial deletion of the base element `x` (its live version `v`). The owner
is the (unique, Lemma 8.8) running thread with a copy whose coverage contains `v`; the lowest such
thread and its first such copy are taken. -/
def deleteOp (x : Fin inst.u) : AlgState inst :=
  let v := st.liveVer x
  let st1 : AlgState inst :=
    { st with fg := { st.fg with plvl := Function.update st.fg.plvl v (st.fg.lvl v) },
              alive := st.alive.erase v }
  let st2 := st1.fgRemove v
  match st2.pool.findIdx? (fun T => decide (∃ c ∈ T.C, v ∈ c.cov)) with
  | none => { st2 with pool := st2.pool.map fun T => T.removeV v }
  | some j =>
    match st2.pool[j]? with
    | none => st2
    | some Tj =>
      match Tj.C.find? (fun c => decide (v ∈ c.cov)) with
      | none => st2
      | some c =>
        let justFrozen := decide (v ∈ Tj.unfrozen)
        { st2 with pool := st2.pool.mapIdx fun i T =>
            if i = j then ownerUpdate st2.alive T c v
            else if i < j then
              (if justFrozen = true ∧ st2.fg.lvl v ≤ T.idx then
                { T with supp := insert v T.supp } else T).removeV v
            else T.removeV v }

/-- Whether a time unit ends after a critical operation that produced `st'`: always outside
tails; in a tail, when the active thread's `¬Fr` has become empty (Algorithm 8). -/
def critEnds (tail : Bool) (st' : AlgState inst) : Bool :=
  !tail || (match st'.pool with
            | T :: _ => decide (T.unfrozen = ∅)
            | [] => true)

/-- The state after a critical operation inside a time unit. -/
def afterCrit (count : ℕ) (tail : Bool) (st' : AlgState inst) : AlgState inst :=
  if critEnds tail st' = true then { st' with mode := .check count }
  else { st' with mode := .unit count tail }

end AlgState

open AlgState in
/-- One event of the algorithm (Algorithms 5–9 and the phases of Algorithms 1–4). -/
inductive Step {inst : Instance} (ε : ℝ) : AlgState inst → Ev → AlgState inst → Prop
  /-- no further input: the algorithm waits -/
  | wait (st : AlgState inst) : st.mode = .idle → st.rest = [] → Step ε st .idle st
  /-- Algorithm 9, line 1 with Algorithm 5; then `count ← σ` -/
  | ins (st : AlgState inst) (x : Fin inst.u) (xs : List (Update inst.u)) (se : Fin inst.m) :
      st.mode = .idle → st.rest = .ins x :: xs → IsCheapest x se →
      Step ε st .update { st.insertOp ε x se with mode := .top (budget inst ε), rest := xs }
  /-- Algorithm 9, line 1 with Algorithm 6; then `count ← σ` -/
  | del (st : AlgState inst) (x : Fin inst.u) (xs : List (Update inst.u)) :
      st.mode = .idle → st.rest = .del x :: xs →
      Step ε st .update { st.deleteOp x with mode := .top (budget inst ε), rest := xs }
  /-- Algorithm 9, line 3: the loop ends -/
  | exit (st : AlgState inst) (c : ℕ) :
      st.mode = .top c → ¬ (0 < c ∨ st.ActiveInTail ε) → Step ε st .control { st with mode := .idle }
  /-- Algorithm 9, line 4 (Algorithm 7): one activation -/
  | activate (st : AlgState inst) (c k : ℕ) :
      st.mode = .top c → (0 < c ∨ st.ActiveInTail ε) → st.IsActTarget ε k →
      Step ε st .activate (st.activateOp ε k)
  /-- Algorithm 9, lines 5–6: empty pool -/
  | empty (st : AlgState inst) (c : ℕ) :
      st.mode = .top c → (0 < c ∨ st.ActiveInTail ε) → st.NoActTarget ε → st.pool = [] →
      Step ε st .control { st with mode := .idle }
  /-- Algorithm 9, lines 8–10: start a time unit on the active thread, `count ← count − 1` -/
  | startUnit (st : AlgState inst) (c : ℕ) (T : Thread inst.m) (Ts : List (Thread inst.m)) :
      st.mode = .top c → (0 < c ∨ st.ActiveInTail ε) → st.NoActTarget ε → st.pool = T :: Ts →
      T.unfrozen.Nonempty →
      Step ε st .control
        { st with mode := .unit (c - 1) (decide ((T.unfrozen.card : ℝ) ≤ 10 / ε)) }
  /-- Algorithm 9, lines 11–13 without a time unit (`¬Fr_k = ∅`): terminate -/
  | termNoUnit (st : AlgState inst) (c : ℕ) (T : Thread inst.m) (Ts : List (Thread inst.m)) :
      st.mode = .top c → (0 < c ∨ st.ActiveInTail ε) → st.NoActTarget ε → st.pool = T :: Ts →
      T.unfrozen = ∅ →
      Step ε st .terminate { st.terminateOp T Ts with mode := .top c }
  /-- Algorithm 2: one preprocessing scan (a critical operation) -/
  | scan (st : AlgState inst) (c : ℕ) (b : Bool) (T : Thread inst.m) (Ts : List (Thread inst.m))
      (v : ℕ) :
      st.mode = .unit c b → st.pool = T :: Ts → v ∈ T.pending →
      Step ε st (.crit (critEnds b (st.scanOp T v))) (afterCrit c b (st.scanOp T v))
  /-- Algorithm 3, lines 2–3: a greedy selection (not a critical operation) -/
  | select (st : AlgState inst) (c : ℕ) (b : Bool) (T : Thread inst.m) (Ts : List (Thread inst.m))
      (s : Fin inst.m) :
      st.mode = .unit c b → st.pool = T :: Ts → T.pending = ∅ → T.cur ∩ T.unfrozen = ∅ →
      T.unfrozen.Nonempty → st.IsGreedy T s →
      Step ε st .select (st.selectOp ε T s)
  /-- Algorithm 3, lines 4–8: freeze one element of the current greedy copy (a critical
  operation) -/
  | freeze (st : AlgState inst) (c : ℕ) (b : Bool) (T : Thread inst.m) (Ts : List (Thread inst.m))
      (v : ℕ) :
      st.mode = .unit c b → st.pool = T :: Ts → T.pending = ∅ → v ∈ T.cur ∩ T.unfrozen →
      Step ε st (.crit (critEnds b (st.freezeOp T v))) (afterCrit c b (st.freezeOp T v))
  /-- defensive totality: a time unit with nothing left to do ends without a critical operation
  (not reachable: a unit starts only with `¬Fr ≠ ∅` and ends as soon as `¬Fr = ∅`) -/
  | unitDone (st : AlgState inst) (c : ℕ) (b : Bool) :
      st.mode = .unit c b →
      (match st.pool with
       | T :: _ => T.pending = ∅ ∧ T.unfrozen = ∅
       | [] => True) →
      Step ε st .control { st with mode := .check c }
  /-- Algorithm 9, lines 11–13 after a time unit: terminate if `¬Fr_k = ∅` -/
  | checkTerm (st : AlgState inst) (c : ℕ) (T : Thread inst.m) (Ts : List (Thread inst.m)) :
      st.mode = .check c → st.pool = T :: Ts → T.unfrozen = ∅ →
      Step ε st .terminate { st.terminateOp T Ts with mode := .top c }
  /-- Algorithm 9, line 11: `¬Fr_k ≠ ∅`, continue the loop -/
  | checkCont (st : AlgState inst) (c : ℕ) :
      st.mode = .check c →
      (match st.pool with
       | T :: _ => T.unfrozen.Nonempty
       | [] => True) →
      Step ε st .control { st with mode := .top c }

namespace AlgState

variable {inst : Instance}

/-- The initial state: empty foreground, empty pool, no versions, scheduler idle, input `ups`
(updates of base elements, starting from the empty live set). -/
def init (inst : Instance) (ups : List (Update inst.u)) : AlgState inst :=
  { fg := ⟨∅, fun _ => 0, fun _ => 0, []⟩, pool := [], alive := ∅, base := fun _ => none,
    liveVer := fun _ => 0, nextVer := 0, nextTid := 0, mode := .idle, rest := ups }

variable (st : AlgState inst)

/-- The background solution `C^B = ⋃_k C^B_k` over the running threads (a multiset). -/
def bgCopies : List (VCopy inst.m) := st.pool.flatMap fun T => T.C

/-- The output `C^F + C^B` (a multiset of copies). -/
def outCopies : List (VCopy inst.m) := st.fg.C ++ st.bgCopies

/-- The base elements of the alive versions. -/
def aliveBase : Finset (Fin inst.u) := st.alive.biUnion fun v => (st.base v).toFinset

/-- The cost of a minimum set cover of the alive elements (original costs). -/
noncomputable def optAlive : ℝ := inst.OPT0 st.aliveBase

end AlgState

/-- A run of the algorithm with parameter `ε` on the input updates `ups` (applied from the empty
live set): `c i` is the state before event `i`, and every event is a `Step`. -/
def IsRun (inst : Instance) (ε : ℝ) (ups : List (Update inst.u)) (c : ℕ → AlgState inst)
    (ev : ℕ → Ev) : Prop :=
  c 0 = AlgState.init inst ups ∧ ∀ i, Step ε (c i) (ev i) (c (i + 1))

/-- An indefinitely continued legal adversarial history, from the empty live set. Every finite
prefix is legal; an arbitrary initial live set is supplied by an initial insertion prefix. -/
def LegalStream {u : ℕ} (ups : ℕ → Update u) : Prop :=
  ∀ k, LegalSeq ∅ ((List.range k).map ups)

/-- A run with an indefinitely supplied update stream, for the lifetime assertion of Lemma 10.1.
Only the next update is loaded when the scheduler is idle; the thread transitions are exactly
`Step`. There is no fairness, thread termination, or update-completion assumption in this predicate.
Unlike a finite `IsRun`, this run never waits merely because the external input has ended. -/
def IsStreamRun (inst : Instance) (ε : ℝ) (ups : ℕ → Update inst.u)
    (c : ℕ → AlgState inst) (ev : ℕ → Ev) : Prop :=
  c 0 = AlgState.init inst [] ∧ ∀ i,
    let j := ((Finset.range i).filter fun h => ev h = .update).card
    Step ε (match (c i).mode with
      | .idle => { c i with rest := [ups j] }
      | _ => c i) (ev i) (c (i + 1))

end WeightedSetCoverWorstCase.Dynamic


