-- Prove2me | Definitions.Def_DynSetCover_Supplement_BatchAlgorithm
-- name    : DynSetCover_Supplement_BatchAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:56:10.940196+00:00
-- url     : https://prove2.me/theorems/716708fc-14ec-4e7d-82d0-eb8ec8676ced
-- title:
--   §3 — the batch algorithm: copies, opening and deficiency conditions, maximum-priority scheduling with a budget of 2048 operations, admissible runs
-- statement:
--   The **batch algorithm** of §3 maintains, for the active set $A_t$, a collection $\mathcal S_t$ of retained **copies**. A copy $Q$ has an underlying input set $S_Q$, a current level $h_Q\in\mathbb Z$, an accounting level $q_Q\in\mathbb Z$, and an assigned set $\mathrm{cov}_t(Q)\subseteq A_t$; the assigned sets partition $A_t$, and every element assigned to $Q$ has actual level $\ell(e)=h_Q$. The **physical cover** is $\{S:\mu_t(S)>0\}$, where $\mu_t(S)=|\{Q\in\mathcal S_t:S_Q=S\}|$.
--
--   Costs are rounded, $c(S)=2^{H(S)}$ with $H(S)=\lceil\log_2c_0(S)\rceil$; $S_e$ is a cheapest set containing $e$ and $b(e)=H(S_e)$. The volume is $\mathrm{vol}(e,i)=2^{i-b(e)}$ (no floor) and $\mathrm{vol}(X,i)=\sum_{e\in X}\mathrm{vol}(e,i)$; $A_t(r)=\{e\in A_t:\ell(e)=r\}$.
--
--   Internal operations:
--   1. **Level decrement** $(S,r)$, priority $r$, applicable when the opening condition (21) $2^r\,\mathrm{vol}(S\cap A_t(r),r)\ge c(S)$ holds (also when a copy of $S$ is retained). It installs a fresh copy $Q$ of $S$ with $h_Q=q_Q=r-1$ and reassigns every element of $X=S\cap A_t(r)$ to $Q$, at level $r-1$; earlier copies keep their levels.
--   2. **Level increment** of a nonempty **deficient** copy $Q$, i.e. one with (22) $2^{h_Q}\mathrm{vol}(\mathrm{cov}_t(Q),h_Q)<c(S_Q)/64$; priority $q_Q$ (before execution). It sets $h_Q\leftarrow h_Q+1$, moving all assigned elements with it, and in the same operation sets $q_Q\leftarrow h_Q$ if $Q$ is funded (not deficient) at the new level.
--   3. **Empty-copy deletion** of a copy with $\mathrm{cov}_t(Q)=\emptyset$; priority $q_Q$.
--
--   Input updates: initially no element is active and no copy is retained. An arrival of $e$ activates it and creates a fresh copy $Q$ of $S_e$ with $\mathrm{cov}_t(Q)=\{e\}$ and $q_Q=h_Q=b(e)-1$. A departure of $e$ removes $e$ from $A_t$ and from its copy, which is retained with unchanged levels even if empty. After each update the algorithm executes at most $2048$ internal operations, each an applicable operation of maximum priority (decrements first at equal priority), and stops earlier only when none is applicable; the state reached is the **update boundary**.
--
--   This is the algorithm of Theorem 1.1, whose approximation is Theorem 4.1. It differs from the faster algorithm of §5 (no volume floor, no pending lists, no work charges).
--
--   **Formalization Note** A copy is a pair (fresh identifier, set index). Remaining ties are left free: an admissible run may execute any applicable operation that is maximal in (priority, decrement-first) order, and the cheapest sets $S_e$ are any fixed choice; the paper's FIFO run is one admissible run.
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), §3.1.1, p.15 (PDF 17); §3.1.3, pp.17–21 (PDF 19–23), opening condition (21), deficiency condition (22), Modification 2, Input updates and operation budget

import Mathlib
import Definitions.Def_DynSetCover_Rounding
import Definitions.Def_DynSetCover_Updates

namespace DynSetCover.Supplement

/-! # The batch algorithm of §3 as a relation on admissible runs

Paul, Solomon, *Weighted Set Cover with Constant Worst-Case Recourse* (STOC 2027 submission,
sha256 a671756b…): copies, assignments and the physical cover §3.1.1, p.15 (PDF 17); rounding,
bases, geometric volume, level decrements (opening condition (21)), level increments
(deficiency condition (22)), empty-copy deletions, accounting levels, the maximum-priority
rule, input updates and the operation budget of 2048, §3.1.3, pp.17–21 (PDF 19–23).

This is the **batch** algorithm of §3 (each operation moves a whole batch), not the faster
algorithm of §5 (`DynSetCover.Algorithm`): its volume is the geometric volume
`vol(e, i) = 2^{i−b(e)}` with no floor, it has no pending or waiting lists and no work charges,
and every internal operation counts `1` towards the budget of `2048`.

A **state** records the active set `A_t`, the actual level `ℓ(e)` of each element, and the
retained copies `S_t`. A copy `Q` has an underlying input set `S_Q`, a current level `h_Q`, an
accounting level `q_Q`, and an assigned set `cov_t(Q)`. The physical (maintained) cover is the
set of input sets `S` with `µ_t(S) = |{Q ∈ S_t : S_Q = S}| > 0`.

**Formalization Note.**
* Costs, cheapest sets and bases are those of the rounded instance (p.17): `c(S) = 2^{H(S)}`,
  `H(S) = ⌈log₂ c0(S)⌉`, and `b(e) = H(S_e)` (`DynSetCover.Instance.c`, `.H`, `.base`).
* A copy is a pair `(id, s)` of a fresh identifier and the index `s` of its underlying input
  set `S_Q`; fresh identifiers come from the counter `next`.
* The actual level `ℓ(e) = h_{ϕ_t(e)}` is stored in the field `level`, and every operation that
  moves elements updates it together with `h`; the update rules keep `ℓ(e) = h_Q` for every
  `e ∈ cov_t(Q)` (the paper's definition of `ℓ`).
* The paper breaks ties inside a (priority, category) class FIFO, with a fixed deterministic
  order for simultaneous ties (p.21). This development quantifies over every **admissible
  run**: each executed operation is applicable and maximal in (priority, decrement-first) order;
  an update executes at most `2048` operations and stops earlier only when no operation is
  applicable. The paper's FIFO run is one admissible run.
* The cheapest sets `S_e` are a parameter `ce` (any fixed choice, `Instance.IsCheapest`). -/

variable (inst : Instance)

/-- A copy of the batch algorithm: a fresh identifier and the index of its underlying input set
`S_Q`. -/
abbrev BatchCopy := ℕ × Fin inst.m

/-- A state of the §3 batch algorithm. -/
structure BatchState where
  /-- the active set `A_t` -/
  active : Finset (Fin inst.u)
  /-- the actual level `ℓ(e)` -/
  level : Fin inst.u → ℤ
  /-- the retained copies `S_t` -/
  copies : Finset (BatchCopy inst)
  /-- the next fresh copy identifier -/
  next : ℕ
  /-- the current level `h_Q` -/
  h : BatchCopy inst → ℤ
  /-- the accounting level `q_Q` -/
  q : BatchCopy inst → ℤ
  /-- the assigned set `cov_t(Q)` -/
  cov : BatchCopy inst → Finset (Fin inst.u)

namespace BatchState

/-- The initial state: no element is active and no copy is retained (p.21). -/
def init : BatchState inst :=
  ⟨∅, fun _ => 0, ∅, 0, fun _ => 0, fun _ => 0, fun _ => ∅⟩

/-- The physical (maintained) cover: the input sets `S` with `µ_t(S) > 0`, i.e. with at least one
retained copy (p.15). Each such set appears once, however many copies it has. -/
def physCover (s : BatchState inst) : Finset (Fin inst.m) := s.copies.image Prod.snd

end BatchState

/-- The geometric volume `vol(e, i) = 2^{i−b(e)}` (p.17); no volume floor. -/
noncomputable def bvol (e : Fin inst.u) (i : ℤ) : ℝ := (2 : ℝ) ^ (i - inst.base e)

/-- `vol(X, i) = Σ_{e∈X} vol(e, i)`: every element of `X` is evaluated at level `i` (p.15). -/
noncomputable def bvolSet (X : Finset (Fin inst.u)) (i : ℤ) : ℝ := ∑ e ∈ X, bvol inst e i

/-- The decrement batch `S ∩ A_t(r)`, where `A_t(r) = {e ∈ A_t : ℓ(e) = r}` (p.17). -/
def bbatch (s : BatchState inst) (S : Fin inst.m) (r : ℤ) : Finset (Fin inst.u) :=
  (inst.S S).filter (fun e => e ∈ s.active ∧ s.level e = r)

/-- The deficiency condition (22), p.18, at level `i`: `2^i vol(cov_t(Q), i) < C_Q / 64`, with
`C_Q = c(S_Q)` the rounded cost. A nonempty copy is *funded* at its current level when
`BDeficientAt s Q (s.h Q)` fails. -/
noncomputable def BDeficientAt (s : BatchState inst) (Q : BatchCopy inst) (i : ℤ) : Prop :=
  (2 : ℝ) ^ i * bvolSet inst (s.cov Q) i < inst.c Q.2 / 64

/-- The internal operations of the batch algorithm (pp.17–19). -/
inductive BatchOp where
  /-- level decrement (stabilization) for the input set `S` at level `r` -/
  | dec (S : Fin inst.m) (r : ℤ)
  /-- level increment (float up) of the copy `Q` -/
  | inc (Q : BatchCopy inst)
  /-- deletion of the empty copy `Q` -/
  | del (Q : BatchCopy inst)

variable {inst}

/-- The tie-breaking category: at equal priority, decrements (`2`) precede increments and
empty-copy deletions (`1`) (p.21). -/
def BatchOp.cat : BatchOp inst → ℕ
  | .dec _ _ => 2
  | _ => 1

variable (inst)

/-- Applicability (pp.17–18): a decrement `(S, r)` needs the opening condition (21)
`2^r vol(S ∩ A_t(r), r) ≥ c(S)` (non-strict, tested even when a copy of `S` is retained); an
increment needs a retained nonempty deficient copy (22); a deletion needs a retained empty
copy. -/
def BApplicable (s : BatchState inst) : BatchOp inst → Prop
  | .dec S r => inst.c S ≤ (2 : ℝ) ^ r * bvolSet inst (bbatch inst s S r) r
  | .inc Q => Q ∈ s.copies ∧ (s.cov Q).Nonempty ∧ BDeficientAt inst s Q (s.h Q)
  | .del Q => Q ∈ s.copies ∧ s.cov Q = ∅

/-- The priority, evaluated before execution (p.19): a decrement `(S, r)` has priority `r`; an
increment or deletion of `Q` has priority `q_Q`. -/
def bprio (s : BatchState inst) : BatchOp inst → ℤ
  | .dec _ r => r
  | .inc Q => s.q Q
  | .del Q => s.q Q

/-- `o` is selected in `s`: it is applicable and of maximum priority among the applicable
operations, a decrement whenever a decrement of that priority is applicable (p.21). -/
def BSelected (s : BatchState inst) (o : BatchOp inst) : Prop :=
  BApplicable inst s o ∧ ∀ o', BApplicable inst s o' →
    bprio inst s o' < bprio inst s o ∨ (bprio inst s o' = bprio inst s o ∧ o'.cat ≤ o.cat)

open Classical in
/-- Execution of an internal operation (pp.18–19).
* Decrement `(S, r)`: install a fresh copy `Q` of `S` with `h_Q = q_Q = r − 1` and reassign
  every element of `X = S ∩ A_t(r)` to it (now at level `r − 1`); previous copies lose their
  elements of `X` and keep their levels.
* Increment of `Q`: `h_Q ← h_Q + 1`, all assigned elements move with it; then, in the same
  operation, `q_Q ← h_Q + 1` if `Q` is funded at the new level, else `q_Q` is unchanged.
* Deletion of `Q`: remove the copy. -/
noncomputable def bexec (s : BatchState inst) : BatchOp inst → BatchState inst
  | .dec S r =>
      let Q : BatchCopy inst := (s.next, S)
      let X := bbatch inst s S r
      { s with copies := insert Q s.copies, next := s.next + 1,
               level := fun e => if e ∈ X then r - 1 else s.level e,
               h := Function.update s.h Q (r - 1), q := Function.update s.q Q (r - 1),
               cov := fun Q' => if Q' = Q then X else s.cov Q' \ X }
  | .inc Q =>
      let s₁ : BatchState inst :=
        { s with h := Function.update s.h Q (s.h Q + 1),
                 level := fun e => if e ∈ s.cov Q then s.h Q + 1 else s.level e }
      { s₁ with
          q := Function.update s.q Q
            (if BDeficientAt inst s₁ Q (s.h Q + 1) then s.q Q else s.h Q + 1) }
  | .del Q => { s with copies := s.copies.erase Q }

/-- An input update (p.21): an arrival of `e` activates `e` and creates a fresh copy `Q` of
`S_e` with `cov_t(Q) = {e}` and `q_Q = h_Q = ℓ(e) = b(e) − 1`; a departure of `e` removes `e`
from the active set and from its assigned copy, which is retained with unchanged levels even if
it becomes empty. -/
noncomputable def bapplyUpdate (ce : Fin inst.u → Fin inst.m) (s : BatchState inst) :
    Upd inst.u → BatchState inst
  | .ins e =>
      let Q : BatchCopy inst := (s.next, ce e)
      { s with active := insert e s.active,
               level := Function.update s.level e (inst.base e - 1),
               copies := insert Q s.copies, next := s.next + 1,
               h := Function.update s.h Q (inst.base e - 1),
               q := Function.update s.q Q (inst.base e - 1),
               cov := Function.update s.cov Q {e} }
  | .del e =>
      { s with active := s.active.erase e, cov := fun Q => (s.cov Q).erase e }

/-- `BPhase s ops s'`: starting in `s`, the operations `ops` are executed in order, each selected
(applicable and maximal) in the state in which it executes, reaching `s'`. -/
inductive BPhase : BatchState inst → List (BatchOp inst) → BatchState inst → Prop
  | refl (s : BatchState inst) : BPhase s [] s
  | step {s : BatchState inst} {o : BatchOp inst} {ops : List (BatchOp inst)}
      {s' : BatchState inst} :
      BSelected inst s o → BPhase (bexec inst s o) ops s' → BPhase s (o :: ops) s'

/-- Processing one input update (p.21): the update is valid for the active set; apply it, then
execute at most `2048` selected internal operations, stopping earlier only when no operation is
applicable. The state reached is the update boundary. -/
def BProcess (ce : Fin inst.u → Fin inst.m) (s : BatchState inst) (x : Upd inst.u)
    (s' : BatchState inst) : Prop :=
  x.ValidAt s.active ∧ ∃ ops : List (BatchOp inst),
    BPhase inst (bapplyUpdate inst ce s x) ops s' ∧ ops.length ≤ 2048 ∧
      (ops.length = 2048 ∨ ∀ o, ¬ BApplicable inst s' o)

/-- `bs` lists the update boundaries `bs 0, …, bs σ.length` of an admissible run of the batch
algorithm on `σ`; `bs 0` is the initial state and `bs t` the update boundary after update `t`. -/
def IsBatchRun (ce : Fin inst.u → Fin inst.m) (σ : List (Upd inst.u)) (bs : ℕ → BatchState inst) :
    Prop :=
  bs 0 = BatchState.init inst ∧ ∀ t (ht : t < σ.length), BProcess inst ce (bs t) (σ[t]) (bs (t + 1))

end DynSetCover.Supplement


