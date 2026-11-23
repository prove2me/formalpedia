-- Prove2me | Definitions.Def_FracTruthSched_PaddedConstruction
-- name    : FracTruthSched_PaddedConstruction
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:49:22.234046+00:00
-- url     : https://prove2.me/theorems/91edbcf5-ae02-4c89-b3ef-0d01fad78052
-- title:
--   Explicit finite padding, symmetrization, slicing and reservoir averaging
-- statement:
--   This module implements the finite construction of Appendix A.1 at Lean stage $K$, corresponding to paper stage $K+1$. It enumerates the positive rationals by $r_{(a,b)}=(a+1)/(b+1)$ using a pairing function, and forms the listed zero types
--   $$T_K^{\mathrm{Lean}}=\{(0,0)\}\cup\{(0,r_h),(r_h,0):0\le h\le K\}.$$
--   A reservoir-count vector assigns to every machine pair and listed zero type an offset in $\{0,\ldots,K+1\}$, hence between $K+1$ and $2(K+1)$ actual reservoir tasks. The padded task type consists of the core tasks, these reservoir tasks, and one extra self-loop. At non-endpoints a task has value $(K+1)^2$, and the extra loop has value $1/(K+1)$ at the first machine.
--
--   The construction then transports the appropriate member of the original family to this finite task type, averages over all permutations preserving machine-pair classes and fixing self-loops, slices to core tasks while subtracting each machine's cost on its fixed tasks from its payment, and finally averages uniformly over reservoir-count vectors. It also supplies general task-reindexing, symmetrization, slicing and finite-averaging operations used by the proof of Claims 2–7.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Appendix A.1, pp.23–24 (Padding, Symmetrization, The padded mechanism); Lean stage K is paper stage K+1.

import Mathlib
import Definitions.Def_FracTruthSched_FracMech
import Definitions.Def_FracTruthSched_CoreTask
import Definitions.Def_FracTruthSched_incident
import Definitions.Def_FracTruthSched_relabel

set_option autoImplicit false

namespace FracTruthSched

/-- Transport a mechanism along an equivalence of task sets. -/
def reindexMech {n : ℕ} {τ σ : Type*} (M : FracMech n τ) (e : σ ≃ τ) :
    FracMech n σ where
  x s i j := M.x (fun u k => s u (e.symm k)) i (e j)
  P s i := M.P (fun u k => s u (e.symm k)) i

open Classical in
/-- Symmetrization over a subgroup of task permutations, for an arbitrary finite task type. -/
noncomputable def symmetrizeGen {n : ℕ} {τ : Type*} [Fintype τ]
    (M : FracMech n τ) (G : Subgroup (Equiv.Perm τ)) : FracMech n τ where
  x s i e := (1 / (Fintype.card G : ℝ)) * ∑ π : G, M.x (relabel π.1 s) i (π.1⁻¹ e)
  P s i := (1 / (Fintype.card G : ℝ)) * ∑ π : G, M.P (relabel π.1 s) i

open Classical in
/-- The uniform average of a nonempty finite family of mechanisms on a common task set. -/
noncomputable def averageMech {n : ℕ} {τ ι : Type*} [Fintype τ] [Fintype ι] [Nonempty ι]
    (N : ι → FracMech n τ) : FracMech n τ where
  x s i e := (1 / (Fintype.card ι : ℝ)) * ∑ a, (N a).x s i e
  P s i := (1 / (Fintype.card ι : ℝ)) * ∑ a, (N a).P s i

open Classical in
/-- Slice a mechanism on an extended task set to the tasks in the range of `core`.
The payment is reduced by the machine's cost on all tasks except its own core tasks. -/
noncomputable def sliceMech {n : ℕ} {τ σ : Type*} [Fintype σ]
    (N : FracMech n σ) (core : τ → σ)
    (extend : (Fin n → τ → ℝ) → (Fin n → σ → ℝ))
    (own : Fin n → σ → Prop) : FracMech n τ where
  x t i e := N.x (extend t) i (core e)
  P t i := N.P (extend t) i -
    ∑ f : σ, if own i f then 0 else extend t i f * N.x (extend t) i f

/-- The permutations preserving every fiber of a task-class function. -/
def classPerms {τ ι : Type*} (c : τ → ι) : Subgroup (Equiv.Perm τ) where
  carrier := {π | ∀ e, c (π e) = c e}
  one_mem' := by intro e; rfl
  mul_mem' := by
    intro π γ hπ hγ e
    change c (π (γ e)) = c e
    rw [hπ, hγ]
  inv_mem' := by
    intro π hπ e
    have h := hπ (π⁻¹ e)
    simpa using h.symm

/-- Unordered pairs of distinct machines, with their canonical orientation. -/
abbrev MachinePair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- `(0,0)` together with the first `K+1` positive rational values on either side.
This is the zero-type list `T_{K+1}` of the paper. -/
abbrev ZeroTypeIndex (K : ℕ) := Option (Bool × Fin (K + 1))

/-- An explicit surjective enumeration of the positive rationals. -/
def positiveRatEnum (h : ℕ) : ℚ :=
  let p := Nat.unpair h
  ((p.1 + 1 : ℕ) : ℚ) / ((p.2 + 1 : ℕ) : ℚ)

/-- The rational zero type attached to a list index. -/
def zeroTypeValues (K : ℕ) : ZeroTypeIndex K → ℚ × ℚ
  | none => (0, 0)
  | some (false, h) => (0, positiveRatEnum h.1)
  | some (true, h) => (positiveRatEnum h.1, 0)

/-- Reservoir classes are indexed by an unordered machine pair and a listed zero type. -/
abbrev ReservoirCoord (n K : ℕ) := MachinePair n × ZeroTypeIndex K

/-- At Lean stage `K`, every coordinate has `K+1,...,2*(K+1)` copies, encoded by an offset. -/
abbrev ReservoirVector (n K : ℕ) := ReservoirCoord n K → Fin (K + 2)

/-- The actual number of reservoir tasks at one coordinate. -/
def reservoirCount {n K : ℕ} (κ : ReservoirVector n K) (c : ReservoirCoord n K) : ℕ :=
  K + 1 + (κ c).1

/-- The reservoir tasks for a fixed vector of reservoir counts. -/
abbrev ReservoirTask {n K : ℕ} (κ : ReservoirVector n K) :=
  (c : ReservoirCoord n K) × Fin (reservoirCount κ c)

/-- Core tasks, reservoir tasks, and the extra self-loop. -/
abbrev PaddedTask {n ℓ K : ℕ} (κ : ReservoirVector n K) :=
  CoreTask n ℓ ⊕ (ReservoirTask κ ⊕ Unit)

/-- The common value at a machine ineligible for a padded task. -/
noncomputable def paddingHigh (K : ℕ) : ℝ := ((K : ℝ) + 1) ^ 2

/-- The small value of the extra self-loop at the first machine. -/
noncomputable def paddingBeta (K : ℕ) : ℝ := 1 / ((K : ℝ) + 1)

/-- The padded instance `(t,κ)` of Appendix A.1. -/
noncomputable def paddedInput {n ℓ K : ℕ} [NeZero n] (κ : ReservoirVector n K)
    (t : Fin n → CoreTask n ℓ → ℝ) : Fin n → PaddedTask (ℓ := ℓ) κ → ℝ
  | i, .inl e => if incident i e then t i e else paddingHigh K
  | i, .inr (.inl ⟨c, _⟩) =>
      if i = c.1.1.1 then ((zeroTypeValues K c.2).1 : ℝ)
      else if i = c.1.1.2 then ((zeroTypeValues K c.2).2 : ℝ)
      else paddingHigh K
  | i, .inr (.inr _) => if i = 0 then paddingBeta K else paddingHigh K

/-- The classes within which the padded tasks are permuted: one class for every machine pair,
one singleton class for every core self-loop, and one singleton class for the extra loop. -/
abbrev PaddedClass (n : ℕ) := MachinePair n ⊕ (Fin n ⊕ Unit)

/-- Class labels of padded tasks. -/
def paddedClass {n ℓ K : ℕ} {κ : ReservoirVector n K} : PaddedTask (ℓ := ℓ) κ → PaddedClass n
  | .inl (.inl (p, _)) => .inl p
  | .inl (.inr i) => .inr (.inl i)
  | .inr (.inl ⟨c, _⟩) => .inl c.1
  | .inr (.inr _) => .inr (.inr ())

/-- The symmetrized mechanism on the full padded task set. -/
noncomputable def paddedSymMech {n ℓ K : ℕ} [NeZero n]
    (R : (m : ℕ) → FracMech n (Fin m)) (κ : ReservoirVector n K) :
    FracMech n (PaddedTask (ℓ := ℓ) κ) :=
  symmetrizeGen
    (reindexMech (R (Fintype.card (PaddedTask (ℓ := ℓ) κ))) (Fintype.equivFin _))
    (classPerms paddedClass)

/-- The slice of the padded mechanism to the core tasks, before averaging over `κ`. -/
noncomputable def paddedSlice {n ℓ K : ℕ} [NeZero n]
    (R : (m : ℕ) → FracMech n (Fin m)) (κ : ReservoirVector n K) :
    FracMech n (CoreTask n ℓ) :=
  sliceMech (paddedSymMech R κ) (fun e => Sum.inl e) (paddedInput κ)
    (fun i f => ∃ e, f = Sum.inl e ∧ incident i e)

/-- The finite padded mechanism at Lean stage `K` (paper stage `K+1`). -/
noncomputable def paddedMechanism {n ℓ : ℕ} [NeZero n]
    (R : (m : ℕ) → FracMech n (Fin m)) (K : ℕ) : FracMech n (CoreTask n ℓ) :=
  averageMech (fun κ : ReservoirVector n K => paddedSlice R κ)

end FracTruthSched


