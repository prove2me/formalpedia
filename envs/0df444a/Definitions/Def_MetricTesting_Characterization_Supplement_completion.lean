-- Prove2me | Definitions.Def_MetricTesting_Characterization_Supplement_completion
-- name    : MetricTesting_Characterization_Supplement_completion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:19:08.337217+00:00
-- url     : https://prove2.me/theorems/2060cbfb-d4c8-4255-b389-d187e85ad57a
-- title:
--   Specified graphs, cycles, completion and obstruction sequences
-- statement:
--   For a partial array $A$, its specified graph contains exactly the unordered pairs with specified values. A simple cycle is nonmetric when one edge is longer than the sum of the other edges. The operational cycle predicate records distinct cyclic vertices, their specified edges and weights. Exact completion requires a valid total target agreeing with every specified entry. Deleting a set of specified edges turns them into holes.
--
--   For real $C>1$, set
--
--   $$M_C=\prod_{r=4}^{\lceil C\rceil}(r+1),$$
--
--   with empty product one. A packing obstruction is a sequence of arrays on orders $s_j\to\infty$ having packing number at least $\alpha s_j^2$ for some $\alpha>0$ and violation density tending to zero. A completion obstruction is a sequence of locally consistent partial arrays on orders $s_j\to\infty$, with hole density tending to zero and completion distance at least a fixed $\gamma>0$.
--
--   For input and target value sets that differ, cross-value distance minimizes the number of unequal nonnegative real entries before multiplying by $2/n^2$. All uses here have nonempty target classes; the auxiliary minimum has the same total zero fallback outside that domain as the published minimum. These definitions keep obstruction sequences and repair targets independent of their asserted properties.
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), Corollary 3.12, printed p. 12 (PDF p. 13); §5.3, printed pp. 21–24 (PDF pp. 22–25)

import Mathlib
import Definitions.Def_MetricTesting_Characterization_Supplement_geometry
import Definitions.Def_MetricTesting_Characterization_moduli

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The simple graph of specified unordered pairs, with no added connectivity assumption. -/
def specifiedGraph {Λ : Set NNReal} {n : ℕ} (A : PartialArray Λ n) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ ∃ e : Edge n, e.1 = {i,j} ∧ (A e).isSome
  symm := ⟨by
    intro i j h
    exact ⟨Ne.symm h.1, by simpa [Finset.pair_comm] using h.2⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

/-- Cyclic successor; the length is positive at every use in a simple cycle. -/
def cyclicNext {r : ℕ} (hr : 0 < r) (i : Fin r) : Fin r :=
  ⟨(i.val + 1) % r, Nat.mod_lt _ hr⟩

/-- E is the edge set of a simple cycle, with one edge longer than all the rest together. -/
def NonmetricCycle {Λ : Set NNReal} {n : ℕ} (A : PartialArray Λ n)
    (r : ℕ) (E : Finset (Edge n)) : Prop :=
  ∃ (hr : 3 ≤ r) (v : Fin r ↪ Fin n) (e : Fin r → Edge n) (w : Fin r → Λ),
    (∀ i, (e i).1 = {v i, v (cyclicNext (by omega) i)}) ∧
    (∀ i, A (e i) = some (w i)) ∧ E = Finset.univ.image e ∧
    ∃ t : Fin r, (∑ i ∈ Finset.univ.erase t, ((w i : NNReal) : ℝ)) < (w t : NNReal)

def ExactCompletion (F : LocalData) {n : ℕ} (A : PartialArray F.values n) : Prop :=
  ∃ B : Array F.values n, Valid F B ∧ Completes A B

def deleteEdges {Λ : Set NNReal} {n : ℕ} (A : PartialArray Λ n)
    (S : Finset (Edge n)) : PartialArray Λ n := fun e => if e ∈ S then none else A e

def Specified {Λ : Set NNReal} {n : ℕ} (A : PartialArray Λ n) : Finset (Edge n) :=
  Finset.univ.filter fun e => (A e).isSome

/-- Exact product, including the empty-product regime 1<C≤3. -/
def completionFactor (C : ℝ) : ℕ := ∏ r ∈ Finset.Icc 4 ⌈C⌉₊, (r+1)

/-- Operational obstruction sequences, independent of the properties they will refute. -/
def PackingObstruction (F : LocalData) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ s : ℕ → ℕ, Filter.Tendsto s Filter.atTop Filter.atTop ∧
    ∃ D : (j : ℕ) → Array F.values (s j),
      (∀ j, F.k ≤ s j ∧ α * (s j : ℝ)^2 ≤ (packingNumber F (D j) : ℝ)) ∧
      Filter.Tendsto (fun j => violationDensity F (D j)) Filter.atTop (nhds 0)

def CompletionObstruction (F : LocalData) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∃ s : ℕ → ℕ, Filter.Tendsto s Filter.atTop Filter.atTop ∧
    ∃ A : (j : ℕ) → PartialArray F.values (s j),
      (∀ j, F.k ≤ s j ∧ LocallyConsistent F (A j) ∧ γ ≤ completionDistance F (A j)) ∧
      Filter.Tendsto (fun j => ((Holes (A j)).card : ℝ) / (s j : ℝ)^2)
        Filter.atTop (nhds 0)

/-- Agreement is tested after coercion; repair values need not lie in the input alphabet. -/
def crossDiscrepancy {Λ Γ : Set NNReal} {n : ℕ} (D : Array Λ n) (B : Array Γ n) : ℕ :=
  (Finset.univ.filter fun e => (D e : NNReal) ≠ (B e : NNReal)).card

def crossDistance {Λ : Set NNReal} {n : ℕ} (F : LocalData) (D : Array Λ n) : ℝ :=
  2 * (if h : ∃ m : ℕ, ∃ B : Array F.values n, Valid F B ∧ crossDiscrepancy D B = m
    then Nat.find h else 0) / (n : ℝ)^2

end MetricTesting.Characterization.Supplement


