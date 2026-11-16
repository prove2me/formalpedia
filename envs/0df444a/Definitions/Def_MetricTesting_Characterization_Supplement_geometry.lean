-- Prove2me | Definitions.Def_MetricTesting_Characterization_Supplement_geometry
-- name    : MetricTesting_Characterization_Supplement_geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:18:33.997864+00:00
-- url     : https://prove2.me/theorems/21ca1ad7-b67a-40d7-8af0-cbc8bf869369
-- title:
--   Metric and geometric local predicates
-- statement:
--   An input is a symmetric zero-diagonal array of nonnegative real distances on unordered pairs of $n$ labels. The general pseudometric predicate is the published predicate on real-valued pairs, applied to this array; positive and bounded targets retain their stated value sets. On triples the metric condition is
--
--   $$d(i,k)\le d(i,j)+d(j,k).$$
--
--   The bounded ambient set is $[1,C]$, for a real $C>1$. Strict tree targets have positive off-diagonal entries and the four-point condition $d(i,j)+d(k,l)\le\max\{d(i,k)+d(j,l),d(i,l)+d(j,k)\}$ for every four labels, including repetitions. Strict Euclidean targets have positive off-diagonal entries and exact distances $\|x_i-x_j\|_2$ between points of $\mathbb R^d$, with arity $d+3$. Both strict families are defined on positive and nonnegative ambient inputs. Hyperbolic metric targets additionally satisfy the four-point inequality with additive allowance $2\delta$, together with the metric and positivity conditions, at arity four.
--
--   These predicates specify the repair classes independently of any stability or testing claim. Permutation closure includes the identity and changes none of these invariant predicates. Below each arity the published local validity convention is vacuous; it is retained for geometric local families.
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), §2, printed pp. 6–8 (PDF pp. 7–9); Remark 4.12, printed p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_MetricTesting_Characterization_arrays
import Definitions.Def_MetricMinTest_IsPseudometric

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The diagonal is zero; entries on unordered pairs retain exact real values. -/
def entry {Λ : Set NNReal} {n : ℕ} (D : Array Λ n) (i j : Fin n) : ℝ :=
  if h : i = j then 0 else (D ⟨{i,j}, by simp [h]⟩ : NNReal)

def Triangle {Λ : Set NNReal} {n : ℕ} (D : Array Λ n) : Prop :=
  MetricMinTest.IsPseudometric (entry D)

def Positive {Λ : Set NNReal} {n : ℕ} (D : Array Λ n) : Prop :=
  ∀ e, 0 < (D e : NNReal)

/-- Permutation closure supplies a structural invariant API; it includes the identity. -/
def localFamily (k : ℕ) (hk : 2 ≤ k) (Λ : Set NNReal) (hΛ : Λ.Nonempty)
    (R : Array Λ k → Prop) : LocalData where
  k := k
  arity := hk
  values := Λ
  values_nonempty := hΛ
  predicate := {D | ∀ σ : Equiv.Perm (Fin k), R (restrictArray D σ.toEmbedding)}
  invariant := by
    intro D σ
    have comp (B : Array Λ k) (τ υ : Equiv.Perm (Fin k)) :
        restrictArray (restrictArray B τ.toEmbedding) υ.toEmbedding =
          restrictArray B (υ.trans τ).toEmbedding := by
      funext e
      apply congrArg B
      apply Subtype.ext
      simp [edgeMap, Finset.map_map]
    constructor
    · intro h τ
      have hh := h (τ.trans σ.symm)
      simpa only [comp, Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.trans_refl] using hh
    · intro h τ
      rw [comp]
      exact h _

def BoundedValues (C : ℝ) : Set NNReal := {x | 1 ≤ (x : ℝ) ∧ (x : ℝ) ≤ C}
def PositiveValues : Set NNReal := {x | 0 < x}
def NonnegativeValues : Set NNReal := Set.univ

def boundedMetric (C : ℝ) (hC : 1 < C) : LocalData :=
  localFamily 3 (by omega) (BoundedValues C) ⟨1, by simpa [BoundedValues] using le_of_lt hC⟩ Triangle

def positiveMetric : LocalData :=
  localFamily 3 (by omega) PositiveValues ⟨1, by simp [PositiveValues]⟩ Triangle

def pseudoMetric : LocalData :=
  localFamily 3 (by omega) NonnegativeValues ⟨0, Set.mem_univ _⟩ Triangle

/-- Repeated labels include the triangle inequalities in the four-point condition. -/
def FourPoint {Λ : Set NNReal} {n : ℕ} (δ : ℝ) (D : Array Λ n) : Prop :=
  ∀ i j k l, entry D i j + entry D k l ≤
    max (entry D i k + entry D j l) (entry D i l + entry D j k) + 2 * δ

def strictTree (positiveAmbient : Bool) : LocalData :=
  if positiveAmbient then
    localFamily 4 (by omega) PositiveValues ⟨1, by simp [PositiveValues]⟩
      (fun D => Positive D ∧ FourPoint 0 D)
  else localFamily 4 (by omega) NonnegativeValues ⟨0, Set.mem_univ _⟩
      (fun D => Positive D ∧ FourPoint 0 D)

def Euclidean {Λ : Set NNReal} {n : ℕ} (d : ℕ) (D : Array Λ n) : Prop :=
  ∃ x : Fin n → EuclideanSpace ℝ (Fin d), ∀ i j, entry D i j = dist (x i) (x j)

def strictEuclidean (d : ℕ) (positiveAmbient : Bool) : LocalData :=
  if positiveAmbient then
    localFamily (d+3) (by omega) PositiveValues ⟨1, by simp [PositiveValues]⟩
      (fun D => Positive D ∧ Euclidean d D)
  else localFamily (d+3) (by omega) NonnegativeValues ⟨0, Set.mem_univ _⟩
      (fun D => Positive D ∧ Euclidean d D)

def hyperbolic (δ : ℝ) : LocalData :=
  localFamily 4 (by omega) NonnegativeValues ⟨0, Set.mem_univ _⟩
    (fun D => Positive D ∧ Triangle D ∧ FourPoint δ D)

end MetricTesting.Characterization.Supplement


