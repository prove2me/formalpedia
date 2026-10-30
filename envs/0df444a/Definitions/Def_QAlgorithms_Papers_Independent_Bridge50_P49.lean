-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P49
-- name    : QAlgorithms_Papers_Independent_Bridge50_P49
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T09:18:34.760003+00:00
-- url     : https://prove2.me/theorems/9a439dae-9e58-41cd-9b90-f3c3378aaa3d
-- title:
--   Definitions for Sandwiched Rényi Divergence Satisfies Data Processing Inequality
-- statement:
--   The objects the formalized statements of *Sandwiched Rényi Divergence Satisfies Data Processing Inequality* (arXiv:1306.5920) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `reciprocalOrder`: PDF p.5, (12): reciprocal order, including 1/infinity = 0.
--   - `interpolatedOrder`: PDF p.5, (12): harmonic interpolation, including equal infinite endpoints.
--   - `beigiWeightedSchattenNorm`: PDF p.4: weighted Schatten norm on all complex matrices; weights need not have trace one. This differs from Information100.P32.weightedNorm, a fixed norm on three coordinates.
--   - `weightedMapNorm`: PDF p.6, (13): induced norm, with all nonzero complex matrices admissible. Positive-definite weights and orders at least one ensure boundedness. In a zero-dimensional domain the norm is zero (the real supremum of the empty set).
--   - `StripBounded`: PDF p.5: entrywise boundedness on the closed strip, independent of its extension outside.
--   - `StripRegular`: PDF p.5: entrywise holomorphy with continuity from within the closed strip.
--   - `boundaryNorm`: PDF p.5: the boundary supremum is computed from F, not a free upper bound.
--   - `beigiSandwichedDivergence`: PDF p.2, (3), and p.8, (15): natural-log sandwiched divergence. The support guard applies ALSO below order one. The second input may be unnormalized. Dependency50.P35.divergence instead uses bits, trace normalization, and a different support guard. The accepted rawTrace uses support inverses, with zero on the kernel.
--   - `maxDivergence`: PDF pp.2,10: max-relative entropy, the infinite-order endpoint, in natural units.
--   - `orderDivergence`: PDF pp.2,10: finite and infinite orders are distinct cases.
--   - `beigiConditionalRenyiEntropy`: PDF p.2, (4): genuine extended-real infimum over normalized density matrices. Information100.P67.conditionalEntropy is the ordinary von Neumann quantity in bits.
--   - `scaledDivergence`: PDF p.10, Theorem 8: reciprocal-conjugate scaled divergence. The printed order-one endpoint means the continuous scaled value zero; this branch is evaluated before any divergence, including support failure.
--   - `interpolationWeight`: PDF p.10: the uniquely defined interpolation weight for a < b < c.
--   - `beigiRenyiMutualInformation`: PDF p.11, (23): mutual information with the usual value at one. The reference on B ranges over all densities, including correlated references when B itself is a composite register. Dependency50.P19.mutualInformation is only the ordinary order-one quantity in bits, not this order-indexed family.
--   - `purificationOperator`: PDF p.12, (24): the B-operator after the A and C sandwiches and both partial traces. Each Gamma exponent contributes HALF that exponent on each side of the matrix.
--   - `purificationObjective`: PDF p.12, (24): the scalar optimized quantity is the Schatten beta norm.
--   - `groupedProduct`: PDF p.12, Theorem 11: tensor product regrouped as (AA'),(BB').
--   - `ensembleState`: PDF p.12, (25): arbitrary finite mixed-signal ensemble, classical register first.
--   - `beigiRenyiHolevoInformation`: PDF p.12, (25): extended supremum over ALL finite alphabet sizes and mixed signals. Dependency50.P48.holevoInformation is a fixed ensemble value in bits, not a channel supremum.
-- source:
--   Sandwiched Rényi Divergence Satisfies Data Processing Inequality, arXiv:1306.5920v6, https://arxiv.org/abs/1306.5920v6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

/-!
arXiv:1306.5920v6, Beigi, PDF pp.1--12. Natural logarithms throughout.
The independent-paper workflow permits reuse of the pinned accepted-library modules.
Natural entropy and the full tensor-channel action are imported rather than restated.
Beigi-specific names distinguish concepts whose frozen short-name matches differ in
order domain, support convention, optimization domain, or mathematical object.
Only their audited definitions are used, never their sorry-ended results.
The scalar Theorem 1 is recorded as Mathlib reuse in items.json.
No theorem asserts anything about totalized definitions outside its order domain.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P49

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)
open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)
open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower Dominates rawTrace leftMarginal rightMarginal marginalAB marginalAC)

/-- PDF p.5, (12): reciprocal order, including 1/infinity = 0. -/
def reciprocalOrder (p : ℝ≥0∞) : ℝ := (p⁻¹).toReal

/-- PDF p.5, (12): harmonic interpolation, including equal infinite endpoints. -/
def interpolatedOrder (p q : ℝ≥0∞) (theta : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal ((1 - theta) * reciprocalOrder p + theta * reciprocalOrder q))⁻¹

/-- PDF p.4: weighted Schatten norm on all complex matrices; weights need not have trace one.
This differs from Information100.P32.weightedNorm, a fixed norm on three coordinates. -/
def beigiWeightedSchattenNorm {I : Type} [Fintype I] [DecidableEq I]
    (p : ℝ≥0∞) (sigma X : Mat I) : ℝ :=
  schattenNorm p
    (spectralPower sigma (reciprocalOrder p / 2) * X *
      spectralPower sigma (reciprocalOrder p / 2))

/-- PDF p.6, (13): induced norm, with all nonzero complex matrices admissible.
Positive-definite weights and orders at least one ensure boundedness.
In a zero-dimensional domain the norm is zero (the real supremum of the empty set). -/
def weightedMapNorm {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (p q : ℝ≥0∞) (sigma : Mat I) (tau : Mat J)
    (Phi : Mat I →ₗ[ℂ] Mat J) : ℝ :=
  sSup {v : ℝ | ∃ X : Mat I, X ≠ 0 ∧
    v = beigiWeightedSchattenNorm q tau (Phi X) / beigiWeightedSchattenNorm p sigma X}

/-- PDF p.5: entrywise boundedness on the closed strip, independent of its extension outside. -/
def StripBounded {I : Type} (F : ℂ → Mat I) : Prop :=
  ∀ i j, ∃ C : ℝ, ∀ z : ℂ,
    z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 → ‖F z i j‖ ≤ C

/-- PDF p.5: entrywise holomorphy with continuity from within the closed strip. -/
def StripRegular {I : Type} (F : ℂ → Mat I) : Prop :=
  ∀ i j, DiffContOnCl ℂ (fun z => F z i j)
    (Complex.HadamardThreeLines.verticalStrip 0 1)

/-- PDF p.5: the boundary supremum is computed from F, not a free upper bound. -/
def boundaryNorm {I : Type} [Fintype I] [DecidableEq I]
    (F : ℂ → Mat I) (p : ℝ≥0∞) (sigma : Mat I) (k : ℝ) : ℝ :=
  sSup (Set.range fun t : ℝ => beigiWeightedSchattenNorm p sigma (F ((k : ℂ) + (t : ℂ) * Complex.I)))

/-- PDF p.2, (3), and p.8, (15): natural-log sandwiched divergence.
The support guard applies ALSO below order one. The second input may be unnormalized.
Dependency50.P35.divergence instead uses bits, trace normalization, and a different support guard.
The accepted rawTrace uses support inverses, with zero on the kernel. -/
def beigiSandwichedDivergence {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (rho sigma : Mat I) : EReal :=
  if Dominates sigma rho then
    ((1 / (a - 1) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (rawTrace a rho sigma))
  else ⊤

/-- PDF pp.2,10: max-relative entropy, the infinite-order endpoint, in natural units. -/
def maxDivergence {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Mat I) : EReal :=
  sInf {v : EReal | ∃ t : ℝ, v = (t : EReal) ∧
    ((Real.exp t : ℂ) • sigma - rho).PosSemidef}

/-- PDF pp.2,10: finite and infinite orders are distinct cases. -/
def orderDivergence {I : Type} [Fintype I] [DecidableEq I]
    (p : ℝ≥0∞) (rho sigma : Mat I) : EReal :=
  if p = ⊤ then maxDivergence rho sigma else beigiSandwichedDivergence p.toReal rho sigma

/-- PDF p.2, (4): genuine extended-real infimum over normalized density matrices.
Information100.P67.conditionalEntropy is the ordinary von Neumann quantity in bits. -/
def beigiConditionalRenyiEntropy {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (p : ℝ≥0∞) (rho : Mat (A × B)) : EReal :=
  -sInf {v : EReal | ∃ sigma : Mat B, IsDensityMatrix sigma ∧
    v = orderDivergence p rho (Matrix.kronecker (1 : Mat A) sigma)}

/-- PDF p.10, Theorem 8: reciprocal-conjugate scaled divergence.
The printed order-one endpoint means the continuous scaled value zero;
this branch is evaluated before any divergence, including support failure. -/
def scaledDivergence {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (rho sigma : Mat I) : EReal :=
  if a = 1 then 0 else ((1 - 1 / a : ℝ) : EReal) * beigiSandwichedDivergence a rho sigma

/-- PDF p.10: the uniquely defined interpolation weight for a < b < c. -/
def interpolationWeight (a b c : ℝ) : ℝ := (1 / b - 1 / a) / (1 / c - 1 / a)

/-- PDF p.11, (23): mutual information with the usual value at one.
The reference on B ranges over all densities, including correlated references
when B itself is a composite register. Dependency50.P19.mutualInformation is only
the ordinary order-one quantity in bits, not this order-indexed family. -/
def beigiRenyiMutualInformation {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (a : ℝ) (rho : Mat (A × B)) : EReal :=
  if a = 1 then (entropy (leftMarginal rho) + entropy (rightMarginal rho) - entropy rho : ℝ)
  else sInf {v : EReal | ∃ sigma : Mat B, IsDensityMatrix sigma ∧
    v = beigiSandwichedDivergence a rho (Matrix.kronecker (leftMarginal rho) sigma)}

/-- PDF p.12, (24): the B-operator after the A and C sandwiches and both partial traces.
Each Gamma exponent contributes HALF that exponent on each side of the matrix. -/
def purificationOperator {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a : ℝ) (rhoA : Mat A) (R : Mat (A × (B × C))) (tau : Mat C) : Mat B :=
  let K := Matrix.kronecker (spectralPower rhoA (-(1 - 1 / a) / 2))
    (Matrix.kronecker (1 : Mat B) (spectralPower tau ((1 - 1 / a) / 2)))
  fun b d => ∑ i : A, ∑ j : C, (K * R * K) (i, (b, j)) (i, (d, j))

/-- PDF p.12, (24): the scalar optimized quantity is the Schatten beta norm. -/
def purificationObjective {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a b : ℝ) (rhoA : Mat A) (R : Mat (A × (B × C))) (tau : Mat C) : ℝ :=
  schattenNorm (ENNReal.ofReal b) (purificationOperator a rhoA R tau)

/-- PDF p.12, Theorem 11: tensor product regrouped as (AA'),(BB'). -/
def groupedProduct {A B C D : Type} (rho : Mat (A × B)) (eta : Mat (C × D)) :
    Mat ((A × C) × (B × D)) :=
  fun i j => rho (i.1.1, i.2.1) (j.1.1, j.2.1) *
    eta (i.1.2, i.2.2) (j.1.2, j.2.2)

/-- PDF p.12, (25): arbitrary finite mixed-signal ensemble, classical register first. -/
def ensembleState {A : Type} {k : ℕ} (p : Distribution (Fin k))
    (rho : Fin k → Mat A) : Mat (Fin k × A) :=
  fun i j => if i.1 = j.1 then (p.val i.1 : ℂ) * rho i.1 i.2 j.2 else 0

/-- PDF p.12, (25): extended supremum over ALL finite alphabet sizes and mixed signals.
Dependency50.P48.holevoInformation is a fixed ensemble value in bits, not a channel supremum. -/
def beigiRenyiHolevoInformation {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (a : ℝ) (Phi : Superop A B) : EReal :=
  sSup {v : EReal | ∃ (k : ℕ) (p : Distribution (Fin k)) (rho : Fin k → Mat A),
    (∀ x, IsDensityMatrix (rho x)) ∧
      v = beigiRenyiMutualInformation a (idTensorSuperop Phi (ensembleState p rho))}

/-! Sanity checks for the local definition layer. -/

example : reciprocalOrder ⊤ = 0 := by simp [reciprocalOrder]

example (theta : ℝ) : interpolatedOrder ⊤ ⊤ theta = ⊤ := by
  simp [interpolatedOrder, reciprocalOrder]

example {I : Type} [Fintype I] [DecidableEq I] (sigma X : Mat I) :
    beigiWeightedSchattenNorm ⊤ sigma X = specNorm X := by
  simp [beigiWeightedSchattenNorm, reciprocalOrder, spectralPower, schattenNorm]

example {I : Type} [Fintype I] [DecidableEq I] (a : ℝ) (rho sigma : Mat I)
    (h : ¬ Dominates sigma rho) : beigiSandwichedDivergence a rho sigma = ⊤ := by
  simp [beigiSandwichedDivergence, h]

example {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Mat I) :
    scaledDivergence 1 rho sigma = 0 := by simp [scaledDivergence]

example {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Mat I) :
    orderDivergence ⊤ rho sigma = maxDivergence rho sigma := by simp [orderDivergence]

example {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (Psi : Superop C D) (X : Mat (A × C)) :
    tensorChannel (fun _ => (0 : Mat B)) Psi X = 0 := by
  ext i j
  simp [tensorChannel]

end QAlgorithms.Papers.Independent.Bridge50.P49


