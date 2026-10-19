-- Prove2me | Definitions.Def_OAIE3v2B224
-- name    : OAIE3v2B224
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:26:09.573045+00:00
-- url     : https://prove2.me/theorems/711f4896-0e6d-47bf-9cf9-06e818f0d86f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 229 of 311
-- statement:
--   Definitions bundle 229 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B198`, `OAIE3v2B199`, `OAIE3v2B203`, `OAIE3v2B204` of this split.
--
--   Modules: `Estimates/BoundedNativeDependentApproximations.lean`, `Estimates/CommonDependentWordLayers.lean`, `Estimates/CommonInducedCorrelation.lean`, `Estimates/CommonMarkedMultidegree.lean`, `Estimates/CommonUniformCoefficientCorrections.lean`, `Estimates/CoveredInducedCorrelationFamily.lean`, `Estimates/MarkedEvaluationJointBounds.lean`, `Estimates/MarkedLocalCoefficientValue.lean`, `Estimates/MarkedParameterOrbit.lean`, `Estimates/MarkedShiftGeneratorBounds.lean`, `Estimates/MixedPrimitiveGowers.lean`, `Estimates/UnitVerticalNativeInverseModels.lean`, `Geometry/MarkedDirectionCoordinates.lean`, `Geometry/MarkedLocalObservableMetric.lean`, `Geometry/NormalizedMarkedChart.lean`, `Lattices/CommonAffineOrbitEvaluation.lean`, `Lattices/MarkedDirectionLatticeScale.lean`, `Lattices/RealMarkedAffineShift.lean`, `Linear/CommonFreeSpanBounds.lean`, `Linear/CommonRankCoefficientCorrections.lean`, `Linear/NativeCoefficientKernel.lean`, `Polynomial/LocalPhaseMarkedObservable.lean`, `Polynomial/NormalizedMarkedPhase.lean`, `Polynomial/PhaseBandCoordinateLifts.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B198
import Definitions.Def_OAIE3v2B199
import Definitions.Def_OAIE3v2B203
import Definitions.Def_OAIE3v2B204

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeCoefficientKernel
namespace OAI

section

namespace Erdos3.NativeRankInterval

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

theorem real_rankProjection_abs_bound
    (x : ℝ ⊗[ℚ] (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
    {B : ℝ} (hx : ∀ j, |((pi (I.productModels i)).basis.baseChange ℝ).repr x j| ≤ B)
    (j : Σ _ : Fin 4, Fin W.dim) :
    |(W.fourRankBasis.baseChange ℝ).repr ((I.rankProjection i).toLinearMap.baseChange ℝ x) j| ≤ B := by
  rw [I.real_rankProjection_coordinates i]
  exact hx _

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

theorem projectedRepresentative_slow (hP : 0 ≤ P)
    (E : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (hE : (pi (I.productModels D.index)).filtration.SymbolSlowBound
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1)
      (fun _ => (I.length : ℝ)) (Real.exp P) E) (α : Unit →₀ ℕ) (j : Σ _ : Fin 4, Fin W.dim) :
    |(W.fourRankBasis.baseChange ℝ).repr (D.projectedRepresentative E α) j| ≤
      Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α := by
  apply I.real_rankProjection_abs_bound D.index
  intro k
  apply (pi (I.productModels D.index)).filtration.realSymbolRepresentative_slow_original_coordinates
    D.adapted.basis D.adapted.weight D.adapted.layers (pi (I.productModels D.index)).basis
    (fun _ : Unit => 1) (fun _ => (I.length : ℝ)) (fun _ => by exact_mod_cast I.length_pos) hP
  · simpa only [Fintype.card_fin] using D.adapted_complexity.1.1
  · exact D.forward
  · exact hE

end Erdos3.NativeRankInterval.SunflowerWitness

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRankCoefficientCorrections
namespace OAI

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankRelation

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)}

namespace CommonData

variable {R : NativeRankRelation W out H p q} {P Q : ℝ} (D : R.CommonData P)

theorem horizontalImage_eq (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples)
    (d : Fin (s + 1)) :
    (R.interval ⟨t, D.subset ht⟩).refilteredHorizontalImage
      (D.witness t ht).index (D.witness t ht).subalgebra d.val =
        W.rank.filtration.horizontalImageOfSubmodule (D.spaces d) d.val := by
  rw [(D.witness t ht).horizontalImage_eq, D.projection t ht d]

end CommonData

end NativeRankRelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonUniformCoefficientCorrections
namespace OAI

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankRelation.CommonData

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_common_projected_denominator (D : R.CommonData P) (hP : 0 ≤ P) :
    ∃ (E : R.CommonData ((P + 2) ^ 3 + 2 * P)) (l : ℕ),
      E.quadruples ⊆ D.quadruples ∧ E.spaces = D.spaces ∧ 0 < l ∧
      (l : ℝ) ≤ Real.exp ((P + 2) ^ 3 + P) ∧
      ∀ t (ht : t ∈ E.quadruples), (E.witness t ht).projectedDenominator = l := by
  classical
  let B := (P + 2) ^ 3 + P
  let code (t : ZMod N × ZMod N × ZMod N) :=
    if ht : t ∈ D.quadruples then (D.witness t ht).projectedDenominator else 1
  let A := (Finset.Icc 1 ⌊Real.exp B⌋₊ : Finset ℕ)
  have hcode (t) (ht : t ∈ D.quadruples) : code t ∈ (A : Set ℕ) := by
    simp only [code, dif_pos ht, Finset.mem_coe, A, Finset.mem_Icc]
    exact ⟨(D.witness t ht).projectedDenominator_pos,
      Nat.le_floor ((D.witness t ht).projectedDenominator_bound hP)⟩
  have hcount : ((A : Set ℕ).ncard : ℝ) ≤ Real.exp B := by
    simpa only [Set.ncard_coe_finset, A, Nat.card_Icc, Nat.add_sub_cancel] using
      Nat.floor_le (Real.exp_pos B).le
  obtain ⟨l, hl, T, hTD, hT, hconst, hsize⟩ := exists_exponential_constant_fiber
    D.quadruples D.nonempty code A A.finite_toSet hcode hcount
  have hPP : P ≤ (P + 2) ^ 3 + 2 * P := by
    have hcube : 0 ≤ (P + 2) ^ 3 := by positivity
    linarith
  let E : R.CommonData ((P + 2) ^ 3 + 2 * P) := {
    quadruples := T
    subset := hTD.trans D.subset
    nonempty := hT
    density := by
      calc
        Real.exp (-((P + 2) ^ 3 + 2 * P)) * (Fintype.card (ZMod N) : ℝ) ^ 3 =
            Real.exp (-B) * (Real.exp (-P) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          dsimp only [B]
          ring
        _ ≤ Real.exp (-B) * D.quadruples.card :=
          mul_le_mul_of_nonneg_left D.density (Real.exp_pos _).le
        _ ≤ T.card := hsize
    spaces := D.spaces
    witness := fun t ht => (D.witness t (hTD ht)).mono hPP
    projection := fun t ht d => D.projection t (hTD ht) d }
  have hl' : 1 ≤ l ∧ l ≤ ⌊Real.exp B⌋₊ := Finset.mem_Icc.mp hl
  refine ⟨E, l, hTD, rfl, hl'.1,
    (Nat.cast_le.mpr hl'.2).trans (Nat.floor_le (Real.exp_pos B).le), ?_⟩
  intro t ht
  change ((D.witness t (hTD ht)).mono hPP).projectedDenominator = l
  rw [NativeRankInterval.SunflowerWitness.mono_projectedDenominator]
  simpa only [code, dif_pos (hTD ht)] using hconst t ht

end NativeRankRelation.CommonData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedNativeDependentApproximations
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_sparse_anchors (D : R.CommonData P) : Nonempty D.SparseAnchors := by
  obtain ⟨a, b, c, d, S, hS, hsize, hmem⟩ :=
    exists_simultaneous_four_point_anchors D.quadruples (Real.exp_pos _) D.density
  refine ⟨{
    anchors12 := (a, b)
    anchors13 := (c, d)
    shifts := S
    nonempty := hS
    density := ?_
    relations := hmem }⟩
  simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_neg] using hsize

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonFreeSpanBounds
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem commonFreeSpan_le_coefficientFreeSpan (d : Fin s) :
    D.commonFreeSpan d ≤ D.coefficientFreeSpan d := le_sup_left

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentWordLayers
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

def coefficientLayerIndex : D.CoefficientAlphabet → Fin s := Sum.elim (fun x => x.1) (fun x => x.1)

theorem coefficientWeight_eq_layerIndex (x : D.CoefficientAlphabet) :
    D.coefficientWeight x = (D.coefficientLayerIndex x).val + 1 := by
  cases x <;> rfl

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedShiftGeneratorBounds
namespace OAI

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

theorem markedShiftTranslate_first_order (h : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    markedShiftTranslate F v w marked hw hv t h x - x - ⁅markedShiftDirection F v w marked t h, x⁆ ∈
      markedShiftSecondIdeal F v w marked t := by
  constructor
  · change x.val.right - x.val.right - (⁅markedShiftDirection F v w marked t h, x⁆).val.right = 0
    rw [markedShiftDirection_lie_right, sub_self, sub_zero]
  · change translate h x.val.left.val - x.val.left.val -
      (⁅markedShiftDirection F v w marked t h, x⁆).val.left.val ∈ _
    rw [markedShiftDirection_lie_left]
    exact markedPolynomialLayer_taylorRemainder v w marked h x.property

theorem markedShiftTranslate_quotient (h : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    lieQuotientMap (markedShiftSecondIdeal F v w marked t) (markedShiftTranslate F v w marked hw hv t h x) =
      lieQuotientMap (markedShiftSecondIdeal F v w marked t) x +
        ⁅markedQuotientDirection F v w marked t h, lieQuotientMap (markedShiftSecondIdeal F v w marked t) x⁆ := by
  have he := (lieQuotientMap_eq_zero (markedShiftSecondIdeal F v w marked t)
    (markedShiftTranslate F v w marked hw hv t h x - x - ⁅markedShiftDirection F v w marked t h, x⁆)).mpr
      (markedShiftTranslate_first_order F v w marked hw hv t h x)
  rw [map_sub, map_sub, LieHom.map_lie] at he
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp he)).trans (add_comm _ _)

theorem markedQuotientTranslate_first_order (h : Fin t → ℚ) (x : MarkedShiftQuotient F v w marked t) :
    markedQuotientTranslate F v w marked hw hv t h x = x + ⁅markedQuotientDirection F v w marked t h, x⁆ := by
  obtain ⟨z, rfl⟩ := lieQuotientMap_surjective (markedShiftSecondIdeal F v w marked t) x
  exact markedShiftTranslate_quotient F v w marked hw hv t h z

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NormalizedMarkedPhase
namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)

theorem markedQuotientPhase_direction (a : Fin t → ℚ) :
    markedQuotientPhase F v w marked t (markedQuotientDirection F v w marked t a) = a := rfl

end Erdos3

end

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t m : ℕ)

theorem normalizedMarkedPhase_scaled_direction (hm : 0 < m) (a : Fin t → ℚ) :
    normalizedMarkedPhase F v w marked t m
      ((m : ℚ) • markedQuotientDirection F v w marked t a) = a := by
  rw [normalizedMarkedPhase_apply, map_smul, markedQuotientPhase_direction]
  change (m : ℚ)⁻¹ • ((m : ℚ) • a) = a
  rw [smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast hm.ne' : (m : ℚ) ≠ 0), one_smul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MarkedDirectionCoordinates
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem markedQuotientDirection_coordinate_height (hω : ∀ i, ω i ≤ s) {H Q q : ℕ} (hH : 1 ≤ H)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) H) (f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t))
    (hf : ∀ i j, RationalHeightLE
      (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i) Q)
    (i : Fin t) (j : Fin q) :
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    let B := (a + 1) * (rationalSolveHeight d H * H) ^ a
    RationalHeightLE (f.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j)
      ((d + 1) * (B * Q) ^ d) := by
  have hb := linearMap_coordinate_height e f (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap
    (fun j i => hf i j) (markedShiftDirection F v w marked t (RationalTorus.basis t i))
    (markedShiftDirection_coordinate_height F v w marked t b ω hF hω hH e he i) j
  simp only [Fintype.card_fin] at hb
  exact hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedEvaluationJointBounds
namespace OAI

section

namespace Erdos3

open Module

variable {I ι ν L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hF hω hw hv hH hc hgen in
theorem exists_markedShiftQuotient_bounded_evaluation_data (t : ℕ)
    (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
    (c : Basis ν ℚ (L ⧸ J)) {K : ℕ}
    (hcoef : ∀ i j, RationalHeightLE (c.repr (lieQuotientMap J (b j)) i) K) :
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    ∃ m : ℕ, m ≤ finrank ℚ (markedShiftSecondIdeal F v w marked t).toSubmodule ∧
      ∃ q : ℕ, q ≤ d ∧ ∃ f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t),
        let R := markedEvaluationHeight s (Fintype.card ι) a d m q H K
        (∀ i j k, RationalHeightLE (lieStructureConstants f i j k) R) ∧
        (∀ α : Fin 2 → ℕ,
          ∃ e : Basis (Fin (finrank ℚ (markedShiftQuotientLayer F v w marked t α))) ℚ
              (markedShiftQuotientLayer F v w marked t α),
            ∀ i j, RationalHeightLE (f.repr (e i).val j) R) ∧
        (∀ i j, RationalHeightLE
          (f.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) R) ∧
        (∀ i j, RationalHeightLE (markedQuotientPhase F v w marked t (f j) i) R) ∧
        ∀ i j, RationalHeightLE (c.repr (markedBaseEvaluation F v w marked t J hJ 0 (f j)) i) R := by
  classical
  let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
  let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
  let T := lieTreeHeight (Fintype.card ι) H s
  let U := max T (s + 1)
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  let C := rationalLieStructureHeight a (max U (rationalSolveHeight d U))
  obtain ⟨e, he⟩ := exists_markedShift_bounded_basis F b ω hF v w marked hw hv hH hc hgen hω t
  obtain ⟨m, hm, q, hq, f, hf⟩ := exists_markedShiftQuotient_bounded_coordinates
    F b ω hF v w marked hw hv hH hc hgen hω t e he
  let Q := rationalKernelHeight m B
  let V := max 1 (max C Q)
  let A := max T ((Fintype.card ι + 1) * (T * K) ^ Fintype.card ι)
  let G := markedQuotientHeight s (Fintype.card ι) a d m q H
  let R := markedEvaluationHeight s (Fintype.card ι) a d m q H K
  have hGR : G ≤ R := Nat.le_max_left _ _
  have hT : 1 ≤ T := hH.trans (lieTreeHeight_ge_input _ _ _)
  have hsolve := rationalSolveHeight_pos d hT
  have hB : 1 ≤ B := by
    dsimp [B]
    have := Nat.zero_lt_of_lt hT
    exact Nat.succ_le_iff.mpr (by positivity)
  have hQ : 1 ≤ Q := rationalKernelHeight_pos m hB
  have hC : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) C :=
    markedShiftBasis_structure_height F b ω hF hω v w marked hH hc t e he
  have hproj : ∀ i j, RationalHeightLE
      (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i) Q := hf
  have hmatrix (i j) : RationalHeightLE
      (LinearMap.toMatrix e f (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap i j) V := by
    rw [LinearMap.toMatrix_apply]
    exact (hproj i j).mono ((Nat.le_max_right C Q).trans (Nat.le_max_right 1 _))
  obtain ⟨_, _, _, hstructure⟩ := exists_bounded_lie_quotient_section e f
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)) (lieQuotientMap_surjective _)
    (Nat.le_max_left 1 (max C Q))
    (fun i j k => (hC i j k).mono ((Nat.le_max_left C Q).trans (Nat.le_max_right 1 _))) hmatrix
  have hphaseR : (d + 1) * (rationalSolveHeight q Q * T) ^ d ≤ R := by
    apply le_trans _ (Nat.le_max_right G _)
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.le_max_left _ _)) _)
  have hevalR : (d + 1) *
      (rationalSolveHeight q Q * ((Fintype.card ι + 1) * (T * K) ^ Fintype.card ι)) ^ d ≤ R := by
    apply le_trans _ (Nat.le_max_right G _)
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.le_max_right _ _)) _)
  refine ⟨m, hm, q, hq, f, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j k
    apply RationalHeightLE.mono _ hGR
    change RationalHeightLE _ (max (rationalLieStructureHeight d (max V (rationalSolveHeight q V)))
      ((d + 1) * (B * Q) ^ d))
    apply RationalHeightLE.mono _ (Nat.le_max_left _ _)
    simpa only [Fintype.card_fin] using hstructure i j k
  · intro α
    obtain ⟨e', he'⟩ := exists_markedShiftQuotientLayer_bounded_basis
      F b ω hF v w marked hw hv hH hc hgen hω t e he f hproj α
    refine ⟨e', ?_⟩
    intro i j
    exact (he' i j).mono ((Nat.le_max_right _ _).trans hGR)
  · intro i j
    exact (markedQuotientDirection_coordinate_height F v w marked t b ω hF hω hT
      e he f hproj i j).mono ((Nat.le_max_right _ _).trans hGR)
  · intro i j
    exact (markedQuotientPhase_coordinate_height F v w marked t b ω hF e he f hQ hproj i j).mono hphaseR
  · intro i j
    exact (markedBaseEvaluation_zero_coordinate_height F v w marked t b ω hF e he f hQ hproj
      J hJ c hcoef i j).mono hevalR

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonMarkedMultidegree
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

noncomputable def realMarkedDirection (h : Fin t → ℚ) : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t :=
  rationalLieInclusion (markedQuotientDirection F v w marked t h)

theorem realMarkedTranslate_first_order (h : Fin t → ℚ) (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    (markedQuotientTranslate F v w marked hw hv t h).baseChange ℝ x =
      x + ⁅realMarkedDirection F v w marked t h, x⁆ := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [lie_zero (L := ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) (M := ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
    simp
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, markedQuotientTranslate_first_order, TensorProduct.tmul_add]
    change a ⊗ₜ[ℚ] x + a ⊗ₜ[ℚ] ⁅markedQuotientDirection F v w marked t h, x⁆ =
      a ⊗ₜ[ℚ] x + ⁅(1 : ℝ) ⊗ₜ[ℚ] markedQuotientDirection F v w marked t h, a ⊗ₜ[ℚ] x⁆
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  | add x y hx hy =>
    rw [map_add, hx, hy, LieRing.lie_add]
    abel

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ)

theorem markedQuotientDirection_smul (q : ℚ) (a : Fin t → ℚ) :
    markedQuotientDirection F v w marked t (q • a) =
      q • markedQuotientDirection F v w marked t a :=
  (markedQuotientDirectionLinear F v w marked t).map_smul q a

theorem markedDirection_mem_realLattice_of_smul {k d : ℕ}
    (E : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) k d)
    (q : ℚ) (a : Fin t → ℚ)
    (ha : (⟨q • markedQuotientDirection F v w marked t a⟩ : E.filtration.Group) ∈ E.lattice) :
    (⟨realMarkedDirection F v w marked t (q • a)⟩ : E.RealGroup) ∈ E.realLattice := by
  refine Subgroup.mem_map.mpr ⟨⟨q • markedQuotientDirection F v w marked t a⟩, ha, ?_⟩
  apply NilpotentLieBCHGroup.ext
  exact congrArg rationalLieInclusion (markedQuotientDirection_smul F v w marked t q a).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

theorem rationalMarkedDirectionMap_apply (a : Fin t → ℚ) :
    rationalMarkedDirectionMap F v w marked t a = realMarkedDirection F v w marked t a := rfl

theorem realMarkedParameterDirection_apply (a : Fin t → ℝ) :
    realMarkedParameterDirection F v w marked t a =
      ∑ i, a i • realMarkedDirection F v w marked t (Pi.single i 1) := by
  rw [realMarkedParameterDirection, realDirectionExtension_apply]
  simp only [rationalMarkedDirectionMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun h : Fin t → ℚ => a i • realMarkedDirection F v w marked t h)
  funext j
  by_cases hij : i = j <;> simp [hij, eq_comm]

theorem realMarkedParameterDirection_rat (a : Fin t → ℚ) :
    realMarkedParameterDirection F v w marked t (fun i => (a i : ℝ)) =
      realMarkedDirection F v w marked t a :=
  realDirectionExtension_rat (rationalMarkedDirectionMap F v w marked t) a

theorem markedQuotientDirection_mem_first (a : Fin t → ℚ) :
    markedQuotientDirection F v w marked t a ∈
      markedShiftQuotientLayer F v w marked t (correlationInput 1 0) := by
  refine ⟨markedShiftDirection F v w marked t a, ?_, rfl⟩
  refine ⟨(markedPolynomialLayer v w marked 0 1 0).zero_mem, ?_⟩
  intro h
  change 0 ≠ 0 ∨ 1 < 1 at h
  omega

theorem realMarkedDirection_mem_first (a : Fin t → ℚ) :
    realMarkedDirection F v w marked t a ∈
      (markedShiftMultidegree F v w marked hw hv t).realification.layer (correlationInput 1 0) :=
  Submodule.tmul_mem_baseChange_of_mem 1 (markedQuotientDirection_mem_first F v w marked t a)

theorem realMarkedParameterDirection_mem_first (a : Fin t → ℝ) :
    realMarkedParameterDirection F v w marked t a ∈
      (markedShiftMultidegree F v w marked hw hv t).realification.layer (correlationInput 1 0) := by
  change realMarkedParameterDirection F v w marked t a ∈
    (markedShiftQuotientLayer F v w marked t (correlationInput 1 0)).baseChange ℝ
  rw [realMarkedParameterDirection_apply]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (realMarkedDirection_mem_first F v w marked hw hv t (Pi.single i 1))

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

include hw hv in
theorem realMarkedParameterDirection_lie (a b : Fin t → ℝ) :
    ⁅realMarkedParameterDirection F v w marked t a, realMarkedParameterDirection F v w marked t b⁆ = 0 :=
  marked_first_layer_bracket_zero F v w marked hw hv t
    (realMarkedParameterDirection_mem_first F v w marked hw hv t a)
    (realMarkedParameterDirection_mem_first F v w marked hw hv t b)

include hw hv in
theorem realMarkedParameterDirection_double_lie (a : Fin t → ℝ)
    (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    ⁅realMarkedParameterDirection F v w marked t a,
      ⁅realMarkedParameterDirection F v w marked t a, x⁆⁆ = 0 := by
  let M := (markedShiftMultidegree F v w marked hw hv t).realification
  have ha := realMarkedParameterDirection_mem_first F v w marked hw hv t a
  have hx : x ∈ M.layer 0 := by rw [M.zero_eq_top]; trivial
  have hb := M.lie_mem ha hx
  rw [add_zero] at hb
  exact marked_first_layer_bracket_zero F v w marked hw hv t ha hb

theorem realMarkedParameterElement_mul (a b : Fin t → ℝ) :
    realMarkedParameterElement F v w marked hw hv t a *
      realMarkedParameterElement F v w marked hw hv t b =
        realMarkedParameterElement F v w marked hw hv t (a + b) := by
  apply NilpotentLieBCHGroup.ext
  change lieBCH (s + 1) (realMarkedParameterDirection F v w marked t a)
    (realMarkedParameterDirection F v w marked t b) = _
  rw [lieBCH_eq_add_of_lie_eq_zero
    (markedShiftMultidegree F v w marked hw hv t).realification.ordinary.lowerCentralSeries_eq_bot
    (realMarkedParameterDirection_lie F v w marked hw hv t a b)]
  exact ((realMarkedParameterDirection F v w marked t).map_add a b).symm

theorem realMarkedParameterElement_inv (a : Fin t → ℝ) :
    (realMarkedParameterElement F v w marked hw hv t a)⁻¹ =
      realMarkedParameterElement F v w marked hw hv t (-a) := by
  apply NilpotentLieBCHGroup.ext
  exact ((realMarkedParameterDirection F v w marked t).map_neg a).symm

theorem realMarkedParameterElement_conjugation (hs : 1 ≤ s) (a : Fin t → ℝ)
    (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    conjugationCoord (realMarkedParameterElement F v w marked hw hv t a) x =
      x + ⁅realMarkedParameterDirection F v w marked t a, x⁆ :=
  conjugationCoord_eq_add_lie (by omega) _ x
    (realMarkedParameterDirection_double_lie F v w marked hw hv t a x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MarkedDirectionLatticeScale
namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r k d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ) (E : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) k d)

theorem exists_marked_direction_lattice_scale {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hgrid : (E.grid : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (E.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 3) ^ 3) ∧
      ∀ a : Fin t → ℤ,
        (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
          E.filtration.Group) ∈ E.lattice := by
  have hp1 : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  obtain ⟨m, hm, hmb, hmem⟩ := E.exists_direction_lattice_scale_with_budget (RationalTorus.basis t)
    (markedQuotientDirectionLinear F v w marked t)
    (p := p + 1) (hp.trans hp1) (hd.trans hp1) (ht.trans hp1)
    (hgrid.trans (Real.exp_le_exp.mpr hp1)) (ceil_exp_le_exp_add_one hp)
    (fun i j => rationalHeightLE_ceil_exp (hdir i j))
  refine ⟨m, hm, ?_, ?_⟩
  · simpa only [add_assoc, show (1 : ℝ) + 2 = 3 by norm_num] using hmb
  · intro a
    exact hmem (fun i => (a i : ℚ))
      ⟨a, fun i => congrFun (RationalTorus.basis_equivFun t (fun j => (a j : ℚ))) i⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonAffineOrbitEvaluation
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

variable (t l : ℕ)
  (c : ∀ j : Fin s, (markedPolynomialLayer (σ := Fin t) v w marked (j.val + 1) 0 l).baseChange ℝ)
  (d : ∀ j : Fin s, (markedPolynomialLayer (σ := Fin t) v w marked (j.val + 1) 1 l).baseChange ℝ)

noncomputable def realMarkedAffineMixedOrbit :
    (markedShiftMultidegree F v w marked hw hv t).realification.PolynomialOrbit :=
  (markedShiftMultidegree F v w marked hw hv t).realification.affineMixedOrbit
    (fun j => realMarkedQuotientCoefficient F v w marked hw hv t (j.val + 1) 0 l (c j))
    (fun j => realMarkedQuotientCoefficient F v w marked hw hv t (j.val + 1) 1 l (d j))
    (fun j => realMarkedPolynomialLift_quotient_mem F v w marked hw hv t (j.val + 1) 0 l (c j))
    (fun j => realMarkedPolynomialLift_quotient_mem F v w marked hw hv t (j.val + 1) 1 l (d j))

theorem realMarkedAffineMixedOrbit_eval (h n : ℤ) :
    ((markedShiftMultidegree F v w marked hw hv t).realification.polynomialOrbitEval
      (correlationInput h n) (realMarkedAffineMixedOrbit F v w marked hw hv t l c d)).coord =
        ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
          (realMarkedQuotientCoefficient F v w marked hw hv t (j.val + 1) 0 l (c j) +
          (h : ℚ) • realMarkedQuotientCoefficient F v w marked hw hv t (j.val + 1) 1 l (d j)) :=
  MultidegreeLieFiltration.affineMixedOrbit_eval _ _ _ _ _ (correlationInput h n)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedParameterOrbit
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

noncomputable def realMarkedParameterOrbit (b a : Fin t → ℝ) :
    (markedShiftMultidegree F v w marked hw hv t).realification.PolynomialOrbit :=
  (markedShiftMultidegree F v w marked hw hv t).realification.polynomialOrbitOfLog
    (monomial 0 (realMarkedParameterDirection F v w marked t b) +
      monomial (correlationExponent 1 0) (realMarkedParameterDirection F v w marked t a)) (by
        apply (markedShiftMultidegree F v w marked hw hv t).realification.adaptedSubmodule.add_mem
        · apply MultidegreeLieFiltration.monomial_mem_adaptedSubmodule
          change _ ∈ (markedShiftMultidegree F v w marked hw hv t).realification.layer 0
          rw [MultidegreeLieFiltration.zero_eq_top]
          trivial
        · apply MultidegreeLieFiltration.monomial_mem_adaptedSubmodule
          simpa only [correlationExponent_apply] using
            realMarkedParameterDirection_mem_first F v w marked hw hv t a)

theorem realMarkedParameterOrbit_eval (b a : Fin t → ℝ) (h n : ℤ) :
    (markedShiftMultidegree F v w marked hw hv t).realification.polynomialOrbitEval
      (correlationInput h n) (realMarkedParameterOrbit F v w marked hw hv t b a) =
        realMarkedParameterElement F v w marked hw hv t (b + (h : ℝ) • a) := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun i => ((correlationInput h n i : ℤ) : ℚ))
    (monomial 0 (realMarkedParameterDirection F v w marked t b) +
      monomial (correlationExponent 1 0) (realMarkedParameterDirection F v w marked t a)) =
        realMarkedParameterDirection F v w marked t (b + (h : ℝ) • a)
  rw [map_add, eval_correlation_monomial, eval_monomial]
  simp only [Finsupp.prod_zero_index, one_smul, pow_one, pow_zero, mul_one]
  change realMarkedParameterDirection F v w marked t b +
    (h : ℚ) • realMarkedParameterDirection F v w marked t a =
      realMarkedParameterDirection F v w marked t (b + (h : ℝ) • a)
  rw [map_add, map_smul]
  apply congrArg (realMarkedParameterDirection F v w marked t b + ·)
  simpa only [Rat.cast_intCast] using
    (Rat.cast_smul_eq_qsmul ℝ (h : ℚ) (realMarkedParameterDirection F v w marked t a)).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RealMarkedAffineShift
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

theorem realMarkedAffineShift_quotient (a : Fin t → ℝ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ
        (realMarkedAffineShift F v w marked hw hv t a p) =
      (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ p +
        ⁅realMarkedParameterDirection F v w marked t a,
          (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ p⁆ := by
  let q := (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ
  have hb : ⁅realMarkedParameterDirection F v w marked t a, q p⁆ =
      ∑ i, a i • ⁅realMarkedDirection F v w marked t (Pi.single i 1), q p⁆ := by
    apply (congrArg (fun z : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t => ⁅z, q p⁆)
      (realMarkedParameterDirection_apply F v w marked t a)).trans
    apply (sum_lie Finset.univ
      (fun i => a i • realMarkedDirection F v w marked t (Pi.single i 1)) (q p)).trans
    apply Finset.sum_congr rfl
    intro i _
    exact smul_lie (R := ℝ) (a i) (realMarkedDirection F v w marked t (Pi.single i 1)) (q p)
  calc
    q (realMarkedAffineShift F v w marked hw hv t a p) = q p +
        ∑ i, a i • (q ((markedShiftTranslate F v w marked hw hv t (Pi.single i 1)).baseChange ℝ p) - q p) := by
      rw [realMarkedAffineShift_apply F v w marked hw hv t a p]
      simp only [map_add, map_sum, map_smul, map_sub]
    _ = q p + ∑ i, a i • ⁅realMarkedDirection F v w marked t (Pi.single i 1), q p⁆ := by
      apply congrArg (q p + ·)
      apply Finset.sum_congr rfl
      intro i _
      have he := (realMarkedTranslate_quotient F v w marked hw hv t (Pi.single i 1) p).trans
        (realMarkedTranslate_first_order F v w marked hw hv t (Pi.single i 1) (q p))
      rw [he, add_sub_cancel_left]
    _ = _ := congrArg (q p + ·) hb.symm

theorem realMarkedAffineShift_conjugation (hs : 1 ≤ s) (a : Fin t → ℝ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    conjugationCoord (realMarkedParameterElement F v w marked hw hv t a)
        ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ p) =
      (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ
        (realMarkedAffineShift F v w marked hw hv t a p) :=
  (realMarkedParameterElement_conjugation F v w marked hw hv t hs a _).trans
    (realMarkedAffineShift_quotient F v w marked hw hv t a p).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LocalPhaseMarkedObservable
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ) (e : Basis (Fin d) ℚ (MarkedShiftQuotient F v w marked t))

theorem realMarkedParameterDirection_coordinate (a : Fin t → ℝ) (j : Fin d) :
    (e.baseChange ℝ).repr (realMarkedParameterDirection F v w marked t a) j =
      ∑ i, a i * (e.repr (markedQuotientDirection F v w marked t (Pi.single i 1)) j : ℝ) := by
  apply (congrArg (fun z => (e.baseChange ℝ).repr z j)
    (realMarkedParameterDirection_apply F v w marked t a)).trans
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    realMarkedDirection, rationalLieInclusion_coordinates]

theorem realMarkedParameterDirection_coordinate_le (a : Fin t → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (ha : ∀ i, |a i| ≤ A)
    (he : ∀ i j, |(e.repr (markedQuotientDirection F v w marked t (Pi.single i 1)) j : ℝ)| ≤ B)
    (j : Fin d) :
    |(e.baseChange ℝ).repr (realMarkedParameterDirection F v w marked t a) j| ≤ (t : ℝ) * A * B := by
  rw [realMarkedParameterDirection_coordinate]
  calc
    _ ≤ ∑ i, |a i * (e.repr (markedQuotientDirection F v w marked t (Pi.single i 1)) j : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin t, A * B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (ha i) (he i j) (abs_nonneg _) hA
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedMarkedChart
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t m : ℕ)

theorem normalizedMarkedPhase_real_parameter (a : Fin t → ℝ) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (realMarkedParameterDirection F v w marked t a) = fun i => (m : ℝ)⁻¹ * a i := by
  classical
  have hsingle (j i : Fin t) :
      torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
        (realMarkedDirection F v w marked t (Pi.single j 1)) i =
          (m : ℝ)⁻¹ * (if j = i then 1 else 0) := by
    change torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      ((1 : ℝ) ⊗ₜ[ℚ] markedQuotientDirection F v w marked t (Pi.single j 1)) i = _
    rw [torusPhaseLinear_tmul, _root_.one_mul, normalizedMarkedPhase_apply,
      markedQuotientPhase_direction]
    change (((m : ℚ)⁻¹ * (Pi.single j (1 : ℚ) : Fin t → ℚ) i : ℚ) : ℝ) = _
    by_cases hji : j = i
    · subst j
      simp
    · have hij : i ≠ j := Ne.symm hji
      simp [hji, hij]
  rw [realMarkedParameterDirection_apply, map_sum]
  funext i
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, hsingle]
  simp [mul_comm]

theorem normalizedMarkedPhase_real_scaled_parameter (hm : 0 < m) (a : Fin t → ℝ) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (realMarkedParameterDirection F v w marked t ((m : ℝ) • a)) = a := by
  rw [normalizedMarkedPhase_real_parameter]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0), _root_.one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedLocalCoefficientValue
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t m : ℕ)
  (E : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)

noncomputable def normalizedMarkedRetraction (g : E.RealGroup) : E.RealGroup :=
  realMarkedParameterElement F v w marked hw hv t
    ((m : ℝ) • -(torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord)) * g

theorem normalizedMarkedRetraction_phase (hm : 0 < m) (g : E.RealGroup) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (normalizedMarkedRetraction F v w marked hw hv t m E g).coord = 0 := by
  unfold normalizedMarkedRetraction
  rw [torusPhaseLinear_mul E]
  change torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
    (realMarkedParameterDirection F v w marked t
      ((m : ℝ) • -(torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord))) +
        torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord = 0
  rw [normalizedMarkedPhase_real_scaled_parameter F v w marked t m hm]
  exact neg_add_cancel _

theorem normalizedMarkedRetraction_pure (hm : 0 < m) (g : E.RealGroup) :
    (normalizedMarkedRetraction F v w marked hw hv t m E g).coord ∈
      (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule.baseChange ℝ :=
  (normalizedMarkedPhase_real_eq_zero_iff F v w marked t m hm _).mp
    (normalizedMarkedRetraction_phase F v w marked hw hv t m E hm g)

theorem normalizedMarkedRetraction_scaled_parameter (hm : 0 < m) (a : Fin t → ℝ) (g : E.RealGroup)
    (hg : torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord = 0) :
    normalizedMarkedRetraction F v w marked hw hv t m E
      (realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • a) * g) = g := by
  have hphase : torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • a) * g).coord = a := by
    rw [torusPhaseLinear_mul E, hg, add_zero]
    exact normalizedMarkedPhase_real_scaled_parameter F v w marked t m hm a
  unfold normalizedMarkedRetraction
  rw [hphase, smul_neg, ← realMarkedParameterElement_inv]
  exact inv_mul_cancel_left _ _

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e u : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t m : ℕ) (hm : 0 < m)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)

noncomputable def normalizedMarkedPureRetraction (g : D.RealGroup) :
    realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t) :=
  ⟨normalizedMarkedRetraction F v w marked hw hv t m D g,
    normalizedMarkedRetraction_pure F v w marked hw hv t m D hm g⟩

variable (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
  (E : RationalFilteredNilmanifold (L ⧸ J) u e)
  (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
    (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)

noncomputable def markedLocalCoefficientValue (V : E.Space → ℂ) (g : D.RealGroup) : ℂ :=
  V (markedPureSpaceMap F v w marked t D J hJ E 0 hmap
    (QuotientGroup.mk (normalizedMarkedPureRetraction F v w marked hw hv t m hm D g)))

theorem markedLocalCoefficientValue_apply (V : E.Space → ℂ) (g : D.RealGroup) :
    markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g =
      V (QuotientGroup.mk (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ
        (normalizedMarkedRetraction F v w marked hw hv t m D g).coord⟩ : E.RealGroup)) := rfl

theorem markedLocalCoefficientValue_scaled_parameter (V : E.Space → ℂ) (a : Fin t → ℝ) (g : D.RealGroup)
    (hg : torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord = 0) :
    markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V
      (realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • a) * g) =
      V (QuotientGroup.mk (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ g.coord⟩ : E.RealGroup)) := by
  rw [markedLocalCoefficientValue_apply, normalizedMarkedRetraction_scaled_parameter F v w marked hw hv t m D hm a g hg]

theorem markedLocalCoefficientValue_eq_on_small_cosets
    (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice →
      IntegralVector (normalizedMarkedPhase F v w marked t m z.coord))
    (V : E.Space → ℂ) (g h : D.RealGroup)
    (hg : ∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord i| ≤ 1 / 4)
    (hh : ∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) h.coord i| ≤ 1 / 4)
    (heq : (QuotientGroup.mk g : D.Space) = QuotientGroup.mk h) :
    markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g =
      markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V h := by
  let φ := normalizedMarkedPhase F v w marked t m
  let R := normalizedMarkedPureRetraction F v w marked hw hv t m hm D
  have hph : torusPhaseLinear φ g.coord = torusPhaseLinear φ h.coord :=
    torusPhaseLinear_eq_of_small D φ hphase g h hg hh heq
  have hdiff : (R g)⁻¹ * R h ∈ D.realLattice.comap
      (realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (markedQuotientPolynomialAlgebra F v w marked t)).subtype := by
    change (normalizedMarkedRetraction F v w marked hw hv t m D g)⁻¹ *
      normalizedMarkedRetraction F v w marked hw hv t m D h ∈ D.realLattice
    have hcalc : (normalizedMarkedRetraction F v w marked hw hv t m D g)⁻¹ *
        normalizedMarkedRetraction F v w marked hw hv t m D h = g⁻¹ * h := by
      dsimp only [φ] at hph
      unfold normalizedMarkedRetraction
      rw [hph]
      group
    rw [hcalc]
    exact QuotientGroup.eq.mp heq
  have hq : (QuotientGroup.mk (R g) : _ ⧸ D.realLattice.comap
      (realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (markedQuotientPolynomialAlgebra F v w marked t)).subtype) = QuotientGroup.mk (R h) :=
    QuotientGroup.eq.mpr hdiff
  exact congrArg (fun x => V (markedPureSpaceMap F v w marked t D J hJ E 0 hmap x)) hq

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MarkedLocalObservableMetric
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t m : ℕ) (e : Basis (Fin d) ℚ (MarkedShiftQuotient F v w marked t))

theorem realMarkedParameterDirection_coordinate_norm_le {p : ℝ}
    (ht : (t : ℝ) ≤ p)
    (hdir : ∀ i j, rationalLogHeight
      (e.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (a : Fin t → ℝ) :
    ‖(e.baseChange ℝ).equivFun (realMarkedParameterDirection F v w marked t a)‖ ≤
      Real.exp (2 * p) * ‖a‖ := by
  have hentries (i : Fin t) (j : Fin d) :
      |(e.repr (markedQuotientDirection F v w marked t (Pi.single i 1)) j : ℝ)| ≤ Real.exp p := by
    have hi : (RationalTorus.basis t i : Fin t → ℚ) = Pi.single i 1 := Pi.basisFun_apply ℚ (Fin t) i
    have h := hdir i j
    rw [hi] at h
    exact (rational_abs_real_le_numerator _).trans ((rationalLogHeight_le_iff _ _).mp h).1
  have hnorm : ‖(e.baseChange ℝ).equivFun (realMarkedParameterDirection F v w marked t a)‖ ≤
      (t : ℝ) * ‖a‖ * Real.exp p := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    exact realMarkedParameterDirection_coordinate_le F v w marked t e a (norm_nonneg _)
      (fun i => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm a i) hentries j
  apply hnorm.trans
  have ht' : (t : ℝ) ≤ Real.exp p := ht.trans (by linarith [Real.add_one_le_exp p])
  calc
    (t : ℝ) * ‖a‖ * Real.exp p ≤ Real.exp p * ‖a‖ * Real.exp p := by gcongr
    _ = Real.exp (2 * p) * ‖a‖ := by rw [show 2 * p = p + p by ring, Real.exp_add]; ring

noncomputable def markedPhaseRemovalLinear :
    (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) →ₗ[ℝ]
      (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
  (realMarkedParameterDirection F v w marked t).comp
    ((m : ℝ) • (-torusPhaseLinear (normalizedMarkedPhase F v w marked t m)))

theorem markedPhaseRemovalLinear_apply (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    markedPhaseRemovalLinear F v w marked t m x =
      realMarkedParameterDirection F v w marked t
        ((m : ℝ) • -(torusPhaseLinear (normalizedMarkedPhase F v w marked t m) x)) := rfl

theorem markedPhaseRemovalLinear_coordinate_norm_le {p : ℝ}
    (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (e.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (e j) i) ≤ p)
    (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    ‖(e.baseChange ℝ).equivFun (markedPhaseRemovalLinear F v w marked t m x)‖ ≤
      Real.exp (5 * p) * ‖(e.baseChange ℝ).equivFun x‖ := by
  rw [markedPhaseRemovalLinear_apply]
  apply (realMarkedParameterDirection_coordinate_norm_le F v w marked t e ht hdir _).trans
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg m), norm_neg]
  calc
    Real.exp (2 * p) * ((m : ℝ) * ‖torusPhaseLinear (normalizedMarkedPhase F v w marked t m) x‖) ≤
        Real.exp (2 * p) * (Real.exp p * (Real.exp (2 * p) * ‖(e.baseChange ℝ).equivFun x‖)) := by
      gcongr
      exact normalizedMarkedPhase_coordinate_norm_le F v w marked t m e hd hphase x
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring

theorem markedPhaseRemovalLinear_coordinate_dist_le {p : ℝ}
    (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (e.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (e j) i) ≤ p)
    (x y : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    dist ((e.baseChange ℝ).equivFun (markedPhaseRemovalLinear F v w marked t m x))
      ((e.baseChange ℝ).equivFun (markedPhaseRemovalLinear F v w marked t m y)) ≤
      Real.exp (5 * p) * dist ((e.baseChange ℝ).equivFun x) ((e.baseChange ℝ).equivFun y) := by
  simpa only [map_sub, ← dist_eq_norm] using
    markedPhaseRemovalLinear_coordinate_norm_le F v w marked t m e hd ht hm hdir hphase (x - y)

variable (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)

theorem normalizedMarkedRetraction_coord (g : D.RealGroup) :
    (normalizedMarkedRetraction F v w marked hw hv t m D g).coord =
      lieBCH (s + 1) (markedPhaseRemovalLinear F v w marked t m g.coord) g.coord := rfl

theorem normalizedMarkedRetraction_coordinate_dist_le {p B : ℝ} {H : ℕ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (hB : 1 ≤ B) (g h : D.RealGroup)
    (hg : ‖(D.basis.baseChange ℝ).equivFun g.coord‖ ≤ B)
    (hh : ‖(D.basis.baseChange ℝ).equivFun h.coord‖ ≤ B) :
    dist ((D.basis.baseChange ℝ).equivFun (normalizedMarkedRetraction F v w marked hw hv t m D g).coord)
      ((D.basis.baseChange ℝ).equivFun (normalizedMarkedRetraction F v w marked hw hv t m D h).coord) ≤
      (bchBoxCoordinateBound (s + 1) d H (Real.exp (5 * p) * B) * Real.exp (5 * p)) *
        dist ((D.basis.baseChange ℝ).equivFun g.coord) ((D.basis.baseChange ℝ).equivFun h.coord) := by
  let A := Real.exp (5 * p)
  have hA : 1 ≤ A := Real.one_le_exp (by positivity)
  have hBA : B ≤ A * B := by nlinarith
  have hbox (x : D.RealGroup) (hx : ‖(D.basis.baseChange ℝ).equivFun x.coord‖ ≤ B) :
      ‖(D.basis.baseChange ℝ).equivFun (markedPhaseRemovalLinear F v w marked t m x.coord)‖ ≤ A * B :=
    (markedPhaseRemovalLinear_coordinate_norm_le F v w marked t m D.basis hd ht hm hdir hphase x.coord).trans
      (mul_le_mul_of_nonneg_left hx (Real.exp_nonneg _))
  rw [normalizedMarkedRetraction_coord, normalizedMarkedRetraction_coord, mul_assoc]
  have hbch := lieBCH_pair_coordinate_dist_le (s := s + 1)
    (D.basis.baseChange ℝ) (lieStructureConstants D.basis)
    (fun i j k => (realLieBasis_structure D.basis i j k).symm) hc
    _ _ _ _ (hB.trans hBA) (by positivity)
    (hbox g hg) (hg.trans hBA) (hbox h hh) (hh.trans hBA)
    (markedPhaseRemovalLinear_coordinate_dist_le F v w marked t m D.basis hd ht hm hdir hphase _ _)
    (le_mul_of_one_le_left dist_nonneg hA)
  simpa only [Fintype.card_fin] using hbch

theorem normalizedMarkedRetraction_coordinate_norm_le {p B : ℝ} {H : ℕ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (hB : 1 ≤ B) (g : D.RealGroup)
    (hg : ‖(D.basis.baseChange ℝ).equivFun g.coord‖ ≤ B) :
    ‖(D.basis.baseChange ℝ).equivFun (normalizedMarkedRetraction F v w marked hw hv t m D g).coord‖ ≤
      (bchBoxCoordinateBound (s + 1) d H (Real.exp (5 * p) * B) * Real.exp (5 * p)) * B := by
  have hzero : normalizedMarkedRetraction F v w marked hw hv t m D 1 = 1 := by
    apply NilpotentLieBCHGroup.ext
    rw [normalizedMarkedRetraction_coord, coord_one, map_zero,
      lieBCH_zero_left D.filtration.realification.lowerCentralSeries_eq_bot]
  have h := normalizedMarkedRetraction_coordinate_dist_le F v w marked t m hw hv D
    hp hd ht hm hdir hphase hc hB g 1 hg (by simpa using (show (0 : ℝ) ≤ B by linarith))
  rw [hzero, coord_one, map_zero, dist_zero_right, dist_zero_right] at h
  exact h.trans (mul_le_mul_of_nonneg_left hg (mul_nonneg
    (bchBoxCoordinateBound_nonneg _ _ _ (mul_nonneg (Real.exp_nonneg _) (by linarith))) (Real.exp_nonneg _)))

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e u : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t m : ℕ) (hm : 0 < m)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
  (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
  (E : RationalFilteredNilmanifold (L ⧸ J) u e)
  (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
    (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)

theorem markedLocalCoefficientValue_norm_le (V : E.Space → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1) (g : D.RealGroup) :
    ‖markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g‖ ≤ 1 := hV _

variable [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ J))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ J))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ J))] [T2Space (ℝ ⊗[ℚ] (L ⧸ J))]

theorem markedLocalCoefficientValue_coordinate_dist_le {p : ℝ} {H Ht : ℕ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hmp : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p)
    (heval : ∀ i j, rationalLogHeight (E.basis.repr
      (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤ p)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (hct : ∀ i j k, RationalHeightLE (lieStructureConstants E.basis i j k) Ht)
    (B ℓ : ℝ≥0) (hB : 1 ≤ B) (V : E.Space → ℂ)
    (hV : letI := E.metricSpace; LipschitzWith ℓ V)
    (g h : D.RealGroup)
    (hg : ‖(D.basis.baseChange ℝ).equivFun g.coord‖ ≤ B)
    (hh : ‖(D.basis.baseChange ℝ).equivFun h.coord‖ ≤ B) :
    dist (markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g)
      (markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V h) ≤
        markedLocalBoxConstant s d H u e Ht p B ℓ *
          dist ((D.basis.baseChange ℝ).equivFun g.coord) ((D.basis.baseChange ℝ).equivFun h.coord) := by
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := E.metricSpace
  let q := markedBaseEvaluation F v w marked t J hJ 0
  let a (x : D.RealGroup) : E.RealGroup :=
    ⟨q.baseChange ℝ (normalizedMarkedRetraction F v w marked hw hv t m D x).coord⟩
  let R := markedRetractionBoxConstant s d H p B
  let T := markedEvaluationBoxRadius s d H p B
  let Δ := dist ((D.basis.baseChange ℝ).equivFun g.coord) ((D.basis.baseChange ℝ).equivFun h.coord)
  have hT : 1 ≤ T := by
    dsimp only [T, markedEvaluationBoxRadius]
    exact le_add_of_nonneg_left (by positivity)
  have hB' : (1 : ℝ) ≤ B := hB
  have hnorm (x : D.RealGroup) (hx : ‖(D.basis.baseChange ℝ).equivFun x.coord‖ ≤ B) :
      ‖(E.basis.baseChange ℝ).equivFun (a x).coord‖ ≤ T := by
    have hr := normalizedMarkedRetraction_coordinate_norm_le F v w marked t m hw hv D
      hp hd ht hmp hdir hphase hc hB' x hx
    have he := scalarExtension_coordinate_norm_le D.basis E.basis q
      (by simpa only [Fintype.card_fin] using hd) heval
      (normalizedMarkedRetraction F v w marked hw hv t m D x).coord
    change ‖(E.basis.baseChange ℝ).equivFun (a x).coord‖ ≤
      Real.exp (2 * p) * (R : ℝ) * B + 1
    calc
      _ ≤ Real.exp (2 * p) * ‖(D.basis.baseChange ℝ).equivFun
          (normalizedMarkedRetraction F v w marked hw hv t m D x).coord‖ := he
      _ ≤ Real.exp (2 * p) * ((R : ℝ) * B) := mul_le_mul_of_nonneg_left hr (Real.exp_nonneg _)
      _ ≤ _ := by ring_nf; linarith
  have hevaldist : dist ((E.basis.baseChange ℝ).equivFun (a g).coord)
      ((E.basis.baseChange ℝ).equivFun (a h).coord) ≤ Real.exp (2 * p) * (R : ℝ) * Δ := by
    have hr := normalizedMarkedRetraction_coordinate_dist_le F v w marked t m hw hv D
      hp hd ht hmp hdir hphase hc hB' g h hg hh
    have he := scalarExtension_coordinate_dist_le D.basis E.basis q
      (by simpa only [Fintype.card_fin] using hd) heval
      (normalizedMarkedRetraction F v w marked hw hv t m D g).coord
      (normalizedMarkedRetraction F v w marked hw hv t m D h).coord
    exact he.trans ((mul_le_mul_of_nonneg_left hr (Real.exp_nonneg _)).trans_eq (mul_assoc _ _ _).symm)
  have hgroup : dist (a g) (a h) ≤ bchBoxMetricConstant u e Ht T * (Real.exp (2 * p) * (R : ℝ) * Δ) := by
    have hb := dist_le_bchBoxMetricConstant (E.basis.baseChange ℝ) (lieStructureConstants E.basis)
      (fun i j k => (realLieBasis_structure E.basis i j k).symm) hct T hT
      (show 0 ≤ Real.exp (2 * p) * (R : ℝ) * Δ by dsimp [Δ]; positivity) (a g) (a h)
      (fun i => by
        calc
          _ ≤ ‖(E.basis.baseChange ℝ).equivFun (a g).coord‖ := by
            simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using
              norm_le_pi_norm ((E.basis.baseChange ℝ).equivFun (a g).coord) i
          _ ≤ T := hnorm g hg)
      (fun i => by
        calc
          _ ≤ ‖(E.basis.baseChange ℝ).equivFun (a h).coord‖ := by
            simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using
              norm_le_pi_norm ((E.basis.baseChange ℝ).equivFun (a h).coord) i
          _ ≤ T := hnorm h hh)
      (fun i => by
        calc
          _ ≤ dist ((E.basis.baseChange ℝ).equivFun (a g).coord)
              ((E.basis.baseChange ℝ).equivFun (a h).coord) := by
            simpa only [Real.dist_eq, Basis.equivFun_apply] using
              dist_le_pi_dist ((E.basis.baseChange ℝ).equivFun (a g).coord)
                ((E.basis.baseChange ℝ).equivFun (a h).coord) i
          _ ≤ _ := hevaldist)
    simpa only [Fintype.card_fin] using hb
  have hproj := quotientMetricSpace_lipschitz_mk (E.basis.baseChange ℝ) E.realLattice E.realLattice_closed_discrete.1
  have hvalue := (hV.comp hproj).dist_le_mul (a g) (a h)
  simp only [Function.comp_apply, mul_one] at hvalue
  change dist (V (QuotientGroup.mk (a g))) (V (QuotientGroup.mk (a h))) ≤ _
  apply hvalue.trans
  apply (mul_le_mul_of_nonneg_left hgroup ℓ.coe_nonneg).trans_eq
  change (ℓ : ℝ) * ((bchBoxMetricConstant u e Ht T : ℝ) * (Real.exp (2 * p) * (R : ℝ) * Δ)) =
    (((ℓ : ℝ) * (bchBoxMetricConstant u e Ht T : ℝ) * Real.exp (2 * p)) * (R : ℝ)) * Δ
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PhaseBandCoordinateLifts
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t m : ℕ)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)

theorem realMarkedParameterElement_scaled_integer_mem
    (hdir : ∀ a : Fin t → ℤ,
      (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
        D.filtration.Group) ∈ D.lattice) (a : Fin t → ℤ) :
    (realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • (fun i => (a i : ℝ))) :
      D.RealGroup) ∈ D.realLattice := by
  have h := markedDirection_mem_realLattice_of_smul F v w marked t D (m : ℚ)
    (fun i => (a i : ℚ)) (hdir a)
  have heq : realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • (fun i => (a i : ℝ))) =
      (⟨realMarkedDirection F v w marked t ((m : ℚ) • (fun i => (a i : ℚ)))⟩ : D.RealGroup) := by
    apply NilpotentLieBCHGroup.ext
    change realMarkedParameterDirection F v w marked t _ = _
    rw [← realMarkedParameterDirection_rat]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast]
  exact heq ▸ h

theorem marked_phase_correction_coordinate_norm_le {p R : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hmp : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p)
    (hR : 1 ≤ R) (g z γ : D.RealGroup) (hg : g = z * γ)
    (hgphase : ‖torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord‖ ≤ 1 / 4)
    (hz : ‖(D.basis.baseChange ℝ).equivFun z.coord‖ ≤ R) :
    ‖(D.basis.baseChange ℝ).equivFun (realMarkedParameterDirection F v w marked t
      ((m : ℝ) • torusPhaseLinear (normalizedMarkedPhase F v w marked t m) γ.coord))‖ ≤
        2 * Real.exp (5 * p) * R := by
  let φ := normalizedMarkedPhase F v w marked t m
  have hsum : torusPhaseLinear φ g.coord = torusPhaseLinear φ z.coord + torusPhaseLinear φ γ.coord := by
    rw [hg, torusPhaseLinear_mul D]
  have hγ : torusPhaseLinear φ γ.coord = torusPhaseLinear φ g.coord - torusPhaseLinear φ z.coord := by
    rw [hsum, add_sub_cancel_left]
  have hzphase : ‖torusPhaseLinear φ z.coord‖ ≤ Real.exp (2 * p) * R :=
    (normalizedMarkedPhase_coordinate_norm_le F v w marked t m D.basis hd hphase z.coord).trans
      (mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _))
  have hγnorm : ‖torusPhaseLinear φ γ.coord‖ ≤ 1 / 4 + Real.exp (2 * p) * R := by
    rw [hγ]
    exact (norm_sub_le _ _).trans (add_le_add hgphase hzphase)
  have hlarge : 1 ≤ Real.exp (2 * p) * R :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity)) hR
  have hγnorm' : ‖torusPhaseLinear φ γ.coord‖ ≤ 2 * Real.exp (2 * p) * R := by
    nlinarith
  have h := realMarkedParameterDirection_coordinate_norm_le F v w marked t D.basis ht hdir
    ((m : ℝ) • torusPhaseLinear φ γ.coord)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg m)] at h
  apply h.trans
  calc
    Real.exp (2 * p) * ((m : ℝ) * ‖torusPhaseLinear φ γ.coord‖) ≤
        Real.exp (2 * p) * (Real.exp p * (2 * Real.exp (2 * p) * R)) := by gcongr
    _ = 2 * Real.exp (5 * p) * R := by
      rw [show 5 * p = 2 * p + p + 2 * p by ring, Real.exp_add, Real.exp_add]
      ring

theorem exists_marked_phase_band_representatives (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {r d t m : ℕ}
      (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (_hw : ∀ i, 0 < w i) (_hv : ∀ i, v i ∈ F.layer (w i) 1)
      [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (t : ℝ) ≤ p → 0 < m → (m : ℝ) ≤ Real.exp p →
      (∀ i j, rationalLogHeight
        (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p) →
      (∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p) →
      (∀ z : D.filtration.Group, z ∈ D.lattice →
        IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) →
      (∀ a : Fin t → ℤ,
        (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
          D.filtration.Group) ∈ D.lattice) →
      ∀ g : D.RealGroup,
        (∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord i| ≤ 1 / 4) →
        ∃ z : D.RealGroup,
          (QuotientGroup.mk z : D.Space) = QuotientGroup.mk g ∧
          torusPhaseLinear (normalizedMarkedPhase F v w marked t m) z.coord =
            torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord ∧
          ‖(D.basis.baseChange ℝ).equivFun z.coord‖ ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨A, hA, hrep⟩ := exists_realification_representatives_exp_bound (s + 1)
  obtain ⟨B, hB, hprod⟩ := exists_bch_group_product_exp_bound (s + 1) (A + 2)
  refine ⟨(A + 10) + B + 2, by omega, ?_⟩
  intro I L _ _ r d t m F v w marked hw hv _ _ _ D p hp hD ht hm hmp hdir hphase hint hlat g hg
  let φ := normalizedMarkedPhase F v w marked t m
  let H := ⌈Real.exp p⌉₊
  have hc (i j k) : RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  obtain ⟨z, hz, γ, hγ, heq⟩ := hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice
    D.grid H (p + 1) D.grid_pos D.inner_grid hc (by linarith)
    (by simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith))
    (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith))) g
  let R := Real.exp (((p + 1) + A) ^ A)
  have hR : 1 ≤ R := Real.one_le_exp (by positivity)
  have hznorm : ‖(D.basis.baseChange ℝ).equivFun z.coord‖ ≤ R :=
    (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr (fun i => by
      simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using hz i)
  obtain ⟨a, ha⟩ := torusPhaseLinear_realLattice_integral D φ hint γ hγ
  let δ : D.RealGroup := realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • (fun i => (a i : ℝ)))
  have hδ : δ ∈ D.realLattice := realMarkedParameterElement_scaled_integer_mem F v w marked hw hv t m D hlat a
  have hδphase : torusPhaseLinear φ δ.coord = torusPhaseLinear φ γ.coord := by
    change torusPhaseLinear φ (realMarkedParameterDirection F v w marked t _) = _
    rw [normalizedMarkedPhase_real_scaled_parameter F v w marked t m hm, ha]
  have hδnorm : ‖(D.basis.baseChange ℝ).equivFun δ.coord‖ ≤ 2 * Real.exp (5 * p) * R := by
    change ‖(D.basis.baseChange ℝ).equivFun (realMarkedParameterDirection F v w marked t _)‖ ≤ _
    rw [← ha]
    exact marked_phase_correction_coordinate_norm_le F v w marked t m D hp hD.1 ht hmp hdir hphase
      hR g z γ heq ((pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun i => by
        simpa only [Real.norm_eq_abs] using hg i)) hznorm
  let q := p + (A + 10 : ℕ)
  have hpq : p + 1 ≤ q := by dsimp [q]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) A]
  have hq : 0 ≤ q := by positivity
  have hinput : 2 * Real.exp (5 * p) * R ≤ Real.exp ((q + 2) ^ (A + 2)) := by
    have hQ : 6 ≤ q + 2 := by dsimp [q]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) A]
    have hpQ : p ≤ q + 2 := by linarith
    have hQpow : q + 2 ≤ (q + 2) ^ A := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ q + 2) (by omega : 1 ≤ A)
    have hRpow : ((p + 1) + A) ^ A ≤ (q + 2) ^ A :=
      pow_le_pow_left₀ (by positivity) (by dsimp [q]; push_cast; linarith) A
    have hexp : 1 + 5 * p + ((p + 1) + A) ^ A ≤ (q + 2) ^ (A + 2) := by
      calc
        _ ≤ 7 * (q + 2) ^ A := by nlinarith
        _ ≤ (q + 2) ^ A * (q + 2) ^ 2 :=
          by nlinarith [pow_nonneg (by linarith : 0 ≤ q + 2) A, sq_nonneg (q + 2 - 3)]
        _ = _ := (pow_add _ _ _).symm
    calc
      _ ≤ Real.exp 1 * Real.exp (5 * p) * Real.exp (((p + 1) + A) ^ A) := by
        gcongr
        linarith [Real.add_one_le_exp (1 : ℝ)]
      _ = Real.exp (1 + 5 * p + ((p + 1) + A) ^ A) := by rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr hexp
  have hRinput : R ≤ Real.exp ((q + 2) ^ (A + 2)) := by
    apply le_trans ?_ hinput
    have he : 1 ≤ Real.exp (5 * p) := Real.one_le_exp (by positivity)
    nlinarith [Real.exp_nonneg (5 * p)]
  refine ⟨z * δ, ?_, ?_, ?_⟩
  · rw [heq]
    exact (QuotientGroup.mk_mul_of_mem z hδ).trans
      (QuotientGroup.mk_mul_of_mem z (show γ ∈ D.realLattice from hγ)).symm
  · rw [heq, torusPhaseLinear_mul D, torusPhaseLinear_mul D, hδphase]
  · have hbound := hprod (D.basis.baseChange ℝ) (lieStructureConstants D.basis) H q
      D.filtration.realification.lowerCentralSeries_eq_bot [z, δ]
      (fun i j k => (realLieBasis_structure D.basis i j k).symm) hq
      (by simpa only [Fintype.card_fin] using hD.1.trans (by linarith : p ≤ q))
      (by simpa using (show 2 ≤ s + 1 by omega))
      ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hpq)) hc
      (by
        intro x hx i
        have hxnorm : ‖(D.basis.baseChange ℝ).equivFun x.coord‖ ≤ Real.exp ((q + 2) ^ (A + 2)) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact hznorm.trans hRinput
          · exact hδnorm.trans hinput
        calc
          _ ≤ ‖(D.basis.baseChange ℝ).equivFun x.coord‖ := by
            simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using
              norm_le_pi_norm ((D.basis.baseChange ℝ).equivFun x.coord) i
          _ ≤ _ := hxnorm)
    have hfinal := Real.exp_le_exp.mpr (shifted_center_power_bound (A + 10) B hp)
    apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr
    intro i
    simpa only [List.prod_cons, List.prod_nil, mul_one, Real.norm_eq_abs, Basis.equivFun_apply] using
      (hbound i).trans hfinal

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonInducedCorrelation
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem induced_marked_observable_scaled_parameter
    {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e u t m : ℕ}
    (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (hm : 0 < m)
    (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
    (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
    (E : RationalFilteredNilmanifold (L ⧸ J) u e)
    (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
      (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)
    (V : E.Space → ℂ) (G : D.Space → ℂ)
    (hG : ∀ g : D.RealGroup,
      (∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord i| ≤ 1 / 4) →
      G (QuotientGroup.mk g) = markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g)
    (a : Fin t → ℝ) (ha : ∀ i, |a i| ≤ 1 / 4) (g : D.RealGroup)
    (hg : torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord = 0) :
    G (QuotientGroup.mk (realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • a) * g)) =
      V (QuotientGroup.mk (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ g.coord⟩ : E.RealGroup)) := by
  rw [hG]
  · exact markedLocalCoefficientValue_scaled_parameter F v w marked hw hv t m hm D J hJ E hmap V a g hg
  · intro i
    rw [torusPhaseLinear_mul D, hg, add_zero]
    change |torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (realMarkedParameterDirection F v w marked t ((m : ℝ) • a)) i| ≤ 1 / 4
    rw [normalizedMarkedPhase_real_scaled_parameter F v w marked t m hm]
    exact ha i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredInducedCorrelationFamily
namespace OAI

section

namespace Erdos3

open Module

variable {I ι ν L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hF hω hH hc hgen in
theorem exists_markedShift_evaluation_model_with_budget (t : ℕ)
    (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
    (c : Basis ν ℚ (L ⧸ J)) {K : ℕ}
    (hcoef : ∀ i j, RationalHeightLE (c.repr (lieQuotientMap J (b j)) i) K)
    (l : ℕ) (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card ι : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hKp : (K : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ q : ℕ, q ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t ∧
      ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) q,
        ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
          M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
          M.ComplexityLE (markedShiftModelBudget s p) ∧ l ∣ D.grid ∧
          bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid D.grid ∧
          (∀ i j, rationalLogHeight
            (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤
              markedShiftModelBudget s p) ∧
          (∀ i j, rationalLogHeight (markedQuotientPhase F v w marked t (D.basis j) i) ≤
            markedShiftModelBudget s p) ∧
          ∀ i j, rationalLogHeight (c.repr (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤
            markedShiftModelBudget s p := by
  classical
  let _ := F.associatedDegree.polynomialShift_finiteDimensional b ω hF hω t
  let _ : FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t) :=
    inferInstanceAs (FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t).toSubmodule)
  let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
  let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
  have ha : a ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t :=
    F.associatedDegree.polynomialShift_finrank_le b ω hF hω t
  have hd : d ≤ a := (markedShiftSubalgebra F v w marked t).toSubmodule.finrank_le
  have hi : finrank ℚ (markedShiftSecondIdeal F v w marked t).toSubmodule ≤ d :=
    (markedShiftSecondIdeal F v w marked t).toSubmodule.finrank_le
  let R := markedShiftInputBudget s p
  let Q := markedShiftHeightBudget s p
  have hpR : p ≤ R := le_markedShiftInputBudget s hp
  have hR : 0 ≤ R := markedShiftInputBudget_nonneg s hp
  have hRQ : R ≤ Q := markedShiftInputBudget_le_height s hp
  have hQS : Q ≤ markedShiftModelBudget s p := markedShiftHeightBudget_le_model s hp
  have haR : (a : ℝ) ≤ R := (Nat.cast_le.mpr ha).trans
    (markedShift_dimension_budget s (Fintype.card ι) t hp hn ht)
  have hdR : (d : ℝ) ≤ R := (Nat.cast_le.mpr hd).trans haR
  obtain ⟨m, hm, q, hq, f, hstructure, hlayers, hdirection, hphase, heval⟩ :=
    exists_markedShiftQuotient_bounded_evaluation_data F b ω hF hω v w marked hw hv hH hc hgen
      t J hJ c hcoef
  choose c' hc' using hlayers
  let M₀ := markedShiftMultidegree F v w marked hw hv t
  obtain ⟨B, hB, hdiv, hbound, D, M, hMF, hDf, hgrid, hcoords, hcomplex⟩ :=
    M₀.exists_bounded_integral_model f c' hc' hstructure l hl
  have hmR : (m : ℝ) ≤ R := (Nat.cast_le.mpr (hm.trans hi)).trans hdR
  have hqR : (q : ℝ) ≤ R := (Nat.cast_le.mpr hq).trans hdR
  have hheight : (markedEvaluationHeight s (Fintype.card ι) a d m q H K : ℝ) ≤ Real.exp Q :=
    markedEvaluationHeight_le_exp s (Fintype.card ι) a d m q H K hR
      (step_le_markedShiftInputBudget s hp) (hn.trans hpR) haR hdR hmR hqR
      (hHp.trans (Real.exp_le_exp.mpr hpR)) (hKp.trans (Real.exp_le_exp.mpr hpR))
  have hgridS : (B : ℝ) ≤ Real.exp (markedShiftModelBudget s p) := by
    have hb := integral_grid_allowance_le_exp (bchIntegralDenominatorBound (s + 1)) q
      (markedEvaluationHeight s (Fintype.card ι) a d m q H K) l
      (hR.trans hRQ) (hqR.trans hRQ) hheight
      (hlp.trans (Real.exp_le_exp.mpr (hpR.trans hRQ)))
    exact (Nat.cast_le.mpr hbound).trans (hb.trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_left (hR.trans hRQ))))
  refine ⟨q, hq.trans (hd.trans ha), D, M, hMF,
    hcomplex _ (hqR.trans (hRQ.trans hQS)) hgridS
      (hheight.trans (Real.exp_le_exp.mpr hQS)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgrid]
    exact hdiv
  · simpa only [hgrid] using hcoords
  · intro i j
    rw [hDf]
    exact (rationalLogHeight_le_of_height (hdirection i j) hheight).trans hQS
  · intro i j
    rw [hDf]
    exact (rationalLogHeight_le_of_height (hphase i j) hheight).trans hQS
  · intro i j
    rw [hDf]
    exact (rationalLogHeight_le_of_height (heval i j) hheight).trans hQS

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem exists_compatible_marked_evaluation_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I ι L : Type*} [Fintype I] [Fintype ι]
      [LieRing L] [LieAlgebra ℚ L] {r t e u : ℕ}
      (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (_hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
      (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
      (E : RationalFilteredNilmanifold (L ⧸ J) u e) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (t : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) →
      (∀ i j, rationalLogHeight (b.repr (v i) j) ≤ p) → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (lieQuotientMap J (b j)) i) ≤ p) →
      ∃ q : ℕ, q ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t ∧
        ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) q,
          ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
            M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
            M.ComplexityLE ((p + C) ^ C) ∧
            bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid D.grid ∧
            (∀ i j, rationalLogHeight
              (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤
                (p + C) ^ C) ∧
            (∀ i j, rationalLogHeight (markedQuotientPhase F v w marked t (D.basis j) i) ≤
              (p + C) ^ C) ∧
            (∀ i j, rationalLogHeight
              (E.basis.repr (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤
                (p + C) ^ C) ∧
            (∀ z : D.filtration.Group, z ∈ D.lattice →
              (⟨markedBaseEvaluation F v w marked t J hJ 0 z.coord⟩ : E.filtration.Group) ∈ E.lattice) ∧
            (∀ z : D.filtration.Group, z ∈ D.lattice →
              IntegralVector (markedQuotientPhase F v w marked t z.coord)) ∧
            (∀ z : D.RealGroup, z ∈ D.realLattice →
              (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈
                E.realLattice) ∧
            ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              ∀ a : Fin t → ℤ,
                (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
                  D.filtration.Group) ∈ D.lattice := by
  obtain ⟨a, ha, hmodelbudget⟩ := exists_markedShiftModel_budget s
  obtain ⟨c, hcoverC, hcover⟩ := exists_marked_evaluation_lattice s
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := (X + 1 + Polynomial.C a) ^ a
  let Q₀ := (P₀ + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + Q₀ + (Q₀ + 3) ^ 3)
  refine ⟨C, hC, ?_⟩
  intro I ι L _ _ _ _ r t e u F b ω hF hω v w marked hw hv J hJ E p hp hn ht hc hgen hE hcoef
  let P := (p + 1 + a) ^ a
  let Q := (P + c) ^ c
  have hp1 : p ≤ p + 1 := by linarith
  have hp1P : p + 1 ≤ P := by
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
    calc
      p + 1 ≤ p + 1 + a := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (p + 1 + a) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ a)
  have hpP : p ≤ P := hp1.trans hp1P
  have hP : 0 ≤ P := hp.trans hpP
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hPQ : P ≤ Q := by
    have hc1 : 1 ≤ c := by omega
    have hc1' : (1 : ℝ) ≤ c := by exact_mod_cast hc1
    calc
      P ≤ P + c := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (P + c) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) hc1
  have htotal : P + Q + (Q + 3) ^ 3 ≤ (p + C) ^ C := by
    simpa [X, P₀, Q₀, P, Q, Polynomial.eval₂_pow] using hbudget p hp
  have hPC : P ≤ (p + C) ^ C := by
    have hn3 : 0 ≤ (Q + 3) ^ 3 := by positivity
    linarith
  have hQC : Q ≤ (p + C) ^ C := by
    have hn3 : 0 ≤ (Q + 3) ^ 3 := by positivity
    linarith
  have hmC : (Q + 3) ^ 3 ≤ (p + C) ^ C := by linarith
  have hS : markedShiftModelBudget s (p + 1) ≤ P := hmodelbudget (p + 1) (by linarith)
  obtain ⟨q, hqdim, D, M, hMF, hM, _, hcoords, hdir, hphase, heval⟩ :=
    exists_markedShift_evaluation_model_with_budget F b ω hF hω v w marked hw hv
      (one_le_ceil_exp p) (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
      (fun i j => rationalHeightLE_ceil_exp (hgen i j)) t J hJ E.basis
      (fun i j => rationalHeightLE_ceil_exp (hcoef i j)) 1 (by decide)
      (by linarith : 0 ≤ p + 1) (hn.trans hp1) (ht.trans hp1)
      (ceil_exp_le_exp_add_one hp) (ceil_exp_le_exp_add_one hp)
      (by exact_mod_cast Real.one_le_exp (by linarith : 0 ≤ p + 1))
  have hMP : M.ComplexityLE P := hM.mono M hS
  have hdirP (i j) := (hdir i j).trans hS
  have hphaseP (i j) := (hphase i j).trans hS
  have hevalP (i j) := (heval i j).trans hS
  obtain ⟨B, Λ, hB, hin, hout, _, _, hgrid, hMQ, hmap, hintegral, hrealmap⟩ :=
    hcover F v w marked D M J hJ E hP hMP (hE.mono E hpP) (ht.trans hpP) hevalP hphaseP
  let D' := D.withLattice Λ B hB hin hout
  let M' := M.withLattice Λ B hB hin hout
  have hdirQ : ∀ i j, rationalLogHeight
      (D'.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ Q :=
    fun i j => (hdirP i j).trans hPQ
  have htQ : (t : ℝ) ≤ Q := (ht.trans hpP).trans hPQ
  obtain ⟨m, hm, hmb, hmlattice⟩ := exists_marked_direction_lattice_scale F v w marked t D'
    hQ hMQ.1.1 htQ hMQ.1.2.1 hdirQ
  refine ⟨q, hqdim, D', M', hMF, hMQ.mono M' hQC, hgrid,
    (fun i j => (hdirP i j).trans hPC), (fun i j => (hphaseP i j).trans hPC),
    (fun i j => (hevalP i j).trans hPC), hmap, hintegral, hrealmap,
    m, hm, hmb.trans (Real.exp_le_exp.mpr hmC), hmlattice⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalNativeInverseModels
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

namespace NativeUnitVerticalData

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f} {V : NativeVerticalDerivativeData B}
  (U : NativeUnitVerticalData B V q)

theorem test_zero_evalCyclic (h x : ZMod N) :
    (U.test 0 h).evalCyclic N (fun _ => x) = (B.test h).evalCyclic N (fun _ => x) / 2 :=
  U.scalar h _

end NativeUnitVerticalData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPrimitiveGowers
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {d : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)

noncomputable def mixedPrimitiveFactor {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (i : Fin W.outputDim) (n : ZMod N) : ℂ :=
  f n * W.eval i (fun _ => (n.val : ℤ))

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
end


