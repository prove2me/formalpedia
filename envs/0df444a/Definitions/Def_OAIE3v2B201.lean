-- Prove2me | Definitions.Def_OAIE3v2B201
-- name    : OAIE3v2B201
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:10:26.66857+00:00
-- url     : https://prove2.me/theorems/ccbe4f49-5484-4285-955c-4b99c60e48d7
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 205 of 311
-- statement:
--   Definitions bundle 205 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B179`, `OAIE3v2B180`, `OAIE3v2B182`, `OAIE3v2B183`, `OAIE3v2B184`, `OAIE3v2B185` of this split.
--
--   Modules: `Estimates/ControlledRealFastCoefficientAction.lean`, `Estimates/ExtractedInitialState.lean`, `Estimates/FastHorizontalFactorization.lean`, `Estimates/GradedUnitEvaluation.lean`, `Estimates/MixedFixedReduction.lean`, `Estimates/NativeResidualMultiplier.lean`, `Estimates/NativeTwoVariableSplitFreezing.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/UnnormalizedCommonSymbolFactorization.lean`, `Geometry/NativeCoordinateDerivativeSystem.lean`, `Geometry/RealFastCoefficientCoordinates.lean`, `Lattices/NativeRetainedIntegerMultilinearQuadruples.lean`, `Linear/NativeRankRelationExistence.lean`, `Polynomial/GradedPolynomialSymbolInverse.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B179
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B182
import Definitions.Def_OAIE3v2B183
import Definitions.Def_OAIE3v2B184
import Definitions.Def_OAIE3v2B185

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealFastCoefficientCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U))
  (rows : Fin d → FirstCoefficientIndex w ω)
  (hblock : ∀ i j, (rows j).val.1 ≠ i.val.1 →
    b.repr ((F.realFirstCoefficientFastSubmodule w hw U).mkQ
      (F.realFirstCoefficientBasis e ω hF w i)) j = 0)

include hblock

noncomputable def realFastCoefficientHorizontalEquiv {a : ℕ} (ha : a ≤ d)
    (hprefix : ∀ j, j.val < a ↔ (rows j).val.1 = 0) :
    (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :=
  initialHorizontalEquiv ha b (F.realFastCoefficientHorizontal w hw U)
    (F.realFastCoefficientHorizontalSection w hw U)
    (F.realFastCoefficientHorizontal_section w hw U) (fun x j => by
      change b.repr (F.realFastCoefficientHorizontalSection w hw U
        (F.realFastCoefficientHorizontal w hw U x)) j = _
      rw [F.realFastCoefficientHorizontal_projector_repr e ω hF w hw U b rows hblock]
      simp only [← hprefix j, Basis.equivFun_apply])

theorem realFastCoefficientHorizontalEquiv_projection {a : ℕ} (ha : a ≤ d)
    (hprefix : ∀ j, j.val < a ↔ (rows j).val.1 = 0)
    (x : F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) :
    F.realFastCoefficientHorizontalEquiv e ω hF w hw U b rows hblock ha hprefix
      (fun i => b.equivFun x (Fin.castLE ha i)) = F.realFastCoefficientHorizontal w hw U x :=
  initialHorizontalEquiv_projection ha b (F.realFastCoefficientHorizontal w hw U)
    (F.realFastCoefficientHorizontalSection w hw U)
    (F.realFastCoefficientHorizontal_section w hw U) _ x

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledRealFastCoefficientAction
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
  [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
  [Fintype κ] [DecidableEq κ] (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem realFastCoefficientAdjoint_unitriangular
    (rows : κ → FirstCoefficientIndex w ω)
    (b : Basis κ ℝ (F.RealFirstCoefficientModule w ⧸
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)))
    (D : Matrix κ (FirstCoefficientIndex w ω) ℚ)
    (S : Matrix (FirstCoefficientIndex w ω) κ ℚ)
    (hD : LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w) b
      (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ =
      D.map (Rat.castHom ℝ))
    (hDS : D * S = 1)
    (hDb : ∀ a i, (rows a).val.1 ≠ i.val.1 → D a i = 0)
    (hSb : ∀ i a, i.val.1 ≠ (rows a).val.1 → S i a = 0)
    (g : F.RealAdaptedPolynomialGroup w)
    (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (a c : κ) (hac : ω (rows a).val.2 ≤ ω (rows c).val.2) :
    LinearMap.toMatrix b b
        (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
      (1 : Matrix κ κ ℝ) a c := by
  rw [F.realFastCoefficientAdjoint_matrix e ω hF w hw U b D S hD hDS g hg]
  apply block_quotient_unitriangular (fun i : FirstCoefficientIndex w ω => ω i.val.2)
    (fun a => ω (rows a).val.2) _ _ _ ?_ ?_ (real_matrix_right_inverse D S hDS) ?_ a c hac
  · intro a i hai
    change (D a i : ℝ) = 0
    have h := hDb a i (fun he => hai (firstCoefficientIndex_grade_eq_of_monomial_eq w ω _ _ he))
    rw [h, Rat.cast_zero]
  · intro i a hia
    change (S i a : ℝ) = 0
    have h := hSb i a (fun he => hia (firstCoefficientIndex_grade_eq_of_monomial_eq w ω _ _ he))
    rw [h, Rat.cast_zero]
  · intro i j hij
    rw [F.realFirstCoefficientAdjoint_matrix_entry e ω hF w g j i hij]
    simp only [Matrix.one_apply, eq_comm]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastHorizontalFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ F.AssociatedGraded)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
  (hU : (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) U).map
    (F.quotientTopSymbolMap (fun _ => 1)) ≤ F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) W)

local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) W
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) W)

include hU in
theorem realFast_horizontal_normalization [DecidableEq σ]
    (B : 𝓖) (K : Submodule ℝ 𝓗) (S R : K →ₗ[ℝ] 𝓔)
    (hSR : S = (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) W B).toLinearMap.comp R)
    (hS : (𝓟).comp S = K.subtype) (hR : (𝓟).comp R = K.subtype)
    (small rational : σ → 𝓔) (k : σ → K)
    (hsystem : ∀ i, F.realFastCoefficientDirectionMap W B.val (Pi.single i 1) = small i +
      F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) W B (rational i) + S (k i))
    (hsmall : ∀ i, 𝓟 (small i) ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ)
    (hrational : ∀ i, 𝓟 (rational i) ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ)
    (hk : ∀ i, (k i).val ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) :
    ∃ a B' c : 𝓖,
      a.val = F.realLayerOneCorrection e ω hF (fun i => 𝓟 (small i)) ∧
      c.val = F.realLayerOneCorrection e ω hF (fun i => 𝓟 (rational i)) ∧
      (B.val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U →
        B'.val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U) ∧
      coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B'.val.coord) 0 =
        coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B.val.coord) 0 ∧
      (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B.val.coord) 0 = 0 →
        ∀ i, (F.layer 2).mkQ.baseChange ℝ
          (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B'.val.coord) (Finsupp.single i 1)) =
          (k i).val) ∧
      let ρ := F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) W
      let Y := fun (g : 𝓖) i => F.realFastCoefficientDirectionMap W g.val (Pi.single i 1)
      let S' := (ρ a).symm.toLinearMap.comp S
      let R' := (ρ c).toLinearMap.comp R
      let small' := fun i => (ρ a).symm (small i - Y a i)
      let rational' := fun i => ρ c (rational i) - Y c i
      a * B' * c = B ∧ S' = (ρ B').toLinearMap.comp R' ∧
        (𝓟).comp S' = K.subtype ∧ (𝓟).comp R' = K.subtype ∧
        ∀ i, Y B' i = small' i + ρ B' (rational' i) + S' (k i) ∧
          𝓟 (small' i) = 0 ∧ 𝓟 (rational' i) = 0 ∧ 𝓟 (Y B' i) = (k i).val ∧
          𝓟 (Y B' i) ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ ⊓ K := by
  let a := F.realFastLayerOneCorrection e ω hF U W hU (fun i => 𝓟 (small i)) hsmall
  let c := F.realFastLayerOneCorrection e ω hF U W hU (fun i => 𝓟 (rational i)) hrational
  let ρ := F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) W
  let Y := fun (g : 𝓖) i => F.realFastCoefficientDirectionMap W g.val (Pi.single i 1)
  have hdata := cocycle_horizontal_normalization ρ Y
    (fun g h i => F.realFastCoefficientDirectionMap_mul W e ω hF g h (Pi.single i 1))
    𝓟 (F.realFastCoefficientAction_horizontal (fun _ => 1) (fun _ => Nat.zero_lt_one) W e ω hF)
    ((F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) K B a c S R hSR hS hR small rational k hsystem
    (fun i => F.realFastLayerOneCorrection_horizontal e ω hF U W hU _ hsmall i)
    (fun i => F.realFastLayerOneCorrection_horizontal e ω hF U W hU _ hrational i) hk
  have hpointwise : B.val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U →
      (a⁻¹ * B * c⁻¹).val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U := by
    intro hB
    let G := F.realPointwisePolynomialSubgroup e ω hF (fun _ : σ => 1) U
    exact G.mul_mem (G.mul_mem (G.inv_mem
      (F.realLayerOneCorrection_mem_pointwiseSubgroup e ω hF U _ hsmall)) hB)
        (G.inv_mem (F.realLayerOneCorrection_mem_pointwiseSubgroup e ω hF U _ hrational))
  have hzeroa : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) a.val.coord) 0 = 0 := by
    change coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      (F.realLayerOneCorrection e ω hF _).coord) 0 = 0
    rw [F.realLayerOneCorrection_log, coefficients_linearPolynomial_zero]
  have hzeroc : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) c.val.coord) 0 = 0 := by
    change coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      (F.realLayerOneCorrection e ω hF _).coord) 0 = 0
    rw [F.realLayerOneCorrection_log, coefficients_linearPolynomial_zero]
  have hconst := F.realAdapted_factor_middle_constant (fun _ => 1) B.val a.val
    (a⁻¹ * B * c⁻¹).val c.val (congrArg Subtype.val hdata.1) hzeroa hzeroc
  have hlinear : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B.val.coord) 0 = 0 →
      ∀ i, (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) (a⁻¹ * B * c⁻¹).val.coord)
          (Finsupp.single i 1)) = (k i).val := by
    intro hz i
    have hd := F.realFirstCoefficientDirectionMap_horizontal_unit e ω hF i
      (a⁻¹ * B * c⁻¹).val.coord (hconst.trans hz)
    have he : 𝓟 (Y (a⁻¹ * B * c⁻¹) i) = (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) (a⁻¹ * B * c⁻¹).val.coord)
          (Finsupp.single i 1)) := hd
    exact he.symm.trans (hdata.2.2.2.2 i).2.2.2.1
  exact ⟨a, a⁻¹ * B * c⁻¹, c, rfl, rfl, hpointwise, hconst, hlinear, hdata⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ F.AssociatedGraded)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) W
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) W)
local notation "𝓤" => Submodule.baseChange ℝ (F.layerOneGradedSubmodule e ω hF U)
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "Y" => (fun (g : 𝓖) i => F.realFastCoefficientDirectionMap W (Subtype.val g) (Pi.single i 1))

theorem realFast_bounded_horizontal_normalization
    (hU : (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) U).map
      (F.quotientTopSymbolMap (fun _ => 1)) ≤ F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) W)
    (g : 𝓖) (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g.val.coord) 0 = 0)
    (K : Submodule ℝ 𝓗) (S R : K →ₗ[ℝ] 𝓔) (hSR : S = (ρ g).toLinearMap.comp R)
    (hS : (𝓟).comp S = K.subtype) (hR : (𝓟).comp R = K.subtype)
    (small rational : σ → 𝓔) (k : σ → K)
    (hsystem : ∀ i, Y g i = small i + ρ g (rational i) + S (k i))
    (hsmall : ∀ i, 𝓟 (small i) ∈ 𝓤) (hrational : ∀ i, 𝓟 (rational i) ∈ 𝓤)
    (hk : ∀ i, (k i).val ∈ 𝓤)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i, ‖cH (𝓟 (small i))‖ ≤ M / T i)
    (l : ℕ) (hgrid : ∀ i, cH (𝓟 (rational i)) ∈ realDenominatorGrid l) :
    ∃ a g' q : 𝓖,
      a.val = F.realLayerOneCorrection e ω hF (fun i => 𝓟 (small i)) ∧
      q.val = F.realLayerOneCorrection e ω hF (fun i => 𝓟 (rational i)) ∧
      F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T M a.val.coord ∧
      F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l q.val.coord ∧
      coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g'.val.coord) 0 = 0 ∧
      (∀ i, (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g'.val.coord) (Finsupp.single i 1)) =
          (k i).val) ∧
      let S' := (ρ a).symm.toLinearMap.comp S
      let R' := (ρ q).toLinearMap.comp R
      let small' := fun i => (ρ a).symm (small i - Y a i)
      let rational' := fun i => ρ q (rational i) - Y q i
      a * g' * q = g ∧ S' = (ρ g').toLinearMap.comp R' ∧
        (𝓟).comp S' = K.subtype ∧ (𝓟).comp R' = K.subtype ∧
        ∀ i, Y g' i = small' i + ρ g' (rational' i) + S' (k i) ∧
          𝓟 (small' i) = 0 ∧ 𝓟 (rational' i) = 0 ∧ 𝓟 (Y g' i) = (k i).val ∧
          𝓟 (Y g' i) ∈ 𝓤 ⊓ K := by
  classical
  have h := F.realFast_horizontal_normalization (σ := σ) (ι := ι) e ω hF U W hU
    g K S R hSR hS hR small rational k hsystem hsmall hrational hk
  obtain ⟨a, g', q, ha, hq, _, hconst, hlinear, hnew⟩ := h
  refine ⟨a, g', q, ha, hq, ?_, ?_, hconst.trans hzero, hlinear hzero, hnew⟩
  · rw [ha]
    exact F.realLayerOneCorrection_slow e ω hF T hT hM (fun i => 𝓟 (small i)) hbound
  · rw [hq]
    apply F.realLayerOneCorrection_grid e ω hF
    choose z hz using hgrid
    refine ⟨fun x => z x.1 x.2, ?_⟩
    funext x
    exact congrFun (hz x.1) x.2

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ F.AssociatedGraded)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) W
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) W)
local notation "𝓤" => Submodule.baseChange ℝ (F.layerOneGradedSubmodule e ω hF U)
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "Y" => (fun (g : 𝓖) i => F.realFastCoefficientDirectionMap W (Subtype.val g) (Pi.single i 1))

theorem realFast_controlled_horizontal_factorization
    (hU : (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) U).map
      (F.quotientTopSymbolMap (fun _ => 1)) ≤ F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) W)
    (g₀ : 𝓖) (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g₀.val.coord) 0 = 0)
    (K : Submodule ℝ 𝓗) (S R : K →ₗ[ℝ] 𝓔) (hSR : S = (ρ g₀).toLinearMap.comp R)
    (hS : (𝓟).comp S = K.subtype) (hR : (𝓟).comp R = K.subtype)
    (small rational : σ → 𝓔) (k : σ → K)
    (hsystem : ∀ i, Y g₀ i = small i + ρ g₀ (rational i) + S (k i))
    (hsmall : ∀ i, 𝓟 (small i) ∈ 𝓤) (hrational : ∀ i, 𝓟 (rational i) ∈ 𝓤)
    (hk : ∀ i, (k i).val ∈ 𝓤)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i, ‖cH (𝓟 (small i))‖ ≤ M / T i)
    (l : ℕ) (hgrid : ∀ i, cH (𝓟 (rational i)) ∈ realDenominatorGrid l) :
    ∃ a g c : 𝓖, a * g * c = g₀ ∧
      F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T M a.val.coord ∧
      F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l c.val.coord ∧
      (∀ i, (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g.val.coord) (Finsupp.single i 1)) =
          (k i).val) ∧
      (∀ i, 𝓟 (Y a i) = 𝓟 (small i)) ∧ (∀ i, 𝓟 (Y c i) = 𝓟 (rational i)) := by
  have hnorm := F.realFast_bounded_horizontal_normalization e ω hF U W hU
    g₀ hzero K S R hSR hS hR small rational k hsystem hsmall hrational hk T hT M hM hbound l hgrid
  obtain ⟨a, g, c, ha, hc, habound, hcgrid, _, hlinear, hnew⟩ := hnorm
  refine ⟨a, g, c, hnew.1, habound, hcgrid, hlinear, ?_, ?_⟩
  · intro i
    change F.realFirstCoefficientHorizontal (fun _ : σ => 1)
      (F.realFirstCoefficientDirectionMap a.val.coord (Pi.single i 1)) = _
    rw [ha]
    exact F.realLayerOneCorrection_horizontal_derivative e ω hF (fun j => 𝓟 (small j)) i
  · intro i
    change F.realFirstCoefficientHorizontal (fun _ : σ => 1)
      (F.realFirstCoefficientDirectionMap c.val.coord (Pi.single i 1)) = _
    rw [hc]
    exact F.realLayerOneCorrection_horizontal_derivative e ω hF (fun j => 𝓟 (rational j)) i

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GradedUnitEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "ωQ" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))

theorem fullFastPointwise_image_le [Fintype σ] [Fintype ι] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    (F.symbolPointwiseSubalgebra e ω hF w (F.fullFastGradedDiagonal W)).map (F.quotientTopSymbolMap w) ≤
      F.reducedSquareFastDiagonalSubalgebra w (F.fastPointwiseSquare e ω hF w W) := by
  rw [F.fastPointwiseDiagonal_eq e ω hF w hw W hW]
  have hm := F.symbolPointwiseSubalgebra_map_le F.quotientTop e ω hF
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
    (lieQuotientMap (F.layerIdeal (s + 1))) (fun _ _ hx => F.quotientLie_mem _ le_rfl hx)
    w (F.fullFastGradedDiagonal W)
  have hle : (F.fullFastGradedDiagonal W).map F.quotientTopGradedMap ≤ F.fastGradedDiagonal W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  exact hm.trans (F.quotientTop.symbolPointwiseSubalgebra_mono
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF) w hle)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateDerivativeSystem
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) U
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U

theorem exists_native_coordinate_derivative_system :
    F.NativeCoordinateDerivativeSpec (σ := σ) (a := a) (d := d) e ω hF U := by
  intro b rows ha η hη sectionMap hsection Cscale hC hweighted m hm hgrid
    T hT g bound hbound D p hp hap hmp hCp hDp
  have hone (α : σ →₀ ℕ) : monomialScale (fun _ : σ => (1 : ℝ)) α = 1 := by
    simp [monomialScale]
  have hsectionOne (y : Fin d → ℝ) (M : ℝ) (hM : 0 ≤ M) (hy : ∀ j, |y j| ≤ M) :
      F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) (fun _ => 1) (Cscale * M) (sectionMap y) := by
    apply (hweighted (fun _ => 1) (fun _ => by norm_num) M hM).2 y
    intro j
    simpa only [hone, div_one] using hy j
  have hprojOne (x : E) (M : ℝ) (hM : 0 ≤ M)
      (hx : F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) (fun _ => 1) M x) (j : Fin d) :
      |b.equivFun ((J).mkQ x) j| ≤ Cscale * M := by
    simpa only [hone, div_one] using
      (hweighted (fun _ => 1) (fun _ => by norm_num) M hM).1 x hx j
  have hraw := F.layerOne_rational_kernel_basis e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one)
    Uf b ha η hη sectionMap hsection 1 m hm Cscale hC hgrid hsectionOne
    D.K D.basisMatrix D.span_eq D.independent_real D.basis_height
  obtain ⟨v, hv, hspan, hli, hheight⟩ := hraw
  let K := Submodule.span ℚ (Set.range v)
  let bK : Basis (Fin D.k) ℚ K := Basis.span hli
  have hbK (j : Fin D.k) : (bK j : L ⧸ F.layer 2) = v j :=
    Basis.coe_span_apply hli j
  have hbasis (j : Fin D.k) : (1 : ℝ) ⊗ₜ[ℚ] (bK j : L ⧸ F.layer 2) =
      η ((D.basisMatrix.map (Rat.castHom ℝ)).col j) := by
    exact (congrArg (fun z : L ⧸ F.layer 2 => (1 : ℝ) ⊗ₜ[ℚ] z) (hbK j)).trans (hv j)
  have htransport := transport_coordinate_derivatives_to_rational_span ha b η Hq hη T
    (F.realFastCoefficientDirectionMap U g.val) (ρ g)
    (fun i => monomialScale T (rows i).val.1) bound D K bK hspan hbasis
  obtain ⟨S, R, hSR, hS, hR, hSnorm, hRgrid, small, rational, k, hsystem, hrgrid, hsmall⟩ := htransport
  let H₀ := (a + 1) * (max m (Nat.ceil ((m : ℝ) * Cscale)) * D.heightBound) ^ a
  have hH₀ : (H₀ : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    layerOne_basis_transport_height_le_exp a m D.heightBound Cscale p hp hap hmp hC hCp hDp
  have hH : ((max 1 H₀ : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (Real.one_le_exp (by positivity)) hH₀
  let l := D.liftDenominator * D.derivativeDenominator
  have hl : 0 < l := Nat.mul_pos D.liftDenominator_pos D.derivativeDenominator_pos
  have hlb : (l : ℝ) ≤ bound ^ 2 := by
    rw [Nat.cast_mul, pow_two]
    exact mul_le_mul D.liftDenominator_le D.derivativeDenominator_le (Nat.cast_nonneg _) hbound
  have hk : D.k ≤ a := by
    simpa using D.independent_real.fintype_card_le_finrank
  refine ⟨hk, K, bK, max 1 H₀, le_max_left _ _, hH, ?_, l, hl, hlb,
    S, R, hSR, hS, hR, ?_, ?_, small, rational, k, ?_, ?_, hsmall, ?_⟩
  · intro i j
    exact (congrArg (fun z : L ⧸ F.layer 2 =>
      RationalHeightLE ((F.layerOneBasis e ω hF).repr z i) (max 1 H₀)) (hbK j)).mpr
        ((hheight i j).mono (le_max_right 1 H₀))
  · intro x
    have hx := F.layerOne_equiv_symm_norm e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one)
      Uf b ha η hη Cscale hC hprojOne x.val
    calc
      _ ≤ bound * ‖η.symm x.val‖ := hSnorm x
      _ ≤ bound * (Cscale * ‖cH x.val‖) := mul_le_mul_of_nonneg_left hx hbound
      _ = (bound * Cscale) * ‖cH x.val‖ := (mul_assoc _ _ _).symm
  · intro j
    exact realDenominatorGrid_subset_of_dvd D.liftDenominator_pos
      (dvd_mul_right D.liftDenominator D.derivativeDenominator) (hRgrid j)
  · intro i
    exact hsystem i
  · intro i
    exact realDenominatorGrid_subset_of_dvd D.derivativeDenominator_pos
      (dvd_mul_left D.derivativeDenominator D.liftDenominator) (hrgrid i)
  · intro i
    have hx := F.realFastCoefficientHorizontal_section_norm_bound e ω hF (fun _ => 1)
      (fun _ => Nat.zero_lt_one) Uf b sectionMap hsection rows T hT Cscale hC
      (fun M hM => (hweighted T hT M hM).2) (small i)
    calc
      _ ≤ Cscale * ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ := hx
      _ ≤ Cscale * (bound / T i) := mul_le_mul_of_nonneg_left (hsmall i) hC
      _ = (Cscale * bound) / T i := (mul_div_assoc _ _ _).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.GradedPolynomialSymbolInverse
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

section General

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedGradedPolynomialHom_grid (l : ℕ)
    (g : F.RealAdaptedPolynomialGroup w) (hg : F.RealAdaptedCoefficientGrid e ω hF w l g.coord) :
    CoefficientGrid ((F.associatedGradedBasis e ω hF).baseChange ℝ) l
      (F.realAdaptedGradedPolynomialHom e ω hF w g).coord := by
  classical
  intro α
  obtain ⟨a, ha⟩ := (F.realAdaptedCoefficientGrid_iff_formal e ω hF w l g.coord).mp hg α
  refine ⟨fun i => if ω i = Finsupp.weight w α then a i else 0, ?_⟩
  funext i
  change ((if ω i = Finsupp.weight w α then a i else 0 : ℤ) : ℝ) =
    (l : ℝ) * ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr
      (coefficients (F.realAdaptedGradedPolynomialHom e ω hF w g).coord α) i
  rw [F.realAdaptedGradedPolynomialHom_coordinate]
  split_ifs
  · exact congrFun ha i
  · simp only [Int.cast_zero, mul_zero]

end General

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ExtractedInitialState
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

universe uσ uι uκ uν uL

variable {σ : Type uσ} {ι : Type uι} {κ : Type uκ} {ν : Type uν} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι]
  [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "Y" => (fun (g : G) i => F.realFastCoefficientDirectionMap Wf (Subtype.val g) (Pi.single i 1))
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))

theorem exists_initialFormalState_of_horizontal_data
    (aExp C : ℕ) (haExp : 2 ≤ aExp)
    (hcontrol : ControlledInitialRemovalSpec.{uσ, uι, uκ, uν, uL} s aExp C) :
    F.HorizontalInitialStateSpec (σ := σ) (κ := κ) (ν := ν) e ω hF W aExp C := by
  intro H p hH hp hι hσ hHp hstructure hW g₀ hzero K bK b rows sectionMap hsection
    T hT Kscale hKscale hKscalep hprojection hsectionBound l δ hl hδ hδlp
    hprojectionGrid hsectionGrid S R small rational k hSR hsystem hS hR
    hsmallH hrationalH hkH hsmall hSbound hRgrid hrational
  have hraw := hcontrol (σ := σ) (ι := ι) (κ := κ) (ν := ν) (L := L)
    F e ω hF H p hH hp hι hσ hHp hstructure W
  have hraw' := hraw hW
  have hfinish (a g c : G) (hfactor : a * g * c = g₀)
      (habound : F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T
        (Real.exp ((p + 2) ^ aExp)) a.val.coord)
      (hcgrid : F.RealAdaptedCoefficientGrid e ω hF (fun _ : σ => 1) (δ * l) c.val.coord)
      (hlinear : ∀ i, (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g.val.coord) (Finsupp.single i 1)) =
          (k i).val)
      (haH : ∀ i, Hq (Y a i) = Hq (small i))
      (hcH : ∀ i, Hq (Y c i) = Hq (rational i)) :
      ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
        (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
        (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
        (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 ((p + C) ^ C),
        X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val := by
    as_aux_lemma =>
      have hSR' : S = (ρ (a * g * c)).toLinearMap.comp R := by
        simpa only [hfactor] using hSR
      have hsystem' (i : σ) : Y (a * g * c) i = small i + ρ (a * g * c) (rational i) + S (k i) := by
        simpa only [hfactor] using hsystem i
      have hresult := hraw' a g c K bK b rows sectionMap hsection T hT Kscale hKscale hKscalep
        hprojection hsectionBound l δ hl hδ hδlp hprojectionGrid hsectionGrid habound hcgrid
        S R small rational k hSR' hsystem' hS hR haH hcH hlinear hsmall hSbound hRgrid hrational
      exact hresult
  have hsize : Kscale * Real.exp p ≤ Real.exp ((p + 2) ^ aExp) := by
    calc
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul_of_nonneg_right hKscalep (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((p + 2) ^ aExp) := by
        apply Real.exp_le_exp.mpr
        exact (show 2 * p ≤ (p + 2) ^ 2 by nlinarith [sq_nonneg p]).trans
          (pow_le_pow_right₀ (by linarith) haExp)
  have hsmallHorizontalBound (i : σ) :
      ‖cH (Hq (small i))‖ ≤ Real.exp ((p + 2) ^ aExp) / T i := by
    calc
      _ ≤ Kscale * ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ :=
        F.realFastCoefficientHorizontal_section_norm_bound e ω hF (fun _ => 1)
          (fun _ => Nat.zero_lt_one) Uf b sectionMap hsection rows T hT
          Kscale hKscale hsectionBound (small i)
      _ ≤ Kscale * (Real.exp p / T i) := mul_le_mul_of_nonneg_left (hsmall i) hKscale
      _ = (Kscale * Real.exp p) / T i := (mul_div_assoc _ _ _).symm
      _ ≤ _ := div_le_div_of_nonneg_right hsize (hT i).le
  have hrationalHorizontalGrid (i : σ) : cH (Hq (rational i)) ∈ realDenominatorGrid (δ * l) :=
    F.realFastCoefficientHorizontal_section_grid e ω hF (fun _ => 1)
      (fun _ => Nat.zero_lt_one) Uf b sectionMap hsection l (δ * l)
      (hsectionGrid l) (rational i) (hrational i)
  have hnorm := F.realFast_controlled_horizontal_factorization e ω hF
    (F.fullFastGradedDiagonal W) Wf
    (F.fullFastPointwise_image_le e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) W hW)
    g₀ hzero (K.baseChange ℝ) S R hSR hS hR small rational k hsystem hsmallH hrationalH hkH
    T hT (Real.exp ((p + 2) ^ aExp)) (Real.exp_nonneg _) hsmallHorizontalBound
    (δ * l) hrationalHorizontalGrid
  obtain ⟨a, g, c, hfactor, habound, hcgrid, hlinear, haH, hcH⟩ := hnorm
  exact ⟨a, g, c, hfactor, habound, hcgrid, hfinish a g c hfactor habound hcgrid hlinear haH hcH⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))

theorem exists_initialFormalState_from_extraction (C D : ℕ)
    (hbudget : ∀ p : ℝ, 0 ≤ p →
      separationBudget (extractedInitialParameter p) ≤ (p + D) ^ D ∧
      absorbedInitialParameter (extractedInitialParameter p) ≤ (p + D) ^ D ∧
      (absorbedInitialParameter (extractedInitialParameter p) + 2) ^ 2 ≤ (p + D) ^ D ∧
      (absorbedInitialParameter (extractedInitialParameter p) + C) ^ C ≤ (p + D) ^ D)
    (habs : ∀ r : ℕ, F.AbsorbedInitialStateSpec (σ := σ) (κ := Fin r) (ν := Fin d)
      (τ := τ) e ω hF W C) :
    F.ExtractedInitialStateSpec (σ := σ) (τ := τ) (a := a) (d := d) e ω hF W D := by
  intro H p hH hp hι hσ hτ hap hHp hstructure hW v hv hheight g₀ hzero
    b rows ha η hη sectionMap hsection Cscale hC hCp hweighted δ hδ hδp
    hprojectionGrid hsectionGrid T hT B hB hBp sys
  let q := extractedInitialParameter p
  have hq := extractedInitialParameter_controls hp
  have hqpos : 0 ≤ q := hp.trans hq.1
  have hep : Real.exp p ≤ Real.exp q := Real.exp_le_exp.mpr hq.1
  have hb := hbudget p hp
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hTq (i : σ) : Real.exp (separationBudget q) ≤ T i :=
    (Real.exp_le_exp.mpr hb.1).trans (hT i)
  have hgrid (y : Fin d → ℝ) (hy : y ∈ realDenominatorGrid 1) :
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) δ (sectionMap y) :=
    (congrArg (fun n => F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) n (sectionMap y))
      (Nat.mul_one δ)).mp (hsectionGrid 1 y hy)
  have hnative := F.exists_native_coordinate_derivative_system e ω hF Wf
    b rows ha η hη sectionMap hsection Cscale hC hweighted δ hδ hgrid T hTpos
    g₀ B hB sys p hp hap hδp hCp (sys.height_le.trans hBp)
  obtain ⟨hk, K, bK, Hk, hHk, hHkp, hKheight, l, hl, hlB, S, R, hSR, hS, hR,
    hSnorm, hRgrid, small, rational, k, hsystem, hrgrid, hsmall, hsmallH⟩ := hnative
  have hcommon : ((max H Hk : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_max]
    exact max_le (hHp.trans hep) (hHkp.trans (Real.exp_le_exp.mpr hq.2.2))
  have hkcard : (Fintype.card (Fin sys.k) : ℝ) ≤ p := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr hk).trans hap
  have hsize : ((Fintype.card τ + Fintype.card ι + Fintype.card (Fin sys.k) : ℕ) : ℝ) ≤ q := by
    rw [Nat.cast_add, Nat.cast_add]
    calc
      _ ≤ p + p + p := add_le_add (add_le_add hτ hι) hkcard
      _ ≤ q := by linarith [hq.2.1]
  have hproducts := extractedInitialParameter_products hp hB hBp hC hCp δ l hδp hlB
  have hsmallq (i : σ) :
      ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ ≤
        Real.exp q / T i :=
    (hsmall i).trans (div_le_div_of_nonneg_right (hBp.trans hep) (hTpos i).le)
  have hsmallHq (i : σ) : ‖cH (Hq (small i))‖ ≤ Real.exp q / T i := by
    have hCB : Cscale * B ≤ Real.exp q := (mul_comm Cscale B).trans_le hproducts.1
    exact (hsmallH i).trans (div_le_div_of_nonneg_right hCB (hTpos i).le)
  have hSq (x : K.baseChange ℝ) :
      ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (S x)‖ ≤
        Real.exp q * ‖cH x.val‖ :=
    (hSnorm x).trans (mul_le_mul_of_nonneg_right hproducts.1 (norm_nonneg _))
  have hout := habs sys.k (max H Hk) q (hH.trans (le_max_left _ _)) hqpos
    (hι.trans hq.1) (hσ.trans hq.1) hcommon
    (fun i j k => (hstructure i j k).mono (le_max_left _ _)) hW v hv
    (fun j i => (hheight j i).mono (le_max_left _ _)) hsize g₀ hzero K bK
    (fun i j => (hKheight i j).mono (le_max_right _ _)) b rows sectionMap hsection T hTq
    Cscale hC (hCp.trans hep) (fun M hM => (hweighted T hTpos M hM).1)
    (fun M hM => (hweighted T hTpos M hM).2) l δ hl hδ hproducts.2
    hprojectionGrid hsectionGrid S R small rational k hSR hsystem hS hR
    hsmallHq hsmallq hSq hRgrid hrgrid
  obtain ⟨m, hm, hmp, x, g, z, hfactor, hx, hz, X, hX⟩ := hout
  refine ⟨hk, K, bK, Hk, hHk, hHkp, hKheight, m, hm,
    hmp.trans (Real.exp_le_exp.mpr hb.2.1), x, g, z, hfactor, ?_, hz,
    X.enlarge hb.2.2.2 hTpos, hX⟩
  exact F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hTpos
    (Real.exp_le_exp.mpr hb.2.2.1) x.val.coord hx

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualMultiplier
namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def normalizedLower (b : ℝ) (h x : ZMod N) : ℂ :=
  if hh : h ∈ W.shifts then
    ((W.selectedWitness ⟨h, hh⟩).test.expNormalize b).evalCyclic N (fun _ => x)
  else 0

end Erdos3.NativeCorrelationStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeTwoVariableSplitFreezing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

universe u v

open Module
open scoped TensorProduct NNReal

noncomputable def freezingExponent (s : ℕ) : ℕ :=
  Classical.choose (exists_controlled_frozen_niltest.{u, v} s)

theorem freezingExponent_ge_two (s : ℕ) : 2 ≤ freezingExponent.{u, v} s :=
  (Classical.choose_spec (exists_controlled_frozen_niltest.{u, v} s)).1

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem mixed_translation_reduction_transfer {s : ℕ} {p P : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (E : NativeIntegerVectorEquivalence s P
      (fun k (x : Fin 3 → ℤ) => V.eval k (fun j => correlationInput (x 0) (x 1 + x 2) j.1))
      (fun a x => coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a
        (mixedTranslationSample s x)))
    (h δ : ℤ)
    (R : ∀ a : BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length,
      NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) P
        (fun x => translationExpansionRemainder V.eval (mixedTranslationCoordinates s) a
          (mixedTranslationSample s ![h, x (), δ])))
    {Y : Type*} (S : Finset Y) (n : Y → ℤ) (k : Fin V.outputDim) (f : Y → ℂ) (q : ℝ)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star
      (V.eval k (fun j => correlationInput h (n u + δ) j.1))‖) :
    ∃ (a : BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length)
      (b : Fin (E.selectedExpansion k a).count) (c : Fin (R a).count),
      Real.exp (-(q + 3 * P)) ≤ ‖𝔼 u ∈ S, f u * star
        (V.eval (firstTranslationCoordinate (mixedTranslationCoordinates s) a)
            (fun j => correlationInput h (n u) j.1) *
          ((E.selectedExpansion k a).test b).eval ![h, n u, δ] *
          ((R a).test c).eval (fun _ => n u))‖ := by
  let sample (u : Y) : Fin 3 → ℤ := ![h, n u, δ]
  have hc : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star
      (V.eval k (fun j => correlationInput (sample u 0) (sample u 1 + sample u 2) j.1))‖ := hcorr
  obtain ⟨j, v, hjv⟩ := E.transfer_sample_correlation S sample k f
    (fun u _ => coordinateTranslationExpansion_unit V.eval V.unit_eval
      (mixedTranslationCoordinates s) (mixedTranslationSample s (sample u))) hc
  let g (u : Y) := f u * star
    (V.eval (firstTranslationCoordinate (mixedTranslationCoordinates s) j)
        (fun z => correlationInput h (n u) z.1) *
      ((E.selectedExpansion k j).test v).eval (sample u))
  have hg : Real.exp (-(q + 2 * P)) ≤ ‖𝔼 u ∈ S, g u * star
      (translationExpansionRemainder V.eval (mixedTranslationCoordinates s) j
        (mixedTranslationSample s ![h, n u, δ]))‖ := by
    simpa only [V.mixedTranslationExpansion_factor, sample, Matrix.cons_val_zero,
      Matrix.cons_val_one, g, star_mul, mul_assoc, mul_left_comm, mul_comm] using hjv
  obtain ⟨w, hw⟩ := (R j).select_sample_correlation S (fun u (_ : Unit) => n u) g hg
  refine ⟨j, v, w, ?_⟩
  rw [show (q + 2 * P) + P = q + 3 * P by ring] at hw
  simpa only [g, sample, star_mul, mul_assoc, mul_left_comm, mul_comm] using hw

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedFixedReduction
namespace OAI

section

namespace Erdos3.NativeMixedReductionData

open scoped BigOperators

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

def reductionCodeEquiv (k : Fin 4 → Fin V.outputDim) :
    D.ReductionCode k ≃ (Σ t : D.TranslationCode k,
      Fin (D.parallelogram (D.translationCoordinates k t)).count) where
  toFun a := ⟨a.translations, a.term⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance reductionCodeFintype (k : Fin 4 → Fin V.outputDim) :
    Fintype (D.ReductionCode k) :=
  Fintype.ofEquiv _ (D.reductionCodeEquiv k).symm

end Erdos3.NativeMixedReductionData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnnormalizedCommonSymbolFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem bounded_coefficient_derivative_point
    {σ ι κ L : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (b : Basis κ ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1) ⧸
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)))
    (rows : κ → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : (F.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) U))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (C M N : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hN : 0 ≤ N) (l m : ℕ)
    (hslow : ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (M + N) x → ∀ i,
      |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) i| ≤
          C * (M + N) / monomialScale T (rows i).val.1)
    (hgrid : ∀ x, F.FirstCoefficientGrid e ω hF (fun _ => 1) l x →
      b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) ∈ realDenominatorGrid m)
    (h h₀ : σ → ℤ) (hhbox : ∀ i, |(h i : ℝ)| ≤ T i) (hh₀box : ∀ i, |(h₀ i : ℝ)| ≤ T i)
    (S S₀ R R₀ Z : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hh : F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (S + F.realFirstCoefficientAdjoint (fun _ => 1) B R + Z) ∈
        F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U))
    (hh₀ : F.realFirstCoefficientDirectionMap B.coord (fun i => (h₀ i : ℝ)) -
      (S₀ + F.realFirstCoefficientAdjoint (fun _ => 1) B R₀ + Z) ∈
        F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U))
    (hS : F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T M S)
    (hS₀ : F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T N S₀)
    (hR : F.FirstCoefficientGrid e ω hF (fun _ => 1) l R)
    (hR₀ : F.FirstCoefficientGrid e ω hF (fun _ => 1) l R₀) :
    let Y := F.fastCoefficientDirectionCoordinates U b B
    let A := LinearMap.toMatrix b b (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap
    let scale := fun i => monomialScale T (rows i).val.1
    ∃ r : κ → ℝ, r ∈ realDenominatorGrid m ∧
      derivativeGridPoint T scale Y A (h - h₀) r ∈ derivativeGridPoints T scale Y A m ∧
      ‖derivativeGridPoint T scale Y A (h - h₀) r‖ ≤ max 2 (C * (M + N)) := by
  dsimp only
  let V := F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
  let r := b.equivFun (V.mkQ (R - R₀))
  let a := b.equivFun (V.mkQ (S - S₀))
  have hdiff := F.coefficient_common_derivative_difference V B
    (fun i => (h i : ℝ)) (fun i => (h₀ i : ℝ)) S S₀ R R₀ Z hh hh₀
  have hdiff' : F.realFirstCoefficientDirectionMap B.coord (fun i => ((h - h₀) i : ℝ)) -
      ((S - S₀) + F.realFirstCoefficientAdjoint (fun _ => 1) B (R - R₀)) ∈ V := by
    have hcast : (fun i => ((h - h₀) i : ℝ)) =
        (fun i => (h i : ℝ)) - (fun i => (h₀ i : ℝ)) := by
      funext i
      simp only [Pi.sub_apply, Int.cast_sub]
    rw [hcast]
    exact hdiff
  have heq := F.fastCoefficientDerivative_coordinates U b B hB
    (fun i => ((h - h₀) i : ℝ)) (S - S₀) (R - R₀) hdiff'
  have hr : r ∈ realDenominatorGrid m := hgrid (R - R₀)
    (F.firstCoefficientGrid_sub e ω hF (fun _ => 1) l R R₀ hR hR₀)
  have ha : ∀ i, |a i| ≤ C * (M + N) / monomialScale T (rows i).val.1 :=
    hslow (S - S₀) (F.firstCoefficientSlowBound_sub e ω hF (fun _ => 1) T M N S S₀ hS hS₀)
  refine ⟨r, hr, derivativeGridPoint_mem _ _ _ _ m (h - h₀) r hr, ?_⟩
  apply derivativeGridPoint_bound T hT _ (fun i => monomialScale_pos T hT (rows i).val.1)
    _ _ (h - h₀) r a 2 (C * (M + N)) (by norm_num) (mul_nonneg hC (add_nonneg hM hN)) ?_ heq ha
  intro i
  change |((h i - h₀ i : ℤ) : ℝ)| ≤ 2 * T i
  rw [Int.cast_sub]
  exact (abs_sub _ _).trans (by linarith [hhbox i, hh₀box i])

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem bounded_coefficient_difference_inputs
    {σ ι κ L : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (b : Basis κ ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1) ⧸
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)))
    (rows : κ → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : (F.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) U))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) (l m : ℕ)
    (hslow : ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (M + M) x → ∀ i,
      |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) i| ≤
          C * (M + M) / monomialScale T (rows i).val.1)
    (hgrid : ∀ x, F.FirstCoefficientGrid e ω hF (fun _ => 1) l x →
      b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) ∈ realDenominatorGrid m)
    (H : Finset (σ → ℤ)) (h₀ : σ → ℤ) (hh₀ : h₀ ∈ H)
    (S R : (σ → ℤ) → F.RealFirstCoefficientModule (fun _ : σ => 1))
    (Z : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hbox : ∀ h ∈ H, ∀ i, |(h i : ℝ)| ≤ T i)
    (hcommon : ∀ h ∈ H, F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ => 1) B (R h) + Z) ∈
        F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U))
    (hS : ∀ h ∈ H, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T M (S h))
    (hR : ∀ h ∈ H, F.FirstCoefficientGrid e ω hF (fun _ => 1) l (R h)) :
    let Y := F.fastCoefficientDirectionCoordinates U b B
    let A := LinearMap.toMatrix b b (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap
    let scale := fun i => monomialScale T (rows i).val.1
    ∃ D : Finset (σ → ℤ), D.card = H.card ∧
      ∃ q : (σ → ℤ) → κ → ℝ, ∀ h ∈ D,
        q h ∈ realDenominatorGrid m ∧
        ‖derivativeGridPoint T scale Y A h (q h)‖ ≤ max 2 (C * (M + M)) := by
  dsimp only
  apply exists_derivative_difference_inputs T _ _ _ m H h₀ (max 2 (C * (M + M)))
  intro h hh
  obtain ⟨r, hr, _, hnorm⟩ := F.bounded_coefficient_derivative_point
    e ω hF U b rows B hB T hT C M M hC hM hM l m hslow hgrid
    h h₀ (hbox h hh) (hbox h₀ hh₀) (S h) (S h₀) (R h) (R h₀) Z
    (hcommon h hh) (hcommon h₀ hh₀) (hS h hh) (hS h₀ hh₀) (hR h hh) (hR h₀ hh₀)
  exact ⟨r, hr, hnorm⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix TensorProduct

theorem common_coefficient_derivative_system
    {σ ι L : Type*} [Fintype σ] [DecidableEq σ] {d : ℕ}
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1) ⧸
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)))
    (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (hblock : ∀ i j, (rows j).val.1 ≠ i.val.1 →
      b.repr ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ
          (F.realFirstCoefficientBasis e ω hF (fun _ => 1) i)) j = 0)
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : (F.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) U))
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i) (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) (l m : ℕ)
    (hslow : ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (M + M) x → ∀ i,
      |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) i| ≤
          C * (M + M) / monomialScale T (rows i).val.1)
    (hgrid : ∀ x, F.FirstCoefficientGrid e ω hF (fun _ => 1) l x →
      b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) ∈ realDenominatorGrid m)
    (H : Finset (σ → ℤ)) (h₀ : σ → ℤ) (hh₀ : h₀ ∈ H)
    (S R : (σ → ℤ) → F.RealFirstCoefficientModule (fun _ : σ => 1))
    (Z : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hbox : ∀ h ∈ H, ∀ i, |(h i : ℝ)| ≤ T i)
    (hcommon : ∀ h ∈ H, F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ => 1) B (R h) + Z) ∈
        F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U))
    (hS : ∀ h ∈ H, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T M (S h))
    (hR : ∀ h ∈ H, F.FirstCoefficientGrid e ω hF (fun _ => 1) l (R h))
    (haction : ∀ i j, ω (rows i).val.2 ≤ ω (rows j).val.2 →
      LinearMap.toMatrix b b
        (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap i j =
          (1 : Matrix (Fin d) (Fin d) ℝ) i j)
    (hm : 0 < m) (δ p : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hdim : ((Fintype.card σ + Fintype.card (Fin d) : ℕ) : ℝ) ≤ p)
    (hmcap : (m : ℝ) ≤ Real.exp p) (hRcap : max 2 (C * (M + M)) ≤ Real.exp p)
    (hδcap : δ⁻¹ ≤ Real.exp p) (Tmin : ℝ)
    (hmin : Real.exp ((p + 2) ^ 3) < Tmin) (hside : ∀ i, Tmin ≤ T i) :
    ∃ (perm : Equiv.Perm (Fin d)) (a : ℕ) (ha : a ≤ d),
      (∀ i, i.val < a ↔ (rows (perm i)).val.1 = 0) ∧
      let b' := b.reindex perm.symm
      let f := F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB
      let A' := b'.equivFun.symm.trans (f.trans b'.equivFun)
      ∃ η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)),
      (∀ x, η (fun i => b'.equivFun x (Fin.castLE ha i)) =
        F.realFastCoefficientHorizontal (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U) x) ∧
      Nonempty (CoordinateDerivativeSystem ha T (F.fastCoefficientDirectionCoordinates U b' B) A'
        (fun i => monomialScale T (rows (perm i)).val.1) (Real.exp ((p + 2) ^ 3))) := by
  have hTpos : ∀ i, 0 < T i := fun i => lt_of_lt_of_le zero_lt_one (hT i)
  obtain ⟨D, hDcard, q, hq⟩ := F.bounded_coefficient_difference_inputs e ω hF U b rows
    B hB T hTpos C M hC hM l m hslow hgrid H h₀ hh₀ S R Z hbox hcommon hS hR
  let V := F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
  let Y := V.mkQ.comp (F.realFirstCoefficientDirectionMap B.coord)
  let f := F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB
  have hDdense : δ * ∏ i, T i ≤ (D.card : ℝ) := by rw [hDcard]; exact hdense
  obtain ⟨perm, a, ha, hzero, hsystem⟩ :=
    firstCoefficient_coordinate_system ω rows b Y f haction T hT m hm
    (max 2 (C * (M + M))) δ
    ((by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)) hδ D q
    (fun h hh => (hq h hh).1) (fun h hh => (hq h hh).2) hDdense
    p hp hdim hmcap hRcap hδcap Tmin hmin hside
  have hblock' : ∀ i j, (rows (perm j)).val.1 ≠ i.val.1 →
      (b.reindex perm.symm).repr (V.mkQ
        (F.realFirstCoefficientBasis e ω hF (fun _ => 1) i)) j = 0 := by
    intro i j hij
    simpa only [Basis.repr_reindex_apply, Equiv.symm_symm] using hblock i (perm j) hij
  let η := F.realFastCoefficientHorizontalEquiv e ω hF (fun _ : σ => 1) (by simp)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
    (b.reindex perm.symm) (fun i => rows (perm i)) hblock' ha hzero
  refine ⟨perm, a, ha, hzero, η, ?_, hsystem⟩
  exact F.realFastCoefficientHorizontalEquiv_projection e ω hF (fun _ : σ => 1) (by simp)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
    (b.reindex perm.symm) (fun i => rows (perm i)) hblock' ha hzero

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped Matrix TensorProduct

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf

theorem exists_initialFormalState_from_common (C D : ℕ)
    (hbudget : ∀ p : ℝ, 0 ≤ p →
      commonInitialParameter p + 1 ≤ (p + D) ^ D ∧
      (commonInitialParameter p + 2) ^ 3 ≤ (p + D) ^ D ∧
      (commonInitialParameter p + C) ^ C ≤ (p + D) ^ D)
    (hinit : ∀ a : ℕ, F.ExtractedInitialStateSpec (σ := σ) (τ := τ) (a := a) (d := d) e ω hF W C) :
    F.CommonInitialStateSpec (σ := σ) (τ := τ) (d := d) e ω hF W D := by
  intro H p hH hp hι hσ hτ hd hHp hstructure hW v hv hheight g₀ hzero
    b rows sectionMap hsection Cscale hC hCp hweighted δ hδ hδp hprojectionGrid hsectionGrid
    hblock haction T hT M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z hbox hcommon hS hR
    density hdensity hdensityp hdense
  let q := commonExtractionParameter p
  let r := commonInitialParameter p
  have hcontrol := commonExtractionParameter_controls hp
  have hpq : p ≤ q := hcontrol.1
  have hqr : q ≤ r := hcontrol.2.2.2
  have hpr : p ≤ r := hpq.trans hqr
  have hq : 0 ≤ q := hp.trans hpq
  have hr : 0 ≤ r := hp.trans hpr
  have hepq := Real.exp_le_exp.mpr hpq
  have hepr := Real.exp_le_exp.mpr hpr
  have hb := hbudget p hp
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hTlarge (i : σ) : Real.exp (r + 1) ≤ T i :=
    (Real.exp_le_exp.mpr hb.1).trans (hT i)
  have hTone (i : σ) : 1 ≤ T i := (Real.one_le_exp (by linarith : 0 ≤ r + 1)).trans (hTlarge i)
  have hproducts := commonExtractionParameter_products hp hC hCp hM hMp δ l hδp hlp
  have hdim : ((Fintype.card σ + Fintype.card (Fin d) : ℕ) : ℝ) ≤ q := by
    rw [Nat.cast_add, Fintype.card_fin]
    calc
      _ ≤ p + p := add_le_add hσ hd
      _ ≤ q := by linarith [hcontrol.2.1]
  have hmin : Real.exp ((q + 2) ^ 3) < Real.exp (r + 1) :=
    Real.exp_lt_exp.mpr (by change r < r + 1; linarith)
  have hextract := F.common_coefficient_derivative_system e ω hF Wf b rows hblock
    g₀.val g₀.property T hTone Cscale M hC hM l (δ * l)
    ((hweighted T hTpos (M + M) (add_nonneg hM hM)).1)
    (hprojectionGrid l) Hshifts h₀ hh₀ S R Z hbox hcommon hS hR haction
    (Nat.mul_pos hδ hl) density q hdensity hq hdense hdim hproducts.2 hproducts.1
    (hdensityp.trans hepq) (Real.exp (r + 1)) hmin hTlarge
  obtain ⟨perm, a, ha, _, η, hη, ⟨sys⟩⟩ := hextract
  have hsection' := F.exists_reindexed_fast_coefficient_section e ω hF
    (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf b rows sectionMap hsection δ Cscale
    hprojectionGrid hsectionGrid hweighted perm
  obtain ⟨sectionMap', hright', hproj', hgrid', hweighted'⟩ := hsection'
  have har : (a : ℝ) ≤ r := (Nat.cast_le.mpr ha).trans (hd.trans hpr)
  have hTr (i : σ) : Real.exp ((r + C) ^ C) ≤ T i :=
    (Real.exp_le_exp.mpr hb.2.2).trans (hT i)
  have hout := hinit a H r hH hr (hι.trans hpr) (hσ.trans hpr) (hτ.trans hpr) har
    (hHp.trans hepr) hstructure hW v hv hheight g₀ hzero (b.reindex perm.symm)
    (fun i => rows (perm i)) ha η hη sectionMap' hright' Cscale hC (hCp.trans hepr)
    hweighted' δ hδ (hδp.trans hepr) hproj' hgrid' T hTr
    (Real.exp r) (Real.exp_nonneg _) le_rfl sys
  obtain ⟨hk, K, bK, Hk, hHk, hHkp, hKheight, m, hm, hmp, x, g, z, hfactor, hx, hz, X, hX⟩ := hout
  refine ⟨sys.k, hk.trans ha, K, bK, Hk, hHk,
    hHkp.trans (Real.exp_le_exp.mpr hb.2.1), hKheight, m, hm,
    hmp.trans (Real.exp_le_exp.mpr hb.2.2), x, g, z, hfactor, ?_, hz,
    X.enlarge hb.2.2 hTpos, hX⟩
  exact F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hTpos
    (Real.exp_le_exp.mpr hb.2.2) x.val.coord hx

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

omit [DecidableEq σ] in
theorem exists_initialFormalState_from_common_family (c C D : ℕ)
    (hcoords : FullFastCoefficientCoordinateSpec.{uσ, uι, uτ, uL} s c)
    (hcommonState : ∀ d : ℕ,
      F.CommonInitialStateSpec (σ := σ) (τ := τ) (d := d) e ω hF W C)
    (hbudget : ∀ p : ℝ, 0 ≤ p → (fullInitialParameter s c p + C) ^ C ≤ (p + D) ^ D) :
    F.FullInitialStateSpec (σ := σ) (τ := τ) e ω hF W D := by
  intro H p hH hp hι hσ hτ hHp hstructure hW v hv hheight g₀ hzero T hT
    M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z hbox hcommon hS hR density hdensity hdensityp hdense
  have hcoordinateData := hcoords F e ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    W hW v hv hH hheight hp hι hσ hτ hHp
  obtain ⟨d, hd, rows, _, b, sectionMap, δ, hδ, hδp, hproj, hgrid, hright,
    hweighted, hblock, haction⟩ := hcoordinateData
  let q := fullInitialParameter s c p
  have hcontrol := fullInitialParameter_controls s c hp
  have hpq : p ≤ q := hcontrol.1
  have hq : 0 ≤ q := hp.trans hpq
  have hepq := Real.exp_le_exp.mpr hpq
  have hcoordinateBound : Real.exp ((p + c) ^ c) ≤ Real.exp q :=
    Real.exp_le_exp.mpr hcontrol.2.2
  have hdim : (d : ℝ) ≤ q := by
    have hd' : (d : ℝ) ≤
        (Fintype.card ι : ℝ) * (s + 2) * ((Fintype.card σ : ℝ) + 1) ^ (s + 1) := by
      exact_mod_cast hd
    apply hd'.trans
    apply le_trans _ hcontrol.2.1
    gcongr
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hTq (i : σ) : Real.exp ((q + C) ^ C) ≤ T i :=
    (Real.exp_le_exp.mpr (hbudget p hp)).trans (hT i)
  have hout := hcommonState d H q hH hq (hι.trans hpq) (hσ.trans hpq) (hτ.trans hpq) hdim
    (hHp.trans hepq) hstructure hW v hv hheight g₀ hzero b rows sectionMap hright
    (Real.exp ((p + c) ^ c)) (Real.exp_nonneg _) hcoordinateBound hweighted
    δ hδ (hδp.trans hcoordinateBound) hproj hgrid hblock (haction g₀.val g₀.property)
    T hTq M hM (hMp.trans hepq) l hl (hlp.trans hepq) Hshifts h₀ hh₀ S R Z
    hbox hcommon hS hR density hdensity (hdensityp.trans hepq) hdense
  exact hout.mono F e ω hF W hd (hbudget p hp) hTpos

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeRetainedIntegerMultilinearQuadruples
namespace OAI

section

namespace Erdos3.NativeCrossWitnesses

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

theorem integerLower_val (h : H) (x : ZMod N) : U.integerLower h x.val = U.lower h x := rfl

theorem integerProduct_val (M : ZMod N → ℤ → ℂ)
    (hM : ∀ h x, m h x = M h x.val) (h : H) (x : ZMod N) :
    U.integerProduct M h x.val = U.product h x := by
  rw [integerProduct, integerLower_val, product, hM]
  rfl

end Erdos3.NativeCrossWitnesses

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankRelationExistence
namespace OAI

section

namespace Erdos3

namespace NativeWeightedRankIntervals

theorem exists_anchored_fibers {s r N : ℕ} [NeZero N] {b p : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} (F : NativeWeightedRankIntervals W out H p) :
    Nonempty (NativeAnchoredRankFibers F) := by
  have hindex : Function.Injective (fun i => ((F.index i).1, (F.index i).2.1, (F.index i).2.2)) :=
    F.index_injective
  have hsize : Real.exp (-p) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ Fintype.card (Fin F.count) := by
    simpa only [Fintype.card_fin] using F.density
  obtain ⟨anchor, branch, T, A, hA, hAsize, hT, hinj, hfiber⟩ := exists_dense_anchored_fibers
    (fun i => (F.index i).1) (fun i => (F.index i).2.1) (fun i => (F.index i).2.2)
    F.branch hindex (Real.exp_pos (-p)) hsize
  exact ⟨{
    anchor := anchor
    branch := branch
    selected := T
    parameters := A
    parameters_nonempty := hA
    parameters_density := hAsize
    anchor_eq := fun i hi => (hT i hi).1
    branch_eq := fun i hi => (hT i hi).2
    pair_injective := hinj
    fiber_density := hfiber }⟩

end NativeWeightedRankIntervals

end Erdos3

end

end OAI
end


