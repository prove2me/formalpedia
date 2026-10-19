-- Prove2me | Definitions.Def_OAIE3v2B141
-- name    : OAIE3v2B141
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:56:35.244433+00:00
-- url     : https://prove2.me/theorems/034d8ef6-fd77-4589-a458-08dd5fa489f6
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 143 of 311
-- statement:
--   Definitions bundle 143 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B111`, `OAIE3v2B128`, `OAIE3v2B129` of this split.
--
--   Modules: `Estimates/FastCoefficientImage.lean`, `Estimates/FirstCoefficientDerivativeBounds.lean`, `Estimates/FormalInductionTerminal.lean`, `Estimates/NativeEquivalenceTransitivity.lean`, `Estimates/NativeMeanRowCorrelation.lean`, `Estimates/NativeOptionOriginalOrbit.lean`, `Estimates/OptionMarkedSurjective.lean`, `Estimates/PreparedFiniteForwardFixedCenterThreshold.lean`, `Estimates/QuantitativeNoninjectivity.lean`, `Estimates/RealFirstCoefficientHorizontal.lean`, `Estimates/RealProductInclusion.lean`, `Estimates/RealifiedTopQuotient.lean`, `Estimates/ReducedNativeFactorization.lean`, `Estimates/ReducedRelativeCoefficientBounds.lean`, `Estimates/RestrictedSymbolAlgebraicMajorStep.lean`, `Fourier/JoinedFrequencyQuotientInjectivity.lean`, `Geometry/CoordinateQuotientModel.lean`, `Linear/NativeRankQuotientOrbit.lean`, `Linear/RealFirstCoefficientBasis.lean`, `Linear/ReducedSquareFastKernel.lean`, `Linear/SquareSymbolProjection.lean`, `Nilpotent/CyclicNiltestApproximation.lean`, `Nilpotent/NiltestComplement.lean`, `Nilpotent/RealifiedBCHProductEquiv.lean`, `Polynomial/FirstCoefficientPolynomialDerivative.lean`, `Polynomial/FormalPolynomialCorrectionStep.lean`, `Polynomial/NativePolynomialOrbit.lean`, `Polynomial/PolynomialLiftArrays.lean`, `Polynomial/RaisedDegreeRank.lean`, `Polynomial/RealSquarePolynomialFactors.lean`, `Polynomial/RelativeSquarePolynomial.lean`, `Sampling/RealAdaptedCoefficientGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B111
import Definitions.Def_OAIE3v2B128
import Definitions.Def_OAIE3v2B129

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RelativeSquarePolynomial
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem relativeSquareSymbolMap_eq_zero_iff (p : F.normalizedRelativeSubmodule w) :
    F.relativeSquareSymbolMap w hw p = 0 ↔ p.val ∈ F.shiftedPolynomialIdeal w 2 := by
  change F.squareFiltration.polynomialSymbolMap w (F.relativeSquareLift w hw p) = 0 ↔ _
  rw [F.squareFiltration.polynomialSymbolMap_eq_zero_iff]
  constructor
  · intro hp α
    have ha := hp α
    change (coefficients (F.relativeSquarePolynomial w hw p) α : L × L) ∈
      F.squareLayer (Finsupp.weight w α + 1) at ha
    rw [F.relativeSquarePolynomial_coefficient] at ha
    change coefficients p.val.val α ∈ F.layer (Finsupp.weight w α + 2)
    simpa only [sub_zero] using ha.2.2
  · intro hp α
    change (coefficients (F.relativeSquarePolynomial w hw p) α : L × L) ∈
      F.squareLayer (Finsupp.weight w α + 1)
    rw [F.relativeSquarePolynomial_coefficient]
    refine ⟨p.property.1 α, (F.layer _).zero_mem, ?_⟩
    change coefficients p.val.val α - 0 ∈ F.layer (Finsupp.weight w α + 2)
    rw [sub_zero]
    exact hp α

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquareSymbolProjection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

variable (hw : ∀ i, 0 < w i)

theorem relativeSquareSymbolMap_range :
    LinearMap.range (F.relativeSquareSymbolMap w hw) = (F.squareSndSymbolMap w).ker.toSubmodule := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    exact F.squareSndSymbolMap_relative w hw p
  · intro x hx
    obtain ⟨r, rfl⟩ := F.squareFiltration.polynomialSymbolMap_surjective w x
    have hs : ∀ α, (coefficients r.val α).val.2 ∈ F.layer (Finsupp.weight w α + 1) :=
      (F.squareSndSymbolMap_map_eq_zero_iff w r).mp hx
    let p : VectorPolynomial σ ℚ L :=
      VectorPolynomial.map F.squareFst.toLinearMap r.val - VectorPolynomial.map F.squareSnd.toLinearMap r.val
    have hc (α : σ →₀ ℕ) : coefficients p α =
        (coefficients r.val α).val.1 - (coefficients r.val α).val.2 := by
      simp only [p, map_sub, Finsupp.sub_apply, coefficients_map]
      rfl
    have hp : ∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α + 1) := by
      intro α
      rw [hc]
      exact (r.property α).2.2
    have hpa : p ∈ F.adaptedLieSubalgebra w :=
      fun α => F.antitone (Nat.le_succ _) (hp α)
    have hp0 : coefficients p 0 ∈ F.layer 2 := by
      rw [hc]
      exact (F.mem_squareLieSubalgebra _).mp (coefficients r.val 0).property
    let q : F.normalizedRelativeSubmodule w := ⟨⟨p, hpa⟩, hp, hp0⟩
    refine ⟨q, ?_⟩
    apply (F.squareFiltration.polynomialSymbolMap_eq_iff w (F.relativeSquareLift w hw q) r).mpr
    intro α
    rw [map_sub, Finsupp.sub_apply]
    change (coefficients (F.relativeSquarePolynomial w hw q) α).val - (coefficients r.val α).val ∈
      F.squareLayer (Finsupp.weight w α + 1)
    rw [F.relativeSquarePolynomial_coefficient]
    change (coefficients p α, (0 : L)) - (coefficients r.val α).val ∈ _
    rw [hc]
    have he : ((coefficients r.val α).val.1 - (coefficients r.val α).val.2, (0 : L)) -
        (coefficients r.val α).val = (-(coefficients r.val α).val.2, -(coefficients r.val α).val.2) := by
      apply Prod.ext <;> dsimp <;> abel
    rw [he]
    exact ⟨(F.layer _).neg_mem (hs α), (F.layer _).neg_mem (hs α), by simp⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastCoefficientImage
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem firstCoefficientMap_surjective : Function.Surjective (F.firstCoefficientMap w) :=
  Submodule.mkQ_surjective _

theorem normalizedFirstCoefficientMap_range :
    LinearMap.range (F.normalizedFirstCoefficientMap w) = LinearMap.ker (F.firstCoefficientHorizontal w) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).mpr p.property.2
  · intro hx
    obtain ⟨p, rfl⟩ := F.firstCoefficientMap_surjective w x
    have hp : coefficients p.val.val 0 ∈ F.layer 2 := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact ⟨⟨p.val, p.property, hp⟩, rfl⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareSndSymbolKernel_lift {x : F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hx : F.reducedSquareSndSymbolMap w x = 0) :
    ∃ y : F.squareFiltration.PolynomialSymbol w,
      F.squareSndSymbolMap w y = 0 ∧ F.reducedSquareSymbolMap w y = x := by
  obtain ⟨y, rfl⟩ := F.reducedSquareSymbolMap_surjective w x
  refine ⟨y - F.squareDiagonalSymbolMap w (F.squareSndSymbolMap w y), ?_, ?_⟩
  · rw [map_sub, F.squareSndSymbolMap_diagonal, sub_self]
  · rw [map_sub, ← F.reducedSquareDiagonalSymbolMap_quotient,
      ← F.reducedSquareSndSymbolMap_quotient, hx, map_zero, sub_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem reducedRelativeSquareSymbolMap_range :
    LinearMap.range (F.reducedRelativeSquareSymbolMap w hw) =
      (F.reducedSquareSndSymbolMap w).ker.toSubmodule := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    exact F.reducedRelativeSquareSymbolMap_projection w hw p
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := F.reducedSquareSndSymbolKernel_lift w hx
    have hr : y ∈ LinearMap.range (F.relativeSquareSymbolMap w hw) := by
      rw [F.relativeSquareSymbolMap_range w hw]
      exact hy
    obtain ⟨p, rfl⟩ := hr
    exact ⟨p, rfl⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

theorem reducedRelativeSquareSymbolMap_eq_zero_iff (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : F.normalizedRelativeSubmodule w) :
    F.reducedRelativeSquareSymbolMap w hw p = 0 ↔ p.val ∈ F.shiftedPolynomialIdeal w 2 := by
  constructor
  · intro hp α
    change coefficients p.val.val α ∈ F.layer (Finsupp.weight w α + 2)
    change F.squareFiltration.quotientTop.polynomialSymbolMap w
      (F.reducedSquarePolynomialMap w (F.relativeSquareLift w hw p)) = 0 at hp
    have hα := (F.squareFiltration.quotientTop.polynomialSymbolMap_eq_zero_iff w _).mp hp α
    have hd := F.reducedSquareDifference_mem_layer (Finsupp.weight w α + 1) _ hα
    change F.reducedSquareDifference
      (coefficients (map (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))).toLinearMap
        (F.relativeSquarePolynomial w hw p)) α) ∈ _ at hd
    rw [coefficients_map] at hd
    change F.reducedSquareDifference
      (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
        (coefficients (F.relativeSquarePolynomial w hw p) α)) ∈ _ at hd
    rw [F.reducedSquareDifference_mk, F.relativeSquarePolynomial_coefficient] at hd
    simpa only [sub_zero, Nat.add_assoc] using hd
  · intro hp
    rw [F.reducedRelativeSquareSymbolMap_apply,
      (F.relativeSquareSymbolMap_eq_zero_iff w hw p).mpr hp, map_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem normalizedFirstCoefficientMap_ker :
    LinearMap.ker (F.normalizedFirstCoefficientMap w) =
      LinearMap.ker (F.reducedRelativeSquareSymbolMap w hw) := by
  ext p
  change F.normalizedFirstCoefficientMap w p = 0 ↔ F.reducedRelativeSquareSymbolMap w hw p = 0
  rw [F.normalizedFirstCoefficientMap_eq_zero_iff, F.reducedRelativeSquareSymbolMap_eq_zero_iff]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealFirstCoefficientHorizontal
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

noncomputable def realAdaptedLogDerivative
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1) :=
  dualLogDerivative (F.realAdaptedPolynomialJet h x)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realAdaptedDirectionalTangent
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (σ → ℚ) →ₗ[ℚ] (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) where
  toFun h := F.realAdaptedDirectionalDerivative h x
  map_add' h k := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r p =>
      change r ⊗ₜ[ℚ] (F.adaptedDirectionalTangent p (h + k)) =
        r ⊗ₜ[ℚ] (F.adaptedDirectionalTangent p h) + r ⊗ₜ[ℚ] (F.adaptedDirectionalTangent p k)
      rw [map_add, TensorProduct.tmul_add]
    | add x y hx hy => simp only [map_add, hx, hy]; abel
  map_smul' q h := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r p =>
      change r ⊗ₜ[ℚ] (F.adaptedDirectionalTangent p (q • h)) =
        q • (r ⊗ₜ[ℚ] (F.adaptedDirectionalTangent p h))
      rw [map_smul, TensorProduct.tmul_smul]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]

noncomputable def realLogDerivativeDirectionMap
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (σ → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :=
  (dualRealLogarithmicDifferential
    (hnil := (F.adaptedPolynomialFiltration (fun _ : σ => 1)).realification.lowerCentralSeries_eq_bot)
      x).comp (realDirectionExtension (F.realAdaptedDirectionalTangent x))

theorem realLogDerivativeDirectionMap_rat
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) (h : σ → ℚ) :
    F.realLogDerivativeDirectionMap x (fun i => (h i : ℝ)) = F.realAdaptedLogDerivative h x := by
  change dualRealLogarithmicDifferential x
    (realDirectionExtension (F.realAdaptedDirectionalTangent x) (fun i => (h i : ℝ))) = _
  rw [realDirectionExtension_rat]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realAdaptedDirectionalDerivative_mem_first [Fintype σ] (h : σ → ℚ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedDirectionalDerivative h x ∈ F.realShiftedCoefficientSubmodule (fun _ => 1) 1 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r p =>
    change r ⊗ₜ[ℚ] (F.adaptedDirectionalDerivative h p) ∈
      (F.shiftedPolynomialIdeal (fun _ => 1) 1).toSubmodule.baseChange ℝ
    exact Submodule.tmul_mem_baseChange_of_mem r (F.directionalDerivative_mem_next h p)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem realAdaptedLogDerivative_mem_first [Fintype σ] (h : σ → ℚ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedLogDerivative h x ∈ F.realShiftedCoefficientSubmodule (fun _ => 1) 1 := by
  apply dualLogDerivative_mem_of_invariant ⊤
    ((F.realShiftedCoefficientSubmodule (fun _ => 1) 1).restrictScalars ℚ)
    (fun a _ b hb => F.realShiftedCoefficient_lie_mem (fun _ => 1) 1 a b hb)
    (F.realAdaptedPolynomialJet h x) (by trivial)
  rw [F.realAdaptedPolynomialJet_tangent]
  exact F.realAdaptedDirectionalDerivative_mem_first h x

theorem realLogDerivativeDirectionMap_mem_first [Fintype σ]
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) (h : σ → ℝ) :
    F.realLogDerivativeDirectionMap x h ∈ F.realShiftedCoefficientSubmodule (fun _ => 1) 1 := by
  classical
  have he : h = ∑ i, h i • Pi.single i (1 : ℝ) := by ext j; simp [Pi.single_apply]
  rw [he, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  have hunit : (Pi.single i (1 : ℝ)) = (fun j => (((Pi.single i (1 : ℚ) : σ → ℚ) j) : ℝ)) := by
    ext j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  rw [hunit, F.realLogDerivativeDirectionMap_rat]
  exact F.realAdaptedLogDerivative_mem_first _ x

noncomputable def realFirstCoefficientDirectionMap [Fintype σ]
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (σ → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule (fun _ : σ => 1) :=
  (F.realFirstCoefficientMap (fun _ => 1)).comp
    ((F.realLogDerivativeDirectionMap x).codRestrict
      (F.realShiftedCoefficientSubmodule (fun _ => 1) 1) (F.realLogDerivativeDirectionMap_mem_first x))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def firstCoefficientRealEquiv :
    (ℝ ⊗[ℚ] F.FirstCoefficientModule w) ≃ₗ[ℝ] F.RealFirstCoefficientModule w :=
  realSubquotientEquiv (F.shiftedPolynomialIdeal w 1).toSubmodule (F.shiftedPolynomialIdeal w 2).toSubmodule

noncomputable def realFirstCoefficientHorizontal :
    F.RealFirstCoefficientModule w →ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :=
  ((F.firstCoefficientHorizontal w).baseChange ℝ).comp (F.firstCoefficientRealEquiv w).symm.toLinearMap

noncomputable def realNormalizedFirstCoefficientMap :
    (ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) →ₗ[ℝ] F.RealFirstCoefficientModule w :=
  (F.firstCoefficientRealEquiv w).toLinearMap.comp ((F.normalizedFirstCoefficientMap w).baseChange ℝ)

theorem realNormalizedFirstCoefficientMap_range :
    LinearMap.range (F.realNormalizedFirstCoefficientMap w) = LinearMap.ker (F.realFirstCoefficientHorizontal w) := by
  have hr : LinearMap.range ((F.normalizedFirstCoefficientMap w).baseChange ℝ) =
      LinearMap.ker ((F.firstCoefficientHorizontal w).baseChange ℝ) := by
    rw [← realification_ker, ← F.normalizedFirstCoefficientMap_range w]
    have he := realification_map (⊤ : Submodule ℚ (F.normalizedRelativeSubmodule w))
      (F.normalizedFirstCoefficientMap w)
    simpa only [Submodule.map_top, Submodule.baseChange_top] using he.symm
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    change (F.firstCoefficientHorizontal w).baseChange ℝ
      ((F.firstCoefficientRealEquiv w).symm (F.firstCoefficientRealEquiv w
        ((F.normalizedFirstCoefficientMap w).baseChange ℝ p))) = 0
    rw [LinearEquiv.symm_apply_apply]
    exact hr.le ⟨p, rfl⟩
  · intro hx
    have hy : (F.firstCoefficientRealEquiv w).symm x ∈
        LinearMap.range ((F.normalizedFirstCoefficientMap w).baseChange ℝ) := hr.ge hx
    obtain ⟨p, hp⟩ := hy
    refine ⟨p, ?_⟩
    change F.firstCoefficientRealEquiv w ((F.normalizedFirstCoefficientMap w).baseChange ℝ p) = x
    rw [hp, LinearEquiv.apply_symm_apply]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FormalPolynomialCorrectionStep
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]

namespace NilpotentLieFiltration

theorem realGradedSymbolPolynomial_mem_gradedPolynomialSubmodule
    {M κ : Type*} [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration M s) (b : Basis κ ℚ M) (w : κ → ℕ)
    (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (v : σ → ℕ) (x : F.RealPolynomialSymbol v) :
    F.realGradedSymbolPolynomial b w hF v x ∈
      gradedPolynomialSubmodule ((F.associatedGradedBasis b w hF).baseChange ℝ) w v := by
  intro α
  change basisGradeProjection ((F.associatedGradedBasis b w hF).baseChange ℝ) w
    (Finsupp.weight v α) (coefficients (F.realGradedSymbolPolynomial b w hF v x) α) = _
  apply ((F.associatedGradedBasis b w hF).baseChange ℝ).repr.injective
  apply Finsupp.ext
  intro i
  rw [basisGradeProjection_repr]
  by_cases hi : w i = Finsupp.weight v α
  · rw [if_pos hi]
  · rw [if_neg hi]
    exact (F.realGradedSymbolPolynomial_coordinate_of_ne b w hF v x α i (Ne.symm hi)).symm

end NilpotentLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RealAdaptedCoefficientGrid
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

def RealAdaptedCoefficientGrid (l : ℕ) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) : Prop :=
  (fun z : AdaptedBasisIndex w ω => ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr x z)
    ∈ realDenominatorGrid l

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealFirstCoefficientBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realShiftedCoefficient_eq_span (w : σ → ℕ) (k : ℕ) :
    F.realShiftedCoefficientSubmodule w k = Submodule.span ℝ
      ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ ''
        {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}) := by
  change (F.shiftedPolynomialIdeal w k).toSubmodule.baseChange ℝ = _
  rw [F.shiftedPolynomialIdeal_eq_span_monomialBasis b ω hF,
    Submodule.baseChange_span, Set.image_image]
  congr 2
  funext z
  exact (Basis.baseChange_apply ℝ (F.adaptedMonomialBasis b ω hF w) z).symm

noncomputable def realShiftedMonomialBasis (w : σ → ℕ) (k : ℕ) :
    Basis (ShiftedMonomialIndex w ω k) ℝ (F.realShiftedCoefficientSubmodule w k) :=
  supportedSubmoduleBasis ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ)
    (F.realShiftedCoefficientSubmodule w k)
    {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}
    (F.realShiftedCoefficient_eq_span b ω hF w k)

@[simp] theorem realShiftedMonomialBasis_coe (w : σ → ℕ) (k : ℕ) (z : ShiftedMonomialIndex w ω k) :
    (F.realShiftedMonomialBasis b ω hF w k z : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) =
      (F.adaptedMonomialBasis b ω hF w).baseChange ℝ z.val :=
  supportedSubmoduleBasis_coe _ _ _ _ z

theorem realShiftedCoefficient_next_eq_span (w : σ → ℕ) (k : ℕ) :
    (F.realShiftedCoefficientSubmodule w (k + 1)).comap (F.realShiftedCoefficientSubmodule w k).subtype =
      Submodule.span ℝ (F.realShiftedMonomialBasis b ω hF w k ''
        {z | Finsupp.weight w z.val.val.1 + (k + 1) ≤ ω z.val.val.2}) := by
  have hP := F.realShiftedCoefficient_eq_span b ω hF w k
  have hQ := F.realShiftedCoefficient_eq_span b ω hF w (k + 1)
  have hdata := supportedSubmoduleBasis_comap_span
    ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ)
    (F.realShiftedCoefficientSubmodule w k) (F.realShiftedCoefficientSubmodule w (k + 1))
    {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}
    {z | Finsupp.weight w z.val.1 + (k + 1) ≤ ω z.val.2} hP hQ
  exact hdata

noncomputable def realFirstCoefficientBasis (w : σ → ℕ) :
    Basis (FirstCoefficientIndex w ω) ℝ (F.RealFirstCoefficientModule w) :=
  (supportedQuotientBasis (F.realShiftedMonomialBasis b ω hF w 1)
    ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype)
    {z | Finsupp.weight w z.val.val.1 + 2 ≤ ω z.val.val.2}
    (F.realShiftedCoefficient_next_eq_span b ω hF w 1)).reindex (firstCoefficientSurvivorEquiv w ω)

@[simp] theorem realFirstCoefficientBasis_apply (w : σ → ℕ) (z : FirstCoefficientIndex w ω) :
    F.realFirstCoefficientBasis b ω hF w z =
      F.realFirstCoefficientMap w
        (F.realShiftedMonomialBasis b ω hF w 1 ((firstCoefficientSurvivorEquiv w ω).symm z).val) := by
  rw [realFirstCoefficientBasis, Basis.reindex_apply, supportedQuotientBasis_apply]
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FirstCoefficientDerivativeBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def realAdaptedConstant :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :=
  (F.adaptedConstantLieHom w).toLinearMap.baseChange ℝ

theorem realAdaptedConstant_mem_first (x : ℝ ⊗[ℚ] L) :
    F.realAdaptedConstant w x ∈ F.realShiftedCoefficientSubmodule w 1 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul r x =>
    exact Submodule.tmul_mem_baseChange_of_mem r (F.adaptedConstant_mem_shiftedIdeal w x)

noncomputable def realFirstCoefficientConstant :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] F.RealFirstCoefficientModule w :=
  (F.realFirstCoefficientMap w).comp
    ((F.realAdaptedConstant w).codRestrict (F.realShiftedCoefficientSubmodule w 1)
      (F.realAdaptedConstant_mem_first w))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalInductionTerminal
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}

def FormalCorrectionProperty (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L)
    (w : μ → ℕ) (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (g : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot) : Prop :=
  (∀ α, coefficients g.coord α ∈ U) ∧
    g.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
    coefficients g.coord 0 = 0

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

open Module
open scoped BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem pi_geometry {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hD : ∀ i, (D i).GeometryComplexityLE p) :
    (pi D).GeometryComplexityLE ((p + 2) ^ 2) := by
  classical
  have hdim : (Fintype.card (Σ i, Fin (d i)) : ℝ) ≤ p ^ 2 :=
    sigma_card_le_budget hp hι (fun i => by simpa only [Fintype.card_fin] using (hD i).1)
  have hgrid : ((∏ i, (D i).grid : ℕ) : ℝ) ≤ Real.exp (p ^ 2) :=
    product_denominator_le_budget (fun i => (D i).grid) hp hι (fun i => (hD i).2.1)
  have hsmall : p + 1 ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
  have hsq : p ^ 2 ≤ (p + 2) ^ 2 := by nlinarith
  refine ⟨hdim.trans hsq, hgrid.trans (Real.exp_le_exp.mpr hsq), ?_, ?_⟩
  · intro i j k
    change rationalLogHeight (lieStructureConstants (productFinBasis D) i j k) ≤ _
    rw [productFinBasis, lieStructureConstants_reindex]
    have hh := lie_pi_structure_height (fun i => (D i).basis) (one_le_ceil_exp p)
      (fun a i j k => rationalHeightLE_ceil_exp ((hD a).2.2.1 i j k))
    exact (rationalLogHeight_le_of_height (hh _ _ _) (ceil_exp_le_exp_add_one hp)).trans hsmall
  · change ∀ (j : Fin (s + 1))
      (k : Fin (finrank ℚ ((NilpotentLieFiltration.pi (fun i => (D i).filtration)).layer (j.val + 1))))
      (l : Fin (Fintype.card (Σ i, Fin (d i)))),
        rationalLogHeight ((productFinBasis D).repr ((productLayerFinBasis D j k).val) l) ≤ (p + 2) ^ 2
    intro j k l
    rw [productFinBasis, Basis.repr_reindex_apply, productLayerFinBasis, Basis.reindex_apply]
    apply le_trans _ (show p ≤ (p + 2) ^ 2 by linarith)
    exact productLayerBasis_logHeight D hp hD j _ _

end Erdos3.RationalFilteredNilmanifold

end

section

open Module
open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productProjection_matrix_height (i : ι)
    (j : Fin (Fintype.card (Σ i, Fin (d i)))) (k : Fin (d i)) :
    RationalHeightLE ((D i).basis.repr (liePiEval (R := ℚ) i ((pi D).basis j)) k) 1 := by
  classical
  change RationalHeightLE ((D i).basis.repr (productFinBasis D j i) k) 1
  rw [productFinBasis, Basis.reindex_apply]
  generalize he : (Fintype.equivFin (Σ i, Fin (d i))).symm j = z
  rcases z with ⟨a, l⟩
  rw [Pi.basis_apply]
  by_cases hai : a = i
  · subst a
    rw [Pi.single_eq_same, Basis.repr_self]
    by_cases hlk : l = k <;> simp [hlk, RationalHeightLE]
  · rw [Pi.single_eq_of_ne (Ne.symm hai), map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem productProjection_lipschitz (i : ι) :
    letI := (pi D).metricSpace
    letI := (D i).metricSpace
    LipschitzWith (coordinateLipschitzBound (d i) (Fintype.card (Σ i, Fin (d i))) 1)
      (productProjection D i) := by
  let := realificationQuotientMetricSpace (pi D).basis (pi D).lattice
    (pi D).grid (pi D).grid_pos (pi D).outer_grid
  let := realificationQuotientMetricSpace (D i).basis (D i).lattice
    (D i).grid (D i).grid_pos (D i).outer_grid
  have hh := NilpotentLieBCHGroup.lipschitz_realificationMap_quotient
    (pi D).basis (D i).basis (liePiEval i) (pi D).lattice (D i).lattice
    (productProjection_lattice D i) (pi D).grid (D i).grid (pi D).grid_pos (D i).grid_pos
    (pi D).outer_grid (D i).outer_grid 1 (fun k j => productProjection_matrix_height D i j k)
  exact hh.weaken (by simp only [Fintype.card_fin, Nat.cast_one, le_refl])

omit [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))] in
theorem productProjection_lipschitz_bound {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hD : ∀ i, (D i).GeometryComplexityLE p) (i : ι) :
    (coordinateLipschitzBound (d i) (Fintype.card (Σ i, Fin (d i))) 1 : ℝ) ≤
      Real.exp ((p ^ 2 + p + 3) ^ 2) := by
  have hdim := sigma_card_le_budget hp hι
    (κ := fun i => Fin (d i)) (fun i => by simpa only [Fintype.card_fin] using (hD i).1)
  have hi := (hD i).1
  have hq : 0 ≤ p ^ 2 + p + 1 := by positivity
  have hh := coordinateLipschitzBound_le_exp (d i) (Fintype.card (Σ i, Fin (d i))) 1 hq
    (by nlinarith [sq_nonneg p]) (by linarith)
    (by simpa only [NNReal.coe_one] using Real.one_le_exp_iff.mpr hq)
  convert hh using 2
  ring

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3

namespace RationalFilteredNilmanifold

open Module
open scoped TensorProduct

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def optionFactors : ∀ i : Option ι,
    RationalFilteredNilmanifold (optionLieSpace L₀ L i) s (optionDimension d₀ d i)
  | none => D₀
  | some i => D i

noncomputable def optionProduct := pi (optionFactors D₀ D)

end RationalFilteredNilmanifold
end Erdos3

end

section

open scoped TensorProduct BigOperators NNReal

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}

noncomputable def productObservable (T : ∀ i, (D i).Niltest w) (z : (pi D).Space) : ℂ :=
  ∏ i, (T i).observable (productProjection D i z)

theorem productObservable_bounds (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p) :
    letI := (pi D).metricSpace
    (∀ z, ‖productObservable D T z‖ ≤ Real.exp p ^ Fintype.card ι) ∧
    LipschitzWith ((Fintype.card ι : ℝ≥0) *
      productExpBound (productObservableLipBudget p) *
        productExpBound p ^ Fintype.card ι) (productObservable D T) := by
  let := (pi D).metricSpace
  have hB : (1 : ℝ≥0) ≤ productExpBound p := Real.one_le_exp_iff.mpr hp
  have hnorm (i : ι) (z : (pi D).Space) :
      ‖(T i).observable (productProjection D i z)‖ ≤ Real.exp p := by
    have hb := (T i).observable_budget (hT i)
    exact ((T i).norm_le _).trans (by linarith [(T i).lipBound.coe_nonneg])
  have hlip (i : ι) : LipschitzWith
      (productExpBound (productObservableLipBudget p))
        (fun z => (T i).observable (productProjection D i z)) := by
    let := (D i).metricSpace
    apply ((T i).lipschitz.comp (productProjection_lipschitz D i)).weaken
    change (T i).lipBound *
      (coordinateLipschitzBound (d i) (Fintype.card (Σ i, Fin (d i))) 1 : ℝ) ≤ _
    have hb := (T i).observable_budget (hT i)
    have hk : ((T i).lipBound : ℝ) ≤ Real.exp p := by linarith [(T i).normBound.coe_nonneg]
    calc
      _ ≤ Real.exp p * Real.exp ((p ^ 2 + p + 3) ^ 2) :=
        mul_le_mul hk (productProjection_lipschitz_bound D hp hι (fun i => (hT i).1) i)
          (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; rfl
  exact bounded_lipschitz_fintype_prod (fun i z => (T i).observable (productProjection D i z))
    hB hlip hnorm

noncomputable def piNiltest (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p) : (pi D).Niltest w where
  orbit := NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (fun i => (T i).orbit)
  observable := productObservable D T
  normBound := productExpBound p ^ Fintype.card ι
  lipBound := (Fintype.card ι : ℝ≥0) *
    productExpBound (productObservableLipBudget p) *
      productExpBound p ^ Fintype.card ι
  norm_le z := by simpa only [NNReal.coe_pow, coe_productExpBound] using (productObservable_bounds D T hp hι hT).1 z
  lipschitz := (productObservable_bounds D T hp hι hT).2

theorem piNiltest_eval (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p) (x : σ → ℤ) :
    (piNiltest D T hp hι hT).eval x = ∏ i, (T i).eval x := by
  change (∏ i, (T i).observable (productProjection D i
    (QuotientGroup.mk ((pi D).filtration.realification.polynomialOrbitEval w x
      (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (fun i => (T i).orbit)))))) = _
  apply Finset.prod_congr rfl
  intro i _
  rw [productProjection_mk]
  exact congrArg (fun g => (T i).observable (QuotientGroup.mk g))
    (NilpotentLieFiltration.piRealOrbit_eval (fun i => (D i).filtration) (fun i => (T i).orbit) x i)

theorem piNiltest_complexity (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p) :
    (piNiltest D T hp hι hT).ComplexityLE (productNiltestBudget p) := by
  constructor
  · exact GeometryComplexityLE.mono (pi D) (pi_geometry D hp hι (fun i => (hT i).1))
      (productNiltestBudget_geometry hp)
  · change Real.log (2 + (Real.exp p) ^ Fintype.card ι +
      (Fintype.card ι : ℝ) * Real.exp (productObservableLipBudget p) * (Real.exp p) ^ Fintype.card ι) ≤ _
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    exact productNiltestBudget_observable hp _ hι

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeEquivalenceTransitivity
namespace OAI

section

namespace Erdos3.NativeNilsequenceExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeNilsequenceExpansion.lie NativeNilsequenceExpansion.algebra
  NativeNilsequenceExpansion.topology NativeNilsequenceExpansion.topologicalAdd
  NativeNilsequenceExpansion.continuousSMul NativeNilsequenceExpansion.hausdorff

noncomputable def ofFamily {I : Type*} [Fintype I] {L : I → Type}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s N : ℕ} [NeZero N] {d : I → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (T : ∀ i, (D i).Niltest (fun _ : Unit => 1)) (c : I → ℂ)
    {p : ℝ} {f : ZMod N → ℂ} (hcard : (Fintype.card I : ℝ) ≤ Real.exp p)
    (hT : ∀ i, (T i).ComplexityLE p) (hc : (∑ i, ‖c i‖) ≤ Real.exp p)
    (hf : ∀ x, f x = ∑ i, c i * (T i).evalCyclic N (fun _ => x)) :
    NativeNilsequenceExpansion s N p f := by
  let e := (Fintype.equivFin I).symm
  exact {
    count := Fintype.card I
    count_bound := hcard
    L := fun i => L (e i)
    dim := fun i => d (e i)
    model := fun i => D (e i)
    test := fun i => T (e i)
    complexity := fun i => hT (e i)
    coefficient := fun i => c (e i)
    cost := (e.sum_comp (fun i => ‖c i‖)).le.trans hc
    eval := fun x => (hf x).trans (e.sum_comp
      (fun i => c i * (T i).evalCyclic N (fun _ => x))).symm
  }

noncomputable def weightedSum {I : Type*} [Fintype I] {s N : ℕ} [NeZero N]
    {p q : ℝ} {f : I → ZMod N → ℂ} (E : ∀ i, NativeNilsequenceExpansion s N p (f i))
    (c : I → ℂ) (hq : 0 ≤ q) (hcard : (Fintype.card I : ℝ) ≤ Real.exp q)
    (hc : (∑ i, ‖c i‖) ≤ Real.exp q) :
    NativeNilsequenceExpansion s N (p + q) (fun x => ∑ i, c i * f i x) := by
  classical
  let A := Σ i, Fin (E i).count
  refine ofFamily (I := A) (fun a => (E a.1).model a.2)
    (fun a => (E a.1).test a.2) (fun a => c a.1 * (E a.1).coefficient a.2) ?_
    (fun a => ((E a.1).complexity a.2).mono (by linarith)) ?_ ?_
  · change (Fintype.card (Σ i, Fin (E i).count) : ℝ) ≤ _
    rw [Fintype.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _ : I, Real.exp p := Finset.sum_le_sum (fun i _ => by
        simpa only [Fintype.card_fin] using (E i).count_bound)
      _ = (Fintype.card I : ℝ) * Real.exp p := by simp
      _ ≤ Real.exp q * Real.exp p := mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      _ = Real.exp (p + q) := by rw [← Real.exp_add, add_comm]
  · exact (sum_pair_coefficient_norms_le c (fun i => (E i).coefficient)
      (Real.exp_nonneg p) hc (fun i => (E i).cost)).trans_eq
      (by rw [← Real.exp_add, add_comm])
  · intro x
    change (∑ i, c i * f i x) = ∑ a : Sigma (fun i => Fin (E i).count), _
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    rw [(E i).eval x, Finset.mul_sum]
    simp only [mul_assoc]

end Erdos3.NativeNilsequenceExpansion

end

section

namespace Erdos3.NativeNilsequenceExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeNilsequenceExpansion.lie NativeNilsequenceExpansion.algebra
  NativeNilsequenceExpansion.topology NativeNilsequenceExpansion.topologicalAdd
  NativeNilsequenceExpansion.continuousSMul NativeNilsequenceExpansion.hausdorff

noncomputable def ofProduct {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
    {s d e N : ℕ} [NeZero N] {p : ℝ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (T : D.Niltest (fun _ : Unit => 1)) (U : E.Niltest (fun _ : Unit => 1))
    (hp : 2 ≤ p) (hT : T.ComplexityLE p) (hU : U.ComplexityLE p) :
    NativeNilsequenceExpansion s N (productNiltestBudget p)
      (fun x => T.evalCyclic N (fun _ => x) * U.evalCyclic N (fun _ => x)) := by
  have hp0 : 0 ≤ p := by linarith
  let K : Bool → Type := BoolLieFamily L M
  let dims : Bool → ℕ := fun b => Bool.rec e d b
  let models : ∀ b, RationalFilteredNilmanifold (K b) s (dims b) := fun b => by
    cases b
    · exact E
    · exact D
  let tests : ∀ b, (models b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact U
    · exact T
  have htests : ∀ b, (tests b).ComplexityLE p := by
    intro b
    cases b
    · exact hU
    · exact hT
  have hcard : (Fintype.card Bool : ℝ) ≤ p := by
    simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis models).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis models)
  let S := RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests
  have heval (x : ZMod N) : S.evalCyclic N (fun _ => x) =
      T.evalCyclic N (fun _ => x) * U.evalCyclic N (fun _ => x) := by
    change (RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests).eval
      (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.piNiltest_eval, Fintype.prod_bool]
    rfl
  have hB : 1 ≤ Real.exp (productNiltestBudget p) :=
    Real.one_le_exp_iff.mpr ((sq_nonneg (p + 2)).trans (productNiltestBudget_geometry hp0))
  refine ofFamily (I := Unit) (fun _ => RationalFilteredNilmanifold.pi models)
    (fun _ => S) (fun _ => 1) (by simpa using hB)
    (fun _ => RationalFilteredNilmanifold.piNiltest_complexity models tests hp0 hcard htests)
    (by simpa using hB) ?_
  intro x
  simpa only [one_mul, Fintype.sum_unique] using (heval x).symm

noncomputable def mul {s N : ℕ} [NeZero N] {p : ℝ} {f g : ZMod N → ℂ}
    (E : NativeNilsequenceExpansion s N p f) (F : NativeNilsequenceExpansion s N p g)
    (hp : 2 ≤ p) :
    NativeNilsequenceExpansion s N (productNiltestBudget p + 2 * p) (fun x => f x * g x) := by
  let c : Fin E.count × Fin F.count → ℂ := fun ij => E.coefficient ij.1 * F.coefficient ij.2
  let v : Fin E.count × Fin F.count → ZMod N → ℂ := fun ij x =>
    (E.test ij.1).evalCyclic N (fun _ => x) * (F.test ij.2).evalCyclic N (fun _ => x)
  let R : ∀ ij, NativeNilsequenceExpansion s N (productNiltestBudget p) (v ij) :=
    fun ij => ofProduct (E.model ij.1) (F.model ij.2) (E.test ij.1) (F.test ij.2)
      hp (E.complexity ij.1) (F.complexity ij.2)
  have hexp : Real.exp p * Real.exp p = Real.exp (2 * p) := by
    rw [← Real.exp_add, two_mul]
  have hcard : (Fintype.card (Fin E.count × Fin F.count) : ℝ) ≤ Real.exp (2 * p) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul E.count_bound F.count_bound (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans_eq hexp
  have hc : (∑ ij, ‖c ij‖) ≤ Real.exp (2 * p) := by
    calc
      _ = (∑ i, ‖E.coefficient i‖) * (∑ j, ‖F.coefficient j‖) := by
        simp only [c, norm_mul, Fintype.sum_prod_type, Finset.sum_mul_sum]
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul E.cost F.cost (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Real.exp_nonneg _)
      _ = _ := hexp
  have heq : (fun x => ∑ ij, c ij * v ij x) = (fun x => f x * g x) := by
    funext x
    rw [E.eval x, F.eval x]
    simp only [c, v, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  exact heq ▸ weightedSum R c (by linarith) hcard hc

end Erdos3.NativeNilsequenceExpansion

end

section

namespace Erdos3.NativeVectorEquivalence

open scoped BigOperators

theorem trans {J K M : Type*} [Fintype J] [Fintype K] [Fintype M]
    {s N : ℕ} [NeZero N] {p : ℝ}
    {chi : J → ZMod N → ℂ} {eta : K → ZMod N → ℂ} {psi : M → ZMod N → ℂ}
    (E : NativeVectorEquivalence s N p chi eta) (F : NativeVectorEquivalence s N p eta psi)
    (hunit : ∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) (hp : 2 ≤ p) :
    NativeVectorEquivalence s N (productNiltestBudget p + 2 * p + p) chi psi := by
  classical
  have hp0 : 0 ≤ p := by linarith
  have hB : 0 ≤ productNiltestBudget p :=
    (sq_nonneg (p + 2)).trans (productNiltestBudget_geometry hp0)
  have hpq : p ≤ productNiltestBudget p + 2 * p + p := by linarith
  refine {
    left_dimension := E.left_dimension.trans (Real.exp_le_exp.mpr hpq)
    right_dimension := F.right_dimension.trans (Real.exp_le_exp.mpr hpq)
    expansion := ?_
  }
  intro j l
  let A : ∀ k, NativeNilsequenceExpansion s N p (fun x => chi j x * star (eta k x)) :=
    fun k => Classical.choice (E.expansion j k)
  let B : ∀ k, NativeNilsequenceExpansion s N p (fun x => eta k x * star (psi l x)) :=
    fun k => Classical.choice (F.expansion k l)
  let R := fun k => (A k).mul (B k) hp
  have hc : (∑ _ : K, ‖(1 : ℂ)‖) ≤ Real.exp p := by
    simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      using E.right_dimension
  let S := NativeNilsequenceExpansion.weightedSum R (fun _ => 1) hp0 E.right_dimension hc
  have heq : (fun x => ∑ k, (1 : ℂ) *
      ((chi j x * star (eta k x)) * (eta k x * star (psi l x)))) =
      (fun x => chi j x * star (psi l x)) := by
    funext x
    calc
      _ = ∑ k, ((chi j x * star (psi l x)) * star (eta k x)) * eta k x := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := (complex_unit_vector_resolution (fun k => eta k x) (hunit x) _).symm
  exact ⟨heq ▸ S⟩

end Erdos3.NativeVectorEquivalence

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMeanRowCorrelation
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeMeanRowCorrelation {σ H X : Type*} [Fintype H] [Fintype X]
    (w : σ → ℕ) (degree : ℕ) (p : ℝ) (sample : H → X → σ → ℤ) (f : H → X → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest w
  complexity : test.ComplexityLE p
  correlation : Real.exp (-p) ≤ 𝔼 h, ‖𝔼 x, f h x * star (test.eval (sample h x))‖

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealifiedBCHProductEquiv
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}

theorem realBCHPiEquiv_mem_lattice (F : ∀ i, NilpotentLieFiltration (L i) s)
    (Γ : ∀ i, Subgroup (F i).Group) (g : (NilpotentLieFiltration.pi F).realification.Group) :
    g ∈ (piBCHSubgroup F Γ).map realificationHom ↔
      ∀ i, realBCHPiEquiv F g i ∈ (Γ i).map realificationHom := by
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    exact ⟨⟨x.coord i⟩, (mem_piBCHSubgroup F Γ x).mp hx i, rfl⟩
  · intro h
    choose x hx heq using h
    let y : (NilpotentLieFiltration.pi F).Group := ⟨fun i => (x i).coord⟩
    refine Subgroup.mem_map.mpr ⟨y, (mem_piBCHSubgroup F Γ y).mpr hx, ?_⟩
    apply (realBCHPiEquiv F).injective
    funext i
    exact heq i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OptionMarkedSurjective
namespace OAI

section

universe u v

namespace Erdos3

open scoped TensorProduct

variable {ι : Type v} {L₀ M₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing M₀] [LieAlgebra ℚ M₀]
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}

def optionMarkedComponents (φ : L₀ →ₗ⁅ℚ⁆ M₀) :
    ∀ i : Option ι, (∀ j : Option ι, optionLieSpace L₀ L j) →ₗ⁅ℚ⁆
      optionLieSpace M₀ L i
  | none => φ.comp (liePiEval none)
  | some i => liePiEval (some i)

def optionMarkedLieMap (φ : L₀ →ₗ⁅ℚ⁆ M₀) :
    (∀ i : Option ι, optionLieSpace L₀ L i) →ₗ⁅ℚ⁆
      (∀ i : Option ι, optionLieSpace M₀ L i) :=
  liePiMap (optionMarkedComponents (L := L) φ)

@[simp] theorem optionMarkedLieMap_none (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i) :
    optionMarkedLieMap φ x none = φ (x none) := rfl

@[simp] theorem optionMarkedLieMap_some (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i) (i : ι) :
    optionMarkedLieMap φ x (some i) = x (some i) := rfl

open NilpotentLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L Y W J : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing Y] [LieAlgebra ℚ Y] [LieRing W] [LieAlgebra ℚ W] {s : ℕ}
  (F : NilpotentLieFiltration L s) (π : L →ₗ⁅ℚ⁆ Y)
  (eta : J → L →ₗ[ℚ] ℚ) (js : List J)

def pivotAnnihilatorIdeal : LieIdeal ℚ L :=
  F.topSubspaceIdeal (finiteFrequencyKernel (F.layer s ⊓ LinearMap.ker π.toLinearMap) eta js)
    ((finiteFrequencyKernel_le _ _ _).trans inf_le_left)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateQuotientModel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) [DecidablePred (· ∈ S)]
  (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

noncomputable def coordinateQuotientModel (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    RationalFilteredNilmanifold (L ⧸ I) t (Fintype.card {i // i ∉ S}) :=
  (F.quotientLie I hI).ofAdaptedBasis (quotientFinBasis b I S hspan)
    (quotientFinWeight w S) (F.quotientFinBasis_layers b w hlayers I hI S hspan)
    (Γ.map (F.quotientStepHom I hI)) N hN
    (bchSubgroup_inner_grid_reindex _ (Fintype.equivFin _) _
      (F.quotientStep_inner_grid_supported b I hI S hspan Γ hin))
    (bchSubgroup_outer_grid_reindex _ (Fintype.equivFin _) _
      (F.quotientStep_outer_grid_supported b I hI S hspan Γ hout))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuantitativeNoninjectivity
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

theorem noninjectivity_le {Ω J Y : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    [DecidableEq Y] (p : FiniteProbabilityWeights Ω) (F : Ω → J → Y)
    {C : ℝ} (hC : 0 ≤ C)
    (hp : ∀ j k, j ≠ k → p.mean (fun x => if F x j = F x k then 1 else 0) ≤ C) :
    p.mean (fun x => noninjectivityIndicator (F x)) ≤ (Fintype.card J : ℝ)^2*C := by
  have hm := p.mean_mono (fun x => noninjectivityIndicator_le_pairs (F x))
  simp_rw [mean_fintype_sum] at hm
  refine hm.trans ?_
  calc
    _ ≤ ∑ _j : J, ∑ _k : J, C := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      by_cases he : j = k
      · simpa only [if_pos he, mean_const] using hC
      · simpa only [if_neg he] using hp j k he
    _ = _ := by simp [pow_two, mul_assoc]

theorem reweightPositive_noninjectivity_le {Ω J Y : Type*} [Fintype Ω] [Fintype J]
    [DecidableEq J] [DecidableEq Y] (p : FiniteProbabilityWeights Ω) (F : Ω → J → Y)
    (D : Ω → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD : 0 < p.mean D)
    {M C : ℝ} (hM : 0 ≤ M) (hcap : ∀ x, D x ≤ M) (hlower : 1/2 ≤ p.mean D)
    (hC : 0 ≤ C)
    (hp : ∀ j k, j ≠ k → p.mean (fun x => if F x j = F x k then 1 else 0) ≤ C) :
    (p.reweightPositive D hD0 hD).mean (fun x => noninjectivityIndicator (F x)) ≤
      2*M*((Fintype.card J : ℝ)^2*C) := by
  have hb : p.mean (fun x => D x * noninjectivityIndicator (F x)) ≤
      M * p.mean (fun x => noninjectivityIndicator (F x)) := by
    rw [← mean_const_mul]
    exact p.mean_mono (fun x => mul_le_mul_of_nonneg_right (hcap x) (noninjectivityIndicator_nonneg _))
  have ht := p.reweightPositive_test_le D hD0 hD (fun x => noninjectivityIndicator (F x))
    (fun x => noninjectivityIndicator_nonneg _) (a := 1/2) (ε := 0) (by norm_num) hlower
    (by simpa only [add_zero] using hb)
  have hpair := p.noninjectivity_le F hC hp
  have hmul := mul_le_mul_of_nonneg_left hpair (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
  exact (ht.trans_eq (by ring)).trans hmul

end FiniteProbabilityWeights
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionOriginalOrbit
namespace OAI

section

universe u v

namespace Erdos3

open scoped TensorProduct

variable {ι : Type v} {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]

instance optionRealificationTopology
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] (i : Option ι) :
    TopologicalSpace (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
  cases i with
  | none => exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L₀))
  | some i => exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L i))

instance optionRealificationTopologicalAddGroup
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    (i : Option ι) : IsTopologicalAddGroup (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
  cases i with
  | none => exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀))
  | some i => exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L i))

instance optionRealificationContinuousSMul
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)]
    (i : Option ι) : ContinuousSMul ℝ (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
  cases i with
  | none => exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀))
  | some i => exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L i))

instance optionRealificationT2Space
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
    [T2Space (ℝ ⊗[ℚ] L₀)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (i : Option ι) : T2Space (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
  cases i with
  | none => exact (inferInstance : T2Space (ℝ ⊗[ℚ] L₀))
  | some i => exact (inferInstance : T2Space (ℝ ⊗[ℚ] L i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealProductInclusion
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productProjection_joint_injective :
    Function.Injective (fun x : (pi D).Space => fun i => productProjection D i x) := by
  intro x y h
  induction x, y using Quotient.inductionOn₂ with
  | h x y =>
    apply QuotientGroup.eq.mpr
    change x⁻¹ * y ∈ (piBCHSubgroup (fun i => (D i).filtration) (fun i => (D i).lattice)).map realificationHom
    rw [realBCHPiEquiv_mem_lattice]
    intro i
    have hi := congrFun h i
    have hmem := QuotientGroup.eq.mp hi
    change productProjectionHom D i (x⁻¹ * y) ∈ (D i).realLattice
    simpa only [map_mul, map_inv] using hmem

theorem productProjection_joint_surjective :
    Function.Surjective (fun x : (pi D).Space => fun i => productProjection D i x) := by
  intro y
  let F := fun i => (D i).filtration
  let g := (realBCHPiEquiv F).symm (fun i => (y i).out)
  refine ⟨QuotientGroup.mk g, ?_⟩
  funext i
  change QuotientGroup.mk (realBCHPiEquiv F g i) = y i
  rw [show realBCHPiEquiv F g = (fun i => (y i).out) from (realBCHPiEquiv F).apply_symm_apply _]
  exact Quotient.out_eq (y i)

noncomputable def productSpaceEquiv : (pi D).Space ≃ (∀ i, (D i).Space) :=
  Equiv.ofBijective (fun x i => productProjection D i x)
    ⟨productProjection_joint_injective D, productProjection_joint_surjective D⟩

@[simp] theorem productSpaceEquiv_apply (x : (pi D).Space) (i : ι) :
    productSpaceEquiv D x i = productProjection D i x := rfl

@[simp] theorem productSpaceEquiv_mk (g : (pi D).RealGroup) (i : ι) :
    productSpaceEquiv D (QuotientGroup.mk g) i = QuotientGroup.mk (productProjectionHom D i g) := rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestComplement
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

namespace RationalFilteredNilmanifold

open Module
open scoped NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)

noncomputable def raiseStepProjection : (D.raiseStep hst).Space → D.Space :=
  cosetMap (D.raiseStep hst).realLattice D.realLattice
    (NilpotentLieBCHGroup.realificationMap
      (hnil := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L))
    (NilpotentLieBCHGroup.realificationMap_subgroup (LieHom.id : L →ₗ⁅ℚ⁆ L)
      (D.raiseStep hst).lattice D.lattice (D.raiseStep_lattice_back hst))

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem raiseStepProjection_lipschitz :
    let := (D.raiseStep hst).metricSpace
    let := D.metricSpace
    LipschitzWith (coordinateLipschitzBound d d 1) (D.raiseStepProjection hst) := by
  let := realificationQuotientMetricSpace (D.raiseStep hst).basis (D.raiseStep hst).lattice
    (D.raiseStep hst).grid (D.raiseStep hst).grid_pos (D.raiseStep hst).outer_grid
  let := realificationQuotientMetricSpace D.basis D.lattice D.grid D.grid_pos D.outer_grid
  have hentry (k i : Fin d) :
      RationalHeightLE (D.basis.repr ((LieHom.id : L →ₗ⁅ℚ⁆ L) ((D.raiseStep hst).basis i)) k) 1 := by
    change RationalHeightLE (D.basis.repr (D.basis i) k) 1
    rw [Basis.repr_self]
    by_cases h : i = k <;> simp [h, RationalHeightLE]
  have h := NilpotentLieBCHGroup.lipschitz_realificationMap_quotient
    (D.raiseStep hst).basis D.basis (LieHom.id : L →ₗ⁅ℚ⁆ L)
    (D.raiseStep hst).lattice D.lattice (D.raiseStep_lattice_back hst)
    (D.raiseStep hst).grid D.grid (D.raiseStep hst).grid_pos D.grid_pos
    (D.raiseStep hst).outer_grid D.outer_grid 1 hentry
  exact h.weaken (by simp only [Fintype.card_fin, Nat.cast_one, le_refl])

end Metric

noncomputable def raiseStepRealOrbit {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) :
    (D.raiseStep hst).filtration.realification.PolynomialOrbit w :=
  NilpotentLieFiltration.polynomialOrbitOfLog g.log g.adapted

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

namespace RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def raiseStep (T : D.Niltest w) (hst : s ≤ t) : (D.raiseStep hst).Niltest w where
  orbit := D.raiseStepRealOrbit hst T.orbit
  observable := fun z => T.observable (D.raiseStepProjection hst z)
  normBound := T.normBound
  lipBound := T.lipBound * coordinateLipschitzBound d d 1
  norm_le z := T.norm_le _
  lipschitz := by
    let := (D.raiseStep hst).metricSpace
    let := D.metricSpace
    exact T.lipschitz.comp (D.raiseStepProjection_lipschitz hst)

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedTopQuotient
namespace OAI

section

namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M]

noncomputable def lieQuotientProjection (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J) :
    (L ⧸ I) →ₗ⁅ℚ⁆ (M ⧸ J) :=
  lieQuotientDescend I ((lieQuotientMap J).comp φ)
    (fun x hx => (lieQuotientMap_eq_zero J (φ x)).mpr (hφ x hx))

@[simp] theorem lieQuotientProjection_mk (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J) (x : L) :
    lieQuotientProjection I J φ hφ (lieQuotientMap I x) = lieQuotientMap J (φ x) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RaisedDegreeRank
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}

structure DegreeRankStructure (D : RationalFilteredNilmanifold L s d) (r : ℕ) where
  filtration : DegreeRankLieFiltration L s r
  associated : filtration.associatedDegree = D.filtration
  basis : ∀ i j : Fin (s + 1),
    Basis (Fin (finrank ℚ (filtration.layer i.val j.val))) ℚ (filtration.layer i.val j.val)

namespace DegreeRankStructure

variable {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)

def ComplexityLE (p : ℝ) : Prop :=
  D.GeometryComplexityLE p ∧ ∀ i j a k, rationalLogHeight (D.basis.repr (R.basis i j a : L) k) ≤ p

noncomputable def realSubgroup (i j : ℕ) : Subgroup D.RealGroup := R.filtration.realification.subgroup i j

end DegreeRankStructure

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ReducedSquareFastKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

noncomputable def reducedSquareFastDiagonalSubalgebra : LieSubalgebra ℚ (F.quotientTop.PolynomialSymbol w) :=
  W.map (F.reducedSquareSndSymbolMap w)

noncomputable def reducedSquareFastRelativeSubmodule : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w) :=
  W.toSubmodule ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

noncomputable def realLinearCoordinateLift (σ : M →ₗ[ℚ] L)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM)) :
    NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL) :=
  ⟨σ.baseChange ℝ g.coord⟩

@[simp] theorem realLinearCoordinateLift_coord (σ : M →ₗ[ℚ] L)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM)) :
    (realLinearCoordinateLift (hL := hL) (hM := hM) σ g).coord = σ.baseChange ℝ g.coord := rfl

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def reducedSquareRealSymbolHom :
    F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w →*
      F.quotientTop.RealPolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := F.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w) (F.reducedSquareSndSymbolMap w)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareRealSymbolKernel_eq :
    (F.reducedSquareSndSymbolMap w).ker.toSubmodule.baseChange ℝ =
      LinearMap.ker ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ) :=
  realification_ker (F.reducedSquareSndSymbolMap w).toLinearMap

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def reducedSquareRealDiagonalHom :
    F.quotientTop.RealPolynomialSymbolGroup w →*
      F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w :=
  realificationMap
    (hnil := F.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (F.reducedSquareDiagonalSymbolMap w)

@[simp] theorem reducedSquareRealSymbolHom_diagonal (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    F.reducedSquareRealSymbolHom w (F.reducedSquareRealDiagonalHom w g) = g := by
  have h : (F.reducedSquareSndSymbolMap w).toLinearMap.comp
      (F.reducedSquareDiagonalSymbolMap w).toLinearMap = LinearMap.id := by
    ext x
    exact F.reducedSquareSndSymbolMap_diagonal w x
  have hr := congrArg (fun f : F.quotientTop.PolynomialSymbol w →ₗ[ℚ]
    F.quotientTop.PolynomialSymbol w => f.baseChange ℝ) h
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at hr
  apply NilpotentLieBCHGroup.ext
  exact DFunLike.congr_fun hr g.coord

noncomputable def reducedSquareRealRelativePart
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w :=
  splitRelativePart (F.reducedSquareRealSymbolHom w) (F.reducedSquareRealDiagonalHom w) g

@[simp] theorem reducedSquareRealRelativePart_projection
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.reducedSquareRealSymbolHom w (F.reducedSquareRealRelativePart w g) = 1 :=
  splitRelativePart_projection _ _ (F.reducedSquareRealSymbolHom_diagonal w) g

theorem reducedSquareRealRelativePart_coord_kernel
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
      (F.reducedSquareRealRelativePart w g).coord = 0 :=
  congrArg NilpotentLieBCHGroup.coord (F.reducedSquareRealRelativePart_projection w g)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

noncomputable def realReducedRelativeSquareSymbolMap :
    (ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) →ₗ[ℝ]
      (ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w) :=
  (F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ

theorem realReducedRelativeSquareSymbolMap_range :
    LinearMap.range (F.realReducedRelativeSquareSymbolMap w hw) =
      LinearMap.ker ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ) := by
  have h := realification_map (⊤ : Submodule ℚ (F.normalizedRelativeSubmodule w))
    (F.reducedRelativeSquareSymbolMap w hw)
  simp only [Submodule.map_top, Submodule.baseChange_top] at h
  change LinearMap.range ((F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ) = _
  rw [← h, F.reducedRelativeSquareSymbolMap_range, F.reducedSquareRealSymbolKernel_eq]

@[simp] theorem realReducedRelativeSquareSymbolMap_projection
    (p : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
      (F.realReducedRelativeSquareSymbolMap w hw p) = 0 := by
  have h : F.realReducedRelativeSquareSymbolMap w hw p ∈
      LinearMap.range (F.realReducedRelativeSquareSymbolMap w hw) := ⟨p, rfl⟩
  rw [F.realReducedRelativeSquareSymbolMap_range] at h
  exact h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem realNormalizedFirstCoefficientMap_ker :
    LinearMap.ker (F.realNormalizedFirstCoefficientMap w) =
      LinearMap.ker (F.realReducedRelativeSquareSymbolMap w hw) := by
  have hk : LinearMap.ker ((F.normalizedFirstCoefficientMap w).baseChange ℝ) =
      LinearMap.ker ((F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ) := by
    rw [← realification_ker, ← realification_ker, F.normalizedFirstCoefficientMap_ker w hw]
  ext x
  change F.firstCoefficientRealEquiv w ((F.normalizedFirstCoefficientMap w).baseChange ℝ x) = 0 ↔
    (F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ x = 0
  rw [LinearEquiv.map_eq_zero_iff]
  exact SetLike.ext_iff.mp hk x

noncomputable def realFirstCoefficientRelativeEquiv :
    LinearMap.ker (F.realFirstCoefficientHorizontal w) ≃ₗ[ℝ]
      LinearMap.ker ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ) :=
  commonKernelSubmoduleEquiv (F.realNormalizedFirstCoefficientMap w)
    (F.realReducedRelativeSquareSymbolMap w hw)
    (LinearMap.ker (F.realFirstCoefficientHorizontal w))
    (LinearMap.ker ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ))
    (F.realNormalizedFirstCoefficientMap_ker w hw)
    (F.realNormalizedFirstCoefficientMap_range w)
    (F.realReducedRelativeSquareSymbolMap_range w hw)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def adaptedReducedSymbolMap :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.quotientTop.PolynomialSymbol w :=
  (F.quotientTopSymbolMap w).comp (F.polynomialSymbolMap w)

noncomputable def adaptedReducedRealSymbolHom :
    F.RealAdaptedPolynomialGroup w →* F.quotientTop.RealPolynomialSymbolGroup w :=
  realificationMap
    (hnil := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := F.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (F.adaptedReducedSymbolMap w)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

local notation "bq" => F.quotientTopBasis b ω hF
local notation "ωq" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "hq" => F.quotientTopBasis_layers b ω hF
local notation "Bq" => F.quotientTop.polynomialSymbolBasis bq ωq hq w
local notation "Ba" => F.adaptedMonomialBasis b ω hF w

noncomputable def reducedNativeSection : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.adaptedLieSubalgebra w :=
  (Bq).constr ℚ (fun z => Ba (reducedNativeIndex s w ω z))

@[simp] theorem reducedNativeSection_basis (z : SymbolBasisIndex w ωq) :
    F.reducedNativeSection b ω hF w (Bq z) = Ba (reducedNativeIndex s w ω z) :=
  Basis.constr_basis _ _ _ z

theorem adaptedReducedSymbolMap_native_basis (z : SymbolBasisIndex w ωq) :
    F.adaptedReducedSymbolMap w (Ba (reducedNativeIndex s w ω z)) = Bq z := by
  classical
  change F.quotientTop.polynomialSymbolMap w
    (F.quotientTopPolynomialMap w (Ba (reducedNativeIndex s w ω z))) = Bq z
  rw [F.quotientTop.polynomialSymbolBasis_apply]
  congr 1
  apply Subtype.ext
  apply coefficients.injective
  ext α
  change coefficients (VectorPolynomial.map (lieQuotientMap (F.layerIdeal (s + 1))).toLinearMap
    (Ba (reducedNativeIndex s w ω z)).val) α = _
  rw [coefficients_map, F.adaptedMonomialBasis_coe,
    F.quotientTop.adaptedMonomialBasis_coe, coefficients_monomial, coefficients_monomial]
  by_cases h : α = z.val.1
  · subst α
    simp only [reducedNativeIndex, Finsupp.single_eq_same, F.quotientTopBasis_apply]
    rfl
  · simp only [reducedNativeIndex, Finsupp.single_eq_of_ne h, map_zero]

theorem reducedNativeSection_rightInverse (x : F.quotientTop.PolynomialSymbol w) :
    F.adaptedReducedSymbolMap w (F.reducedNativeSection b ω hF w x) = x := by
  have he : (F.adaptedReducedSymbolMap w).toLinearMap.comp (F.reducedNativeSection b ω hF w) =
      LinearMap.id := by
    apply (Bq).ext
    intro z
    exact (congrArg (F.adaptedReducedSymbolMap w) (F.reducedNativeSection_basis b ω hF w z)).trans
      (F.adaptedReducedSymbolMap_native_basis b ω hF w z)
  exact DFunLike.congr_fun he x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

noncomputable def realReducedRelativeCoefficient
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.RealFirstCoefficientModule w :=
  ((F.realFirstCoefficientRelativeEquiv w hw).symm
    ⟨(F.reducedSquareRealRelativePart w g).coord, F.reducedSquareRealRelativePart_coord_kernel w g⟩).val

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realReducedNativeLift (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    F.RealAdaptedPolynomialGroup w :=
  ⟨(F.reducedNativeSection b ω hF w).baseChange ℝ g.coord⟩

@[simp] theorem adaptedReducedRealSymbolHom_lift (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    F.adaptedReducedRealSymbolHom w (F.realReducedNativeLift b ω hF w g) = g := by
  apply NilpotentLieBCHGroup.ext
  change (F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ
    ((F.reducedNativeSection b ω hF w).baseChange ℝ g.coord) = g.coord
  have he : ∀ x : F.quotientTop.RealPolynomialSymbol w,
      (F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ
        ((F.reducedNativeSection b ω hF w).baseChange ℝ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
      exact congrArg (fun y => a ⊗ₜ[ℚ] y) (F.reducedNativeSection_rightInverse b ω hF w x)
  exact he g.coord

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedRelativeCoefficientBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

noncomputable def realFastDiagonalSubgroup : Subgroup (F.RealAdaptedPolynomialGroup w) :=
  (show Subgroup (F.quotientTop.RealPolynomialSymbolGroup w) from
    realLieSubgroup (realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))).comap
      (F.adaptedReducedRealSymbolHom w)

@[simp] theorem mem_realFastDiagonalSubgroup (g : F.RealAdaptedPolynomialGroup w) :
    g ∈ F.realFastDiagonalSubgroup w U ↔ (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U) := Iff.rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FirstCoefficientPolynomialDerivative
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def adaptedShiftedGradedPolynomial (k : ℕ) :
    F.adaptedLieSubalgebra w →ₗ[ℚ] VectorPolynomial σ ℚ F.AssociatedGraded :=
  (F.shiftedGradedPolynomial b ω hF w k).comp (F.adaptedLieSubalgebra w).incl.toLinearMap

@[simp] theorem adaptedShiftedGradedPolynomial_apply (k : ℕ) (p : F.adaptedLieSubalgebra w) :
    F.adaptedShiftedGradedPolynomial b ω hF w k p =
      F.shiftedGradedPolynomial b ω hF w k p.val := rfl

noncomputable def firstCoefficientGradedPolynomial :
    F.FirstCoefficientModule w →ₗ[ℚ] VectorPolynomial σ ℚ F.AssociatedGraded :=
  ((F.shiftedPolynomialIdeal w 2).toSubmodule.comap
    (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype).liftQ
      ((F.adaptedShiftedGradedPolynomial b ω hF w 1).comp
        (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype) (by
          intro p hp
          rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
            F.adaptedShiftedGradedPolynomial_apply]
          have hp' : p.val.val ∈ F.shiftedAdaptedSubmodule w 1 := p.property
          have hp'' : p.val.val ∈ F.shiftedAdaptedSubmodule w 2 := hp
          exact (F.shiftedGradedPolynomial_eq_zero_iff b ω hF w 1 hp').mpr hp'')

@[simp] theorem firstCoefficientGradedPolynomial_map (p : F.shiftedPolynomialIdeal w 1) :
    F.firstCoefficientGradedPolynomial b ω hF w (F.firstCoefficientMap w p) =
      F.adaptedShiftedGradedPolynomial b ω hF w 1 p.val := by
  unfold firstCoefficientGradedPolynomial firstCoefficientMap
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativePolynomialOrbit
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def nativePolynomialOrbit (g : F.RealAdaptedPolynomialGroup w) :
    F.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog (F.realAdaptedPolynomialMap w g.coord)
    (F.realAdaptedPolynomialMap_adapted w g.coord)

@[simp] theorem nativePolynomialOrbit_log (g : F.RealAdaptedPolynomialGroup w) :
    (F.nativePolynomialOrbit w g).log = F.realAdaptedPolynomialMap w g.coord := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealSquarePolynomialFactors
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def realSquareFstPolynomialHom :
    F.squareFiltration.RealAdaptedPolynomialGroup w →* F.RealAdaptedPolynomialGroup w :=
  realificationMap (hnil := (F.squareFiltration.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot) (F.squareFstPolynomialMap w)

noncomputable def realSquareSndPolynomialHom :
    F.squareFiltration.RealAdaptedPolynomialGroup w →* F.RealAdaptedPolynomialGroup w :=
  realificationMap (hnil := (F.squareFiltration.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot) (F.squareSndPolynomialMap w)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankQuotientOrbit
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}

noncomputable def basisOfTail (b : Basis (Fin d) ℚ L) (P : Submodule ℚ L) (c : ℕ)
    (hP : P = basisTail b c) : Basis (Fin (finrank ℚ P)) ℚ P := by
  classical
  let a := supportedSubmoduleBasis b P {j | c ≤ j.val} (hP.trans (basisTail_eq_span b c))
  exact a.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis a).symm)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialLiftArrays
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace VectorPolynomial

noncomputable def assembleFamily {σ κ R V : Type*} [Fintype κ] [CommRing R]
    [AddCommGroup V] [Module R V] (P : κ → VectorPolynomial σ R V) :
    VectorPolynomial σ R (κ → V) := by
  classical
  exact ∑ k, map (LinearMap.single R (fun _ : κ => V) k) (P k)

@[simp] theorem coefficients_assembleFamily {σ κ R V : Type*} [Fintype κ] [CommRing R]
    [AddCommGroup V] [Module R V] (P : κ → VectorPolynomial σ R V) (α : σ →₀ ℕ) (k : κ) :
    coefficients (assembleFamily P) α k = coefficients (P k) α := by
  classical
  simp [assembleFamily, LinearMap.single_apply, Pi.single_apply]

end VectorPolynomial

open VectorPolynomial

variable {σ κ ι L : Type*} [Fintype κ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {V : Submodule ℚ L}

noncomputable def liftQuotientArray (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) : VectorPolynomial σ ℚ (κ × ι → ℝ) :=
  assembleFamily (fun bi : κ × ι => map
    (((LinearMap.proj bi.2).comp (realQuotientCoordinateMap f)).restrictScalars ℚ) (S bi.1))

@[simp] theorem coefficients_liftQuotientArray (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (α : σ →₀ ℕ) (bi : κ × ι) :
    coefficients (liftQuotientArray f S) α bi = realQuotientCoordinateMap f (coefficients (S bi.1) α) bi.2 := by
  rw [liftQuotientArray, coefficients_assembleFamily, coefficients_map]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardFixedCenterThreshold
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def candidateNestedForwardSeed
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outer : ℕ) (x : ℝ) : ℝ :=
  (candidateNestedForwardSeedPolynomial A constants innerDepth outer).eval₂ (Nat.castRingHom ℝ) x

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RestrictedSymbolAlgebraicMajorStep
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

theorem BasisGradedSubmodule.coordinate_dilation_mem
    {R B : Type*} [Field R] [Fintype B]
    (w : B → ℕ) (K : Submodule R (B → R))
    (hK : BasisGradedSubmodule (Pi.basisFun R B) w K)
    (r : R) (x : B → R) (hx : x ∈ K) :
    (fun i => r ^ w i * x i) ∈ K := by
  classical
  have hprojection (j : ℕ) (i : B) :
      basisGradeProjection (Pi.basisFun R B) w j x i =
        if w i = j then x i else 0 := by
    simpa only [Pi.basisFun_repr] using
      basisGradeProjection_repr (Pi.basisFun R B) w j x i
  have hdilation : (fun i => r ^ w i * x i) =
      ∑ j ∈ Finset.univ.image w, r ^ j • basisGradeProjection (Pi.basisFun R B) w j x := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hprojection,
      mul_ite, mul_zero]
    simp
  rw [hdilation]
  exact K.sum_mem (fun j _ => K.smul_mem (r ^ j) (hK j x hx))

end Erdos3

end

end OAI
end


