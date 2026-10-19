-- Prove2me | Definitions.Def_OAIE3v2B168
-- name    : OAIE3v2B168
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:39:50.299201+00:00
-- url     : https://prove2.me/theorems/6847668d-6555-4201-b8bb-3f3c4829640f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 170 of 311
-- statement:
--   Definitions bundle 170 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B152`, `OAIE3v2B153`, `OAIE3v2B154`, `OAIE3v2B155` of this split.
--
--   Modules: `Dynamics/FastCoefficientDimensionBudget.lean`, `Estimates/ControlledRealFastCoefficientAction.lean`, `Estimates/DerivativeHorizontalLifts.lean`, `Estimates/FirstCoefficientDimension.lean`, `Estimates/FormalInductionTerminal.lean`, `Estimates/FormalLinearLiftReabsorption.lean`, `Estimates/NativeBinaryAssignments.lean`, `Estimates/RealFirstCoefficientHorizontal.lean`, `Estimates/ReducedNativeFactorization.lean`, `Estimates/ReducedRelativeCoefficientBounds.lean`, `Estimates/ReindexedFastCoefficientSection.lean`, `Estimates/StepDropTerminalContainment.lean`, `Geometry/ControlledLayerOneCoordinates.lean`, `Geometry/FastCoefficientDerivativeCoordinates.lean`, `Geometry/RealFastCoefficientCoordinates.lean`, `Geometry/ReducedSquareCoefficientCoordinates.lean`, `Geometry/WeightedCoordinateExtraction.lean`, `Lattices/UniformDerivativeLatticeExtraction.lean`, `Linear/FastCoefficientSpanning.lean`, `Nilpotent/ControlledBracketToCurrentLayer.lean`, `Polynomial/PolynomialKernelDirectionBudget.lean`, `Polynomial/QuantitativeOuterPolynomialProducts.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B152
import Definitions.Def_OAIE3v2B153
import Definitions.Def_OAIE3v2B154
import Definitions.Def_OAIE3v2B155

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealFirstCoefficientHorizontal
namespace OAI

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realAdaptedLogDerivative_eq_formal (i : σ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedPolynomialMap (fun _ => 1) (F.realAdaptedLogDerivative (Pi.single i 1) x) =
      formalLogDerivative (hnil := F.realification.lowerCentralSeries_eq_bot) i
        ⟨F.realAdaptedPolynomialMap (fun _ => 1) x⟩ := by
  have h := congrArg
    (fun P : F.realification.adaptedLieSubalgebra (fun _ : σ => 1) => P.val)
    (F.realAdaptedLogDerivative_tensor (Pi.single i 1) x)
  exact h.trans (F.realification.adaptedLogDerivative_eq_formal i
    (F.realAdaptedPolynomialTensor (fun _ => 1) x))

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FirstCoefficientDimension
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ)

variable [Fintype σ] [Fintype ι] (s : ℕ) (hw : ∀ i, 0 < w i) (hω : ∀ i, ω i ≤ s)

include hw hω in
theorem firstCoefficientIndex_card_le [Fintype (FirstCoefficientIndex w ω)] :
    Fintype.card (FirstCoefficientIndex w ω) ≤ Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s := by
  let := adaptedBasisIndexFintype w ω s hw hω
  exact (Fintype.card_le_of_injective _ (firstCoefficientIndexEmbedding w ω).injective).trans
    (adaptedBasisIndex_card_le w ω s hw hω)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FastCoefficientDimensionBudget
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem fastCoefficient_matrix_dimensions
    {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)]
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p) :
    (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ fastCoefficientMatrixParameter s p ∧
    (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ fastCoefficientMatrixParameter s p ∧
    (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ fastCoefficientMatrixParameter s p ∧
    ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤
      fastCoefficientMatrixParameter s p := by
  have hr := (F.reduced_lift_matrix_dimensions e ω hF w hw hp hι hσ hκ).2.1
  rw [Fintype.card_sum, Nat.cast_add] at hr
  have hr0 := reducedMatrixParameter_nonneg s hp
  have hd0 : 0 ≤ (p + (s + 3)) ^ (s + 3) := by positivity
  have hfac0 : 0 ≤ (p + (s + 3)) ^ (s + 3) * (p + 1) := by positivity
  have hrq : reducedMatrixParameter s p ≤ fastCoefficientMatrixParameter s p := by
    unfold fastCoefficientMatrixParameter
    linarith
  have hdf : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ (p + (s + 3)) ^ (s + 3) := by
    have h := (Nat.cast_le (α := ℝ).mpr
      (firstCoefficientIndex_card_le w ω (s + 1) hw (F.adaptedBasis_weight_le_step e ω hF))).trans
      (symbol_dimension_bound_le_power (s + 1) (Fintype.card ι) (Fintype.card σ) hp hι hσ)
    simpa [Nat.cast_add, Nat.add_assoc, add_assoc, show (1 : ℝ) + 2 = 3 by norm_num] using h
  have hdq : (p + (s + 3)) ^ (s + 3) * (p + 1) ≤ fastCoefficientMatrixParameter s p := by
    unfold fastCoefficientMatrixParameter
    linarith
  refine ⟨((le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hr).trans hrq,
    ((le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hr).trans hrq, ?_, ?_⟩
  · exact hdf.trans ((by nlinarith : (p + (s + 3)) ^ (s + 3) ≤
      (p + (s + 3)) ^ (s + 3) * (p + 1)).trans hdq)
  · rw [Nat.cast_mul]
    exact (mul_le_mul hdf (hκ.trans (by linarith)) (Nat.cast_nonneg _) hd0).trans hdq

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

noncomputable def realFastCoefficientHorizontalSection :
    (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) →ₗ[ℝ]
      (F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) :=
  (F.realFirstCoefficientFastSubmodule w hw U).mkQ.comp (F.realFirstCoefficientHorizontalSection w)

theorem realFastCoefficientHorizontal_section (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    F.realFastCoefficientHorizontal w hw U (F.realFastCoefficientHorizontalSection w hw U x) = x :=
  F.realFirstCoefficientHorizontal_section w x

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realAdaptedCoefficientGrid_iff_formal (w : σ → ℕ) (l : ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.RealAdaptedCoefficientGrid b ω hF w l x ↔
      CoefficientGrid (b.baseChange ℝ) l (F.realAdaptedPolynomialMap w x) := by
  rw [F.realAdaptedCoefficientGrid_polynomial_iff b ω hF w l ⟨x⟩]
  constructor
  · rintro ⟨a, ha⟩ α
    exact ⟨fun i => a (α, i), funext (fun i => congrFun ha (α, i))⟩
  · intro h
    choose a ha using h
    exact ⟨fun z => a z.1 z.2, funext (fun z => congrFun (ha z.1) z.2)⟩

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealFastCoefficientCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem firstCoefficientHorizontal_projector_repr
    (x : F.FirstCoefficientModule w) (z : FirstCoefficientIndex w ω) :
    (F.firstCoefficientBasis b ω hF w).repr
        (F.firstCoefficientHorizontalSection w (F.firstCoefficientHorizontal w x)) z =
      if z.val.1 = 0 then (F.firstCoefficientBasis b ω hF w).repr x z else 0 := by
  classical
  obtain ⟨p, rfl⟩ := F.firstCoefficientMap_surjective w x
  rw [F.firstCoefficientHorizontal_map, F.firstCoefficientHorizontalSection_mk]
  change (F.firstCoefficientBasis b ω hF w).repr
      (F.firstCoefficientMap w ⟨F.adaptedConstant w (coefficients p.val.val 0), _⟩) z = _
  rw [F.firstCoefficientBasis_repr_map, F.firstCoefficientBasis_repr_map]
  change b.repr (coefficients (monomial 0 (coefficients p.val.val 0)) z.val.1) z.val.2 = _
  by_cases hz : z.val.1 = 0
  · simp [hz, coefficients_monomial]
  · simp [hz, coefficients_monomial, Finsupp.single_eq_of_ne hz]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct Matrix

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

noncomputable def realFastCoefficientBasis
    (b : Basis κ ℚ (F.FirstCoefficientModule w ⧸ F.firstCoefficientFastSubmodule w hw U)) :
    Basis κ ℝ (F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) :=
  realTransportedQuotientBasis (F.firstCoefficientFastSubmodule w hw U)
    (F.firstCoefficientRealEquiv w) b

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ReducedSquareCoefficientCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem reducedSquareCoefficientMap_repr_symbol
    (p : F.squareFiltration.quotientTop.adaptedLieSubalgebra w) (i : FirstCoefficientIndex w ω) :
    (F.firstCoefficientBasis e ω hF w).repr
      (F.reducedSquareCoefficientMap w (F.squareFiltration.quotientTop.polynomialSymbolMap w p)) i =
      e.repr (F.reducedSquareDifference (coefficients p.val i.val.1)) i.val.2 := by
  rw [F.reducedSquareCoefficientMap_symbol]
  change (F.firstCoefficientBasis e ω hF w).repr
    (F.firstCoefficientMap w ⟨(F.reducedSquareDifferenceRelative w p).val, _⟩) i = _
  rw [F.firstCoefficientBasis_repr_map, F.reducedSquareDifferenceRelative_coefficient]

theorem reducedSquareCoefficientMap_basis_repr [DecidableEq σ]
    (a : ReducedSquareSymbolIndex s w ω) (i : FirstCoefficientIndex w ω) :
    (F.firstCoefficientBasis e ω hF w).repr
      (F.reducedSquareCoefficientMap w (F.reducedSquareSymbolBasis e ω hF w a)) i =
      if a.val.1 = i.val.1 then
        e.repr (F.reducedSquareDifference (F.reducedSquareBasis e ω hF a.val.2)) i.val.2 else 0 := by
  change (F.firstCoefficientBasis e ω hF w).repr
    (F.reducedSquareCoefficientMap w
      (F.squareFiltration.quotientTop.polynomialSymbolBasis (F.reducedSquareBasis e ω hF)
        (fun j => squareBasisWeight ω j.val) (F.reducedSquareBasis_layers e ω hF) w a)) i = _
  rw [F.squareFiltration.quotientTop.polynomialSymbolBasis_apply,
    F.reducedSquareCoefficientMap_repr_symbol, F.squareFiltration.quotientTop.adaptedMonomialBasis_coe,
    coefficients_monomial]
  by_cases hai : a.val.1 = i.val.1
  · simp only [hai, Finsupp.single_eq_same, ite_true]
  · rw [Finsupp.single_eq_of_ne (Ne.symm hai), map_zero, map_zero,
      Finsupp.zero_apply, if_neg hai]

theorem reducedSquareCoefficientMap_basis_height
    (a : ReducedSquareSymbolIndex s w ω) (i : FirstCoefficientIndex w ω) :
    RationalHeightLE ((F.firstCoefficientBasis e ω hF w).repr
      (F.reducedSquareCoefficientMap w (F.reducedSquareSymbolBasis e ω hF w a)) i) 1 := by
  classical
  rw [F.reducedSquareCoefficientMap_basis_repr]
  split_ifs
  · exact F.reducedSquareDifference_basis_height e ω hF a.val.2 i.val.2
  · exact rationalHeightLE_zero le_rfl

theorem reducedSquareCoefficientMap_monomial_blocks
    (a : ReducedSquareSymbolIndex s w ω) (i : FirstCoefficientIndex w ω) (hai : i.val.1 ≠ a.val.1) :
    (F.firstCoefficientBasis e ω hF w).repr
      (F.reducedSquareCoefficientMap w (F.reducedSquareSymbolBasis e ω hF w a)) i = 0 := by
  classical
  rw [F.reducedSquareCoefficientMap_basis_repr, if_neg (Ne.symm hai)]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedRelativeCoefficientBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem firstCoefficientSlowBound_sub (w : σ → ℕ) (T : σ → ℝ) (M N : ℝ)
    (x y : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound e ω hF w T M x)
    (hy : F.FirstCoefficientSlowBound e ω hF w T N y) :
    F.FirstCoefficientSlowBound e ω hF w T (M + N) (x - y) := by
  intro i
  simp only [map_sub, Finsupp.sub_apply]
  exact (abs_sub _ _).trans ((add_le_add (hx i) (hy i)).trans_eq (add_div M N _).symm)

theorem firstCoefficientGrid_sub (w : σ → ℕ) (l : ℕ) (x y : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientGrid e ω hF w l x)
    (hy : F.FirstCoefficientGrid e ω hF w l y) :
    F.FirstCoefficientGrid e ω hF w l (x - y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a - b, ?_⟩
  funext i
  have hai := congrFun ha i
  have hbi := congrFun hb i
  change ((a i - b i : ℤ) : ℝ) =
    (l : ℝ) * (F.realFirstCoefficientBasis e ω hF w).repr (x - y) i
  simp only [Int.cast_sub, map_sub, Finsupp.sub_apply, mul_sub]
  exact congrArg₂ (· - ·) hai hbi

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FastCoefficientSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem reducedSquareCoefficientMap_height [Fintype (ReducedSquareSymbolIndex s w ω)]
    {H : ℕ} (x : F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hx : ∀ i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr x i) H)
    (j : FirstCoefficientIndex w ω) :
    RationalHeightLE ((F.firstCoefficientBasis e ω hF w).repr (F.reducedSquareCoefficientMap w x) j)
      ((Fintype.card (ReducedSquareSymbolIndex s w ω) + 1) *
        H ^ Fintype.card (ReducedSquareSymbolIndex s w ω)) := by
  simpa only [mul_one] using linearMap_coordinate_height
    (F.reducedSquareSymbolBasis e ω hF w) (F.firstCoefficientBasis e ω hF w)
    (F.reducedSquareCoefficientMap w) (F.reducedSquareCoefficientMap_basis_height e ω hF w) x hx j

theorem firstCoefficientFastSubmodule_spanning (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hv : Submodule.span ℚ (Set.range v) = U ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule) :
    Submodule.span ℚ (Set.range (fun i => F.reducedSquareCoefficientMap w (v i))) =
      F.firstCoefficientFastSubmodule w hw U := by
  rw [F.firstCoefficientFastSubmodule_eq_image, ← hv, Submodule.map_span, ← Set.range_comp]
  rfl

theorem firstCoefficientFastSubmodule_spanning_height [Fintype (ReducedSquareSymbolIndex s w ω)]
    (hw : ∀ i, 0 < w i) (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule)
    {H : ℕ} (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H) :
    ∃ z : κ → F.FirstCoefficientModule w,
      Submodule.span ℚ (Set.range z) = F.firstCoefficientFastSubmodule w hw U ∧
      ∀ i j, RationalHeightLE ((F.firstCoefficientBasis e ω hF w).repr (z i) j)
        ((Fintype.card (ReducedSquareSymbolIndex s w ω) + 1) *
          H ^ Fintype.card (ReducedSquareSymbolIndex s w ω)) :=
  ⟨fun i => F.reducedSquareCoefficientMap w (v i),
    F.firstCoefficientFastSubmodule_spanning w hw U v hspan,
    fun i j => F.reducedSquareCoefficientMap_height e ω hF w (v i) (hv i) j⟩

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

theorem firstCoefficientIndex_grade_eq_of_monomial_eq {σ ι : Type*}
    (w : σ → ℕ) (ω : ι → ℕ) (i j : FirstCoefficientIndex w ω)
    (h : i.val.1 = j.val.1) : ω i.val.2 = ω j.val.2 :=
  i.property.symm.trans ((congrArg (fun α => Finsupp.weight w α + 1) h).trans j.property)

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
  {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
  {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L}
  {eK : Basis κ ℚ K} {T : σ → ℝ}

noncomputable def FormalInductionRun.start {p : ℝ}
    (X : F.FormalInductionState b w U V K eK T 2 p) :
    F.FormalInductionRun b w U V K eK T X.P 0 p where
  state := X
  left := []
  right := []
  denominator := X.denominator
  denominator_pos := X.denominator_pos
  denominator_bound := by simpa using X.denominator_bound
  state_denominator_dvd := dvd_refl _
  left_length := by simp
  right_length := by simp
  left_good := by simp
  right_good := by simp
  left_bound := by simp
  right_grid := by simp
  factorization := by simp

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_induction_run_product_controls (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype κ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w)
    {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L} {eK : Basis κ ℚ K}
    {T : σ → ℝ} (_hT : ∀ i, 0 < T i)
    {original : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot}
    {r : ℕ} (_hr : r ≤ s) {q : ℝ}
    (W : F.FormalInductionRun b w U V K eK T original r q)
    {H : ℕ} (_hH : 1 ≤ H)
    (_hStructure : ∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H)
    {p : ℝ} (_hp : 0 ≤ p) (_hqp : q ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hDenom : (W.denominator : ℝ) ≤ Real.exp p),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ W.denominator ∣ m ∧
      CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) W.left.prod.coord ∧
      CoefficientGrid (b.baseChange ℝ) m W.right.prod.coord ∧
      F.FormalCorrectionProperty b w U W.left.prod ∧
      F.FormalCorrectionProperty b w U W.right.prod := by
  obtain ⟨A, hA, hslow⟩ := exists_formal_polynomial_product_bound s 1 (2 * s)
  obtain ⟨B, hB, hgrid⟩ := exists_formal_polynomial_product_grid s (2 * s)
  let C := max A B
  refine ⟨C, hA.trans (Nat.le_max_left A B), ?_⟩
  intro L μ κ σ _ _ _ _ _ F b w hF hgraded U V K eK T hT original r hr q W H hH hStructure
    p hp hqp hμ hσ hHp hDenom
  have hAC : (p + A) ^ A ≤ (p + C) ^ C :=
    shifted_power_self_mono hp (by omega) (Nat.le_max_left A B)
  have hBC : (p + B) ^ B ≤ (p + C) ^ C :=
    shifted_power_self_mono hp (by omega) (Nat.le_max_right A B)
  have hleft : CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + A) ^ A)) W.left.prod.coord := by
    apply hslow F b w hF H p hH hp hμ hσ hHp hStructure T hT W.left
    · rw [W.left_length]
      exact Nat.mul_le_mul_left 2 hr
    · intro x hx
      exact F.gradedPolynomial_mem_adapted b w hF (fun _ => 1) x.coord (W.left_good x hx).2.1
    · intro x hx
      apply (W.left_bound x hx).mono _ T hT (Real.exp_le_exp.mpr ?_)
      simpa only [pow_one] using hqp.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  obtain ⟨m, hm, hmp, hdm, hproducts⟩ :=
    hgrid F b w hF H p hH hp hμ hσ hHp hStructure W.denominator W.denominator_pos hDenom
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hBC), hdm,
    hleft.mono _ T hT (Real.exp_le_exp.mpr hAC), ?_,
    FormalCorrectionProperty.list_prod hgraded W.left W.left_good,
    FormalCorrectionProperty.list_prod hgraded W.right W.right_good⟩
  apply hproducts W.right
  · rw [W.right_length]
    exact Nat.mul_le_mul_left 2 hr
  · intro x hx
    exact F.gradedPolynomial_mem_adapted b w hF (fun _ => 1) x.coord (W.right_good x hx).2.1
  · exact W.right_grid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
  {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L}
  {eK : Basis κ ℚ K} {T : σ → ℝ} {q : ℝ}
  {original : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot}

theorem FormalInductionRun.terminal_lower_log
    (W : F.FormalInductionRun b w U V K eK T original (s - 1) q)
    (hs : 2 ≤ s) (α : σ →₀ ℕ) (d : ℕ) (hd : 2 ≤ d) (hds : d ≤ s) :
    basisGradeProjection (b.baseChange ℝ) w d (coefficients W.state.P.coord α) ∈ V.baseChange ℝ :=
  W.state.lower_log α d hd (by omega)

theorem FormalInductionRun.terminal_lower_bracket
    (W : F.FormalInductionRun b w U V K eK T original (s - 1) q)
    (hs : 2 ≤ s) (d : ℕ) (hd : d < s) (z : κ) (α : σ →₀ ℕ) :
    ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients W.state.P.coord α),
      (1 : ℝ) ⊗ₜ[ℚ] (eK z : L)⁆ ∈ V.baseChange ℝ :=
  W.state.lower_bracket d (by omega) z α

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StepDropTerminalContainment
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
  {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L}
  {eK : Basis κ ℚ K} {T : σ → ℝ} {q : ℝ}
  {original : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot}

theorem FormalInductionRun.terminal_coefficients_mem_stepDropSubmodule
    (W : F.FormalInductionRun b w U V K eK T original (s - 1) q)
    (hs : 2 ≤ s) (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (α : σ →₀ ℕ) :
    coefficients W.state.P.coord α ∈
      stepDropSubmodule (b.baseChange ℝ) w U (V.baseChange ℝ) (K.baseChange ℝ) := by
  apply (mem_stepDropSubmodule _ _ _ _ _ _).mpr
  refine ⟨W.state.mem_U α, W.state.horizontal α, ?_, ?_⟩
  · rintro k ⟨x, rfl⟩
    apply real_bracket_mem_of_basis (eK.baseChange ℝ) (K.subtype.baseChange ℝ) (V.baseChange ℝ)
      (basisGradeProjection (b.baseChange ℝ) w 1 (coefficients W.state.P.coord α)) _ x
    intro z
    simpa only [Basis.baseChange_apply, LinearMap.baseChange_tmul, Submodule.subtype_apply] using
      W.terminal_lower_bracket hs 1 (by omega) z α
  · have h := F.real_sub_horizontal_mem_of_lower_grades b w hF (V.baseChange ℝ)
      (j := s + 1) (by omega) (coefficients W.state.P.coord α)
      (fun d hd hds => W.terminal_lower_log hs α d hd (by omega))
    rw [F.realLayer_terminal] at h
    simpa only [LieSubmodule.bot_toSubmodule, sup_bot_eq] using h

theorem FormalInductionRun.terminal_coefficients_mem_rational_stepDrop
    {U₀ : LieSubalgebra ℚ L}
    (W : F.FormalInductionRun b w (realificationLieSubalgebra U₀) V K eK T original (s - 1) q)
    (hs : 2 ≤ s) (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (α : σ →₀ ℕ) :
    coefficients W.state.P.coord α ∈ (stepDropSubmodule b w U₀ V K).baseChange ℝ := by
  rw [stepDropSubmodule_baseChange b w U₀ V K eK]
  exact W.terminal_coefficients_mem_stepDropSubmodule hs hF α

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DerivativeHorizontalLifts
namespace OAI

section

namespace Erdos3

theorem graph_derivative_decomposition
    {σ : Type*} [Fintype σ] {m a k : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hs : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ Fin m)))
    (ha : a ≤ m) (N : ℝ) (H : ℕ) :
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    ∀ (lifts : RationalHorizontalLift k P ha A scale N H),
      (∀ v : V, euclideanVerticalMap scale hs A (lifts.rationalLift ⟨P v, v, rfl⟩) = v.val.val) →
      ∀ (G : (σ → ℝ) →ₗ[ℝ] Z), (∀ y i, (G y).val (Sum.inl i) = y i) →
      ∀ (x : Z) (y : σ → ℝ) (r : Fin m → ℝ),
        (∀ j, x.val (Sum.inr j) = scale j * (Y y j - A r j)) →
        ∃ (s : Fin m → ℝ) (q : LinearMap.range P),
          Y y = s + A r + lifts.geometricLift q ∧
          ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤
            ‖G (fun i => x.val (Sum.inl i))‖ := by
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  dsimp only
  intro lifts hrecovers G hG x y r hx
  let w := G (fun i => x.val (Sum.inl i))
  let v : V := ⟨x - w, euclidean_graph_residual_mem_kernel T hT Z G hG x⟩
  let q : LinearMap.range P := ⟨P v, v, rfl⟩
  let s : Fin m → ℝ := fun j => w.val (Sum.inr j) / scale j
  have hscale (j) : scale j * s j = w.val (Sum.inr j) := mul_div_cancel₀ _ (hs j)
  have hS (j) : scale j * lifts.geometricLift q j =
      x.val (Sum.inr j) - w.val (Sum.inr j) := by
    calc
      _ = euclideanVerticalMap scale hs A (lifts.rationalLift q) (Sum.inr j) := by
        rw [lifts.factorization]
        rfl
      _ = v.val.val (Sum.inr j) := congrArg (fun z => z (Sum.inr j)) (hrecovers v)
      _ = _ := rfl
  refine ⟨s, q, ?_, ?_⟩
  · funext j
    change Y y j = s j + A r j + lifts.geometricLift q j
    apply mul_left_cancel₀ (hs j)
    nlinarith [hS j, hscale j, hx j]
  · have he : (fun j => scale j * s j) = fun j => w.val (Sum.inr j) := funext hscale
    rw [he]
    exact euclideanVerticalProjection_norm_le w.val

end Erdos3

end

section

namespace Erdos3

theorem indexed_derivative_decomposition
    {σ : Type*} [Fintype σ] [DecidableEq σ] {m a k : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (hTpos : ∀ i, 0 < T i)
    (scale : Fin m → ℝ) (hs : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) (l : ℕ) (hl : 0 < l)
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ Fin m)))
    (ha : a ≤ m) (N B : ℝ) (H : ℕ) :
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    ∀ (lifts : RationalHorizontalLift k P ha A scale N H),
      (∀ v : V, euclideanVerticalMap scale hs A (lifts.rationalLift ⟨P v, v, rfl⟩) = v.val.val) →
      ∀ (G : (σ → ℝ) →ₗ[ℝ] Z), (∀ y i, (G y).val (Sum.inl i) = y i) →
      (∀ i, ‖G (Pi.basisFun ℝ σ i)‖ ≤ B) →
      ∀ (I : ℕ), 0 < I →
      (∀ i, ∃ v : Z, v.val ∈ euclideanDerivativeLattice T hT scale hs Y A l hl ∧
        euclideanDerivativeShiftMap T hT v.val = (I : ℝ) • Pi.basisFun ℝ σ i) →
      ∀ i, ∃ (s r : Fin m → ℝ) (q : LinearMap.range P),
        Y (Pi.basisFun ℝ σ i) = s + A r + lifts.geometricLift q ∧
        r ∈ realDenominatorGrid (l * I) ∧
        ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤ B / T i := by
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  dsimp only
  intro lifts hrecovers G hG hGB I hI hI_lifts i
  obtain ⟨v, hv, hshift⟩ := hI_lifts i
  let x : Z := (I : ℝ)⁻¹ • v
  obtain ⟨r, hr, hright⟩ := divided_derivative_lattice_coordinates T hT scale hs Y A l hl
    I hI (Pi.basisFun ℝ σ i) v.val hv hshift
  obtain ⟨s, q, heq, hsmall⟩ := graph_derivative_decomposition T hT scale hs Y A Z ha N H
    lifts hrecovers G hG x (Pi.basisFun ℝ σ i) r hright
  refine ⟨s, r, q, heq, hr, ?_⟩
  have hleft : (fun j => x.val (Sum.inl j)) =
      fun j => (Pi.basisFun ℝ σ i) j / T j :=
    funext (divided_derivative_horizontal_coordinates T hT I hI (Pi.basisFun ℝ σ i) v.val hshift)
  rw [hleft] at hsmall
  exact hsmall.trans (linearMap_divided_basis_norm_le G T i (hTpos i) B (hGB i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformDerivativeLatticeExtraction
namespace OAI

section

namespace Erdos3

theorem euclideanDerivative_lattice_extraction
    {σ : Type*} [Fintype σ] [DecidableEq σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → Fin m → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i)
    (a : ℕ) (ha : a ≤ m) (Tmin : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) :
    let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT0 scale hs0 Y A l hl
    let Z := shortVectorSpan Λ ρ
    let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
    let V := LinearMap.ker π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    let k := Module.finrank ℝ V
    let C := (((Module.finrank ℝ Z : ℝ) + 2) * ρ) ^ Module.finrank ℝ Z / δ
    let B := C * (l : ℝ) ^ k
    let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * B
    C * (l : ℝ) ^ m < Tmin →
      ∃ lifts : RationalHorizontalLift k P ha A scale N (Nat.ceil B),
        ∃ I : ℕ, 0 < I ∧ (I : ℝ) ≤ B ∧
          ∀ i, ∃ (s r' : Fin m → ℝ) (q : LinearMap.range P),
            Y (Pi.basisFun ℝ σ i) = s + A r' + lifts.geometricLift q ∧
            r' ∈ realDenominatorGrid (l * I) ∧
            ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤ B / T i := by
  let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
  let Λ := euclideanDerivativeLattice T hT0 scale hs0 Y A l hl
  let Z := shortVectorSpan Λ ρ
  let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
  let V := LinearMap.ker π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  let k := Module.finrank ℝ V
  let C := (((Module.finrank ℝ Z : ℝ) + 2) * ρ) ^ Module.finrank ℝ Z / δ
  let B := C * (l : ℝ) ^ k
  let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * B
  let I := (latticeImage (shortVectorLattice Λ ρ) π).toAddSubgroup.relIndex
    integerCoordinateLattice.toAddSubgroup
  change C * (l : ℝ) ^ m < Tmin →
    ∃ lifts : RationalHorizontalLift k P ha A scale N (Nat.ceil B),
      ∃ I : ℕ, 0 < I ∧ (I : ℝ) ≤ B ∧
        ∀ i, ∃ (s r' : Fin m → ℝ) (q : LinearMap.range P),
          Y (Pi.basisFun ℝ σ i) = s + A r' + lifts.geometricLift q ∧
          r' ∈ realDenominatorGrid (l * I) ∧
          ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤ B / T i
  intro hvertical
  obtain ⟨hI, G, hG, _, hcov, hIB, hGB⟩ := euclideanDerivative_index_graph_bounds
    T hT scale hscale Y A hA hdiag l hl R δ hR hδ H r hr hnorm hdense hlarge
  obtain ⟨lifts, hrecovers⟩ := euclideanDerivative_horizontal_lifts T hT0 scale hscale
    Y A hA hdiag l hl ρ a ha Tmin C hscalehor hblock hfar hvertical hcov
  refine ⟨lifts, I, hI, hIB, ?_⟩
  have hGbasis (i) : ‖G (Pi.basisFun ℝ σ i)‖ ≤ B :=
    (euclidean_section_basis_norm_le_gram_sqrt Z G hG i).trans hGB
  have hI_lifts (i) : ∃ v : Z, v.val ∈ Λ ∧
      euclideanDerivativeShiftMap T hT0 v.val = (I : ℝ) • Pi.basisFun ℝ σ i := by
    obtain ⟨v, hv, hπv⟩ := latticeImage_basis_lifts (shortVectorLattice Λ ρ) π i
    exact ⟨v, hv, hπv⟩
  exact indexed_derivative_decomposition (σ := σ) (m := m) (a := a) (k := k)
    T hT0 (fun i => lt_of_lt_of_le zero_lt_one (hT i)) scale hs0 Y A l hl Z ha N B
    (Nat.ceil B) lifts hrecovers G hG hGbasis I hI hI_lifts

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_uniform_lattice_extraction
    {σ : Type*} [Fintype σ] [DecidableEq σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → Fin m → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (a : ℕ) (ha : a ≤ m) (Tmin : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i)
    (p : ℝ) (hp : 0 ≤ p)
    (hdim : ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) ≤ p)
    (hlcap : (l : ℝ) ≤ Real.exp p) (hRcap : R ≤ Real.exp p)
    (hδcap : δ⁻¹ ≤ Real.exp p)
    (hmin : Real.exp ((p + 2) ^ 3) < Tmin) (hside : ∀ i, Tmin ≤ T i) :
    let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT0 scale hs0 Y A l hl
    let Z := shortVectorSpan Λ ρ
    let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
    let V := LinearMap.ker π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    let k := Module.finrank ℝ V
    let C := (((Module.finrank ℝ Z : ℝ) + 2) * ρ) ^ Module.finrank ℝ Z / δ
    let B := C * (l : ℝ) ^ k
    let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * B
    let E := Real.exp ((p + 2) ^ 3)
    ∃ lifts : RationalHorizontalLift k P ha A scale N (Nat.ceil B),
      N ≤ E ∧ (Nat.ceil B : ℝ) ≤ E ∧
        ∃ I : ℕ, 0 < I ∧ ((l * I : ℕ) : ℝ) ≤ E ∧
          ∀ i, ∃ (s r' : Fin m → ℝ) (q : LinearMap.range P),
            Y (Pi.basisFun ℝ σ i) = s + A r' + lifts.geometricLift q ∧
            r' ∈ realDenominatorGrid (l * I) ∧
            ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤ E / T i := by
  let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
  let Λ := euclideanDerivativeLattice T hT0 scale hs0 Y A l hl
  let Z := shortVectorSpan Λ ρ
  let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
  let V := LinearMap.ker π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  let k := Module.finrank ℝ V
  let C := (((Module.finrank ℝ Z : ℝ) + 2) * ρ) ^ Module.finrank ℝ Z / δ
  let B := C * (l : ℝ) ^ k
  let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * B
  let E := Real.exp ((p + 2) ^ 3)
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  obtain ⟨hthreshold, hBE, hNE, hlBE, hheight⟩ :=
    lattice_subspace_budgets_le_exp Z V l R δ p hp hdim hlcap hR0 hRcap hδ hδcap
  have hN : N ≤ E := by
    simpa only [N, Fintype.card_sum] using hNE
  have hσ : (Fintype.card σ : ℝ) ≤ p := by
    have hd : (Fintype.card σ : ℝ) + Fintype.card (Fin m) ≤ p := by exact_mod_cast hdim
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Fin m))]
  have hprojection := derivative_projection_budget_le_exp (Fintype.card σ) R δ p
    hp hσ hR0 hRcap hδ hδcap
  have hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i := by
    intro i
    have hi := (div_lt_iff₀ hδ).mp (hprojection.trans_lt (hmin.trans_le (hside i)))
    simpa only [mul_comm] using hi
  have hvertical : C * (l : ℝ) ^ m < Tmin := hthreshold.trans_lt hmin
  obtain ⟨lifts, I, hI, hIB, hdecomp⟩ := euclideanDerivative_lattice_extraction
    T hT scale hscale Y A hA hdiag l hl R δ hR hδ H r hr hnorm hdense hlarge
    a ha Tmin hscalehor hblock hfar hvertical
  refine ⟨lifts, hN, hheight, I, hI, ?_, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hIB (Nat.cast_nonneg l)).trans hlBE
  · intro i
    obtain ⟨s, r', q, heq, hr', hs⟩ := hdecomp i
    refine ⟨s, r', q, heq, hr', ?_⟩
    exact hs.trans (div_le_div_of_nonneg_right hBE (zero_le_one.trans (hT i)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedCoordinateExtraction
namespace OAI

section

namespace Erdos3

theorem exists_uniform_coordinate_derivative_system
    {σ : Type*} [Fintype σ] [DecidableEq σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → Fin m → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (a : ℕ) (ha : a ≤ m) (Tmin : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i)
    (p : ℝ) (hp : 0 ≤ p)
    (hdim : ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) ≤ p)
    (hlcap : (l : ℝ) ≤ Real.exp p) (hRcap : R ≤ Real.exp p)
    (hδcap : δ⁻¹ ≤ Real.exp p)
    (hmin : Real.exp ((p + 2) ^ 3) < Tmin) (hside : ∀ i, Tmin ≤ T i) :
    Nonempty (CoordinateDerivativeSystem ha T Y A scale (Real.exp ((p + 2) ^ 3))) := by
  obtain ⟨lifts, hN, hheight, I, hI, hIcap, hdecomp⟩ :=
    euclideanDerivative_uniform_lattice_extraction T hT scale hscale Y A hA hdiag
      l hl R δ hR hδ H r hr hnorm hdense a ha Tmin hscalehor hblock hfar
      p hp hdim hlcap hRcap hδcap hmin hside
  exact coordinateDerivativeSystem_of_lifts T Y A scale _ ha _ _ lifts hN hheight
    (l * I) (Nat.mul_pos hl hI) hIcap hdecomp

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem firstCoefficient_coordinate_system
    {σ ι E : Type*} [Fintype σ] [DecidableEq σ] [AddCommGroup E] [Module ℝ E] {d : ℕ}
    (ω : ι → ℕ) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (b : Basis (Fin d) ℝ E) (Y : (σ → ℝ) →ₗ[ℝ] E) (f : E ≃ₗ[ℝ] E)
    (hf : ∀ i j, ω (rows i).val.2 ≤ ω (rows j).val.2 →
      LinearMap.toMatrix b b f.toLinearMap i j = (1 : Matrix (Fin d) (Fin d) ℝ) i j)
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i) (l : ℕ) (hl : 0 < l)
    (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ) (H : Finset (σ → ℤ))
    (r : (σ → ℤ) → Fin d → ℝ) (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T (fun i => monomialScale T (rows i).val.1)
        (b.equivFun.toLinearMap.comp Y) (LinearMap.toMatrix b b f.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (p : ℝ) (hp : 0 ≤ p)
    (hdim : ((Fintype.card σ + Fintype.card (Fin d) : ℕ) : ℝ) ≤ p)
    (hlcap : (l : ℝ) ≤ Real.exp p) (hRcap : R ≤ Real.exp p) (hδcap : δ⁻¹ ≤ Real.exp p)
    (Tmin : ℝ) (hmin : Real.exp ((p + 2) ^ 3) < Tmin) (hside : ∀ i, Tmin ≤ T i) :
    ∃ (e : Equiv.Perm (Fin d)) (a : ℕ) (ha : a ≤ d),
      (∀ i, i.val < a ↔ (rows (e i)).val.1 = 0) ∧
      let b' := b.reindex e.symm
      let Y' := b'.equivFun.toLinearMap.comp Y
      let A' := b'.equivFun.symm.trans (f.trans b'.equivFun)
      Nonempty (CoordinateDerivativeSystem ha T Y' A'
        (fun i => monomialScale T (rows (e i)).val.1) (Real.exp ((p + 2) ^ 3))) := by
  obtain ⟨e, a, ha, hzero, haction⟩ := exists_lattice_ready_firstCoefficient_basis ω rows b
  obtain ⟨htri, hdiag, hblock⟩ := haction f hf
  let b' := b.reindex e.symm
  let Y' := b'.equivFun.toLinearMap.comp Y
  let A' := b'.equivFun.symm.trans (f.trans b'.equivFun)
  let scale := fun i => monomialScale T (rows (e i)).val.1
  let r' := fun h => r h ∘ e
  have hY : Y' = (LinearMap.funLeft ℝ ℝ e).comp (b.equivFun.toLinearMap.comp Y) := by
    apply LinearMap.ext
    intro x
    funext i
    exact congrFun (basis_reindex_equivFun b e (Y x)) i
  have hA : LinearMap.toMatrix' A'.toLinearMap =
      (LinearMap.toMatrix b b f.toLinearMap).submatrix e e := by
    rw [basis_coordinate_linearEquiv_matrix]
    ext i j
    exact basis_reindex_toMatrix b e f.toLinearMap i j
  have hscale : ∀ i, 1 ≤ scale i := fun i => one_le_monomialScale T hT _
  have hTmin : 1 ≤ Tmin := (Real.one_le_exp (by positivity)).trans hmin.le
  obtain ⟨hhor, hfar⟩ := sorted_firstCoefficient_scale_bounds ω (rows ∘ e) hzero T Tmin hTmin hside
  have hr' : ∀ h ∈ H, r' h ∈ realDenominatorGrid l :=
    fun h hh => realDenominatorGrid_comp l (r h) (hr h hh) e
  have hnorm' : ∀ h ∈ H, ‖derivativeGridPoint T scale Y' (LinearMap.toMatrix' A'.toLinearMap)
      h (r' h)‖ ≤ R := by
    intro h hh
    rw [hY, hA]
    exact (derivativeGridPoint_reindex_norm T (fun i => monomialScale T (rows i).val.1)
      (b.equivFun.toLinearMap.comp Y) (LinearMap.toMatrix b b f.toLinearMap) e h (r h)).le.trans
        (hnorm h hh)
  refine ⟨e, a, ha, hzero, ?_⟩
  exact exists_uniform_coordinate_derivative_system T hT scale hscale Y' A' htri hdiag
    l hl R δ hR hδ H r' hr' hnorm' hdense a ha Tmin hhor hblock hfar
    p hp hdim hlcap hRcap hδcap hmin hside

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FastCoefficientDerivativeCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

variable {σ κ L : Type*} [Fintype σ] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
  (b : Basis κ ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1) ⧸
    F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)))

noncomputable def fastCoefficientDirectionCoordinates
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) : (σ → ℝ) →ₗ[ℝ] (κ → ℝ) :=
  b.equivFun.toLinearMap.comp
    ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ.comp
        (F.realFirstCoefficientDirectionMap B.coord))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReindexedFastCoefficientSection
namespace OAI

section

namespace Erdos3

open Module

namespace NilpotentLieFiltration

theorem exists_reindexed_fast_coefficient_section
    {σ ι ν L : Type*} [Fintype ν] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (b : Basis ν ℝ (F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U))
    (rows : ν → FirstCoefficientIndex w ω) (R : (ν → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
    (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R y) = b.equivFun.symm y)
    (δ : ℕ) (C : ℝ)
    (hproj : ∀ l x, F.FirstCoefficientGrid e ω hF w l x →
      b.equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ x) ∈ realDenominatorGrid (δ * l))
    (hgrid : ∀ l y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w (δ * l) (R y))
    (hweighted : ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
      (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
        |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ x) i| ≤
          C * M / monomialScale T (rows i).val.1) ∧
      (∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF w T (C * M) (R y)))
    (perm : Equiv.Perm ν) :
    ∃ R' : (ν → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w,
      (∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R' y) =
        (b.reindex perm.symm).equivFun.symm y) ∧
      (∀ l x, F.FirstCoefficientGrid e ω hF w l x →
        (b.reindex perm.symm).equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ x) ∈
          realDenominatorGrid (δ * l)) ∧
      (∀ l y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w (δ * l) (R' y)) ∧
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
        (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
          |(b.reindex perm.symm).equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ x) i| ≤
            C * M / monomialScale T (rows (perm i)).val.1) ∧
        (∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows (perm i)).val.1) →
          F.FirstCoefficientSlowBound e ω hF w T (C * M) (R' y)) := by
  refine ⟨reindexCoordinateSection R perm,
    reindexCoordinateSection_right_inverse _ b R hR perm, ?_, ?_, ?_⟩
  · intro l x hx
    exact basis_reindex_grid b perm (δ * l) _ (hproj l x hx)
  · intro l y hy
    exact hgrid l _ (realDenominatorGrid_comp l y hy perm.symm)
  · intro T hT M hM
    obtain ⟨hproj', hlift'⟩ := hweighted T hT M hM
    constructor
    · intro x hx i
      simpa only [basis_reindex_equivFun] using hproj' x hx (perm i)
    · intro y hy
      apply hlift' (fun i => y (perm.symm i))
      intro i
      simpa only [Equiv.apply_symm_apply] using hy (perm.symm i)

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledLayerOneCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U))
  (ha : a ≤ d) (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
  (hη : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = F.realFastCoefficientHorizontal w hw U x)

include hη

omit [Fintype ι] in
theorem layerOne_equiv_symm_coordinates (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    η.symm x = fun i => b.equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ
      (F.realFirstCoefficientHorizontalSection w x)) (Fin.castLE ha i) := by
  apply η.injective
  rw [LinearEquiv.apply_symm_apply, hη]
  exact (F.realFirstCoefficientHorizontal_section w x).symm

omit [Fintype ι] in
theorem layerOne_equiv_representative
    (R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
    (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R y) = b.equivFun.symm y)
    (x : Fin a → ℝ) :
    η x = F.realFirstCoefficientHorizontal w (R (extendInitialCoordinates x)) := by
  have h := hη (b.equivFun.symm (extendInitialCoordinates x))
  simp only [LinearEquiv.apply_symm_apply, extendInitialCoordinates_castLE] at h
  rw [← hR] at h
  exact h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalLinearLiftReabsorption
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

variable {σ κ ι K L : Type*} [Fintype κ] [AddCommGroup K] [Module ℝ K]
  [LieRing L] [LieAlgebra ℚ L]

theorem basisPolynomialLift_bound_of_coordinate_bound (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M A τ : ℝ) (hM : 0 ≤ M)
    (hS : ∀ k, CoefficientBound e T M (S k)) (x : K)
    (hx : ‖b.equivFun x‖ ≤ A / τ) :
    CoefficientBound e T ((Fintype.card κ : ℝ) * M * A / τ)
      (basisPolynomialLift b S x) := by
  apply (basisPolynomialLift_coefficientBound b S e T M hS x).mono e T hT
  calc
    (Fintype.card κ : ℝ) * M * ‖b.equivFun x‖ ≤
        (Fintype.card κ : ℝ) * M * (A / τ) :=
      mul_le_mul_of_nonneg_left hx (mul_nonneg (Nat.cast_nonneg _) hM)
    _ = _ := by ring

theorem basisPolynomialLift_reabsorption_bound (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M N A τ : ℝ) (hM : 0 ≤ M)
    (hS : ∀ k, CoefficientBound e T M (S k))
    (small : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : CoefficientBound e T (N / τ) small)
    (x : K) (hx : ‖b.equivFun x‖ ≤ A / τ) :
    CoefficientBound e T ((N + (Fintype.card κ : ℝ) * M * A) / τ)
      (small + basisPolynomialLift b S x) := by
  have h := basisPolynomialLift_bound_of_coordinate_bound b S e T hT M A τ hM hS x hx
  have hsum := hsmall.sub e T (h.neg e T)
  rw [sub_neg_eq_add] at hsum
  convert hsum using 1
  ring

theorem basisPolynomialLift_reabsorption_grid (b : Basis κ ℝ K)
    (R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (l m n : ℕ) (hR : ∀ k, CoefficientGrid e m (R k))
    (rational : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hrational : CoefficientGrid e n rational)
    (x : K) (hx : b.equivFun x ∈ realDenominatorGrid l) :
    CoefficientGrid e (n * (m * l)) (rational + basisPolynomialLift b R x) := by
  have h := basisPolynomialLift_coefficientGrid b R e l m hR x hx
  intro α
  have hsum := realDenominatorGrid_sub_product n (m * l)
    (fun i => e.repr (coefficients rational α) i)
    (-(fun i => e.repr (coefficients (basisPolynomialLift b R x) α) i))
    (hrational α) (realDenominatorGrid_neg (m * l) (h α))
  simp only [sub_neg_eq_add] at hsum
  simp only [map_add, Finsupp.add_apply]
  exact hsum

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBinaryAssignments
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mixedTranslationCoordinates_nodup (s : ℕ) : (mixedTranslationCoordinates s).Nodup :=
  Finset.nodup_toList _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialKernelDirectionBudget
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype κ] {E : Submodule ℚ L}

noncomputable def polynomialKernelDirection (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (i : σ) : κ → ℝ :=
  realSubspaceCoordinateMap b Q (coefficients P (Finsupp.single i 1))

theorem polynomialKernelDirection_lift [DecidableEq κ] (b : Basis μ ℚ L) (e : Basis κ ℚ E)
    (Q : Matrix κ μ ℚ) (hQ : Q * bracketLiftMatrix b e = 1)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hP : ∀ α, coefficients P α ∈ E.baseChange ℝ)
    (i : σ) :
    bracketSystemLift e (polynomialKernelDirection b Q P i) = coefficients P (Finsupp.single i 1) :=
  lift_realSubspaceCoordinateMap b e Q hQ _ (hP _)

theorem polynomialKernelDirection_norm (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    {H : ℕ} (hQ : ∀ i j, RationalHeightLE (Q i j) H)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (M : ℝ) (hM : 0 ≤ M) (hP : CoefficientBound (b.baseChange ℝ) T M P) (i : σ) :
    ‖polynomialKernelDirection b Q P i‖ ≤
      (((Fintype.card μ : ℝ) + 1) * (H + 1)) * M / T i := by
  have hp := (coefficientBound_iff_norm (b.baseChange ℝ) T hT hM P).mp hP (Finsupp.single i 1)
  have hs : monomialScale T (Finsupp.single i 1) = T i := by
    simp only [monomialScale, Finsupp.prod_single_index, pow_zero, pow_one]
  rw [hs] at hp
  apply (realSubspaceCoordinateMap_norm b Q hQ _).trans
  calc
    (((Fintype.card μ : ℝ) + 1) * (H + 1)) * ‖(b.baseChange ℝ).equivFun
        (coefficients P (Finsupp.single i 1))‖ ≤
        (((Fintype.card μ : ℝ) + 1) * (H + 1)) * (M / T i) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

theorem polynomialKernelDirection_grid (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (l : ℕ)
    (hP : CoefficientGrid (b.baseChange ℝ) l P) (i : σ) :
    polynomialKernelDirection b Q P i ∈ realDenominatorGrid (matrixDenominator Q * l) :=
  realSubspaceCoordinateMap_grid b Q l _ (hP _)

theorem exists_controlled_polynomial_kernel_directions
    (b : Basis μ ℚ L) (e : Basis κ ℚ E) {H l : ℕ}
    (hH : 1 ≤ H) (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) H)
    (hl : 0 < l) (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hA : ∀ α, coefficients A α ∈ E.baseChange ℝ)
    (hB : ∀ α, coefficients B α ∈ E.baseChange ℝ)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ) (hM : 0 ≤ M)
    (hAbound : CoefficientBound (b.baseChange ℝ) T M A)
    (hBgrid : CoefficientGrid (b.baseChange ℝ) l B) :
    ∃ (a c : σ → κ → ℝ) (d : ℕ),
      0 < d ∧ d ≤ rationalSolveHeight (Fintype.card κ) H ^
        (Fintype.card κ * Fintype.card μ) * l ∧
      ∀ i,
        bracketSystemLift e (a i) = coefficients A (Finsupp.single i 1) ∧
        bracketSystemLift e (c i) = coefficients B (Finsupp.single i 1) ∧
        ‖a i‖ ≤ (((Fintype.card μ : ℝ) + 1) *
          ((rationalSolveHeight (Fintype.card κ) H : ℝ) + 1)) * M / T i ∧
        c i ∈ realDenominatorGrid d := by
  classical
  obtain ⟨Q, hQ, hQheight⟩ := exists_bracketLiftMatrix_leftInverse b e hH he
  refine ⟨polynomialKernelDirection b Q A, polynomialKernelDirection b Q B,
    matrixDenominator Q * l, Nat.mul_pos (matrixDenominator_pos Q) hl,
    Nat.mul_le_mul_right l (matrixDenominator_le Q hQheight), fun i => ?_⟩
  exact ⟨polynomialKernelDirection_lift b e Q hQ A hA i,
    polynomialKernelDirection_lift b e Q hQ B hB i,
    polynomialKernelDirection_norm b Q hQheight A T hT M hM hAbound i,
    polynomialKernelDirection_grid b Q B l hBgrid i⟩

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_uniform_polynomial_kernel_directions
    {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype μ] [Fintype κ]
    {E : Submodule ℚ L} (b : Basis μ ℚ L) (e : Basis κ ℚ E)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) H)
    {p M : ℝ} (hp : 0 ≤ p) (hM : 0 ≤ M)
    (hambient : (Fintype.card μ : ℝ) ≤ p) (hkernel : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) (hMp : M ≤ Real.exp p)
    (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hA : ∀ α, coefficients A α ∈ E.baseChange ℝ)
    (hB : ∀ α, coefficients B α ∈ E.baseChange ℝ)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (hAbound : CoefficientBound (b.baseChange ℝ) T M A)
    (hBgrid : CoefficientGrid (b.baseChange ℝ) l B) :
    ∃ (a c : σ → κ → ℝ) (d : ℕ),
      0 < d ∧ (d : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      ∀ i,
        bracketSystemLift e (a i) = coefficients A (Finsupp.single i 1) ∧
        bracketSystemLift e (c i) = coefficients B (Finsupp.single i 1) ∧
        ‖a i‖ ≤ Real.exp ((p + 2) ^ 8) / T i ∧ c i ∈ realDenominatorGrid d := by
  obtain ⟨a, c, d, hd, hdbound, hdirs⟩ := exists_controlled_polynomial_kernel_directions
    b e hH he hl A B hA hB T hT M hM hAbound hBgrid
  have hbudget := polynomial_kernel_direction_budget (Fintype.card μ) (Fintype.card κ) H l
    hp hM hH hambient hkernel hHp hlp hMp
  refine ⟨a, c, d, hd, (Nat.cast_le.mpr hdbound).trans hbudget.2, fun i => ?_⟩
  exact ⟨(hdirs i).1, (hdirs i).2.1,
    (hdirs i).2.2.1.trans (div_le_div_of_nonneg_right hbudget.1 (hT i).le), (hdirs i).2.2.2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.ControlledBracketToCurrentLayer
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ σ κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

theorem formal_invariant_correction_preserves_derivative_remainder
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hAV : ∀ α, coefficients A.coord α ∈ V) (hBV : ∀ α, coefficients B.coord α ∈ V)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule) :
    ∀ i α, coefficients (dualAdjoint A⁻¹ (small i - formalLogDerivative i A)) α ∈
        V ⊔ (F.realLayer j).toSubmodule ∧
      coefficients (dualAdjoint B (rational i) - formalLogDerivative i B) α ∈
        V ⊔ (F.realLayer j).toSubmodule := by
  let W := V.restrictScalars ℚ ⊔ F.realification.layer j
  have hWiff (x : ℝ ⊗[ℚ] L) : x ∈ W ↔ x ∈ V ⊔ (F.realLayer j).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer j).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  intro i α
  have h := polynomial_derivative_removal_preserves_coefficients U W
    (F.realification.invariant_sup_layer U (V.restrictScalars ℚ) hUV j)
    i A B (small i) (rational i) hAU hBU
    (fun β => Submodule.mem_sup_left (hAV β)) (fun β => Submodule.mem_sup_left (hBV β))
    (fun β => (hWiff _).mpr (hsmall i β)) (fun β => (hWiff _).mpr (hrational i β))
  exact ⟨(hWiff _).mp (h.1 α), (hWiff _).mp (h.2 α)⟩

include hF in
theorem formal_invariant_bracket_derivative_step (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    {j : ℕ} (hj : 2 ≤ j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hAV : ∀ α, coefficients A.coord α ∈ V) (hBV : ∀ α, coefficients B.coord α ∈ V)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : σ → κ) (I : κ → ℝ ⊗[ℚ] L)
    (hI : ∀ x, basisGradeProjection (b.baseChange ℝ) w 1 (I x) = I x)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational (fun i => S (k i)))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hS : ∀ x α, coefficients (dualAdjoint A⁻¹ (S x) - monomial 0 (I x)) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    let P' := A⁻¹ * P * B⁻¹
    let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A)
    let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B
    let extra' := fun i => dualAdjoint A⁻¹ (S (k i))
    PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P' small' rational' extra' ∧
      (∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer j).toSubmodule ∧
        coefficients (rational' i) α ∈ V ⊔ (F.realLayer j).toSubmodule) ∧
      ∀ i α, coefficients (extra' i - VectorPolynomial.map
        ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
          V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  intro P' small' rational' extra'
  have hnew := PolynomialDerivativeSystemMod.remove U (V.restrictScalars ℚ) hUV P A B hAU
    small rational (fun i => S (k i)) hsystem
  have hrem := F.formal_invariant_correction_preserves_derivative_remainder U V hUV j A B
    hAU hBU hAV hBV small rational hsmall hrational
  have hmono : V ⊔ (F.realLayer j).toSubmodule ≤ V ⊔ (F.realLayer 2).toSubmodule := by
    apply sup_le_sup_left _ V
    intro x hx
    exact F.realification.antitone hj hx
  refine ⟨hnew, hrem, ?_⟩
  apply F.formal_extra_horizontal_equation b w hF hs V hV j P' small' rational' extra'
    hnew (fun i α => hmono (hrem i α).1) (fun i α => hmono (hrem i α).2)
  intro i
  exact F.formal_lift_nonhorizontal_remainder b w hF V hV (by omega : 1 ≤ j)
    (extra' i) (I (k i)) (hI _) (hS _)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hF in
theorem formal_bracket_correction_preserves_log_conditions
    (V K : Submodule ℝ (ℝ ⊗[ℚ] L)) {j : ℕ} (hj : 2 ≤ j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients B.coord α) = coefficients B.coord α)
    (hAK : j = 2 → ∀ α, coefficients A.coord α ∈ K)
    (hBK : j = 2 → ∀ α, coefficients B.coord α ∈ K)
    (hAV : 2 < j → ∀ α, coefficients A.coord α ∈ V)
    (hBV : 2 < j → ∀ α, coefficients B.coord α ∈ V)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V) :
    (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients (A⁻¹ * P * B⁻¹).coord α) ∈ K) ∧
      ∀ α d, 2 ≤ d → d < j →
        basisGradeProjection (b.baseChange ℝ) w d (coefficients (A⁻¹ * P * B⁻¹).coord α) ∈ V := by
  let E := LinearMap.ker (basisGradeProjection (b.baseChange ℝ) w (j - 1) - LinearMap.id)
  have hE : ∀ x ∈ E, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x :=
    fun _ hx => sub_eq_zero.mp hx
  have hgrades := F.polynomial_bchRemove_grades b w hF E (j - 1) hE A.coord P.coord B.coord
    (fun α => sub_eq_zero.mpr (hA α)) (fun α => sub_eq_zero.mpr (hB α))
  have hcurrent (α : σ →₀ ℕ) :
      basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients (A⁻¹ * P * B⁻¹).coord α) =
        basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α) -
          coefficients A.coord α - coefficients B.coord α := by
    have h := congrArg (fun Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients Q α) hgrades.1
    simp only [coefficients_map, map_sub, Finsupp.sub_apply, LinearMap.restrictScalars_apply] at h
    exact h
  have hbelow (d : ℕ) (hd : d < j - 1) (α : σ →₀ ℕ) :
      basisGradeProjection (b.baseChange ℝ) w d (coefficients (A⁻¹ * P * B⁻¹).coord α) =
        basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) := by
    have h := congrArg (fun Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients Q α) (hgrades.2 d hd)
    simp only [coefficients_map, LinearMap.restrictScalars_apply] at h
    exact h
  constructor
  · intro α
    by_cases hj2 : j = 2
    · have h := hcurrent α
      rw [hj2] at h
      change basisGradeProjection (b.baseChange ℝ) w 1 (coefficients (A⁻¹ * P * B⁻¹).coord α) = _ at h
      rw [h]
      exact K.sub_mem (K.sub_mem (hK α) (hAK hj2 α)) (hBK hj2 α)
    · rw [hbelow 1 (by omega)]
      exact hK α
  · intro α d hd hdj
    rcases lt_or_eq_of_le (show d ≤ j - 1 by omega) with hlt | rfl
    · rw [hbelow d hlt]
      exact hlower α d hd hdj
    · rw [hcurrent]
      exact V.sub_mem (V.sub_mem (hlower α (j - 1) hd hdj) (hAV (by omega) α)) (hBV (by omega) α)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ σ K L : Type*} [AddCommGroup K] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hF in
theorem formal_bracket_to_current_layer (hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V H : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (I : K →+ ℝ ⊗[ℚ] L) (hI : ∀ x, basisGradeProjection (b.baseChange ℝ) w 1 (I x) = I x)
    {j : ℕ} (hj : 2 ≤ j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients B.coord α) = coefficients B.coord α)
    (hAhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients A.coord α = 0)
    (hBhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients B.coord α = 0)
    (hAH : j = 2 → ∀ α, coefficients A.coord α ∈ H)
    (hBH : j = 2 → ∀ α, coefficients B.coord α ∈ H)
    (hAV : 2 < j → ∀ α, coefficients A.coord α ∈ V)
    (hBV : 2 < j → ∀ α, coefficients B.coord α ∈ V)
    (hH : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ H)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V)
    (S R : K →+ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k a c : σ → K)
    (ha : j = 2 → ∀ i, I (a i) = coefficients A.coord (Finsupp.single i 1))
    (hc : j = 2 → ∀ i, I (c i) = coefficients B.coord (Finsupp.single i 1))
    (hSR : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R)
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational (fun i => S (k i)))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hS : ∀ x α, coefficients (dualAdjoint A⁻¹ (S x) - monomial 0 (I x)) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hR : ∀ x α, coefficients (dualAdjoint B (R x) - monomial 0 (I x)) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hbracket : ∀ α x, x ∈ H → ⁅coefficients (A⁻¹ * P * B⁻¹).coord α, x⁆ ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    let P' := A⁻¹ * P * B⁻¹
    let S' := (dualAdjointAddEquiv A⁻¹).toAddMonoidHom.comp S
    let R' := (dualAdjointAddEquiv B).toAddMonoidHom.comp R
    let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A) + if j = 2 then S' (a i) else 0
    let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B + if j = 2 then R' (c i) else 0
    let k' := fun i => if j = 2 then k i - a i - c i else k i
    let extra' := fun i => S' (k' i)
    (∀ α, coefficients P'.coord α ∈ U) ∧
      (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P'.coord α) ∈ H) ∧
      (∀ α d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) ∈ V) ∧
      PolynomialLiftSystemMod (V.restrictScalars ℚ) P' S' R' ∧
      PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P' small' rational' extra' ∧
      (∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer j).toSubmodule ∧
        coefficients (rational' i) α ∈ V ⊔ (F.realLayer j).toSubmodule) ∧
      (∀ i α, coefficients (extra' i - VectorPolynomial.map
        ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
          V ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
      ∀ i α, coefficients
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
          (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P'.coord) -
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small' i) -
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational' i)) α ∈ V := by
  intro P' S' R' small' rational' k' extra'
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  have hnewU : ∀ α, coefficients P'.coord α ∈ U :=
    bchRemove_coefficients_mem Uq s A.coord P.coord B.coord hAU hPU hBU
  have hlogs := F.formal_bracket_correction_preserves_log_conditions b w hF V H hj P A B
    hA hB hAH hBH hAV hBV hH hlower
  have hlifts : PolynomialLiftSystemMod (V.restrictScalars ℚ) P' S' R' :=
    PolynomialLiftSystemMod.remove Uq (V.restrictScalars ℚ) hUV P A B hAU S R hSR
  have hderivatives :
      PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P' small' rational' extra' ∧
      (∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer j).toSubmodule ∧
        coefficients (rational' i) α ∈ V ⊔ (F.realLayer j).toSubmodule) ∧
      ∀ i α, coefficients (extra' i - VectorPolynomial.map
        ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
          V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    by_cases hj2 : j = 2
    · subst j
      have h := F.formal_degree_two_reabsorption b w hF hs Uq V hUV hV I hI P A B hAU
        hAhom hBhom S R small rational k a c (ha rfl) (hc rfl) hSR hsystem hsmall hrational hS hR
      simp only [P', S', R', small', rational', k', extra', ite_true]
      exact h.2
    · have h := F.formal_invariant_bracket_derivative_step b w hF hs Uq V hUV hV hj P A B
        hAU hBU (hAV (by omega)) (hBV (by omega)) S k I hI small rational hsystem hsmall hrational hS
      simp only [P', S', small', rational', k', extra', if_neg hj2, add_zero]
      exact h
  refine ⟨hnewU, hlogs.1, hlogs.2, hlifts, hderivatives.1, hderivatives.2.1, hderivatives.2.2, ?_⟩
  exact F.formal_current_layer_derivative_equation_mod b w hF hs U V H hUV hV hj P'
    hnewU hlogs.1 hlogs.2 hbracket small' rational' extra'
    (fun i α => (hderivatives.2.1 i α).2) hderivatives.2.2 hderivatives.1

end Erdos3.NilpotentLieFiltration

end

end OAI
end


