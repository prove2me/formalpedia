-- Prove2me | Definitions.Def_OAIE3v2B184
-- name    : OAIE3v2B184
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:01:41.869198+00:00
-- url     : https://prove2.me/theorems/302259bf-a6a2-446f-8eaa-d6f1b9e77f67
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 187 of 311
-- statement:
--   Definitions bundle 187 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B165`, `OAIE3v2B166`, `OAIE3v2B167`, `OAIE3v2B168` of this split.
--
--   Modules: `Dynamics/FastCoefficientGeneratorBudget.lean`, `Estimates/BoundedFastCoefficientGenerators.lean`, `Estimates/FastCoefficientBlocks.lean`, `Estimates/FastGradedRelativeInvariance.lean`, `Estimates/GradedUnitEvaluation.lean`, `Estimates/TerminalControlledFactorization.lean`, `Estimates/UniformFastCoefficientSpec.lean`, `Geometry/FastCoefficientDerivativeCoordinates.lean`, `Geometry/RealFastCoefficientCoordinates.lean`, `Linear/FullFastHorizontalSpanning.lean`, `Linear/RealFastCoefficientMatrix.lean`, `Linear/RealFastCoefficientQuotientBasis.lean`, `Nilpotent/ControlledBracketToCurrentLayer.lean`, `Polynomial/GradedPolynomialSymbolInverse.lean`, `Polynomial/PolynomialDerivativeDifferences.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B165
import Definitions.Def_OAIE3v2B166
import Definitions.Def_OAIE3v2B167
import Definitions.Def_OAIE3v2B168

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastCoefficientBlocks
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem reducedSquareSnd_kernel_monomial_blocks :
    BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1)
      (F.reducedSquareSndSymbolMap w).ker.toSubmodule :=
  basisBlockInvariant_ker (F.reducedSquareSymbolBasis e ω hF w)
    (F.quotientTopSymbolBasis e ω hF w) (fun z => z.val.1) (fun z => z.val.1)
    (F.reducedSquareSndSymbolMap w).toLinearMap (F.reducedSquareSndSymbolMap_monomial_blocks e ω hF w)

theorem firstCoefficientFastSubmodule_monomial_blocks (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1) U) :
    BasisBlockInvariant (F.firstCoefficientBasis e ω hF w) (fun z => z.val.1)
      (F.firstCoefficientFastSubmodule w hw U) := by
  rw [F.firstCoefficientFastSubmodule_eq_image]
  apply BasisBlockInvariant.map (F.reducedSquareSymbolBasis e ω hF w)
    (F.firstCoefficientBasis e ω hF w) (fun z => z.val.1) (fun z => z.val.1)
    (F.reducedSquareCoefficientMap w) (F.reducedSquareCoefficientMap_monomial_blocks e ω hF w)
  exact hU.inf _ _ _ _ (F.reducedSquareSnd_kernel_monomial_blocks e ω hF w)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedFastCoefficientGenerators
namespace OAI

section

namespace Erdos3

namespace NilpotentLieFiltration

open Module

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
  [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]

theorem exists_bounded_reduced_fast_kernel_generators
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H) :
    ∃ r : ℕ, r ≤ Fintype.card (QuotientTopSymbolIndex s w ω) ∧
      ∃ z : κ → F.squareFiltration.quotientTop.PolynomialSymbol w,
        Submodule.span ℚ (Set.range z) = U ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule ∧
        ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (z i) j)
          (fastKernelGeneratorHeight (Fintype.card (ReducedSquareSymbolIndex s w ω))
            (Fintype.card κ) r H) := by
  have hPv (i : κ) (j : QuotientTopSymbolIndex s w ω) :
      RationalHeightLE ((F.quotientTopSymbolBasis e ω hF w).repr (F.reducedSquareSndSymbolMap w (v i)) j)
        ((Fintype.card (ReducedSquareSymbolIndex s w ω) + 1) *
          H ^ Fintype.card (ReducedSquareSymbolIndex s w ω)) := by
    simpa only [mul_one, LieHom.coe_toLinearMap] using linearMap_coordinate_height
      (F.reducedSquareSymbolBasis e ω hF w) (F.quotientTopSymbolBasis e ω hF w)
      (F.reducedSquareSndSymbolMap w).toLinearMap
      (F.reducedSquareSndSymbolMap_basis_height e ω hF w) (v i) (hv i) j
  have hB : 1 ≤ (Fintype.card (ReducedSquareSymbolIndex s w ω) + 1) *
      H ^ Fintype.card (ReducedSquareSymbolIndex s w ω) := by
    have hp : 0 < H := lt_of_lt_of_le Nat.zero_lt_one hH
    exact Nat.succ_le_of_lt (by positivity)
  have he := exists_bounded_span_kernel_generators
    (F.reducedSquareSymbolBasis e ω hF w) (F.quotientTopSymbolBasis e ω hF w)
    (F.reducedSquareSndSymbolMap w).toLinearMap v hB hv hPv
  simpa only [hspan, fastKernelGeneratorHeight, LieHom.ker_toSubmodule] using he

theorem exists_bounded_fast_coefficient_generators (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H) :
    ∃ r : ℕ, r ≤ Fintype.card (QuotientTopSymbolIndex s w ω) ∧
      ∃ z : κ → F.FirstCoefficientModule w,
        Submodule.span ℚ (Set.range z) = F.firstCoefficientFastSubmodule w hw U ∧
        ∀ i j, RationalHeightLE ((F.firstCoefficientBasis e ω hF w).repr (z i) j)
          (fastCoefficientGeneratorHeight (Fintype.card (ReducedSquareSymbolIndex s w ω))
            (Fintype.card κ) r H) := by
  have he := F.exists_bounded_reduced_fast_kernel_generators e ω hF w U v hspan hH hv
  obtain ⟨r, hr, z, hz, hzh⟩ := he
  exact ⟨r, hr, F.firstCoefficientFastSubmodule_spanning_height e ω hF w hw U z hz hzh⟩

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FastCoefficientGeneratorBudget
namespace OAI

section

namespace Erdos3

namespace NilpotentLieFiltration

open Module

theorem exists_fast_coefficient_generators_exp
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    (hw : ∀ i, 0 < w i) (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 40) ∧
      ∃ z : κ → F.FirstCoefficientModule w,
        Submodule.span ℚ (Set.range z) = F.firstCoefficientFastSubmodule w hw U ∧
        ∀ i j, RationalHeightLE ((F.firstCoefficientBasis e ω hF w).repr (z i) j) H' := by
  have he := F.exists_bounded_fast_coefficient_generators e ω hF w hw U v hspan hH hv
  obtain ⟨r, hr, z, hz, hzh⟩ := he
  refine ⟨_, fastCoefficientGeneratorHeight_pos _ _ _ _ hH, ?_, z, hz, hzh⟩
  exact fastCoefficientGeneratorHeight_le_exp _ _ _ _ hp hn hm
    ((Nat.cast_le.mpr hr).trans hq) hHp

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDerivativeDifferences
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_polynomial_operation_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
          A.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
          CoefficientGrid (b.baseChange ℝ) l A.coord →
          ∀ i : σ, CoefficientGrid (b.baseChange ℝ) m (formalLogDerivative i A)) ∧
        (∀ (A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
          (Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
          A.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
          Q ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
          CoefficientGrid (b.baseChange ℝ) l A.coord →
          CoefficientGrid (b.baseChange ℝ) l Q →
          CoefficientGrid (b.baseChange ℝ) m (dualAdjoint A Q)) := by
  obtain ⟨C, hC, hgrid⟩ := exists_real_adapted_dual_grid s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  classical
  obtain ⟨m, hm, hmp, hlm, hlog, had⟩ := hgrid F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_, ?_⟩
  · intro A hA hAgrid i
    obtain ⟨x, hx⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) A.coord hA
    have hxgrid : F.RealAdaptedCoefficientGrid b ω hF (fun _ : σ => 1) l x := by
      apply (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ l x).mpr
      rwa [hx]
    have hout := (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ m _).mp
      (hlog x hxgrid (Pi.single i 1))
    have hsingle : (fun j => ((Pi.single i 1 : σ → ℤ) j : ℚ)) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i <;> simp [hj]
    rw [hsingle, F.realAdaptedLogDerivative_eq_formal, hx] at hout
    exact hout
  · intro A Q hA hQ hAgrid hQgrid
    obtain ⟨x, hx⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) A.coord hA
    obtain ⟨y, hy⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) Q hQ
    let G : F.RealAdaptedPolynomialGroup (fun _ : σ => 1) := ⟨x⟩
    have hG : F.realFullPolynomialHom (fun _ : σ => 1) G = A := NilpotentLieBCHGroup.ext hx
    have hxgrid : F.RealAdaptedCoefficientGrid b ω hF (fun _ : σ => 1) l x := by
      apply (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ l x).mpr
      rwa [hx]
    have hygrid : F.RealAdaptedCoefficientGrid b ω hF (fun _ : σ => 1) l y := by
      apply (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ l y).mpr
      rwa [hy]
    have hout := (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ m _).mp (had G y hxgrid hygrid)
    rw [F.realAdaptedAdjoint_eq_formal, hG, hy] at hout
    exact hout

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealFastCoefficientCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct Matrix

section Ambient

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem firstCoefficientRealEquiv_basis (i : FirstCoefficientIndex w ω) :
    F.firstCoefficientRealEquiv w ((F.firstCoefficientBasis e ω hF w).baseChange ℝ i) =
      F.realFirstCoefficientBasis e ω hF w i := by
  apply (F.realFirstCoefficientBasis e ω hF w).repr.injective
  ext j
  rw [F.firstCoefficientRealEquiv_coordinates]
  simp only [Basis.repr_self]

end Ambient

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem realFastCoefficientBasis_repr_basis
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis κ ℚ (F.FirstCoefficientModule w ⧸ F.firstCoefficientFastSubmodule w hw U))
    (i : FirstCoefficientIndex w ω) (j : κ) :
    (F.realFastCoefficientBasis w hw U b).repr
        ((F.realFirstCoefficientFastSubmodule w hw U).mkQ
          (F.realFirstCoefficientBasis e ω hF w i)) j =
      (b.repr ((F.firstCoefficientFastSubmodule w hw U).mkQ
        (F.firstCoefficientBasis e ω hF w i)) j : ℝ) := by
  rw [← F.firstCoefficientRealEquiv_basis e ω hF w i]
  exact realTransportedQuotientBasis_repr_basis _ _ _ b i j

theorem realFastCoefficientBasis_matrix
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    [Fintype κ] [DecidableEq κ]
    (b : Basis κ ℚ (F.FirstCoefficientModule w ⧸ F.firstCoefficientFastSubmodule w hw U)) :
    LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w)
        (F.realFastCoefficientBasis w hw U b) (F.realFirstCoefficientFastSubmodule w hw U).mkQ =
      (LinearMap.toMatrix (F.firstCoefficientBasis e ω hF w) b
        (F.firstCoefficientFastSubmodule w hw U).mkQ).map (Rat.castHom ℝ) := by
  ext j i
  simp only [Matrix.map_apply, LinearMap.toMatrix_apply]
  exact F.realFastCoefficientBasis_repr_basis w hw U e ω hF b i j

theorem realFastCoefficientBasis_symm
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    [Fintype κ] [DecidableEq κ]
    (b : Basis κ ℚ (F.FirstCoefficientModule w ⧸ F.firstCoefficientFastSubmodule w hw U))
    (D : Matrix κ (FirstCoefficientIndex w ω) ℚ)
    (S : Matrix (FirstCoefficientIndex w ω) κ ℚ)
    (hD : LinearMap.toMatrix (F.firstCoefficientBasis e ω hF w) b
      (F.firstCoefficientFastSubmodule w hw U).mkQ = D)
    (hDS : D * S = 1) (y : κ → ℝ) :
    (F.realFastCoefficientBasis w hw U b).equivFun.symm y =
      (F.realFirstCoefficientFastSubmodule w hw U).mkQ
        ((F.realFirstCoefficientBasis e ω hF w).equivFun.symm
          (S.map (Rat.castHom ℝ) *ᵥ y)) := by
  apply quotient_basis_representative (F.realFirstCoefficientBasis e ω hF w)
    (F.realFastCoefficientBasis w hw U b) _ (D.map (Rat.castHom ℝ)) _ ?_
    (real_matrix_right_inverse D S hDS) y
  rw [F.realFastCoefficientBasis_matrix, hD]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GradedUnitEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem firstCoefficientGradedPolynomial_normalized_lie (w : σ → ℕ)
    (a : F.adaptedLieSubalgebra w) (p : F.normalizedRelativeSubmodule w) :
    F.firstCoefficientGradedPolynomial e ω hF w
      (F.normalizedFirstCoefficientMap w
        ⟨⁅a, p.val⁆, F.normalizedRelativeSubmodule_lie_mem w a p.val p.property⟩) =
      ⁅F.adaptedGradedPolynomialLie e ω hF w a,
        F.firstCoefficientGradedPolynomial e ω hF w (F.normalizedFirstCoefficientMap w p)⁆ := by
  rw [F.firstCoefficientGradedPolynomial_normalized, F.firstCoefficientGradedPolynomial_normalized]
  have he := F.adaptedShiftedGradedPolynomial_lie e ω hF w a p.val p.property.1
  simp only [F.adaptedShiftedGradedPolynomial_apply] at he
  rw [he]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastGradedRelativeInvariance
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem reducedSquareGradedDifference_basis_height (a : ReducedSquareBasisIndex s ω) (i : ι) :
    RationalHeightLE ((F.associatedGradedBasis e ω hF).repr
      (F.reducedSquareGradedDifference e ω hF (bW a)) i) 1 := by
  rw [F.reducedSquareGradedDifference_basis]
  rcases a with ⟨a, ha⟩
  cases a with
  | inl j =>
    simp only [Sum.elim_inl, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl
  | inr j => exact basis_repr_height_one (F.associatedGradedBasis e ω hF) j.val i

theorem reducedSquareGradedDifference_mem_second (x : F.squareFiltration.quotientTop.AssociatedGraded) :
    F.reducedSquareGradedDifference e ω hF x ∈ F.associatedGradedFiltration.layer 2 := by
  have htop : (⊤ : Submodule ℚ F.squareFiltration.quotientTop.AssociatedGraded) ≤
      (F.associatedGradedFiltration.layer 2).comap (F.reducedSquareGradedDifference e ω hF) := by
    rw [← (bW).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change F.reducedSquareGradedDifference e ω hF (bW a) ∈ F.associatedGradedFiltration.layer 2
    rw [F.reducedSquareGradedDifference_basis]
    rcases a with ⟨a, ha⟩
    cases a with
    | inl i => exact (F.associatedGradedFiltration.layer 2).zero_mem
    | inr i =>
      rw [F.associatedGradedFiltration_layer e ω hF]
      exact Submodule.subset_span ⟨i.val, i.property, rfl⟩
  exact htop (by trivial)

variable (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem fullFastGradedRelative_le_second :
    F.fullFastGradedRelative e ω hF W ≤ F.associatedGradedFiltration.layer 2 := by
  rintro _ ⟨x, _, rfl⟩
  exact F.reducedSquareGradedDifference_mem_second e ω hF x

theorem fullFastGradedRelative_low_projection (j : ℕ) (hj : j < 2)
    (x : F.AssociatedGraded) (hx : x ∈ F.fullFastGradedRelative e ω hF W) :
    basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x = 0 := by
  have hh := F.fullFastGradedRelative_le_second e ω hF W hx
  rw [F.associatedGradedFiltration_layer e ω hF] at hh
  apply (basisCoordinateProjection_eq_zero_iff (F.associatedGradedBasis e ω hF) {i | ω i = j} x).mpr
  apply Submodule.span_mono (Set.image_mono ?_) hh
  intro i hi
  change ω i ≠ j
  change 2 ≤ ω i at hi
  omega

theorem fullFastGradedRelative_graded
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω (F.fullFastGradedRelative e ω hF W) := by
  intro j x hx
  by_cases hj : j = 0
  · subst j
    rw [F.fullFastGradedRelative_low_projection e ω hF W 0 (by decide) x hx]
    exact (F.fullFastGradedRelative e ω hF W).zero_mem
  · obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨basisGradeProjection bW ωW (j - 1) y,
      F.fastGradedRelativeKernel_graded e ω hF W hW (j - 1) y hy, ?_⟩
    have he := F.reducedSquareGradedDifference_gradeProjection e ω hF (j - 1) y
    have hdeg : j - 1 + 1 = j := by omega
    simpa only [hdeg] using he

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FullFastHorizontalSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem gradedHorizontalKernelBasis_span (K : Submodule ℚ (L ⧸ F.layer 2)) (b : Basis κ ℚ K) :
    Submodule.span ℚ (Set.range (fun j =>
      (F.gradedHorizontalKernelBasis e ω hF K b j : F.AssociatedGraded))) =
        F.gradedHorizontalKernel e ω hF K := by
  change Submodule.span ℚ (Set.range ((F.gradedHorizontalKernel e ω hF K).subtype ∘
    F.gradedHorizontalKernelBasis e ω hF K b)) = _
  rw [Set.range_comp, ← Submodule.map_span, Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealFastCoefficientMatrix
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

namespace NilpotentLieFiltration

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
  [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
  [Fintype κ] [DecidableEq κ] (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem realFastCoefficientAdjoint_matrix
    (b : Basis κ ℝ (F.RealFirstCoefficientModule w ⧸
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)))
    (D : Matrix κ (FirstCoefficientIndex w ω) ℚ)
    (S : Matrix (FirstCoefficientIndex w ω) κ ℚ)
    (hD : LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w) b
      (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ =
      D.map (Rat.castHom ℝ))
    (hDS : D * S = 1)
    (g : F.RealAdaptedPolynomialGroup w)
    (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U)) :
    LinearMap.toMatrix b b
        (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap =
      D.map (Rat.castHom ℝ) *
        LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w)
          (F.realFirstCoefficientBasis e ω hF w) (F.realFirstCoefficientAdjoint w g).toLinearMap *
        S.map (Rat.castHom ℝ) := by
  have hsection : LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w) b
      (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ *
      S.map (Rat.castHom ℝ) = 1 := by
    rw [hD]
    exact real_matrix_right_inverse D S hDS
  have h := quotient_action_matrix (F.realFirstCoefficientBasis e ω hF w) b
    (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
    (F.realFirstCoefficientAdjoint w g).toLinearMap
    (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap
    (fun x => (F.realFastCoefficientAdjoint_mk w hw U g hg x).symm)
    (S.map (Rat.castHom ℝ)) hsection
  exact h.trans (congrArg (fun P : Matrix κ (FirstCoefficientIndex w ω) ℝ =>
    P * LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w)
      (F.realFirstCoefficientBasis e ω hF w) (F.realFirstCoefficientAdjoint w g).toLinearMap *
      S.map (Rat.castHom ℝ)) hD)

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealFastCoefficientQuotientBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_fast_coefficient_quotient_projection
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)] (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hd : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ p)
    (hdm : ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 420) ∧
    ∃ Q : Matrix (FirstCoefficientIndex w ω) (FirstCoefficientIndex w ω) ℚ,
      Q * Q = Q ∧
      LinearMap.ker Q.mulVecLin = (F.firstCoefficientFastSubmodule w hw U).map
        (F.firstCoefficientBasis e ω hF w).equivFun.toLinearMap ∧
      (∀ i j, i.val.1 ≠ j.val.1 → Q i j = 0) ∧
      ∀ i j, RationalHeightLE (Q i j) H' := by
  have hg := F.exists_fast_coefficient_generators_exp e ω hF w hw U v hspan hH hv hp hn hm hq hHp
  obtain ⟨K, hK, hKp, z, hz, hzK⟩ := hg
  have hblocks := F.firstCoefficientFastSubmodule_monomial_blocks e ω hF w hw U hU
  have he := exists_submodule_block_quotient_projection (F.firstCoefficientBasis e ω hF w)
    (fun i => i.val.1) (F.firstCoefficientFastSubmodule w hw U) z hz hblocks hK hzK
  obtain ⟨Q, hQQ, hker, hblock, hQ⟩ := he
  have hcost : (imageDefiningHeight
      (Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ)
      (Fintype.card (FirstCoefficientIndex w ω)) K : ℝ) ≤ Real.exp ((p + 2) ^ 420) := by
    have h := imageDefiningHeight_le_exp _ _ K (by positivity : 0 ≤ (p + 2) ^ 40)
      (hdm.trans (le_power_budget hp (by decide : 1 ≤ 40)))
      (hd.trans (le_power_budget hp (by decide : 1 ≤ 40))) hKp
    exact exponential_budget_comp hp (by positivity) 40 10 le_rfl h
  exact ⟨_, imageDefiningHeight_pos _ _ _ hK, hcost, Q, hQQ, hker, hblock, hQ⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem exists_fast_coefficient_quotient_basis
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hd : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ p)
    (hdm : ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card (FirstCoefficientIndex w ω) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℚ (F.FirstCoefficientModule w ⧸ F.firstCoefficientFastSubmodule w hw U),
      ∃ D : Matrix (Fin d) (FirstCoefficientIndex w ω) ℚ,
      ∃ S : Matrix (FirstCoefficientIndex w ω) (Fin d) ℚ,
        LinearMap.toMatrix (F.firstCoefficientBasis e ω hF w) b
          (F.firstCoefficientFastSubmodule w hw U).mkQ = D ∧
        D * S = 1 ∧
        (∀ i j, (rows i).val.1 ≠ j.val.1 → D i j = 0) ∧
        (∀ i j, i.val.1 ≠ (rows j).val.1 → S i j = 0) ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 420) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 420)) ∧
        (∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 2954) ∧
          ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 2954)) ∧
        ∀ y : Fin d → ℚ, b.equivFun.symm y =
          (F.firstCoefficientFastSubmodule w hw U).mkQ
            ((F.firstCoefficientBasis e ω hF w).equivFun.symm (S *ᵥ y)) := by
  classical
  have he := F.exists_fast_coefficient_quotient_projection e ω hF w hw U hU v hspan hH hv
    hp hn hm hq hd hdm hHp
  obtain ⟨K, hK, hKp, Q, _, hkerQ, hQb, hQ⟩ := he
  have hr := exists_block_quotient_rows (fun i : FirstCoefficientIndex w ω => i.val.1) Q hQb hK hQ
  obtain ⟨d, hd', rows, hinj, hsurj, hker, S, hDS, hSb, hS⟩ := hr
  let D := Q.submatrix rows id
  have hkerD : LinearMap.ker D.mulVecLin = (F.firstCoefficientFastSubmodule w hw U).map
      (F.firstCoefficientBasis e ω hF w).equivFun.toLinearMap := hker.trans hkerQ
  let b := submoduleQuotientCoordinateBasis (F.firstCoefficientBasis e ω hF w)
    (F.firstCoefficientFastSubmodule w hw U) D hkerD hsurj
  have hSbudget : (rationalKernelHeight d K : ℝ) ≤ Real.exp ((p + 2) ^ 2954) := by
    have h := rationalKernelHeight_le_budget d K (by positivity : 0 ≤ (p + 2) ^ 420)
      (((Nat.cast_le.mpr hd').trans hd).trans (le_power_budget hp (by decide : 1 ≤ 420))) hKp
    exact exponential_budget_comp hp (by positivity) 420 7 le_rfl h
  refine ⟨d, hd', rows, hinj, b, D, S,
    submoduleQuotientCoordinateBasis_matrix _ _ _ _ _, hDS,
    (fun i j h => hQb (rows i) j h), hSb, ?_, ?_, ?_⟩
  · intro i j
    exact ⟨(Nat.cast_le.mpr (hQ (rows i) j).1).trans hKp,
      (Nat.cast_le.mpr (hQ (rows i) j).2).trans hKp⟩
  · intro i j
    exact ⟨(Nat.cast_le.mpr (hS i j).1).trans hSbudget,
      (Nat.cast_le.mpr (hS i j).2).trans hSbudget⟩
  · intro y
    exact submoduleQuotientCoordinateEquiv_symm _ _ _ _ _ S hDS y

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem exists_real_fast_coefficient_quotient_basis
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hd : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ p)
    (hdm : ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card (FirstCoefficientIndex w ω) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
        F.realFirstCoefficientFastSubmodule w hw U),
      ∃ D : Matrix (Fin d) (FirstCoefficientIndex w ω) ℚ,
      ∃ S : Matrix (FirstCoefficientIndex w ω) (Fin d) ℚ,
        LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w) b
          (F.realFirstCoefficientFastSubmodule w hw U).mkQ = D.map (Rat.castHom ℝ) ∧
        D * S = 1 ∧
        (∀ i j, (rows i).val.1 ≠ j.val.1 → D i j = 0) ∧
        (∀ i j, i.val.1 ≠ (rows j).val.1 → S i j = 0) ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 420) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 420)) ∧
        (∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 2954) ∧
          ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 2954)) ∧
        ∀ y : Fin d → ℝ, b.equivFun.symm y =
          (F.realFirstCoefficientFastSubmodule w hw U).mkQ
            ((F.realFirstCoefficientBasis e ω hF w).equivFun.symm
              (S.map (Rat.castHom ℝ) *ᵥ y)) := by
  have h := F.exists_fast_coefficient_quotient_basis e ω hF w hw U hU v hspan hH hv
    hp hn hm hq hd hdm hHp
  obtain ⟨d, hdim, rows, hinj, b, D, S, hD, hDS, hDb, hSb, hDh, hSh, _⟩ := h
  refine ⟨d, hdim, rows, hinj, F.realFastCoefficientBasis w hw U b, D, S,
    ?_, hDS, hDb, hSb, hDh, hSh, ?_⟩
  · rw [F.realFastCoefficientBasis_matrix, hD]
  · exact F.realFastCoefficientBasis_symm w hw U e ω hF b D S hD hDS

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

def FastCoefficientCoordinateSpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (_hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (_hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) {H : ℕ} (_hH : 1 ≤ H)
    (_hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p),
    ∃ d : ℕ, d ≤ Fintype.card ι * (s + 2) * (Fintype.card σ + 1) ^ (s + 1) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
        F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)),
      ∃ R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w,
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ x, F.FirstCoefficientGrid e ω hF w l x →
          b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) ∈ realDenominatorGrid m) ∧
        (∀ y : Fin d → ℝ, y ∈ realDenominatorGrid l →
          F.FirstCoefficientGrid e ω hF w m (R y)) ∧
        (∀ y : Fin d → ℝ, (F.realFirstCoefficientFastSubmodule w hw
          (F.reducedSquareFastRelativeSubmodule w U)).mkQ (R y) = b.equivFun.symm y) ∧
        (∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
          (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
            |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
              (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) i| ≤
                Real.exp ((p + C) ^ C) * M / monomialScale T (rows i).val.1) ∧
          (∀ y : Fin d → ℝ, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
            F.FirstCoefficientSlowBound e ω hF w T (Real.exp ((p + C) ^ C) * M) (R y))) ∧
        (∀ i j, (rows j).val.1 ≠ i.val.1 →
          b.repr ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ
              (F.realFirstCoefficientBasis e ω hF w i)) j = 0) ∧
        ∀ (g : F.RealAdaptedPolynomialGroup w)
          (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
            realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
          (a c : Fin d), ω (rows a).val.2 ≤ ω (rows c).val.2 →
            LinearMap.toMatrix b b (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
              (1 : Matrix (Fin d) (Fin d) ℝ) a c

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

theorem realAdaptedGradedPolynomialHom_coordinate
    (g : F.RealAdaptedPolynomialGroup w) (α : σ →₀ ℕ) (i : ι) :
    ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr
      (coefficients (F.realAdaptedGradedPolynomialHom e ω hF w g).coord α) i =
        if ω i = Finsupp.weight w α then
          (e.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap w g.coord) α) i else 0 := by
  change ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr
    (coefficients (F.realAdaptedGradedPolynomialLie e ω hF w g.coord) α) i = _
  rw [F.realAdaptedGradedPolynomialLie_coefficient, F.real_gradedPieceProjection_coordinate]

theorem realAdaptedGradedPolynomialHom_bound
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealAdaptedPolynomialGroup w) (hg : F.RealAdaptedCoefficientBound e ω hF w T M g.coord) :
    CoefficientBound ((F.associatedGradedBasis e ω hF).baseChange ℝ) T M
      (F.realAdaptedGradedPolynomialHom e ω hF w g).coord := by
  have hfull := (F.realAdaptedCoefficientBound_iff_formal e ω hF w T hT hM g.coord).mp hg
  intro α i
  rw [F.realAdaptedGradedPolynomialHom_coordinate]
  split_ifs
  · exact hfull α i
  · rw [abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

end General

end Erdos3.NilpotentLieFiltration

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

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype κ] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {K : Submodule ℚ L}

include hF in
theorem exists_controlled_bracket_to_current_layer (hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (e : Basis κ ℚ K)
    (hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {j H m : ℕ} (hj : 2 ≤ j) (hH : 1 ≤ H) (hm : 0 < m)
    (he : ∀ i z, RationalHeightLE (b.repr (e z : L) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hambient : (Fintype.card μ : ℝ) ≤ p)
    (hkernel : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hmp : (m : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients B.coord α) = coefficients B.coord α)
    (hAhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients A.coord α = 0)
    (hBhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients B.coord α = 0)
    (hAK : j = 2 → ∀ α, coefficients A.coord α ∈ K.baseChange ℝ)
    (hBK : j = 2 → ∀ α, coefficients B.coord α ∈ K.baseChange ℝ)
    (hAV : 2 < j → ∀ α, coefficients A.coord α ∈ V)
    (hBV : 2 < j → ∀ α, coefficients B.coord α ∈ V)
    (hPK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K.baseChange ℝ)
    (hlower : ∀ α d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : σ → κ → ℝ)
    (hSR : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R)
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational
      (fun i => basisPolynomialLift (Pi.basisFun ℝ κ) S (k i)))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hS : ∀ z α, coefficients (dualAdjoint A⁻¹ (S z) - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] (e z : L))) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hR : ∀ z α, coefficients (dualAdjoint B (R z) - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] (e z : L))) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hbracket : ∀ z α, ⁅coefficients (A⁻¹ * P * B⁻¹).coord α, (1 : ℝ) ⊗ₜ[ℚ] (e z : L)⁆ ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hAbound : CoefficientBound (b.baseChange ℝ) T (Real.exp p) A.coord)
    (hBgrid : CoefficientGrid (b.baseChange ℝ) m B.coord)
    (hSbound : ∀ z, CoefficientBound (b.baseChange ℝ) T (Real.exp p) (dualAdjoint A⁻¹ (S z)))
    (hRgrid : ∀ z, CoefficientGrid (b.baseChange ℝ) m (dualAdjoint B (R z)))
    (hsmallBound : ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp p / T i)
      (dualAdjoint A⁻¹ (small i - formalLogDerivative i A)))
    (hrationalGrid : ∀ i, CoefficientGrid (b.baseChange ℝ) m
      (dualAdjoint B (rational i) - formalLogDerivative i B))
    (hSshift : ∀ z, dualAdjoint A⁻¹ (S z) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hRshift : ∀ z, dualAdjoint B (R z) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hsmallShift : ∀ i, dualAdjoint A⁻¹ (small i - formalLogDerivative i A) ∈
      shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hrationalShift : ∀ i, dualAdjoint B (rational i) - formalLogDerivative i B ∈
      shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) :
    let S₀ := basisPolynomialLift (Pi.basisFun ℝ κ) S
    let R₀ := basisPolynomialLift (Pi.basisFun ℝ κ) R
    let S' := (dualAdjointAddEquiv A⁻¹).toAddMonoidHom.comp S₀.toAddMonoidHom
    let R' := (dualAdjointAddEquiv B).toAddMonoidHom.comp R₀.toAddMonoidHom
    ∃ (a c : σ → κ → ℝ) (n : ℕ),
      0 < n ∧ (n : ℝ) ≤ Real.exp (bracketTransitionBudget p) ∧
      let P' := A⁻¹ * P * B⁻¹
      let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A) + if j = 2 then S' (a i) else 0
      let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B + if j = 2 then R' (c i) else 0
      let k' := fun i => if j = 2 then k i - a i - c i else k i
      let extra' := fun i => S' (k' i)
      (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P'.coord α) ∈ K.baseChange ℝ) ∧
        (∀ α d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) ∈ V) ∧
        PolynomialLiftSystemMod (V.restrictScalars ℚ) P' S' R' ∧
        PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P' small' rational' extra' ∧
        (∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer j).toSubmodule ∧
          coefficients (rational' i) α ∈ V ⊔ (F.realLayer j).toSubmodule) ∧
        (∀ i α, coefficients (extra' i - VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
            V ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ i α, coefficients
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
            (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P'.coord) -
            VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small' i) -
            VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational' i)) α ∈ V) ∧
        (∀ α x, x ∈ K.baseChange ℝ → ⁅coefficients P'.coord α, x⁆ ∈
          V ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp (bracketTransitionBudget p) / T i) (small' i) ∧
          CoefficientGrid (b.baseChange ℝ) n (rational' i) ∧
          small' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          rational' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) ∧
        ∀ z, CoefficientBound (b.baseChange ℝ) T (Real.exp (bracketTransitionBudget p)) (dualAdjoint A⁻¹ (S z)) ∧
          CoefficientGrid (b.baseChange ℝ) n (dualAdjoint B (R z)) := by
  classical
  intro S₀ R₀ S' R'
  let I := bracketSystemLift e
  have hchoice : ∃ (a c : σ → κ → ℝ) (d : ℕ), 0 < d ∧
      (d : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      (j = 2 → ∀ i, I (a i) = coefficients A.coord (Finsupp.single i 1) ∧
        I (c i) = coefficients B.coord (Finsupp.single i 1)) ∧
      ∀ i, ‖a i‖ ≤ Real.exp ((p + 2) ^ 8) / T i ∧ c i ∈ realDenominatorGrid d := by
    by_cases hj2 : j = 2
    · obtain ⟨a, c, d, hd, hdp, hdirs⟩ := exists_uniform_polynomial_kernel_directions b e hH hm he hp
        (Real.exp_nonneg p) hambient hkernel hHp hmp le_rfl A.coord B.coord (hAK hj2) (hBK hj2)
        T hT hAbound hBgrid
      exact ⟨a, c, d, hd, hdp, fun _ i => ⟨(hdirs i).1, (hdirs i).2.1⟩,
        fun i => ⟨(hdirs i).2.2.1, (hdirs i).2.2.2⟩⟩
    · refine ⟨0, 0, 1, by decide, ?_, fun h => (hj2 h).elim, fun i => ?_⟩
      · simpa only [Nat.cast_one] using Real.one_le_exp (by positivity : 0 ≤ (p + 2) ^ 9)
      · constructor
        · simp only [Pi.zero_apply, norm_zero]
          exact div_nonneg (Real.exp_nonneg _) (hT i).le
        · exact ⟨0, by ext z; simp⟩
  obtain ⟨a, c, d, hd, hdp, hdirs, hcoordinates⟩ := hchoice
  let n := m * (m * d)
  have hn : 0 < n := Nat.mul_pos hm (Nat.mul_pos hm hd)
  have hmdiv : m ∣ n := dvd_mul_right m (m * d)
  obtain ⟨hbase, habsorb, hnbound⟩ := bracket_transition_budget_bounds hp (Fintype.card κ) m d hkernel hmp hdp
  refine ⟨a, c, n, hn, hnbound, ?_⟩
  intro P' small' rational' k' extra'
  have hI : ∀ x, basisGradeProjection (b.baseChange ℝ) w 1 (I x) = I x :=
    fun x => hK _ (bracketSystemLift_mem e x)
  have hSR₀ : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S₀ R₀ :=
    hSR.extend_basis (Pi.basisFun ℝ κ) V P S R
  have hSall : ∀ x α, coefficients (dualAdjoint A⁻¹ (S₀ x) - monomial 0 (I x)) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    apply basisPolynomialLift_adjoint_residual (Pi.basisFun ℝ κ) A⁻¹ S I
      (V ⊔ (F.realLayer (j + 1)).toSubmodule)
    intro z α
    simpa only [I, Pi.basisFun_apply, bracketSystemLift_single] using hS z α
  have hRall : ∀ x α, coefficients (dualAdjoint B (R₀ x) - monomial 0 (I x)) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    apply basisPolynomialLift_adjoint_residual (Pi.basisFun ℝ κ) B R I
      (V ⊔ (F.realLayer (j + 1)).toSubmodule)
    intro z α
    simpa only [I, Pi.basisFun_apply, bracketSystemLift_single] using hR z α
  have hbracketall : ∀ α x, x ∈ K.baseChange ℝ → ⁅coefficients P'.coord α, x⁆ ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    intro α x hx
    obtain ⟨v, rfl⟩ := exists_subspace_basis_coordinates e x hx
    apply real_bracket_mem_of_basis (Pi.basisFun ℝ κ) I
      (V ⊔ (F.realLayer (j + 1)).toSubmodule) (coefficients P'.coord α) _ v
    intro z
    simpa only [I, Pi.basisFun_apply, bracketSystemLift_single] using hbracket z α
  have hgeometry := F.formal_bracket_to_current_layer b w hF hs U V (K.baseChange ℝ) hUV hV
    I.toAddMonoidHom hI hj P A B hPU hAU hBU hA hB hAhom hBhom hAK hBK hAV hBV hPK hlower
    S₀.toAddMonoidHom R₀.toAddMonoidHom small rational k a c
    (fun h i => (hdirs h i).1) (fun h i => (hdirs h i).2)
    hSR₀ hsystem hsmall hrational hSall hRall hbracketall
  refine ⟨hgeometry.1, hgeometry.2.1, hgeometry.2.2.1, hgeometry.2.2.2.1,
    hgeometry.2.2.2.2.1, hgeometry.2.2.2.2.2.1, hgeometry.2.2.2.2.2.2.1,
    hgeometry.2.2.2.2.2.2.2, hbracketall, ?_, ?_⟩
  · intro i
    by_cases hj2 : j = 2
    · have ha : ‖(Pi.basisFun ℝ κ).equivFun (a i)‖ ≤ Real.exp ((p + 2) ^ 8) / T i := by
        rw [Pi.basisFun_equivFun]
        exact (hcoordinates i).1
      have hc : (Pi.basisFun ℝ κ).equivFun (c i) ∈ realDenominatorGrid d := by
        rw [Pi.basisFun_equivFun]
        exact (hcoordinates i).2
      have hbound := basisPolynomialLift_reabsorption_bound (Pi.basisFun ℝ κ)
        (fun z => dualAdjoint A⁻¹ (S z)) (b.baseChange ℝ) T hT (Real.exp p) (Real.exp p)
        (Real.exp ((p + 2) ^ 8)) (T i) (Real.exp_nonneg p) hSbound _ (hsmallBound i) (a i) ha
      have hgrid := basisPolynomialLift_reabsorption_grid (Pi.basisFun ℝ κ)
        (fun z => dualAdjoint B (R z)) (b.baseChange ℝ) d m m hRgrid _ (hrationalGrid i) (c i) hc
      have hSsh := basisPolynomialLift_shiftedGraded (Pi.basisFun ℝ κ)
        (fun z => dualAdjoint A⁻¹ (S z)) (b.baseChange ℝ) w (fun _ : σ => 1) 1 hSshift (a i)
      have hRsh := basisPolynomialLift_shiftedGraded (Pi.basisFun ℝ κ)
        (fun z => dualAdjoint B (R z)) (b.baseChange ℝ) w (fun _ : σ => 1) 1 hRshift (c i)
      rw [basisPolynomialLift_adjoint (hnil := F.realification.lowerCentralSeries_eq_bot)
        (Pi.basisFun ℝ κ) A⁻¹ S] at hbound hSsh
      rw [basisPolynomialLift_adjoint (hnil := F.realification.lowerCentralSeries_eq_bot)
        (Pi.basisFun ℝ κ) B R] at hgrid hRsh
      simp only [small', rational', if_pos hj2]
      exact ⟨hbound.mono _ T hT (div_le_div_of_nonneg_right habsorb (hT i).le), hgrid,
        (shiftedGradedPolynomialSubmodule _ _ _ _).add_mem (hsmallShift i) hSsh,
        (shiftedGradedPolynomialSubmodule _ _ _ _).add_mem (hrationalShift i) hRsh⟩
    · simp only [small', rational', if_neg hj2, add_zero]
      exact ⟨(hsmallBound i).mono _ T hT (div_le_div_of_nonneg_right hbase (hT i).le),
        fun α => realDenominatorGrid_subset_of_dvd hm hmdiv (hrationalGrid i α),
        hsmallShift i, hrationalShift i⟩
  · intro z
    exact ⟨(hSbound z).mono _ T hT hbase,
      fun α => realDenominatorGrid_subset_of_dvd hm hmdiv (hRgrid z α)⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TerminalControlledFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "bG" => F.associatedGradedBasis e ω hF
local notation "FG" => F.associatedGradedFiltration
local notation "U" => F.fullFastGradedDiagonal W
local notation "V" => F.fullFastGradedRelative e ω hF W

def FastTerminalStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hsp : (s + 1 : ℕ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (k : ℕ) (_hk : (k : ℝ) ≤ p) (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis (Fin k) ℚ K)
    (_hKb : ∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (bK j).val i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ V, basisGradeProjection bG ω (s + 1) x = x → η x = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (X : (FG).FormalInductionState bG ω (realificationLieSubalgebra U) V
      (F.gradedHorizontalKernel e ω hF K) (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 p),
    F.FastTerminalFactorization e ω hF W η T X.P ((p + C) ^ C)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFastCoefficientSpec
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

def UniformFastCoefficientCoordinateSpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (_hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (_hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) {H : ℕ} (_hH : 1 ≤ H)
    (_hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p),
    ∃ d : ℕ, d ≤ Fintype.card ι * (s + 2) * (Fintype.card σ + 1) ^ (s + 1) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
        F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)),
      ∃ R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w,
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ l x, F.FirstCoefficientGrid e ω hF w l x →
          b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) ∈ realDenominatorGrid (m * l)) ∧
        (∀ l (y : Fin d → ℝ), y ∈ realDenominatorGrid l →
          F.FirstCoefficientGrid e ω hF w (m * l) (R y)) ∧
        (∀ y : Fin d → ℝ, (F.realFirstCoefficientFastSubmodule w hw
          (F.reducedSquareFastRelativeSubmodule w U)).mkQ (R y) = b.equivFun.symm y) ∧
        (∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
          (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
            |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
              (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) i| ≤
                Real.exp ((p + C) ^ C) * M / monomialScale T (rows i).val.1) ∧
          (∀ y : Fin d → ℝ, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
            F.FirstCoefficientSlowBound e ω hF w T (Real.exp ((p + C) ^ C) * M) (R y))) ∧
        (∀ i j, (rows j).val.1 ≠ i.val.1 →
          b.repr ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ
              (F.realFirstCoefficientBasis e ω hF w i)) j = 0) ∧
        ∀ (g : F.RealAdaptedPolynomialGroup w)
          (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
            realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
          (a c : Fin d), ω (rows a).val.2 ≤ ω (rows c).val.2 →
            LinearMap.toMatrix b b (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
              (1 : Matrix (Fin d) (Fin d) ℝ) a c

end Erdos3.NilpotentLieFiltration

end

end OAI
end


