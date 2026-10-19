-- Prove2me | Definitions.Def_OAIE3v2B143
-- name    : OAIE3v2B143
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:03:06.915734+00:00
-- url     : https://prove2.me/theorems/81137050-3709-4969-afae-27beb7e89efd
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 145 of 311
-- statement:
--   Definitions bundle 145 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B128`, `OAIE3v2B129`, `OAIE3v2B131`, `OAIE3v2B132` of this split.
--
--   Modules: `Dynamics/SharedFreeFullOrbitBudget.lean`, `Estimates/FixedObservableCorrelation.lean`, `Estimates/FreeWeightedModelBounds.lean`, `Estimates/ReducedSquareSymbol.lean`, `Estimates/RefilteredPointwiseSplitting.lean`, `Estimates/SharedFreeComparisonLift.lean`, `Estimates/SquarefreeLayerBases.lean`, `Estimates/SymbolFastMembership.lean`, `Fourier/HomogeneousGradedProjectionFrequency.lean`, `Fourier/JoinedFrequencyQuotientInjectivity.lean`, `Fourier/ProductFrequencyKernel.lean`, `Geometry/StepOneCoordinateMetric.lean`, `Lattices/NativeIntegerAffinePullbackHom.lean`, `Lattices/SharedFreeAffineBudget.lean`, `Lattices/SharedFreeAffineOrbitFamily.lean`, `Linear/AssociatedGradedBasisIndependence.lean`, `Linear/SquareBasisGeometry.lean`, `Linear/TripleProductBasisBounds.lean`, `Nilpotent/CyclicNiltestApproximation.lean`, `Nilpotent/NativeNiltestPartition.lean`, `Nilpotent/RankBracketFactorizationMonotone.lean`, `Polynomial/PositivePolynomialLayerBases.lean`, `Polynomial/PositivePolynomialVectorOrbit.lean`, `Polynomial/QuantitativeOuterPolynomialProducts.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B128
import Definitions.Def_OAIE3v2B129
import Definitions.Def_OAIE3v2B131
import Definitions.Def_OAIE3v2B132

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AssociatedGradedBasisIndependence
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem gradedRefiltrationLayer_eq_inf_comap (U : LieSubalgebra ℚ F.AssociatedGraded) (j : ℕ) :
    F.gradedRefiltrationLayer U j =
      F.layer j ⊓ U.toSubmodule.comap (F.gradedPieceProjection b ω hlayers j) := by
  ext v
  rw [F.mem_gradedRefiltrationLayer, Submodule.mem_inf, Submodule.mem_comap]
  constructor
  · rintro ⟨hv, hU⟩
    exact ⟨hv, (F.gradedPieceProjection_eq_pieceMap b ω hlayers j ⟨v, hv⟩).symm ▸ hU⟩
  · rintro ⟨hv, hU⟩
    exact ⟨hv, F.gradedPieceProjection_eq_pieceMap b ω hlayers j ⟨v, hv⟩ ▸ hU⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.HomogeneousGradedProjectionFrequency
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem gradedFrequency_projection (η : L →ₗ[ℚ] ℚ) (j : ℕ) (x : L) :
    F.gradedFrequency b ω hF η (F.gradedPieceProjection b ω hF j x) =
      η (basisGradeProjection b ω j x) := by
  change η (b.repr.symm ((F.associatedGradedBasis b ω hF).repr
    ((F.associatedGradedBasis b ω hF).repr.symm (b.repr (basisGradeProjection b ω j x))))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

theorem gradedFrequency_top_piece (η : L →ₗ[ℚ] ℚ) (x : F.layer s) :
    F.gradedFrequency b ω hF η (F.associatedGradedPieceMap s x) = η x := by
  rw [← F.gradedPieceProjection_eq_pieceMap b ω hF, F.gradedFrequency_projection,
    F.basisGradeProjection_top b ω hF x]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolFastMembership
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem ControlledSymbolFactorization.mono {η : L →ₗ[ℚ] ℚ} {T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q : ℝ}
    (h : F.ControlledSymbolFactorization b ω hF η T X p) (hpq : p ≤ q)
    (hT : ∀ i, 0 < T i) : F.ControlledSymbolFactorization b ω hF η T X q := by
  obtain ⟨m, E, P, R, W, v, hm, hmp, hprod, hE, hR, hv, hW, hh, hη, hP⟩ := h
  exact ⟨m, E, P, R, W, v, hm, hmp.trans (Real.exp_le_exp.mpr hpq), hprod,
    F.symbolSlowBound_mono b ω hF (fun _ => 1) T hT (Real.exp_le_exp.mpr hpq) E hE,
    hR, hv, hW, (fun i j => (hh i j).trans hpq), hη, hP⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def ControlledSymbolCompositionSpec (s C : ℕ) : Prop :=
  ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i) (η : L →ₗ[ℚ] ℚ)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (A X R : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (_hA : F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp p) A)
    (_hR : F.SymbolRationalGrid b ω hF (fun _ => 1) l R)
    (_hX : F.ControlledSymbolFactorization b ω hF η T X p),
    F.ControlledSymbolFactorization b ω hF η T (A * X * R) ((p + C) ^ C)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem SymbolFactorizationIn.mono {T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q : ℝ} {l : ℕ}
    {W : LieSubalgebra ℚ F.AssociatedGraded}
    (h : F.SymbolFactorizationIn b ω hF T X p l W) (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.SymbolFactorizationIn b ω hF T X q l W := by
  obtain ⟨E, P, R, hprod, hE, hR, hP⟩ := h
  exact ⟨E, P, R, hprod,
    F.symbolSlowBound_mono b ω hF (fun _ => 1) T hT (Real.exp_le_exp.mpr hpq) E hE, hR, hP⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedSquareSymbol
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def reducedSquareGradedDiagonalPiece (j : ℕ) :
    F.layer j →ₗ[ℚ] F.squareFiltration.quotientTop.AssociatedGraded :=
  F.squareFiltration.quotientTopGradedMap.toLinearMap.comp (F.squareGradedDiagonalPiece j)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquareBasisGeometry
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev ReducedSquareSymbolIndex (s : ℕ) (w : σ → ℕ) (ω : ι → ℕ) :=
  SymbolBasisIndex w (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω i.val)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem polynomialRationalGrid_iff_formal {ι : Type*} (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (w : σ → ℕ) (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.PolynomialRationalGrid b w l g ↔
      CoefficientGrid (b.baseChange ℝ) l (F.realification.adaptedFullPolynomialHom w g).coord := by
  constructor
  · rintro ⟨a, ha⟩ α
    exact ⟨fun i => a (α, i), funext (fun i => congrFun ha (α, i))⟩
  · intro h
    choose a ha using h
    exact ⟨fun z => a z.1 z.2, funext (fun z => congrFun (ha z.1) z.2)⟩

theorem polynomialSlowBound_iff_formal {ι : Type*} (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (w : σ → ℕ) (T : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.PolynomialSlowBound b w T M g ↔
      CoefficientBound (b.baseChange ℝ) T M (F.realification.adaptedFullPolynomialHom w g).coord :=
  Iff.rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeWeightedModelBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bounded_free_weighted_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (w : X → ℕ)
      (hw : ∀ x, 0 < w x) (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeWeightedNilpotentLieAlgebra X s w) : ℝ) ≤ (p + C) ^ C ∧
      ∃ (b : Basis (Fin (finrank ℚ (FreeWeightedNilpotentLieAlgebra X s w))) ℚ
          (FreeWeightedNilpotentLieAlgebra X s w))
        (u : Fin (finrank ℚ (FreeWeightedNilpotentLieAlgebra X s w)) → ℕ),
        Monotone u ∧ (∀ j, u j ≤ s + 1) ∧ IsCentralLieBasis b ∧
        (∀ d, (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).layer d =
          Submodule.span ℚ (b '' {j | d ≤ u j})) ∧
        (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C) ∧
        (∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
          rationalLogHeight (b.repr (FreeWeightedNilpotentLieAlgebra.mk X s w x) i) ≤ (p + C) ^ C) ∧
        ∃ e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ
            (FreeNilpotentLieAlgebra X s),
          (∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
          (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
          ∃ S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s)))
              (Fin (finrank ℚ (FreeWeightedNilpotentLieAlgebra X s w))) ℚ,
            LinearMap.toMatrix e b (FreeWeightedNilpotentLieAlgebra.mk X s w).toLinearMap * S = 1 ∧
            ∀ i j, rationalLogHeight (S i j) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hquotient⟩ := exists_bounded_free_weighted_quotient s
  let B₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let P₀ := (B₀ + 2) ^ 4
  let Q₀ := P₀ + (P₀ + 3) ^ 5
  let R₀ := (Q₀ + 2) ^ 4 + (P₀ + 3) ^ 11 + B₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R₀ + (R₀ + 3) ^ 5)
  refine ⟨C, hC, ?_⟩
  intro X _ w hw p hp hX
  classical
  let B := (p + a) ^ a
  let P := (B + 2) ^ 4
  let Q := P + (P + 3) ^ 5
  let R := (Q + 2) ^ 4 + (P + 3) ^ 11 + B
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hBP : B ≤ P := le_power_budget hB (by norm_num : 1 ≤ (4 : ℕ))
  have hPQ : P ≤ Q := le_add_of_nonneg_right (by positivity)
  have hIQ : (P + 3) ^ 5 ≤ Q := le_add_of_nonneg_left hP
  have hBR : B ≤ R := le_add_of_nonneg_left (by positivity)
  have hR : 0 ≤ R := hB.trans hBR
  have hprojectionR : (Q + 2) ^ 4 ≤ R :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (P + 3) ^ 11)).trans
      (le_add_of_nonneg_right hB)
  have hstructureR : (P + 3) ^ 11 ≤ R :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (Q + 2) ^ 4)).trans
      (le_add_of_nonneg_right hB)
  have hsum : R + (R + 3) ^ 5 ≤ (p + C) ^ C := by
    simpa [B₀, P₀, Q₀, R₀, B, P, Q, R, Polynomial.eval₂_pow] using hbudget p hp
  have hRC : R ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (R + 3) ^ 5)).trans hsum
  have hSC : (R + 3) ^ 5 ≤ (p + C) ^ C := (le_add_of_nonneg_left hR).trans hsum
  obtain ⟨hdim, e, he, hgen, d, hd, hdimq, q, D, _, hmatrix, _, hD, _, hc⟩ :=
    hquotient X w p hp hX
  have hdimq' : (finrank ℚ (FreeWeightedNilpotentLieAlgebra X s w) : ℝ) ≤ B := by
    simpa only [finrank_eq_card_basis q, Fintype.card_fin] using hdimq
  have htree (x : FreeNilpotentLieAlgebra X s)
      (hx : x ∈ FreeNilpotentLieAlgebra.treeGenerators X s) (j : Fin d) :
      rationalLogHeight (q.repr (FreeWeightedNilpotentLieAlgebra.mk X s w x) j) ≤ P := by
    apply linearMap_coordinate_logHeight e q
      (FreeWeightedNilpotentLieAlgebra.mk X s w).toLinearMap hB
      (by simpa only [Fintype.card_fin] using hdim) ?_ x (hgen x hx)
    intro i j
    have h := hD j i
    rw [← hmatrix, LinearMap.toMatrix_apply] at h
    exact h
  let F := FreeWeightedNilpotentLieAlgebra.filtration X s w hw
  let v (i : Fin (s + 1)) := FreeWeightedNilpotentLieAlgebra.layerFamily X s w hw (i.val + 1)
  have hv (i : Fin (s + 1)) (x : FreeWeightedNilpotentLieAlgebra.layerGenerators X s w (i.val + 1))
      (j : Fin d) : rationalLogHeight (q.repr (v i x : FreeWeightedNilpotentLieAlgebra X s w) j) ≤ P := by
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp x.property
    change rationalLogHeight (q.repr x.val j) ≤ P
    rw [← hxy]
    exact htree y (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w (i.val + 1) hy) j
  obtain ⟨b, u, hu, hub, hcentral, hlayer, _, hinverse, hstructure⟩ :=
    F.exists_bounded_sorted_adapted_basis_logHeight q v
      (fun i => FreeWeightedNilpotentLieAlgebra.layerFamily_span X s w hw (i.val + 1))
      hP (by simpa only [Fintype.card_fin] using hdimq.trans hBP) hv
      (fun i j k => (hc i j k).trans hBP)
  have htree' (x : FreeNilpotentLieAlgebra X s)
      (hx : x ∈ FreeNilpotentLieAlgebra.treeGenerators X s) (j) :
      rationalLogHeight (b.repr (FreeWeightedNilpotentLieAlgebra.mk X s w x) j) ≤ R := by
    apply le_trans _ hprojectionR
    exact linearMap_coordinate_logHeight q b (LinearMap.id) hQ
      (by simpa only [Fintype.card_fin] using hdimq.trans (hBP.trans hPQ))
      (fun i k => (hinverse i k).trans hIQ)
      (FreeWeightedNilpotentLieAlgebra.mk X s w x) (fun i => (htree x hx i).trans hPQ) j
  let A := LinearMap.toMatrix e b (FreeWeightedNilpotentLieAlgebra.mk X s w).toLinearMap
  have hA (i j) : rationalLogHeight (A i j) ≤ R := by
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact htree' (e j) (he j) i
  obtain ⟨S, hAS, hS⟩ := exists_rational_section_exp_height A
    (basisMatrix_surjective e b (FreeWeightedNilpotentLieAlgebra.mk X s w).toLinearMap
      (FreeWeightedNilpotentLieAlgebra.mk_surjective X s w))
    (one_le_ceil_exp R) (fun i j => rationalHeightLE_ceil_exp (hA i j))
    (hR.trans (le_add_of_nonneg_right zero_le_one))
    (by simpa only [Fintype.card_fin] using (hdimq'.trans
      (hBR.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))))
    (ceil_exp_le_exp_add_one hR)
  refine ⟨hdimq'.trans (hBR.trans hRC), b, u, hu, hub, hcentral, hlayer,
    fun i j k => (hstructure i j k).trans (hstructureR.trans hRC),
    fun x hx j => (htree' x hx j).trans hRC, e, he, hdim.trans (hBR.trans hRC), S, hAS, ?_⟩
  intro i j
  apply le_trans ((rationalLogHeight_le_iff _ _).mpr (hS i j))
  simpa only [show R + 1 + 2 = R + 3 by ring] using hSC

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefilteredPointwiseSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (U : LieSubalgebra ℚ F.AssociatedGraded)

theorem realGradedRefiltrationLayer_le (j : ℕ) :
    F.realGradedRefiltrationLayer U j ≤ (F.realLayer j).toSubmodule :=
  Submodule.baseChange_mono ℝ (F.gradedRefiltrationLayer_le U j)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

theorem associatedGradedPieceMap_grade_fixed (j : ℕ) (x : F.layer j) :
    basisGradeProjection (F.associatedGradedBasis b w hF) w j (F.associatedGradedPieceMap j x) =
      F.associatedGradedPieceMap j x := by
  rw [← F.gradedPieceProjection_eq_pieceMap b w hF j x]
  apply (F.associatedGradedBasis b w hF).repr.injective
  ext i
  simp only [basisGradeProjection_repr, F.gradedPieceProjection_coordinate]
  split_ifs <;> rfl

theorem frequency_zero_on_refiltered_top (U : LieSubalgebra ℚ F.AssociatedGraded)
    (eta : L →ₗ[ℚ] ℚ)
    (hzero : ∀ x ∈ U, basisGradeProjection (F.associatedGradedBasis b w hF) w s x = x →
      F.gradedFrequency b w hF eta x = 0) :
    ∀ x ∈ F.gradedRefiltrationLayer U s, eta x = 0 := by
  intro x hx
  obtain ⟨hxs, hxU⟩ := (F.mem_gradedRefiltrationLayer U s x).mp hx
  rw [← F.gradedFrequency_top_piece b w hF eta ⟨x, hxs⟩]
  exact hzero _ hxU (F.associatedGradedPieceMap_grade_fixed b w hF s ⟨x, hxs⟩)

theorem real_frequency_zero_on_refiltered_top (U : LieSubalgebra ℚ F.AssociatedGraded)
    (eta : L →ₗ[ℚ] ℚ)
    (hzero : ∀ x ∈ U, basisGradeProjection (F.associatedGradedBasis b w hF) w s x = x →
      F.gradedFrequency b w hF eta x = 0) :
    ∀ x ∈ F.realGradedRefiltrationLayer U s, realifyFunctional eta x = 0 := by
  have hle : F.gradedRefiltrationLayer U s ≤ LinearMap.ker eta :=
    F.frequency_zero_on_refiltered_top b w hF U eta hzero
  intro x hx
  exact (mem_realified_frequency_kernel_iff eta x).mp (Submodule.baseChange_mono ℝ hle hx)

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeLayerBases
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module
open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*} [∀ a, Fintype (κ a)]
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))

theorem squarefreeSupportedFinBasis_height (P : SquarefreeIndex ι → Prop) (j k) :
    RationalHeightLE ((F.squarefreeBasis π b).repr (F.squarefreeSupportedFinBasis π b P j).val k) 1 := by
  classical
  unfold squarefreeSupportedFinBasis
  rw [Basis.reindex_apply, F.squarefreeSupportedBasis_coe]
  exact basis_repr_height_one _ _ _

noncomputable def squarefreeMultidegreeBasis (c : ι → ℕ) :
    Basis (Fin (finrank ℚ (F.squarefreeMultidegreeLayer π c))) ℚ (F.squarefreeMultidegreeLayer π c) :=
  F.squarefreeSupportedFinBasis π b (fun a => c ≤ fun i => a.val i)

theorem squarefreeMultidegreeBasis_height (c : ι → ℕ) (j k) :
    RationalHeightLE ((F.squarefreeBasis π b).repr (F.squarefreeMultidegreeBasis π b c j).val k) 1 :=
  F.squarefreeSupportedFinBasis_height π b _ j k

theorem squarefreeDegreeBasis_height (n : ℕ) (j k) :
    RationalHeightLE ((F.squarefreeBasis π b).repr (F.squarefreeDegreeBasis π b n j).val k) 1 :=
  F.squarefreeSupportedFinBasis_height π b _ j k

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.StepOneCoordinateMetric
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module Manifold NilpotentLieBCHGroup
open scoped Manifold ContDiff Bundle NNReal ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  (F : NilpotentLieFiltration L 1) (e : Basis ι ℝ L)

theorem stepOne_coordinates_lipschitz :
    letI := rightMetricSpace (hnil := F.lowerCentralSeries_eq_bot) e
    LipschitzWith 1 (basisHomeomorph (hnil := F.lowerCentralSeries_eq_bot) e) := by
  let := basisChartedSpace (hnil := F.lowerCentralSeries_eq_bot) e
  let := rightRiemannianBundle (hnil := F.lowerCentralSeries_eq_bot) e
  let := rightMetricSpace (hnil := F.lowerCentralSeries_eq_bot) e
  intro x y
  let r : ℝ≥0 := ⟨dist x y + 1, by positivity⟩
  have hnear : (1 : ℝ≥0∞) * riemannianEDist 𝓘(ℝ, ι → ℝ) x y < r := by
    change (1 : ℝ≥0∞) * edist x y < r
    rw [one_mul, edist_dist]
    rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal (dist x y) < ENNReal.ofReal (dist x y + 1)
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  have hbound : ∀ z : F.Group, basisHomeomorph e z ∈ Metric.closedBall (basisHomeomorph e x) r →
      ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) z,
        ‖tangentModelVector (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (basisHomeomorph e) z v)‖ₑ ≤
          (1 : ℝ≥0∞) * ‖v‖ₑ := by
    intro z _ v
    simpa only [one_mul, ofReal_norm] using
      ENNReal.ofReal_le_ofReal (F.stepOne_norm_mfderiv_coordinates_le e z v)
  exact coordinate_edist_le_of_riemannianEDist_lt (C := 1) (r := r) (by norm_num)
    (contMDiff_basisHomeomorph e 1) x y hbound hnear

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ProductFrequencyKernel
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

namespace RationalFilteredNilmanifold

variable {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem piFrequency_basis (eta : ∀ i, L i →ₗ[ℚ] ℚ)
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
    piFrequency eta ((pi D).basis k) = eta z.1 ((D z.1).basis z.2) := by
  classical
  change piFrequency eta (productFinBasis D k) = _
  rw [productFinBasis, Basis.reindex_apply]
  generalize hz : (Fintype.equivFin (Σ i, Fin (d i))).symm k = z
  rcases z with ⟨i, j⟩
  rw [Pi.basis_apply, piFrequency_single]

theorem piFrequency_logHeight (eta : ∀ i, L i →ₗ[ℚ] ℚ) {p : ℝ}
    (hheight : ∀ i j, rationalLogHeight (eta i ((D i).basis j)) ≤ p)
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    rationalLogHeight (piFrequency eta ((pi D).basis k)) ≤ p := by
  rw [piFrequency_basis D]
  exact hheight _ _

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.TripleProductBasisBounds
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productFinBasis_repr (x : ∀ i, L i) (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
    (pi D).basis.repr x k = (D z.1).basis.repr (x z.1) z.2 := by
  change (productFinBasis D).repr x k = _
  rw [productFinBasis, Basis.repr_reindex_apply, Pi.basis_repr]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productProjection_smul (i : ι) (g : (pi D).RealGroup) (x : (pi D).Space) :
    productProjection D i (g • x) = productProjectionHom D i g • productProjection D i x :=
  cosetMap_smul _ _ _ _ g x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

namespace RationalFilteredNilmanifold

namespace Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem unit_interval_evalCyclic (T : D.Niltest w) (hT : T.UnitIntervalValued)
    (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (T.evalCyclic N x).im = 0 ∧ 0 ≤ (T.evalCyclic N x).re ∧ (T.evalCyclic N x).re ≤ 1 := hT _

end Niltest
end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedObservableCorrelation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_frozen_parameter_fiber (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p ε : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → 0 < ε → 1 / ε ≤ Real.exp p →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (H : Finset G) (a u : G → D.RealGroup), H.Nonempty →
      (∀ h ∈ H, ∀ i, |(D.basis.baseChange ℝ).repr (a h).coord i| ≤ Real.exp ((p + 2) ^ k)) →
      (∀ h ∈ H, ∀ i, |(D.basis.baseChange ℝ).repr (u h).coord i| ≤ Real.exp ((p + 2) ^ k)) →
      (∀ h ∈ H, (D.basis.baseChange ℝ).equivFun (u h).coord ∈ realDenominatorGrid q) →
      ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∃ a₀ u₀ : D.RealGroup,
          (∀ i, |(D.basis.baseChange ℝ).repr a₀.coord i| ≤ Real.exp ((p + 2) ^ k)) ∧
          (∀ i, |(D.basis.baseChange ℝ).repr u₀.coord i| ≤ Real.exp ((p + 2) ^ k)) ∧
          (D.basis.baseChange ℝ).equivFun u₀.coord ∈ realDenominatorGrid q ∧
          letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            (D.basis.baseChange ℝ)
          ∀ h ∈ H', dist (a h) a₀ ≤ ε ∧ u h = u₀ := by
  obtain ⟨b, _, hcover⟩ := exists_native_group_parameter_cover s k
  let A := k + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C b) ^ b +
      (Polynomial.X + Polynomial.C (A + 5)) ^ (A + 5))
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D p ε hp hD hε hεp q hq hqp H a u hH ha hu hugrid
  classical
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let B : ℝ≥0 := ⟨Real.exp ((p + 2) ^ k), (Real.exp_pos _).le⟩
  have hB : 1 ≤ B := by
    change (1 : ℝ) ≤ Real.exp ((p + 2) ^ k)
    exact Real.one_le_exp (pow_nonneg (by linarith) _)
  obtain ⟨n, hn, hnp, centers, hnet⟩ := hcover D B hp hD hB le_rfl hε hεp
  have hac (h : {h // h ∈ H}) : a h ∈ coordinateBox
      (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) B :=
    ha h h.property
  choose index hindex using fun h : {h // h ∈ H} => hnet ⟨a h, hac h⟩
  let label (h : G) : Fin n := if hh : h ∈ H then index ⟨h, hh⟩ else ⟨0, hn⟩
  have hlabel (h : G) (hh : h ∈ H) : dist (a h) (centers (label h)).val ≤ ε := by
    simpa only [label, dif_pos hh, Subtype.dist_eq] using hindex ⟨h, hh⟩
  let S : Set (Fin d → ℝ) := {v | (∀ i, |v i| ≤ B) ∧ v ∈ realDenominatorGrid q}
  have hA : 2 ≤ A := by dsimp [A]; omega
  have hpow : (p + 2) ^ k ≤ (p + A) ^ A := by
    have hAr : (2 : ℝ) ≤ A := by exact_mod_cast hA
    exact (pow_le_pow_left₀ (by linarith) (by linarith) k).trans
      (pow_le_pow_right₀ (by linarith) (by dsimp [A]; omega))
  obtain ⟨hS, hScard⟩ := finite_card_real_grid_box S q
    ⌈(q : ℝ) * Real.exp ((p + A) ^ A)⌉₊ hq (fun _ hv => hv.2)
    (fun v hv i => (hv.1 i).trans (Real.exp_le_exp.mpr hpow)) (Nat.le_ceil _)
  have hScount : (S.ncard : ℝ) ≤ Real.exp ((p + (A + 5 : ℕ)) ^ (A + 5)) := by
    apply (Nat.cast_le.mpr (by simpa only [Fintype.card_fin] using hScard)).trans
    simpa only [Nat.cast_add, Nat.cast_ofNat] using grid_box_count_le_exp A d q hA hp hD.1 hqp
  let colors : Set (Fin n × (Fin d → ℝ)) := Set.univ ×ˢ S
  have hcolors : colors.Finite := (Set.toFinite (Set.univ : Set (Fin n))).prod hS
  let code (h : G) : Fin n × (Fin d → ℝ) :=
    (label h, (D.basis.baseChange ℝ).equivFun (u h).coord)
  have hcode (h : G) (hh : h ∈ H) : code h ∈ colors :=
    ⟨Set.mem_univ _, hu h hh, hugrid h hh⟩
  have hcost : (p + b) ^ b + (p + (A + 5 : ℕ)) ^ (A + 5) ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have hcount : (colors.ncard : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [colors, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul hnp hScount (Nat.cast_nonneg _) (Real.exp_pos _).le).trans
      (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hcost)
  obtain ⟨⟨j, z⟩, _, H', hsub, hnonempty, hconstant, hdense⟩ :=
    exists_exponential_constant_fiber H hH code colors hcolors hcode hcount
  obtain ⟨h₀, hh₀⟩ := hnonempty
  refine ⟨H', hsub, ⟨h₀, hh₀⟩, hdense, (centers j).val, u h₀,
    (centers j).property, hu h₀ (hsub hh₀), hugrid h₀ (hsub hh₀), ?_⟩
  intro h hh
  have hi : label h = j := congrArg Prod.fst (hconstant h hh)
  refine ⟨by simpa only [hi] using hlabel h (hsub hh), ?_⟩
  apply NilpotentLieBCHGroup.ext
  apply (D.basis.baseChange ℝ).equivFun.injective
  exact (congrArg Prod.snd (hconstant h hh)).trans (congrArg Prod.snd (hconstant h₀ hh₀)).symm

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem norm_eval_le {σ : Type*} {w : σ → ℕ} {s : ℕ} {p : ℝ} {f : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion w s p f) (x : σ → ℤ) : ‖f x‖ ≤ Real.exp (2 * p) := by
  rw [E.eval x]
  calc
    ‖∑ i, E.coefficient i * (E.test i).eval x‖ ≤
        ∑ i, ‖E.coefficient i * (E.test i).eval x‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖E.coefficient i‖ * Real.exp p := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((E.test i).eval_budget (E.complexity i) x) (norm_nonneg _)
    _ = (∑ i, ‖E.coefficient i‖) * Real.exp p := (Finset.sum_mul _ _ _).symm
    _ ≤ Real.exp p * Real.exp p := mul_le_mul_of_nonneg_right E.cost (Real.exp_nonneg _)
    _ = Real.exp (2 * p) := by rw [← Real.exp_add, two_mul]

end Erdos3.NativeIntegerExpansion

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeNiltestPartition
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_native_niltest_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ) {p ρ : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → 0 < ρ →
      1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∀ g : D.filtration.realification.PolynomialOrbit w,
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ A : Fin n → D.Niltest w,
            (∀ i, (A i).orbit = g) ∧
            (∀ i, (A i).UnitIntervalValued) ∧
            (∀ i, (A i).ComplexityLE ((p + C) ^ C)) ∧
            (∀ z, ∑ i, ((A i).observable z).re = 1) ∧
            (letI := D.metricSpace
             ∀ i x y, 0 < ((A i).observable x).re → 0 < ((A i).observable y).re → dist x y ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_native_positive_partition s a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C B) ^ B + 2)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ d D w p ρ hp hD hρ hρinv g
  obtain ⟨n, hn, hnb, K, hK, ψ, hψ, hsum, hLip, hdiam⟩ := hpartition D hp hD hρ hρinv
  have hcost : p + (p + B) ^ B + 2 ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have hB0 : 0 ≤ (p + B) ^ B := pow_nonneg (by positivity) _
  have hBC : (p + B) ^ B ≤ (p + C) ^ C := by linarith
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hlog : Real.log (3 + (K : ℝ)) ≤ (p + C) ^ C := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have h1 : 1 ≤ Real.exp ((p + B) ^ B) := Real.one_le_exp hB0
    have h2 : (4 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    have hle : 3 + (K : ℝ) ≤ Real.exp ((p + B) ^ B + 2) := by
      rw [Real.exp_add]
      nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg ((p + B) ^ B))]
    exact hle.trans (Real.exp_le_exp.mpr (by linarith))
  let A : Fin n → D.Niltest w := fun i =>
    D.sectionNiltest g (fun z (_ : Unit) => ψ i z) (fun z _ => hψ i z) K (fun _ => hLip i) (some ())
  refine ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr hBC), A, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro i
    exact D.sectionNiltest_unit_interval g _ _ K _ (some ())
  · intro i
    exact D.sectionNiltest_complexityLE g _ _ K _ (some ()) (hD.mono D hpC) hlog
  · intro z
    change ∑ i, ψ i z = 1
    exact hsum z
  · let := D.metricSpace
    intro i x y hx hy
    exact hdiam i x y hx hy

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PositivePolynomialLayerBases
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))

noncomputable def positivePolynomialSupport (S : Set (σ →₀ ℕ)) : Submodule ℚ F.positivePolynomialAlgebra :=
  (coefficientSupport S).comap F.positivePolynomialAlgebra.incl.toLinearMap

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))
  (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J)

theorem positivePolynomialDownsetIdeal_eq_support :
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ).toSubmodule =
      F.positivePolynomialSupport Jᶜ := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators

variable {α σ L : Type*} [Fintype α] [DecidableEq α] [Fintype σ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ} {bound : σ → ℕ}
  (F : MultidegreeLieFiltration σ L s bound)
  (J : α → Set (σ →₀ ℕ)) (hJ : ∀ a, IsLowerSet (J a))

noncomputable def positivePolynomialQuotientProduct :=
  NilpotentLieFiltration.pi (fun a => (F.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary)

noncomputable def positivePolynomialQuotientProductMap :
    F.positivePolynomialAlgebra →ₗ⁅ℚ⁆
      (∀ a, F.positivePolynomialAlgebra ⧸ restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a)) :=
  liePiMap (fun a => lieQuotientMap (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a)))

noncomputable def positivePolynomialQuotientProductRealMap :
    F.positivePolynomialMultidegree.ordinary.realification.Group →*
      (F.positivePolynomialQuotientProduct J hJ).realification.Group :=
  realificationMap (hnil := F.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
    (hM := (F.positivePolynomialQuotientProduct J hJ).lowerCentralSeries_eq_bot)
    (F.positivePolynomialQuotientProductMap J hJ)

noncomputable def positivePolynomialQuotientProductLattice
    (Γ : Subgroup F.positivePolynomialMultidegree.ordinary.Group) :
    Subgroup (F.positivePolynomialQuotientProduct J hJ).Group :=
  piBCHSubgroup (fun a => (F.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary)
    (fun a => Γ.map (F.positivePolynomialMultidegree.ordinary.quotientStepHom
      (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a))
      (by rw [F.positivePolynomialMultidegree.ordinary.terminal]; exact bot_le)))

theorem positivePolynomialQuotientProductRealMap_component
    (g : F.positivePolynomialMultidegree.ordinary.realification.Group) (a : α) :
    realBCHPiEquiv (fun a => (F.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary)
      (F.positivePolynomialQuotientProductRealMap J hJ g) a =
        F.positivePolynomialMultidegree.ordinary.realQuotientStepHom
          (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a))
          (by rw [F.positivePolynomialMultidegree.ordinary.terminal]; exact bot_le) g := by
  apply NilpotentLieBCHGroup.ext
  exact realification_liePiEval_liePiMap _ g.coord a

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PositivePolynomialVectorOrbit
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialMonomial (a : σ →₀ ℕ) (ha : a ≠ 0) :
    F.layer (fun i => a i) →ₗ[ℚ] F.positivePolynomialAlgebra where
  toFun x := ⟨monomial a x.val, F.monomial_mem_adaptedSubmodule a x.property, by
    classical
    simp [ha]⟩
  map_add' x y := by
    apply Subtype.ext
    change monomial a (x.val + y.val) = monomial a x.val + monomial a y.val
    simp [monomial, TensorProduct.tmul_add]
  map_smul' c x := by
    apply Subtype.ext
    change monomial a (c • x.val) = c • monomial a x.val
    simp [monomial]

theorem positivePolynomialMonomial_mem_layer (a : σ →₀ ℕ) (ha : a ≠ 0)
    (x : F.layer (fun i => a i)) :
    F.positivePolynomialMonomial a ha x ∈ F.positivePolynomialMultidegreeLayer (fun i => a i) := by
  change monomial a x.val ∈ coefficientSupport {b : σ →₀ ℕ | (fun i => a i) ≤ fun i => b i}
  apply monomial_mem_coefficientSupport
  exact fun i => le_rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realPositivePolynomialMap_monomial (a : σ →₀ ℕ) (ha : a ≠ 0)
    (x : ℝ ⊗[ℚ] F.layer (fun i => a i)) :
    F.realPositivePolynomialMap ((F.positivePolynomialMonomial a ha).baseChange ℝ x) =
      monomial a ((F.layer (fun i => a i)).subtype.baseChange ℝ x) := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => first | (simp; done) | (simp [monomial]; done) | exact (map_zero _).symm
  | tmul r y =>
    apply coefficients.injective
    ext b
    rw [LinearMap.baseChange_tmul, F.realPositivePolynomialMap_coefficient_tmul]
    change r ⊗ₜ[ℚ] coefficients (monomial a y.val) b =
      coefficients (monomial a (r ⊗ₜ[ℚ] y.val)) b
    by_cases hab : a = b
    · subst b
      simp
    · simp [hab]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    simp [monomial, TensorProduct.tmul_add]

theorem realPositivePolynomialMonomial_mem_layer (a : σ →₀ ℕ) (ha : a ≠ 0)
    (x : ℝ ⊗[ℚ] F.layer (fun i => a i)) :
    (F.positivePolynomialMonomial a ha).baseChange ℝ x ∈
      (F.positivePolynomialMultidegreeLayer (fun i => a i)).baseChange ℝ := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    rw [LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem r (F.positivePolynomialMonomial_mem_layer a ha y)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem exists_realPositivePolynomial_component
    (p : F.realification.positivePolynomialAlgebra) (a : σ →₀ ℕ) :
    ∃ x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra,
      F.realPositivePolynomialTensor x = F.realification.positivePolynomialComponent a p ∧
      x ∈ (F.positivePolynomialMultidegreeLayer (fun i => a i)).baseChange ℝ := by
  classical
  by_cases ha : a = 0
  · subst a
    refine ⟨0, ?_, Submodule.zero_mem _⟩
    rw [map_zero]
    exact ((F.realification.positivePolynomialComponent_eq_zero 0 p).mpr p.property.2).symm
  · let Q := F.layer (fun i => a i)
    let c : Q.baseChange ℝ := ⟨coefficients p.val a, p.property.1 a⟩
    let y : ℝ ⊗[ℚ] Q := (realificationSubmoduleEquiv Q).symm c
    have hy : Q.subtype.baseChange ℝ y = c.val :=
      congrArg Subtype.val ((realificationSubmoduleEquiv Q).apply_symm_apply c)
    refine ⟨(F.positivePolynomialMonomial a ha).baseChange ℝ y, ?_,
      F.realPositivePolynomialMonomial_mem_layer a ha y⟩
    apply Subtype.ext
    change F.realPositivePolynomialMap ((F.positivePolynomialMonomial a ha).baseChange ℝ y) =
      monomial a (coefficients p.val a)
    rw [F.realPositivePolynomialMap_monomial, hy]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realPositivePolynomialTensor_mem_layer (a : σ → ℕ)
    {x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra}
    (hx : x ∈ (F.positivePolynomialMultidegreeLayer a).baseChange ℝ) :
    F.realPositivePolynomialTensor x ∈ F.realification.positivePolynomialMultidegreeLayer a := by
  let U := F.positivePolynomialMultidegreeLayer a
  have hbase (z : ℝ ⊗[ℚ] U) :
      F.realPositivePolynomialTensor (U.subtype.baseChange ℝ z) ∈
        F.realification.positivePolynomialMultidegreeLayer a := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r p =>
      intro b hb
      change coefficients (F.realPositivePolynomialMap
        (U.subtype.baseChange ℝ (r ⊗ₜ[ℚ] p))) b = 0
      rw [LinearMap.baseChange_tmul, F.realPositivePolynomialMap_coefficient_tmul]
      have hz : coefficients p.val.val b = 0 := p.property b hb
      change r ⊗ₜ[ℚ] coefficients p.val.val b = 0
      rw [hz, TensorProduct.tmul_zero]
    | add z w hz hw =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hz hw
  let z := (realificationSubmoduleEquiv U).symm ⟨x, hx⟩
  have hz : U.subtype.baseChange ℝ z = x :=
    congrArg Subtype.val ((realificationSubmoduleEquiv U).apply_symm_apply ⟨x, hx⟩)
  exact hz ▸ hbase z

theorem exists_realPositivePolynomial_preimage_layer (a : σ → ℕ)
    (p : F.realification.positivePolynomialAlgebra)
    (hp : p ∈ F.realification.positivePolynomialMultidegreeLayer a) :
    ∃ x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra,
      x ∈ (F.positivePolynomialMultidegreeLayer a).baseChange ℝ ∧
      F.realPositivePolynomialTensor x = p := by
  classical
  choose y hy hylayer using F.exists_realPositivePolynomial_component p
  refine ⟨∑ b ∈ (coefficients p.val).support, y b, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro b hb
    have hab : a ≤ fun i => b i := by
      by_contra h
      have hz : coefficients p.val b = 0 := hp b h
      exact (Finsupp.mem_support_iff.mp hb) hz
    exact Submodule.baseChange_mono ℝ (F.positivePolynomialMultidegreeLayer_antitone hab) (hylayer b)
  · rw [map_sum]
    simp_rw [hy]
    exact F.realification.sum_positivePolynomialComponent p

theorem realPositivePolynomialTensor_surjective : Function.Surjective F.realPositivePolynomialTensor := by
  intro p
  obtain ⟨x, _, hx⟩ := F.exists_realPositivePolynomial_preimage_layer 0 p (by
    rw [F.realification.positivePolynomialMultidegreeLayer_zero]
    trivial)
  exact ⟨x, hx⟩

noncomputable def realPositivePolynomialEquiv :
    (ℝ ⊗[ℚ] F.positivePolynomialAlgebra) ≃ₗ⁅ℚ⁆ F.realification.positivePolynomialAlgebra :=
  LieEquiv.ofBijective F.realPositivePolynomialTensor
    ⟨F.realPositivePolynomialTensor_injective, F.realPositivePolynomialTensor_surjective⟩

theorem realPositivePolynomialEquiv_mem_layer (a : σ → ℕ)
    (x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra) :
    F.realPositivePolynomialEquiv x ∈ F.realification.positivePolynomialMultidegreeLayer a ↔
      x ∈ (F.positivePolynomialMultidegreeLayer a).baseChange ℝ := by
  constructor
  · intro hx
    obtain ⟨y, hy, heq⟩ := F.exists_realPositivePolynomial_preimage_layer a _ hx
    have hxy : y = x := F.realPositivePolynomialTensor_injective heq
    exact hxy ▸ hy
  · exact F.realPositivePolynomialTensor_mem_layer a

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def realPositivePolynomialOrbitTransport
    (g : F.realification.positivePolynomialMultidegree.PolynomialOrbit) :
    F.positivePolynomialMultidegree.realification.PolynomialOrbit :=
  F.positivePolynomialMultidegree.realification.polynomialOrbitOfLog
    (VectorPolynomial.map F.realPositivePolynomialEquiv.symm.toLinearMap
      (PolynomialOrbit.log F.realification.positivePolynomialMultidegree g)) (by
        intro a
        rw [coefficients_map]
        change F.realPositivePolynomialEquiv.symm _ ∈
          (F.positivePolynomialMultidegreeLayer (fun i => a i)).baseChange ℝ
        apply (F.realPositivePolynomialEquiv_mem_layer (fun i => a i) _).mp
        rw [F.realPositivePolynomialEquiv.apply_symm_apply]
        exact PolynomialOrbit.adapted F.realification.positivePolynomialMultidegree g a)

theorem realPositivePolynomialOrbitTransport_eval
    (g : F.realification.positivePolynomialMultidegree.PolynomialOrbit) (x : σ → ℤ) :
    NilpotentLieBCHGroup.mapOfSteps F.realPositivePolynomialEquiv.toLieHom
        (F.positivePolynomialMultidegree.realification.polynomialOrbitEval x
          (F.realPositivePolynomialOrbitTransport g)) =
      F.realification.positivePolynomialMultidegree.polynomialOrbitEval x g := by
  apply NilpotentLieBCHGroup.ext
  change F.realPositivePolynomialEquiv
      (eval (fun i => (x i : ℚ)) (VectorPolynomial.map F.realPositivePolynomialEquiv.symm.toLinearMap
        (PolynomialOrbit.log F.realification.positivePolynomialMultidegree g))) = _
  rw [eval_map]
  exact F.realPositivePolynomialEquiv.apply_symm_apply _

theorem realPositivePolynomialOrbitTransport_zero
    (g : F.realification.positivePolynomialMultidegree.PolynomialOrbit)
    (hg : F.realification.positivePolynomialMultidegree.polynomialOrbitEval 0 g = 1) :
    F.positivePolynomialMultidegree.realification.polynomialOrbitEval 0
      (F.realPositivePolynomialOrbitTransport g) = 1 := by
  apply NilpotentLieBCHGroup.mapOfSteps_injective F.realPositivePolynomialEquiv.toLieHom
    F.realPositivePolynomialEquiv.injective
  rw [map_one, F.realPositivePolynomialOrbitTransport_eval, hg]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem exists_realPositivePolynomial_orbit (g : F.realification.PolynomialOrbit)
    (hg : F.realification.polynomialOrbitEval 0 g = 1) :
    ∃ h : F.positivePolynomialMultidegree.realification.PolynomialOrbit,
      F.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
      ∀ x, NilpotentLieBCHGroup.realificationMap
          (hnil := F.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
          (hM := F.ordinary.lowerCentralSeries_eq_bot) F.positivePolynomialEvaluation
          (F.positivePolynomialMultidegree.realification.polynomialOrbitEval x h) =
        F.realification.polynomialOrbitEval x g := by
  obtain ⟨q, hqzero, hq⟩ := F.realification.exists_positivePolynomial_orbit g hg
  refine ⟨F.realPositivePolynomialOrbitTransport q,
    F.realPositivePolynomialOrbitTransport_zero q hqzero, ?_⟩
  intro x
  apply NilpotentLieBCHGroup.ext
  have htransport := congrArg NilpotentLieBCHGroup.coord
    (F.realPositivePolynomialOrbitTransport_eval q x)
  have hprojection := congrArg NilpotentLieBCHGroup.coord (hq x)
  calc
    _ = F.realification.positivePolynomialEvaluation (F.realPositivePolynomialEquiv
        (F.positivePolynomialMultidegree.realification.polynomialOrbitEval x
          (F.realPositivePolynomialOrbitTransport q)).coord) :=
      (F.realPositivePolynomialEvaluation_commute _).symm
    _ = F.realification.positivePolynomialEvaluation
        (F.realification.positivePolynomialMultidegree.polynomialOrbitEval x q).coord :=
      congrArg F.realification.positivePolynomialEvaluation htransport
    _ = _ := hprojection

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J)

noncomputable def positivePolynomialDownsetOrbit
    (g : F.positivePolynomialMultidegree.realification.PolynomialOrbit) :
    (F.positivePolynomialDownsetQuotient J hJ).realification.PolynomialOrbit :=
  F.positivePolynomialMultidegree.realQuotientMultidegreeOrbit
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ) g

theorem positivePolynomialDownsetOrbit_eval
    (g : F.positivePolynomialMultidegree.realification.PolynomialOrbit) (x : σ → ℤ) :
    (F.positivePolynomialDownsetQuotient J hJ).realification.polynomialOrbitEval x
      (F.positivePolynomialDownsetOrbit J hJ g) =
        F.positivePolynomialMultidegree.realQuotientMultidegreeMap
          (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ)
          (F.positivePolynomialMultidegree.realification.polynomialOrbitEval x g) :=
  F.positivePolynomialMultidegree.realQuotientMultidegreeOrbit_eval _ g x

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RankBracketFactorizationMonotone
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

namespace NilpotentLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem real_refiltered_lieTreeEval_mem (U : LieSubalgebra ℚ F.AssociatedGraded)
    (d : I → ℕ) (v : I → ℝ ⊗[ℚ] L) (hv : ∀ i, v i ∈ F.realGradedRefiltrationLayer U (d i))
    (a : FreeMagma I) : lieTreeEval v a ∈ F.realGradedRefiltrationLayer U (lieTreeWeight d a) := by
  induction a using FreeMagma.rec with
  | of i => exact hv i
  | mul a b ha hb => exact F.realGradedRefiltrationLayer_lie_mem U ha hb

end NilpotentLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SharedFreeAffineBudget
namespace OAI

section

namespace Erdos3

open CyclicCrootSisask

theorem exists_sharedFreeAffineSelection_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → ∀ n : ℕ, (n : ℝ) ≤ 4 * (s : ℝ) * p →
      affineRecoveryLogLoss ((p + 2) ^ 3 + 2 * p) n ≤ (p + C) ^ C ∧
      2 + quarticBogolyubovConstant *
        (roundedModelLogBudget ((p + 2) ^ 3 + 2 * p) n + 1) ^ 4 ≤ (p + C) ^ C := by
  let C₀ := ⌈max quarticBogolyubovProgressionConstant quarticBogolyubovConstant⌉₊
  have hC₀ : quarticBogolyubovProgressionConstant ≤ (C₀ : ℝ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  have hC₁ : quarticBogolyubovConstant ≤ (C₀ : ℝ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  let PB : Polynomial ℕ := (Polynomial.X + 2) ^ 3 + 2 * Polynomial.X
  let PD : Polynomial ℕ := 4 * Polynomial.C s * Polynomial.X
  let PZ : Polynomial ℕ := 736 + 96 * PB + 1504 * PD
  let T : Polynomial ℕ := Polynomial.C C₀ * (PZ + 1) ^ 8 +
    (PB + 13 * PD) + 16 * (PD + 3) + (2 + Polynomial.C C₀ * (PZ + 1) ^ 4)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro p hp n hn
  let B := (p + 2) ^ 3 + 2 * p
  let D := 4 * (s : ℝ) * p
  let U := 736 + 96 * B + 1504 * D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hz : roundedModelLogBudget B n ≤ U := by
    unfold roundedModelLogBudget
    rw [max_eq_left hB]
    dsimp [U]
    gcongr
  have hz0 : 0 ≤ roundedModelLogBudget B n + 1 := by
    linarith [roundedModelLogBudget_nonneg B n]
  have hcost : affineRecoveryLogLoss B n ≤
      (C₀ : ℝ) * (U + 1) ^ 8 + (B + 13 * D) + 16 * (D + 3) := by
    unfold affineRecoveryLogLoss
    gcongr
  have hrank : 2 + quarticBogolyubovConstant * (roundedModelLogBudget B n + 1) ^ 4 ≤
      2 + (C₀ : ℝ) * (U + 1) ^ 4 := by gcongr
  have heval : T.eval₂ (Nat.castRingHom ℝ) p =
      (C₀ : ℝ) * (U + 1) ^ 8 + (B + 13 * D) + 16 * (D + 3) +
        (2 + (C₀ : ℝ) * (U + 1) ^ 4) := by
    simp [T, PZ, PD, PB, B, D, U, Polynomial.eval₂_pow]
  have htotal := hbound p hp
  rw [heval] at htotal
  have hcost0 : 0 ≤ (C₀ : ℝ) * (U + 1) ^ 8 + (B + 13 * D) + 16 * (D + 3) := by
    positivity
  have hrank0 : 0 ≤ 2 + (C₀ : ℝ) * (U + 1) ^ 4 := by positivity
  constructor <;> linarith

theorem exists_sharedFreeAffineUniform_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      ∀ n : ℕ, (n : ℝ) ≤ 4 * (s : ℝ) * p →
        sharedFreeRecoveryThreshold s q p ≤ (p + C) ^ C ∧
        affineRecoveryLogLoss ((p + 2) ^ 3 + 2 * p) n ≤ (p + C) ^ C ∧
        2 + quarticBogolyubovConstant *
          (roundedModelLogBudget ((p + 2) ^ 3 + 2 * p) n + 1) ^ 4 ≤ (p + C) ^ C := by
  obtain ⟨C₁, hC₁, hthreshold⟩ := exists_sharedFreeRecoveryThreshold_bound s
  obtain ⟨C₂, hC₂, hselection⟩ := exists_sharedFreeAffineSelection_bound s
  let C := C₁ + C₂
  have hC : 2 ≤ C := by dsimp [C]; omega
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp n hn
  have hshift (c : ℕ) (hc : c ≤ C) : (p + c) ^ c ≤ (p + C) ^ C := by
    have hcR : (c : ℝ) ≤ C := by exact_mod_cast hc
    have hCR : (2 : ℝ) ≤ C := by exact_mod_cast hC
    exact (pow_le_pow_left₀ (by positivity) (by linarith : p + c ≤ p + C) c).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ p + C) hc)
  have h₁ := hshift C₁ (by dsimp [C]; omega)
  have h₂ := hshift C₂ (by dsimp [C]; omega)
  have hs := hselection p hp n hn
  exact ⟨(hthreshold q p hq hqp hp).trans h₁, hs.1.trans h₂, hs.2.trans h₂⟩

noncomputable def sharedFreeAffineConstant (s : ℕ) : ℕ :=
  (exists_sharedFreeAffineUniform_bound s).choose +
    (exists_sharedFreeProperAffineSelection_bound s).choose

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeComparisonLift
namespace OAI

section

namespace Erdos3

noncomputable def sharedFreeCommonCorrectionBudget (s : ℕ) (q p : ℝ) : ℝ :=
  let Λ := (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
  let t := (q + p + Λ) + 1
  (t + 2) ^ 3 + (t + 2) ^ 36 + Λ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SharedFreeAffineOrbitFamily
namespace OAI

section

namespace Erdos3

noncomputable def sharedFreePetalLiftInput (s : ℕ) (q p : ℝ) : ℝ :=
  4 * p + fourRefinementAnnihilatorBudget (q + coefficientFourHeightBudget p) +
    (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s

noncomputable def sharedFreePetalLiftBudget (s : ℕ) (q p : ℝ) : ℝ :=
  let t := (sharedFreePetalLiftInput s q p + 2) ^ 4 + 1
  (t + 2) ^ 3 + (t + 2) ^ 36 + (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SharedFreeFullOrbitBudget
namespace OAI

section

namespace Erdos3

theorem exists_sharedFreePetalLiftBudget_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      sharedFreePetalLiftBudget s q p ≤ (p + C) ^ C := by
  let R (X : Polynomial ℕ) := ((X + 1 + (X + 3) ^ 7 + 2) ^ 9 + X + 4) ^ 4
  let H (X : Polynomial ℕ) := X + R X + 2
  let G (X : Polynomial ℕ) := X + X * ((X + 2) ^ 7 + X)
  let V (X : Polynomial ℕ) := G (X + (X + (X + 3) ^ 7 + 2) ^ 4 + 1)
  let F (X : Polynomial ℕ) := (4 * X + (X + V (4 * X)) + 3) ^ 7
  let Λ : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C (sharedFreeAffineConstant s)) ^ sharedFreeAffineConstant s
  let A : Polynomial ℕ := 4 * Polynomial.X + F (Polynomial.X + H Polynomial.X) + Λ
  let T₀ : Polynomial ℕ := (A + 2) ^ 4 + 1
  let T : Polynomial ℕ := (T₀ + 2) ^ 3 + (T₀ + 2) ^ 36 + Λ
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  have hheight : 0 ≤ coefficientFourHeightBudget p := coefficientFourHeightBudget_nonneg hp
  have hF : fourRefinementAnnihilatorBudget (q + coefficientFourHeightBudget p) ≤
      fourRefinementAnnihilatorBudget (p + coefficientFourHeightBudget p) := by
    unfold fourRefinementAnnihilatorBudget fourRefinementBasisBudget preimageBasisBudget
      sparseGeneratorBudget
    gcongr
  have hA : sharedFreePetalLiftInput s q p ≤ sharedFreePetalLiftInput s p p := by
    unfold sharedFreePetalLiftInput
    linarith
  have hA0 : 0 ≤ sharedFreePetalLiftInput s q p := by
    have h := fourRefinementAnnihilatorBudget_nonneg (add_nonneg hq hheight)
    unfold sharedFreePetalLiftInput
    positivity
  have hupper : sharedFreePetalLiftBudget s q p ≤ sharedFreePetalLiftBudget s p p := by
    dsimp only [sharedFreePetalLiftBudget]
    gcongr
  apply hupper.trans
  simpa [T, T₀, A, Λ, F, V, G, H, R, sharedFreePetalLiftBudget, sharedFreePetalLiftInput,
    coefficientFourHeightBudget, refiltrationCoordinateBudget, fourRefinementAnnihilatorBudget,
    fourRefinementBasisBudget, preimageBasisBudget, sparseGeneratorBudget, Polynomial.eval₂_pow]
      using hbound p hp

end Erdos3

end

section

namespace Erdos3

theorem exists_sharedFreeCommonCorrectionBudget_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      sharedFreeCommonCorrectionBudget s q p ≤ (p + C) ^ C := by
  let Λ : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C (sharedFreeAffineConstant s)) ^ sharedFreeAffineConstant s
  let T₀ : Polynomial ℕ := 2 * Polynomial.X + Λ + 1
  let T : Polynomial ℕ := (T₀ + 2) ^ 3 + (T₀ + 2) ^ 36 + Λ
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  have hupper : sharedFreeCommonCorrectionBudget s q p ≤
      sharedFreeCommonCorrectionBudget s p p := by
    dsimp only [sharedFreeCommonCorrectionBudget]
    gcongr
  apply hupper.trans
  simpa [T, T₀, Λ, sharedFreeCommonCorrectionBudget, two_mul, Polynomial.eval₂_pow]
    using hbound p hp

end Erdos3

end

section

namespace Erdos3

theorem exists_sharedFreeFullOrbitBudget_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ≤ (p + C) ^ C ∧
      sharedFreeCommonCorrectionBudget s q p ≤ (p + C) ^ C ∧
      sharedFreePetalLiftBudget s q p ≤ (p + C) ^ C ∧
      (s : ℝ) * (sharedFreeCommonCorrectionBudget s q p + sharedFreePetalLiftBudget s q p) ≤
        (p + C) ^ C ∧
      Real.exp (sharedFreeCommonCorrectionBudget s q p) + Real.exp (sharedFreePetalLiftBudget s q p) ≤
        Real.exp ((p + C) ^ C) := by
  obtain ⟨c, _hc, hcommon⟩ := exists_sharedFreeCommonCorrectionBudget_bound s
  obtain ⟨v, _hv, hpetal⟩ := exists_sharedFreePetalLiftBudget_bound s
  let Pc : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  let Pv : Polynomial ℕ := (Polynomial.X + Polynomial.C v) ^ v
  let Pa : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C (sharedFreeAffineConstant s)) ^ sharedFreeAffineConstant s
  let T : Polynomial ℕ := Polynomial.C s * (Pc + Pv) + (Pc + Pv + 2) + Pa
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  let Bc := (p + c) ^ c
  let Bv := (p + v) ^ v
  let Λ := (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
  have hBc : 0 ≤ Bc := pow_nonneg (add_nonneg hp (Nat.cast_nonneg c)) _
  have hBv : 0 ≤ Bv := pow_nonneg (add_nonneg hp (Nat.cast_nonneg v)) _
  have hΛ : 0 ≤ Λ := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have htotal : (s : ℝ) * (Bc + Bv) + (Bc + Bv + 2) + Λ ≤ (p + C) ^ C := by
    simpa [T, Pc, Pv, Pa, Bc, Bv, Λ, Polynomial.eval₂_pow] using hbound p hp
  have hprod : 0 ≤ (s : ℝ) * (Bc + Bv) := mul_nonneg hs0 (add_nonneg hBc hBv)
  have hplain : Bc + Bv + 2 ≤ (p + C) ^ C := by linarith only [htotal, hprod, hΛ]
  have hc := hcommon q p hq hqp hp
  have hv := hpetal q p hq hqp hp
  change sharedFreeCommonCorrectionBudget s q p ≤ Bc at hc
  change sharedFreePetalLiftBudget s q p ≤ Bv at hv
  have hscaled := mul_le_mul_of_nonneg_left (add_le_add hc hv) hs0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change Λ ≤ _
    linarith only [htotal, hprod, hBc, hBv]
  · linarith only [hc, hplain, hBv]
  · linarith only [hv, hplain, hBc]
  · linarith only [hscaled, htotal, hBc, hBv, hΛ]
  · calc
      _ ≤ Real.exp Bc + Real.exp Bv :=
        add_le_add (Real.exp_le_exp.mpr hc) (Real.exp_le_exp.mpr hv)
      _ ≤ Real.exp Bc + Real.exp Bc + Real.exp Bv := by linarith only [Real.exp_pos Bc]
      _ ≤ Real.exp (Bc + Bv + 2) := exp_repeated_add_le hBc hBv
      _ ≤ _ := Real.exp_le_exp.mpr hplain

end Erdos3

end

end OAI
end


