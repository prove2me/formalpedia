-- Prove2me | Definitions.Def_OAIE3v2B108
-- name    : OAIE3v2B108
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:43:50.799981+00:00
-- url     : https://prove2.me/theorems/49b869a3-5f26-4cef-bb52-9458dcc3fe43
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 110 of 311
-- statement:
--   Definitions bundle 110 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B087`, `OAIE3v2B088`, `OAIE3v2B089`, `OAIE3v2B090`, `OAIE3v2B092`, `OAIE3v2B093`, `OAIE3v2B298`, `OAIE3v2B095` of this split.
--
--   Modules: `Dynamics/SparseGeneratorBudget.lean`, `Estimates/BlockQuotientRows.lean`, `Estimates/BoundedQuotientFunctional.lean`, `Estimates/BoundedSparseGenerators.lean`, `Estimates/CoefficientSliceEmbedding.lean`, `Estimates/CommonDependentIntegralModel.lean`, `Estimates/CurrentLayerSplitting.lean`, `Estimates/LieTreeMultidegree.lean`, `Estimates/RationalImageIntersections.lean`, `Estimates/RationalSubspaces.lean`, `Estimates/RealSymbolRepresentativeSplitting.lean`, `Estimates/ReplicatedLieAction.lean`, `Estimates/SymbolAbsorptionBounds.lean`, `Estimates/WeightedAxisScaling.lean`, `Fourier/LogCharacterBudget.lean`, `Geometry/MarkedLocalObservableMetric.lean`, `Linear/DualAdjointAction.lean`, `Linear/DualDerivativeRemoval.lean`, `Linear/MarkedLieSpan.lean`, `Linear/QuotientProjectionCoordinates.lean`, `Linear/SpanKernelGenerators.lean`, `Nilpotent/AmbientBracketCorrectionPolynomials.lean`, `Nilpotent/BCHPairCoordinateMetric.lean`, `Nilpotent/BCHSubgroupGridExistence.lean`, `Nilpotent/FilteredAdjointFirstBracket.lean`, `Polynomial/ExtendedPolynomialValues.lean`, `Polynomial/PhaseBandCoordinateLifts.lean`, `Polynomial/RealGradedSymbolPolynomial.lean`, `Polynomial/RealPolynomialChartSubstitution.lean`, `Polynomial/TotalDegreeSplitDownsets.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B087
import Definitions.Def_OAIE3v2B088
import Definitions.Def_OAIE3v2B089
import Definitions.Def_OAIE3v2B090
import Definitions.Def_OAIE3v2B092
import Definitions.Def_OAIE3v2B093
import Definitions.Def_OAIE3v2B298
import Definitions.Def_OAIE3v2B095

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpanKernelGenerators
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in

theorem exists_bounded_rational_kernel_basis (A : Matrix ι κ ℚ) {H : ℕ}
    (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ b : Module.Basis (Fin (Module.finrank ℚ (LinearMap.ker A.mulVecLin)))
        ℚ (LinearMap.ker A.mulVecLin),
        ∀ i j, RationalHeightLE ((b i : κ → ℚ) j) (rationalKernelHeight r H) := by
  obtain ⟨r, hr, v, hli, hspan, hv⟩ := exists_bounded_rational_kernel_family A hH hA
  refine ⟨r, hr, (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan), ?_⟩
  intro i j
  simpa only [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply] using hv i j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedSparseGenerators
namespace OAI

section

namespace Erdos3

open Module

theorem exists_bounded_sparse_generators
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (K : Finset (Fin 4))
    (v : κ → Fin 4 → ι → ℚ) (hv : Submodule.span ℚ (Set.range v) = J)
    {H : ℕ} (hH : 1 ≤ H) (hvH : ∀ a k i, RationalHeightLE (v a k i) H) :
    ∃ r : ℕ, r ≤ Fintype.card (Σ _ : K, ι) ∧ ∃ w : κ → ι → ℚ,
      Submodule.span ℚ (Set.range w) = fourSparseFirstProjection J K ∧
      ∀ a i, RationalHeightLE (w a i)
        ((Fintype.card κ + 1) * (rationalKernelHeight r H * H) ^ Fintype.card κ) := by
  let P : (Fin 4 → ι → ℚ) →ₗ[ℚ] ((Σ _ : K, ι) → ℚ) := {
    toFun := fun x j => x j.1 j.2
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker P = fourCoordinateKernel K := by
    ext x
    rw [LinearMap.mem_ker, mem_fourCoordinateKernel]
    constructor
    · intro hx k hk
      funext i
      exact congrFun hx ⟨⟨k, hk⟩, i⟩
    · intro hx
      funext j
      exact congrFun (hx j.1 j.1.property) j.2
  obtain ⟨r, hr, z, hz, hzH⟩ := exists_bounded_span_kernel_generators
    (Pi.basis (fun _ : Fin 4 => Pi.basisFun ℚ ι)) (Pi.basisFun ℚ (Σ _ : K, ι)) P v hH
    (fun a j => by simpa only [Pi.basis_repr, Pi.basisFun_repr] using hvH a j.1 j.2)
    (fun a j => hvH a j.1 j.2)
  refine ⟨r, hr, fun a => z a 0, ?_, ?_⟩
  · change Submodule.span ℚ (Set.range (fun a => z a 0)) =
      (J ⊓ fourCoordinateKernel K).map (LinearMap.proj 0)
    rw [← hv, ← hker, ← hz, Submodule.map_span, ← Set.range_comp]
    rfl
  · intro a i
    simpa only [Pi.basis_repr, Pi.basisFun_repr] using hzH a ⟨0, i⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalSubspaces
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

section Intersection

variable {η κ : Type*} [Fintype η] [Fintype κ] [DecidableEq κ]
variable {ρ : η → Type*} [∀ i, Fintype (ρ i)]

theorem exists_bounded_rational_intersection_basis (A : ∀ i, Matrix (ρ i) κ ℚ)
    {H : ℕ} (hH : 1 ≤ H) (hA : ∀ i j k, RationalHeightLE (A i j k) H) :
    ∃ r : ℕ, r ≤ ∑ i, Fintype.card (ρ i) ∧
      ∃ b : Module.Basis (Fin (Module.finrank ℚ
        (⨅ i, LinearMap.ker (A i).mulVecLin : Submodule ℚ (κ → ℚ))))
        ℚ (⨅ i, LinearMap.ker (A i).mulVecLin : Submodule ℚ (κ → ℚ)),
        ∀ i j, RationalHeightLE ((b i : κ → ℚ) j) (rationalKernelHeight r H) := by
  have h := exists_bounded_rational_kernel_basis (jointMatrix A) hH
    (fun ij k => hA ij.1 ij.2 k)
  rw [← jointMatrix_ker A]
  simpa only [Fintype.card_sigma] using h

end Intersection

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalImageIntersections
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {η κ : Type*} [Fintype η] [Fintype κ] [DecidableEq κ]
variable {ρ : η → Type*} [∀ i, Fintype (ρ i)]

theorem exists_bounded_image_intersection_basis (A : ∀ i, Matrix κ (ρ i) ℚ)
    {H : ℕ} (hH : 1 ≤ H) (hA : ∀ i j k, RationalHeightLE (A i j k) H) :
    ∃ r : ℕ, r ≤ Fintype.card η * Fintype.card κ ∧
      ∃ b : Module.Basis (Fin (Module.finrank ℚ
          (⨅ i, LinearMap.range (A i).mulVecLin : Submodule ℚ (κ → ℚ))))
        ℚ (⨅ i, LinearMap.range (A i).mulVecLin : Submodule ℚ (κ → ℚ)),
        ∀ i j, RationalHeightLE ((b i : κ → ℚ) j)
          (rationalKernelHeight r (rationalKernelHeight (∑ i, Fintype.card (ρ i)) H)) := by
  classical
  choose t ht d hd D hsurj hker hD using
    (fun i => exists_bounded_image_equations (A i) hH (hA i))
  let M := ∑ i, Fintype.card (ρ i)
  let K := rationalKernelHeight M H
  have htM : ∀ i, t i ≤ M := by
    intro i
    exact (ht i).trans (Finset.single_le_sum (fun j _ => Nat.zero_le (Fintype.card (ρ j)))
      (Finset.mem_univ i))
  have hDK : ∀ i j k, RationalHeightLE (D i j k) K := by
    intro i j k
    exact (hD i j k).mono (rationalKernelHeight_mono hH (htM i))
  have hsub : (⨅ i, LinearMap.ker (D i).mulVecLin : Submodule ℚ (κ → ℚ)) =
      ⨅ i, LinearMap.range (A i).mulVecLin := iInf_congr hker
  rw [← hsub]
  obtain ⟨r, hr, b, hb⟩ := exists_bounded_rational_intersection_basis D
    (rationalKernelHeight_pos M hH) hDK
  refine ⟨r, ?_, b, hb⟩
  calc
    r ≤ ∑ i, d i := by simpa only [Fintype.card_fin] using hr
    _ ≤ ∑ _ : η, Fintype.card κ := Finset.sum_le_sum fun i _ => hd i
    _ = _ := by simp

theorem exists_image_intersection_basis_exp_height (A : ∀ i, Matrix κ (ρ i) ℚ)
    {H : ℕ} (hHpos : 1 ≤ H) (hA : ∀ i j k, RationalHeightLE (A i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hcount : (Fintype.card η : ℝ) ≤ p)
    (hdim : (Fintype.card κ : ℝ) ≤ p)
    (hcols : ((∑ i, Fintype.card (ρ i) : ℕ) : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ b : Module.Basis (Fin (Module.finrank ℚ
        (⨅ i, LinearMap.range (A i).mulVecLin : Submodule ℚ (κ → ℚ))))
      ℚ (⨅ i, LinearMap.range (A i).mulVecLin : Submodule ℚ (κ → ℚ)), ∀ i j,
        ((((b i : κ → ℚ) j).num.natAbs) : ℝ) ≤ Real.exp ((p + 2) ^ 63) ∧
        ((((b i : κ → ℚ) j).den) : ℝ) ≤ Real.exp ((p + 2) ^ 63) := by
  obtain ⟨r, hr, b, hb⟩ := exists_bounded_image_intersection_basis A hHpos hA
  let M := ∑ i, Fintype.card (ρ i)
  have hK := rationalKernelHeight_le_budget M H hp hcols hH
  have hrp : (r : ℝ) ≤ (p + 2) ^ 7 := by
    calc
      (r : ℝ) ≤ (Fintype.card η : ℝ) * Fintype.card κ := by exact_mod_cast hr
      _ ≤ (p + 2) ^ 2 := by nlinarith [mul_le_mul hcount hdim (Nat.cast_nonneg _) hp]
      _ ≤ (p + 2) ^ 7 := pow_le_pow_right₀ (by linarith) (by decide)
  have hbudget : (rationalKernelHeight r (rationalKernelHeight M H) : ℝ) ≤
      Real.exp ((p + 2) ^ 63) := by
    have h := rationalKernelHeight_le_budget r (rationalKernelHeight M H)
      (by positivity : 0 ≤ (p + 2) ^ 7) hrp hK
    exact exponential_budget_comp hp (by positivity) 7 7 le_rfl h
  refine ⟨b, fun i j => ?_⟩
  constructor
  · exact (show ((((b i : κ → ℚ) j).num.natAbs) : ℝ) ≤
      rationalKernelHeight r (rationalKernelHeight M H) from
      by exact_mod_cast (hb i j).1).trans hbudget
  · exact (show ((((b i : κ → ℚ) j).den) : ℝ) ≤
      rationalKernelHeight r (rationalKernelHeight M H) from
      by exact_mod_cast (hb i j).2).trans hbudget

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SparseGeneratorBudget
namespace OAI

section

namespace Erdos3

theorem exists_sparse_generators_exp_height
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (K : Finset (Fin 4))
    (v : κ → Fin 4 → ι → ℚ) (hv : Submodule.span ℚ (Set.range v) = J)
    {H : ℕ} (hH : 1 ≤ H) (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ p)
    (hcols : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ M : ℕ, 1 ≤ M ∧ (M : ℝ) ≤ Real.exp (sparseGeneratorBudget p) ∧
      ∃ w : κ → ι → ℚ, Submodule.span ℚ (Set.range w) = fourSparseFirstProjection J K ∧
        ∀ a i, RationalHeightLE (w a i) M := by
  obtain ⟨r, hr, w, hw, hwH⟩ := exists_bounded_sparse_generators J K v hv hH hvH
  refine ⟨(Fintype.card κ + 1) * (rationalKernelHeight r H * H) ^ Fintype.card κ, ?_,
    sparseGeneratorHeight_bound hp r (Fintype.card κ) H
      ((Nat.cast_le.mpr hr).trans hrows) hcols hHp, w, hw, hwH⟩
  have hkernel := rationalKernelHeight_pos r hH
  exact Nat.mul_pos (Nat.zero_lt_succ _) (pow_pos (Nat.mul_pos hkernel hH) _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem conjugationCoord_zsmul (g : NilpotentLieBCHGroup L s hnil) (n : ℤ) (x : L) :
    conjugationCoord g (n • x) = n • conjugationCoord g x := by
  have he : (⟨n • x⟩ : NilpotentLieBCHGroup L s hnil) =
      (⟨x⟩ : NilpotentLieBCHGroup L s hnil) ^ n := by
    apply ext
    exact (coord_zpow _ _).symm
  change ((MulAut.conj g) (⟨n • x⟩ : NilpotentLieBCHGroup L s hnil)).coord = _
  rw [he, map_zpow, coord_zpow]
  rfl

theorem conjugationCoord_rat_smul (g : NilpotentLieBCHGroup L s hnil) (q : ℚ) (x : L) :
    conjugationCoord g (q • x) = q • conjugationCoord g x := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (q.den : ℚ) * q = (q.num : ℚ) := by
    calc
      _ = (q.den : ℚ) * ((q.num : ℚ) / q.den) :=
        congrArg ((q.den : ℚ) * ·) (Rat.num_div_den q).symm
      _ = _ := by field_simp
  apply smul_right_injective L hd
  dsimp only
  calc
    _ = conjugationCoord g ((q.den : ℚ) • (q • x)) := by
      simpa only [Nat.cast_smul_eq_nsmul] using (conjugationCoord_nsmul g q.den (q • x)).symm
    _ = conjugationCoord g ((q.num : ℚ) • x) := by rw [smul_smul, hq]
    _ = (q.num : ℚ) • conjugationCoord g x := by
      simpa only [Int.cast_smul_eq_zsmul] using conjugationCoord_zsmul g q.num x
    _ = _ := by rw [smul_smul, hq]

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped TensorProduct

variable {σ R S V W : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]
  [AddCommGroup W] [Module R W] [Module S W] [IsScalarTower R S W]

section Field

variable {K : Type*} [Field K] [Infinite K] [Algebra R K]
  [Module K V] [IsScalarTower R K V]

theorem eval₂_mem_iff_coefficients (U : Submodule K V) (p : VectorPolynomial σ R V) :
    (∀ x : σ → K, eval₂ x p ∈ U) ↔ ∀ α, coefficients p α ∈ U := by
  constructor
  · intro hp
    have hz : map (U.mkQ.restrictScalars R) p = 0 := by
      apply eq_zero_of_eval₂_zero (K := K)
      intro x
      rw [eval₂_map]
      exact (Submodule.Quotient.mk_eq_zero U).mpr (hp x)
    intro α
    apply (Submodule.Quotient.mk_eq_zero U).mp
    change U.mkQ (coefficients p α) = 0
    have hc := congrArg (fun q : VectorPolynomial σ R (V ⧸ U) => coefficients q α) hz
    simpa only [coefficients_map, LinearMap.restrictScalars_apply, map_zero, Finsupp.zero_apply] using hc
  · intro hp x
    classical
    rw [← sum_monomial_coefficients p]
    simp only [Finsupp.sum, map_sum, eval₂_monomial]
    exact U.sum_mem (fun α _ => U.smul_mem _ (hp α))

end Field

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualAdjointAction
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_sub (g : NilpotentLieBCHGroup L s hnil) (x y : L) :
    dualAdjoint g (x - y) = dualAdjoint g x - dualAdjoint g y := by
  simp only [sub_eq_add_neg, dualAdjoint_add, dualAdjoint_neg]

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FilteredAdjointFirstBracket
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem lieBCH_conjugation_sub_mem {s : ℕ} (hs : 2 ≤ s) (I : LieIdeal ℚ L)
    (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ ∈ I) (hb : ⁅b, ⁅a, b⁆⁆ ∈ I) :
    lieBCH s (lieBCH s a b) (-a) - (b + ⁅a, b⁆) ∈ I := by
  apply (lieQuotientMap_eq_zero I _).mp
  rw [map_sub, map_add, map_lieBCH, map_lieBCH, map_neg, LieHom.map_lie]
  apply sub_eq_zero.mpr
  apply lieBCH_conjugation_of_central_commutator hs
  · rw [← LieHom.map_lie, ← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr ha
  · rw [← LieHom.map_lie, ← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hb

end Erdos3

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_eq_add_lie (hs : 2 ≤ s)
    (g : NilpotentLieBCHGroup L s hnil) (x : L) (hgx : ⁅g.coord, ⁅g.coord, x⁆⁆ = 0) :
    dualAdjoint g x = x + ⁅g.coord, x⁆ := by
  change dualTangentLinear
    (lieBCH s (lieBCH s (dualConstantLie g.coord) (dualInfinitesimal x))
      (-dualConstantLie g.coord)) = _
  rw [lieBCH_conjugation_of_central_commutator hs _ _
    (by rw [dualConstant_infinitesimal_lie, dualConstant_infinitesimal_lie, hgx, map_zero])
    (by rw [dualConstant_infinitesimal_lie, dualInfinitesimal_lie]),
    dualConstant_infinitesimal_lie, map_add, dualTangentLinear_infinitesimal,
    dualTangentLinear_infinitesimal]

theorem dualAdjoint_sub_first_bracket_mem (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (x : L)
    (hgx : ⁅g.coord, ⁅g.coord, x⁆⁆ ∈ V) :
    dualAdjoint g x - (x + ⁅g.coord, x⁆) ∈ V := by
  let S := dualBaseSubalgebra U
  let I := dualInvariantTangentIdeal U V hUV
  let a : S := ⟨dualConstantLie g.coord, by
    change dualBaseLinear (dualConstantLie g.coord) ∈ U ∧ _
    exact ⟨by simpa only [dualBaseLinear_constant] using hg, by trivial⟩⟩
  let b : S := ⟨dualInfinitesimal x, by
    change dualBaseLinear (dualInfinitesimal x) ∈ U ∧ _
    exact ⟨by simpa only [dualBaseLinear_infinitesimal] using U.zero_mem, by trivial⟩⟩
  have ha : ⁅a, ⁅a, b⁆⁆ ∈ I := by
    change dualBaseLinear ⁅dualConstantLie g.coord,
        ⁅dualConstantLie g.coord, dualInfinitesimal x⁆⁆ = 0 ∧
      dualTangentLinear ⁅dualConstantLie g.coord,
        ⁅dualConstantLie g.coord, dualInfinitesimal x⁆⁆ ∈ V
    rw [dualConstant_infinitesimal_lie, dualConstant_infinitesimal_lie,
      dualBaseLinear_infinitesimal, dualTangentLinear_infinitesimal]
    exact ⟨rfl, hgx⟩
  have hb : ⁅b, ⁅a, b⁆⁆ ∈ I := by
    have he : ⁅b, ⁅a, b⁆⁆ = 0 := by
      apply Subtype.ext
      change ⁅dualInfinitesimal x, ⁅dualConstantLie g.coord, dualInfinitesimal x⁆⁆ = 0
      rw [dualConstant_infinitesimal_lie, dualInfinitesimal_lie]
    rw [he]
    exact I.zero_mem
  have h := (lieBCH_conjugation_sub_mem hs I a b ha hb).2
  change dualTangentLinear (S.incl
    (lieBCH s (lieBCH s a b) (-a) - (b + ⁅a, b⁆))) ∈ V at h
  simp only [map_sub, map_add, map_lieBCH, map_neg, LieHom.map_lie] at h
  change dualTangentLinear
      (lieBCH s (lieBCH s (dualConstantLie g.coord) (dualInfinitesimal x))
        (-dualConstantLie g.coord)) -
    (dualTangentLinear (dualInfinitesimal x) +
      dualTangentLinear ⁅dualConstantLie g.coord, dualInfinitesimal x⁆) ∈ V at h
  simp only [dualConstant_infinitesimal_lie, dualTangentLinear_infinitesimal] at h
  exact h

theorem dualAdjoint_current_bracket_relation (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (r k p : L)
    (hr : ⁅g.coord, r - k⁆ ∈ V) (hp : ⁅g.coord - p, k⁆ ∈ V)
    (hk : ⁅g.coord, ⁅g.coord, k⁆⁆ ∈ V) :
    ⁅p, k⁆ - (dualAdjoint g r - r) ∈ V := by
  have hdouble : ⁅g.coord, ⁅g.coord, r⁆⁆ ∈ V := by
    have h := V.add_mem (hUV _ hg _ hr) hk
    simp only [lie_sub] at h
    simpa only [sub_add_cancel] using h
  have hmain := dualAdjoint_sub_first_bracket_mem hs U V hUV g hg r hdouble
  have hdelta : ⁅g.coord, r⁆ - ⁅p, k⁆ ∈ V := by
    have h := V.add_mem hr hp
    simp only [lie_sub, sub_lie] at h
    convert h using 1; abel
  convert V.neg_mem (V.add_mem hmain hdelta) using 1; abel

end NilpotentLieBCHGroup

namespace NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {s : ℕ} (F : NilpotentLieFiltration L s)

theorem dualAdjoint_sub_first_bracket_mem_layer (hs : 2 ≤ s) {i j : ℕ}
    (g : F.Group) (hg : g.coord ∈ F.layer i) (x : L) (hx : x ∈ F.layer j) :
    dualAdjoint g x - (x + ⁅g.coord, x⁆) ∈ F.layer (2 * i + j) := by
  apply dualAdjoint_sub_first_bracket_mem hs ⊤ (F.layerIdeal (2 * i + j)).toSubmodule
    (fun _ _ _ hv => (F.layerIdeal _).lie_mem hv) g (by trivial) x
  change ⁅g.coord, ⁅g.coord, x⁆⁆ ∈ F.layer (2 * i + j)
  simpa only [two_mul, Nat.add_assoc] using F.lie_mem hg (F.lie_mem hg hx)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def polynomialDualEval : VectorPolynomial Unit ℚ L →ₗ⁅ℚ⁆ DualLieAlgebra L where
  toLinearMap := (MvPolynomial.aeval (fun _ : Unit => (DualNumber.eps : DualNumber ℚ))).toLinearMap.rTensor L
  map_lie' {p q} := by
    let e : VectorPolynomial Unit ℚ L →ₗ[ℚ] DualLieAlgebra L :=
      (MvPolynomial.aeval (fun _ : Unit => (DualNumber.eps : DualNumber ℚ))).toLinearMap.rTensor L
    change e ⁅p, q⁆ = ⁅e p, e q⁆
    induction p using TensorProduct.induction_on with
    | zero => refine (congrArg _ (zero_lie (L := VectorPolynomial Unit ℚ L) (M := VectorPolynomial Unit ℚ L) _)).trans ?_; first | (simp; done) | (rw [map_zero]; exact (zero_lie (L := DualLieAlgebra L) (M := DualLieAlgebra L) _).symm) | exact (zero_lie (L := DualLieAlgebra L) (M := DualLieAlgebra L) _).symm
    | tmul a x =>
      induction q using TensorProduct.induction_on with
      | zero => refine (congrArg _ (lie_zero (L := VectorPolynomial Unit ℚ L) (M := VectorPolynomial Unit ℚ L) _)).trans ?_; first | (simp; done) | (rw [map_zero]; exact (lie_zero (L := DualLieAlgebra L) (M := DualLieAlgebra L) _).symm) | exact (lie_zero (L := DualLieAlgebra L) (M := DualLieAlgebra L) _).symm
      | tmul b y =>
        simp only [e, LieAlgebra.ExtendScalars.bracket_tmul, LinearMap.rTensor_tmul,
          AlgHom.toLinearMap_apply, map_mul]
      | add q q' hq hq' =>
        simp only [LieRing.lie_add, map_add, hq, hq']
        exact (LieRing.lie_add (e (a ⊗ₜ[ℚ] x)) (e q) (e q')).symm
    | add p p' hp hp' =>
      simp only [LieRing.add_lie, map_add, hp, hp']
      exact (LieRing.add_lie (e p) (e p') (e q)).symm

theorem polynomialDualEval_constant (x : L) :
    polynomialDualEval (monomial (0 : Unit →₀ ℕ) x) = dualConstantLie x := by
  change MvPolynomial.aeval (fun _ : Unit => (DualNumber.eps : DualNumber ℚ))
    (1 : MvPolynomial Unit ℚ) ⊗ₜ[ℚ] x = _
  rw [map_one]
  rfl

theorem polynomialDualEval_linear (x : L) :
    polynomialDualEval (monomial (Finsupp.single () 1) x) = dualInfinitesimal x := by
  change MvPolynomial.aeval (fun _ : Unit => (DualNumber.eps : DualNumber ℚ))
    (MvPolynomial.X ()) ⊗ₜ[ℚ] x = _
  rw [MvPolynomial.aeval_X]
  rfl

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem conjugation_polynomial (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    lieBCH s (lieBCH s (monomial (R := ℚ) (0 : Unit →₀ ℕ) g.coord)
      (monomial (Finsupp.single () 1) x)) (-monomial 0 g.coord) =
        monomial (Finsupp.single () 1) (conjugationCoord g x) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval_zero
  intro a
  simp only [map_sub, eval_lieBCH, map_neg, eval_monomial,
    Finsupp.prod_zero_index, one_smul, Finsupp.prod_single_index, pow_zero, pow_one]
  exact sub_eq_zero.mpr (conjugationCoord_rat_smul g (a ()) x)

theorem dualAdjoint_eq_conjugationCoord (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjoint g x = conjugationCoord g x := by
  have he := congrArg (polynomialDualEval (L := L)) (conjugation_polynomial g x)
  rw [map_lieBCH, map_lieBCH, map_neg, polynomialDualEval_constant,
    polynomialDualEval_linear, polynomialDualEval_linear] at he
  have ht := congrArg (dualTangentLinear (L := L)) he
  exact ht.trans (dualTangentLinear_infinitesimal _)

theorem conjugationCoord_eq_add_lie (hs : 2 ≤ s)
    (g : NilpotentLieBCHGroup L s hnil) (x : L) (hx : ⁅g.coord, ⁅g.coord, x⁆⁆ = 0) :
    conjugationCoord g x = x + ⁅g.coord, x⁆ := by
  rw [← dualAdjoint_eq_conjugationCoord]
  exact dualAdjoint_eq_add_lie hs g x hx

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)
  (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
  (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)

include hUV

theorem adjoint_current_layer_relation (hs : 2 ≤ s) {j : ℕ} (hj : 1 ≤ j)
    (g : F.Group) (hg : g.coord ∈ U) (r k p : L)
    (hp : p ∈ F.layer (j - 1)) (hk : k ∈ F.layer 1)
    (hr : r - k ∈ V ⊔ F.layer j)
    (hlower : ⁅g.coord - p, k⁆ ∈ V ⊔ F.layer (j + 1)) :
    ⁅p, k⁆ - (dualAdjoint g r - r) ∈ V ⊔ F.layer (j + 1) := by
  have hW := F.invariant_sup_layer U V hUV (j + 1)
  apply dualAdjoint_current_bracket_relation hs U (V ⊔ F.layer (j + 1)) hW g hg r k p
    (F.lie_mem_invariant_sup_next_layer U V hUV j hg hr) hlower
  have hpk : ⁅p, k⁆ ∈ F.layer j := by
    simpa only [Nat.sub_add_cancel hj] using F.lie_mem hp hk
  have hg1 : g.coord ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hhigh : ⁅g.coord, ⁅p, k⁆⁆ ∈ F.layer (j + 1) := by
    simpa only [Nat.add_comm 1 j] using F.lie_mem hg1 hpk
  have h := (V ⊔ F.layer (j + 1)).add_mem (hW _ hg _ hlower) (Submodule.mem_sup_right hhigh)
  simpa only [sub_lie, lie_sub, sub_add_cancel] using h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualDerivativeRemoval
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualLogDerivative_sub_tangent_mem (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (z : DualGroup hnil) (hb : dualBaseLinear z.coord ∈ U)
    (hbr : ⁅dualBaseLinear z.coord, dualTangentLinear z.coord⁆ ∈ V) :
    dualLogDerivative z - dualTangentLinear z.coord ∈ V := by
  let S := dualBaseSubalgebra U
  let I := dualInvariantTangentIdeal U V hUV
  let a : S := ⟨z.coord, ⟨hb, by trivial⟩⟩
  let b : S := ⟨-dualConstantLie (dualBaseLinear z.coord), by
    change dualBaseLinear (-dualConstantLie (dualBaseLinear z.coord)) ∈ U ∧ _
    constructor
    · rw [map_neg, dualBaseLinear_constant]
      exact U.neg_mem hb
    · trivial⟩
  have hab : ⁅a, b⁆ ∈ I := by
    change dualBaseLinear ⁅z.coord, -dualConstantLie (dualBaseLinear z.coord)⁆ = 0 ∧
      dualTangentLinear ⁅z.coord, -dualConstantLie (dualBaseLinear z.coord)⁆ ∈ V
    simp only [dualBaseLinear_lie, dualTangentLinear_lie, map_neg,
      dualBaseLinear_constant, dualTangentLinear_constant, neg_zero, lie_zero,
      zero_add, lie_neg, lie_self]
    rw [lie_skew]
    exact ⟨trivial, hbr⟩
  have he : lieBCH s a b - (a + b) ∈ I := by
    apply (lieQuotientMap_eq_zero I _).mp
    rw [map_sub, map_add, map_lieBCH]
    have hzero : ⁅lieQuotientMap I a, lieQuotientMap I b⁆ = 0 := by
      rw [← LieHom.map_lie]
      exact (lieQuotientMap_eq_zero I _).mpr hab
    rw [lieBCH_eq_add_of_lie_eq_zero_pos hs hzero, sub_self]
  have h := he.2
  change dualTangentLinear (S.incl (lieBCH s a b - (a + b))) ∈ V at h
  simp only [map_sub, map_add, map_lieBCH] at h
  change dualTangentLinear
      (lieBCH s z.coord (-dualConstantLie (dualBaseLinear z.coord))) -
    (dualTangentLinear z.coord +
      dualTangentLinear (-dualConstantLie (dualBaseLinear z.coord))) ∈ V at h
  simp only [map_neg, dualTangentLinear_constant, neg_zero, add_zero] at h
  exact h

end NilpotentLieBCHGroup

namespace NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {s : ℕ} (F : NilpotentLieFiltration L s)

theorem dualLogDerivative_sub_tangent_mem_layer (hs : 1 ≤ s) {i j : ℕ}
    (z : DualGroup F.lowerCentralSeries_eq_bot)
    (hb : dualBaseLinear z.coord ∈ F.layer i)
    (ht : dualTangentLinear z.coord ∈ F.layer j) :
    dualLogDerivative z - dualTangentLinear z.coord ∈ F.layer (i + j) := by
  exact dualLogDerivative_sub_tangent_mem hs ⊤ (F.layerIdeal (i + j)).toSubmodule
    (fun _ _ _ hv => (F.layerIdeal _).lie_mem hv) z (by trivial) (F.lie_mem hb ht)

theorem logDerivative_current_layer_relation (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (z : DualGroup F.lowerCentralSeries_eq_bot) (hb : dualBaseLinear z.coord ∈ U)
    (hbr : ⁅dualBaseLinear z.coord, dualTangentLinear z.coord⁆ ∈ V ⊔ F.layer (j + 1)) :
    dualLogDerivative z - dualTangentLinear z.coord ∈ V ⊔ F.layer (j + 1) :=
  dualLogDerivative_sub_tangent_mem hs U (V ⊔ F.layer (j + 1))
    (F.invariant_sup_layer U V hUV (j + 1)) z hb hbr

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialChartSubstitution
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

def PolynomialDerivativeSystem (P : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L) : Prop :=
  ∀ i, formalLogDerivative i P = small i + dualAdjoint P (rational i) + extra i

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedAxisScaling
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

theorem aeval_weightedHomogeneousComponent (v : σ → ℕ) (w : τ → ℕ)
    (f : σ → MvPolynomial τ R)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (v i))
    (n : ℕ) (p : MvPolynomial σ R) :
    aeval f (weightedHomogeneousComponent v n p) =
      weightedHomogeneousComponent w n (aeval f p) := by
  classical
  rw [← p.support_sum_monomial_coeff]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro α _
  have hm := isWeightedHomogeneous_monomial v α (p.coeff α) rfl
  have hfα := isWeightedHomogeneous_aeval_monomial v w f hf α (p.coeff α)
  by_cases h : n = Finsupp.weight v α
  · rw [h, hm.weightedHomogeneousComponent_same, hfα.weightedHomogeneousComponent_same]
  · rw [hm.weightedHomogeneousComponent_ne n h, map_zero,
      hfα.weightedHomogeneousComponent_ne n h]

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieTreeMultidegree
namespace OAI

section

namespace Erdos3

variable {I J L : Type*} [LieRing L]

theorem lieTreeOccurrenceTree_eval (v : I → L) (a : FreeMagma I) :
    lieTreeEval (v ∘ lieTreeOccurrenceLabel a) (lieTreeOccurrenceTree a) = lieTreeEval v a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change ⁅lieTreeEval _ (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a)),
      lieTreeEval _ (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b))⁆ = _
    rw [lieTreeEval_relabel, lieTreeEval_relabel]
    exact congrArg₂ (fun x y : L => ⁅x, y⁆) ha hb

theorem lieTreeOccurrenceTree_weight (w : I → ℕ) (a : FreeMagma I) :
    lieTreeWeight (w ∘ lieTreeOccurrenceLabel a) (lieTreeOccurrenceTree a) = lieTreeWeight w a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change lieTreeWeight _ (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a)) +
      lieTreeWeight _ (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b)) = _
    rw [lieTreeWeight_relabel, lieTreeWeight_relabel]
    exact congrArg₂ (· + ·) ha hb

end Erdos3

end

section

namespace Erdos3

variable {R I J L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

theorem lieTreeOccurrenceMultilinear_original (v : I → L) (a : FreeMagma I) :
    lieTreeOccurrenceMultilinear (R := R) a (v ∘ lieTreeOccurrenceLabel a) = lieTreeEval v a :=
  (lieTreeOccurrenceMultilinear_apply a _).trans (lieTreeOccurrenceTree_eval v a)

theorem exists_linear_lieTree_expansion {E : Type*} [AddCommGroup E] [Module R E]
    (η : L →ₗ[R] E) (C D : I → Submodule R L) (hDC : ∀ i, D i ≤ C i)
    (a : FreeMagma I) (x : I → L) (hx : ∀ i, x i ∈ C i)
    (hvanish : ∀ v : LieTreeOccurrences a → L,
      (∀ i, v i ∈ C (lieTreeOccurrenceLabel a i)) → ∀ i j, i ≠ j →
        v i ∈ D (lieTreeOccurrenceLabel a i) → v j ∈ D (lieTreeOccurrenceLabel a j) →
        η (lieTreeEval v (lieTreeOccurrenceTree a)) = 0) :
    ∃ A : (∀ i, D i) →ₗ[R] E, ∀ y : ∀ i, D i,
      η (lieTreeEval (fun i => x i + (y i : L)) a) = η (lieTreeEval x a) + A y := by
  classical
  let f := η.compMultilinearMap (lieTreeOccurrenceMultilinear (R := R) a)
  obtain ⟨A, hA⟩ := exists_linear_expansion_of_two_vanish f
    (C ∘ lieTreeOccurrenceLabel a) (D ∘ lieTreeOccurrenceLabel a)
    (fun i => hDC (lieTreeOccurrenceLabel a i))
    (fun v hv i j hij hi hj => by
      change η (lieTreeOccurrenceMultilinear a v) = 0
      rw [lieTreeOccurrenceMultilinear_apply]
      exact hvanish v hv i j hij hi hj)
    (x ∘ lieTreeOccurrenceLabel a) (fun i => hx (lieTreeOccurrenceLabel a i))
  let diagonal : (∀ i, D i) →ₗ[R] (∀ j : LieTreeOccurrences a, D (lieTreeOccurrenceLabel a j)) :=
    LinearMap.pi (fun j => LinearMap.proj (lieTreeOccurrenceLabel a j))
  refine ⟨A.comp diagonal, ?_⟩
  intro y
  have h := hA (diagonal y)
  change η (lieTreeOccurrenceMultilinear a ((fun i => x i + (y i : L)) ∘
      lieTreeOccurrenceLabel a)) =
    η (lieTreeOccurrenceMultilinear a (x ∘ lieTreeOccurrenceLabel a)) + A (diagonal y) at h
  simpa only [lieTreeOccurrenceMultilinear_original, LinearMap.comp_apply] using h

end Erdos3

end

section

namespace Erdos3

variable {I : Type*}

theorem lieTreeWeight_eq_sum_occurrences (w : I → ℕ) (a : FreeMagma I) :
    lieTreeWeight w a = ∑ i : LieTreeOccurrences a, w (lieTreeOccurrenceLabel a i) := by
  induction a using FreeMagma.rec with
  | of i => simp [lieTreeWeight, LieTreeOccurrences, lieTreeOccurrenceLabel]
  | mul a b ha hb =>
    change lieTreeWeight w a + lieTreeWeight w b =
      ∑ i : LieTreeOccurrences a ⊕ LieTreeOccurrences b,
        w (Sum.elim (lieTreeOccurrenceLabel a) (lieTreeOccurrenceLabel b) i)
    rw [Fintype.sum_sum_type, ha, hb]
    rfl

theorem lieTreeMarkedCount_eq_card (marked : I → Bool) (a : FreeMagma I) :
    lieTreeMarkedCount marked a =
      (Finset.univ.filter (fun i : LieTreeOccurrences a => marked (lieTreeOccurrenceLabel a i))).card := by
  classical
  rw [lieTreeMarkedCount, lieTreeWeight_eq_sum_occurrences]
  simp only [Finset.card_filter]

theorem exists_two_marked_occurrences (marked : I → Bool) (a : FreeMagma I)
    (ha : 2 ≤ lieTreeMarkedCount marked a) :
    ∃ i j : LieTreeOccurrences a, i ≠ j ∧
      marked (lieTreeOccurrenceLabel a i) = true ∧
      marked (lieTreeOccurrenceLabel a j) = true := by
  classical
  rw [lieTreeMarkedCount_eq_card] at ha
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show 1 < _ from ha)
  exact ⟨i, j, hij, (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bounded_block_quotient_projection {ι κ δ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → δ) (d : κ → δ) (A : Matrix ι κ ℚ)
    (hblock : ∀ i j, c i ≠ d j → A i j = 0) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ Q : Matrix ι ι ℚ, Q * Q = Q ∧
      LinearMap.ker Q.mulVecLin = LinearMap.range A.mulVecLin ∧
      (∀ i j, c i ≠ c j → Q i j = 0) ∧
      ∀ i j, RationalHeightLE (Q i j) (imageDefiningHeight (Fintype.card κ) (Fintype.card ι) H) := by
  classical
  obtain ⟨S, hS, hSb, hSH⟩ := exists_bounded_block_image_section c d A hblock hH hA
  let Q : Matrix ι ι ℚ := 1 - A * S
  have hId : (A * S) * (A * S) = A * S := by rw [← Matrix.mul_assoc, hS]
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · dsimp only [Q]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hId, sub_self, sub_zero]
  · ext x
    change (1 - A * S) *ᵥ x = 0 ↔ ∃ y, A *ᵥ y = x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    constructor
    · intro hx
      exact ⟨S *ᵥ x, (sub_eq_zero.mp hx).symm⟩
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hS, sub_self]
  · intro i j hij
    have hne : i ≠ j := fun h => hij (congrArg c h)
    have hprod : (A * S) i j = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hik : c i = d k
      · exact (congrArg (fun z : ℚ => A i k * z)
          (hSb k j (fun hkj => hij (hik.trans hkj)))).trans (mul_zero _)
      · exact (congrArg (fun z : ℚ => z * S k j) (hblock i k hik)).trans (zero_mul _)
    simp only [Q, Matrix.sub_apply, Matrix.one_apply, hne, ↓reduceIte, hprod, sub_self]
  · intro i j
    have hI : RationalHeightLE ((1 : Matrix ι ι ℚ) i j) 1 := by
      by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
    have hp := rationalHeightLE_matrix_mul A S hA hSH i j
    simpa only [Q, Matrix.sub_apply, imageDefiningHeight, mul_one] using hI.sub hp

theorem exists_submodule_block_quotient_projection
    {V ι κ δ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ]
    (b : Basis ι ℚ V) (c : ι → δ) (U : Submodule ℚ V) (v : κ → V)
    (hspan : Submodule.span ℚ (Set.range v) = U) (hU : BasisBlockInvariant b c U)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H) :
    ∃ Q : Matrix ι ι ℚ, Q * Q = Q ∧
      LinearMap.ker Q.mulVecLin = U.map b.equivFun.toLinearMap ∧
      (∀ i j, c i ≠ c j → Q i j = 0) ∧
      ∀ i j, RationalHeightLE (Q i j)
        (imageDefiningHeight (Fintype.card ι * Fintype.card κ) (Fintype.card ι) H) := by
  classical
  let v' := blockSpanningFamily b c v
  let A : Matrix ι (ι × κ) ℚ := fun i j => b.repr (v' j) i
  have hA : ∀ i j, RationalHeightLE (A i j) H :=
    fun i j => blockSpanningFamily_height b c v hH hv j i
  have hAb : ∀ i j, c i ≠ c j.1 → A i j = 0 := by
    intro i j hij
    exact (blockSpanningFamily_repr b c v j i).trans (if_neg hij)
  have he := exists_bounded_block_quotient_projection c (fun j : ι × κ => c j.1) A hAb hH hA
  obtain ⟨Q, hQQ, hker, hblock, hQ⟩ := he
  refine ⟨Q, hQQ, hker.trans ?_, hblock, ?_⟩
  · rw [Matrix.range_mulVecLin, ← blockSpanningFamily_span b c U v hspan hU,
      Submodule.map_span, ← Set.range_comp]
    rfl
  · simpa only [Fintype.card_prod] using hQ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BlockQuotientRows
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_block_quotient_rows {ι δ : Type*} [Fintype ι]
    (c : ι → δ) (Q : Matrix ι ι ℚ) (hblock : ∀ i j, c i ≠ c j → Q i j = 0)
    {H : ℕ} (hH : 1 ≤ H) (hQ : ∀ i j, RationalHeightLE (Q i j) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ rows : Fin r → ι, Function.Injective rows ∧
      Function.Surjective (Q.submatrix rows id).mulVec ∧
      LinearMap.ker (Q.submatrix rows id).mulVecLin = LinearMap.ker Q.mulVecLin ∧
      ∃ S : Matrix ι (Fin r) ℚ, Q.submatrix rows id * S = 1 ∧
        (∀ i j, c i ≠ c (rows j) → S i j = 0) ∧
        ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight r H) := by
  classical
  obtain ⟨r, hr, rows, hinj, hsurj, hker⟩ := exists_independent_defining_rows Q
  let D := Q.submatrix rows id
  have hD : ∀ i j, c (rows i) ≠ c j → D i j = 0 := fun i j h => hblock (rows i) j h
  obtain ⟨S, hS, hSb, hSH⟩ := exists_bounded_block_image_section (fun i => c (rows i)) c D hD hH
    (fun i j => hQ (rows i) j)
  have hDS : D * S = 1 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    change (D * S) *ᵥ (D *ᵥ x) = 1 *ᵥ (D *ᵥ x)
    rw [Matrix.mulVec_mulVec, hS, Matrix.one_mulVec]
  exact ⟨r, hr, rows, hinj, hsurj, hker, S, hDS, hSb, by simpa only [Fintype.card_fin] using hSH⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedQuotientFunctional
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix BigOperators

variable {ι κ V U : Type*} [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module ℚ V] [AddCommGroup U] [Module ℚ U]

theorem exists_bounded_linear_retraction (a : Basis κ ℚ U) (b : Basis ι ℚ V)
    (φ : U →ₗ[ℚ] V) (hφ : Function.Injective φ) {H : ℕ} (hH : 1 ≤ H)
    (ha : ∀ i j, RationalHeightLE (b.repr (φ (a j)) i) H) :
    ∃ ρ : V →ₗ[ℚ] U, (∀ x, ρ (φ x) = x) ∧
      ∀ i j, RationalHeightLE (a.repr (ρ (b j)) i)
        (rationalSolveHeight (Fintype.card κ) H) := by
  classical
  let A := LinearMap.toMatrix a b φ
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have heq (z : κ → ℚ) : A *ᵥ z = b.equivFun (φ (a.equivFun.symm z)) := by
      have hz := LinearMap.toMatrix_mulVec_repr a b φ (a.equivFun.symm z)
      simpa only [A, ← a.equivFun_apply, ← b.equivFun_apply,
        LinearEquiv.apply_symm_apply] using hz
    rw [heq, heq] at hxy
    exact a.equivFun.symm.injective (hφ (b.equivFun.injective hxy))
  obtain ⟨P, hPA, hP⟩ := exists_bounded_rational_left_inverse A
    (Matrix.mulVec_injective_iff.mp hinj) hH
    (by simpa only [A, LinearMap.toMatrix_apply] using ha)
  refine ⟨Matrix.toLin b a P, ?_, ?_⟩
  · intro x
    have hcomp : (Matrix.toLin b a P).comp φ = LinearMap.id := by
      calc
        _ = (Matrix.toLin b a P).comp (Matrix.toLin a b A) := by
          rw [Matrix.toLin_toMatrix]
        _ = Matrix.toLin a a (P * A) := (Matrix.toLin_mul a b a P A).symm
        _ = LinearMap.id := by rw [hPA, Matrix.toLin_one]
    exact LinearMap.congr_fun hcomp x
  · intro i j
    have hij := LinearMap.toMatrix_toLin b a P
    have hv := congrArg (fun M => M i j) hij
    rw [LinearMap.toMatrix_apply] at hv
    rw [hv]
    exact hP i j

theorem exists_bounded_functional_extension (a : Basis κ ℚ U) (b : Basis ι ℚ V)
    (φ : U →ₗ[ℚ] V) (hφ : Function.Injective φ) (η : U →ₗ[ℚ] ℚ)
    {H K : ℕ} (hH : 1 ≤ H)
    (ha : ∀ i j, RationalHeightLE (b.repr (φ (a j)) i) H)
    (hη : ∀ j, RationalHeightLE (η (a j)) K) :
    ∃ ξ : V →ₗ[ℚ] ℚ, (∀ x, ξ (φ x) = η x) ∧
      ∀ i, RationalHeightLE (ξ (b i))
        ((Fintype.card κ + 1) *
          (rationalSolveHeight (Fintype.card κ) H * K) ^ Fintype.card κ) := by
  classical
  obtain ⟨ρ, hρ, hheight⟩ := exists_bounded_linear_retraction a b φ hφ hH ha
  refine ⟨η.comp ρ, fun x => by simp only [LinearMap.comp_apply, hρ], ?_⟩
  intro i
  have he : η (ρ (b i)) = ∑ j, a.repr (ρ (b i)) j * η (a j) := by
    conv_lhs => rw [← a.sum_repr (ρ (b i))]
    simp only [map_sum, map_smul, smul_eq_mul]
  change RationalHeightLE (η (ρ (b i))) _
  rw [he]
  exact rationalHeightLE_sum _ (fun j => (hheight j i).mul (hη j))

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_bounded_functional_preserving_subspace
    {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (W : Submodule ℚ V) (v : κ → V)
    (hspan : Submodule.span ℚ (Set.range v) = W) (η : V →ₗ[ℚ] ℚ)
    {H K : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (b.repr (v i) j) H)
    (hη : ∀ i, RationalHeightLE (η (v i)) K) :
    ∃ ξ : V →ₗ[ℚ] ℚ, (∀ x ∈ W, ξ x = η x) ∧
      ∀ i, RationalHeightLE (ξ (b i))
        ((finrank ℚ W + 1) * (rationalSolveHeight (finrank ℚ W) H * K) ^ finrank ℚ W) := by
  classical
  let : FiniteDimensional ℚ V := b.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hspan] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  let a : Basis (Fin (finrank ℚ W)) ℚ W :=
    (Basis.span hzli).map (LinearEquiv.ofEq _ _ hzspan)
  have ha (i) : (a i : V) = z i := by
    simp only [a, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  have hcoords (i j) : RationalHeightLE (b.repr (W.subtype (a j)) i) H := by
    change RationalHeightLE (b.repr (a j : V) i) H
    rw [ha]
    obtain ⟨k, hk⟩ := hz j
    rw [← hk]
    exact hv k i
  have hvalues (j) : RationalHeightLE ((η.comp W.subtype) (a j)) K := by
    change RationalHeightLE (η (a j : V)) K
    rw [ha]
    obtain ⟨k, hk⟩ := hz j
    rw [← hk]
    exact hη k
  obtain ⟨ξ, hξ, hbound⟩ := exists_bounded_functional_extension a b W.subtype
    Subtype.val_injective (η.comp W.subtype) hH hcoords hvalues
  refine ⟨ξ, fun x hx => hξ ⟨x, hx⟩, ?_⟩
  simpa only [Fintype.card_fin] using hbound

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolAbsorptionBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem realGradeTruncation_eq_iff (j : ℕ) (x y : ℝ ⊗[ℚ] L) :
    basisBelowProjection (b.baseChange ℝ) w j x = basisBelowProjection (b.baseChange ℝ) w j y ↔
      x - y ∈ F.realification.layer j := by
  change _ ↔ x - y ∈ (F.realLayer j).toSubmodule
  rw [F.realLayer_eq_span_basis b j {i | j ≤ w i} (hlayers j)]
  exact basisBelowProjection_eq_iff (b.baseChange ℝ) w j x y

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealGradedSymbolPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

section Lie

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realificationLieEquiv_smul (a : ℝ)
    (x : ℝ ⊗[ℚ] VectorPolynomial σ ℚ L) :
    realificationLieEquiv (a • x) = a • realificationLieEquiv x :=
  (realificationRealLinearEquiv (σ := σ) (V := L)).map_smul a x

noncomputable instance realLieAlgebra : LieAlgebra ℝ (VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) where
  lie_smul a P Q := by
    obtain ⟨p, rfl⟩ := realificationLieEquiv.surjective P
    obtain ⟨q, rfl⟩ := realificationLieEquiv.surjective Q
    change ⁅realificationLieEquiv p, a • realificationLieEquiv q⁆ =
      a • ⁅realificationLieEquiv p, realificationLieEquiv q⁆
    rw [← realificationLieEquiv_smul, ← LieEquiv.map_lie, lie_smul,
      realificationLieEquiv_smul, LieEquiv.map_lie]

end Lie

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolRepresentativeSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem realSymbolRepresentative_slow_coefficients (T : σ → ℝ)
    (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hlayers w T M g)
    (α : σ →₀ ℕ) (i : ι) :
    |(b.baseChange ℝ).repr (coefficients (F.realSymbolRepresentative b ω hlayers w g.coord) α) i| ≤
      M / monomialScale T α := by
  by_cases h : Finsupp.weight w α = ω i
  · have hc := F.realSymbolRepresentative_coefficient b ω hlayers w g.coord ⟨(α, i), h⟩
    exact (congrArg abs hc).le.trans (hg ⟨(α, i), h⟩)
  · rw [F.realSymbolRepresentative_coefficient_of_ne b ω hlayers w g.coord α i h, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TotalDegreeSplitDownsets
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem totalDegree_zero_layer : F.layer 0 = ⊤ := by
  apply top_unique
  rw [← F.one_eq_top]
  exact F.antitone (Nat.zero_le 1)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReplicatedLieAction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*}

theorem replicated_blockDegree_le [Fintype σ] (bound : σ → ℕ)
    (a : SquarefreeIndex (ReplicatedIndex bound)) :
    blockDegree (fun j : ReplicatedIndex bound => j.1) a.val ≤ bound := by
  intro i
  rw [replicated_blockDegree_apply]
  calc
    _ ≤ ∑ _j : Fin (bound i), 1 := Finset.sum_le_sum fun j _ => a.property ⟨i, j⟩
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

noncomputable def cellLength : ℕ := residueCellLength d.mesh d.length d.modulusBound

end ScalarCubeLocalizationData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CurrentLayerSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem bch_triple_sub_sum_mem_next_layer (k : ℕ) (a p d : L)
    (ha : a ∈ F.layer k) (hd : d ∈ F.layer k) :
    lieBCH s (lieBCH s a p) d - (a + p + d) ∈ F.layer (k + 1) := by
  have hp : p ∈ F.layer 1 := by simp only [F.one_eq_top, Submodule.mem_top]
  have hap : lieBCH s a p ∈ F.layer 1 := by
    simp only [F.one_eq_top, Submodule.mem_top]
  have h₁ := lieBCH_sub_add_mem F.lowerCentralSeries_eq_bot
    (F.layerIdeal (k + 1)) a p (F.lie_mem ha hp)
  have h₂ := lieBCH_sub_add_mem F.lowerCentralSeries_eq_bot
    (F.layerIdeal (k + 1)) (lieBCH s a p) d
    (by
      change ⁅lieBCH s a p, d⁆ ∈ F.layer (k + 1)
      simpa only [Nat.add_comm 1 k] using F.lie_mem hap hd)
  have h := (F.layer (k + 1)).add_mem h₂ h₁
  convert h using 1
  abel

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AmbientBracketCorrectionPolynomials
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

variable {L ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype ι] [Fintype κ] [Fintype ν] {E V : Submodule ℚ L}

theorem exists_controlled_bracket_corrections
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (κ × ι) : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ (Q : Matrix ν (κ × ι) ℚ) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      let C := Matrix.mulVecLin (fun i j => (Q i j : ℝ))
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (small rational : κ × ι → ℝ) (v : ν → ℝ),
        ‖small‖ ≤ Real.exp p / monomialScale T α → rational ∈ realDenominatorGrid l →
        realBracketSystem f k (bracketSystemLift e v) = small + rational →
        bracketSystemLift e (C small) ∈ E.baseChange ℝ ∧
        bracketSystemLift e (C rational) ∈ E.baseChange ℝ ∧
        realBracketSystem f k (bracketSystemLift e (C small)) = small ∧
        realBracketSystem f k (bracketSystemLift e (C rational)) = rational ∧
        ‖C small‖ ≤ Real.exp ((p + 2) ^ 18 + p) / monomialScale T α ∧
        C rational ∈ realDenominatorGrid m ∧
        ∀ b, ⁅bracketSystemLift e v - bracketSystemLift e (C small) -
          bracketSystemLift e (C rational), (1 : ℝ) ⊗ₜ[ℚ] k b⁆ ∈ V.baseChange ℝ := by
  have hsplit := exists_controlled_linear_splitting (bracketSystemMatrix e f k)
    hH hl hA hp hrows hcols hHp hlp T hT
  obtain ⟨Q, m, hm, hmp, hQ⟩ := hsplit
  refine ⟨Q, m, hm, hmp, ?_⟩
  intro C α hα small rational v hsmall hrational heq
  have heq' := (bracketSystemMatrix_real_apply e f k v).trans heq
  obtain ⟨hsmallQ, hratQ, hnorm, hgrid, hzero⟩ :=
    hQ α hα small rational v hsmall hrational heq'
  refine ⟨bracketSystemLift_mem e _, bracketSystemLift_mem e _,
    (bracketSystemMatrix_real_apply e f k (C small)).symm.trans hsmallQ,
    (bracketSystemMatrix_real_apply e f k (C rational)).symm.trans hratQ,
    hnorm, hgrid, ?_⟩
  apply (realBracketSystem_eq_zero_iff f k _).mp
  have h := (bracketSystemMatrix_real_apply e f k (v - C small - C rational)).symm.trans hzero
  simpa only [map_sub] using h

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L μ ν : Type*} [LieRing L] [LieAlgebra ℚ L] {E : Submodule ℚ L}

theorem bracketSystemLift_grid [Fintype μ] [Fintype ν]
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) (m : ℕ) (x : ν → ℝ)
    (hx : x ∈ realDenominatorGrid m) :
    (b.baseChange ℝ).equivFun (bracketSystemLift e x) ∈
      realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m) := by
  rw [bracketSystemLift_coordinates]
  exact real_matrix_denominator_grid (bracketLiftMatrix b e) m x hx

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {L ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype ι] [Fintype κ] [Fintype ν] {E V : Submodule ℚ L}

theorem exists_bracket_correction_polynomials
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (κ × ι) : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P : VectorPolynomial σ ℚ (ν → ℝ))
    (small rational : VectorPolynomial σ ℚ (κ × ι → ℝ))
    (hP0 : coefficients P 0 = 0) (hsmall0 : coefficients small 0 = 0)
    (hrational0 : coefficients rational 0 = 0)
    (hsmall : ∀ α, ‖coefficients small α‖ ≤ Real.exp p / monomialScale T α)
    (hrational : ∀ α, coefficients rational α ∈ realDenominatorGrid l)
    (heq : ∀ α, realBracketSystem f k (bracketSystemLift e (coefficients P α)) =
      coefficients small α + coefficients rational α) :
    ∃ (m : ℕ) (A B : VectorPolynomial σ ℚ (ν → ℝ)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      map (((realBracketSystem f k).comp (bracketSystemLift e)).restrictScalars ℚ) A = small ∧
      map (((realBracketSystem f k).comp (bracketSystemLift e)).restrictScalars ℚ) B = rational ∧
      (∀ α, coefficients small α = 0 → coefficients A α = 0) ∧
      (∀ α, coefficients rational α = 0 → coefficients B α = 0) ∧
      (∀ α, ‖coefficients A α‖ ≤ Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, coefficients B α ∈ realDenominatorGrid m) ∧
      ∀ α b, ⁅bracketSystemLift e (coefficients (P - A - B) α),
        (1 : ℝ) ⊗ₜ[ℚ] k b⁆ ∈ V.baseChange ℝ := by
  have h := exists_controlled_bracket_corrections e f k hH hl hA hp hrows hcols hHp hlp T hT
  obtain ⟨Q, m, hm, hmp, hQ⟩ := h
  let C : (κ × ι → ℝ) →ₗ[ℝ] (ν → ℝ) := Matrix.mulVecLin (fun i j => (Q i j : ℝ))
  let A := map (C.restrictScalars ℚ) small
  let B := map (C.restrictScalars ℚ) rational
  have hAc (α : σ →₀ ℕ) : coefficients A α = C (coefficients small α) :=
    coefficients_map _ _ _
  have hBc (α : σ →₀ ℕ) : coefficients B α = C (coefficients rational α) :=
    coefficients_map _ _ _
  have hcoeff (α : σ →₀ ℕ) (hα : α ≠ 0) :=
    hQ α hα (coefficients small α) (coefficients rational α) (coefficients P α)
      (hsmall α) (hrational α) (heq α)
  refine ⟨m, A, B, hm, hmp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map, hAc]
    change realBracketSystem f k (bracketSystemLift e (C (coefficients small α))) = _
    by_cases hα : α = 0
    · simp only [hα, hsmall0, map_zero]
    · exact (hcoeff α hα).2.2.1
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map, hBc]
    change realBracketSystem f k (bracketSystemLift e (C (coefficients rational α))) = _
    by_cases hα : α = 0
    · simp only [hα, hrational0, map_zero]
    · exact (hcoeff α hα).2.2.2.1
  · intro α hα
    rw [hAc, hα, map_zero]
  · intro α hα
    rw [hBc, hα, map_zero]
  · intro α
    rw [hAc]
    by_cases hα : α = 0
    · simp only [hα, hsmall0, map_zero, norm_zero, monomialScale_zero, div_one]
      exact Real.exp_nonneg _
    · exact (hcoeff α hα).2.2.2.2.1
  · intro α
    rw [hBc]
    by_cases hα : α = 0
    · rw [hα, hrational0, map_zero]
      exact ⟨0, by ext i; simp⟩
    · exact (hcoeff α hα).2.2.2.2.2.1
  · intro α b
    simp only [map_sub, Finsupp.sub_apply, hAc, hBc]
    by_cases hα : α = 0
    · simp only [hα, hP0, hsmall0, hrational0, map_zero, sub_zero, zero_lie]
      exact (V.baseChange ℝ).zero_mem
    · simpa only [map_sub] using (hcoeff α hα).2.2.2.2.2.2 b

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {L μ ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] {E V : Submodule ℚ L}

theorem exists_ambient_bracket_correction_polynomials
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    {H J l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) J)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (κ × ι) : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P : VectorPolynomial σ ℚ (ν → ℝ))
    (small rational : VectorPolynomial σ ℚ (κ × ι → ℝ))
    (hP0 : coefficients P 0 = 0) (hsmall0 : coefficients small 0 = 0)
    (hrational0 : coefficients rational 0 = 0)
    (hsmall : ∀ α, ‖coefficients small α‖ ≤ Real.exp p / monomialScale T α)
    (hrational : ∀ α, coefficients rational α ∈ realDenominatorGrid l)
    (heq : ∀ α, realBracketSystem f k (bracketSystemLift e (coefficients P α)) =
      coefficients small α + coefficients rational α) :
    ∃ (m : ℕ) (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      map ((realBracketSystem f k).restrictScalars ℚ) A = small ∧
      map ((realBracketSystem f k).restrictScalars ℚ) B = rational ∧
      (∀ α, coefficients A α ∈ E.baseChange ℝ ∧ coefficients B α ∈ E.baseChange ℝ) ∧
      (∀ α, coefficients small α = 0 → coefficients A α = 0) ∧
      (∀ α, coefficients rational α = 0 → coefficients B α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) *
          Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      ∀ α t, ⁅coefficients (map ((bracketSystemLift e).restrictScalars ℚ) P - A - B) α,
        (1 : ℝ) ⊗ₜ[ℚ] k t⁆ ∈ V.baseChange ℝ := by
  have h := exists_bracket_correction_polynomials e f k hH hl hA hp hrows hcols hHp hlp
    T hT P small rational hP0 hsmall0 hrational0 hsmall hrational heq
  obtain ⟨m, A₀, B₀, hm, hmp, hAQ, hBQ, hAzero, hBzero, hAnorm, hBgrid, hres⟩ := h
  let A := map ((bracketSystemLift e).restrictScalars ℚ) A₀
  let B := map ((bracketSystemLift e).restrictScalars ℚ) B₀
  have hAc (α : σ →₀ ℕ) : coefficients A α = bracketSystemLift e (coefficients A₀ α) :=
    coefficients_map _ _ _
  have hBc (α : σ →₀ ℕ) : coefficients B α = bracketSystemLift e (coefficients B₀ α) :=
    coefficients_map _ _ _
  refine ⟨m, A, B, hm, hmp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map, hAc]
    simpa only [coefficients_map, LinearMap.restrictScalars_apply, LinearMap.comp_apply]
      using congrArg (fun q => coefficients q α) hAQ
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map, hBc]
    simpa only [coefficients_map, LinearMap.restrictScalars_apply, LinearMap.comp_apply]
      using congrArg (fun q => coefficients q α) hBQ
  · intro α
    rw [hAc, hBc]
    exact ⟨bracketSystemLift_mem e _, bracketSystemLift_mem e _⟩
  · intro α hα
    rw [hAc, hAzero α hα, map_zero]
  · intro α hα
    rw [hBc, hBzero α hα, map_zero]
  · intro α
    rw [hAc]
    apply (bracketSystemLift_norm_bound b e he _).trans
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (hAnorm α)
      (by positivity : 0 ≤ ((Fintype.card ν : ℝ) + 1) * (J + 1))
  · intro α
    rw [hBc]
    exact bracketSystemLift_grid b e m _ (hBgrid α)
  · intro α t
    simp only [map_sub, Finsupp.sub_apply, coefficients_map, hAc, hBc]
    simpa only [map_sub, Finsupp.sub_apply, LinearMap.restrictScalars_apply] using hres α t

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LogCharacterBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def logCharacterMetricConstant (s d H : ℕ) (A : ℝ≥0) : ℝ≥0 :=
  (2 + CircleFourier.characterLipConstant * A) * bchLogMetricConstant s d H 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MarkedLieSpan
namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem markedLieSpan_leaf (v : I → L) (w : I → ℕ) (marked : I → Bool) (i : I) :
    v i ∈ markedLieSpan v w marked (w i) (if marked i then 1 else 0) 1 :=
  Submodule.subset_span ⟨.of i, le_rfl, le_rfl, le_rfl, rfl⟩

theorem markedLieSpan_top_le_ker {A : Type*} [AddCommGroup A] [Module ℚ A]
    {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (k : ℕ) (η : L →ₗ[ℚ] A)
    (hzero : ∀ a : FreeMagma I, lieTreeWeight w a = s → a.length = r →
      k ≤ lieTreeMarkedCount marked a → η (lieTreeEval v a) = 0) :
    markedLieSpan v w marked s k r ≤ η.ker := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, hd, hk, hl, rfl⟩
  change η (lieTreeEval v a) = 0
  by_cases he : lieTreeWeight w a = s
  · by_cases hn : a.length = r
    · exact hzero a he hn hk
    · have hm := F.lieTreeEval_mem_length v w hv a
      rw [F.layer_eq_bot_of_past_top (Or.inr ⟨he.symm, by omega⟩), Submodule.mem_bot] at hm
      rw [hm, map_zero]
  · have hm := F.lieTreeEval_mem_length v w hv a
    rw [F.layer_eq_bot_of_past_top (Or.inl (by omega)), Submodule.mem_bot] at hm
    rw [hm, map_zero]

theorem markedLieSpan_marked_terminal {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (d l : ℕ) :
    markedLieSpan v w marked d (s + 1) l = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro x ⟨a, _, hk, _, rfl⟩
  have hcount := (lieTreeMarkedCount_le_length marked a).trans (lieTree_length_le_weight w hw a)
  have hs : s < lieTreeWeight w a := by omega
  have hm := F.lieTreeEval_mem_length v w hv a
  rw [F.layer_eq_bot_of_past_top (Or.inl hs)] at hm
  exact hm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentIntegralModel
namespace OAI

section

namespace Erdos3

open Module

variable {I L : Type*} [Fintype I] [LieRing L] [LieAlgebra ℚ L]

theorem finiteMarkedLieValues_mem (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (s d k l : ℕ) {x : L} (hx : x ∈ finiteMarkedLieValues v w marked s d k l) :
    x ∈ markedLieSpan v w marked d k l := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨_, hd, hk, hl⟩ := Finset.mem_filter.mp ha
  exact Submodule.subset_span ⟨a, hd, hk, hl, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHPairCoordinateMetric
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

variable {ι L : Type*} [Fintype ι]
  [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
  (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H s : ℕ}
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)

include hstructure hc

theorem lieBCH_pair_coordinates_bound (x₁ y₁ x₂ y₂ : L) {B δ : ℝ}
    (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hx₁ : ∀ i, |e.repr x₁ i| ≤ B) (hy₁ : ∀ i, |e.repr y₁ i| ≤ B)
    (hx₂ : ∀ i, |e.repr x₂ i| ≤ B) (hy₂ : ∀ i, |e.repr y₂ i| ≤ B)
    (hxx : ∀ i, |e.repr x₁ i - e.repr x₂ i| ≤ δ)
    (hyy : ∀ i, |e.repr y₁ i - e.repr y₂ i| ≤ δ) (k : ι) :
    |e.repr (lieBCH s x₁ y₁) k - e.repr (lieBCH s x₂ y₂) k| ≤
      bchBoxCoordinateBound s (Fintype.card ι) H B * δ := by
  classical
  let P := bchCoordinatePolynomial c s k
  let v : Fin 2 × ι → ℝ := fun z => e.repr (![x₁, y₁] z.1) z.2
  let w : Fin 2 × ι → ℝ := fun z => e.repr (![x₂, y₂] z.1) z.2
  have hdegree : P.totalDegree ≤ s := bchCoordinatePolynomial_totalDegree c s k
  have hv (z : Fin 2 × ι) : |v z| ≤ B := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hx₁ i
    · exact hy₁ i
  have hw (z : Fin 2 × ι) : |w z| ≤ B := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hx₂ i
    · exact hy₂ i
  have hvw (z : Fin 2 × ι) : |v z - w z| ≤ δ := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hxx i
    · exact hyy i
  have hcoeff (m) : |((P.coeff m : ℚ) : ℝ)| ≤ bchCoordinateHeight s (Fintype.card ι) H :=
    (bchCoordinatePolynomial_height c hc s k m).abs_real_le
  have h := abs_aeval_sub_aeval_box_bound P v w (Nat.cast_nonneg _) hB hδ hcoeff hv hw hvw hdegree
  have hevalv : aeval v P = e.repr (lieBCH s x₁ y₁) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s x₁ y₁ k
  have hevalw : aeval w P = e.repr (lieBCH s x₂ y₂) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s x₂ y₂ k
  rw [hevalv, hevalw] at h
  have hcard := polynomial_support_card_le P hdegree
  apply h.trans
  dsimp only [bchBoxCoordinateBound]
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  gcongr
  exact_mod_cast hcard

theorem lieBCH_pair_coordinate_dist_le (x₁ y₁ x₂ y₂ : L) {B δ : ℝ}
    (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hx₁ : ‖e.equivFun x₁‖ ≤ B) (hy₁ : ‖e.equivFun y₁‖ ≤ B)
    (hx₂ : ‖e.equivFun x₂‖ ≤ B) (hy₂ : ‖e.equivFun y₂‖ ≤ B)
    (hxx : dist (e.equivFun x₁) (e.equivFun x₂) ≤ δ)
    (hyy : dist (e.equivFun y₁) (e.equivFun y₂) ≤ δ) :
    dist (e.equivFun (lieBCH s x₁ y₁)) (e.equivFun (lieBCH s x₂ y₂)) ≤
      bchBoxCoordinateBound s (Fintype.card ι) H B * δ := by
  apply (dist_pi_le_iff (mul_nonneg (bchBoxCoordinateBound_nonneg s _ H (by linarith)) hδ)).mpr
  intro i
  have hcoord (x : L) (hx : ‖e.equivFun x‖ ≤ B) (j : ι) : |e.repr x j| ≤ B := by
    calc
      _ ≤ ‖e.equivFun x‖ := by
        simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using norm_le_pi_norm (e.equivFun x) j
      _ ≤ B := hx
  have hdiff (x y : L) (hxy : dist (e.equivFun x) (e.equivFun y) ≤ δ) (j : ι) :
      |e.repr x j - e.repr y j| ≤ δ := by
    calc
      _ ≤ dist (e.equivFun x) (e.equivFun y) := by
        simpa only [Real.dist_eq, Basis.equivFun_apply] using dist_le_pi_dist (e.equivFun x) (e.equivFun y) j
      _ ≤ δ := hxy
  exact lieBCH_pair_coordinates_bound e c hstructure hc x₁ y₁ x₂ y₂ hB hδ
    (hcoord _ hx₁) (hcoord _ hy₁) (hcoord _ hx₂) (hcoord _ hy₂) (hdiff _ _ hxx) (hdiff _ _ hyy) i

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
open scoped TensorProduct NNReal

noncomputable def markedRetractionBoxConstant (s d H : ℕ) (p : ℝ) (B : ℝ≥0) : ℝ≥0 :=
  ⟨bchBoxCoordinateBound (s + 1) d H (Real.exp (5 * p) * B) * Real.exp (5 * p),
    mul_nonneg (bchBoxCoordinateBound_nonneg _ _ _ (mul_nonneg (Real.exp_nonneg _) B.coe_nonneg))
      (Real.exp_nonneg _)⟩

noncomputable def markedEvaluationBoxRadius (s d H : ℕ) (p : ℝ) (B : ℝ≥0) : ℝ≥0 :=
  ⟨Real.exp (2 * p), Real.exp_nonneg _⟩ * markedRetractionBoxConstant s d H p B * B + 1

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
open scoped TensorProduct NNReal

noncomputable def phaseBandCoordinateConstant (s d H : ℕ) (R : ℝ≥0) : ℝ≥0 :=
  bchLogMetricConstant s d H R * bchLogMetricConstant s d H 1

noncomputable def phaseBandQuotientConstant (s d H : ℕ) (R K L : ℝ≥0) : ℝ≥0 :=
  2 * phaseBandCoordinateConstant s d H R * L +
    16 * (K + bchLogMetricConstant s d H 1 + phaseBandCoordinateConstant s d H R + 1)

end Erdos3

end

end OAI
end


