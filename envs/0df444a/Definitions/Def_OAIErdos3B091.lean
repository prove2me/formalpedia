-- Prove2me | Definitions.Def_OAIErdos3B091
-- name    : OAIErdos3B091
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T16:13:28.061624+00:00
-- url     : https://prove2.me/theorems/cf7d116c-f42e-4909-8d83-70831b3e62fd
-- title:
--   OpenAI Erdős-3 split, definitions bundle 92 of 103
-- statement:
--   Definitions bundle 92 of 103 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B090`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 92 available.
--
--   Modules: `OAI.Erdos3.BasisGradedSubmodule.mem_sup_higher_of_grade`, `OAI.Erdos3.BasisHomogeneousBrackets`, `OAI.Erdos3.BasisHomogeneousBrackets.baseChange`, `OAI.Erdos3.BasisHomogeneousBrackets.lie_mem_span`, `OAI.Erdos3.BasisHomogeneousBrackets.projection_lie`, `OAI.Erdos3.MultidegreeLieFiltration.piRealOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.piRealOrbit_eval`, `OAI.Erdos3.MultidegreeLieFiltration.realProductSingle_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedBasis_homogeneous_brackets`, `OAI.Erdos3.NilpotentLieFiltration.exists_associatedGradedPieceMap_of_pure`, `OAI.Erdos3.NilpotentLieFiltration.normalizedRelativeSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.normalizedRelative_coefficient_mem_two`, `OAI.Erdos3.NilpotentLieFiltration.piRealOrbit`, `OAI.Erdos3.NilpotentLieFiltration.piRealOrbit_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.piRealOrbit_eval`, `OAI.Erdos3.NilpotentLieFiltration.piRealOrbit_project_log`, `OAI.Erdos3.NilpotentLieFiltration.realGradeProjection_bch_triple`, `OAI.Erdos3.NilpotentLieFiltration.realGradeProjection_eq_zero_of_mem_next_layer`, `OAI.Erdos3.NilpotentLieFiltration.realGradeProjection_normalized_residual_mem`, `OAI.Erdos3.NilpotentLieFiltration.realGradeProjection_normalized_splitting`, `OAI.Erdos3.NilpotentLieFiltration.relativeSquareLift`, `OAI.Erdos3.NilpotentLieFiltration.relativeSquarePolynomial`, `OAI.Erdos3.NilpotentLieFiltration.relativeSquarePolynomial_adapted`, `OAI.Erdos3.NilpotentLieFiltration.relativeSquarePolynomial_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.relativeSquareSymbolMap`, `OAI.Erdos3.NilpotentLieFiltration.relativeSquareSymbolMap_eq_zero_iff`, `OAI.Erdos3.NilpotentLieFiltration.supportedQuotientBasis_layers`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_homogeneous_brackets`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_inl_base`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_inl_polynomial`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_inr_base`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_inr_polynomial`, `OAI.Erdos3.baseChange_mem_of_mapsTo`, `OAI.Erdos3.basisGradeProjection_eq_zero_of_mem_higher`, `OAI.Erdos3.realProductSingle`, `OAI.Erdos3.realProductSingle_mem_layer`, `OAI.Erdos3.realProductSingle_projection`, `OAI.Erdos3.realProductSingle_projection_ne`, `OAI.Erdos3.realification_moduleTopology_t2`, `OAI.Erdos3.sub_basisGradeProjection_mem_higher`, `OAI.Erdos3.supportedQuotientBasis_lieStructure`, `OAI.Erdos3.supportedQuotientBasis_projection_height`, `_private.Nilpotent.CurrentBracketInductionStep.0.OAI.Erdos3.PolynomialTranslationLie.coeff_pderiv_monomial_grade`, `_private.Nilpotent.CurrentBracketInductionStep.0.OAI.Erdos3.PolynomialTranslationLie.single_direction_derivative`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B025

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GradedPieceRepresentative
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_associatedGradedPieceMap_of_pure
    {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (j : ℕ) (x : F.AssociatedGraded)
    (hx : basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x = x) :
    ∃ v : F.layer j, F.associatedGradedPieceMap j v = x := by
  have hm := basisCoordinateProjection_mem_span (F.associatedGradedBasis e ω hF)
    {i | ω i = j} x
  change basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x ∈ _ at hm
  rw [hx, ← F.associatedGradedPieceMap_range e ω hF j] at hm
  exact hm

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductOrbitCongruence
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3

theorem baseChange_mem_of_mapsTo {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (P : Submodule ℚ V) (Q : Submodule ℚ W)
    (f : V →ₗ[ℚ] W) (hf : ∀ x ∈ P, f x ∈ Q) {x : ℝ ⊗[ℚ] V}
    (hx : x ∈ P.baseChange ℝ) : f.baseChange ℝ x ∈ Q.baseChange ℝ := by
  have hm : P.baseChange ℝ ≤ (Q.baseChange ℝ).comap (f.baseChange ℝ) := by
    rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.tmul_mem_baseChange_of_mem 1 (hf a ha)
  exact hm hx

variable {ι : Type*} {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

noncomputable def realProductSingle (i : ι) :
    (ℝ ⊗[ℚ] L i) →ₗ[ℝ] (ℝ ⊗[ℚ] (∀ j, L j)) := by
  classical
  exact (LinearMap.single ℚ L i).baseChange ℝ

theorem realProductSingle_projection (i : ι) (x : ℝ ⊗[ℚ] L i) :
    realificationLieHom (liePiEval i) (realProductSingle i x) = x := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    change r ⊗ₜ[ℚ] (Pi.single i x i) = r ⊗ₜ[ℚ] x
    rw [Pi.single_eq_same]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realProductSingle_projection_ne {i j : ι} (hij : j ≠ i) (x : ℝ ⊗[ℚ] L i) :
    realificationLieHom (liePiEval j) (realProductSingle i x) = 0 := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    change r ⊗ₜ[ℚ] (Pi.single i x j) = 0
    rw [Pi.single_eq_of_ne hij, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem realProductSingle_mem_layer {s : ℕ} (F : ∀ i, NilpotentLieFiltration (L i) s)
    (i : ι) (n : ℕ) {x : ℝ ⊗[ℚ] L i} (hx : x ∈ (F i).realification.layer n) :
    realProductSingle i x ∈ (NilpotentLieFiltration.pi F).realification.layer n := by
  classical
  apply baseChange_mem_of_mapsTo ((F i).layer n) ((NilpotentLieFiltration.pi F).layer n)
    (LinearMap.single ℚ L i) _ hx
  intro a ha
  apply (NilpotentLieFiltration.mem_pi_layer F n _).mpr
  intro j
  change Pi.single i a j ∈ (F j).layer n
  by_cases hji : j = i
  · subst j
    simpa only [Pi.single_eq_same] using ha
  · rw [Pi.single_eq_of_ne hji]
    exact Submodule.zero_mem _

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {bound : σ → ℕ}
  (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound)

theorem realProductSingle_mem_layer (i : ι) (a : σ → ℕ) {x : ℝ ⊗[ℚ] L i}
    (hx : x ∈ (F i).realification.layer a) :
    realProductSingle i x ∈ (pi F).realification.layer a := by
  classical
  apply baseChange_mem_of_mapsTo ((F i).layer a) ((pi F).layer a)
    (LinearMap.single ℚ L i) _ hx
  intro y hy
  apply (mem_pi_layer F a _).mpr
  intro j
  change Pi.single i y j ∈ (F j).layer a
  by_cases hji : j = i
  · subst j
    simpa only [Pi.single_eq_same] using hy
  · rw [Pi.single_eq_of_ne hji]
    exact Submodule.zero_mem _

noncomputable def piRealOrbit (g : ∀ i, (F i).realification.PolynomialOrbit) :
    (pi F).realification.PolynomialOrbit :=
  (pi F).realification.polynomialOrbitOfLog
    (∑ i, VectorPolynomial.map ((realProductSingle i).restrictScalars ℚ)
      ((g i).log (F i).realification)) (by
      intro a
      simp only [map_sum, Finsupp.finsetSum_apply, VectorPolynomial.coefficients_map]
      apply Submodule.sum_mem
      intro i _
      exact realProductSingle_mem_layer F i _ ((g i).adapted (F i).realification a))

theorem piRealOrbit_eval (g : ∀ i, (F i).realification.PolynomialOrbit) (x : σ → ℤ) (i : ι) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := (pi F).ordinary.lowerCentralSeries_eq_bot)
      (hM := (F i).ordinary.lowerCentralSeries_eq_bot) (liePiEval i)
      ((pi F).realification.polynomialOrbitEval x (piRealOrbit F g)) =
        (F i).realification.polynomialOrbitEval x (g i) := by
  classical
  apply NilpotentLieBCHGroup.ext
  simp only [NilpotentLieBCHGroup.realificationMap_coord, polynomialOrbitEval_coord,
    piRealOrbit, polynomialOrbitOfLog, PolynomialOrbit.log, map_sum, VectorPolynomial.eval_map]
  rw [Finset.sum_eq_single i]
  · exact realProductSingle_projection i _
  · intro j _ hji
    exact realProductSingle_projection_ne (Ne.symm hji) _
  · simp

end Erdos3.MultidegreeLieFiltration

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.NilpotentLieFiltration

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
  (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}

noncomputable def piRealOrbit (p : ∀ i, (F i).realification.PolynomialOrbit w) :
    (pi F).realification.PolynomialOrbit w :=
  polynomialOrbitOfLog
    (∑ i, VectorPolynomial.map ((realProductSingle i).restrictScalars ℚ) (p i).log) (by
      apply ((pi F).realification.adapted_iff_coefficients w _).mpr
      intro α
      simp only [map_sum, Finsupp.finsetSum_apply, VectorPolynomial.coefficients_map]
      apply Submodule.sum_mem
      intro i _
      exact realProductSingle_mem_layer F i _
        (((F i).realification.adapted_iff_coefficients w _).mp (p i).adapted α))

theorem piRealOrbit_eval (p : ∀ i, (F i).realification.PolynomialOrbit w)
    (x : σ → ℤ) (i : ι) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := (pi F).lowerCentralSeries_eq_bot) (hM := (F i).lowerCentralSeries_eq_bot) (liePiEval i)
      ((pi F).realification.polynomialOrbitEval w x (piRealOrbit F p)) =
        (F i).realification.polynomialOrbitEval w x (p i) := by
  classical
  apply NilpotentLieBCHGroup.ext
  simp only [NilpotentLieBCHGroup.realificationMap_coord, polynomialOrbitEval_coord,
    piRealOrbit, polynomialOrbitOfLog_log, map_sum, VectorPolynomial.eval_map]
  rw [Finset.sum_eq_single i]
  · exact realProductSingle_projection i _
  · intro j _ hji
    exact realProductSingle_projection_ne (Ne.symm hji) _
  · simp

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
  (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}

theorem piRealOrbit_coefficient (p : ∀ i, (F i).realification.PolynomialOrbit w)
    (α : σ →₀ ℕ) (i : ι) :
    realificationLieHom (liePiEval i) (coefficients (piRealOrbit F p).log α) =
      coefficients (p i).log α := by
  classical
  simp only [piRealOrbit, polynomialOrbitOfLog_log, map_sum,
    Finsupp.finsetSum_apply, coefficients_map]
  rw [Finset.sum_eq_single i]
  · exact realProductSingle_projection i _
  · intro j _ hji
    exact realProductSingle_projection_ne (Ne.symm hji) _
  · simp

theorem piRealOrbit_project_log (p : ∀ i, (F i).realification.PolynomialOrbit w) (i : ι) :
    VectorPolynomial.map ((realificationLieHom (liePiEval i)).toLinearMap.restrictScalars ℚ)
      (piRealOrbit F p).log = (p i).log := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  exact piRealOrbit_coefficient F p α i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open scoped TensorProduct

end Erdos3

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.NilpotentLieFiltration

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealificationModuleTopology
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem realification_moduleTopology_t2 {κ L : Type*} [Fintype κ]
    [AddCommGroup L] [Module ℚ L] (b : Basis κ ℚ L) :
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] L)
    T2Space (ℝ ⊗[ℚ] L) := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] L)
  have hc : Continuous (b.baseChange ℝ).equivFun :=
    IsModuleTopology.continuous_of_linearMap (b.baseChange ℝ).equivFun.toLinearMap
  exact T2Space.of_injective_continuous (b.baseChange ℝ).equivFun.injective hc

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedLieQuotient
namespace OAI

section

namespace Erdos3

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem supportedQuotientBasis_lieStructure (b : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (S : Set ι) (hI : I.toSubmodule = Submodule.span ℚ (b '' S))
    (i j k : {i // i ∉ S}) :
    lieStructureConstants (L := L ⧸ I) (supportedQuotientBasis b I.toSubmodule S hI) i j k =
      lieStructureConstants b i j k := by
  unfold lieStructureConstants
  rw [supportedQuotientBasis_apply, supportedQuotientBasis_apply]
  change (supportedQuotientBasis b I.toSubmodule S hI).repr
    (I.toSubmodule.mkQ ⁅b i, b j⁆) k = _
  exact supportedQuotientBasis_repr_mk b I.toSubmodule S hI _ k

theorem supportedQuotientBasis_projection_height (b : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (S : Set ι) (hI : I.toSubmodule = Submodule.span ℚ (b '' S))
    (i : ι) (j : {i // i ∉ S}) :
    RationalHeightLE ((supportedQuotientBasis b I.toSubmodule S hI).repr
      (lieQuotientMap I (b i)) j) 1 := by
  change RationalHeightLE ((supportedQuotientBasis b I.toSubmodule S hI).repr
    (I.toSubmodule.mkQ (b i)) j) 1
  rw [supportedQuotientBasis_repr_mk]
  exact basis_repr_height_one b i j

namespace NilpotentLieFiltration

variable {s t : ℕ} (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

include hlayers in
theorem supportedQuotientBasis_layers (j : ℕ) :
    (F.quotientLie I hI).layer j = Submodule.span ℚ
      (supportedQuotientBasis b I.toSubmodule S hspan '' {i | j ≤ w i}) := by
  change (F.layer j).map I.toSubmodule.mkQ = _
  rw [hlayers j]
  exact supportedQuotientBasis_map_span b I.toSubmodule S hspan {i | j ≤ w i}

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.GradeProjectionRemainder
namespace OAI

section

namespace Erdos3

open Module

section Coordinates

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem basisGradeProjection_eq_zero_of_mem_higher (b : Basis ι K V)
    (w : ι → ℕ) (k : ℕ) (x : V)
    (hx : x ∈ Submodule.span K (b '' {i | k + 1 ≤ w i})) :
    basisGradeProjection b w k x = 0 := by
  apply (basisCoordinateProjection_eq_zero_iff b {i | w i = k} x).mpr
  apply Submodule.span_mono (Set.image_mono ?_) hx
  intro i hi
  change w i ≠ k
  change k + 1 ≤ w i at hi
  omega

theorem sub_basisGradeProjection_mem_higher (b : Basis ι K V)
    (w : ι → ℕ) (k : ℕ) (x : V)
    (hx : x ∈ Submodule.span K (b '' {i | k ≤ w i})) :
    x - basisGradeProjection b w k x ∈ Submodule.span K (b '' {i | k + 1 ≤ w i}) := by
  apply (basis_mem_span_image_iff b _ _).mpr
  intro i hi
  change ¬ k + 1 ≤ w i at hi
  rw [map_sub, Finsupp.sub_apply, basisGradeProjection_repr]
  by_cases hki : w i = k
  · simp only [hki, ↓reduceIte, sub_self]
  · rw [if_neg hki, sub_zero]
    exact (basis_mem_span_image_iff b _ x).mp hx i (by
      change ¬ k ≤ w i
      omega)

theorem BasisGradedSubmodule.mem_sup_higher_of_grade (b : Basis ι K V)
    (w : ι → ℕ) (U : Submodule K V) (hU : BasisGradedSubmodule b w U)
    (k : ℕ) (x : V) (hx : x ∈ U ⊔ Submodule.span K (b '' {i | k ≤ w i}))
    (hgrade : basisGradeProjection b w k x ∈ U) :
    x ∈ U ⊔ Submodule.span K (b '' {i | k + 1 ≤ w i}) := by
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  have hgz : basisGradeProjection b w k z ∈ U := by
    have h := U.sub_mem hgrade (hU k u hu)
    simpa only [map_add, add_sub_cancel_left] using h
  refine Submodule.mem_sup.mpr ⟨u + basisGradeProjection b w k z, U.add_mem hu hgz,
    z - basisGradeProjection b w k z, sub_basisGradeProjection_mem_higher b w k z hz, ?_⟩
  abel

end Coordinates

namespace NilpotentLieFiltration

open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem realGradeProjection_eq_zero_of_mem_next_layer (k : ℕ) (x : ℝ ⊗[ℚ] L)
    (hx : x ∈ F.realification.layer (k + 1)) :
    basisGradeProjection (b.baseChange ℝ) w k x = 0 := by
  apply basisGradeProjection_eq_zero_of_mem_higher
  change x ∈ (F.realLayer (k + 1)).toSubmodule at hx
  rwa [F.realLayer_eq_span_basis b (k + 1) _ (hlayers (k + 1))] at hx

include hlayers in
theorem realGradeProjection_bch_triple (k : ℕ) (a p d : ℝ ⊗[ℚ] L)
    (ha : a ∈ F.realification.layer k) (hd : d ∈ F.realification.layer k) :
    basisGradeProjection (b.baseChange ℝ) w k (lieBCH s (lieBCH s a p) d) =
      basisGradeProjection (b.baseChange ℝ) w k a +
        basisGradeProjection (b.baseChange ℝ) w k p +
        basisGradeProjection (b.baseChange ℝ) w k d := by
  have h := F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers k _
    (F.realification.bch_triple_sub_sum_mem_next_layer k a p d ha hd)
  simpa only [map_sub, map_add, sub_eq_zero] using h

include hlayers in
theorem realGradeProjection_normalized_splitting (k : ℕ)
    (E P R E₀ R₀ : F.realification.Group)
    (hE : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) E₀ =
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) E)
    (hR : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) R =
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) R₀) :
    basisGradeProjection (b.baseChange ℝ) w k (E₀⁻¹ * (E * P * R) * R₀⁻¹).coord =
      basisGradeProjection (b.baseChange ℝ) w k (E₀⁻¹ * E).coord +
        basisGradeProjection (b.baseChange ℝ) w k P.coord +
        basisGradeProjection (b.baseChange ℝ) w k (R * R₀⁻¹).coord := by
  have h := F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers k _
    (F.realification.normalized_splitting_sub_sum_mem_next_layer k E P R E₀ R₀ hE hR)
  simpa only [map_sub, map_add, sub_eq_zero] using h

include hlayers in

theorem realGradeProjection_normalized_residual_mem
    (U : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hU : BasisGradedSubmodule (b.baseChange ℝ) w U) (k : ℕ)
    (E P R E₀ R₀ : F.realification.Group) (hP : P.coord ∈ U)
    (hE : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) E₀ =
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) E)
    (hR : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) R =
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) R₀) :
    basisGradeProjection (b.baseChange ℝ) w k (E₀⁻¹ * (E * P * R) * R₀⁻¹).coord -
      basisGradeProjection (b.baseChange ℝ) w k (E₀⁻¹ * E).coord -
      basisGradeProjection (b.baseChange ℝ) w k (R * R₀⁻¹).coord ∈ U := by
  rw [F.realGradeProjection_normalized_splitting b w hlayers k E P R E₀ R₀ hE hR]
  convert hU k P.coord hP using 1
  abel

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CurrentBracketInductionStep
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

section General

variable {R L ι : Type*} [Field R] [LieRing L] [LieAlgebra R L]

def BasisHomogeneousBrackets (b : Basis ι R L) (w : ι → ℕ) : Prop :=
  ∀ i j k, w k ≠ w i + w j → b.repr ⁅b i, b j⁆ k = 0

theorem BasisHomogeneousBrackets.lie_mem_span (b : Basis ι R L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) {i j : ℕ} {x y : L}
    (hx : x ∈ Submodule.span R (b '' {k | w k = i}))
    (hy : y ∈ Submodule.span R (b '' {k | w k = j})) :
    ⁅x, y⁆ ∈ Submodule.span R (b '' {k | w k = i + j}) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := hy
    change w a = i at ha
    change w c = j at hc
    apply (basis_mem_span_image_iff b _ _).mpr
    intro k hk
    change w k ≠ i + j at hk
    exact hb a c k (by simpa only [ha, hc] using hk)
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left r x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ r h
  | smul_right r x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ r h

theorem BasisHomogeneousBrackets.projection_lie (b : Basis ι R L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) {i j : ℕ} {x y : L}
    (hx : basisGradeProjection b w i x = x) (hy : basisGradeProjection b w j y = y) :
    basisGradeProjection b w (i + j) ⁅x, y⁆ = ⁅x, y⁆ := by
  apply basisCoordinateProjection_eq_self
  apply hb.lie_mem_span b w
  · rw [← hx]
    exact basisCoordinateProjection_mem_span b _ _
  · rw [← hy]
    exact basisCoordinateProjection_mem_span b _ _

end General

theorem BasisHomogeneousBrackets.baseChange {L ι : Type*} [LieRing L] [LieAlgebra ℚ L]
    (b : Basis ι ℚ L) (w : ι → ℕ) (hb : BasisHomogeneousBrackets b w) :
    BasisHomogeneousBrackets (b.baseChange ℝ) w := by
  intro i j k hk
  rw [Basis.baseChange_apply, Basis.baseChange_apply,
    LieAlgebra.ExtendScalars.bracket_tmul, one_mul, Basis.baseChange_repr_tmul, hb i j k hk]
  exact zero_smul ℚ (1 : ℝ)

namespace NilpotentLieFiltration

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

theorem associatedGradedBasis_homogeneous_brackets :
    BasisHomogeneousBrackets (F.associatedGradedBasis b w hlayers) w := by
  intro i j k hk
  rw [F.associatedGradedBasis_bracket b w hlayers, if_neg (Ne.symm hk)]

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ : Type*} [Fintype σ]

@[simp] theorem weightedBasis_inl_base [DecidableEq σ] (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (i : σ) : (weightedBasis w d hw (Sum.inl i)).val.base = Pi.single i 1 := by
  classical
  unfold weightedBasis
  erw [Basis.map_apply]
  rw [Basis.prod_apply]
  simp [weightedCoordinatesEquiv]
  rfl

@[simp] theorem weightedBasis_inl_polynomial (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (i : σ) :
    (weightedBasis w d hw (Sum.inl i)).val.polynomial = 0 := by
  unfold weightedBasis
  erw [Basis.map_apply]
  rw [Basis.prod_apply]
  simp [weightedCoordinatesEquiv]
  rfl

@[simp] theorem weightedBasis_inr_base (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    (weightedBasis w d hw (Sum.inr a)).val.base = 0 := by
  unfold weightedBasis
  erw [Basis.map_apply]
  rw [Basis.prod_apply]
  simp [weightedCoordinatesEquiv]
  rfl

@[simp] theorem weightedBasis_inr_polynomial (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    (weightedBasis w d hw (Sum.inr a)).val.polynomial = monomial a.val 1 := by
  classical
  apply MvPolynomial.ext
  intro t
  by_cases ht : Finsupp.weight w t < d
  · rw [← weightedBasis_repr_inr w d hw _ ⟨t, ht⟩]
    simp [Basis.repr_self, Finsupp.single_apply, coeff_monomial, Subtype.ext_iff]
  · have hcoeff : (weightedBasis w d hw (Sum.inr a)).val.polynomial.coeff t = 0 := by
      by_contra hn
      have hh := (weightedBasis w d hw (Sum.inr a)).property.2 (mem_support_iff.mpr hn)
      change Finsupp.weight w t + 1 ≤ d at hh
      omega
    rw [hcoeff, coeff_monomial]
    have hne : a.val ≠ t := by
      intro he
      exact ht (he ▸ a.property)
    simp [hne]

theorem single_direction_derivative [DecidableEq σ] (i : σ)
    (P : MvPolynomial σ ℚ) : scalarDirectionalDerivative (Pi.single i 1) P = pderiv i P := by
  classical
  simp [scalarDirectionalDerivative_apply, Pi.single_apply]

omit [Fintype σ] in
theorem coeff_pderiv_monomial_grade (w : σ → ℕ) (d : ℕ)
    (i : σ) (a c : {a : σ →₀ ℕ | Finsupp.weight w a < d})
    (h : d - Finsupp.weight w c.val ≠ w i + (d - Finsupp.weight w a.val)) :
    (pderiv i (monomial a.val (1 : ℚ))).coeff c.val = 0 := by
  classical
  have hne : a.val ≠ c.val + Finsupp.single i 1 := by
    intro he
    have hh := congrArg (Finsupp.weight w) he
    simp only [map_add, Finsupp.weight_single, one_smul] at hh
    have ha : Finsupp.weight w a.val < d := a.property
    have hc : Finsupp.weight w c.val < d := c.property
    omega
  rw [coeff_pderiv, coeff_monomial, if_neg hne, zero_mul]

theorem weightedBasis_homogeneous_brackets (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) :
    BasisHomogeneousBrackets (weightedBasis w d hw) (weightedBasisGrade w d) := by
  classical
  intro i j k hk
  cases k with
  | inl k =>
      rw [weightedBasis_repr_inl]
      rfl
  | inr c =>
      rw [weightedBasis_repr_inr]
      change (scalarDirectionalDerivative (weightedBasis w d hw i).val.base
        (weightedBasis w d hw j).val.polynomial -
        scalarDirectionalDerivative (weightedBasis w d hw j).val.base
          (weightedBasis w d hw i).val.polynomial).coeff c.val = 0
      cases i with
      | inl i =>
          cases j with
          | inl j => simp
          | inr a =>
              simp only [weightedBasis_inl_base, weightedBasis_inr_polynomial,
                weightedBasis_inr_base, weightedBasis_inl_polynomial,
                scalarDirectionalDerivative_direction_zero, sub_zero,
                single_direction_derivative]
              exact coeff_pderiv_monomial_grade w d i a c hk
      | inr a =>
          cases j with
          | inl i =>
              simp only [weightedBasis_inl_base, weightedBasis_inr_polynomial,
                weightedBasis_inr_base, weightedBasis_inl_polynomial,
                scalarDirectionalDerivative_direction_zero, zero_sub,
                single_direction_derivative, coeff_neg, neg_eq_zero]
              exact coeff_pderiv_monomial_grade w d i a c (by
                simpa only [weightedBasisGrade_inl, weightedBasisGrade_inr, Nat.add_comm] using hk)
          | inr b => simp

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RelativeSquarePolynomial
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

noncomputable def normalizedRelativeSubmodule : Submodule ℚ (F.adaptedLieSubalgebra w) :=
  (F.shiftedAdaptedIdeal w).toSubmodule ⊓ (F.layer 2).comap (F.adaptedCoefficientMap w 0)

include hw in
theorem normalizedRelative_coefficient_mem_two (p : F.normalizedRelativeSubmodule w) (α : σ →₀ ℕ) :
    coefficients p.val.val α ∈ F.layer 2 := by
  by_cases hα : α = 0
  · subst α
    exact p.property.2
  · exact F.antitone (by have := positive_weight_of_ne_zero w hw hα; omega) (p.property.1 α)

noncomputable def relativeSquarePolynomial (p : F.normalizedRelativeSubmodule w) :
    VectorPolynomial σ ℚ F.squareLieSubalgebra :=
  restrictCoefficients F.squareLieSubalgebra.toSubmodule (pair p.val.val 0) (by
    intro α
    rw [coefficients_pair, map_zero, Finsupp.zero_apply]
    apply (F.mem_squareLieSubalgebra _).mpr
    simpa only [sub_zero] using F.normalizedRelative_coefficient_mem_two w hw p α)

theorem relativeSquarePolynomial_coefficient (p : F.normalizedRelativeSubmodule w) (α : σ →₀ ℕ) :
    (coefficients (F.relativeSquarePolynomial w hw p) α : L × L) = (coefficients p.val.val α, 0) := by
  rw [relativeSquarePolynomial, coefficients_restrictCoefficients, coefficients_pair, map_zero,
    Finsupp.zero_apply]

theorem relativeSquarePolynomial_adapted (p : F.normalizedRelativeSubmodule w) :
    F.relativeSquarePolynomial w hw p ∈ F.squareFiltration.adaptedLieSubalgebra w := by
  intro α
  change (coefficients (F.relativeSquarePolynomial w hw p) α : L × L) ∈ F.squareLayer (Finsupp.weight w α)
  rw [F.relativeSquarePolynomial_coefficient]
  refine ⟨p.val.property α, (F.layer _).zero_mem, ?_⟩
  change coefficients p.val.val α - 0 ∈ F.layer (Finsupp.weight w α + 1)
  rw [sub_zero]
  exact p.property.1 α

noncomputable def relativeSquareLift :
    F.normalizedRelativeSubmodule w →ₗ[ℚ] F.squareFiltration.adaptedLieSubalgebra w where
  toFun p := ⟨F.relativeSquarePolynomial w hw p, F.relativeSquarePolynomial_adapted w hw p⟩
  map_add' p q := by
    apply Subtype.ext
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    change coefficients (F.relativeSquarePolynomial w hw (p + q)) α =
      coefficients (F.relativeSquarePolynomial w hw p + F.relativeSquarePolynomial w hw q) α
    rw [map_add, Finsupp.add_apply]
    apply Subtype.ext
    change (coefficients (F.relativeSquarePolynomial w hw (p + q)) α : L × L) =
      (coefficients (F.relativeSquarePolynomial w hw p) α : L × L) +
        (coefficients (F.relativeSquarePolynomial w hw q) α : L × L)
    rw [F.relativeSquarePolynomial_coefficient, F.relativeSquarePolynomial_coefficient,
      F.relativeSquarePolynomial_coefficient]
    change (coefficients (p.val.val + q.val.val) α, 0) = _
    simp only [map_add, Finsupp.add_apply, Prod.mk_add_mk, add_zero]
  map_smul' c p := by
    apply Subtype.ext
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    change coefficients (F.relativeSquarePolynomial w hw (c • p)) α =
      coefficients (c • F.relativeSquarePolynomial w hw p) α
    rw [map_smul, Finsupp.smul_apply]
    apply Subtype.ext
    change (coefficients (F.relativeSquarePolynomial w hw (c • p)) α : L × L) =
      c • (coefficients (F.relativeSquarePolynomial w hw p) α : L × L)
    rw [F.relativeSquarePolynomial_coefficient, F.relativeSquarePolynomial_coefficient]
    change (coefficients (c • p.val.val) α, 0) = _
    simp only [map_smul, Finsupp.smul_apply, Prod.smul_mk, smul_zero]

noncomputable def relativeSquareSymbolMap :
    F.normalizedRelativeSubmodule w →ₗ[ℚ] F.squareFiltration.PolynomialSymbol w :=
  (F.squareFiltration.polynomialSymbolMap w).toLinearMap.comp (F.relativeSquareLift w hw)

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


