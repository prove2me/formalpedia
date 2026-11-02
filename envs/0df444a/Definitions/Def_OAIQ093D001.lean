-- Prove2me | Definitions.Def_OAIQ093D001
-- name    : OAIQ093D001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T15:59:49.631622+00:00
-- url     : https://prove2.me/theorems/10363eaf-66ec-4caa-8198-b08b1960fb9a
-- title:
--   Definitions bundle OAIQ093D001 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 294 declarations of OpenAI's Lean: 110 definitions, 17 inductive types or structures, 9 instances and 158 theorems. The definitions and types are `GeneratesNS.FreshTopology`, `GeneratesNS.GeneratesWithParam`, `GeneratesNS.Theorem3_1_Input`, `GeneratesNS.countElemOrInv`, `GeneratesNS.e_i_regular_helper`, `GeneratesNS.gamma_m_helper`, `GeneratesNS.list_len_n`, `GeneratesNS.three_two_B_n`, `GeneratesNS.three_two_S_n`, `Group.Generators.IsGeodesic`, `Group.Generators.groupNorm`, `Group.Generators.lift`, `Group.Generators.normedGroup`, `Group.Generators.wordLength`, `Group.Generators.wordProd`, `HnEpsData`, `HnEpsData.H_n_eps`, `HnEpsData.HnData`, `HnEpsData.Theorem3_8_Data`, `HnEpsData.c'`, `HnEpsData.f`, `HnEpsData.swap_le`, `HnEpsData.theorem_3_8_h_n`, `HnEpsData.theorem_3_8_h_n_list`, `IsoData`, `KroneckerPow`, `KroneckerPow_exists`, `KroneckerPow_single`, `OAI.ChromaticCyclic.CyclicSeries.append`, `OAI.ChromaticCyclic.CyclicSeries.comap`, `OAI.ChromaticCyclic.CyclicSeries.cons`, `OAI.ChromaticCyclic.CyclicSeries.map`, `OAI.ChromaticCyclic.CyclicSeries.refl`, `OAI.ChromaticCyclic.CyclicSeries.tail`, `OAI.ChromaticCyclic.CyclicStep.factorComap`, `OAI.ChromaticCyclic.CyclicStep.factorMap`, `OAI.PolycyclicRecognition.AbelianRealSpace`, `OAI.PolycyclicRecognition.ActionDepth`, `OAI.PolycyclicRecognition.AffinePolynomialPoint`, `OAI.PolycyclicRecognition.AffinePolynomialPoint.polynomialMap` and 87 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `CyclicSeries_Length`, `GrowthZero`, `MatrixSubsum`, `PolycyclicRecognition_Algebra_AbelianRealSpace`, `PolycyclicRecognition_Algebra_ActionDepth`, `PolycyclicRecognition_Algebra_AlgebraGroupTangent`, `PolycyclicRecognition_Algebra_AlternatingPolynomialCoordinates`, `PolycyclicRecognition_Algebra_BracketWords`, `PolycyclicRecognition_Algebra_ComplexificationRealForm`, `PolycyclicRecognition_Algebra_FiniteBracketWords`, `PolycyclicRecognition_Algebra_FiniteWordBases`, `PolycyclicRecognition_Algebra_HomogeneousGenerators`, `PolycyclicRecognition_Algebra_LinearActionFiltration`, `PolycyclicRecognition_Algebra_NormalizedWordBrackets`, `PolycyclicRecognition_Algebra_QuotientTrace`, `PolycyclicRecognition_Algebra_RealTorusAction`, `PolycyclicRecognition_Algebra_WordBasisCoordinates`, `PolycyclicRecognition_Algebra_WordExponents`, `PolycyclicRecognition_Analysis_AffinePolynomialTopology`, `PolycyclicRecognition_Analysis_BoundedPathGrowth`, `PolycyclicRecognition_Analysis_CompactGeneratingBalls`, `PolycyclicRecognition_Analysis_OccupationSampling`, `PolycyclicRecognition_Analysis_ProfileParameterContinuity`, `PolycyclicRecognition_Analysis_RescaledProfiles`, `PolycyclicRecognition_Analysis_SectionProbeReparametrization`, `PolycyclicRecognition_Analysis_SupportNorm`, `PolycyclicRecognition_Analysis_SupportTemplates`, `PolycyclicRecognition_Geometry_BoundaryMapFamily`, `PolycyclicRecognition_Geometry_BoundaryVolumeComparison`, `PolycyclicRecognition_Geometry_CanonicalHeight`, `PolycyclicRecognition_Geometry_CartanActualProbeProfiles`, `PolycyclicRecognition_Geometry_CartanCanonicalProfiles`, `PolycyclicRecognition_Geometry_CartanCoverRootDistortion`, `PolycyclicRecognition_Geometry_CartanDecomposition`, `PolycyclicRecognition_Geometry_CartanFactorModel`, `PolycyclicRecognition_Geometry_CartanFixedProfileMeasurable`, `PolycyclicRecognition_Geometry_CartanHeightRays`, `PolycyclicRecognition_Geometry_CartanModel`, `PolycyclicRecognition_Geometry_CartanRootWidths`, `PolycyclicRecognition_Geometry_CartanSampledProbeFrames`, `PolycyclicRecognition_Geometry_CartanSemidirectCover`, `PolycyclicRecognition_Geometry_CartanSupportData`, `PolycyclicRecognition_Geometry_CartanTrace`, `PolycyclicRecognition_Geometry_CartanWeightDerivation`, `PolycyclicRecognition_Geometry_CartanWeightDilation`, `PolycyclicRecognition_Geometry_CartanWeights`, `PolycyclicRecognition_Geometry_CartanWordBasis`, `PolycyclicRecognition_Geometry_CartanWordModel`, `PolycyclicRecognition_Geometry_CartanWordTrace`, `PolycyclicRecognition_Geometry_ComplexAdjointKernel`, `PolycyclicRecognition_Geometry_ComplexAdjointWeights`, `PolycyclicRecognition_Geometry_ComplexCartanQuotient`, `PolycyclicRecognition_Geometry_ComplexCartanRotations`, `PolycyclicRecognition_Geometry_ComplexNilradical`, `PolycyclicRecognition_Geometry_ComplexRotationTorus`, `PolycyclicRecognition_Geometry_ComplexifiedCartan`, `PolycyclicRecognition_Geometry_ConjugateCartanWeights`, `PolycyclicRecognition_Geometry_LieExponential`, `PolycyclicRecognition_Geometry_NilpotentLieModel`, `PolycyclicRecognition_Geometry_RealCartanQuotient`, `PolycyclicRecognition_Geometry_RealCartanRotations`, `PolycyclicRecognition_Geometry_RealRotationTorus`, `PolycyclicRecognition_Geometry_SemidirectProductTopology`, `PolycyclicRecognition_Geometry_TriangularHeight`, `PolycyclicRecognition_Geometry_TriangularPrimary`, `PolycyclicRecognition_Geometry_UniversalAllScaleCartanProfiles`, `PolycyclicRecognition_Geometry_WeightBasisTrace`, `PolycyclicRecognition_Geometry_WeightedColumnBasis`, `PolycyclicRecognition_Lattices_CartanNilshadow`, `Representation`, `RhoAbelian`, `TendstoNhdsMul`, `ThreeTwoGrowth`, `ToMathlib_Analysis_Matrix_UnitaryAux`, `ToMathlib_Data_List_Finite`, `ToMathlib_LinearAlgebra_Matrix_Det`, `ToMathlib_LinearAlgebra_Matrix_ToMatrix`, `UnitaryGromov`, `Unitary_Basic`, `Unitary_HnEps`, `Unitary_HnLowerBound`, `Unitary_Words`, `Vendor_Carleson_ToMathlib_Analysis_Convolution`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D006`, `OAIQ093D007`, `OAIQ093D008`, `OAIQ093D009`, `OAIQ093D010` and `OAIQ093D011`; the statements `GeneratesNS.exists_theorem_3_1_input`, `GeneratesNS.theorem_3_1`, `GeneratesNS.three_two_S_n_generates`, `HnEpsData.H_n_contradiction`, `HnEpsData.central_trivial_virtually_abelian`, `KroneckerPow_pos`, `OAI.PolycyclicRecognition.NilpotentLieModel.group_nilpotent`, `OAI.PolycyclicRecognition.cartan_unitary_reduced_vanishing`, `centralizer_iso`, `compact_lie_virtually_abelian` and `int_matrix_unipotent`; the proofs of `HnEpsData.H_n_contradiction`, `HnEpsData.central_trivial_virtually_abelian`, `KroneckerPow_pos`, `centralizer_iso`, `compact_lie_virtually_abelian` and `int_matrix_unipotent`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PolycyclicRecognition

section
-- module Solutions.OAIQ093_PR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ093_PR.CyclicSeries_Length
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cyclic subnormal series and their minimum lengths in finite p-groups. -/

namespace ChromaticCyclic

namespace CyclicStep
variable {G A : Type*} [Group G] [Group A] {H K : Subgroup G}

theorem normal_map (s : CyclicStep H K) (f : G →* A) :
    ((H.map f).subgroupOf (K.map f)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    ((Subgroup.map_mono
      ((Subgroup.normal_subgroupOf_iff_le_normalizer s.le).mp s.normal)).trans
      (H.le_normalizer_map f))

def factorMap (s : CyclicStep H K) (f : G →* A) :
    letI := s.normal
    letI := s.normal_map f
    K ⧸ H.subgroupOf K →* K.map f ⧸ (H.map f).subgroupOf (K.map f) := by
  letI := s.normal
  letI := s.normal_map f
  exact QuotientGroup.map _ _ (f.subgroupMap K) (by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

theorem factorMap_surjective (s : CyclicStep H K) (f : G →* A) :
    letI := s.normal
    letI := s.normal_map f
    Function.Surjective (s.factorMap f) := by
  let := s.normal
  let := s.normal_map f
  exact QuotientGroup.map_surjective_of_surjective _ _ _
    (Quotient.mk''_surjective.comp (f.subgroupMap_surjective K)) _

protected theorem map (s : CyclicStep H K) (f : G →* A) :
    CyclicStep (H.map f) (K.map f) := by
  refine ⟨Subgroup.map_mono s.le, s.normal_map f, ?_⟩
  let := s.normal
  let := s.normal_map f
  let := s.cyclic
  exact isCyclic_of_surjective (s.factorMap f) (s.factorMap_surjective f)

theorem normal_comap (s : CyclicStep H K) (f : A →* G) :
    ((H.comap f).subgroupOf (K.comap f)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    ((Subgroup.comap_mono
      ((Subgroup.normal_subgroupOf_iff_le_normalizer s.le).mp s.normal)).trans
      (H.le_normalizer_comap f))

def factorComap (s : CyclicStep H K) (f : A →* G) :
    letI := s.normal
    letI := s.normal_comap f
    K.comap f ⧸ (H.comap f).subgroupOf (K.comap f) →* K ⧸ H.subgroupOf K := by
  letI := s.normal
  letI := s.normal_comap f
  let g : K.comap f →* K := (f.domRestrict (K.comap f)).codRestrict _ (fun x => x.property)
  exact QuotientGroup.map _ _ g (by intro x hx; exact hx)

theorem factorComap_injective (s : CyclicStep H K) (f : A →* G) :
    letI := s.normal
    letI := s.normal_comap f
    Function.Injective (s.factorComap f) := by
  let := s.normal
  let := s.normal_comap f
  apply (s.factorComap f).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
  change (↑(⟨f x.val, x.property⟩ : K) : K ⧸ H.subgroupOf K) = 1 at hx
  have hx' := (QuotientGroup.eq_one_iff (⟨f x.val, x.property⟩ : K)).mp hx
  change (↑x : K.comap f ⧸ (H.comap f).subgroupOf (K.comap f)) = 1
  exact (QuotientGroup.eq_one_iff _).mpr hx'

protected theorem comap (s : CyclicStep H K) (f : A →* G) :
    CyclicStep (H.comap f) (K.comap f) := by
  refine ⟨Subgroup.comap_mono s.le, s.normal_comap f, ?_⟩
  let := s.normal
  let := s.normal_comap f
  let := s.cyclic
  exact isCyclic_of_injective (s.factorComap f) (s.factorComap_injective f)

end CyclicStep

namespace CyclicSeries
variable {G A : Type*} [Group G] [Group A] {H K L : Subgroup G} {n : ℕ}

def refl (H : Subgroup G) : CyclicSeries H H 0 where
  group := fun _ => H
  first := rfl
  last := rfl
  step := by omega

def cons (s : CyclicStep H K) (c : CyclicSeries K L n) : CyclicSeries H L (n + 1) where
  group := fun | 0 => H | i + 1 => c.group i
  first := rfl
  last := c.last
  step := by
    rintro (_ | i) hi
    · simpa [c.first] using s
    · exact c.step i (by omega)

def map (c : CyclicSeries H K n) (f : G →* A) :
    CyclicSeries (H.map f) (K.map f) n where
  group := fun i => (c.group i).map f
  first := congrArg (Subgroup.map f) c.first
  last := congrArg (Subgroup.map f) c.last
  step := fun i hi => (c.step i hi).map f

def comap (c : CyclicSeries H K n) (f : A →* G) :
    CyclicSeries (H.comap f) (K.comap f) n where
  group := fun i => (c.group i).comap f
  first := congrArg (Subgroup.comap f) c.first
  last := congrArg (Subgroup.comap f) c.last
  step := fun i hi => (c.step i hi).comap f

def tail (c : CyclicSeries H K (n + 1)) : CyclicSeries (c.group 1) K n where
  group := fun i => c.group (i + 1)
  first := rfl
  last := c.last
  step := fun i hi => c.step (i + 1) (by omega)

end CyclicSeries



namespace CyclicSeries
variable {G : Type*} [Group G] {H K L : Subgroup G} {n m : ℕ}

def append (c : CyclicSeries H K n) (d : CyclicSeries K L m) :
    CyclicSeries H L (n + m) := by
  induction n generalizing H with
  | zero =>
    have h : H = K := c.first.symm.trans c.last
    subst H
    simpa using d
  | succ n ih =>
    have s : CyclicStep H (c.group 1) := by
      simpa only [c.first] using c.step 0 (Nat.succ_pos n)
    simpa only [Nat.succ_add, Nat.add_succ] using cons s (ih c.tail)

end CyclicSeries

end ChromaticCyclic

end OAI
end

section
-- module Solutions.OAIQ093_PR.TendstoNhdsMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Products of one-sided limits

Staging ground for `Filter.TendstoNhdsWithinIoi.mul`, the two-function analogue of the existing
`Filter.TendstoNhdsWithinIoi.const_mul` / `Filter.TendstoNhdsWithinIoi.mul_const` lemmas in
`Mathlib.Topology.Algebra.Monoid`. Intended to be upstreamed into that file later.
-/


open Filter Topology Set

/-- A `squeeze_zero` landing in `𝓝[>] 0` rather than `𝓝 0`: if `0 < f ≤ g` eventually and `g`
tends to `0`, then `f` tends to `0` from the right. Companion to `squeeze_zero'` (which only
concludes `Tendsto f t₀ (𝓝 0)`). -/
theorem squeeze_zero_nhdsGT {α : Type*} {f g : α → ℝ} {t₀ : Filter α}
    (hf : ∀ᶠ t in t₀, 0 < f t) (hft : ∀ᶠ t in t₀, f t ≤ g t)
    (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝[>] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (squeeze_zero' (hf.mono fun _ h => h.le) hft g0) (hf.mono fun _ h => Set.mem_Ioi.mpr h)
end

section
-- module Solutions.OAIQ093_PR.ToMathlib_LinearAlgebra_Matrix_ToMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Matrices of bilinear maps

General-purpose material extracted from the Gromov development, destined for mathlib.
-/


/-- Reindexing both bases of a `LinearMap.toMatrix₂` by an equiv turns it into a `submatrix`. -/
theorem LinearMap.toMatrix₂_reindex {R M ι κ : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι R M) (e : ι ≃ κ) (B : M →ₗ[R] M →ₗ[R] R) :
    LinearMap.toMatrix₂ (b.reindex e) (b.reindex e) B
      = (LinearMap.toMatrix₂ b b B).submatrix e.symm e.symm := by
  ext i j
  simp [LinearMap.toMatrix₂_apply, Module.Basis.reindex_apply, Matrix.submatrix_apply]
end

section
-- module Solutions.OAIQ093_PR.ToMathlib_LinearAlgebra_Matrix_Det
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Determinants of matrices of bilinear forms

General-purpose material extracted from the Gromov development, destined for mathlib.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

open scoped Finset
open scoped Pointwise

/-- The determinant of `LinearMap.toMatrix₂` is invariant under reindexing the basis. -/
theorem LinearMap.toMatrix₂_reindex_det {R M ι κ : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι R M) (e : ι ≃ κ) (B : M →ₗ[R] M →ₗ[R] R) :
    (LinearMap.toMatrix₂ (b.reindex e) (b.reindex e) B).det
      = (LinearMap.toMatrix₂ b b B).det := by
  rw [LinearMap.toMatrix₂_reindex, Matrix.det_submatrix_equiv_self]

/-- For two bases `b`, `c` of the same real vector space, the `LinearMap.toMatrix₂`
determinants differ by a fixed positive constant `K = (b.reindex e).det c)²` (the square of the
change-of-basis determinant), **uniformly in the bilinear form** `B`. In particular the ratio of
two such determinants (e.g. at different scales) is basis-independent. -/
theorem LinearMap.toMatrix₂_det_basis_change {M ι κ : Type*} [AddCommGroup M] [Module ℝ M]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℝ M) (c : Module.Basis κ ℝ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ B : M →ₗ[ℝ] M →ₗ[ℝ] ℝ,
      (LinearMap.toMatrix₂ c c B).det = K * (LinearMap.toMatrix₂ b b B).det := by
  let e := b.indexEquiv c
  refine ⟨((b.reindex e).det ⇑c) ^ 2, ?_, fun B => ?_⟩
  · have hne : (b.reindex e).det ⇑c ≠ 0 := by
      rw [Module.Basis.det_apply]
      exact left_ne_zero_of_mul_eq_one (by
        rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one])
    positivity
  · rw [← LinearMap.toMatrix₂_reindex_det b e B,
        ← LinearMap.toMatrix₂_mul_basis_toMatrix (b₁ := b.reindex e) (b₂ := b.reindex e) c c B,
        Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← Module.Basis.det_apply]
    ring
end

section
-- module Solutions.OAIQ093_PR.Vendor_Carleson_ToMathlib_Analysis_Convolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Vendored from the Carleson project

Port of the part of `Carleson/ToMathlib/Analysis/Convolution.lean` from
<https://github.com/fpvandoorn/carleson> (branch `young-add-group`) that is needed for
`ConvolutionExists.of_memLp_memLp`.
-/

set_option linter.style.header false

section

open scoped Convolution

namespace MeasureTheory

universe u𝕜 uG uE uE' uF

variable {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF}

variable [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup F]
  {f : G → E} {g : G → E'}

variable [NontriviallyNormedField 𝕜]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F]
variable {L : E →L[𝕜] E' →L[𝕜] F}

variable [MeasurableSpace G]

/-- This implies both of the following theorems `ConvolutionExists.of_memLp_memLp` and
`enorm_convolution_le_eLpNorm_mul_eLpNorm`. -/
lemma lintegral_enorm_convolution_integrand_le_eLpNorm_mul_eLpNorm [AddGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G} [SFinite μ] [μ.IsNegInvariant]
    [μ.IsAddLeftInvariant] {p q : ENNReal} (hpq : p.HolderConjugate q)
    (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ ‖f x‖ * ‖g y‖)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (x₀ : G) :
    ∫⁻ a, ‖L (f a) (g (x₀ - a))‖ₑ ∂μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  rw [eLpNorm_comp_measurePreserving (p := q) hg (μ.measurePreserving_sub_left x₀) |>.symm]
  replace hpq : 1 / 1 = 1 / p + 1 / q := by
    simpa using (ENNReal.HolderConjugate.inv_add_inv_eq_one p q).symm
  replace hpq : ENNReal.HolderTriple p q 1 := ⟨by simpa [eq_comm] using hpq⟩
  have hg' : AEStronglyMeasurable (g <| x₀ - ·) μ :=
    hg.comp_quasiMeasurePreserving <| quasiMeasurePreserving_sub_left μ x₀
  have hL' : ∀ᵐ (x : G) ∂μ, ‖L (f x) (g (x₀ - x))‖ ≤ (1 : NNReal) * ‖f x‖ * ‖g (x₀ - x)‖ := by
    simpa using Filter.Eventually.of_forall (fun x ↦ hL x (x₀ - x))
  simpa [eLpNorm, eLpNorm', Function.comp_def] using
    eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm hf hg' (L ·) _ hL' (hpqr := hpq)

/-- If `MemLp f p μ` and `MemLp g q μ`, where `p` and `q` are Hölder conjugates, then the
convolution of `f` and `g` exists everywhere. -/
theorem ConvolutionExists.of_memLp_memLp [AddGroup G] [MeasurableAdd₂ G]
    [MeasurableNeg G] (μ : Measure G) [SFinite μ] [μ.IsNegInvariant] [μ.IsAddLeftInvariant]
    [μ.IsAddRightInvariant] {p q : ENNReal} (hpq : p.HolderConjugate q)
    (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ ‖f x‖ * ‖g y‖) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hfp : MemLp f p μ) (hgq : MemLp g q μ) :
    ConvolutionExists f g L μ := by
  refine fun x ↦ ⟨AEStronglyMeasurable.convolution_integrand_snd L hf hg x, ?_⟩
  apply lt_of_le_of_lt (lintegral_enorm_convolution_integrand_le_eLpNorm_mul_eLpNorm hpq hL hf hg x)
  exact ENNReal.mul_lt_top hfp.eLpNorm_lt_top hgq.eLpNorm_lt_top

end MeasureTheory
end
end

section
-- module Solutions.OAIQ093_PR.ToMathlib_Data_List_Finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finiteness of lists of bounded length

General-purpose material extracted from the Gromov development, destined for mathlib.
-/


@[expose]
instance simple_finite_list {G: Type*} (P: Finset G) (n: ℕ): Finite { l: List P | l.length ≤ n } := by
  apply List.finite_length_le
end

section
-- module Solutions.OAIQ093_PR.MatrixSubsum
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Eigenvalues of integer matrices and unipotence

That an integer matrix whose orbit grows polynomially has all eigenvalues of norm `1`, and is
therefore unipotent after passing to a power.

Root of the `Gromov.MatrixSubsum` hierarchy.
-/


open scoped Finset
open scoped Pointwise

lemma char_nonzero {d: ℕ} {K: Type*} [Field K] (A: (Matrix (Fin d) (Fin d) K)): A.charpoly ≠ 0 := by
  by_contra!
  have monic := A.charpoly_monic
  simp [this] at monic

lemma eigen_nonzero {d: ℕ} (A: (Matrix (Fin d) (Fin d) ℤ)ˣ): ∀ (k : Module.End.Eigenvalues (A.val.map (Int.castRingHom ℂ)).toLin'), k.val ≠ 0 := by
  intro k
  by_contra!
  have eigen_zero := LinearMap.hasEigenvalue_zero_tfae ((A.val.map (Int.castRingHom ℂ)).toLin')
  have det_zero := (eigen_zero.out 0 3).mp
  have has_k := k.prop
  conv at has_k =>
    lhs
    equals k.val => rfl


  specialize det_zero (by
    simp at this
    simp [this] at has_k
    exact has_k
  )
  have a_det := Matrix.GeneralLinearGroup.det_ne_zero A
  simp at det_zero
  conv at det_zero =>
    lhs
    arg 1
    equals (A.val).map (Int.castRingHom ℂ) =>
      simp
  rw [← RingHom.mapMatrix_apply] at det_zero
  simp at det_zero
  apply_fun (fun a => (Int.castRingHom ℂ) a) at a_det
  . conv at a_det =>
      rhs
      simp
    rw [RingHom.map_det] at a_det
    simp at a_det
    contradiction
  . simp
    exact Int.cast_injective

@[expose]
def KroneckerPow_exists {d: ℕ} (A: (Matrix (Fin d) (Fin d) ℤ)ˣ) (k: Module.End.Eigenvalues (A.val.map (Int.castRingHom ℂ)).toLin') (eigen_one_complex: ∀ k : Module.End.Eigenvalues ((A.val.map (Int.castRingHom ℂ ))).toLin', ‖k.val‖ = 1) := Polynomial.pow_eq_one_of_mahlerMeasure_eq_one (by
  rw [Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  rw [Polynomial.Monic.leadingCoeff]
  .
    simp
    apply Multiset.prod_eq_one
    intro x hx
    simp at hx
    obtain ⟨a, ⟨charpoly_nonzero, a_root⟩, x_eq⟩ := hx
    rw [← x_eq]
    simp
    apply le_of_eq
    apply eigen_one_complex ⟨a, ?_⟩
    conv =>
      equals Module.End.HasEigenvalue ((Matrix.toLin' ((A.val).map ⇑(Int.castRingHom ℂ)))) a => rfl
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
    simp
    rw [← Matrix.charpoly_map] at a_root
    simpa using a_root

  . apply Polynomial.Monic.map
    apply Matrix.charpoly_monic
) (by
  apply eigen_nonzero
) (by
  simp

  have k_prop := k.property
  conv at k_prop =>
    equals Module.End.HasEigenvalue ((A.val).map ⇑(Int.castRingHom ℂ)).toLin' (↑k) =>
      rfl
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly] at k_prop

  have k_mem_roots: ↑k.val ∈ ((A.val).map ⇑(Int.castRingHom ℂ)).toLin'.charpoly.rootSet ℂ := by
    simp [Polynomial.mem_rootSet]
    refine ⟨char_nonzero _, ?_⟩
    simp at k_prop
    exact k_prop


  refine ⟨?_, ?_⟩
  .
    rw [← Matrix.charpoly_map]
    apply char_nonzero
  .
    rw [← Matrix.charpoly_map]
    rw [Polynomial.mem_rootSet] at k_mem_roots
    have foo := k_mem_roots.2
    simp at foo
    exact foo
) (z := k) (p := A.val.charpoly)

@[expose]
noncomputable def KroneckerPow_single {d: ℕ} (A: (Matrix (Fin d) (Fin d) ℤ)ˣ) (k: Module.End.Eigenvalues (A.val.map (Int.castRingHom ℂ)).toLin') (eigen_one_complex: ∀ k : Module.End.Eigenvalues ((A.val.map (Int.castRingHom ℂ ))).toLin', ‖k.val‖ = 1) :=
  (KroneckerPow_exists A k eigen_one_complex).choose

@[expose]
noncomputable def KroneckerPow {d: ℕ} (A: (Matrix (Fin d) (Fin d) ℤ)ˣ) (eigen_one_complex: ∀ k : Module.End.Eigenvalues ((A.val.map (Int.castRingHom ℂ ))).toLin', ‖k.val‖ = 1) :=
  ∏ (k : Module.End.Eigenvalues (A.val.map (Int.castRingHom ℂ )).toLin'), (KroneckerPow_single A k eigen_one_complex)


open scoped Pointwise Finset
end

section
-- module Solutions.OAIQ093_PR.ToMathlib_Analysis_Matrix_UnitaryAux
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Unitary matrices: helper lemmas

General-purpose material extracted from the Gromov development, destined for mathlib.
-/


structure IsoData {n: ℕ} {G: Subgroup (Matrix.unitaryGroup (Fin n) ℂ)} (g: G) where
  a : ℕ
  b: ℕ
  ha: a ≠ 0
  hb: b ≠ 0
  hab: a + b = n
  A: Subgroup (Matrix.unitaryGroup (Fin a) ℂ)
  B: Subgroup (Matrix.unitaryGroup (Fin b) ℂ)
  iso: Subgroup.centralizer {g.val} ≃* A × B
end

section
-- module Solutions.OAIQ093_PR.Unitary_Basic
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Subgroups of the unitary group

Properness and compactness of the unitary group, the transfer of polynomial growth along a
group isomorphism, and the distance estimate `small_dist_matrix`.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


-- Lemma 3.29 (Shrinking Conjugators)
lemma shrinking_conjugators (n : ℕ) (g h : Matrix.unitaryGroup (Fin n) ℂ) :
  ‖⁅g, h⁆.val - 1‖ ≤ 2 * ‖g.val - 1‖ * ‖h.val - 1‖ := by
  dsimp only [Bracket.bracket]
  calc
    _ = ‖((g* h).val - (h * g).val) * (g⁻¹ * h⁻¹)‖ := by
      rw [sub_mul]
      repeat rw [← Submonoid.coe_mul]
      conv =>
        rhs
        arg 1
        rhs
        arg 1
        equals 1 => group
      repeat rw [← mul_assoc]
      simp
    _ = ‖((g* h).val - (h * g).val)‖ := by
      rw [ ← Submonoid.coe_mul, CStarRing.norm_mul_coe_unitary]
    _ = ‖(g* h).val - g - h + 1 - ((h*g).val - h - g + 1)‖ := by abel_nf
    _ = ‖(g.val - 1)*(h.val - 1) - (h.val - 1)*(g.val - 1)‖ := by
      conv =>
        rhs
        repeat rw [mul_sub]
        repeat rw [sub_mul]
      simp
      abel_nf
    _ ≤ ‖(g.val - 1)*(h.val - 1)‖ + ‖(h.val - 1)*(g.val - 1)‖ := norm_sub_le _ _
    _ ≤ 2 * ‖g.val - 1‖ * ‖h.val - 1‖ := by
      linarith [Matrix.l2_opNorm_mul (g.val - 1) (h.val - 1),
                Matrix.l2_opNorm_mul (h.val - 1) (g.val - 1)]


abbrev diag_unitary (c : ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun _ => c)

lemma small_dist_matrix (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ (∀ h : Matrix (Fin n) (Fin n) ℂ, h.det = 1 → ∀ c : ℂ, ‖c‖ = 1 → h = diag_unitary c n → (‖h - 1‖ < C) → c = 1) := by


  have nezero_n : NeZero n := ⟨by omega⟩
  let dists := (fun (x : ℂ) => (‖x - 1‖ : ℝ)) '' ((Units.val '' (rootsOfUnity n ℂ).carrier \ {1}))

  -- TODO - why can't we combine these into a single line?
  have foo := Set.Finite.exists_minimal (s := dists) ?_ ?_
  obtain ⟨min_dist, ⟨h_min, h_min_prop⟩⟩ := foo
  · refine ⟨min_dist, ?_, ?_⟩
    · simp only [dists, Set.mem_image] at h_min
      obtain ⟨x, x_mem, min_dist_eq⟩ := h_min
      simp at x_mem
      by_contra!
      by_cases min_dist_lt : min_dist < 0
      · rw [← min_dist_eq] at min_dist_lt
        linarith [norm_nonneg (x - 1)]

      simp [show min_dist = 0 by linarith, sub_eq_zero] at min_dist_eq
      have x_neq_one := x_mem.2
      contradiction

    intro h h_det c hc h_mul h_dist

    have c_nonzero : c ≠ 0 := by
      by_contra!
      rw [this] at hc
      simp at hc

    have ne_zero_n : NeZero n := by
      rw [neZero_iff]
      linarith

    let c_unit : Units ℂ := {
        val := c,
        inv := c⁻¹,
        val_inv := by field_simp
        inv_val := by field_simp
      }


    have det_eq_c_n : h.det = c^n := by
      rw [h_mul]
      simp


    rw [h_det] at det_eq_c_n

    rw [h_mul] at h_dist
    simp [diag_unitary] at h_dist

    conv at h_dist =>
      arg 1
      arg 1
      lhs
      equals c • (Matrix.diagonal (fun _ => 1)) =>
        rw [← Matrix.smul_one_eq_diagonal]
        simp

    rw [Matrix.diagonal_one] at h_dist
    conv at h_dist =>
      arg 1
      arg 1
      rhs
      equals (1 : ℂ) • 1 =>
        simp
    rw [← sub_smul] at h_dist
    rw [norm_smul] at h_dist
    conv at h_dist =>
      lhs
      rhs
      equals (1 : ℝ) =>
        bound

    simp at h_dist

    by_contra!


    have c_dist_e : min_dist < ‖ c - 1‖ := by
      have c_dist  := h_min_prop (y := ‖c - 1‖)
      simp [dists] at c_dist
      have dist_ge := c_dist c_unit ?_ ?_ ?_
      · by_contra!
        specialize dist_ge (by linarith)
        linarith
      · simp [c_unit]
        ext
        simp
        rw [det_eq_c_n]
      · simp [c_unit]
        rw [Units.ext_iff]
        simp
        simp [this]
      · simp [c_unit]
    linarith
  · simp [dists]
    apply Set.Finite.image
    apply Set.Finite.diff
    apply Set.Finite.image


    have finite_roots : Finite ↥(rootsOfUnity n ℂ) := by infer_instance
    -- TODO - how is this working???
    exact finite_roots
  · --have n_gt_one : 1 < n := by omega
    simp [dists]
    rw [Set.diff_nonempty]
    simp

    let my_root : Units ℂ := {
      val := Complex.exp (2 * ↑Real.pi * Complex.I * (1 / ↑n)),
      inv := (Complex.exp (2 * ↑Real.pi * Complex.I * (1 / ↑n)))⁻¹
      val_inv := by simp
      inv_val := by simp
    }
    use my_root
    simp [my_root]
    refine ⟨?_, ?_⟩
    · ext
      simp
      rw [← Complex.exp_nat_mul, mul_comm]
      field_simp
      simp
    · simp [Units.ext_iff, Complex.exp_eq_one_iff]
      intro a
      conv =>
        arg 1
        rhs
        rw [mul_comm]
      field_simp
      by_contra!
      simp at this
      field_simp at this
      have abs_lt_one : ‖((1 : ℂ) / ↑n)‖ < 1 := by
        simp
        have div_le := Nat.cast_inv_le_one (α := ℝ) n
        by_cases inv_eq_one : (n : ℝ)⁻¹ = 1
        · simp at inv_eq_one div_le
          linarith
        · simpa [← ne_iff_lt_iff_le, show n ≠ 1 by omega] using div_le
      by_cases a_eq_zero : a = 0
      · simp [a_eq_zero] at this
        omega
      · simp [this] at abs_lt_one
        norm_cast at abs_lt_one
        linarith [Int.one_le_abs a_eq_zero]

-- Lemma 3.31 (Volume Packing)
end

section
-- module Solutions.OAIQ093_PR.Unitary_HnEps
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The sets `H_n` and their upper bounds

The `HnEpsData` bundle of standing hypotheses, the sets `H_n eps`, and upper bounds on products
of their elements.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


open scoped Pointwise Finset

structure SPolyData {T: Type*} [DecidableEq T] [Group T] (G : Subgroup T) where
  S: Set G
  S_finite: Set.Finite S
  S_one: 1 ∈ S
  S_inv: S = S⁻¹
  S_generates: Subgroup.closure S = ⊤
  S_poly_const: ℕ
  S_poly_const_pos: 0 ≠ S_poly_const
  S_poly_deg: ℕ
  S_poly: ∀ r ≥ 1, #(S_finite.toFinset ^ r) ≤ S_poly_const * (r ^ S_poly_deg)

class HnEpsData where
  degree: ℕ


namespace HnEpsData
variable [h_n_eps_data: HnEpsData]

-- A sufficiently small epsilon to use for the h_n elements in Theorem 3.8 (independent of the choice of n)
@[expose]
noncomputable def H_n_eps {d : ℕ} (hd : 2 ≤ d): ℝ := min (((1 : ℝ) / 60)) (min (((1 : ℝ) / 60) / ((Real.exp (4 + h_n_eps_data.degree * Real.log 2) + 1))) ((small_dist_matrix d hd).choose / 2))

-- H_n_eps is less than 1/2
lemma H_n_eps_lt {d : ℕ} (hd : 2 ≤ d) : H_n_eps hd < ((1 : ℝ) / 4) := by
  simp [H_n_eps]
  left
  norm_num


lemma H_n_eps_pos {d : ℕ} (hd : 2 ≤ d) : 0 < H_n_eps hd := by
  simp [H_n_eps]
  refine ⟨?_, ?_⟩
  . positivity
  .
    have small_pos := (small_dist_matrix d hd).choose_spec
    linarith


open scoped Finset
open scoped Pointwise


structure HnData where
  d : ℕ
  hd : 2 ≤ d
  G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)
  G_central_trivial : ∀ g : G, g ∈ Set.center G → ∃ z : ℂ, g.val.val = z • 1
  S : Set G
  S_generates : Subgroup.closure S = ⊤
  S_finite : S.Finite
  S_one: 1 ∈ S
  S_inv: ∀ s ∈ S, s⁻¹ ∈ S
  S_dist : ∀ s ∈ S, ‖s.val.val - 1‖ ≤ (H_n_eps hd)
  S_poly_const: ℕ
  S_poly_const_pos: 0 ≠ S_poly_const
  S_poly_deg: ℕ
  S_poly: ∀ r ≥ 1, #(S_finite.toFinset ^ r) ≤ S_poly_const * (r ^ S_poly_deg)
  h : S
  h_nontrivial : ¬ ∃(z : ℂ), h.val.val.val = z • 1

structure Theorem3_8_Data (data: HnData) where
  g: data.G
  g_nontrivial : ¬ ∃ z : ℂ, g.val.val = z • 1
  g_dist_nonzero : ‖g.val.val - 1‖ ≠ 0
  g_dist : ‖g.val.val - 1‖ ≤ (H_n_eps data.hd)


-- The element of S in the left-hand side of the commutator in theorem_3_8_h_n
theorem theorem_3_8_h_n_left_S (data: HnData) (prev: Theorem3_8_Data data): ∃ s : data.S, ∀ z : ℂ, ⁅s.val.val, prev.g.val⁆.val ≠ z • 1 := by
  by_contra!
  have comm_eq_id : ∀ s : data.S, ⁅s.val.val, prev.g.val⁆ = 1 := by
    intro s
    obtain ⟨z, comm_eq_z⟩ := this s
    have norm_z : ‖z‖ = 1 := by
      have z_mul_unitary : z • 1 ∈ Matrix.unitaryGroup (Fin data.d) ℂ := by
        rw [← comm_eq_z]
        simp


      have det_unitary := Matrix.det_of_mem_unitary z_mul_unitary
      simp at det_unitary
      apply CStarRing.norm_of_mem_unitary at det_unitary
      simp at det_unitary
      have d_ne_zero : data.d ≠ 0 := by
        have hd := data.hd
        omega
      have z_pow := (pow_eq_one_iff_of_ne_zero (a := ‖z‖) d_ne_zero).mp det_unitary
      have norm_pos : 0 ≤ ‖z‖ := by
        positivity
      have norm_not_neg : ‖z‖ ≠ -1 := by
        linarith

      simp [norm_not_neg] at z_pow
      exact z_pow
    have det_one : ⁅s.val.val, prev.g.val⁆.val.det = 1 := by
      simp [Bracket.bracket]
      rw [Matrix.star_eq_conjTranspose]
      rw [Matrix.star_eq_conjTranspose]
      rw [mul_comm]
      rw [mul_assoc]
      nth_rw 2 [mul_comm]
      rw [mul_assoc]
      rw [← Matrix.det_mul]
      rw [← Matrix.star_eq_conjTranspose]
      rw [← Matrix.star_eq_conjTranspose]
      rw [Matrix.UnitaryGroup.star_mul_self]
      rw [← mul_assoc]
      rw [← Matrix.det_mul]
      rw [Matrix.UnitaryGroup.star_mul_self]
      simp

    have prev_prop := prev.g_dist
    have norm_le := shrinking_conjugators data.d s.val prev.g.val
    grw [data.S_dist s, prev_prop] at norm_le
    · have two_mul_le : 2 * (H_n_eps data.hd) ≤ 1 := by
        grw [H_n_eps_lt data.hd]
        norm_num
      grw [two_mul_le] at norm_le
      · simp at norm_le


        let C := (small_dist_matrix data.d data.hd).choose

        have H_eps_lt_C : H_n_eps data.hd < C := by
          rw [H_n_eps]
          unfold C
          grw [min_le_right]
          simp
          right
          have my_spec := (small_dist_matrix data.d data.hd).choose_spec
          linarith

        unfold C at H_eps_lt_C


        obtain ⟨C_pos, small_eps⟩ := (small_dist_matrix data.d data.hd).choose_spec
        have z_eq_one := small_eps ⁅s.val.val, prev.g.val⁆.val det_one z norm_z (by
          simp [diag_unitary]
          rw [← Matrix.smul_one_eq_diagonal]
          exact comm_eq_z
        ) (by
          grw [norm_le]
          exact H_eps_lt_C
        )
        simp [z_eq_one] at comm_eq_z
        exact comm_eq_z
      · -- TODO - deduplicate this
        have foo := H_n_eps_pos data.hd
        linarith
    · have foo := H_n_eps_pos data.hd
      linarith
    · simp
  · have subgroup_le := Subgroup.closure_le_centralizer_centralizer data.S
    simp [data.S_generates] at subgroup_le
    have prev_mem_centralizer : prev.g ∈ Subgroup.centralizer data.S := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have h_comm := comm_eq_id ⟨s, hs⟩
      simp [Bracket.bracket] at h_comm
      rw [mul_assoc] at h_comm
      apply eq_inv_of_mul_eq_one_left at h_comm
      simp at h_comm
      rw [Subtype.ext_iff]
      simp
      exact h_comm

    have prev_central := subgroup_le prev_mem_centralizer
    have prev_trivial := data.G_central_trivial _ prev_central
    have prev_nontrivial := prev.g_nontrivial
    contradiction


-- 'h' is our initial element - we define ε in terms of ‖h - 1‖, so that we can obtain the proper bound
-- for the commutators in the inductive case
set_option maxHeartbeats 500000 in
@[expose]
noncomputable def theorem_3_8_h_n (data : HnData) (n : ℕ): Theorem3_8_Data data := match hn : n with
  | 0 => {
    g := data.h,
    g_nontrivial := data.h_nontrivial,
    g_dist_nonzero := by
      by_contra!
      simp at this
      rw [sub_eq_zero] at this
      have h_nontrivial := data.h_nontrivial
      simp at h_nontrivial
      have h_neq := h_nontrivial 1
      simp at h_neq
      simp at this
      contradiction
    ,
    g_dist := data.S_dist data.h data.h.property
  }
  | k + 1 => by
    -- TODO - why do we get a heartbeat timeout if we inline 'prev'?
    let prev := (theorem_3_8_h_n data k)
    use ⁅(theorem_3_8_h_n_left_S data prev).choose.val, prev.g⁆
    · rw [not_exists]
      exact (theorem_3_8_h_n_left_S data prev).choose_spec
    · by_contra!
      simp at this
      rw [sub_eq_zero] at this
      have my_nontrivial := (theorem_3_8_h_n_left_S data prev).choose_spec 1
      simp at my_nontrivial
      simp at this
      rw [commutatorElement_eq_one_iff_mul_comm] at this
      rw [commutatorElement_eq_one_iff_mul_comm] at my_nontrivial
      rw [Subtype.ext_iff] at this
      simp at this
      contradiction
    · have my_shrink := shrinking_conjugators data.d (theorem_3_8_h_n_left_S data prev).choose prev.g
      conv =>
        lhs
        arg 1
        lhs
        equals ⁅ (theorem_3_8_h_n_left_S data prev).choose.val.val, prev.g.val ⁆.val =>
          rw [commutatorElement_def, commutatorElement_def]
          rfl
      grw [my_shrink]
      have prev_prop := prev.g_dist
      grw [prev_prop]
      have comm_choose_le := data.S_dist (theorem_3_8_h_n_left_S data prev).choose (by simp)
      grw [comm_choose_le]
      have two_mul_le : 2 * (H_n_eps data.hd) ≤ 1 := by
        grw [H_n_eps_lt data.hd]
        norm_num
      grw [two_mul_le]
      · simp
      · linarith [H_n_eps_pos data.hd]
      · linarith [H_n_eps_pos data.hd]


termination_by n
decreasing_by
  simp

end HnEpsData
end

section
-- module Solutions.OAIQ093_PR.Unitary_HnLowerBound
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# A lower bound for powers in `H_n`

The real auxiliary function `f` and the resulting lower bound `H_n_single_pow_lower_bound`.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


namespace HnEpsData

variable [h_n_eps_data: HnEpsData]


@[expose]
noncomputable def f (a: ℝ) (x: ℝ): ℝ := 1 + (2*x - 1)*a - (1 + a)^x

end HnEpsData
end

section
-- module Solutions.OAIQ093_PR.Unitary_Words
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Distinct words in `H_n`

`words_distinct` and the resulting cardinality bound `H_n_ball_S_card` for balls in the word
metric.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


namespace HnEpsData

variable [h_n_eps_data: HnEpsData]

-- Unfold the commutators from theorem_3_8_h_n as a list of elements
@[expose]
noncomputable def theorem_3_8_h_n_list (data: HnData) (m: ℕ): List (data.S) :=
  match m with
  | 0 => [data.h]
  | a + 1 => [(theorem_3_8_h_n_left_S data (theorem_3_8_h_n data a)).choose]
              ++ theorem_3_8_h_n_list data a
              ++ [⟨(theorem_3_8_h_n_left_S data (theorem_3_8_h_n data a)).choose.val⁻¹, (by
                apply data.S_inv
                simp
              )⟩]
              ++ (List.map (fun s => ⟨s.val⁻¹, by apply data.S_inv; simp⟩) (theorem_3_8_h_n_list data a)).reverse


-- The c' constant from Vikman
@[expose]
def c' := 3

abbrev swap_le {a b: ℝ} (_: a ≤ b): Prop := b < a

-- Our lower bound gives us a contradiction with polynomial growth

end HnEpsData
end

section
-- module Solutions.OAIQ093_PR.UnitaryGromov
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Compact Lie subgroups of polynomial growth are virtually abelian

`compact_lie_virtually_abelian`.

Root of the `Gromov.Unitary` hierarchy.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


@[expose]
def map_S_data {G H: Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H] (A: Subgroup G) {f: G →* H} (S_data: SPolyData A): SPolyData (Subgroup.map f A) := {
  S := f.subgroupMap A '' S_data.S
  S_finite := by
    apply Set.Finite.image
    apply S_data.S_finite
  S_one := by
    simp only [Set.mem_image]
    use 1
    simp
    apply S_data.S_one
  S_inv := by
    rw [← Set.image_inv]
    rw [← S_data.S_inv]
  S_generates := by
    rw [← MonoidHom.map_closure]
    rw [S_data.S_generates]
    rw [Subgroup.map_top_of_surjective]
    apply MonoidHom.subgroupMap_surjective
  S_poly_const := S_data.S_poly_const
  S_poly_const_pos := S_data.S_poly_const_pos
  S_poly_deg := S_data.S_poly_deg
  S_poly := by
    intro r hr
    rw [Set.Finite.toFinset_image]
    rw [← Finset.image_pow]
    grw [Finset.card_image_le]
    .
      apply S_data.S_poly r hr
    . exact S_data.S_finite
}
end

section
-- module Solutions.OAIQ093_PR.Representation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The representation of `G` on `W`

The space `W = LipschitzH ⧸ ConstF`, the representation `GRep` / `GRepW` of `G` on it, and the
fact that it preserves the quotient norm.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
-- TODO - vscode stops reporting underlines if there are too many total underlines / gutter messages
-- I've disabled some failing lints for now so that error underlines still sho up
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS

open scoped RealInnerProductSpace

-- `LipschitzH_seminorm` and `LipschitzH_normed` are public instances in
-- `Gromov.LipschitzNorm`, so they are already available here.

-- The lift of LipschitzSemiNorm to W, using a proof that LipschitzSemiNorm doesn't depend on the choice representative
-- (adding a constant to a Lipschitz function doesn't change its Lipschitz constant)


set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 9000000


set_option synthInstance.maxHeartbeats 500000


@[expose]
def FreshTopology (V: Type*) := V
instance instGroupFreshTopology (V: Type*) [base_group: Group V]: Group (FreshTopology V) := base_group
instance instAddCommGroupFreshTopology (V: Type*) [base_comm: AddCommGroup V]: AddCommGroup (FreshTopology V) := base_comm
instance instModuleRealFreshTopology (V: Type*) [AddCommGroup V] [base_module: Module ℝ V]: Module ℝ (FreshTopology V) := base_module
@[expose]
instance instFiniteDimensionalRealFreshTopology (V: Type*) [AddCommGroup V] [Module ℝ V]  [base_finite: FiniteDimensional ℝ V]: FiniteDimensional ℝ (FreshTopology V) := base_finite


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.RhoAbelian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# `rho_g` contains a finite-index abelian subgroup

`rho_g_contains_abelian`, the bundled input `Theorem3_1_Input`, and the infinite-image case.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS

open scoped RealInnerProductSpace

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 9000000

structure Theorem3_1_Input (G: Type*) [Group G] where
  -- A finite index subgroup G' of G
  G': Subgroup G
  finite_index: G'.FiniteIndex
  -- G' can be mapped homomorphically onto ℤ
  φ: (Additive G') →+ ℤ
  hφ: Function.Surjective φ


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.ThreeTwoGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Polynomial growth of the sets `S_n`

`new_three_two_poly_growth` and `three_poly_poly_growth_all_s_n`.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS

open scoped RealInnerProductSpace

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 9000000

open MeasureTheory

open Additive

abbrev countElemOrInv {T: Type*} [ht: Group T] [heq: DecidableEq T] {E: Set T} (l: List E) (γ: T): ℤ := (l.map (fun (s: E) => if s = γ then 1 else if s = γ⁻¹ then -1 else 0)).sum

open Additive


@[expose]
def e_i_regular_helper {G: Type*} [Group G] [DecidableEq G] {S: Finset G} (φ: (Additive G) →+ ℤ) (γ: G) (s: S): G := (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))


@[expose]
def gamma_m_helper {G: Type*} [Group G] [DecidableEq G] {S: Finset G} (φ: (Additive G) →+ ℤ) (γ: G) (m: ℤ) (s: S): G := γ^m * (e_i_regular_helper φ γ s) * γ^(-m)

@[expose]
noncomputable def three_two_S_n {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Finset G := Finset.image (Function.uncurry (gamma_m_helper φ γ)) ((Finset.Icc (-n : ℤ) n).product S.attach)
-- The set of words of at length at most n generated by {γ_m_i}_{m ≤ n}
-- Note - This is based on https://terrytao.wordpress.com/2010/02/18/a-proof-of-gromovs-theorem/, which uses
-- "length at most n"
-- The Vikman paper says "words of length n", which seems incorrect


@[expose]
noncomputable def list_len_n {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Finset (List ((three_two_S_n S φ γ n ))) := @Set.toFinset _ { l: List ((three_two_S_n S φ γ n )) | l.length ≤ n } (@Fintype.ofFinite _ _)

@[expose]
noncomputable def three_two_B_n {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Finset G := Finset.image (fun l => l.unattach.prod) (list_len_n S φ γ n )


--set_option maxHeartbeats 600000


attribute [local implicit_reducible] Additive Multiplicative

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.GrowthZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Polynomial growth of the kernel, and growth exponent zero

`three_two_kernel_poly_growth`, and that a group of growth exponent zero is finite.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS

open scoped RealInnerProductSpace

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 1000000

open MeasureTheory

open Additive

attribute [local implicit_reducible] Additive Multiplicative

structure GeneratesWithParam (G: Type*) [Group G] [DecidableEq G] where
  S: Finset G
  hS: Nonempty S
  generates : ((closure (S : Set G) : Set G) = ⊤)
  -- This should be fine, since the growth rate doesn't depend on the generating set
  one_mem: (1 : G) ∈ S
  has_inv: ∀ g ∈ S, g⁻¹ ∈ S
  g_infinite: Infinite G

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BracketWords
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual bracket words for the nilpotent box construction

The linear span of evaluated bracket words is exactly the generated Lie
subalgebra. A finite-dimensional generated algebra therefore has a basis
chosen from actual words. Letter counts give the weights of these words,
including for generalized weight vectors.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped BigOperators
open Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

def evalBracketWord (X : I → L) : FreeMagma I → L
  | .of i => X i
  | .mul a b => ⁅evalBracketWord X a, evalBracketWord X b⁆

omit [LieAlgebra ℝ L] in
@[simp] theorem evalBracketWord_of (X : I → L) (i : I) :
    evalBracketWord X (.of i) = X i := rfl

omit [LieAlgebra ℝ L] in
@[simp] theorem evalBracketWord_mul (X : I → L) (a b : FreeMagma I) :
    evalBracketWord X (a * b) = ⁅evalBracketWord X a, evalBracketWord X b⁆ := rfl

def bracketWordCount [DecidableEq I] : FreeMagma I → I → ℕ
  | .of j, i => if i = j then 1 else 0
  | .mul a b, i => bracketWordCount a i + bracketWordCount b i

theorem evalBracketWord_map {L' : Type*} [LieRing L'] [LieAlgebra ℝ L']
    (f : L →ₗ⁅ℝ⁆ L') (X : I → L) (w : FreeMagma I) :
    f (evalBracketWord X w) = evalBracketWord (fun i => f (X i)) w := by
  induction w using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb => simp only [evalBracketWord, f.map_lie, ha, hb]

def bracketWordWeight {H : Type*} [AddCommGroup H] [Module ℝ H]
    (α : I → H →ₗ[ℝ] ℝ) : FreeMagma I → H →ₗ[ℝ] ℝ
  | .of i => α i
  | .mul a b => bracketWordWeight α a + bracketWordWeight α b

theorem bracketWordWeight_eq_count [Fintype I] [DecidableEq I]
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (α : I → H →ₗ[ℝ] ℝ) (w : FreeMagma I) (h : H) :
    bracketWordWeight α w h = ∑ i, (bracketWordCount w i : ℝ) * α i h := by
  induction w using FreeMagma.rec with
  | of j => simp [bracketWordWeight, bracketWordCount]
  | mul a b ha hb =>
    simp only [bracketWordWeight, LinearMap.add_apply, ha, hb,
      bracketWordCount, Nat.cast_add, add_mul, Finset.sum_add_distrib]

/-- Generalized weight vectors remain generalized after taking brackets.
The nilpotent part of the Cartan action is retained. -/
theorem evalBracketWord_mem_generalizedWeight
    (H : LieSubalgebra ℝ L) (α : I → H →ₗ[ℝ] ℝ) (X : I → L)
    (hX : ∀ i (h : H), X i ∈ (LieAlgebra.ad ℝ L h).maxGenEigenspace (α i h))
    (w : FreeMagma I) (h : H) :
    evalBracketWord X w ∈
      (LieAlgebra.ad ℝ L h).maxGenEigenspace (bracketWordWeight α w h) := by
  induction w using FreeMagma.rec with
  | of i => exact hX i h
  | mul a b ha hb =>
    exact LieModule.lie_mem_maxGenEigenspace_toEnd ha hb

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieExponential
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): the tangent-space instances and casts it
declares beside `TangentSpace` (`IsManifold/Basic.lean`, `IsManifold/ExtChartAt.lean`). -/

section TangentSpaceCompat

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

instance TangentSpace.instFiniteDimensionalCompat [FiniteDimensional 𝕜 E] :
    FiniteDimensional 𝕜 (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional 𝕜 E)

end TangentSpaceCompat
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteBracketWords
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite list containing every nonzero bracket word

A word of depth `k` belongs to the `k`th lower central ideal. Thus a
nilpotency bound gives a finite list containing every nonzero evaluated
word. The depth cutoff avoids choosing a minimal nilpotence class.
-/

noncomputable section

namespace PolycyclicRecognition

open LieModule Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

def bracketWordDepth : FreeMagma I → ℕ
  | .of _ => 0
  | .mul a b => max (bracketWordDepth a) (bracketWordDepth b) + 1

variable [Fintype I] [DecidableEq I]

def boundedBracketWords : ℕ → Finset (FreeMagma I)
  | 0 => ∅
  | k + 1 => Finset.univ.image FreeMagma.of ∪
      ((boundedBracketWords k).product (boundedBracketWords k)).image
        (fun p => p.1 * p.2)

@[simp] theorem mem_boundedBracketWords (w : FreeMagma I) (k : ℕ) :
    w ∈ boundedBracketWords (I := I) k ↔ bracketWordDepth w < k := by
  induction k generalizing w with
  | zero => simp [boundedBracketWords]
  | succ k ih =>
    cases w with
    | of i => simp [boundedBracketWords, bracketWordDepth]
    | mul a b =>
      rw [boundedBracketWords, Finset.mem_union]
      have hn : a * b ∉ Finset.univ.image (FreeMagma.of : I → FreeMagma I) := by
        rintro he
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
        cases hi
      change (a * b ∈ Finset.univ.image FreeMagma.of ∨
        a * b ∈ ((boundedBracketWords k).product (boundedBracketWords k)).image
          (fun p => p.1 * p.2)) ↔
          max (bracketWordDepth a) (bracketWordDepth b) + 1 < k + 1
      rw [or_iff_right hn, Finset.mem_image]
      constructor
      · rintro ⟨⟨c, d⟩, hcd, he⟩
        have hab : c = a ∧ d = b := by cases he; exact ⟨rfl, rfl⟩
        rcases hab with ⟨rfl, rfl⟩
        have hh := Finset.mem_product.mp hcd
        exact Nat.add_lt_add_right (max_lt ((ih _).mp hh.1) ((ih _).mp hh.2)) 1
      · intro hh
        have hab : bracketWordDepth a < k ∧ bracketWordDepth b < k :=
          max_lt_iff.mp (Nat.lt_of_add_lt_add_right hh)
        exact ⟨(a, b), Finset.mem_product.mpr
          ⟨(ih a).mpr hab.1, (ih b).mpr hab.2⟩, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteWordBases
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All bases from a finite word list

The indexing type is finite and includes every ordered word basis selected
from the list. Nilpotence proves this family is nonempty for a generating
alphabet, including the zero-dimensional case.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- All ordered bases selected from `S`, retaining the actual word labels. -/
def WordBasisSelections (X : I → L) (S : Finset (FreeMagma I)) :=
  {w : Fin (finrank ℝ L) → S //
    ∃ b : Basis (Fin (finrank ℝ L)) ℝ L, ∀ j, evalBracketWord X (w j) = b j}

namespace WordBasisSelections

variable (X : I → L) (S : Finset (FreeMagma I))

instance instFintype : Fintype (WordBasisSelections X S) := by
  classical
  unfold WordBasisSelections
  infer_instance

/-- The word labels of this selected basis. -/
def words (β : WordBasisSelections X S) (j : Fin (finrank ℝ L)) : FreeMagma I := β.val j

/-- The corresponding actual basis of the Lie algebra. -/
def basis (β : WordBasisSelections X S) : Basis (Fin (finrank ℝ L)) ℝ L :=
  Classical.choose β.property

theorem eval_words (β : WordBasisSelections X S) (j : Fin (finrank ℝ L)) :
    evalBracketWord X (words X S β j) = basis X S β j :=
  Classical.choose_spec β.property j

end WordBasisSelections

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedColumnBasis
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!+# Maximizing bases and normalized box coefficients

This is the basis-exchange step in the manuscript's box calculus. A nonzero
coefficient permits column replacement. Maximality of the basis weight then
makes the exponential rescaling factor at most one.
-/

noncomputable section

open scoped BigOperators

namespace PolycyclicRecognition

variable {I : Type*} {n : ℕ}

/-- The columns chosen from a finite list of vectors. -/
def columnBasisMatrix (v : I → Fin n → ℝ) (b : Fin n → I) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => v (b j) i

def columnBasisWeight (w : I → ℝ) (b : Fin n → I) : ℝ := ∑ j, w (b j)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordBasisCoordinates
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maximizing actual word bases

Invertible selections from the coordinate matrix are exactly the actual word
bases. Thus the finite maximizing-basis argument applies to the Lie word list.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (X : I → L) (S : Finset (FreeMagma I))
  (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)

def wordListCoordinates (w : S) : Fin (finrank ℝ L) → ℝ := b₀.equivFun (evalBracketWord X w)

/-- An invertible coordinate selection gives precisely the actual word basis
needed for the finite family, including dimension zero. -/
def wordBasisOfDet (w : Fin (finrank ℝ L) → S)
    (hw : (columnBasisMatrix (wordListCoordinates X S b₀) w).det ≠ 0) :
    WordBasisSelections X S := by
  have hli : LinearIndependent ℝ (fun j => evalBracketWord X (w j)) := by
    apply LinearIndependent.of_comp b₀.equivFun.toLinearMap
    exact Matrix.linearIndependent_cols_of_det_ne_zero hw
  let b := basisOfLinearIndependentOfCardEqFinrank'
    (fun j => evalBracketWord X (w j)) hli (Fintype.card_fin _)
  exact ⟨w, b, fun j => (congrFun (coe_basisOfLinearIndependentOfCardEqFinrank'
    (fun j => evalBracketWord X (w j)) hli (Fintype.card_fin _)) j).symm⟩

@[simp] theorem wordBasisOfDet_val (w : Fin (finrank ℝ L) → S)
    (hw : (columnBasisMatrix (wordListCoordinates X S b₀) w).det ≠ 0) :
    (wordBasisOfDet X S b₀ w hw).val = w := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordExponents
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additive exponents of bracket words

Letter amplitudes add through every bracket. The sum in a word basis is the
letter-count expression used by the support datum.
-/

namespace PolycyclicRecognition

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I]

def bracketWordExponent (s : I → ℝ) (w : FreeMagma I) : ℝ :=
  ∑ i, (bracketWordCount w i : ℝ) * s i

@[simp] theorem bracketWordExponent_of (s : I → ℝ) (i : I) :
    bracketWordExponent s (.of i) = s i := by
  simp [bracketWordExponent, bracketWordCount]

@[simp] theorem bracketWordExponent_mul (s : I → ℝ) (u v : FreeMagma I) :
    bracketWordExponent s (u * v) = bracketWordExponent s u + bracketWordExponent s v := by
  simp [bracketWordExponent, bracketWordCount, add_mul, Finset.sum_add_distrib]

@[simp] theorem bracketWordExponent_add (s t : I → ℝ) (w : FreeMagma I) :
    bracketWordExponent (s + t) w = bracketWordExponent s w + bracketWordExponent t w := by
  simp [bracketWordExponent, mul_add, Finset.sum_add_distrib]

/-- Multiplying all letter costs multiplies every bracket-word cost. -/
@[simp] theorem bracketWordExponent_const_mul (a : ℝ) (s : I → ℝ) (w : FreeMagma I) :
    bracketWordExponent (fun i => a * s i) w = a * bracketWordExponent s w := by
  simp only [bracketWordExponent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedWordBrackets
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform normalized structure constants

In a maximizing word basis, the bracket of two basis words is either zero
or another word of the finite list. Basis exchange then bounds every scaled
bracket coefficient independently of the letter amplitudes.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]
  [Fintype I] [DecidableEq I] [FiniteDimensional ℝ L]

/-- The actual rescaled basis whose structure constants are being bounded. -/
def exponentialRescaleBasis {J : Type*} (b : Basis J ℝ L) (cost : J → ℝ) (r : ℝ) :
    Basis J ℝ L :=
  b.unitsSMul (fun j => Units.mk0 (Real.exp (r * cost j)) (Real.exp_ne_zero _))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentLieModel
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The simply connected nilpotent Lie models needed by Cartan factorization

J. M. Lee, *Introduction to Smooth Manifolds*, second edition (2013),
Theorem 20.21, p.531, gives the simply connected integration of a finite
dimensional real Lie algebra. For the nilpotent case, exponential coordinates
have a finite polynomial BCH law: F. Baudoin, *An Introduction to the Geometry
of Stochastic Flows* (2004), Appendix B.5–B.6, pp.123–126. These coordinates
give the analytic Lie-group model used here. No metric-growth, Haar-volume,
Cartan-factorization, or quasi-isometry conclusion is included in this input.

The universe of the model can be chosen to match the algebra by using its
finite-dimensional coordinate space (or a lifted copy).
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

universe u

/-- Only the finite-dimensional simply connected integration data. Haar
measure and intrinsic exponentials are obtained from their separate input. -/
structure NilpotentLieModel (L : Type u) [LieRing L] [LieAlgebra ℝ L] where
  modelSpace : Type u
  [normedAddCommGroup : NormedAddCommGroup modelSpace]
  [normedSpace : NormedSpace ℝ modelSpace]
  [finiteDimensional : FiniteDimensional ℝ modelSpace]
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  [chartedSpace : ChartedSpace modelSpace carrier]
  [group : Group carrier]
  [lieGroup : LieGroup (𝓘(ℝ, modelSpace)) ⊤ carrier]
  [t2Space : T2Space carrier]
  [simplyConnectedSpace : SimplyConnectedSpace carrier]
  [measurableSpace : MeasurableSpace carrier]
  [borelSpace : BorelSpace carrier]
  equiv : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, modelSpace)) carrier

attribute [instance] NilpotentLieModel.normedAddCommGroup NilpotentLieModel.normedSpace
  NilpotentLieModel.finiteDimensional NilpotentLieModel.topologicalSpace
  NilpotentLieModel.chartedSpace NilpotentLieModel.group NilpotentLieModel.lieGroup
  NilpotentLieModel.t2Space NilpotentLieModel.simplyConnectedSpace
  NilpotentLieModel.measurableSpace NilpotentLieModel.borelSpace

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AbelianRealSpace
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real abelian coordinate space and its explicit integer lattice -/

noncomputable section
namespace PolycyclicRecognition

def AbelianRealSpace (n : ℕ) := Fin n → ℝ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LinearActionFiltration
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The dimension bound for an eventually vanishing action filtration

Take successive spans of the images of a family of operators. If this
descending filtration ever vanishes, it vanishes by the dimension of the
space: an equality at one stage propagates to all later stages, so every
nonzero stage must strictly lower dimension.
-/

noncomputable section
namespace PolycyclicRecognition

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

def linearActionStep (D : I → Module.End K V) (W : Submodule K V) : Submodule K V :=
  ⨆ i, W.map (D i)

def linearActionFiltration (D : I → Module.End K V) : ℕ → Submodule K V
  | 0 => ⊤
  | n + 1 => linearActionStep D (linearActionFiltration D n)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ActionDepth
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Commutators advance an operator filtration

If every action difference raises a descending filtration by one step, its
commutators raise it further. This controls the lower central series using
the length at which the action filtration vanishes.
-/

namespace PolycyclicRecognition

open scoped commutatorElement

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

def ActionDepth (D : I → Module.End K V) (k : ℕ) (f : Module.End K V) : Prop :=
  ∀ n v, v ∈ linearActionFiltration D n → f v ∈ linearActionFiltration D (n + k)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlgebraGroupTangent
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Infinitesimal commutators of matrix groups

The finite-dimensional span of derivatives of curves in a subgroup records
its infinitesimal action. Differentiating group commutators twice puts the
algebra commutator into the tangent span of the derived subgroup.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Topology commutatorElement
open Filter

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [FiniteDimensional ℝ A] [CompleteSpace A]

/-- A derivative at the identity of a curve contained in a given matrix group. -/
def AlgebraGroupTangentVector (D : Subgroup Aˣ) (X : A) : Prop :=
  ∃ c : ℝ → Aˣ, (∀ t, c t ∈ D) ∧ c 0 = 1 ∧
    HasDerivAt (fun t => (c t : A)) X 0

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportNorm
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The norm obtained from weighted nilpotent boxes

For a bracket-word basis, each generator occurs with a positive integral
multiplicity. Unimodularity says that the corresponding weighted sum of
characters is zero. The support exponent of a segment is the maximum, over
these bases, of the weighted positive parts of the characters. This finite
data yields the support norm identities.
-/

namespace PolycyclicRecognition

open scoped BigOperators

variable {W I B : Type*} [AddCommGroup W] [Module ℝ W]
  [Fintype I] [Fintype B] [Nonempty B]

/-- The finite algebraic data of the segment-support formula. -/
structure SupportDatum (W I B : Type*) [AddCommGroup W] [Module ℝ W]
    [Fintype I] [Fintype B] where
  weight : I → W →ₗ[ℝ] ℝ
  multiplicity : B → I → ℕ
  positive : ∀ b i, 0 < multiplicity b i
  balanced : ∀ b w, ∑ i, (multiplicity b i : ℝ) * weight i w = 0
  separates : ∀ w, (∀ i, weight i w = 0) → w = 0

namespace SupportDatum

variable (D : SupportDatum W I B)

/-- The support exponent contributed by one bracket-word basis. -/
noncomputable def basisSupport (b : B) (w : W) : ℝ :=
  ∑ i, (D.multiplicity b i : ℝ) * max 0 (D.weight i w)

/-- The support exponent of the segment from zero to `w`. -/
noncomputable def segmentSupport (w : W) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun b => D.basisSupport b w)

omit [Nonempty B] in
theorem basisSupport_nonneg (b : B) (w : W) : 0 ≤ D.basisSupport b w := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _)

theorem basisSupport_le (b : B) (w : W) :
    D.basisSupport b w ≤ D.segmentSupport w := by
  exact Finset.le_sup' (f := fun b => D.basisSupport b w) (Finset.mem_univ b)

theorem segmentSupport_le {w : W} {r : ℝ}
    (h : ∀ b, D.basisSupport b w ≤ r) : D.segmentSupport w ≤ r := by
  exact Finset.sup'_le _ _ fun b _ => h b

theorem segmentSupport_nonneg (w : W) : 0 ≤ D.segmentSupport w := by
  obtain ⟨b⟩ := ‹Nonempty B›
  exact (D.basisSupport_nonneg b w).trans (D.basisSupport_le b w)

omit [Nonempty B] in
@[simp] theorem basisSupport_zero (b : B) : D.basisSupport b 0 = 0 := by
  simp [basisSupport]

@[simp] theorem segmentSupport_zero : D.segmentSupport 0 = 0 := by
  apply le_antisymm (D.segmentSupport_le fun b => (D.basisSupport_zero b).le)
  exact D.segmentSupport_nonneg 0

omit [Nonempty B] in
theorem basisSupport_neg (b : B) (w : W) :
    D.basisSupport b (-w) = D.basisSupport b w := by
  have hpart (a : ℝ) : max 0 (-a) = max 0 a - a := by
    rcases le_total 0 a with ha | ha
    · rw [max_eq_right ha, max_eq_left (neg_nonpos.mpr ha)]
      ring
    · rw [max_eq_left ha, max_eq_right (neg_nonneg.mpr ha)]
      ring
  simp only [basisSupport, map_neg, hpart, mul_sub, Finset.sum_sub_distrib]
  rw [D.balanced, sub_zero]

@[simp] theorem segmentSupport_neg (w : W) :
    D.segmentSupport (-w) = D.segmentSupport w := by
  simp only [segmentSupport, D.basisSupport_neg]

omit [Nonempty B] in
theorem weight_eq_zero_of_basisSupport_eq_zero (b : B) (w : W)
    (h : D.basisSupport b w = 0) (i : I) : D.weight i w = 0 := by
  have hpos (v : W) (hv : D.basisSupport b v = 0) : D.weight i v ≤ 0 := by
    have hterm : (D.multiplicity b i : ℝ) * max 0 (D.weight i v) ≤ 0 := by
      calc
        _ ≤ D.basisSupport b v := Finset.single_le_sum
          (fun j _ => mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _)) (Finset.mem_univ i)
        _ = 0 := hv
    have hm : (0 : ℝ) < D.multiplicity b i := Nat.cast_pos.mpr (D.positive b i)
    have hmax : max 0 (D.weight i v) ≤ 0 := by nlinarith
    exact (le_max_right _ _).trans hmax
  apply le_antisymm (hpos w h)
  have hn := hpos (-w) ((D.basisSupport_neg b w).trans h)
  simpa only [map_neg, neg_nonpos] using hn

@[simp] theorem segmentSupport_eq_zero_iff (w : W) :
    D.segmentSupport w = 0 ↔ w = 0 := by
  constructor
  · intro hw
    obtain ⟨b⟩ := ‹Nonempty B›
    apply D.separates w
    intro i
    apply D.weight_eq_zero_of_basisSupport_eq_zero b w _ i
    exact le_antisymm ((D.basisSupport_le b w).trans_eq hw) (D.basisSupport_nonneg b w)
  · rintro rfl
    exact D.segmentSupport_zero

end SupportDatum
end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_QuotientTrace
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Trace after removing a nilpotent quotient action

The Cartan ideal has the same adjoint trace as the ambient algebra because
the quotient action comes from the nilpotent Cartan algebra. This is the
finite-dimensional linear step of that argument.
-/

noncomputable section

namespace PolycyclicRecognition

variable {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]

theorem trace_eq_restrict_of_nilpotent_quotient
    (N : Submodule ℝ M) (f : M →ₗ[ℝ] M) (hf : ∀ x ∈ N, f x ∈ N)
    (hnil : IsNilpotent (N.mapQ N f hf)) :
    LinearMap.trace ℝ M f = LinearMap.trace ℝ N (f.restrict hf) := by
  let A := N.mapQ N f hf
  obtain ⟨s, hs⟩ := N.mkQ.exists_rightInverse_of_surjective N.range_mkQ
  have hsection (x : M ⧸ N) : N.mkQ (s x) = x :=
    congrArg (fun F : (M ⧸ N) →ₗ[ℝ] (M ⧸ N) => F x) hs
  let B : M →ₗ[ℝ] M := s.comp (A.comp N.mkQ)
  have hinside (x : M) : (f - B) x ∈ N := by
    apply (Submodule.Quotient.mk_eq_zero N).mp
    change N.mkQ (f x - s (A (N.mkQ x))) = 0
    rw [map_sub, hsection]
    exact sub_self _
  have hBn (x : N) : B x = 0 := by
    change s (A (N.mkQ x)) = 0
    have hx : N.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero N).mpr x.property
    rw [hx, map_zero, map_zero]
  have hrest : (f - B).restrict (fun x _ => hinside x) = f.restrict hf := by
    ext x
    change f x - B x = f x
    rw [hBn, sub_zero]
  have htraceB : LinearMap.trace ℝ M B = 0 := by
    change LinearMap.trace ℝ M ((s.comp A).comp N.mkQ) = 0
    rw [LinearMap.trace_comp_comm' N.mkQ (s.comp A)]
    have heq : N.mkQ.comp (s.comp A) = A := by
      ext x
      exact hsection (A (N.mkQ x))
    rw [heq]
    exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have ht := LinearMap.trace_restrict_eq_of_forall_mem N (f - B) hinside
  rw [hrest, map_sub, htraceB, sub_zero] at ht
  exact ht.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CanonicalHeight
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The linear canonical height quotient

The height space is the quotient by the common kernel of the diagonal adjoint
characters. The induced characters on this quotient separate points.
-/

namespace PolycyclicRecognition

open scoped BigOperators

section Linear

variable {L I : Type*} [AddCommGroup L] [Module ℝ L]

/-- Each character descends to the height quotient. -/
def heightCharacter (χ : I → L →ₗ[ℝ] ℝ) (i : I) : HeightSpace χ →ₗ[ℝ] ℝ :=
  (heightKernel χ).liftQ (χ i) (iInf_le _ i)

@[simp] theorem heightCharacter_projection (χ : I → L →ₗ[ℝ] ℝ) (i : I) (x : L) :
    heightCharacter χ i (heightProjection χ x) = χ i x := rfl

theorem heightProjection_surjective (χ : I → L →ₗ[ℝ] ℝ) :
    Function.Surjective (heightProjection χ) := (heightKernel χ).mkQ_surjective

@[simp] theorem mem_heightKernel (χ : I → L →ₗ[ℝ] ℝ) (x : L) :
    x ∈ heightKernel χ ↔ ∀ i, χ i x = 0 := by
  simp only [heightKernel, Submodule.mem_iInf, LinearMap.mem_ker]

end Linear

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- Characters vanishing on brackets make every bracket have zero height. -/
theorem heightProjection_lie_eq_zero
    (χ : I → L →ₗ[ℝ] ℝ) (hχ : ∀ i (x y : L), χ i ⁅x, y⁆ = 0) (x y : L) :
    heightProjection χ ⁅x, y⁆ = 0 := by
  apply (Submodule.Quotient.mk_eq_zero (heightKernel χ)).mpr
  exact (mem_heightKernel χ ⁅x, y⁆).mpr fun i => hχ i x y

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularHeight
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Diagonal adjoint characters and the zero-height case

Starting from an actual simultaneous upper triangular basis for the adjoint
action, the diagonal entries are linear characters and kill every bracket.
The resulting canonical height space is zero exactly when the Lie algebra is
nilpotent. This proves the algebraic zero-height branch used in the manuscript;
it does not assume nilpotence from vanishing height.
-/

namespace PolycyclicRecognition

open Module

theorem upperTriangular_mul_diag {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

theorem upperTriangular_pow_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (k : ℕ) (i : Fin n) :
    (A ^ k) i i = (A i i) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, upperTriangular_mul_diag _ _ (hA.pow k) hA, ih, pow_succ]

theorem upperTriangular_nilpotent_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (hnil : IsNilpotent A) (i : Fin n) : A i i = 0 := by
  obtain ⟨k, hk⟩ := hnil
  apply IsNilpotent.eq_zero
  refine ⟨k, ?_⟩
  rw [← upperTriangular_pow_diag A hA k i, hk]
  rfl

theorem upperTriangular_nilpotent_of_diag_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsUpperTriangular)
    (hz : ∀ i, A i i = 0) : IsNilpotent A := by
  have hp : A.charpoly = Polynomial.X ^ n := by
    rw [Matrix.charpoly_of_isUpperTriangular A hA]
    simp [hz]
  refine ⟨n, ?_⟩
  have h := Matrix.aeval_self_charpoly A
  simpa only [hp, map_pow, Polynomial.aeval_X] using h

namespace TriangularAdjoint

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
variable (T : TriangularAdjoint L n)

@[simp] theorem character_eq_diag (i : Fin n) (x : L) :
    T.character i x = LinearMap.toMatrix T.basis T.basis (LieAlgebra.ad ℝ L x) i i := by
  simp [character, LinearMap.toMatrix_apply]

/-- The diagonal of a commutator of upper triangular matrices vanishes. -/
theorem character_lie (i : Fin n) (x y : L) : T.character i ⁅x, y⁆ = 0 := by
  have had : LieAlgebra.ad ℝ L ⁅x, y⁆ =
      LieAlgebra.ad ℝ L x * LieAlgebra.ad ℝ L y -
        LieAlgebra.ad ℝ L y * LieAlgebra.ad ℝ L x := by
    ext z
    change ⁅⁅x, y⁆, z⁆ = ⁅x, ⁅y, z⁆⁆ - ⁅y, ⁅x, z⁆⁆
    exact lie_lie x y z
  rw [character_eq_diag, had, map_sub, LinearMap.toMatrix_mul,
    LinearMap.toMatrix_mul, Matrix.sub_apply,
    upperTriangular_mul_diag _ _ (T.upper x) (T.upper y),
    upperTriangular_mul_diag _ _ (T.upper y) (T.upper x), mul_comm, sub_self]

/-- The canonical height map kills the Lie bracket, so its quotient is abelian. -/
theorem height_lie (x y : L) : heightProjection T.character ⁅x, y⁆ = 0 :=
  heightProjection_lie_eq_zero T.character T.character_lie x y

/-- The common character kernel is a Lie ideal, not just a linear subspace. -/
noncomputable def kernelIdeal : LieIdeal ℝ L where
  __ := heightKernel T.character
  lie_mem := by
    intro x y _
    exact (mem_heightKernel T.character _).mpr fun i => T.character_lie i x y

@[simp] theorem mem_kernelIdeal (x : L) :
    x ∈ T.kernelIdeal ↔ ∀ i, T.character i x = 0 := mem_heightKernel T.character x

/-- Every element of the height kernel acts nilpotently on the entire Lie algebra. -/
theorem ad_nilpotent_of_mem_kernel (x : L) (hx : x ∈ T.kernelIdeal) :
    IsNilpotent (LieAlgebra.ad ℝ L x) := by
  have hz (i : Fin n) :
      LinearMap.toMatrix T.basis T.basis (LieAlgebra.ad ℝ L x) i i = 0 := by
    rw [← T.character_eq_diag]
    exact (T.mem_kernelIdeal x).mp hx i
  obtain ⟨k, hk⟩ := upperTriangular_nilpotent_of_diag_zero _ (T.upper x) hz
  refine ⟨k, (LinearMap.toMatrixAlgEquiv T.basis).injective ?_⟩
  rw [map_pow, map_zero]
  exact hk

/-- Conversely, a nilpotent adjoint operator has zero diagonal characters. -/
theorem mem_kernelIdeal_of_ad_nilpotent (x : L)
    (hx : IsNilpotent (LieAlgebra.ad ℝ L x)) : x ∈ T.kernelIdeal := by
  apply (T.mem_kernelIdeal x).mpr
  intro i
  rw [T.character_eq_diag]
  exact upperTriangular_nilpotent_diag _ (T.upper x)
    (hx.map (LinearMap.toMatrixAlgEquiv T.basis).toRingHom) i

end TriangularAdjoint
end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanModel
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nilpotent ideal in the Cartan model

Nonzero generalized root vectors lie in the derived algebra. Their generated
ideal is nilpotent for an actual triangular adjoint representation, and its
sum with the Cartan subalgebra is the full Lie algebra.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

set_option maxHeartbeats 1000000 in
/-- A generalized eigenvector for a nonzero eigenvalue lies in every
submodule containing the image of the operator. -/
theorem mem_submodule_of_generalized_eigenvector
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S : Submodule ℝ V) (f : Module.End ℝ V) (hf : ∀ v, f v ∈ S)
    {a : ℝ} (ha : a ≠ 0) (k : ℕ) (v : V)
    (hv : ((f - a • 1) ^ k) v = 0) : v ∈ S := by
  induction k generalizing v with
  | zero =>
    have hz : v = 0 := by simpa using hv
    rw [hz]
    exact S.zero_mem
  | succ k ih =>
    have hy : (f - a • 1) v ∈ S := by
      apply ih
      simpa only [pow_succ, Module.End.mul_apply] using hv
    have hsmul : a • v ∈ S := by
      convert S.sub_mem (hf v) hy using 1
      all_goals try with_reducible_and_instances rfl
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      abel
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using S.smul_mem a⁻¹ hsmul

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- Nonzero generalized roots lie in every ideal containing the brackets. -/
theorem nonzero_root_le_ideal (I : LieIdeal ℝ L)
    (hI : ∀ x y : L, ⁅x, y⁆ ∈ I)
    (χ : Weight ℝ H L) (hχ : χ.IsNonZero) : rootSpace H χ ≤ I.restr H := by
  have hex : ∃ h : H, χ h ≠ 0 := by
    by_contra! hz
    apply hχ
    funext h
    exact hz h
  obtain ⟨h, hh⟩ := hex
  intro v hv
  obtain ⟨k, hk⟩ := (mem_genWeightSpace L (χ : H → ℝ) v).mp hv h
  exact mem_submodule_of_generalized_eigenvector I.toSubmodule
    (toEnd ℝ H L h) (fun v => hI h v) hh k v hk

set_option maxHeartbeats 1000000 in
/-- The ideal generated by the nonzero generalized root spaces. -/
def cartanRootIdeal : LieIdeal ℝ L :=
  LieSubmodule.lieSpan ℝ L {v | ∃ χ : Weight ℝ H L, χ.IsNonZero ∧ v ∈ rootSpace H χ}

set_option maxHeartbeats 1000000 in
/-- The real upper triangular adjoint representation makes the nonzero-root
ideal a subideal of the canonical nilpotent kernel. -/
theorem cartanRootIdeal_le_kernel {n : ℕ} (T : TriangularAdjoint L n) :
    cartanRootIdeal H ≤ T.kernelIdeal := by
  apply LieSubmodule.lieSpan_le.mpr
  rintro v ⟨χ, hχ, hv⟩
  apply nonzero_root_le_ideal H T.kernelIdeal _ χ hχ hv
  intro x y
  exact (T.mem_kernelIdeal _).mpr fun i => T.character_lie i x y

set_option maxHeartbeats 1000000 in
/-- The Cartan subalgebra and the nonzero-root ideal span the full algebra.
Their overlap is retained; no complementary-subalgebra assertion is used. -/
theorem cartanRootIdeal_sup_cartan [FiniteDimensional ℝ L]
    [LieModule.IsTriangularizable ℝ H L] :
    (cartanRootIdeal H).toSubmodule ⊔ H.toSubmodule = ⊤ := by
  have hroot : (⨆ χ : Weight ℝ H L, ⨆ (_ : χ.IsNonZero), rootSpace H χ) ≤
      (cartanRootIdeal H).restr H := by
    apply iSup_le
    intro χ
    apply iSup_le
    intro hχ v hv
    exact LieSubmodule.subset_lieSpan ⟨χ, hχ, hv⟩
  have hh : H.toLieSubmodule ⊔ (cartanRootIdeal H).restr H = ⊤ := by
    apply top_unique
    rw [← cartan_sup_iSup_rootSpace_eq_top (H := H)]
    exact sup_le_sup le_rfl hroot
  have heq := congrArg LieSubmodule.toSubmodule hh
  change H.toSubmodule ⊔ (cartanRootIdeal H).toSubmodule = ⊤ at heq
  simpa only [sup_comm] using heq

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularPrimary
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primary decomposition from the triangular adjoint basis

The real triangular basis supplies the real generalized eigenspace
decomposition required by the Cartan root-space construction.
-/

noncomputable section

open scoped BigOperators

namespace PolycyclicRecognition

theorem prod_dvd_pow_card {R I : Type*} [CommMonoid R]
    (s : Finset I) (f : I → R) (a : R) (h : ∀ i ∈ s, f i ∣ a) :
    (∏ i ∈ s, f i) ∣ a ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ']
    exact mul_dvd_mul (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

/-- An annihilating product of real linear factors gives a decomposition
into generalized eigenspaces, including repeated eigenvalues. -/
theorem iSup_maxGenEigenspace_eq_top_of_annihilating_product
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (F : Module.End ℝ V) (S : Finset ℝ) (n : ℕ)
    (hzero : Polynomial.aeval F ((∏ a ∈ S, (Polynomial.X - Polynomial.C a)) ^ n) = 0) :
    (⨆ a : ℝ, F.maxGenEigenspace a) = ⊤ := by
  let g : ℝ → Module.End ℝ V := fun a => (F - a • 1) ^ n
  have hcomm (a b : ℝ) : Commute (g a) (g b) := by
    have ha : Commute (a • (1 : Module.End ℝ V)) (F - b • 1) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (Algebra.commute_algebraMap_left a (F - b • 1))
    have hb : Commute F (b • (1 : Module.End ℝ V)) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (Algebra.commute_algebraMap_right b F)
    exact ((Commute.sub_right (Commute.refl F) hb).sub_left ha).pow_pow _ _
  have hmap := Finset.map_noncommProd S (fun a => (Polynomial.X - Polynomial.C a) ^ n)
    (fun _ _ _ _ _ => Commute.all _ _) (Polynomial.aeval F).toRingHom
  change Polynomial.aeval F (S.noncommProd _ _) = S.noncommProd
    (fun a => Polynomial.aeval F ((Polynomial.X - Polynomial.C a) ^ n)) _ at hmap
  have hprod : S.noncommProd g (fun a _ b _ _ => hcomm a b) = 0 := by
    have he : Polynomial.aeval F ((∏ a ∈ S, (Polynomial.X - Polynomial.C a)) ^ n) =
        S.noncommProd g (fun a _ b _ _ => hcomm a b) := by
      simpa only [g, Finset.noncommProd_eq_prod, ← Finset.prod_pow, map_pow, map_sub,
        Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one] using hmap
    exact he.symm.trans hzero
  have hind : S.SupIndep (fun a => LinearMap.ker (g a)) := by
    simpa only [g, ← Module.End.genEigenspace_nat] using
      (F.independent_genEigenspace (n : ℕ∞)).supIndep' S
  have hk := LinearMap.ker_noncommProd_eq_of_supIndep_ker S
    (fun a _ b _ _ => hcomm a b) hind
  rw [hprod, LinearMap.ker_zero] at hk
  apply top_unique
  rw [hk]
  apply iSup_le
  intro a
  apply iSup_le
  intro _
  rw [show LinearMap.ker (g a) = F.genEigenspace a (n : ℕ∞) by
    exact Module.End.genEigenspace_nat.symm]
  exact ((F.genEigenspace a).monotone le_top).trans (le_iSup F.maxGenEigenspace a)

namespace TriangularAdjoint

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)

/-- The real triangular adjoint basis implies real triangularizability
in the generalized-eigenspace sense used by the library's Cartan theory. -/
theorem isTriangularizable (T : TriangularAdjoint L n) :
    LieModule.IsTriangularizable ℝ L L where
  maxGenEigenspace_eq_top x := by
    classical
    let F := LieAlgebra.ad ℝ L x
    let d : Fin n → ℝ := fun i => T.character i x
    let S := Finset.univ.image d
    let Q : Polynomial ℝ := ∏ a ∈ S, (Polynomial.X - Polynomial.C a)
    have hdiv : F.charpoly ∣ Q ^ n := by
      rw [← LinearMap.charpoly_toMatrix F T.basis,
        Matrix.charpoly_of_isUpperTriangular _ (T.upper x)]
      have hh := prod_dvd_pow_card Finset.univ
        (fun i : Fin n => Polynomial.X - Polynomial.C (d i)) Q (by
          intro i _
          exact Finset.dvd_prod_of_mem _ (Finset.mem_image_of_mem d (Finset.mem_univ i)))
      simpa only [Finset.card_univ, Fintype.card_fin, d, character_eq_diag] using hh
    obtain ⟨q, hq⟩ := hdiv
    apply iSup_maxGenEigenspace_eq_top_of_annihilating_product F S n
    change Polynomial.aeval F (Q ^ n) = 0
    rw [hq, map_mul, F.aeval_self_charpoly, zero_mul]

end TriangularAdjoint

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanDecomposition
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan models for the real triangular adjoint action

The nilpotent ideal and Cartan subalgebra span the algebra, and the Cartan
subalgebra maps onto the actual canonical height quotient.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)

set_option maxHeartbeats 1000000 in
theorem triangular_cartan_spanning (T : TriangularAdjoint L n)
    (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] :
    (cartanRootIdeal H).toSubmodule ⊔ H.toSubmodule = ⊤ := by
  let := T.isTriangularizable
  exact cartanRootIdeal_sup_cartan H

set_option maxHeartbeats 1000000 in
/-- Every height has a representative in the Cartan subalgebra. -/
theorem cartan_height_surjective (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] :
    Function.Surjective ((heightProjection T.character).comp H.subtype) := by
  intro w
  obtain ⟨x, hx⟩ := heightProjection_surjective T.character w
  have hx' : x ∈ (cartanRootIdeal H).toSubmodule ⊔ H.toSubmodule := by
    rw [triangular_cartan_spanning T H]
    trivial
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx'
  refine ⟨⟨v, hv⟩, ?_⟩
  have hz : heightProjection T.character u = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (cartanRootIdeal_le_kernel H T hu)
  change heightProjection T.character v = w
  rw [← hx, ← huv, map_add, hz, zero_add]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTrace
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unimodularity on the Cartan ideal

The quotient of the ambient algebra by its nonzero-root ideal is generated
by the nilpotent Cartan subalgebra. Its induced adjoint operators are
nilpotent. Consequently restriction to the ideal preserves the trace.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

include T

set_option maxHeartbeats 1000000 in
theorem cartan_quotient_ad_nilpotent (h : H) :
    let N := (cartanRootIdeal H).toSubmodule
    _root_.IsNilpotent (N.mapQ N (ad ℝ L h)
      (fun _ hx => (cartanRootIdeal H).lie_mem hx)) := by
  let N := (cartanRootIdeal H).toSubmodule
  let A := N.mapQ N (ad ℝ L h) (fun _ hx => (cartanRootIdeal H).lie_mem hx)
  let φ : H →ₗ[ℝ] (L ⧸ N) := N.mkQ.comp H.subtype
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := N.mkQ_surjective q
    have hx : x ∈ N ⊔ H.toSubmodule := by
      rw [triangular_cartan_spanning T H]
      trivial
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨v, hv⟩, ?_⟩
    change N.mkQ v = N.mkQ (u + v)
    have hu' : N.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hu
    rw [map_add, hu', zero_add]
  have hinter (x : H) : A (φ x) = φ (ad ℝ H h x) := rfl
  have hpow (k : ℕ) (x : H) : (A ^ k) (φ x) = φ ((ad ℝ H h ^ k) x) := by
    induction k with
    | zero => rfl
    | succ k hk =>
      rw [pow_succ', Module.End.mul_apply, hk, hinter, pow_succ', Module.End.mul_apply]
  obtain ⟨k, hk⟩ := LieAlgebra.nilpotent_ad_of_nilpotent_algebra (R := ℝ) (L := H)
  refine ⟨k, ?_⟩
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := hφ q
  rw [hpow, hk h]
  rfl

set_option maxHeartbeats 1000000 in
/-- The trace-zero action required by the support data follows from ambient
unimodularity, even when the Cartan subgroup overlaps the root ideal. -/
theorem trace_cartanRootIdeal_eq_zero
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0) (h : H) :
    LinearMap.trace ℝ (cartanRootIdeal H) (toEnd ℝ H (cartanRootIdeal H) h) = 0 := by
  let N := (cartanRootIdeal H).toSubmodule
  have hf : ∀ x ∈ N, ad ℝ L h x ∈ N :=
    fun _ hx => (cartanRootIdeal H).lie_mem hx
  have ht := trace_eq_restrict_of_nilpotent_quotient N (ad ℝ L h) hf
    (cartan_quotient_ad_nilpotent T H h)
  have heq : (ad ℝ L h).restrict hf = toEnd ℝ H (cartanRootIdeal H) h := by
    ext x
    rfl
  rw [heq] at ht
  exact ht.symm.trans (hunimod h)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HomogeneousGenerators
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.wordBasisOfDet_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing generators and their positive word multiplicities

A basis of the abelianization can be selected from any homogeneous spanning
pool. Its lifts generate the nilpotent algebra. Every bracket-word basis
then uses every selected generator, which is the positivity needed in the
support-volume formula.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

variable {I : Type*} [DecidableEq I]

/-- An abelian coordinate of a word without the corresponding letter is zero. -/
theorem abelian_coordinate_eval_eq_zero_of_count_zero
    (X : I → L) (f : L →ₗ[ℝ] ℝ) (i : I)
    (hbracket : ∀ x y : L, f ⁅x, y⁆ = 0)
    (hX : ∀ j, j ≠ i → f (X j) = 0)
    (w : FreeMagma I) (hw : bracketWordCount w i = 0) :
    f (evalBracketWord X w) = 0 := by
  cases w with
  | of j =>
    have hij : i ≠ j := by
      intro heq
      simp [bracketWordCount, heq] at hw
    exact hX j hij.symm
  | mul a b => exact hbracket _ _

/-- Every word basis uses every generator whose images are a basis in an
abelian quotient. In particular its total letter count is strictly positive. -/
theorem positive_bracketWord_multiplicities
    [Fintype I] {J Q : Type*} [Fintype J]
    [AddCommGroup Q] [Module ℝ Q]
    (q : L →ₗ[ℝ] Q) (hq : ∀ x y : L, q ⁅x, y⁆ = 0)
    (X : I → L) (bq : Basis I ℝ Q) (hX : ∀ i, q (X i) = bq i)
    (b : Basis J ℝ L) (words : J → FreeMagma I)
    (hwords : ∀ j, evalBracketWord X (words j) = b j) :
    ∀ i, 0 < ∑ j, bracketWordCount (words j) i := by
  intro i
  by_contra hn
  have hcounts : ∀ j, bracketWordCount (words j) i = 0 := by
    have hsum : ∑ j, bracketWordCount (words j) i = 0 := Nat.eq_zero_of_not_pos hn
    exact fun j => Nat.eq_zero_of_le_zero
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hsum.le)
  let f := (bq.coord i).comp q
  have hf : f = 0 := b.ext fun j => by
    rw [← hwords]
    apply abelian_coordinate_eval_eq_zero_of_count_zero X f i
    · intro x y
      simp only [f, LinearMap.comp_apply, hq, map_zero]
    · intro k hk
      simp [f, hX, Basis.coord_apply, hk]
    · exact hcounts j
  have h := congrArg (fun F : L →ₗ[ℝ] ℝ => F (X i)) hf
  simp [f, hX, Basis.coord_apply] at h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWeights
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan roots descend to and separate canonical height

The roots vanish on the canonical nilpotent kernel. Conversely, vanishing of
all nonzero roots forces zero canonical height. Thus the weight coordinates
used by the box estimates are coordinates on the actual canonical quotient.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ L] in
theorem cartan_weight_zero_of_height_zero (χ : Weight ℝ H L) (h : H)
    (hh : heightProjection T.character h = 0) : χ h = 0 := by
  apply χ.apply_eq_zero_of_isNilpotent h
  apply T.ad_nilpotent_of_mem_kernel
  exact (Submodule.Quotient.mk_eq_zero _).mp hh

set_option maxHeartbeats 1000000 in
/-- Choose a linear Cartan representative of each height. -/
def cartanHeightSection : HeightSpace T.character →ₗ[ℝ] H :=
  Classical.choose (((heightProjection T.character).comp H.subtype).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (cartan_height_surjective T H)))

set_option maxHeartbeats 1000000 in
@[simp] theorem cartanHeightSection_height (w : HeightSpace T.character) :
    heightProjection T.character (cartanHeightSection T H w : L) = w := by
  have hs := Classical.choose_spec (((heightProjection T.character).comp H.subtype).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (cartan_height_surjective T H)))
  exact congrArg (fun f : HeightSpace T.character →ₗ[ℝ] HeightSpace T.character => f w) hs

set_option maxHeartbeats 1000000 in
/-- A Cartan root as a linear form on the canonical height quotient. -/
def cartanHeightWeight (χ : Weight ℝ H L) : HeightSpace T.character →ₗ[ℝ] ℝ :=
  (χ : H →ₗ[ℝ] ℝ).comp (cartanHeightSection T H)

set_option maxHeartbeats 1000000 in
@[simp] theorem cartanHeightWeight_projection (χ : Weight ℝ H L) (h : H) :
    cartanHeightWeight T H χ (heightProjection T.character h) = χ h := by
  have hz : heightProjection T.character
      ((cartanHeightSection T H (heightProjection T.character h) - h : H) : L) = 0 := by
    change heightProjection T.character
      ((cartanHeightSection T H (heightProjection T.character h) : L) - h) = 0
    rw [map_sub, cartanHeightSection_height, sub_self]
  have hc := cartan_weight_zero_of_height_zero T H χ _ hz
  change χ (cartanHeightSection T H (heightProjection T.character h) - h) = 0 at hc
  rw [map_sub, sub_eq_zero] at hc
  exact hc

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordBasis
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A homogeneous bracket-word basis of the Cartan ideal

This supplies actual nonzero-root letters and strictly positive integral
letter multiplicities for the nilpotent box data.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
abbrev cartanRootAbelianization :=
  (cartanRootIdeal H) ⧸ (LieModule.lowerCentralSeries ℝ
    (cartanRootIdeal H) (cartanRootIdeal H) 1).toSubmodule

set_option maxHeartbeats 1000000 in
/-- The weights of a generating family in the Cartan ideal already separate
canonical height; one need not retain the full set of adjoint weights. -/
theorem cartan_generator_weights_separate [FiniteDimensional ℝ L]
    {n : ℕ} (T : TriangularAdjoint L n) {I : Type*}
    (X : I → cartanRootIdeal H) (χ : I → Weight ℝ H L)
    (hX : ∀ i, (X i : L) ∈ rootSpace H (χ i))
    (hgen : LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (Set.range X) = ⊤)
    (w : HeightSpace T.character)
    (hw : ∀ i, cartanHeightWeight T H (χ i) w = 0) : w = 0 := by
  let h := cartanHeightSection T H w
  let V := (LieAlgebra.ad ℝ L h).maxGenEigenspace 0
  have hletter (i : I) : (X i : L) ∈ V := by
    have hi := genWeightSpace_le_genWeightSpaceOf L h (χ i : H → ℝ) (hX i)
    have hχ : χ i h = 0 := hw i
    change (X i : L) ∈ (toEnd ℝ H L h).maxGenEigenspace (χ i h) at hi
    rw [hχ] at hi
    exact hi
  have hbracket {x y : L} (hx : x ∈ V) (hy : y ∈ V) : ⁅x, y⁆ ∈ V := by
    simpa only [V, LieAlgebra.ad, zero_add] using
      LieModule.lie_mem_maxGenEigenspace_toEnd hx hy
  have hN (x : cartanRootIdeal H) : (x : L) ∈ V := by
    have hx : x ∈ LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (Set.range X) := by
      rw [hgen]
      trivial
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hletter i
    | zero => exact V.zero_mem
    | add x y _ _ hx hy => exact V.add_mem hx hy
    | smul r x _ hx => exact V.smul_mem r hx
    | lie x y _ _ hx hy => exact hbracket hx hy
  have hH (x : H) : (x : L) ∈ V := by
    have hx : (x : L) ∈ rootSpace H (0 : H → ℝ) := by
      rw [rootSpace_zero_eq]
      exact x.property
    exact genWeightSpace_le_genWeightSpaceOf L h (0 : H → ℝ) hx
  have htop : V = ⊤ := by
    apply top_unique
    rw [← triangular_cartan_spanning T H]
    exact sup_le (fun x hx => hN ⟨x, hx⟩) (fun x hx => hH ⟨x, hx⟩)
  have hnil : _root_.IsNilpotent (LieAlgebra.ad ℝ L h) := by
    dsimp only [V] at htop
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
      Module.End.genEigenspace_nat, zero_smul, sub_zero, LinearMap.ker_eq_top] at htop
    exact ⟨Module.finrank ℝ L, htop⟩
  have hp := (Submodule.Quotient.mk_eq_zero _).mpr
    (T.mem_kernelIdeal_of_ad_nilpotent h hnil)
  change heightProjection T.character (h : L) = 0 at hp
  simpa only [h, cartanHeightSection_height] using hp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightBasisTrace
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Trace in an arbitrary generalized-weight basis

Bracket-word bases need not triangularize the nilpotent parts of the Cartan
action. The trace is nevertheless the sum of their weights. We prove this by
separating the scalar action on each generalized weight space; the residual
operator has zero trace on every such space.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped BigOperators

variable {H M J : Type*} [LieRing H] [LieAlgebra ℝ H] [LieRing.IsNilpotent H]
  [AddCommGroup M] [Module ℝ M] [LieRingModule H M] [LieModule ℝ H M]
  [FiniteDimensional ℝ M] [Fintype J]

theorem trace_eq_sum_of_generalizedWeight_basis
    (b : Basis J ℝ M) (χ : J → Weight ℝ H M)
    (hb : ∀ j, b j ∈ genWeightSpace M (χ j)) (h : H) :
    LinearMap.trace ℝ M (toEnd ℝ H M h) = ∑ j, χ j h := by
  classical
  let S : Weight ℝ H M → Submodule ℝ M := fun α => (genWeightSpace M α).toSubmodule
  have hsp : iSup S = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Submodule.mem_iSup_of_mem (χ j) (hb j)
  have hind : iSupIndep S :=
    LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace' ℝ H M)
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsp
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap S) hds
  let D : M →ₗ[ℝ] M := (DirectSum.toModule ℝ (Weight ℝ H M) M
    (fun α => (α h) • (S α).subtype)).comp e.symm.toLinearMap
  have hD (α : Weight ℝ H M) (x : M) (hx : x ∈ S α) : D x = α h • x := by
    have he : e (DirectSum.lof ℝ (Weight ℝ H M) (fun α => S α) α ⟨x, hx⟩) = x :=
      DirectSum.coeLinearMap_lof S α ⟨x, hx⟩
    change (DirectSum.toModule ℝ (Weight ℝ H M) M
      (fun α => (α h) • (S α).subtype)) (e.symm x) = _
    rw [← he, e.symm_apply_apply, DirectSum.toModule_lof]
    rw [he]
    rfl
  let f := toEnd ℝ H M h
  have hstable (α : Weight ℝ H M) : Set.MapsTo (f - D) (S α) (S α) := by
    intro x hx
    change f x - D x ∈ S α
    rw [hD α x hx]
    exact (genWeightSpace M α).sub_mem ((genWeightSpace M α).lie_mem hx)
      ((genWeightSpace M α).smul_mem _ hx)
  have htrace : LinearMap.trace ℝ M (f - D) = 0 := by
    rw [LinearMap.trace_eq_sum_trace_restrict hds hstable]
    apply Finset.sum_eq_zero
    intro α _
    have hr : (f - D).restrict (hstable α) =
        toEnd ℝ H (genWeightSpace M α) h - (α h) • LinearMap.id := by
      ext x
      change f x - D x = f x - α h • (x : M)
      rw [hD α x x.property]
    rw [hr, map_sub, map_smul, LinearMap.trace_id]
    change LinearMap.trace ℝ (genWeightSpace M α)
      (toEnd ℝ H (genWeightSpace M α) h) -
        α h • (Module.finrank ℝ (genWeightSpace M α) : ℝ) = 0
    rw [trace_toEnd_genWeightSpace]
    simp only [nsmul_eq_mul, smul_eq_mul, mul_comm, sub_self]
  have hDtrace : LinearMap.trace ℝ M D = ∑ j, χ j h := by
    rw [LinearMap.trace_eq_matrix_trace ℝ b]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hD (χ j) (b j) (hb j)]
    simp
  rw [map_sub, sub_eq_zero] at htrace
  exact htrace.trans hDtrace

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordTrace
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Balanced letter counts for actual Cartan word bases

The trace calculation is valid for generalized roots: no diagonalizability
or triangularity of the chosen word basis is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped BigOperators

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  (X : I → cartanRootIdeal H) (χ : I → Weight ℝ H L)
  (hX : ∀ i, (X i : L) ∈ rootSpace H (χ i))

include hX

set_option maxHeartbeats 1000000 in
theorem cartan_word_mem_genWeight (w : FreeMagma I) :
    evalBracketWord X w ∈ genWeightSpace (cartanRootIdeal H)
      (bracketWordWeight (fun i => (χ i : H →ₗ[ℝ] ℝ)) w) := by
  let α := fun i => (χ i : H →ₗ[ℝ] ℝ)
  have hm : evalBracketWord (fun i => (X i : L)) w ∈
      genWeightSpace L (bracketWordWeight α w) := by
    apply (mem_genWeightSpace L _ _).mpr
    intro h
    have hi (i : I) (h : H) : (X i : L) ∈
        (ad ℝ L h).maxGenEigenspace (α i h) :=
      genWeightSpace_le_genWeightSpaceOf L h (χ i) (hX i)
    have hw := evalBracketWord_mem_generalizedWeight H α (fun i => (X i : L)) hi w h
    change evalBracketWord (fun i => (X i : L)) w ∈
      (toEnd ℝ H L h).maxGenEigenspace (bracketWordWeight α w h) at hw
    simpa only [Module.End.mem_maxGenEigenspace] using hw
  let ι : (cartanRootIdeal H) →ₗ⁅ℝ,H⁆ L := ((cartanRootIdeal H).restr H).incl
  rw [← comap_genWeightSpace_eq_of_injective (f := ι)
    ((cartanRootIdeal H).restr H).injective_incl]
  change ι (evalBracketWord X w) ∈ genWeightSpace L (bracketWordWeight α w)
  change (cartanRootIdeal H).incl (evalBracketWord X w) ∈ _
  rw [evalBracketWord_map]
  exact hm

variable [Fintype I] [DecidableEq I]

set_option maxHeartbeats 1000000 in
/-- The trace character on the ideal is the sum of the actual letter weights,
counted with their occurrences in the selected word basis. -/
theorem trace_cartan_word_basis {J : Type*} [Fintype J]
    (b : Basis J ℝ (cartanRootIdeal H)) (words : J → FreeMagma I)
    (hwords : ∀ j, evalBracketWord X (words j) = b j) (h : H) :
    LinearMap.trace ℝ (cartanRootIdeal H) (toEnd ℝ H (cartanRootIdeal H) h) =
      ∑ i, ((∑ j, bracketWordCount (words j) i : ℕ) : ℝ) * χ i h := by
  let α := fun i => (χ i : H →ₗ[ℝ] ℝ)
  have hm (j : J) : b j ∈ genWeightSpace (cartanRootIdeal H)
      (bracketWordWeight α (words j)) := by
    rw [← hwords j]
    exact cartan_word_mem_genWeight H X χ hX (words j)
  let ψ : J → Weight ℝ H (cartanRootIdeal H) := fun j =>
    { toFun := bracketWordWeight α (words j)
      genWeightSpace_ne_bot' := by
        intro hz
        have hh := hm j
        rw [hz] at hh
        change b j = 0 at hh
        exact b.ne_zero j hh }
  have ht := trace_eq_sum_of_generalizedWeight_basis b ψ hm h
  change LinearMap.trace ℝ (cartanRootIdeal H) (toEnd ℝ H (cartanRootIdeal H) h) =
    ∑ j, bracketWordWeight α (words j) h at ht
  rw [ht]
  simp_rw [bracketWordWeight_eq_count, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

set_option maxHeartbeats 1000000 in
theorem balanced_cartan_word_counts {n : ℕ} (T : TriangularAdjoint L n)
    {J : Type*} [Fintype J]
    (b : Basis J ℝ (cartanRootIdeal H)) (words : J → FreeMagma I)
    (hwords : ∀ j, evalBracketWord X (words j) = b j)
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
    (w : HeightSpace T.character) :
    ∑ i, ((∑ j, bracketWordCount (words j) i : ℕ) : ℝ) *
      cartanHeightWeight T H (χ i) w = 0 := by
  have ht := (trace_cartan_word_basis H X χ hX b words hwords
    (cartanHeightSection T H w)).symm.trans
      (trace_cartanRootIdeal_eq_zero T H hunimod (cartanHeightSection T H w))
  exact ht

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSupportData
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support data from the actual Cartan ideal

Every finite family of word bases in homogeneous lifts of an abelianization
basis gives balanced positive support data. The ambient adjoint action need
only be triangularizable, not diagonalizable.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  {n m : ℕ} (T : TriangularAdjoint L n)
  (X : Fin m → cartanRootIdeal H) (χ : Fin m → Weight ℝ H L)
  (hX : ∀ i, (X i : L) ∈ rootSpace H (χ i))
  (bq : Basis (Fin m) ℝ (cartanRootAbelianization H))
  (hXq : ∀ i, (lowerCentralSeries ℝ (cartanRootIdeal H)
    (cartanRootIdeal H) 1).toSubmodule.mkQ (X i) = bq i)
  (hgen : LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (Set.range X) = ⊤)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)

set_option maxHeartbeats 1000000 in
/-- Support data for any finite collection of actual word bases. -/
def cartanSupportDatum {B J : Type*} [Fintype B] [Fintype J]
    (b : B → Basis J ℝ (cartanRootIdeal H))
    (words : B → J → FreeMagma (Fin m))
    (hwords : ∀ β j, evalBracketWord X (words β j) = b β j) :
    SupportDatum (HeightSpace T.character) (Fin m) B where
  weight i := cartanHeightWeight T H (χ i)
  multiplicity β i := ∑ j, bracketWordCount (words β j) i
  positive β := by
    let C := (lowerCentralSeries ℝ (cartanRootIdeal H)
      (cartanRootIdeal H) 1).toSubmodule
    apply positive_bracketWord_multiplicities C.mkQ _ X bq hXq (b β) (words β) (hwords β)
    intro x y
    apply (Submodule.Quotient.mk_eq_zero C).mpr
    change ⁅x, y⁆ ∈ lowerCentralSeries ℝ (cartanRootIdeal H) (cartanRootIdeal H) (0 + 1)
    rw [lowerCentralSeries_succ, lowerCentralSeries_zero]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top y)
  balanced β := balanced_cartan_word_counts H X χ hX T (b β) (words β) (hwords β) hunimod
  separates := cartan_generator_weights_separate H T X χ hX hgen

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordModel
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite Cartan word model

The support datum uses all ordered bases selected from a finite list that
contains every nonzero evaluated word. It is therefore attached to the Lie
algebra generators, rather than to an extra family of assumed bases.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule LieAlgebra

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- Finite homogeneous generators, their abelianization basis, and an actual
lower-central-series bound for the Cartan ideal. -/
structure CartanWordModel where
  letterCount : ℕ
  letter : Fin letterCount → cartanRootIdeal H
  weight : Fin letterCount → Weight ℝ H L
  weight_nonzero : ∀ i, (weight i).IsNonZero
  letter_root : ∀ i, (letter i : L) ∈ rootSpace H (weight i)
  abelianBasis : Basis (Fin letterCount) ℝ (cartanRootAbelianization H)
  letter_quotient : ∀ i, (lowerCentralSeries ℝ (cartanRootIdeal H)
    (cartanRootIdeal H) 1).toSubmodule.mkQ (letter i) = abelianBasis i
  generates : LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (Set.range letter) = ⊤
  bound : ℕ
  bound_zero : lowerCentralSeries ℝ (cartanRootIdeal H) (cartanRootIdeal H) bound = ⊥

namespace CartanWordModel

variable {H} (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
abbrev wordList : Finset (FreeMagma (Fin M.letterCount)) := boundedBracketWords M.bound

set_option maxHeartbeats 1000000 in
abbrev Bases := WordBasisSelections M.letter M.wordList

set_option maxHeartbeats 1000000 in
/-- The finite support data derived from all word bases. -/
def supportDatum {n : ℕ} (T : TriangularAdjoint L n)
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0) :
    SupportDatum (HeightSpace T.character) (Fin M.letterCount) M.Bases :=
  cartanSupportDatum H T M.letter M.weight M.letter_root M.abelianBasis
    M.letter_quotient M.generates hunimod
    (WordBasisSelections.basis M.letter M.wordList)
    (WordBasisSelections.words M.letter M.wordList)
    (WordBasisSelections.eval_words M.letter M.wordList)

set_option maxHeartbeats 1000000 in
@[simp] theorem supportDatum_weight {n : ℕ} (T : TriangularAdjoint L n)
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0) (i : Fin M.letterCount) :
    (M.supportDatum T hunimod).weight i = cartanHeightWeight T H (M.weight i) := rfl

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportTemplates
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support exponents of compact templates

The support exponent is the finite maximum of word-basis exponents, with
each letter allowed its own supporting point. Balance gives translation
invariance, and segments recover the support norm.
-/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

def weightSupport (E : Set W) (i : I) : ℝ := sSup (D.weight i '' E)

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWeightDilation
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact dilations of generalized Cartan weight spaces

Scalar multiplication by `exp (χ h)` on every generalized root space defines
an actual Lie automorphism. The nilpotent parts of the Cartan action do not
enter this construction. These are the exact weight dilations used in the
box-translation argument.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule
open scoped DirectSum

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

include T

set_option maxHeartbeats 1000000 in
def cartanWeightDecomposition :
    (⨁ χ : Weight ℝ H L, (genWeightSpace L χ).toSubmodule) ≃ₗ[ℝ] L := by
  classical
  let := T.isTriangularizable
  exact LinearEquiv.ofBijective (DirectSum.coeLinearMap
    (fun χ : Weight ℝ H L => (genWeightSpace L χ).toSubmodule))
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace' ℝ H L))
      (LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top' ℝ H L)))

set_option maxHeartbeats 1000000 in
/-- Scalar dilation on the actual generalized-root direct sum. -/
def cartanWeightScale (h : H) : L →ₗ[ℝ] L := by
  classical
  exact (DirectSum.toModule ℝ (Weight ℝ H L) L
    (fun χ => Real.exp (χ h) • (genWeightSpace L χ).toSubmodule.subtype)).comp
      (cartanWeightDecomposition T H).symm.toLinearMap

set_option maxHeartbeats 1000000 in
theorem cartanWeightScale_apply_root (h : H) (χ : Weight ℝ H L) {x : L}
    (hx : x ∈ rootSpace H χ) : cartanWeightScale T H h x = Real.exp (χ h) • x := by
  classical
  let S := fun χ : Weight ℝ H L => (genWeightSpace L χ).toSubmodule
  have he : cartanWeightDecomposition T H
      (DirectSum.lof ℝ (Weight ℝ H L) (fun χ => S χ) χ ⟨x, hx⟩) = x :=
    DirectSum.coeLinearMap_lof S χ ⟨x, hx⟩
  change (DirectSum.toModule ℝ (Weight ℝ H L) L
    (fun χ => Real.exp (χ h) • (S χ).subtype))
      ((cartanWeightDecomposition T H).symm x) = _
  rw [← he, LinearEquiv.symm_apply_apply, DirectSum.toModule_lof]
  rw [he]
  rfl

set_option maxHeartbeats 1000000 in
/-- This also applies when the weight function is zero or its root space is
zero; it does not require choosing a nonzero root vector. -/
theorem cartanWeightScale_apply_genWeight (h : H) (χ : H → ℝ) {x : L}
    (hx : x ∈ genWeightSpace L χ) :
    cartanWeightScale T H h x = Real.exp (χ h) • x := by
  by_cases hχ : genWeightSpace L χ = ⊥
  · have hx0 : x = 0 := by simpa only [hχ, LieSubmodule.mem_bot] using hx
    simp [hx0]
  · exact cartanWeightScale_apply_root T H h ⟨χ, hχ⟩ hx

set_option maxHeartbeats 1000000 in
theorem cartan_root_induction {p : L → Prop}
    (hp : ∀ (χ : Weight ℝ H L) (x : L), x ∈ rootSpace H χ → p x)
    (hzero : p 0) (hadd : ∀ x y, p x → p y → p (x + y)) (x : L) : p x := by
  let := T.isTriangularizable
  have hx : x ∈ ⨆ χ : Weight ℝ H L, (genWeightSpace L χ).toSubmodule := by
    rw [LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top' ℝ H L)]
    trivial
  exact Submodule.iSup_induction (fun χ : Weight ℝ H L =>
    (genWeightSpace L χ).toSubmodule) (motive := p) hx hp hzero hadd

set_option maxHeartbeats 1000000 in
/-- Addition of generalized weights makes the scalar dilation respect Lie
brackets, even when the Cartan representation is not semisimple. -/
theorem cartanWeightScale_map_lie (h : H) (x y : L) :
    cartanWeightScale T H h ⁅x, y⁆ =
      ⁅cartanWeightScale T H h x, cartanWeightScale T H h y⁆ := by
  apply cartan_root_induction T H (x := x)
  · intro χ u hu
    apply cartan_root_induction T H (x := y)
    · intro ψ v hv
      rw [cartanWeightScale_apply_genWeight T H h (χ + ψ)
        (lie_mem_genWeightSpace_of_mem_genWeightSpace hu hv),
        cartanWeightScale_apply_root T H h χ hu,
        cartanWeightScale_apply_root T H h ψ hv]
      simp only [Pi.add_apply, Real.exp_add, lie_smul, smul_lie, smul_smul, mul_comm]
    · simp
    · intro v w hv hw
      simp only [lie_add, map_add, hv, hw]
  · simp
  · intro u v hu hv
    simp only [add_lie, map_add, hu, hv]

set_option maxHeartbeats 1000000 in
@[simp] theorem cartanWeightScale_add_apply (h k : H) (x : L) :
    cartanWeightScale T H (h + k) x =
      cartanWeightScale T H h (cartanWeightScale T H k x) := by
  apply cartan_root_induction T H (x := x)
  · intro χ u hu
    rw [cartanWeightScale_apply_root T H (h + k) χ hu,
      cartanWeightScale_apply_root T H k χ hu, map_smul,
      cartanWeightScale_apply_root T H h χ hu]
    simp only [map_add, Real.exp_add, smul_smul, mul_comm]
  · simp
  · intro u v hu hv
    simp only [map_add, hu, hv]

set_option maxHeartbeats 1000000 in
@[simp] theorem cartanWeightScale_zero_apply (x : L) : cartanWeightScale T H 0 x = x := by
  apply cartan_root_induction T H (x := x)
  · intro χ u hu
    rw [cartanWeightScale_apply_root T H 0 χ hu]
    simp
  · simp
  · intro u v hu hv
    simp only [map_add, hu, hv]

set_option maxHeartbeats 1000000 in
/-- Exact dilation as a Lie algebra automorphism, with inverse parameter `-h`. -/
def cartanWeightDilation (h : H) : L ≃ₗ⁅ℝ⁆ L where
  toFun := cartanWeightScale T H h
  map_add' := (cartanWeightScale T H h).map_add
  map_smul' := (cartanWeightScale T H h).map_smul
  invFun := cartanWeightScale T H (-h)
  left_inv := fun x => by
    rw [← cartanWeightScale_add_apply, neg_add_cancel, cartanWeightScale_zero_apply]
  right_inv := fun x => by
    rw [← cartanWeightScale_add_apply, add_neg_cancel, cartanWeightScale_zero_apply]
  map_lie' := fun {x y} => cartanWeightScale_map_lie T H h x y

set_option maxHeartbeats 1000000 in
@[simp] theorem cartanWeightDilation_apply (h : H) (x : L) :
    cartanWeightDilation T H h x = cartanWeightScale T H h x := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRootWidths
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root-space widths inside actual word boxes

A nonzero coordinate of a root vector can occur only at a word of the same
weight. Its word exponent dominates the support of that root. Consequently
rescaling a letter-root vector never enlarges its coordinates in the scaled
word box. This includes zero-weight bracket directions.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule LieAlgebra
open scoped BigOperators

namespace CartanWordModel

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

include T

variable (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
omit T hunimod eW [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] in
/-- Inclusion of a nonzero generalized root space into the Cartan ideal. -/
def rootInIdeal (χ : LieModule.Weight ℝ H L) (hχ : χ.IsNonZero) :
    LieAlgebra.rootSpace H χ →ₗ[ℝ] cartanRootIdeal H where
  toFun v := ⟨v, LieSubmodule.subset_lieSpan ⟨χ, hχ, v.property⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlternatingPolynomialCoordinates
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial and smooth coordinates for the alternating product

These coordinates keep the two embedding maps among the coefficient
parameters. The input chart can be any fixed continuous linear equivalence.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

abbrev AlternatingLawData (n : ℕ) :=
  ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ×
    (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexAdjointWeights
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex adjoint weights for solvable real Lie algebras

The existing simultaneous-basis construction applies over the complex
numbers as well. Its restriction to real vectors supplies the weights whose
lifted group characters are used in the general solvable lattice argument.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped TensorProduct
open Module
attribute [local instance 100] LieRing.ofAssociativeRing

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]

/-- The canonical real Lie homomorphism into the complexification. -/
def complexificationLieHom : L →ₗ⁅ℝ⁆ ℂ ⊗[ℝ] L :=
  { toLinearMap := TensorProduct.mk ℝ ℂ L 1
    map_lie' := by
      intro x y
      change 1 ⊗ₜ[ℝ] ⁅x, y⁆ = ⁅(1 : ℂ) ⊗ₜ[ℝ] x, (1 : ℂ) ⊗ₜ[ℝ] y⁆
      simp }

theorem complexificationLieHom_injective : Function.Injective (complexificationLieHom L) := by
  intro x y hxy
  change (1 : ℂ) ⊗ₜ[ℝ] x = (1 : ℂ) ⊗ₜ[ℝ] y at hxy
  apply sub_eq_zero.mp
  apply (Module.FaithfullyFlat.one_tmul_eq_zero_iff ℝ L (A := ℂ) (x - y)).mp
  simpa only [TensorProduct.tmul_sub, sub_eq_zero] using hxy

/-- The complexified adjoint matrices, restricted to the original real algebra. -/
def complexifiedAdjointMatrix {n : ℕ} (b : Basis (Fin n) ℂ (ℂ ⊗[ℝ] L)) :
    L →ₗ⁅ℝ⁆ Matrix (Fin n) (Fin n) ℂ := by
  let j := (LinearMap.toMatrixAlgEquiv b).toLieEquiv.toLieHom.comp
    (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L))
  let jr : (ℂ ⊗[ℝ] L) →ₗ⁅ℝ⁆ Matrix (Fin n) (Fin n) ℂ :=
    { toLinearMap := j.toLinearMap.restrictScalars ℝ
      map_lie' := j.map_lie' }
  exact jr.comp (complexificationLieHom L)

@[simp] theorem complexifiedAdjointMatrix_apply {n : ℕ}
    (b : Basis (Fin n) ℂ (ℂ ⊗[ℝ] L)) (x : L) :
    complexifiedAdjointMatrix L b x =
      LinearMap.toMatrix b b (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L) (1 ⊗ₜ[ℝ] x)) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexificationRealForm
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real form inside a complexified Lie algebra

Real and imaginary tensor coordinates detect membership in a complexified
subalgebra. In particular the complexification of the chosen real Cartan
subalgebra is again Cartan; it is preserved by the canonical conjugation.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]

def complexificationRealPart : (ℂ ⊗[ℝ] L) →ₗ[ℝ] L :=
  (TensorProduct.lid ℝ L).toLinearMap.comp
    (TensorProduct.map Complex.reLm (LinearMap.id : L →ₗ[ℝ] L))

def complexificationImagPart : (ℂ ⊗[ℝ] L) →ₗ[ℝ] L :=
  (TensorProduct.lid ℝ L).toLinearMap.comp
    (TensorProduct.map Complex.imLm (LinearMap.id : L →ₗ[ℝ] L))

@[simp] theorem complexificationRealPart_tmul (z : ℂ) (x : L) :
    complexificationRealPart L (z ⊗ₜ[ℝ] x) = z.re • x := rfl

@[simp] theorem complexificationImagPart_tmul (z : ℂ) (x : L) :
    complexificationImagPart L (z ⊗ₜ[ℝ] x) = z.im • x := rfl

theorem complexification_decompose (x : ℂ ⊗[ℝ] L) :
    x = (1 : ℂ) ⊗ₜ[ℝ] complexificationRealPart L x +
      Complex.I ⊗ₜ[ℝ] complexificationImagPart L x := by
  induction x using OAI.tensorInductionOn with
  | tmul z x =>
    simp only [complexificationRealPart_tmul, complexificationImagPart_tmul]
    rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
    congr 1
    simp
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add]
    conv_lhs => rw [hx, hy]
    abel

/-- Conjugation on the complexification as a real Lie automorphism. -/
def complexificationConjugation : (ℂ ⊗[ℝ] L) ≃ₗ⁅ℝ⁆ (ℂ ⊗[ℝ] L) := by
  let f := LieAlgebra.ExtendScalars.map Complex.conjAe.toAlgHom (LieHom.id : L →ₗ⁅ℝ⁆ L)
  have hi : Function.Involutive f := by
    intro x
    induction x using OAI.tensorInductionOn with
    | tmul z x => simp [f]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  exact { f with invFun := f, left_inv := hi, right_inv := hi }

@[simp] theorem complexificationConjugation_tmul (z : ℂ) (x : L) :
    complexificationConjugation L (z ⊗ₜ[ℝ] x) = star z ⊗ₜ[ℝ] x := rfl

theorem complexification_conjugation_fixed_iff (x : ℂ ⊗[ℝ] L) :
    complexificationConjugation L x = x ↔
      ∃ y : L, x = (1 : ℂ) ⊗ₜ[ℝ] y := by
  constructor
  · intro hx
    have hi : complexificationImagPart L x = 0 := by
      have he := congrArg (complexificationImagPart L) hx
      have hc : complexificationImagPart L (complexificationConjugation L x) =
          -complexificationImagPart L x := by
        clear hx he
        induction x using OAI.tensorInductionOn with
        | tmul z y => simp
        | add x y hx hy => simp [hx, hy, add_comm]
      rw [hc] at he
      have ht : (2 : ℝ) • complexificationImagPart L x = 0 := by
        simpa only [two_smul, ← neg_eq_iff_add_eq_zero] using he
      exact (smul_eq_zero.mp ht).resolve_left (by norm_num)
    exact ⟨complexificationRealPart L x, by simpa [hi] using complexification_decompose L x⟩
  · rintro ⟨y, rfl⟩
    simp

/-- Complexification of the inclusion of a real Lie subalgebra. -/
def complexifiedInclusion (H : LieSubalgebra ℝ L) :
    (ℂ ⊗[ℝ] H) →ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] L) where
  __ := H.incl.toLinearMap.baseChange ℂ
  map_lie' := fun {x y} =>
    (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ) H.incl).map_lie x y

@[simp] theorem complexifiedInclusion_tmul (H : LieSubalgebra ℝ L) (z : ℂ) (h : H) :
    complexifiedInclusion L H (z ⊗ₜ[ℝ] h) = z ⊗ₜ[ℝ] (h : L) := rfl

/-- The actual complex Lie subalgebra generated by the real subalgebra. -/
def complexifiedSubalgebra (H : LieSubalgebra ℝ L) : LieSubalgebra ℂ (ℂ ⊗[ℝ] L) :=
  (complexifiedInclusion L H).range

theorem mem_complexifiedSubalgebra_iff (H : LieSubalgebra ℝ L) (x : ℂ ⊗[ℝ] L) :
    x ∈ complexifiedSubalgebra L H ↔
      complexificationRealPart L x ∈ H ∧ complexificationImagPart L x ∈ H := by
  constructor
  · rintro ⟨y, rfl⟩
    change complexificationRealPart L (complexifiedInclusion L H y) ∈ H ∧
      complexificationImagPart L (complexifiedInclusion L H y) ∈ H
    induction y using OAI.tensorInductionOn with
    | tmul z h =>
      simp only [complexifiedInclusion_tmul, complexificationRealPart_tmul,
        complexificationImagPart_tmul]
      exact ⟨H.smul_mem _ h.property, H.smul_mem _ h.property⟩
    | add x y hx hy =>
      simp only [map_add]
      exact ⟨H.add_mem hx.1 hy.1, H.add_mem hx.2 hy.2⟩
  · rintro ⟨hr, hi⟩
    refine ⟨1 ⊗ₜ[ℝ] (⟨complexificationRealPart L x, hr⟩ : H) +
      Complex.I ⊗ₜ[ℝ] (⟨complexificationImagPart L x, hi⟩ : H), ?_⟩
    change complexifiedInclusion L H
      (1 ⊗ₜ[ℝ] (⟨complexificationRealPart L x, hr⟩ : H) +
      Complex.I ⊗ₜ[ℝ] (⟨complexificationImagPart L x, hi⟩ : H)) = x
    simpa only [map_add, complexifiedInclusion_tmul] using (complexification_decompose L x).symm

theorem complexificationConjugation_involutive (x : ℂ ⊗[ℝ] L) :
    complexificationConjugation L (complexificationConjugation L x) = x :=
  (complexificationConjugation L).left_inv x

theorem complexificationConjugation_inclusion (H : LieSubalgebra ℝ L) (x : ℂ ⊗[ℝ] H) :
    complexificationConjugation L (complexifiedInclusion L H x) =
      complexifiedInclusion L H (complexificationConjugation H x) := by
  induction x using OAI.tensorInductionOn with
  | tmul z h => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem complexifiedSubalgebra_conjugation (H : LieSubalgebra ℝ L)
    {x : ℂ ⊗[ℝ] L} (hx : x ∈ complexifiedSubalgebra L H) :
    complexificationConjugation L x ∈ complexifiedSubalgebra L H := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨complexificationConjugation H y, (complexificationConjugation_inclusion L H y).symm⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexCartanRotations
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rotations on complex Cartan weight spaces

The imaginary parts of the generalized weights define genuine Lie algebra
automorphisms. Their coefficient vectors lie in a fixed compact torus. These
are the rotations to be removed in the real-triangulable model construction.
-/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan

open LieAlgebra LieModule Module
open scoped DirectSum

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- The generalized Cartan decomposition over the complex numbers. -/
def weightDecomposition :
    (⨁ χ : Weight ℂ H L, (genWeightSpace L χ).toSubmodule) ≃ₗ[ℂ] L := by
  classical
  exact LinearEquiv.ofBijective (DirectSum.coeLinearMap
    (fun χ : Weight ℂ H L => (genWeightSpace L χ).toSubmodule))
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace' ℂ H L))
      (LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top' ℂ H L)))

set_option maxHeartbeats 1000000 in
/-- A scalar on each generalized weight block. -/
def weightOperator (z : Weight ℂ H L → ℂ) : L →ₗ[ℂ] L := by
  classical
  exact (DirectSum.toModule ℂ (Weight ℂ H L) L
    (fun χ => z χ • (genWeightSpace L χ).toSubmodule.subtype)).comp
      (weightDecomposition H).symm.toLinearMap

set_option maxHeartbeats 1000000 in
theorem weightOperator_apply (z : Weight ℂ H L → ℂ) (χ : Weight ℂ H L)
    {x : L} (hx : x ∈ genWeightSpace L χ) : weightOperator H z x = z χ • x := by
  classical
  let S := fun χ : Weight ℂ H L => (genWeightSpace L χ).toSubmodule
  have he : weightDecomposition H
      (DirectSum.lof ℂ (Weight ℂ H L) (fun χ => S χ) χ ⟨x, hx⟩) = x :=
    DirectSum.coeLinearMap_lof S χ ⟨x, hx⟩
  change (DirectSum.toModule ℂ (Weight ℂ H L) L
    (fun χ => z χ • (S χ).subtype)) ((weightDecomposition H).symm x) = _
  rw [← he, LinearEquiv.symm_apply_apply, DirectSum.toModule_lof, he]
  rfl

set_option maxHeartbeats 1000000 in
theorem root_induction {p : L → Prop}
    (hp : ∀ (χ : Weight ℂ H L) (x : L), x ∈ genWeightSpace L χ → p x)
    (hzero : p 0) (hadd : ∀ x y, p x → p y → p (x + y)) (x : L) : p x := by
  have hx : x ∈ ⨆ χ : Weight ℂ H L, (genWeightSpace L χ).toSubmodule := by
    rw [LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top' ℂ H L)]
    trivial
  exact Submodule.iSup_induction (fun χ : Weight ℂ H L =>
    (genWeightSpace L χ).toSubmodule) (motive := p) hx hp hzero hadd

end PolycyclicRecognition.ComplexCartan

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexRotationTorus
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact group containing the Cartan rotations

Diagonal unit scalars are invertible on the generalized weight decomposition.
The equations for preserving the bracket and fixing the Cartan algebra cut out
an actual closed subgroup of a finite torus, giving a compact action.
-/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan

open LieAlgebra LieModule Module Set

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

/-- A unit diagonal coefficient vector acts on the entire algebra. -/
def torusOperator (z : Weight ℂ H L → Circle) : Module.End ℂ L :=
  weightOperator H (fun χ => (z χ : ℂ))

@[simp] theorem torusOperator_one (x : L) : torusOperator H 1 x = x := by
  apply root_induction H (x := x)
  · intro χ v hv
    rw [torusOperator, weightOperator_apply H _ χ hv]
    simp
  · simp [torusOperator]
  · intro v w hv hw
    simp only [map_add, hv, hw]

@[simp] theorem torusOperator_mul (z w : Weight ℂ H L → Circle) (x : L) :
    torusOperator H (z * w) x = torusOperator H z (torusOperator H w x) := by
  apply root_induction H (x := x)
  · intro χ v hv
    simp only [torusOperator, weightOperator_apply H _ χ hv, Pi.mul_apply, Circle.coe_mul,
      map_smul, smul_smul, mul_comm]
  · simp [torusOperator]
  · intro v w hv hw
    simp only [map_add, hv, hw]

theorem torusOperator_injective (z : Weight ℂ H L → Circle) :
    Function.Injective (torusOperator H z) := by
  intro x y he
  have h := congrArg (torusOperator H z⁻¹) he
  simpa only [← torusOperator_mul, inv_mul_cancel, torusOperator_one] using h

/-- Bracket-preserving unit coefficient vectors that fix the Cartan algebra. -/
def rotationTorus : Subgroup (Weight ℂ H L → Circle) where
  carrier := {z | (∀ x y : L, torusOperator H z ⁅x, y⁆ =
      ⁅torusOperator H z x, torusOperator H z y⁆) ∧
    ∀ h : H, torusOperator H z h = h}
  one_mem' := by simp
  mul_mem' := by
    rintro z w ⟨hz, hzf⟩ ⟨hw, hwf⟩
    constructor
    · intro x y
      rw [torusOperator_mul, hw, hz, torusOperator_mul, torusOperator_mul]
    · intro h
      rw [torusOperator_mul, hwf, hzf]
  inv_mem' := by
    rintro z ⟨hz, hzf⟩
    constructor
    · intro x y
      apply torusOperator_injective H z
      simp only [← torusOperator_mul, mul_inv_cancel, torusOperator_one]
      rw [hz]
      simp only [← torusOperator_mul, mul_inv_cancel, torusOperator_one]
    · intro h
      apply torusOperator_injective H z
      rw [← torusOperator_mul, mul_inv_cancel, torusOperator_one, hzf]

section Topology

local instance rotationNormedAddCommGroup : NormedAddCommGroup L :=
  NormedAddCommGroup.induced _ _ (finBasis ℂ L).equivFun.toLinearMap
    (finBasis ℂ L).equivFun.injective
local instance rotationNormedSpace : NormedSpace ℂ L :=
  NormedSpace.induced ℂ _ _ (finBasis ℂ L).equivFun.toLinearMap

end Topology
end PolycyclicRecognition.ComplexCartan

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexifiedCartan
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complexification preserves the chosen real Cartan algebra -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]

set_option maxHeartbeats 1000000 in
theorem complexificationRealPart_lie_one (x : ℂ ⊗[ℝ] L) (h : L) :
    complexificationRealPart L ⁅x, (1 : ℂ) ⊗ₜ[ℝ] h⁆ =
      ⁅complexificationRealPart L x, h⁆ := by
  induction x using OAI.tensorInductionOn with
  | tmul z x => simp [smul_lie]
  | add x y hx hy => simp [add_lie, hx, hy]

set_option maxHeartbeats 1000000 in
theorem complexificationImagPart_lie_one (x : ℂ ⊗[ℝ] L) (h : L) :
    complexificationImagPart L ⁅x, (1 : ℂ) ⊗ₜ[ℝ] h⁆ =
      ⁅complexificationImagPart L x, h⁆ := by
  induction x using OAI.tensorInductionOn with
  | tmul z x => simp [smul_lie]
  | add x y hx hy => simp [add_lie, hx, hy]

set_option maxHeartbeats 1000000 in
instance complexifiedSubalgebra_isCartan (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] :
    (complexifiedSubalgebra L H).IsCartanSubalgebra where
  nilpotent := (complexifiedInclusion L H).isNilpotent_range
  self_normalizing := by
    apply le_antisymm _ (complexifiedSubalgebra L H).le_normalizer
    intro x hx
    apply (mem_complexifiedSubalgebra_iff L H x).mpr
    have hn (h : L) (hh : h ∈ H) :
        complexificationRealPart L ⁅x, (1 : ℂ) ⊗ₜ[ℝ] h⁆ ∈ H ∧
        complexificationImagPart L ⁅x, (1 : ℂ) ⊗ₜ[ℝ] h⁆ ∈ H := by
      apply (mem_complexifiedSubalgebra_iff L H _).mp
      apply ((complexifiedSubalgebra L H).mem_normalizer_iff x).mp hx
      exact ⟨1 ⊗ₜ[ℝ] (⟨h, hh⟩ : H), rfl⟩
    constructor
    · have hr : complexificationRealPart L x ∈ H.normalizer := by
        apply (H.mem_normalizer_iff _).mpr
        intro h hh
        simpa only [complexificationRealPart_lie_one] using (hn h hh).1
      rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing] at hr
    · have hi : complexificationImagPart L x ∈ H.normalizer := by
        apply (H.mem_normalizer_iff _).mpr
        intro h hh
        simpa only [complexificationImagPart_lie_one] using (hn h hh).2
      rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing] at hi

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ConjugateCartanWeights
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation of the complex Cartan weight spaces -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- The conjugation induced on the actual complexified Cartan subalgebra. -/
def cartanConjugation (h : complexifiedSubalgebra L H) : complexifiedSubalgebra L H :=
  ⟨complexificationConjugation L h, complexifiedSubalgebra_conjugation L H h.property⟩

set_option maxHeartbeats 1000000 in
omit [H.IsCartanSubalgebra] in
@[simp] theorem cartanConjugation_involutive (h : complexifiedSubalgebra L H) :
    cartanConjugation L H (cartanConjugation L H h) = h := by
  apply Subtype.ext
  exact complexificationConjugation_involutive L h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealCartanRotations
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan rotations preserve the actual real form -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- The original real Cartan algebra inside its complexification. -/
def realCartanInComplex (h : H) : complexifiedSubalgebra L H :=
  ⟨1 ⊗ₜ[ℝ] (h : L), ⟨1 ⊗ₜ[ℝ] h, rfl⟩⟩

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] in
@[simp] theorem cartanConjugation_real (h : H) :
    cartanConjugation L H (realCartanInComplex L H h) = realCartanInComplex L H h := by
  apply Subtype.ext
  simp [cartanConjugation, realCartanInComplex]

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] in
@[simp] theorem realCartanInComplex_add (h k : H) :
    realCartanInComplex L H (h + k) = realCartanInComplex L H h + realCartanInComplex L H k := by
  apply Subtype.ext
  simp [realCartanInComplex, TensorProduct.tmul_add]

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] in
@[simp] theorem realCartanInComplex_zero : realCartanInComplex L H 0 = 0 := by
  apply Subtype.ext
  simp [realCartanInComplex]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealRotationTorus
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compact torus of automorphisms preserving the real form

Commuting with the canonical conjugation is a closed subgroup condition.
The resulting compact subgroup contains every real Cartan rotation.
-/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule Module Set
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

abbrev complexCartanTorus := ComplexCartan.rotationTorus (complexifiedSubalgebra L H)

/-- Those compact diagonal automorphisms which preserve the original real
Lie algebra, expressed by commutation with conjugation. -/
def realRotationTorus : Subgroup (complexCartanTorus L H) where
  carrier := {z | ∀ x : ℂ ⊗[ℝ] L,
    complexificationConjugation L
        (ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val x) =
      ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val
        (complexificationConjugation L x)}
  one_mem' := by simp
  mul_mem' := by
    intro z w hz hw x
    change complexificationConjugation L
      (ComplexCartan.torusOperator _ (z.val * w.val) x) =
      ComplexCartan.torusOperator _ (z.val * w.val) (complexificationConjugation L x)
    rw [ComplexCartan.torusOperator_mul, hz, hw, ComplexCartan.torusOperator_mul]
  inv_mem' := by
    intro z hz x
    change complexificationConjugation L
      (ComplexCartan.torusOperator _ z.val⁻¹ x) =
      ComplexCartan.torusOperator _ z.val⁻¹ (complexificationConjugation L x)
    apply ComplexCartan.torusOperator_injective (complexifiedSubalgebra L H) z.val
    rw [← hz, ← ComplexCartan.torusOperator_mul, mul_inv_cancel,
      ComplexCartan.torusOperator_one, ← ComplexCartan.torusOperator_mul,
      mul_inv_cancel, ComplexCartan.torusOperator_one]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RealTorusAction
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact rotational group acts on the real Lie algebra -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- The compact torus action restricted to the original real form. -/
def realTorusOperator (z : realRotationTorus L H) : L →ₗ[ℝ] L :=
  (complexificationRealPart L).comp
    ((ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val.val).restrictScalars ℝ |>.comp
      (complexificationLieHom L).toLinearMap)

@[simp] theorem realTorusOperator_complexify (z : realRotationTorus L H) (x : L) :
    (1 : ℂ) ⊗ₜ[ℝ] realTorusOperator L H z x =
      ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val.val ((1 : ℂ) ⊗ₜ[ℝ] x) := by
  have hf : complexificationConjugation L
      (ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val.val ((1 : ℂ) ⊗ₜ[ℝ] x)) =
      ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val.val ((1 : ℂ) ⊗ₜ[ℝ] x) := by
    rw [z.property]
    simp
  obtain ⟨y, hy⟩ := (complexification_conjugation_fixed_iff L _).mp hf
  change (1 : ℂ) ⊗ₜ[ℝ] complexificationRealPart L
    (ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val.val ((1 : ℂ) ⊗ₜ[ℝ] x)) = _
  rw [hy, complexificationRealPart_tmul, Complex.one_re, one_smul]

@[simp] theorem realTorusOperator_one (x : L) : realTorusOperator L H 1 x = x := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] _
  rw [realTorusOperator_complexify]
  exact ComplexCartan.torusOperator_one _ _

@[simp] theorem realTorusOperator_mul (z w : realRotationTorus L H) (x : L) :
    realTorusOperator L H (z * w) x = realTorusOperator L H z (realTorusOperator L H w x) := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] _
  rw [realTorusOperator_complexify, realTorusOperator_complexify, realTorusOperator_complexify]
  exact ComplexCartan.torusOperator_mul _ _ _ _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AffinePolynomialTopology
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The polynomial topology on finite affine coordinates

Points are embedded into the prime spectrum by their evaluation kernels.
This gives a Noetherian T1 topology on finitely many field coordinates.
Polynomial coordinate maps are continuous. This is the topology needed
for the finite-component argument for linear groups.
-/

noncomputable section
namespace PolycyclicRecognition

@[ext]
structure AffinePolynomialPoint (ι K : Type*) where
  coord : ι → K

namespace AffinePolynomialPoint

variable {ι κ K : Type*} [Field K]

def toPrime (x : AffinePolynomialPoint ι K) : PrimeSpectrum (MvPolynomial ι K) :=
  ⟨RingHom.ker (MvPolynomial.eval x.coord), RingHom.ker_isPrime _⟩

instance instTopologicalSpace : TopologicalSpace (AffinePolynomialPoint ι K) :=
  TopologicalSpace.induced toPrime inferInstance

def polynomialMap (p : κ → MvPolynomial ι K) (x : AffinePolynomialPoint ι K) :
    AffinePolynomialPoint κ K :=
  ⟨fun i => MvPolynomial.eval x.coord (p i)⟩

end AffinePolynomialPoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BoundedPathGrowth
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From bounded-height word paths to polynomial growth

Word chains and a uniform metric multiplicity bound turn polynomial packing
of bounded-height chains into polynomial growth. Gromov's theorem then gives
virtual nilpotence of the subgroup.
-/

namespace PolycyclicRecognition

variable {X W : Type*} [PseudoMetricSpace X] [NormedAddCommGroup W]

/-- A finite chain whose steps and heights are uniformly bounded. -/
inductive BoundedHeightChain (π : X → W) (L M : ℝ) : ℕ → X → X → Prop
  | nil (x : X) (hheight : ‖π x‖ ≤ M) : BoundedHeightChain π L M 0 x x
  | cons {n : ℕ} {x y z : X} (hheight : ‖π x‖ ≤ M) (hstep : dist x y ≤ L)
      (tail : BoundedHeightChain π L M n y z) : BoundedHeightChain π L M (n + 1) x z

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactGeneratingBalls
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): the word API of `Group.Generators`
(`Mathlib/Geometry/Group/WordProd.lean` and `WordMetric.lean` there). -/

namespace Group.Generators

variable {G ι : Type*} [Group G] (P : Group.Generators G ι)

/-- The lift of a generating family to the free group. -/
abbrev lift : FreeGroup ι →* G := FreeGroup.lift P.val

theorem lift_surjective : Function.Surjective P.lift := P.lift_val_surjective

/-- The evaluation of a word over a generating family. -/
def wordProd (l : List (ι × Bool)) : G := P.lift (FreeGroup.mk l)

theorem wordProd_surjective : Function.Surjective P.wordProd :=
  P.lift_surjective.comp Quot.mk_surjective

@[simp]
lemma wordProd_nil : P.wordProd [] = 1 := by
  simp [wordProd]

@[simp]
lemma wordProd_singleton (i : ι) (b : Bool) :
    P.wordProd [(i, b)] = cond b (P.val i) (P.val i)⁻¹ := by
  cases b <;> simp [wordProd]

lemma wordProd_cons (i : ι) (b : Bool) (l : List (ι × Bool)) :
    P.wordProd ((i, b) :: l) = cond b (P.val i) (P.val i)⁻¹ * P.wordProd l := by
  rw [show (i, b) :: l = [(i, b)] ++ l from rfl, wordProd, ← FreeGroup.mul_mk, map_mul]
  cases b <;> simp [wordProd]

lemma wordProd_append (l₁ l₂ : List (ι × Bool)) :
    P.wordProd (l₁ ++ l₂) = P.wordProd l₁ * P.wordProd l₂ := by
  simp [wordProd, ← FreeGroup.mul_mk]

lemma wordProd_invRev (l : List (ι × Bool)) :
    P.wordProd (FreeGroup.invRev l) = (P.wordProd l)⁻¹ := by
  simp [wordProd, ← FreeGroup.inv_mk]

/-- The word length of `g` with respect to the generating family `P`. -/
noncomputable def wordLength (g : G) : ℕ := sInf {n | ∃ l, P.wordProd l = g ∧ l.length = n}

/-- A word is geodesic if its length is the word length of the element it represents. -/
def IsGeodesic (l : List (ι × Bool)) : Prop := P.wordLength (P.wordProd l) = l.length

lemma IsGeodesic.eq {l : List (ι × Bool)} (hl : P.IsGeodesic l) :
    P.wordLength (P.wordProd l) = l.length := hl

theorem exists_isGeodesic (g : G) : ∃ l, P.IsGeodesic l ∧ P.wordProd l = g := by
  obtain ⟨l, rfl, hlen⟩ := Nat.sInf_mem (Set.Nonempty.image List.length (P.wordProd_surjective g))
  exact ⟨l, hlen.symm, rfl⟩

lemma wordLength_wordProd_le (l : List (ι × Bool)) : P.wordLength (P.wordProd l) ≤ l.length :=
  Nat.sInf_le ⟨l, rfl, rfl⟩

theorem wordLength_le_iff (g : G) {n : ℕ} :
    P.wordLength g ≤ n ↔ ∃ l, l.length ≤ n ∧ P.wordProd l = g := by
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := P.exists_isGeodesic g
    exact ⟨l, hl.eq ▸ h, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact (P.wordLength_wordProd_le l).trans hl

@[simp]
lemma wordLength_eq_zero_iff {g : G} : P.wordLength g = 0 ↔ g = 1 := by
  rw [← Nat.le_zero, wordLength_le_iff]
  simp [eq_comm]

@[simp]
lemma wordLength_one : P.wordLength (1 : G) = 0 := by
  rw [wordLength_eq_zero_iff]

lemma wordLength_inv_le (g : G) : P.wordLength g⁻¹ ≤ P.wordLength g := by
  obtain ⟨l, hl, rfl⟩ := P.exists_isGeodesic g
  simpa [wordProd_invRev, hl.eq] using P.wordLength_wordProd_le (FreeGroup.invRev l)

@[simp]
lemma wordLength_inv (g : G) : P.wordLength g⁻¹ = P.wordLength g := by
  apply le_antisymm
  · exact P.wordLength_inv_le g
  · simpa using P.wordLength_inv_le g⁻¹

lemma wordLength_mul_le (g h : G) : P.wordLength (g * h) ≤ P.wordLength g + P.wordLength h := by
  obtain ⟨l₁, hl₁, rfl⟩ := P.exists_isGeodesic g
  obtain ⟨l₂, hl₂, rfl⟩ := P.exists_isGeodesic h
  simpa [wordProd_append, hl₁.eq, hl₂.eq] using P.wordLength_wordProd_le (l₁ ++ l₂)

/-- The word length as a group norm. -/
noncomputable def groupNorm : GroupNorm G where
  toFun g := P.wordLength g
  map_one' := by simp
  mul_le' := mod_cast P.wordLength_mul_le
  inv' := by simp
  eq_one_of_map_eq_zero' := by simp

/-- `G` as a normed group with the word metric `dist g h = ‖g⁻¹ * h‖`. -/
@[reducible]
noncomputable def normedGroup : NormedGroup G := P.groupNorm.toNormedGroup

end Group.Generators
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_OccupationSampling
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual probability laws of independent chart samples -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

/-- The law of a measurable chart sampled independently in its two factors. -/
theorem _root_.MeasureTheory.Measure.nonempty_of_isProbabilityMeasure_compat {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] : Nonempty A := by
  by_contra h
  rw [not_nonempty_iff] at h
  simpa [Subsingleton.elim μ 0] using measure_univ (μ := μ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledProfiles
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equicontinuity of actual rescaled map profiles -/

noncomputable section

namespace PolycyclicRecognition

open Module Filter
open scoped Topology NNReal

variable {G W Z : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The map profile on an exponential chart, centered at `x` with suffix `k`. -/
def rescaledMapProfile (J : G → W) (x k : G) (r : ℝ) (φ : Z → G) (z : Z) : W :=
  (Real.exp r)⁻¹ • (J (x * k * φ z) - J x)

variable [TopologicalSpace Z]

omit [IsIsometricSMul G G] in
/-- Continuity at each fixed scale is inherited from the actual chart. -/
theorem continuous_rescaledMapProfile {J : G → W} (hJ : Continuous J)
    (x k : G) (r : ℝ) {φ : Z → G} (hφ : Continuous φ)
    [IsTopologicalGroup G] : Continuous (rescaledMapProfile J x k r φ) := by
  exact continuous_const.smul
    ((hJ.comp (continuous_const.mul hφ)).sub continuous_const)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProfileParameterContinuity
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous dependence of actual profiles on their sheet parameters -/

noncomputable section
namespace PolycyclicRecognition

variable {G W Z A : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [TopologicalSpace Z] [TopologicalSpace A]

/-- The actual rescaled profile as a continuous function of the chart point. -/
def rescaledContinuousProfile (J : G → W) (hJ : Continuous J)
    (x k : G) (r : ℝ) (φ : Z → G) (hφ : Continuous φ) : C(Z, W) :=
  ⟨rescaledMapProfile J x k r φ, continuous_rescaledMapProfile hJ x k r hφ⟩

/-- At a fixed scale the full profile varies continuously with its suffix,
for the topology of uniform convergence on compact chart sets. -/
theorem continuous_rescaledContinuousProfile
    (J : G → W) (hJ : Continuous J) (x : G) (r : ℝ)
    (φ : Z → G) (hφ : Continuous φ) :
    Continuous (fun k => rescaledContinuousProfile J hJ x k r φ hφ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_const.smul
    ((hJ.comp ((continuous_const.mul continuous_fst).mul (hφ.comp continuous_snd))).sub
      continuous_const)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SectionProbeReparametrization
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Probe coordinates on the original quotient/kernel cell

The sampling law may be chosen on the original Haar cell and composed with
this homeomorphism. Thus the compact set selected by concentration is already
measured by the probability law required by source packing.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {Z I Q K : Type*} [TopologicalSpace Z] [TopologicalSpace I]
  [TopologicalSpace Q] [TopologicalSpace K]

/-- Coordinates of a point of the actual quotient/kernel product cell. -/
def sectionProbeCoordinates (eQ : Z ≃ₜ Q) (eI : I ≃ₜ K) (B : Set Z) (U : Set I) :
    ((eQ '' B) ×ˢ (eI '' U)) ≃ₜ B × U :=
  (Homeomorph.Set.prod (eQ '' B) (eI '' U)).trans
    ((eQ.image B).symm.prodCongr (eI.image U).symm)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFactorModel
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Construction of the two Cartan factor models

The only existence premises are the cited Lie correspondence specialized to
the actual root ideal and Cartan algebra. Integration, normality and global
charts are supplied by the separately named published inputs. All assertions
about the multiplication map are derived in `CartanFactorization`.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
  (ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G)

set_option maxHeartbeats 1000000 in
/-- The concrete group part of the manuscript's Cartan model. The ambient
overlap is retained, and all lifting conclusions refer to the actual map. -/
structure CartanFactorModel where
  N : NilpotentLieModel (cartanRootIdeal H)
  D : NilpotentLieModel H
  ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier
  ExpD : GroupLieAlgebra (𝓘(ℝ, D.modelSpace)) D.carrier → D.carrier
  isExpN : IsGroupExponential ExpN
  isExpD : IsGroupExponential ExpD
  inclusionN : N.carrier →* G
  inclusionD : D.carrier →* G
  action : D.carrier →* MulAut N.carrier
  closedN : Topology.IsClosedEmbedding inclusionN
  closedD : Topology.IsClosedEmbedding inclusionD
  compatibleN : ∀ x : cartanRootIdeal H, inclusionN (ExpN (N.equiv x)) = ExpG x
  compatibleD : ∀ x : H, inclusionD (ExpD (D.equiv x)) = ExpG x
  normalN : inclusionN.range.Normal
  conjugation : ∀ d n, inclusionN (action d n) =
    inclusionD d * inclusionN n * (inclusionD d)⁻¹
  surjective : Function.Surjective (fun p : N.carrier × D.carrier =>
    inclusionN p.1 * inclusionD p.2)
  compactLifts : ∀ K : Set G, IsCompact K → ∃ C : Set (N.carrier × D.carrier),
    IsCompact C ∧ K ⊆ (fun p => inclusionN p.1 * inclusionD p.2) '' C
  overlap : Set.range inclusionN ∩ Set.range inclusionD = ExpG ''
    ((cartanRootIdeal H : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∩
      (H : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryMapFamily
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous boundary maps with one compact shadow -/

noncomputable section
namespace PolycyclicRecognition

/-- Data constructed by the ray-limit theorem. The compact set is common
to all maps in the family and all ambient basepoints. -/
structure BoundaryMapFamily {P G S T : Type*} [Group G]
    [One S] [TopologicalSpace S] [One T] [TopologicalSpace T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T) (f : P → G → G) where
  map : P → S → T
  compact : Set T
  isCompact : IsCompact compact
  continuous : ∀ p, Continuous (map p)
  shadow : ∀ p x, ∃ z ∈ compact, map p (actS x 1) = actT (f p x) z

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundaryVolumeComparison
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The common boundary window and its actual Haar characters -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory TopologicalSpace Set
open scoped ENNReal

variable {G S U W P : Type*} [Group G] [Group S] [Group U]
  [TopologicalSpace S] [MeasurableSpace S]
  [TopologicalSpace U] [MeasurableSpace U]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm U)
  (αS αT : W →L[ℝ] ℝ) (height : G →* Multiplicative W) (f : P → G → G)

/-- The measures, common window, and estimates produced by the compact
boundary shadows. These data are constructed below, not published inputs. -/
structure BoundaryVolumeComparison where
  boundary : P → S ≃ₜ U
  window : PositiveCompacts S
  sourceMeasure : Measure S
  targetMeasure : Measure U
  sourceHaar : sourceMeasure.IsHaarMeasure
  targetHaar : targetMeasure.IsHaarMeasure
  sourceRate : ℝ
  targetRate : ℝ
  sourceRate_pos : 0 < sourceRate
  targetRate_pos : 0 < targetRate
  source_volume : ∀ g E, sourceMeasure (actS g '' E) =
    ENNReal.ofReal (Real.exp (sourceRate * αS (height g).toAdd)) * sourceMeasure E
  target_volume : ∀ g E, targetMeasure (actT g '' E) =
    ENNReal.ofReal (Real.exp (targetRate * αT (height g).toAdd)) * targetMeasure E
  constant : ℝ
  constant_pos : 0 < constant
  mass : ∀ p x,
    ENNReal.ofReal (Real.exp (targetRate * αT (height (f p x)).toAdd)) ≤
      ENNReal.ofReal constant * targetMeasure
        (boundary p '' (actS x '' (window : Set S))) ∧
    targetMeasure (boundary p '' (actS x '' (window : Set S))) ≤
      ENNReal.ofReal constant *
        ENNReal.ofReal (Real.exp (targetRate * αT (height (f p x)).toAdd))
  traceBound : ℝ
  traceBound_nonneg : 0 ≤ traceBound
  equal_set_trace : ∀ p x y,
    actS x '' (window : Set S) =
      actS y '' (window : Set S) →
    |targetRate * αT (height (f p x)).toAdd - targetRate * αT (height (f p y)).toAdd| ≤ traceBound


end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanActualProbeProfiles
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual measurable profiles of the sampled probe chains -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
/-- A Cartan chart, in the coordinates used for the profiles. -/
def CartanFactorModel.profileChart
    (bD : Basis (Fin (finrank ℝ H)) ℝ H) : (Fin (finrank ℝ H) → ℝ) → G :=
  fun z => F.inclusionD (F.ExpD (F.D.equiv (bD.equivFun.symm z)))

set_option maxHeartbeats 1000000 in
omit [IsTopologicalGroup G] in
theorem CartanFactorModel.continuous_profileChart
    (hD : Continuous F.ExpD) (bD : Basis (Fin (finrank ℝ H)) ℝ H) :
    Continuous (F.profileChart bD) :=
  F.closedD.continuous.comp (hD.comp
    (F.D.equiv.toLinearMap.comp bD.equivFun.symm.toLinearMap).continuous_of_finiteDimensional)

set_option maxHeartbeats 1000000 in
/-- The original sample is multiplied by the actual probe prefix. -/
def CartanFactorModel.sampledProbeSuffix
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) (v : cartanRootIdeal H) : G :=
  F.inclusionN (F.ExpN (F.N.equiv (bN.equivFun.symm y)) *
    F.ExpN (F.N.equiv v))

set_option maxHeartbeats 1000000 in
/-- This is a continuous map on the whole Cartan chart, before restricting
to the compact set chosen for all three paths. -/
def CartanFactorModel.sampledProbeProfile
    (hD : Continuous F.ExpD) (J : G → W) (hJ : Continuous J) (x : G) (r : ℝ)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bD : Basis (Fin (finrank ℝ H)) ℝ H)
    (y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) (v : cartanRootIdeal H) :
    C((Fin (finrank ℝ H) → ℝ), W) :=
  rescaledContinuousProfile J hJ x (F.sampledProbeSuffix bN y v) r
    (F.profileChart bD) (F.continuous_profileChart hD bD)

set_option maxHeartbeats 1000000 in
@[simp] theorem CartanFactorModel.sampledProbeProfile_apply
    (hD : Continuous F.ExpD) (J : G → W) (hJ : Continuous J) (x : G) (r : ℝ)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bD : Basis (Fin (finrank ℝ H)) ℝ H)
    (y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) (v : cartanRootIdeal H)
    (z : Fin (finrank ℝ H) → ℝ) :
    F.sampledProbeProfile hD J hJ x r bN bD y v z =
      rescaledMapProfile J x
        (F.inclusionN (F.ExpN (F.N.equiv (bN.equivFun.symm y))) *
          F.inclusionN (F.ExpN (F.N.equiv v))) r
        (fun z => F.inclusionD (F.ExpD (F.D.equiv (bD.equivFun.symm z)))) z := by
  simp only [sampledProbeProfile, sampledProbeSuffix, map_mul]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCanonicalProfiles
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual profiles indexed by a real physical scale -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
def CartanFactorModel.realScaleProfile
    (hD : Continuous F.ExpD) (J : G → W) (hJ : Continuous J) (x : G)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (r : ℝ) (k : F.N.carrier) : C((Fin (finrank ℝ H) → ℝ), W) :=
  rescaledContinuousProfile J hJ x (F.inclusionN k) (max (Real.log r) 0)
    (F.profileChart (exponentialRescaleBasis (WordBasisSelections.basis X S β)
      (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (max (Real.log r) 0)))
    (F.continuous_profileChart hD _)

set_option maxHeartbeats 1000000 in
@[simp] theorem CartanFactorModel.realScaleProfile_apply
    (hD : Continuous F.ExpD) (J : G → W) (hJ : Continuous J) (x : G)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (r : ℝ) (k : F.N.carrier) (z : Fin (finrank ℝ H) → ℝ) :
    F.realScaleProfile hD J hJ x X S β r k z =
      rescaledMapProfile J x (F.inclusionN k) (max (Real.log r) 0)
        (F.profileChart (exponentialRescaleBasis (WordBasisSelections.basis X S β)
          (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (max (Real.log r) 0))) z := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectProductTopology
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The product topology on the Cartan semidirect cover -/

noncomputable section
namespace PolycyclicRecognition

variable {N D : Type*} [Group N] [Group D] [TopologicalSpace N] [TopologicalSpace D]
  (φ : D →* MulAut N)

variable [IsTopologicalGroup N] [IsTopologicalGroup D]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def semidirectProductLift (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹) : (N ⋊[φ] D) →* G :=
  SemidirectProduct.lift ι κ (by intro d; ext n; exact hc d n)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSemidirectCover
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The genuine product cover of the Cartan factors

The factors in the ambient group may overlap. Their semidirect product instead
has unique product coordinates; the projection is surjective and has compact
lifts, which suffices to descend compact coboundary approximations.
-/

noncomputable section
namespace PolycyclicRecognition

universe v

open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

local instance instIsTopologicalGroupCarrierSubtypeGroupLieAlgebraRealModelWithCornersSelfMemLieIdealCartanRootIdealN_r7d1378_1 : IsTopologicalGroup F.N.carrier :=
  topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
local instance instIsTopologicalGroupCarrierSubtypeGroupLieAlgebraRealModelWithCornersSelfMemLieSubalgebraD_r7d1378_1 : IsTopologicalGroup F.D.carrier :=
  topologicalGroup_of_lieGroup (𝓘(ℝ, F.D.modelSpace)) ⊤
set_option maxHeartbeats 1000000 in
def CartanFactorModel.semidirectProjection :
    (F.N.carrier ⋊[F.action] F.D.carrier) →* G :=
  semidirectProductLift F.action F.inclusionN F.inclusionD F.conjugation

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWeightDerivation
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The semisimple derivations attached to canonical height

On a generalized Cartan root space the operator is scalar multiplication by
the root. Its dependence on the canonical height, rather than a choice of
Cartan representative, is proved here.
-/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule
open scoped DirectSum

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
def cartanWeightOperator (h : H) : L →ₗ[ℝ] L := by
  classical
  exact (DirectSum.toModule ℝ (Weight ℝ H L) L
    (fun χ => χ h • (genWeightSpace L χ).toSubmodule.subtype)).comp
      (cartanWeightDecomposition T H).symm.toLinearMap

set_option maxHeartbeats 1000000 in
theorem cartanWeightOperator_apply_root (h : H) (χ : Weight ℝ H L) {x : L}
    (hx : x ∈ rootSpace H χ) : cartanWeightOperator T H h x = χ h • x := by
  classical
  let S := fun χ : Weight ℝ H L => (genWeightSpace L χ).toSubmodule
  have he : cartanWeightDecomposition T H
      (DirectSum.lof ℝ (Weight ℝ H L) (fun χ => S χ) χ ⟨x, hx⟩) = x :=
    DirectSum.coeLinearMap_lof S χ ⟨x, hx⟩
  change (DirectSum.toModule ℝ (Weight ℝ H L) L
    (fun χ => χ h • (S χ).subtype)) ((cartanWeightDecomposition T H).symm x) = _
  rw [← he, LinearEquiv.symm_apply_apply, DirectSum.toModule_lof]
  rw [he]
  rfl

set_option maxHeartbeats 1000000 in
theorem cartanWeightOperator_apply_genWeight (h : H) (χ : H → ℝ) {x : L}
    (hx : x ∈ genWeightSpace L χ) : cartanWeightOperator T H h x = χ h • x := by
  by_cases hχ : genWeightSpace L χ = ⊥
  · have hx0 : x = 0 := by simpa only [hχ, LieSubmodule.mem_bot] using hx
    simp [hx0]
  · exact cartanWeightOperator_apply_root T H h ⟨χ, hχ⟩ hx

set_option maxHeartbeats 1000000 in
theorem cartanWeightOperator_lie (h : H) (x y : L) :
    cartanWeightOperator T H h ⁅x, y⁆ =
      ⁅x, cartanWeightOperator T H h y⁆ + ⁅cartanWeightOperator T H h x, y⁆ := by
  apply cartan_root_induction T H (x := x)
  · intro χ u hu
    apply cartan_root_induction T H (x := y)
    · intro ψ v hv
      rw [cartanWeightOperator_apply_genWeight T H h (χ + ψ)
        (lie_mem_genWeightSpace_of_mem_genWeightSpace hu hv),
        cartanWeightOperator_apply_root T H h χ hu,
        cartanWeightOperator_apply_root T H h ψ hv]
      simp only [Pi.add_apply, lie_smul, smul_lie, add_smul, add_comm]
    · simp
    · intro v w hv hw
      simp only [lie_add, map_add, hv, hw]
      abel
  · simp
  · intro u v hu hv
    simp only [add_lie, map_add, hu, hv]
    abel

set_option maxHeartbeats 1000000 in
def cartanWeightDerivation (h : H) : LieDerivation ℝ L L where
  toLinearMap := cartanWeightOperator T H h
  leibniz' x y := by
    rw [cartanWeightOperator_lie]
    rw [← lie_skew (cartanWeightOperator T H h x) y]
    exact (sub_eq_add_neg _ _).symm

set_option maxHeartbeats 1000000 in
@[simp]
theorem cartanWeightDerivation_apply_root (h : H) (χ : Weight ℝ H L) {x : L}
    (hx : x ∈ rootSpace H χ) : cartanWeightDerivation T H h x = χ h • x :=
  cartanWeightOperator_apply_root T H h χ hx

set_option maxHeartbeats 1000000 in
theorem cartanWeightDerivation_add (h k : H) :
    cartanWeightDerivation T H (h + k) = cartanWeightDerivation T H h +
      cartanWeightDerivation T H k := by
  apply LieDerivation.ext
  intro x
  apply cartan_root_induction T H (x := x)
  · intro χ u hu
    simp only [LieDerivation.add_apply, cartanWeightDerivation_apply_root T H _ χ hu,
      map_add, add_smul]
  · simp
  · intro u v hu hv
    simp only [map_add, LieDerivation.add_apply] at hu hv ⊢
    rw [hu, hv]

set_option maxHeartbeats 1000000 in
theorem cartanWeightDerivation_smul (r : ℝ) (h : H) :
    cartanWeightDerivation T H (r • h) = r • cartanWeightDerivation T H h := by
  apply LieDerivation.ext
  intro x
  apply cartan_root_induction T H (x := x)
  · intro χ u hu
    simp only [LieDerivation.smul_apply, cartanWeightDerivation_apply_root T H _ χ hu,
      map_smul, smul_eq_mul, smul_smul]
  · simp
  · intro u v hu hv
    simp only [map_add, LieDerivation.smul_apply] at hu hv ⊢
    rw [hu, hv]

set_option maxHeartbeats 1000000 in
def cartanWeightDerivationLinear : H →ₗ[ℝ] LieDerivation ℝ L L where
  toFun := cartanWeightDerivation T H
  map_add' := cartanWeightDerivation_add T H
  map_smul' := cartanWeightDerivation_smul T H

set_option maxHeartbeats 1000000 in
theorem cartanWeightDerivation_commute (h k : H) :
    ⁅cartanWeightDerivation T H h, cartanWeightDerivation T H k⁆ = 0 := by
  apply LieDerivation.ext
  intro x
  change cartanWeightDerivation T H h (cartanWeightDerivation T H k x) -
    cartanWeightDerivation T H k (cartanWeightDerivation T H h x) = 0
  apply cartan_root_induction T H (x := x)
  · intro χ u hu
    rw [cartanWeightDerivation_apply_root T H k χ hu, map_smul,
      cartanWeightDerivation_apply_root T H h χ hu, map_smul,
      cartanWeightDerivation_apply_root T H k χ hu]
    simp only [smul_smul, mul_comm, sub_self]
  · simp
  · intro u v hu hv
    simp only [map_add, sub_eq_zero.mp hu, sub_eq_zero.mp hv, sub_self]

set_option maxHeartbeats 1000000 in
/-- The chosen Cartan section disappears from the eigenvalues: they are the
canonical height weights. -/
def heightSemisimpleAction : L →ₗ[ℝ] LieDerivation ℝ L L :=
  (cartanWeightDerivationLinear T H).comp
    ((cartanHeightSection T H).comp (heightProjection T.character))

set_option maxHeartbeats 1000000 in
theorem heightSemisimpleAction_apply_root (x : L) (χ : Weight ℝ H L) {y : L}
    (hy : y ∈ rootSpace H χ) :
    heightSemisimpleAction T H x y =
      cartanHeightWeight T H χ (heightProjection T.character x) • y :=
  cartanWeightDerivation_apply_root T H _ χ hy

set_option maxHeartbeats 1000000 in
theorem heightSemisimpleAction_lie (x y : L) :
    heightSemisimpleAction T H ⁅x, y⁆ = 0 := by
  change cartanWeightDerivationLinear T H
    (cartanHeightSection T H (heightProjection T.character ⁅x, y⁆)) = 0
  rw [T.height_lie, map_zero, map_zero]

set_option maxHeartbeats 1000000 in
theorem heightSemisimpleAction_commute (x y : L) :
    ⁅heightSemisimpleAction T H x, heightSemisimpleAction T H y⁆ = 0 :=
  cartanWeightDerivation_commute T H _ _

set_option maxHeartbeats 1000000 in
theorem heightSemisimpleAction_height_zero (x y : L) :
    heightProjection T.character (heightSemisimpleAction T H x y) = 0 := by
  apply cartan_root_induction T H (x := y)
  · intro χ v hv
    rw [heightSemisimpleAction_apply_root T H x χ hv, map_smul]
    by_cases hχ : χ.IsNonZero
    · have hk : v ∈ T.kernelIdeal := cartanRootIdeal_le_kernel H T
        (LieSubmodule.subset_lieSpan ⟨χ, hχ, hv⟩)
      rw [show heightProjection T.character v = 0 from
        (Submodule.Quotient.mk_eq_zero _).mpr hk, smul_zero]
    · have hz : (χ : H → ℝ) = 0 := not_not.mp hχ
      have hc : cartanHeightWeight T H χ (heightProjection T.character x) = 0 :=
        congrFun hz _
      rw [hc, zero_smul]
  · simp
  · intro u v hu hv
    simp only [map_add, hu, hv, add_zero]

set_option maxHeartbeats 1000000 in
theorem heightSemisimpleAction_annihilate (x y : L) :
    heightSemisimpleAction T H (heightSemisimpleAction T H x y) = 0 := by
  change cartanWeightDerivationLinear T H (cartanHeightSection T H
    (heightProjection T.character (heightSemisimpleAction T H x y))) = 0
  rw [heightSemisimpleAction_height_zero, map_zero, map_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_CartanNilshadow
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nilpotent Lie algebra attached to the Cartan height action

The graph of minus the semisimple height action is a Lie subalgebra of the
affine derivation algebra. Its first coordinate is linearly the original Lie
algebra, while its bracket has the semisimple action removed.
-/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
def cartanNilshadowSubalgebra :
    LieSubalgebra ℝ (L ⋊⁅(LieHom.id : LieDerivation ℝ L L →ₗ⁅ℝ⁆ LieDerivation ℝ L L)⁆
      LieDerivation ℝ L L) where
  carrier := {p | p.right = -heightSemisimpleAction T H p.left}
  zero_mem' := by simp
  add_mem' {p q} hp hq := by
    change p.right + q.right = -heightSemisimpleAction T H (p.left + q.left)
    rw [hp, hq, map_add, neg_add]
  smul_mem' r {p} hp := by
    change r • p.right = -heightSemisimpleAction T H (r • p.left)
    rw [hp, map_smul, smul_neg]
  lie_mem' {p q} hp hq := by
    change ⁅p.right, q.right⁆ = -heightSemisimpleAction T H
      (⁅p.left, q.left⁆ + p.right q.left - q.right p.left)
    rw [hp, hq]
    simp only [neg_lie, lie_neg, heightSemisimpleAction_commute,
      LieDerivation.neg_apply, map_add, map_sub, map_neg,
      heightSemisimpleAction_lie, heightSemisimpleAction_annihilate, neg_zero,
      add_zero, sub_zero]

set_option maxHeartbeats 1000000 in
abbrev CartanNilshadow := cartanNilshadowSubalgebra T H

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCoverRootDistortion
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic root distortion in the genuine Cartan cover

Ambient conjugation identities lift to the nilpotent coordinate because its
inclusion is injective. No injectivity of the whole cover projection is used.
-/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
/-- The root exponential in the first coordinate of the semidirect cover. -/
def CartanFactorModel.semidirectRootExp
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (v : rootSpace H χ) : F.N.carrier ⋊[F.action] F.D.carrier :=
  SemidirectProduct.inl (F.ExpN (F.N.equiv (CartanWordModel.rootInIdeal χ hχ v)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFixedProfileMeasurable
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual measurable profiles of the sampled probe chains -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
/-- The fixed initial suffix is a continuous function of the original sample.
This proof avoids introducing an artificial product probe space. -/
theorem CartanFactorModel.measurable_fixed_sampledProbeProfile
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (J : G → W) (hJ : Continuous J) (x : G) (r : ℝ)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bD : Basis (Fin (finrank ℝ H)) ℝ H) (v : cartanRootIdeal H)
    (Z : Set (Fin (finrank ℝ H) → ℝ))
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)] :
    Measurable (fun y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ =>
      (F.sampledProbeProfile hD J hJ x r bN bD y v).restrict Z) := by
  have hs : Continuous (fun y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ =>
      F.sampledProbeSuffix bN y v) := by
    simpa only [CartanFactorModel.sampledProbeSuffix, map_mul, Function.comp_apply,
      LinearMap.comp_apply, LieHom.coe_toLinearMap, LieEquiv.coe_toLieHom, LinearEquiv.coe_coe] using
      (F.closedN.continuous.comp (hN.comp
      (F.N.equiv.toLinearMap.comp bN.equivFun.symm.toLinearMap).continuous_of_finiteDimensional)).mul_const _
  exact ((ContinuousMap.continuous_restrict Z).comp
    ((continuous_rescaledContinuousProfile J hJ x r
      (F.profileChart bD) (F.continuous_profileChart hD bD)).comp hs)).measurable

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanHeightRays
attribute [-instance] _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.cartanWeightDilation_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_add_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_zero_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual Cartan representatives of height rays

The height is exactly linear along these rays. Continuity on one compact
ball and the one-parameter group identity give their linear metric growth.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold

namespace CartanFactorModel

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [Group G] [ChartedSpace EG G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G}
  (F : CartanFactorModel H ExpG) (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The Cartan one-parameter ray representing the height `t • w`. -/
def heightRay (w : W) (t : ℝ) : F.D.carrier :=
  F.ExpD (F.D.equiv (t • cartanHeightSection T H (eW.symm w)))

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ W] in
@[simp] theorem heightRay_zero (w : W) : F.heightRay T eW w 0 = 1 := by
  simp only [heightRay, zero_smul, map_zero, F.isExpD.map_zero]

end CartanFactorModel

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSampledProbeFrames
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original center and exact group frames of a sampled profile -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
/-- The root element selected by the independent coordinate-cube sample. -/
def CartanFactorModel.sampleRoot
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) : F.N.carrier :=
  F.ExpN (F.N.equiv (bN.equivFun.symm y))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexAdjointKernel
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nilpotent kernel of the complex adjoint weights

Complex weights retain rotational directions. Their common real kernel is
nilpotent by triangular matrices, faithful scalar extension, and Engel's theorem.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}

structure ComplexTriangularAdjoint (L : Type*) [LieRing L] [LieAlgebra ℝ L] (n : ℕ) where
  basis : Basis (Fin n) ℂ (ℂ ⊗[ℝ] L)
  upper : ∀ x : ℂ ⊗[ℝ] L,
    (LinearMap.toMatrix basis basis (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L) x)).IsUpperTriangular

namespace ComplexTriangularAdjoint
variable (T : ComplexTriangularAdjoint L n)

def weightMap : L →ₗ[ℝ] (Fin n → ℂ) where
  toFun x i := complexifiedAdjointMatrix L T.basis x i i
  map_add' x y := by
    ext i
    exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i i)
      ((complexifiedAdjointMatrix L T.basis).map_add x y)
  map_smul' r x := by
    ext i
    exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i i)
      ((complexifiedAdjointMatrix L T.basis).map_smul r x)

theorem mul_diag (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

@[simp] theorem weightMap_lie (x y : L) : T.weightMap ⁅x, y⁆ = 0 := by
  ext i
  change complexifiedAdjointMatrix L T.basis ⁅x, y⁆ i i = 0
  rw [LieHom.map_lie]
  change (complexifiedAdjointMatrix L T.basis x * complexifiedAdjointMatrix L T.basis y -
    complexifiedAdjointMatrix L T.basis y * complexifiedAdjointMatrix L T.basis x) i i = 0
  simp only [complexifiedAdjointMatrix_apply]
  rw [Matrix.sub_apply, mul_diag _ _ (T.upper _) (T.upper _),
    mul_diag _ _ (T.upper _) (T.upper _), mul_comm, sub_self]

def kernelIdeal : LieIdeal ℝ L where
  __ := T.weightMap.ker
  lie_mem := by intro x y _; exact T.weightMap_lie x y

@[simp] theorem mem_kernelIdeal (x : L) :
    x ∈ T.kernelIdeal ↔ T.weightMap x = 0 := Iff.rfl

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexNilradical
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The intrinsic meaning of the complex weight kernel

The common kernel consists exactly of the elements with nilpotent adjoint.
In particular it is preserved by every Lie automorphism. This identifies the
nilpotent factor without making a choice of triangular basis part of its data.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}

namespace ComplexTriangularAdjoint
variable (T : ComplexTriangularAdjoint L n)

theorem diagonal_mul (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

theorem diagonal_pow (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (k : ℕ) (i : Fin n) :
    (A ^ k) i i = (A i i) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, diagonal_mul _ _ (hA.pow k) hA, ih, pow_succ]

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexCartanQuotient
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact rotations act trivially on the adjoint-weight quotient -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}

namespace ComplexTriangularAdjoint
variable (T : ComplexTriangularAdjoint L n)

set_option maxHeartbeats 1000000 in
/-- The same adjoint diagonal on the entire complexification. -/
def complexWeightMap : (ℂ ⊗[ℝ] L) →ₗ[ℂ] (Fin n → ℂ) where
  toFun x i := LinearMap.toMatrix T.basis T.basis (ad ℂ (ℂ ⊗[ℝ] L) x) i i
  map_add' x y := by
    ext i
    simp only [map_add, Matrix.add_apply, Pi.add_apply]
  map_smul' r x := by
    ext i
    simp only [map_smul, Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply]

set_option maxHeartbeats 1000000 in
@[simp] theorem complexWeightMap_one_tmul (x : L) :
    T.complexWeightMap ((1 : ℂ) ⊗ₜ[ℝ] x) = T.weightMap x := rfl

set_option maxHeartbeats 1000000 in
theorem complexWeightMap_eq_zero_iff (x : ℂ ⊗[ℝ] L) :
    T.complexWeightMap x = 0 ↔ IsNilpotent (ad ℂ (ℂ ⊗[ℝ] L) x) := by
  let A := LinearMap.toMatrix T.basis T.basis (ad ℂ (ℂ ⊗[ℝ] L) x)
  constructor
  · intro hx
    have hz (i : Fin n) : A i i = 0 := congrFun hx i
    have hp : A.charpoly = Polynomial.X ^ n := by
      rw [Matrix.charpoly_of_isUpperTriangular A (T.upper x)]
      simp [hz]
    have hA : A ^ n = 0 := by
      simpa only [hp, map_pow, Polynomial.aeval_X] using Matrix.aeval_self_charpoly A
    refine ⟨n, (LinearMap.toMatrixAlgEquiv T.basis).injective ?_⟩
    rw [map_pow, map_zero]
    exact hA
  · rintro ⟨k, hk⟩
    have hA : A ^ k = 0 := by
      change ((LinearMap.toMatrixAlgEquiv T.basis) (ad ℂ (ℂ ⊗[ℝ] L) x)) ^ k = 0
      rw [← map_pow, hk, map_zero]
    ext i
    change A i i = 0
    apply eq_zero_of_pow_eq_zero (n := k)
    rw [← diagonal_pow A (T.upper x) k i, hA]
    rfl

variable [FiniteDimensional ℝ L] (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- The nonzero Cartan root spaces lie in the common complex weight kernel. -/
theorem complexWeightMap_root_zero
    {χ : complexifiedSubalgebra L H → ℂ} (hχ : χ ≠ 0)
    {x : ℂ ⊗[ℝ] L} (hx : x ∈ rootSpace (complexifiedSubalgebra L H) χ) :
    T.complexWeightMap x = 0 :=
  (T.complexWeightMap_eq_zero_iff x).mpr
    (LieAlgebra.isNilpotent_ad_of_mem_rootSpace (complexifiedSubalgebra L H) hχ hx)

set_option maxHeartbeats 1000000 in
/-- All the complex weight coordinates have a common representative in the
complexified Cartan subalgebra. -/
theorem exists_complex_cartan_representative (x : ℂ ⊗[ℝ] L) :
    ∃ h : complexifiedSubalgebra L H, T.complexWeightMap h = T.complexWeightMap x := by
  apply ComplexCartan.root_induction (complexifiedSubalgebra L H) (x := x)
  · intro χ v hv
    by_cases hχ : (χ : complexifiedSubalgebra L H → ℂ) = 0
    · have hm : v ∈ complexifiedSubalgebra L H := by
        have hv' : v ∈ rootSpace (complexifiedSubalgebra L H) 0 := by
          simpa only [hχ] using hv
        rwa [rootSpace_zero_eq] at hv'
      exact ⟨⟨v, hm⟩, rfl⟩
    · refine ⟨0, ?_⟩
      change T.complexWeightMap 0 = T.complexWeightMap v
      rw [map_zero, T.complexWeightMap_root_zero H hχ hv]
  · exact ⟨0, by simp⟩
  · rintro v w ⟨h, hh⟩ ⟨k, hk⟩
    refine ⟨h + k, ?_⟩
    change T.complexWeightMap ((h : ℂ ⊗[ℝ] L) + k) = _
    rw [map_add, hh, hk, map_add]

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealCartanQuotient
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real Cartan representatives of the complex adjoint-weight quotient -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]

variable {L} {n : ℕ} (T : ComplexTriangularAdjoint L n)

namespace ComplexTriangularAdjoint

set_option maxHeartbeats 1000000 in
/-- Conjugation preserves the common complex weight kernel. -/
theorem complexWeightMap_conjugate_zero {x : ℂ ⊗[ℝ] L}
    (hx : T.complexWeightMap x = 0) :
    T.complexWeightMap (complexificationConjugation L x) = 0 := by
  rw [T.complexWeightMap_eq_zero_iff] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  let c := complexificationConjugation L
  have hi (m : ℕ) (y : ℂ ⊗[ℝ] L) :
      ((ad ℂ (ℂ ⊗[ℝ] L) (c x)) ^ m) (c y) =
        c (((ad ℂ (ℂ ⊗[ℝ] L) x) ^ m) y) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ih]
      exact (c.map_lie x _).symm
  refine ⟨k, ?_⟩
  apply LinearMap.ext
  intro y
  obtain ⟨z, rfl⟩ := c.surjective y
  change ((ad ℂ (ℂ ⊗[ℝ] L) (c x)) ^ k) (c z) = 0
  rw [hi, hk]
  simp

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_UniversalAllScaleCartanProfiles
attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compact profile family for every nonnegative real scale -/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology NNReal

set_option maxHeartbeats 1000000 in
/-- Only the metric data used to form a normalized chart profile. -/
structure AllScaleProfileData (G W : Type*) [Group G] [PseudoMetricSpace G]
    [NormedAddCommGroup W] (K : ℝ≥0) (B : ℝ) where
  scale : ℝ
  nonneg : 0 ≤ scale
  map : G → W
  lipschitz : LipschitzWith K map
  center : G
  suffix : G
  suffix_bound : dist 1 suffix / Real.exp scale ≤ B

end PolycyclicRecognition

end

end OAI
end


