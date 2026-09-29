-- Prove2me | solution 1 for AlgebraicCurve.exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e4ced01e-9c41-5e22-8a09-8877d2fb17b9

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_AlgebraicCurve_Place_analyticAt_evalAt_extChartAt_symm_of_mem
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds.AlgebraicCurve Filter Topology Set"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.FiniteResidue Place.ord_zero HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite IsCurveOver Place.evalAt Place.evalAt_one regularDifferentials Place.chartRead_apply Place.readDifferential_apply IsPrimitiveAlong pathIntegral abelJacobiVec abelJacobiVec_def abelJacobiDiv pathPeriodLattice mem_pathPeriodLattice_of_loop Place.analyticAt_evalAt_extChartAt_symm_of_mem dCoordGenerates_of_isCurveOver essFiniteType_of_transcendental_of_finiteDimensional exists_isPrimitiveAlong_of_mem_regularDifferentials"
namespace LocalJacobiProof
p2m_open "AlgebraicCurve"

section Algebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pos_of_not_isUnit (v : Place K F) {a : v.toValuationSubring} (ha : a ≠ 0)
    (hu : ¬IsUnit a) : 0 < v.ord (a : F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hn : n ≠ 0 := by
    rintro rfl
    exact hu (by rw [pow_zero, mul_one]; exact u.isUnit)
  have hcoe : (((u : v.toValuationSubring) * π ^ n : v.toValuationSubring) : F) =
      ((u : v.toValuationSubring) : F) * (π : F) ^ (n : ℤ) := by
    rw [zpow_natCast, Subring.coe_mul, SubmonoidClass.coe_pow]
  rw [hcoe, v.ord_unit_smul_zpow u hπ]
  exact_mod_cast Nat.pos_of_ne_zero hn

theorem ord_neg_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.ord f < 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf (zero_mem _)
  have hinv : f⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf
  have hu : ¬IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
    intro h
    obtain ⟨u, hu⟩ := h
    apply hf
    have : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val = f := by
      have h1 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val * f⁻¹ = 1 := by
        have := congrArg (fun a : v.toValuationSubring => (a : F)) (u.inv_mul)
        simpa [hu] using this
      have := congrArg (· * f) h1
      simpa [inv_mul_cancel_right₀ hf0, mul_assoc, inv_mul_cancel₀ hf0] using this
    rw [← this]
    exact SetLike.coe_mem _
  have ha : (⟨f⁻¹, hinv⟩ : v.toValuationSubring) ≠ 0 := by
    intro h
    exact inv_ne_zero hf0 (by simpa using congrArg Subtype.val h)
  have := ord_pos_of_not_isUnit v ha hu
  rw [show ((⟨f⁻¹, hinv⟩ : v.toValuationSubring) : F) = f⁻¹ from rfl, v.ord_inv] at this
  omega

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  by_contra hf
  exact absurd (ord_neg_of_not_mem v hf) (not_lt.2 h)

theorem mem_of_ord_eq_one (v : Place K F) {f : F} (hf : v.ord f = 1) : f ∈ v.toValuationSubring :=
  mem_of_ord_nonneg v (by rw [hf]; exact zero_le_one)

theorem finite_setOf_not_mem [HasPrincipalDivisors K F] {f : F} (hf0 : f ≠ 0) :
    {w : Place K F | f ∉ w.toValuationSubring}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  refine (D.support.finite_toSet).subset fun w hw => ?_
  have h := ord_neg_of_not_mem w hw
  rw [← hD w] at h
  simpa [Finsupp.mem_support_iff] using h.ne

theorem isRational_of_isAlgClosed [IsAlgClosed K] (w : Place K F) [w.FiniteResidue] :
    w.IsRational := by
  haveI : Module.Finite K w.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

theorem residue_algebraMap (w : Place K F) (a : K) :
    IsLocalRing.residue w.toValuationSubring
        (⟨algebraMap K F a, w.algebraMap_mem' a⟩ : w.toValuationSubring) =
      algebraMap K w.ResidueField a := by
  have h : (⟨algebraMap K F a, w.algebraMap_mem' a⟩ : w.toValuationSubring) =
      algebraMap K w.toValuationSubring a := Subtype.ext (w.coe_algebraMap a).symm
  rw [h]
  exact (IsScalarTower.algebraMap_apply K w.toValuationSubring w.ResidueField a).symm

theorem evalAt_algebraMap' (w : Place K F) (a : K) : w.evalAt (algebraMap K F a) = a := by
  rw [w.evalAt_of_mem (w.algebraMap_mem' a), residue_algebraMap, w.residueInv_algebraMap]

theorem evalAt_zero' (w : Place K F) : w.evalAt (0 : F) = 0 := by
  simpa using evalAt_algebraMap' w (0 : K)

theorem evalAt_mul (w : Place K F) (hw : w.IsRational) {f g : F}
    (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f * g) = w.evalAt f * w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw (mul_mem hf hg), map_mul, w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_mul]
  rfl

theorem evalAt_add (w : Place K F) (hw : w.IsRational) {f g : F}
    (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f + g) = w.evalAt f + w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw (add_mem hf hg), map_add, w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_add]
  rfl

theorem dCoordFn_mem (v : Place K F) : v.dCoordFn ∈ v.toValuationSubring :=
  mem_of_ord_eq_one v v.ord_dCoordFn

theorem differentialCoeff_mem [Nontrivial (Ω[F⁄K])] {η : Ω[F⁄K]}
    (hη : η ∈ regularDifferentials K F) (v : Place K F) [v.DCoordGenerates] :
    v.differentialCoeff η ∈ v.toValuationSubring := by
  obtain ⟨f, hf, hfeq⟩ := hη v
  rw [v.differentialCoeff_unique hfeq]
  exact hf

end Algebra

section Surface

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

abbrev φ (v : Place ℂ F) : PartialEquiv (Place ℂ F) ℂ := extChartAt 𝓘(ℂ, ℂ) v

abbrev ctr (v : Place ℂ F) : ℂ := extChartAt 𝓘(ℂ, ℂ) v v

def ChartCompatible (F : Type*) [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] : Prop :=
  ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
    MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) ∧
    meromorphicOrderAt
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ)

variable [IsCurveOver ℂ F]

omit [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] in
theorem isRational (w : Place ℂ F) : w.IsRational := isRational_of_isAlgClosed w

variable [T2Space (Place ℂ F)]

omit [ChartedSpace ℂ (Place ℂ F)] in
theorem isOpen_setOf_mem (f : F) : IsOpen {w : Place ℂ F | f ∈ w.toValuationSubring} := by
  by_cases hf0 : f = 0
  · have : {w : Place ℂ F | f ∈ w.toValuationSubring} = univ :=
      eq_univ_of_forall fun w => by
        rw [mem_setOf_eq, hf0]; exact zero_mem w.toValuationSubring
    rw [this]
    exact isOpen_univ
  have h := (finite_setOf_not_mem (K := ℂ) hf0).isClosed.isOpen_compl
  convert h using 1
  ext w
  simp

omit [ChartedSpace ℂ (Place ℂ F)] in
theorem eventually_mem_nhds {f : F} {u : Place ℂ F} (hf : f ∈ u.toValuationSubring) :
    ∀ᶠ w in 𝓝 u, f ∈ w.toValuationSubring :=
  (isOpen_setOf_mem f).mem_nhds hf

theorem eventually_mem_punctured (f : F) (w : Place ℂ F) :
    ∀ᶠ z in 𝓝[≠] (ctr w), f ∈ ((φ w).symm z).toValuationSubring := by
  have hopen : IsOpen ({u : Place ℂ F | f ∈ u.toValuationSubring} ∪ {w}) := by
    by_cases hf0 : f = 0
    · have : ({u : Place ℂ F | f ∈ u.toValuationSubring} ∪ {w}) = univ :=
        eq_univ_of_forall fun u => Or.inl (by
          rw [mem_setOf_eq, hf0]; exact zero_mem u.toValuationSubring)
      rw [this]
      exact isOpen_univ
    have hfin : ({u : Place ℂ F | f ∉ u.toValuationSubring} \ {w}).Finite :=
      (finite_setOf_not_mem (K := ℂ) hf0).subset diff_subset
    have h := hfin.isClosed.isOpen_compl
    convert h using 1
    ext u
    simp only [mem_union, mem_setOf_eq, mem_singleton_iff, mem_compl_iff, mem_diff]
    tauto
  have hmem : (φ w).symm (ctr w) ∈ ({u : Place ℂ F | f ∈ u.toValuationSubring} ∪ {w}) := by
    rw [extChartAt_to_inv]
    exact Or.inr rfl
  have h1 : ∀ᶠ z in 𝓝 (ctr w), (φ w).symm z ∈ ({u : Place ℂ F | f ∈ u.toValuationSubring} ∪ {w}) :=
    (continuousAt_extChartAt_symm w).preimage_mem_nhds (hopen.mem_nhds hmem)
  have h2 : ∀ᶠ z in 𝓝 (ctr w), z ∈ (φ w).target := extChartAt_target_mem_nhds w
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h1, h2] with z hz hzt hne
  rcases hz with h | h
  · exact h
  · exfalso
    apply hne
    have : φ w ((φ w).symm z) = z := (φ w).right_inv hzt
    rw [mem_singleton_iff] at h
    rw [mem_singleton_iff, ← this, h]

theorem eventually_eventually_of_punctured {c : ℂ} {P : ℂ → Prop}
    (h : ∀ᶠ z in 𝓝[≠] c, P z) : ∀ᶠ z in 𝓝[≠] c, ∀ᶠ z' in 𝓝 z, P z' := by
  rw [eventually_nhdsWithin_iff] at h ⊢
  filter_upwards [h.eventually_nhds] with z hz hne
  have hne' : ∀ᶠ z' in 𝓝 z, z' ≠ c := isOpen_compl_singleton.mem_nhds hne
  filter_upwards [hz, hne'] with z' h1 h2
  exact h1 h2

theorem analyticAt_chartRead_center (hF : ChartCompatible F) (v : Place ℂ F) {f : F}
    (hf : f ∈ v.toValuationSubring) : AnalyticAt ℂ (v.chartRead f) (ctr v) :=
  AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF v hf

variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] in
theorem analyticAt_transition (u v : Place ℂ F) {y : ℂ} (hy : y ∈ (φ v).target)
    (hu : (φ v).symm y ∈ (φ u).source) : AnalyticAt ℂ (φ u ∘ (φ v).symm) y := by
  have hcd := contDiffOn_ext_coord_change (I := 𝓘(ℂ, ℂ)) (n := ω) u v
  have hsrc : ((φ v).symm ≫ φ u).source ∈ 𝓝 y := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    refine Filter.inter_mem (extChartAt_target_mem_nhds' hy) ?_
    exact (continuousAt_extChartAt_symm'' hy).preimage_mem_nhds (extChartAt_source_mem_nhds' hu)
  exact (hcd.contDiffAt hsrc).analyticAt

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem chartRead_eq_comp {u v : Place ℂ F} (f : F) {z : ℂ} (hz : (φ v).symm z ∈ (φ u).source) :
    v.chartRead f z = u.chartRead f (φ u ((φ v).symm z)) := by
  simp only [Place.chartRead_apply]
  rw [(φ u).left_inv hz]

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem eventually_symm_mem_source {u v : Place ℂ F} {y : ℂ} (hy : y ∈ (φ v).target)
    (hu : (φ v).symm y ∈ (φ u).source) : ∀ᶠ z in 𝓝 y, (φ v).symm z ∈ (φ u).source :=
  (continuousAt_extChartAt_symm'' hy).preimage_mem_nhds (extChartAt_source_mem_nhds' hu)

theorem analyticAt_chartRead (hF : ChartCompatible F) {u v : Place ℂ F}
    (hu : u ∈ (φ v).source) {f : F} (hf : f ∈ u.toValuationSubring) :
    AnalyticAt ℂ (v.chartRead f) (φ v u) := by
  have hy : φ v u ∈ (φ v).target := (φ v).map_source hu
  have hu' : (φ v).symm (φ v u) ∈ (φ u).source := by
    rw [(φ v).left_inv hu]
    exact mem_extChartAt_source u
  have h1 : AnalyticAt ℂ (u.chartRead f) ((φ u ∘ (φ v).symm) (φ v u)) := by
    have : (φ u ∘ (φ v).symm) (φ v u) = ctr u := by
      simp only [Function.comp_apply]
      rw [(φ v).left_inv hu]
    rw [this]
    exact analyticAt_chartRead_center hF u hf
  have h2 := h1.comp (analyticAt_transition u v hy hu')
  refine h2.congr ?_
  filter_upwards [eventually_symm_mem_source hy hu'] with z hz
  exact (chartRead_eq_comp f hz).symm

theorem analyticAt_chartRead' (hF : ChartCompatible F) (w : Place ℂ F) {z : ℂ}
    (hz : z ∈ (φ w).target) {f : F} (hf : f ∈ ((φ w).symm z).toValuationSubring) :
    AnalyticAt ℂ (w.chartRead f) z := by
  have h := analyticAt_chartRead hF ((φ w).map_target hz) hf
  rwa [(φ w).right_inv hz] at h

end Surface

section Uniqueness

theorem eventually_sub_eq_of_hasDerivAt {Φ₁ Φ₂ h : ℂ → ℂ} {z₀ : ℂ}
    (h₁ : ∀ᶠ z in 𝓝 z₀, HasDerivAt Φ₁ (h z) z) (h₂ : ∀ᶠ z in 𝓝 z₀, HasDerivAt Φ₂ (h z) z) :
    ∀ᶠ z in 𝓝 z₀, Φ₁ z - Φ₂ z = Φ₁ z₀ - Φ₂ z₀ := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (h₁.and h₂)
  filter_upwards [Metric.ball_mem_nhds z₀ hr] with z hz
  have key := (convex_ball z₀ r).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => Φ₁ z - Φ₂ z) (f' := fun _ => (0 : ℂ)) (C := 0)
    (fun x hx => ((hball hx).1.sub (hball hx).2).hasDerivWithinAt.congr_deriv (sub_self _))
    (fun x _ => by simp) (Metric.mem_ball_self hr) hz
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at key
  exact key

theorem eventuallyEq_nhds_of_punctured {f g : ℂ → ℂ} {c : ℂ} (h : f =ᶠ[𝓝[≠] c] g)
    (hf : ContinuousAt f c) (hg : ContinuousAt g c) : f =ᶠ[𝓝 c] g := by
  have hfc : f c = g c := by
    have h1 : Tendsto f (𝓝[≠] c) (𝓝 (f c)) := hf.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto g (𝓝[≠] c) (𝓝 (g c)) := hg.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (h1.congr' h) h2
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at h
  filter_upwards [h] with z hz
  by_cases hzc : z = c
  · rw [hzc, hfc]
  · exact hz hzc

end Uniqueness

section Derivation

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

abbrev pf (w : Place ℂ F) : Filter ℂ := 𝓝[≠] (ctr w)

theorem chartRead_algebraMap (w : Place ℂ F) (a : ℂ) :
    w.chartRead (algebraMap ℂ F a) = fun _ => a :=
  funext fun _ => evalAt_algebraMap' _ a

theorem chartRead_one (w : Place ℂ F) : w.chartRead (1 : F) = 1 :=
  funext fun _ => Place.evalAt_one _

theorem chartRead_zero (w : Place ℂ F) : w.chartRead (0 : F) = 0 :=
  funext fun _ => evalAt_zero' _

variable [IsCurveOver ℂ F] [T2Space (Place ℂ F)]

theorem chartRead_mul (w : Place ℂ F) (f g : F) :
    w.chartRead (f * g) =ᶠ[pf w] w.chartRead f * w.chartRead g := by
  filter_upwards [eventually_mem_punctured f w, eventually_mem_punctured g w] with z hf hg
  exact evalAt_mul _ (isRational _) hf hg

theorem chartRead_add (w : Place ℂ F) (f g : F) :
    w.chartRead (f + g) =ᶠ[pf w] w.chartRead f + w.chartRead g := by
  filter_upwards [eventually_mem_punctured f w, eventually_mem_punctured g w] with z hf hg
  exact evalAt_add _ (isRational _) hf hg

def readHom (w : Place ℂ F) : F →+* Germ (pf w) ℂ where
  toFun f := ((w.chartRead f : ℂ → ℂ) : Germ (pf w) ℂ)
  map_one' := by rw [chartRead_one, Germ.coe_one]
  map_mul' f g := by
    rw [← Germ.coe_mul]
    exact Germ.coe_eq.2 (chartRead_mul w f g)
  map_zero' := by rw [chartRead_zero, Germ.coe_zero]
  map_add' f g := by
    rw [← Germ.coe_add]
    exact Germ.coe_eq.2 (chartRead_add w f g)

theorem readHom_apply (w : Place ℂ F) (f : F) :
    readHom w f = ((w.chartRead f : ℂ → ℂ) : Germ (pf w) ℂ) := rfl

@[reducible] def germAlgebra (w : Place ℂ F) : Algebra F (Germ (pf w) ℂ) := (readHom w).toAlgebra

attribute [local instance] germAlgebra

theorem smul_def' (w : Place ℂ F) (f : F) (m : Germ (pf w) ℂ) : f • m = readHom w f * m := rfl

scoped instance isScalarTower_germ (w : Place ℂ F) : IsScalarTower ℂ F (Germ (pf w) ℂ) :=
  IsScalarTower.of_algebraMap_smul fun a m => Germ.inductionOn m fun x => by
    rw [smul_def', readHom_apply, chartRead_algebraMap, ← Germ.coe_mul, ← Germ.coe_smul]
    exact Germ.coe_eq.2 (Filter.Eventually.of_forall fun z => by simp [smul_eq_mul])

variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem eventually_target (w : Place ℂ F) : ∀ᶠ z in pf w, z ∈ (φ w).target :=
  mem_nhdsWithin_of_mem_nhds (extChartAt_target_mem_nhds w)

theorem eventually_differentiableAt (hF : ChartCompatible F) (w : Place ℂ F) (f : F) :
    ∀ᶠ z in pf w, DifferentiableAt ℂ (w.chartRead f) z := by
  filter_upwards [eventually_target w, eventually_mem_punctured f w] with z hz hf
  exact (analyticAt_chartRead' hF w hz hf).differentiableAt

theorem deriv_chartRead_add (hF : ChartCompatible F) (w : Place ℂ F) (f g : F) :
    deriv (w.chartRead (f + g)) =ᶠ[pf w] deriv (w.chartRead f) + deriv (w.chartRead g) := by
  filter_upwards [eventually_eventually_of_punctured (chartRead_add w f g),
    eventually_differentiableAt hF w f, eventually_differentiableAt hF w g] with z heq hf hg
  rw [Filter.EventuallyEq.deriv_eq heq, Pi.add_apply]
  exact deriv_add hf hg

theorem deriv_chartRead_mul (hF : ChartCompatible F) (w : Place ℂ F) (f g : F) :
    deriv (w.chartRead (f * g)) =ᶠ[pf w]
      deriv (w.chartRead f) * w.chartRead g + w.chartRead f * deriv (w.chartRead g) := by
  filter_upwards [eventually_eventually_of_punctured (chartRead_mul w f g),
    eventually_differentiableAt hF w f, eventually_differentiableAt hF w g] with z heq hf hg
  rw [Filter.EventuallyEq.deriv_eq heq, Pi.add_apply, Pi.mul_apply, Pi.mul_apply]
  exact deriv_mul hf hg

theorem deriv_chartRead_smul (hF : ChartCompatible F) (w : Place ℂ F) (a : ℂ) (f : F) :
    deriv (w.chartRead (a • f)) =ᶠ[pf w] a • deriv (w.chartRead f) := by
  rw [Algebra.smul_def]
  filter_upwards [deriv_chartRead_mul hF w (algebraMap ℂ F a) f] with z hz
  rw [hz, chartRead_algebraMap]
  simp

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem deriv_chartRead_one (w : Place ℂ F) : deriv (w.chartRead (1 : F)) = 0 := by
  rw [chartRead_one]
  funext z
  exact deriv_const z 1

def readDeriv (hF : ChartCompatible F) (w : Place ℂ F) : Derivation ℂ F (Germ (pf w) ℂ) where
  toFun f := ((deriv (w.chartRead f) : ℂ → ℂ) : Germ (pf w) ℂ)
  map_add' f g := by
    rw [← Germ.coe_add]
    exact Germ.coe_eq.2 (deriv_chartRead_add hF w f g)
  map_smul' a f := by
    rw [RingHom.id_apply, ← Germ.coe_smul]
    exact Germ.coe_eq.2 (deriv_chartRead_smul hF w a f)
  map_one_eq_zero' := by
    show ((deriv (w.chartRead (1 : F)) : ℂ → ℂ) : Germ (pf w) ℂ) = 0
    rw [deriv_chartRead_one, Germ.coe_zero]
  leibniz' f g := by
    show ((deriv (w.chartRead (f * g)) : ℂ → ℂ) : Germ (pf w) ℂ) =
      f • ((deriv (w.chartRead g) : ℂ → ℂ) : Germ (pf w) ℂ) +
        g • ((deriv (w.chartRead f) : ℂ → ℂ) : Germ (pf w) ℂ)
    rw [smul_def', smul_def', readHom_apply, readHom_apply, ← Germ.coe_mul, ← Germ.coe_mul,
      ← Germ.coe_add]
    refine Germ.coe_eq.2 ?_
    filter_upwards [deriv_chartRead_mul hF w f g] with z hz
    rw [hz]
    simp only [Pi.add_apply, Pi.mul_apply]
    ring

theorem readDeriv_apply (hF : ChartCompatible F) (w : Place ℂ F) (f : F) :
    readDeriv hF w f = ((deriv (w.chartRead f) : ℂ → ℂ) : Germ (pf w) ℂ) := rfl

theorem lift_smul_D (hF : ChartCompatible F) (w : Place ℂ F) (h g : F) :
    (readDeriv hF w).liftKaehlerDifferential (h • KaehlerDifferential.D ℂ F g) =
      ((w.chartRead h * deriv (w.chartRead g) : ℂ → ℂ) : Germ (pf w) ℂ) := by
  rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, readDeriv_apply, smul_def',
    readHom_apply, Germ.coe_mul]

theorem readDifferential_eventuallyEq_pf (hF : ChartCompatible F) (w v : Place ℂ F)
    [w.DCoordGenerates] [v.DCoordGenerates] (η : Ω[F⁄ℂ]) :
    w.readDifferential η =ᶠ[pf w]
      w.chartRead (v.differentialCoeff η) * deriv (w.chartRead v.dCoordFn) := by
  have h1 : η = w.differentialCoeff η • KaehlerDifferential.D ℂ F w.dCoordFn := by
    rw [← w.dCoord_eq_D_dCoordFn, w.differentialCoeff_smul_dCoord]
  have h2 : η = v.differentialCoeff η • KaehlerDifferential.D ℂ F v.dCoordFn := by
    rw [← v.dCoord_eq_D_dCoordFn, v.differentialCoeff_smul_dCoord]
  have e1 := lift_smul_D hF w (w.differentialCoeff η) w.dCoordFn
  have e2 := lift_smul_D hF w (v.differentialCoeff η) v.dCoordFn
  rw [← h1] at e1
  rw [← h2] at e2
  exact Germ.coe_eq.1 (e1.symm.trans e2)

omit [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem analyticAt_readDifferential (hF : ChartCompatible F) (w : Place ℂ F) {η : Ω[F⁄ℂ]}
    (hh : w.differentialCoeff η ∈ w.toValuationSubring) :
    AnalyticAt ℂ (w.readDifferential η) (ctr w) :=
  (analyticAt_chartRead_center hF w hh).mul (analyticAt_chartRead_center hF w (dCoordFn_mem w)).deriv

theorem readDifferential_eventuallyEq (hF : ChartCompatible F) (w v : Place ℂ F)
    [w.DCoordGenerates] [v.DCoordGenerates] {η : Ω[F⁄ℂ]}
    (hhw : w.differentialCoeff η ∈ w.toValuationSubring)
    (hh : v.differentialCoeff η ∈ w.toValuationSubring)
    (hπ : v.dCoordFn ∈ w.toValuationSubring) :
    w.readDifferential η =ᶠ[𝓝 (ctr w)]
      w.chartRead (v.differentialCoeff η) * deriv (w.chartRead v.dCoordFn) :=
  eventuallyEq_nhds_of_punctured (readDifferential_eventuallyEq_pf hF w v η)
    (analyticAt_readDifferential hF w hhw).continuousAt
    ((analyticAt_chartRead_center hF w hh).mul
      (analyticAt_chartRead_center hF w hπ).deriv).continuousAt

theorem readDifferential_change (hF : ChartCompatible F) {v w : Place ℂ F}
    [w.DCoordGenerates] [v.DCoordGenerates] {η : Ω[F⁄ℂ]} (hw : w ∈ (φ v).source)
    (hhw : w.differentialCoeff η ∈ w.toValuationSubring)
    (hh : v.differentialCoeff η ∈ w.toValuationSubring)
    (hπ : v.dCoordFn ∈ w.toValuationSubring) :
    w.readDifferential η =ᶠ[𝓝 (ctr w)] fun z =>
      v.readDifferential η (φ v ((φ w).symm z)) * deriv (φ v ∘ (φ w).symm) z := by
  refine (readDifferential_eventuallyEq hF w v hhw hh hπ).trans ?_
  have hw' : (φ w).symm (ctr w) ∈ (φ v).source := by rw [extChartAt_to_inv]; exact hw
  have hsrc : ∀ᶠ z in 𝓝 (ctr w), (φ w).symm z ∈ (φ v).source :=
    eventually_symm_mem_source (mem_extChartAt_target w) hw'
  have hπ' : ∀ᶠ z in 𝓝 (ctr w), v.dCoordFn ∈ ((φ w).symm z).toValuationSubring := by
    have hmem : (φ w).symm (ctr w) ∈ {u : Place ℂ F | v.dCoordFn ∈ u.toValuationSubring} := by
      rw [mem_setOf_eq, extChartAt_to_inv]; exact hπ
    exact (continuousAt_extChartAt_symm w).preimage_mem_nhds
      ((isOpen_setOf_mem v.dCoordFn).mem_nhds hmem)
  have htgt : ∀ᶠ z in 𝓝 (ctr w), z ∈ (φ w).target := extChartAt_target_mem_nhds w
  filter_upwards [hsrc, hπ'.eventually_nhds, htgt, hsrc.eventually_nhds] with z hz hπz hzt hsz
  have hcomp : w.chartRead v.dCoordFn =ᶠ[𝓝 z] (v.chartRead v.dCoordFn ∘ (φ v ∘ (φ w).symm)) := by
    filter_upwards [hsz] with z' hz'
    exact chartRead_eq_comp v.dCoordFn hz'
  have hτ : AnalyticAt ℂ (φ v ∘ (φ w).symm) z := analyticAt_transition v w hzt hz
  have hread : DifferentiableAt ℂ (v.chartRead v.dCoordFn) ((φ v ∘ (φ w).symm) z) :=
    (analyticAt_chartRead hF hz hπz.self_of_nhds).differentiableAt
  have hderiv : deriv (w.chartRead v.dCoordFn) z =
      deriv (v.chartRead v.dCoordFn) ((φ v ∘ (φ w).symm) z) * deriv (φ v ∘ (φ w).symm) z := by
    rw [hcomp.deriv_eq]
    exact (hread.hasDerivAt.comp z hτ.differentiableAt.hasDerivAt).deriv
  rw [Pi.mul_apply, hderiv, chartRead_eq_comp (v.differentialCoeff η) hz,
    Place.readDifferential_apply]
  simp only [Function.comp_apply]
  ring

theorem deriv_chartRead_dCoordFn_ne_zero (hF : ChartCompatible F) (v : Place ℂ F) :
    deriv (v.chartRead v.dCoordFn) (ctr v) ≠ 0 := by
  set x₀ := ctr v with hx₀
  have hord := v.ord_dCoordFn (K := ℂ)
  have hπ0 : v.dCoordFn ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hord; exact zero_ne_one hord
  have han : AnalyticAt ℂ (v.chartRead v.dCoordFn) x₀ :=
    analyticAt_chartRead_center hF v (dCoordFn_mem v)
  have hmero := (hF _ hπ0 v).2
  rw [hord] at hmero
  have hordan : analyticOrderAt (v.chartRead v.dCoordFn) x₀ = (1 : ℕ) := by
    have := han.meromorphicOrderAt_eq
    change meromorphicOrderAt (v.chartRead v.dCoordFn) x₀ = _ at hmero
    rw [hmero] at this
    cases h : analyticOrderAt (v.chartRead v.dCoordFn) x₀ with
    | top => rw [h] at this; simp at this
    | coe m =>
      rw [h, ENat.map_coe] at this
      have hm : (m : ℤ) = 1 := by exact_mod_cast (WithTop.coe_injective this).symm
      have : m = 1 := by exact_mod_cast hm
      subst this; rfl
  obtain ⟨p, hp, hp0, hpeq⟩ := han.analyticOrderAt_eq_natCast.mp hordan
  have hloc : v.chartRead v.dCoordFn =ᶠ[𝓝 x₀] fun w => (w - x₀) * p w := by
    filter_upwards [hpeq] with w hw
    rw [hw, pow_one, smul_eq_mul]
  rw [hloc.deriv_eq]
  have hpd : HasDerivAt p (deriv p x₀) x₀ := hp.differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun w => w - x₀) 1 x₀ := (hasDerivAt_id x₀).sub_const x₀
  have h2 : HasDerivAt (fun w => (w - x₀) * p w) (1 * p x₀ + (x₀ - x₀) * deriv p x₀) x₀ := h1.mul hpd
  rw [h2.deriv]
  simpa using hp0

end Derivation

section PathCalculus

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem eventually_eq_add_of_hasDerivAt {f Φ Ψ : ℂ → ℂ} {x₀ : ℂ}
    (hΦ : ∀ᶠ z in 𝓝 x₀, HasDerivAt Φ (f z) z) (hΨ : ∀ᶠ z in 𝓝 x₀, HasDerivAt Ψ (f z) z) :
    ∀ᶠ z in 𝓝 x₀, Ψ z = Φ z + (Ψ x₀ - Φ x₀) := by
  filter_upwards [eventually_sub_eq_of_hasDerivAt hΨ hΦ] with z hz
  linear_combination hz

theorem isPrimitiveAlong_sub_eq_sub {η : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g g' : unitInterval → ℂ} (hg : IsPrimitiveAlong η γ g) (hg' : IsPrimitiveAlong η γ g')
    (t s : unitInterval) : g t - g' t = g s - g' s := by
  have hloc : IsLocallyConstant (fun t => g t - g' t) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun t₀ => ?_
    obtain ⟨Φ, hΦ, hgΦ⟩ := hg t₀
    obtain ⟨Ψ, hΨ, hgΨ⟩ := hg' t₀
    have key := eventually_eq_add_of_hasDerivAt hΦ hΨ
    have hc : ContinuousAt (fun t : unitInterval => extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ t)) t₀ :=
      (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) (γ t₀)).comp γ.continuous.continuousAt
    have key' := hc.eventually key
    have h1 := hgΦ.self_of_nhds
    have h2 := hgΨ.self_of_nhds
    filter_upwards [hgΦ, hgΨ, key'] with t ht ht' hk
    rw [ht, ht', hk, h1, h2]; ring
  exact hloc.apply_eq_of_preconnectedSpace (f := fun t => g t - g' t) t s

theorem pathIntegral_eq_of_isPrimitiveAlong {η : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong η γ g) : pathIntegral η γ = g 1 - g 0 := by
  have h : ∃ g, IsPrimitiveAlong η γ g := ⟨g, hg⟩
  rw [pathIntegral, dif_pos h]
  have := isPrimitiveAlong_sub_eq_sub h.choose_spec hg 1 0
  linear_combination this

theorem isPrimitiveAlong_symm {η : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong η γ g) :
    IsPrimitiveAlong η γ.symm (g ∘ unitInterval.symm) := by
  intro t₀
  obtain ⟨Φ, hΦ, hgΦ⟩ := hg (unitInterval.symm t₀)
  refine ⟨Φ, ?_, ?_⟩
  · simpa only [Path.symm_apply, Function.comp_apply] using hΦ
  · have hσ : ContinuousAt unitInterval.symm t₀ := unitInterval.continuous_symm.continuousAt
    have := hσ.eventually hgΦ
    filter_upwards [this] with t ht
    simpa only [Path.symm_apply, Function.comp_apply] using ht

theorem pathIntegral_symm {η : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong η γ g) :
    pathIntegral η γ.symm = -pathIntegral η γ := by
  rw [pathIntegral_eq_of_isPrimitiveAlong hg, pathIntegral_eq_of_isPrimitiveAlong
    (isPrimitiveAlong_symm hg)]
  simp only [Function.comp_apply, unitInterval.symm_one, unitInterval.symm_zero]
  ring

def transPrimitive (g h : unitInterval → ℂ) : unitInterval → ℂ := fun t =>
  if (t : ℝ) ≤ 1 / 2 then Set.IccExtend zero_le_one g (2 * t)
  else Set.IccExtend zero_le_one h (2 * t - 1) + (g 1 - h 0)

theorem transPrimitive_zero (g h : unitInterval → ℂ) : transPrimitive g h 0 = g 0 := by
  simp [transPrimitive]

theorem transPrimitive_one (g h : unitInterval → ℂ) : transPrimitive g h 1 = h 1 + (g 1 - h 0) := by
  have h2 : ¬ ((1 : unitInterval) : ℝ) ≤ 1 / 2 := by norm_num
  show (if ((1 : unitInterval) : ℝ) ≤ 1 / 2 then _ else _) = _
  rw [if_neg h2]
  congr 1
  have h21 : (2 * ((1 : unitInterval) : ℝ) - 1) = 1 := by norm_num
  rw [h21, Set.IccExtend_right]
  rfl

theorem isPrimitiveAlong_trans {η : Ω[F⁄ℂ]} {P Q R : Place ℂ F} {γ : Path P Q} {δ : Path Q R}
    {g h : unitInterval → ℂ} (hg : IsPrimitiveAlong η γ g) (hh : IsPrimitiveAlong η δ h) :
    IsPrimitiveAlong η (γ.trans δ) (transPrimitive g h) := by
  intro t₀
  set ρ₁ : unitInterval → unitInterval := fun t => Set.projIcc 0 1 zero_le_one (2 * t) with hρ₁
  set ρ₂ : unitInterval → unitInterval := fun t => Set.projIcc 0 1 zero_le_one (2 * t - 1) with hρ₂
  have hρ₁c : Continuous ρ₁ := continuous_projIcc.comp (by fun_prop)
  have hρ₂c : Continuous ρ₂ := continuous_projIcc.comp (by fun_prop)
  have htrans₁ : ∀ t : unitInterval, (t : ℝ) ≤ 1 / 2 → (γ.trans δ) t = γ (ρ₁ t) := by
    intro t ht
    show (if (t : ℝ) ≤ 1 / 2 then γ.extend (2 * t) else δ.extend (2 * t - 1)) = _
    rw [if_pos ht]; rfl
  have htrans₂ : ∀ t : unitInterval, ¬ (t : ℝ) ≤ 1 / 2 → (γ.trans δ) t = δ (ρ₂ t) := by
    intro t ht
    show (if (t : ℝ) ≤ 1 / 2 then γ.extend (2 * t) else δ.extend (2 * t - 1)) = _
    rw [if_neg ht]; rfl
  have hG₁ : ∀ t : unitInterval, (t : ℝ) ≤ 1 / 2 → transPrimitive g h t = g (ρ₁ t) := by
    intro t ht; simp only [transPrimitive, if_pos ht]; rfl
  have hG₂ : ∀ t : unitInterval, ¬ (t : ℝ) ≤ 1 / 2 →
      transPrimitive g h t = h (ρ₂ t) + (g 1 - h 0) := by
    intro t ht; simp only [transPrimitive, if_neg ht]; rfl
  rcases lt_trichotomy (t₀ : ℝ) (1 / 2) with hlt | heq | hgt
  · obtain ⟨Φ, hΦ, hgΦ⟩ := hg (ρ₁ t₀)
    have hev : ∀ᶠ t : unitInterval in 𝓝 t₀, (t : ℝ) < 1 / 2 :=
      (continuous_subtype_val.continuousAt (x := t₀)).eventually (Iio_mem_nhds hlt)
    refine ⟨Φ, ?_, ?_⟩
    · rw [htrans₁ t₀ hlt.le]; exact hΦ
    · have := (hρ₁c.continuousAt (x := t₀)).eventually hgΦ
      filter_upwards [this, hev] with t ht ht'
      rw [hG₁ t ht'.le, htrans₁ t₀ hlt.le, htrans₁ t ht'.le]
      exact ht
  · have hρ₁t₀ : ρ₁ t₀ = 1 := by
      apply Subtype.ext
      simp only [hρ₁, heq]
      norm_num [Set.projIcc]
    have hρ₂t₀ : ρ₂ t₀ = 0 := by
      apply Subtype.ext
      simp only [hρ₂, heq]
      norm_num [Set.projIcc]
    have hmid : (γ.trans δ) t₀ = Q := by rw [htrans₁ t₀ heq.le, hρ₁t₀, γ.target]
    obtain ⟨Φ, hΦ, hgΦ⟩ := hg 1
    obtain ⟨Ψ, hΨ, hhΨ⟩ := hh 0
    simp only [γ.target] at hΦ hgΦ
    simp only [δ.source] at hΨ hhΨ
    have key := eventually_eq_add_of_hasDerivAt hΦ hΨ
    have hg1 : g 1 = Φ (extChartAt 𝓘(ℂ, ℂ) Q Q) := by simpa [γ.target] using hgΦ.self_of_nhds
    have hh0 : h 0 = Ψ (extChartAt 𝓘(ℂ, ℂ) Q Q) := by simpa [δ.source] using hhΨ.self_of_nhds
    refine ⟨Φ, by rw [hmid]; exact hΦ, ?_⟩
    have hc : Tendsto (fun t : unitInterval => extChartAt 𝓘(ℂ, ℂ) Q ((γ.trans δ) t)) (𝓝 t₀)
        (𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q)) := by
      have h1 : Tendsto (γ.trans δ) (𝓝 t₀) (𝓝 Q) := by
        have := (γ.trans δ).continuous.continuousAt (x := t₀)
        rwa [ContinuousAt, hmid] at this
      exact (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) Q).tendsto.comp h1
    have key' := hc.eventually key
    have ev₁ : ∀ᶠ t : unitInterval in 𝓝 t₀, g (ρ₁ t) = Φ (extChartAt 𝓘(ℂ, ℂ) Q (γ (ρ₁ t))) := by
      have := (hρ₁c.continuousAt (x := t₀))
      rw [ContinuousAt, hρ₁t₀] at this
      exact this.eventually hgΦ
    have ev₂ : ∀ᶠ t : unitInterval in 𝓝 t₀, h (ρ₂ t) = Ψ (extChartAt 𝓘(ℂ, ℂ) Q (δ (ρ₂ t))) := by
      have := (hρ₂c.continuousAt (x := t₀))
      rw [ContinuousAt, hρ₂t₀] at this
      exact this.eventually hhΨ
    filter_upwards [ev₁, ev₂, key'] with t h₁ h₂ hk
    rw [hmid]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [hG₁ t ht, h₁, htrans₁ t ht]
    · rw [hG₂ t ht, h₂, ← htrans₂ t ht, hk, hg1, hh0]; ring
  · obtain ⟨Ψ, hΨ, hhΨ⟩ := hh (ρ₂ t₀)
    have hev : ∀ᶠ t : unitInterval in 𝓝 t₀, (1 / 2 : ℝ) < t :=
      (continuous_subtype_val.continuousAt (x := t₀)).eventually (Ioi_mem_nhds hgt)
    refine ⟨fun z => Ψ z + (g 1 - h 0), ?_, ?_⟩
    · rw [htrans₂ t₀ (not_le.mpr hgt)]
      filter_upwards [hΨ] with z hz using hz.add_const _
    · have := (hρ₂c.continuousAt (x := t₀)).eventually hhΨ
      filter_upwards [this, hev] with t ht ht'
      rw [hG₂ t (not_le.mpr ht'), htrans₂ t₀ (not_le.mpr hgt), htrans₂ t (not_le.mpr ht')]
      simp only [ht]

theorem pathIntegral_trans {η : Ω[F⁄ℂ]} {P Q R : Place ℂ F} {γ : Path P Q} {δ : Path Q R}
    {g h : unitInterval → ℂ} (hg : IsPrimitiveAlong η γ g) (hh : IsPrimitiveAlong η δ h) :
    pathIntegral η (γ.trans δ) = pathIntegral η γ + pathIntegral η δ := by
  rw [pathIntegral_eq_of_isPrimitiveAlong (isPrimitiveAlong_trans hg hh),
    pathIntegral_eq_of_isPrimitiveAlong hg, pathIntegral_eq_of_isPrimitiveAlong hh,
    transPrimitive_one, transPrimitive_zero]
  ring

end PathCalculus

section Disc

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
variable [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

structure DiscData {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (v : Place ℂ F) where
  r : ℝ
  r_pos : 0 < r
  G : Fin n → ℂ → ℂ
  ball_subset : Metric.ball (ctr v) r ⊆ (φ v).target
  good : ∀ z ∈ Metric.ball (ctr v) r, (φ v).symm z ∈ (φ v).source ∧
    (∀ i, v.differentialCoeff (b i) ∈ ((φ v).symm z).toValuationSubring) ∧
    v.dCoordFn ∈ ((φ v).symm z).toValuationSubring
  hasDerivAt : ∀ i, ∀ z ∈ Metric.ball (ctr v) r, HasDerivAt (G i) (v.readDifferential (b i) z) z

theorem exists_discData (hF : ChartCompatible F) (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    {n : ℕ} {b : Fin n → Ω[F⁄ℂ]} (hb : ∀ i, b i ∈ regularDifferentials ℂ F) (v : Place ℂ F) :
    Nonempty (DiscData b v) := by
  haveI := hgen

  set Good : Set (Place ℂ F) := (φ v).source ∩
    ((⋂ i, {u : Place ℂ F | v.differentialCoeff (b i) ∈ u.toValuationSubring}) ∩
      {u | v.dCoordFn ∈ u.toValuationSubring}) with hGood
  have hopen : IsOpen Good :=
    (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) v).inter
      ((isOpen_iInter_of_finite fun i => isOpen_setOf_mem _).inter (isOpen_setOf_mem _))
  have hvGood : v ∈ Good :=
    ⟨mem_extChartAt_source v, ⟨mem_iInter.2 fun i => differentialCoeff_mem (hb i) v, dCoordFn_mem v⟩⟩
  have h1 : ∀ᶠ z in 𝓝 (ctr v), (φ v).symm z ∈ Good := by
    refine (continuousAt_extChartAt_symm v).preimage_mem_nhds (hopen.mem_nhds ?_)
    rw [extChartAt_to_inv]; exact hvGood
  have h2 : ∀ᶠ z in 𝓝 (ctr v), z ∈ (φ v).target := extChartAt_target_mem_nhds v
  have h3 : ∀ᶠ z in 𝓝 (ctr v), ∀ i, AnalyticAt ℂ (v.readDifferential (b i)) z := by
    refine Filter.eventually_all.2 fun i => ?_
    exact (analyticAt_readDifferential hF v (differentialCoeff_mem (hb i) v)).eventually_analyticAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and (h2.and h3))
  have hG : ∀ i, ∃ G : ℂ → ℂ, ∀ z ∈ Metric.ball (ctr v) r,
      HasDerivAt G (v.readDifferential (b i) z) z := fun i => by
    have hdiff : DifferentiableOn ℂ (v.readDifferential (b i)) (Metric.ball (ctr v) r) :=
      fun z hz => ((hball z hz).2.2 i).differentiableAt.differentiableWithinAt
    exact hdiff.isExactOn_ball
  choose G hG using hG
  refine ⟨⟨r, hr, G, fun z hz => (hball z hz).2.1, fun z hz => ?_, hG⟩⟩
  obtain ⟨hsrc, hcoef, hπ⟩ := (hball z hz).1
  exact ⟨hsrc, mem_iInter.1 hcoef, hπ⟩

variable {n : ℕ} {b : Fin n → Ω[F⁄ℂ]} {v : Place ℂ F}

def seg (v : Place ℂ F) (w : ℂ) (t : ℝ) : ℂ := ctr v + (t : ℂ) * (w - ctr v)

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem seg_mem_ball {r : ℝ} {w : ℂ} (hw : w ∈ Metric.ball (ctr v) r) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : seg v w t ∈ Metric.ball (ctr v) r := by
  have h := (convex_ball (ctr v) r).add_smul_sub_mem (Metric.mem_ball_self
    (lt_of_le_of_lt dist_nonneg (Metric.mem_ball.1 hw) : 0 < r)) hw ht
  simpa [seg, Complex.real_smul] using h

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem continuous_seg (w : ℂ) : Continuous (seg v w) := by
  unfold seg; fun_prop

def segPath (d : DiscData b v) {w : ℂ} (hw : w ∈ Metric.ball (ctr v) d.r) :
    Path v ((φ v).symm w) where
  toFun t := (φ v).symm (seg v w t)
  continuous_toFun := by
    refine (continuousOn_extChartAt_symm v).comp_continuous
      ((continuous_seg w).comp continuous_subtype_val) fun t => ?_
    exact d.ball_subset (seg_mem_ball hw t.2)
  source' := by
    show (φ v).symm (seg v w ((0 : unitInterval) : ℝ)) = v
    simp only [seg, Set.Icc.coe_zero, Complex.ofReal_zero, zero_mul, add_zero]
    exact extChartAt_to_inv v
  target' := by
    show (φ v).symm (seg v w ((1 : unitInterval) : ℝ)) = (φ v).symm w
    simp only [seg, Set.Icc.coe_one, Complex.ofReal_one, one_mul, add_sub_cancel]

theorem segPath_apply (d : DiscData b v) {w : ℂ} (hw : w ∈ Metric.ball (ctr v) d.r)
    (t : unitInterval) : segPath d hw t = (φ v).symm (seg v w t) := rfl

theorem isPrimitiveAlong_segPath (hF : ChartCompatible F) (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    (hb : ∀ i, b i ∈ regularDifferentials ℂ F) (d : DiscData b v) {w : ℂ}
    (hw : w ∈ Metric.ball (ctr v) d.r) (i : Fin n) :
    IsPrimitiveAlong (b i) (segPath d hw) (fun t => d.G i (seg v w t)) := by
  haveI := hgen
  intro t₀
  set Q : Place ℂ F := segPath d hw t₀ with hQ
  have hst₀ : seg v w t₀ ∈ Metric.ball (ctr v) d.r := seg_mem_ball hw t₀.2
  obtain ⟨hQsrc, hQcoef, hQπ⟩ := d.good _ hst₀
  have hQeq : (φ v).symm (seg v w t₀) = Q := rfl
  rw [hQeq] at hQsrc hQcoef hQπ
  have hφQ : φ v Q = seg v w t₀ := by
    rw [← hQeq]; exact (φ v).right_inv (d.ball_subset hst₀)
  refine ⟨d.G i ∘ (φ v ∘ (φ Q).symm), ?_, ?_⟩
  ·
    have hchg := readDifferential_change hF (v := v) (w := Q) hQsrc
      (differentialCoeff_mem (hb i) Q) (hQcoef i) hQπ
    have hzt : ∀ᶠ z in 𝓝 (ctr Q), z ∈ (φ Q).target := extChartAt_target_mem_nhds _
    have hzs : ∀ᶠ z in 𝓝 (ctr Q), (φ Q).symm z ∈ (φ v).source :=
      eventually_symm_mem_source (mem_extChartAt_target _)
        (by rw [extChartAt_to_inv]; exact hQsrc)
    have hzb : ∀ᶠ z in 𝓝 (ctr Q), φ v ((φ Q).symm z) ∈ Metric.ball (ctr v) d.r := by
      have hcont : ContinuousAt (φ v ∘ (φ Q).symm) (ctr Q) := by
        refine ContinuousAt.comp ?_ (continuousAt_extChartAt_symm _)
        rw [extChartAt_to_inv]
        exact continuousAt_extChartAt' hQsrc
      refine hcont.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds ?_)
      show φ v ((φ Q).symm (ctr Q)) ∈ Metric.ball (ctr v) d.r
      rw [extChartAt_to_inv, hφQ]
      exact hst₀
    show ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q),
      HasDerivAt (d.G i ∘ (φ v ∘ (φ Q).symm)) (Q.readDifferential (b i) z) z
    filter_upwards [hchg, hzt, hzs, hzb] with z hz hzt hzs hzb
    have hd := (d.hasDerivAt i _ hzb).comp z
      (analyticAt_transition v Q hzt hzs).differentiableAt.hasDerivAt
    rw [hz]
    exact hd
  ·
    have hmem : ∀ᶠ t in 𝓝 t₀, segPath d hw t ∈ (φ Q).source := by
      have := (segPath d hw).continuous.continuousAt (x := t₀)
      exact this.eventually (extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) Q)
    filter_upwards [hmem] with t ht
    show d.G i (seg v w t) = d.G i (φ v ((φ Q).symm (φ Q (segPath d hw t))))
    rw [(φ Q).left_inv ht, segPath_apply, (φ v).right_inv (d.ball_subset (seg_mem_ball hw t.2))]

theorem pathIntegral_segPath (hF : ChartCompatible F) (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    (hb : ∀ i, b i ∈ regularDifferentials ℂ F) (d : DiscData b v) {w : ℂ}
    (hw : w ∈ Metric.ball (ctr v) d.r) (i : Fin n) :
    pathIntegral (b i) (segPath d hw) = d.G i w - d.G i (ctr v) := by
  rw [pathIntegral_eq_of_isPrimitiveAlong (isPrimitiveAlong_segPath hF hgen hb d hw i)]
  simp [seg]

end Disc

section Congruence

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
variable [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

theorem exists_prim (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ChartCompatible F) {η : Ω[F⁄ℂ]} (hη : η ∈ regularDifferentials ℂ F)
    {P Q : Place ℂ F} (γ : Path P Q) : ∃ g, IsPrimitiveAlong η γ g :=
  (exists_isPrimitiveAlong_of_mem_regularDifferentials F hfg hF η hη γ).1

variable [ConnectedSpace (Place ℂ F)]

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem pathConnectedSpace : PathConnectedSpace (Place ℂ F) := by
  haveI : LocallyPathConnectedSpace (Place ℂ F) := ChartedSpace.locallyPathConnectedSpace ℂ (Place ℂ F)
  exact pathConnectedSpace_iff_connectedSpace.2 inferInstance

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem nonempty_path (P Q : Place ℂ F) : Nonempty (Path P Q) :=
  haveI := pathConnectedSpace (F := F)
  ⟨PathConnectedSpace.somePath P Q⟩

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem abelJacobiVec_eq {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ P : Place ℂ F) :
    abelJacobiVec b P₀ P = fun i => pathIntegral (b i) (Classical.choice (nonempty_path P₀ P)) := by
  rw [abelJacobiVec_def, dif_pos (nonempty_path P₀ P)]

theorem abelJacobiVec_sub_sub_mem (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ChartCompatible F) (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    {n : ℕ} {b : Fin n → Ω[F⁄ℂ]} (hb : ∀ i, b i ∈ regularDifferentials ℂ F) {v : Place ℂ F}
    (d : DiscData b v) {w : ℂ} (hw : w ∈ Metric.ball (ctr v) d.r) (P₀ : Place ℂ F) :
    abelJacobiVec b P₀ ((φ v).symm w) - abelJacobiVec b P₀ v - (fun i => d.G i w - d.G i (ctr v)) ∈
      pathPeriodLattice b := by
  set α : Path P₀ ((φ v).symm w) := Classical.choice (nonempty_path P₀ ((φ v).symm w)) with hα
  set β : Path P₀ v := Classical.choice (nonempty_path P₀ v) with hβ
  set σ : Path v ((φ v).symm w) := segPath d hw with hσ
  set ℓ : Path P₀ P₀ := (β.trans σ).trans α.symm with hℓ
  have hloop : (fun i => pathIntegral (b i) ℓ) ∈ pathPeriodLattice b :=
    mem_pathPeriodLattice_of_loop b ℓ
  have key : abelJacobiVec b P₀ ((φ v).symm w) - abelJacobiVec b P₀ v -
      (fun i => d.G i w - d.G i (ctr v)) = -(fun i => pathIntegral (b i) ℓ) := by
    rw [abelJacobiVec_eq, abelJacobiVec_eq]
    funext i
    simp only [Pi.sub_apply, Pi.neg_apply]
    obtain ⟨gα, hgα⟩ := exists_prim hfg hF (hb i) α
    obtain ⟨gβ, hgβ⟩ := exists_prim hfg hF (hb i) β
    have hgσ := isPrimitiveAlong_segPath hF hgen hb d hw i
    rw [hℓ, pathIntegral_trans (isPrimitiveAlong_trans hgβ hgσ) (isPrimitiveAlong_symm hgα),
      pathIntegral_trans hgβ hgσ, pathIntegral_symm hgα, ← hσ,
      pathIntegral_segPath hF hgen hb d hw i]
    ring
  rw [key]
  exact (pathPeriodLattice b).neg_mem hloop

end Congruence

end AlgebraicCurve.LocalJacobiProof
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds.AlgebraicCurve.LocalJacobiProof"
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds.AlgebraicCurve"

open AlgebraicCurve.LocalJacobiProof in
theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    (v : Fin n → Place ℂ F)
    (hv : IsUnit (Matrix.det (Matrix.of fun i j : Fin n =>
        (v j).evalAt ((v j).differentialCoeff (b i)))))
    (P₀ : Place ℂ F) :
    ∃ Φ : (Fin n → Place ℂ F) → (Fin n → ℂ), Φ v = 0 ∧
      (∀ U ∈ 𝓝 v, Φ '' U ∈ 𝓝 (0 : Fin n → ℂ)) ∧
      ∀ᶠ P in 𝓝 v,
        abelJacobiDiv b P₀ ((∑ j, Finsupp.single (P j) 1) - ∑ j, Finsupp.single (v j) 1) - Φ P ∈
          pathPeriodLattice b := by
  classical
  obtain ⟨x, hx, hxfd⟩ := id hfg
  haveI : Algebra.EssFiniteType ℂ F := essFiniteType_of_transcendental_of_finiteDimensional hx hxfd
  have hgen : ∀ v : Place ℂ F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  haveI := hgen
  have hF' : ChartCompatible F := hF

  have hd : ∀ j, Nonempty (DiscData b (v j)) := fun j => exists_discData hF' hgen hb (v j)
  choose d _ using fun j => (⟨Classical.choice (hd j), trivial⟩ : ∃ _ : DiscData b (v j), True)

  set c : Fin n → ℂ := fun j => ctr (v j) with hc
  set Φ₀ : (Fin n → ℂ) → (Fin n → ℂ) := fun w i => (∑ j, (d j).G i (w j)) - ∑ j, (d j).G i (c j)
    with hΦ₀
  set χ : (Fin n → Place ℂ F) → (Fin n → ℂ) := fun P j => φ (v j) (P j) with hχ
  refine ⟨Φ₀ ∘ χ, ?_, ?_, ?_⟩
  ·
    funext i
    exact sub_self _
  ·
    intro U hU

    set M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => (v j).readDifferential (b i) (c j)
      with hM
    have hMunit : IsUnit M := by
      have hMeq : M = (Matrix.of fun i j : Fin n => (v j).evalAt ((v j).differentialCoeff (b i))) *
          Matrix.diagonal fun j => deriv ((v j).chartRead (v j).dCoordFn) (c j) := by
        ext i j
        rw [Matrix.mul_diagonal, hM, Matrix.of_apply, Matrix.of_apply, Place.readDifferential_apply,
          Place.chartRead_apply, hc]
        simp only [extChartAt_to_inv]
      rw [Matrix.isUnit_iff_isUnit_det, hMeq, Matrix.det_mul, Matrix.det_diagonal]
      refine hv.mul (isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun j _ => ?_))
      exact deriv_chartRead_dCoordFn_ne_zero hF' (v j)

    set L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun i =>
      ∑ j, (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (M i j)).comp (ContinuousLinearMap.proj j)
      with hL
    have hLapply : ∀ h : Fin n → ℂ, L h = M.mulVec h := by
      intro h
      funext i
      simp only [hL, ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_eq_mul,
        Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hLinj : Function.Injective L := by
      intro h₁ h₂ h12
      rw [hLapply, hLapply] at h12
      exact Matrix.mulVec_injective_iff_isUnit.2 hMunit h12
    set e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
      (LinearEquiv.ofBijective (L : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
        ⟨hLinj, LinearMap.surjective_of_injective hLinj⟩).toContinuousLinearEquiv with he
    have hecoe : (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = L := by
      ext1 h
      rfl

    have hG : ∀ i j, HasStrictDerivAt ((d j).G i) (M i j) (c j) := by
      intro i j
      have hdiff : DifferentiableOn ℂ ((d j).G i) (Metric.ball (c j) (d j).r) := fun z hz =>
        ((d j).hasDerivAt i z hz).differentiableAt.differentiableWithinAt
      have han : AnalyticAt ℂ ((d j).G i) (c j) :=
        hdiff.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (d j).r_pos))
      have hstrict := han.contDiffAt.hasStrictDerivAt (n := ω) (by simp)
      have hderiv : deriv ((d j).G i) (c j) = M i j := by
        rw [hM, Matrix.of_apply]
        exact ((d j).hasDerivAt i (c j) (Metric.mem_ball_self (d j).r_pos)).deriv
      rw [hderiv] at hstrict
      exact hstrict
    have hΦ₀ : HasStrictFDerivAt Φ₀ L c := by
      rw [hL]
      refine hasStrictFDerivAt_pi.2 fun i => ?_
      have hsum : HasStrictFDerivAt (fun w : Fin n → ℂ => ∑ j, (d j).G i (w j))
          (∑ j, (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (M i j)).comp
            (ContinuousLinearMap.proj j)) c := by
        refine HasStrictFDerivAt.fun_sum fun j _ => ?_
        exact ((hG i j).hasStrictFDerivAt).comp c (hasStrictFDerivAt_apply j c)
      exact hsum.sub_const _
    have hΦ₀' : HasStrictFDerivAt Φ₀ (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) c := by
      rw [hecoe]; exact hΦ₀
    have hΦ₀c : Φ₀ c = 0 := by
      funext i
      exact sub_self _
    have hmap : Filter.map Φ₀ (𝓝 c) = 𝓝 0 := by
      rw [hΦ₀'.map_nhds_eq_of_equiv, hΦ₀c]

    rw [nhds_pi] at hU
    obtain ⟨I, -, t, ht, hts⟩ := Filter.mem_pi.1 hU
    set t' : ∀ j, Set (Place ℂ F) := fun j => t j ∩ (φ (v j)).source with ht'
    have ht'nhds : ∀ j, t' j ∈ 𝓝 (v j) := fun j =>
      Filter.inter_mem (ht j) (extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) (v j))
    have hbox : Set.pi Set.univ (fun j => φ (v j) '' t' j) ∈ 𝓝 c :=
      set_pi_mem_nhds Set.finite_univ fun j _ =>
        extChartAt_image_nhds_mem_nhds_of_boundaryless (ht'nhds j)
    have himage : Φ₀ '' Set.pi Set.univ (fun j => φ (v j) '' t' j) ∈ 𝓝 (0 : Fin n → ℂ) := by
      rw [← hmap]; exact Filter.image_mem_map hbox
    refine Filter.mem_of_superset himage ?_
    rintro _ ⟨w, hw, rfl⟩
    have hw' : ∀ j, ∃ Q ∈ t' j, φ (v j) Q = w j := fun j => hw j (Set.mem_univ j)
    choose Q hQt hQw using hw'
    refine ⟨Q, hts (fun j _ => (hQt j).1), ?_⟩
    show Φ₀ (χ Q) = Φ₀ w
    congr 1
    funext j
    exact hQw j
  ·
    have hbox : Set.pi Set.univ (fun j => (φ (v j)).source ∩
        φ (v j) ⁻¹' Metric.ball (c j) (d j).r) ∈ 𝓝 v :=
      set_pi_mem_nhds Set.finite_univ fun j _ => Filter.inter_mem
        (extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) (v j))
        ((continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) (v j)).preimage_mem_nhds
          (Metric.ball_mem_nhds _ (d j).r_pos))
    filter_upwards [hbox] with P hP
    have hPj : ∀ j, P j ∈ (φ (v j)).source ∧ φ (v j) (P j) ∈ Metric.ball (c j) (d j).r :=
      fun j => hP j (Set.mem_univ j)
    have hAJ : abelJacobiDiv b P₀ ((∑ j, Finsupp.single (P j) 1) - ∑ j, Finsupp.single (v j) 1) =
        ∑ j, (abelJacobiVec b P₀ (P j) - abelJacobiVec b P₀ (v j)) := by
      simp [Finset.sum_sub_distrib]
    have hΦ : (Φ₀ ∘ χ) P = ∑ j, fun i => (d j).G i (φ (v j) (P j)) - (d j).G i (c j) := by
      funext i
      simp [hΦ₀, hχ, Finset.sum_sub_distrib]
    rw [hAJ, hΦ, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun j _ => ?_
    have key := abelJacobiVec_sub_sub_mem hfg hF' hgen hb (d j) (hPj j).2 P₀
    rwa [(φ (v j)).left_inv (hPj j).1] at key

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds.AlgebraicCurve.LocalJacobiProof"

end S_AlgebraicCurve_exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds
end P2MW
export P2MW.S_AlgebraicCurve_exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds (solution)
