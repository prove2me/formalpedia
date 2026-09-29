-- Prove2me | solution 1 for AlgebraicCurve.span_real_pathPeriodLattice_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/49ce9fe2-6dfb-5e21-a226-0e3cb900cf3c

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

namespace P2MW.S_AlgebraicCurve_span_real_pathPeriodLattice_eq_top

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_span_real_pathPeriodLattice_eq_top.AlgebraicCurve Filter Topology Set"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.FiniteResidue Place.ord_zero HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite IsCurveOver HasCanonicalDivisor Place.evalAt Place.evalAt_one regularDifferentials Place.chartRead_apply Place.readDifferential_apply IsPrimitiveAlong pathIntegral pathPeriodLattice mem_pathPeriodLattice_of_loop Place.analyticAt_evalAt_extChartAt_symm_of_mem dCoordGenerates_of_isCurveOver essFiniteType_of_transcendental_of_finiteDimensional exists_isPrimitiveAlong_of_mem_regularDifferentials"
namespace SpanRealProof
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
  mem_of_ord_nonneg v (by rw [v.ord_dCoordFn]; exact zero_le_one)

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

theorem eventually_mem_chart (v : Place ℂ F) {f : F} (hf : f ∈ v.toValuationSubring) :
    ∀ᶠ ζ in 𝓝 (ctr v), f ∈ ((φ v).symm ζ).toValuationSubring := by
  have hmem : (φ v).symm (ctr v) ∈ {u : Place ℂ F | f ∈ u.toValuationSubring} := by
    rw [mem_setOf_eq, extChartAt_to_inv]; exact hf
  exact (continuousAt_extChartAt_symm v).preimage_mem_nhds ((isOpen_setOf_mem f).mem_nhds hmem)

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

theorem eventually_eq_add_of_hasDerivAt {f Φ Ψ : ℂ → ℂ} {x₀ : ℂ}
    (hΦ : ∀ᶠ z in 𝓝 x₀, HasDerivAt Φ (f z) z) (hΨ : ∀ᶠ z in 𝓝 x₀, HasDerivAt Ψ (f z) z) :
    ∀ᶠ z in 𝓝 x₀, Ψ z = Φ z + (Ψ x₀ - Φ x₀) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hΦ.and hΨ)
  have hΦd : DifferentiableOn ℂ Φ (Metric.ball x₀ r) := fun z hz =>
    (hball z hz).1.differentiableAt.differentiableWithinAt
  have hΨd : DifferentiableOn ℂ Ψ (Metric.ball x₀ r) := fun z hz =>
    (hball z hz).2.differentiableAt.differentiableWithinAt
  have hderiv : (Metric.ball x₀ r).EqOn (deriv Ψ) (deriv Φ) := fun z hz => by
    rw [(hball z hz).2.deriv, (hball z hz).1.deriv]
  obtain ⟨a, ha⟩ := Metric.isOpen_ball.exists_eq_add_of_deriv_eq
    (convex_ball x₀ r).isPreconnected hΨd hΦd hderiv
  have ha0 : Ψ x₀ = Φ x₀ + a := ha (Metric.mem_ball_self hr)
  filter_upwards [Metric.ball_mem_nhds x₀ hr] with z hz
  rw [ha hz, ha0]; ring

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

theorem lift_eq_readDifferential (hF : ChartCompatible F) (w : Place ℂ F) [w.DCoordGenerates]
    (η : Ω[F⁄ℂ]) :
    (readDeriv hF w).liftKaehlerDifferential η =
      ((w.readDifferential η : ℂ → ℂ) : Germ (pf w) ℂ) := by
  have h1 : η = w.differentialCoeff η • KaehlerDifferential.D ℂ F w.dCoordFn := by
    rw [← w.dCoord_eq_D_dCoordFn, w.differentialCoeff_smul_dCoord]
  have e1 := lift_smul_D hF w (w.differentialCoeff η) w.dCoordFn
  rw [← h1] at e1
  exact e1

theorem readDifferential_eventuallyEq_pf (hF : ChartCompatible F) (w v : Place ℂ F)
    [w.DCoordGenerates] [v.DCoordGenerates] (η : Ω[F⁄ℂ]) :
    w.readDifferential η =ᶠ[pf w]
      w.chartRead (v.differentialCoeff η) * deriv (w.chartRead v.dCoordFn) := by
  have h2 : η = v.differentialCoeff η • KaehlerDifferential.D ℂ F v.dCoordFn := by
    rw [← v.dCoord_eq_D_dCoordFn, v.differentialCoeff_smul_dCoord]
  have e1 := lift_eq_readDifferential hF w η
  have e2 := lift_smul_D hF w (v.differentialCoeff η) v.dCoordFn
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
  have hπ' : ∀ᶠ z in 𝓝 (ctr w), v.dCoordFn ∈ ((φ w).symm z).toValuationSubring :=
    eventually_mem_chart w hπ
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

theorem readDifferential_sum_smul_pf (hF : ChartCompatible F) (w : Place ℂ F)
    [w.DCoordGenerates] {ι : Type*} (s : Finset ι) (c : ι → ℂ) (η : ι → Ω[F⁄ℂ]) :
    w.readDifferential (∑ i ∈ s, c i • η i) =ᶠ[pf w]
      fun z => ∑ i ∈ s, c i * w.readDifferential (η i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e := lift_eq_readDifferential hF w (0 : Ω[F⁄ℂ])
    rw [map_zero] at e
    have e' : ((w.readDifferential (0 : Ω[F⁄ℂ]) : ℂ → ℂ) : Germ (pf w) ℂ) =
        ((fun _ => (0 : ℂ) : ℂ → ℂ) : Germ (pf w) ℂ) := by
      rw [← e]; rfl
    simpa only [Finset.sum_empty] using Germ.coe_eq.1 e'
  | insert a s ha ih =>
    have hlin : (readDeriv hF w).liftKaehlerDifferential (c a • η a + ∑ i ∈ s, c i • η i) =
        c a • (readDeriv hF w).liftKaehlerDifferential (η a) +
          (readDeriv hF w).liftKaehlerDifferential (∑ i ∈ s, c i • η i) := by
      rw [map_add, LinearMap.map_smul_of_tower]
    rw [lift_eq_readDifferential, lift_eq_readDifferential, lift_eq_readDifferential,
      ← Germ.coe_smul, ← Germ.coe_add] at hlin
    have hev := Germ.coe_eq.1 hlin
    rw [Finset.sum_insert ha]
    filter_upwards [hev, ih] with z hz hz'
    rw [hz, Pi.add_apply, Pi.smul_apply, hz', Finset.sum_insert ha, smul_eq_mul]

theorem readDifferential_sum_smul (hF : ChartCompatible F) (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    (w : Place ℂ F) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (η : ι → Ω[F⁄ℂ])
    (hη : ∀ i, η i ∈ regularDifferentials ℂ F) :
    w.readDifferential (∑ i ∈ s, c i • η i) =ᶠ[𝓝 (ctr w)]
      fun z => ∑ i ∈ s, c i * w.readDifferential (η i) z := by
  haveI := hgen
  have hmem : (∑ i ∈ s, c i • η i) ∈ regularDifferentials ℂ F :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hη i)
  refine eventuallyEq_nhds_of_punctured (readDifferential_sum_smul_pf hF w s c η)
    (analyticAt_readDifferential hF w (differentialCoeff_mem hmem w)).continuousAt ?_
  exact tendsto_finsetSum s fun i _ =>
    (continuousAt_const.mul
      (analyticAt_readDifferential hF w (differentialCoeff_mem (hη i) w)).continuousAt)

end Derivation

section PathCalculus

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem IsPrimitiveAlong.sub_eq_sub {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g g' : unitInterval → ℂ} (hg : IsPrimitiveAlong θ γ g) (hg' : IsPrimitiveAlong θ γ g')
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

theorem pathIntegral_eq_of_isPrimitiveAlong {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong θ γ g) : pathIntegral θ γ = g 1 - g 0 := by
  have h : ∃ g, IsPrimitiveAlong θ γ g := ⟨g, hg⟩
  rw [pathIntegral, dif_pos h]
  have := IsPrimitiveAlong.sub_eq_sub h.choose_spec hg 1 0
  linear_combination this

theorem pathIntegral_of_not_exists {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    (h : ¬ ∃ g, IsPrimitiveAlong θ γ g) : pathIntegral θ γ = 0 := by
  rw [pathIntegral, dif_neg h]

namespace IsPrimitiveAlong

private theorem _root_.AlgebraicCurve.SpanRealProof.IsPrimitiveAlong.symm {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong θ γ g) :
    IsPrimitiveAlong θ γ.symm (g ∘ unitInterval.symm) := by
  intro t₀
  obtain ⟨Φ, hΦ, hgΦ⟩ := hg (unitInterval.symm t₀)
  refine ⟨Φ, ?_, ?_⟩
  · simpa only [Path.symm_apply, Function.comp_apply] using hΦ
  · have hσ : ContinuousAt unitInterval.symm t₀ := unitInterval.continuous_symm.continuousAt
    have := hσ.eventually hgΦ
    filter_upwards [this] with t ht
    simpa only [Path.symm_apply, Function.comp_apply] using ht

end IsPrimitiveAlong
p2m_export "AlgebraicCurve.SpanRealProof" "IsPrimitiveAlong.symm"
theorem exists_isPrimitiveAlong_symm_iff {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q} :
    (∃ g, IsPrimitiveAlong θ γ.symm g) ↔ ∃ g, IsPrimitiveAlong θ γ g := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g ∘ unitInterval.symm, by simpa only [Path.symm_symm] using IsPrimitiveAlong.symm hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g ∘ unitInterval.symm, IsPrimitiveAlong.symm hg⟩

theorem pathIntegral_symm (θ : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) :
    pathIntegral θ γ.symm = -pathIntegral θ γ := by
  by_cases h : ∃ g, IsPrimitiveAlong θ γ g
  · obtain ⟨g, hg⟩ := h
    rw [pathIntegral_eq_of_isPrimitiveAlong hg,
      pathIntegral_eq_of_isPrimitiveAlong (IsPrimitiveAlong.symm hg)]
    simp only [Function.comp_apply, unitInterval.symm_one, unitInterval.symm_zero]
    ring
  · rw [pathIntegral_of_not_exists h, pathIntegral_of_not_exists
      (mt exists_isPrimitiveAlong_symm_iff.mp h), neg_zero]

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

namespace IsPrimitiveAlong

private theorem _root_.AlgebraicCurve.SpanRealProof.IsPrimitiveAlong.trans {θ : Ω[F⁄ℂ]} {P Q R : Place ℂ F} {γ : Path P Q} {δ : Path Q R}
    {g h : unitInterval → ℂ} (hg : IsPrimitiveAlong θ γ g) (hh : IsPrimitiveAlong θ δ h) :
    IsPrimitiveAlong θ (γ.trans δ) (transPrimitive g h) := by
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
  ·
    obtain ⟨Φ, hΦ, hgΦ⟩ := hg (ρ₁ t₀)
    have hev : ∀ᶠ t : unitInterval in 𝓝 t₀, (t : ℝ) < 1 / 2 :=
      (continuous_subtype_val.continuousAt (x := t₀)).eventually (Iio_mem_nhds hlt)
    refine ⟨Φ, ?_, ?_⟩
    · rw [htrans₁ t₀ hlt.le]; exact hΦ
    · have := (hρ₁c.continuousAt (x := t₀)).eventually hgΦ
      filter_upwards [this, hev] with t ht ht'
      rw [hG₁ t ht'.le, htrans₁ t₀ hlt.le, htrans₁ t ht'.le]
      exact ht
  ·
    have hρ₁t₀ : ρ₁ t₀ = 1 := by
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
  ·
    obtain ⟨Ψ, hΨ, hhΨ⟩ := hh (ρ₂ t₀)
    have hev : ∀ᶠ t : unitInterval in 𝓝 t₀, (1 / 2 : ℝ) < t :=
      (continuous_subtype_val.continuousAt (x := t₀)).eventually (Ioi_mem_nhds hgt)
    refine ⟨fun z => Ψ z + (g 1 - h 0), ?_, ?_⟩
    · rw [htrans₂ t₀ (not_le.mpr hgt)]
      filter_upwards [hΨ] with z hz using hz.add_const _
    · have := (hρ₂c.continuousAt (x := t₀)).eventually hhΨ
      filter_upwards [this, hev] with t ht ht'
      rw [hG₂ t (not_le.mpr ht'), htrans₂ t₀ (not_le.mpr hgt), htrans₂ t (not_le.mpr ht')]
      simp only [ht]

end IsPrimitiveAlong
p2m_export "AlgebraicCurve.SpanRealProof" "IsPrimitiveAlong.trans"

theorem pathIntegral_trans {θ : Ω[F⁄ℂ]} {P Q R : Place ℂ F} {γ : Path P Q} {δ : Path Q R}
    (hγ : ∃ g, IsPrimitiveAlong θ γ g) (hδ : ∃ h, IsPrimitiveAlong θ δ h) :
    pathIntegral θ (γ.trans δ) = pathIntegral θ γ + pathIntegral θ δ := by
  obtain ⟨g, hg⟩ := hγ
  obtain ⟨h, hh⟩ := hδ
  rw [pathIntegral_eq_of_isPrimitiveAlong (IsPrimitiveAlong.trans hg hh),
    pathIntegral_eq_of_isPrimitiveAlong hg, pathIntegral_eq_of_isPrimitiveAlong hh,
    transPrimitive_one, transPrimitive_zero]
  ring

end PathCalculus

theorem eventually_eq_of_isLocalMax_re {Φ : ℂ → ℂ} {z₀ : ℂ} (hΦ : AnalyticAt ℂ Φ z₀)
    (hmax : IsLocalMax (fun z => (Φ z).re) z₀) : ∀ᶠ z in 𝓝 z₀, Φ z = Φ z₀ := by
  rcases hΦ.eventually_constant_or_nhds_le_map_nhds with h | h
  · exact h
  · exfalso
    have hmem : {w : ℂ | w.re ≤ (Φ z₀).re} ∈ 𝓝 (Φ z₀) := h (Filter.mem_map.mpr hmax)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
    have hin : Φ z₀ + ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (Φ z₀) ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    have := hball hin
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, add_le_iff_nonpos_right] at this
    linarith

section EndStep

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
variable [IsCurveOver ℂ F] [T2Space (Place ℂ F)]

theorem eventually_deriv_chartRead_dCoordFn_ne_zero (hF : ChartCompatible F) (v : Place ℂ F) :
    ∀ᶠ z in 𝓝 (ctr v), deriv (v.chartRead v.dCoordFn) z ≠ 0 := by
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

  have hderiv : ∀ᶠ z in 𝓝 x₀,
      deriv (v.chartRead v.dCoordFn) z = p z + (z - x₀) * deriv p z := by
    obtain ⟨U, hU, hUo, hxU⟩ : ∃ U, (∀ z ∈ U, v.chartRead v.dCoordFn z = (z - x₀) ^ 1 • p z ∧
        AnalyticAt ℂ p z) ∧ IsOpen U ∧ x₀ ∈ U := by
      obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.mp (hpeq.and hp.eventually_analyticAt)
      exact ⟨U, hU, hUo, hxU⟩
    filter_upwards [hUo.mem_nhds hxU] with z hz
    have hloc : v.chartRead v.dCoordFn =ᶠ[𝓝 z] fun w => (w - x₀) * p w := by
      filter_upwards [hUo.mem_nhds hz] with w hw
      rw [(hU w hw).1, pow_one, smul_eq_mul]
    rw [hloc.deriv_eq]
    have hpd : HasDerivAt p (deriv p z) z := (hU z hz).2.differentiableAt.hasDerivAt
    have h1 : HasDerivAt (fun w => w - x₀) 1 z := (hasDerivAt_id z).sub_const x₀
    have h2 : HasDerivAt (fun w => (w - x₀) * p w) (1 * p z + (z - x₀) * deriv p z) z := h1.mul hpd
    rw [h2.deriv]; ring
  have hcont : ContinuousAt (fun z => p z + (z - x₀) * deriv p z) x₀ := by
    have : ContinuousAt (deriv p) x₀ := hp.deriv.continuousAt
    exact hp.continuousAt.add ((continuousAt_id.sub continuousAt_const).mul this)
  have hne : (fun z => p z + (z - x₀) * deriv p z) x₀ ≠ 0 := by simpa using hp0
  filter_upwards [hderiv, hcont.eventually_ne hne] with z hz hz'
  rwa [hz]

theorem eq_zero_of_readDifferential_eventually_eq_zero (hF : ChartCompatible F)
    (v : Place ℂ F) [v.DCoordGenerates] (θ : Ω[F⁄ℂ])
    (h0 : ∀ᶠ z in 𝓝 (ctr v), v.readDifferential θ z = 0) : θ = 0 := by
  set c := v.differentialCoeff θ with hc
  suffices hc0 : c = 0 by
    rw [← v.differentialCoeff_smul_dCoord θ, ← hc, hc0, zero_smul]
  by_contra hc0

  have hread : ∀ᶠ z in 𝓝 (ctr v), v.chartRead c z = 0 := by
    filter_upwards [h0, eventually_deriv_chartRead_dCoordFn_ne_zero hF v] with z hz hz'
    exact (mul_eq_zero.mp hz).resolve_right hz'

  have htop : meromorphicOrderAt (v.chartRead c) (ctr v) = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (hread.filter_mono nhdsWithin_le_nhds)
  have := (hF c hc0 v).2
  change meromorphicOrderAt (v.chartRead c) _ = _ at this
  rw [htop] at this
  exact WithTop.top_ne_coe this

end EndStep

section Segment

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def seg (v : Place ℂ F) (z : ℂ) (t : unitInterval) : ℂ := ctr v + ((t : ℝ) : ℂ) * (z - ctr v)

omit [ChartedSpace ℂ (Place ℂ F)] in
theorem seg_zero [ChartedSpace ℂ (Place ℂ F)] (v : Place ℂ F) (z : ℂ) : seg v z 0 = ctr v := by
  simp [seg]

omit [ChartedSpace ℂ (Place ℂ F)] in
theorem seg_one [ChartedSpace ℂ (Place ℂ F)] (v : Place ℂ F) (z : ℂ) : seg v z 1 = z := by
  simp [seg]

theorem continuous_seg (v : Place ℂ F) (z : ℂ) : Continuous (seg v z) := by
  unfold seg
  fun_prop

theorem seg_mem_ball (v : Place ℂ F) {z : ℂ} {r : ℝ} (hz : z ∈ Metric.ball (ctr v) r)
    (t : unitInterval) : seg v z t ∈ Metric.ball (ctr v) r := by
  rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have : seg v z t - ctr v = ((t : ℝ) : ℂ) * (z - ctr v) := by simp [seg]
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  calc (t : ℝ) * ‖z - ctr v‖ ≤ 1 * ‖z - ctr v‖ :=
        mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
    _ = ‖z - ctr v‖ := one_mul _
    _ < r := hz

def segPath (v : Place ℂ F) {r : ℝ} (hr : Metric.ball (ctr v) r ⊆ (φ v).target) {z : ℂ}
    (hz : z ∈ Metric.ball (ctr v) r) : Path v ((φ v).symm z) where
  toFun t := (φ v).symm (seg v z t)
  continuous_toFun :=
    (continuousOn_extChartAt_symm v).comp_continuous (continuous_seg v z)
      fun t => hr (seg_mem_ball v hz t)
  source' := by
    show (φ v).symm (seg v z 0) = v
    rw [seg_zero, extChartAt_to_inv]
  target' := by
    show (φ v).symm (seg v z 1) = (φ v).symm z
    rw [seg_one]

theorem segPath_apply (v : Place ℂ F) {r : ℝ} (hr : Metric.ball (ctr v) r ⊆ (φ v).target) {z : ℂ}
    (hz : z ∈ Metric.ball (ctr v) r) (t : unitInterval) :
    segPath v hr hz t = (φ v).symm (seg v z t) := rfl

variable [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

theorem isPrimitiveAlong_segPath (hF : ChartCompatible F) (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    {η : Ω[F⁄ℂ]} (hη : η ∈ regularDifferentials ℂ F) (v : Place ℂ F) {r : ℝ}
    (hr : Metric.ball (ctr v) r ⊆ (φ v).target)
    (hreg : ∀ ζ ∈ Metric.ball (ctr v) r,
      v.differentialCoeff η ∈ ((φ v).symm ζ).toValuationSubring ∧
        v.dCoordFn ∈ ((φ v).symm ζ).toValuationSubring)
    {Φ : ℂ → ℂ} (hΦ : ∀ ζ ∈ Metric.ball (ctr v) r, HasDerivAt Φ (v.readDifferential η ζ) ζ)
    {z : ℂ} (hz : z ∈ Metric.ball (ctr v) r) :
    IsPrimitiveAlong η (segPath v hr hz) (fun t => Φ (seg v z t)) := by
  haveI := hgen
  intro t₀
  have hζ₀ : seg v z t₀ ∈ Metric.ball (ctr v) r := seg_mem_ball v hz t₀
  set w : Place ℂ F := (φ v).symm (seg v z t₀) with hw_def
  have hw : w ∈ (φ v).source := (φ v).map_target (hr hζ₀)
  have hφw : φ v w = seg v z t₀ := (φ v).right_inv (hr hζ₀)
  have hpt : segPath v hr hz t₀ = w := rfl
  refine ⟨Φ ∘ (φ v ∘ (φ w).symm), ?_, ?_⟩
  · rw [hpt]
    have hchg := readDifferential_change hF (v := v) (w := w) hw
      (differentialCoeff_mem hη w) (hreg _ hζ₀).1 (hreg _ hζ₀).2
    have hzt : ∀ᶠ ζ in 𝓝 (ctr w), ζ ∈ (φ w).target := extChartAt_target_mem_nhds _
    have hzs : ∀ᶠ ζ in 𝓝 (ctr w), (φ w).symm ζ ∈ (φ v).source :=
      eventually_symm_mem_source (mem_extChartAt_target _)
        (by rw [extChartAt_to_inv]; exact hw)
    have hzb : ∀ᶠ ζ in 𝓝 (ctr w), φ v ((φ w).symm ζ) ∈ Metric.ball (ctr v) r := by
      have hcont : ContinuousAt (φ v ∘ (φ w).symm) (ctr w) := by
        refine ContinuousAt.comp ?_ (continuousAt_extChartAt_symm _)
        rw [extChartAt_to_inv]
        exact continuousAt_extChartAt' hw
      refine hcont.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds ?_)
      show φ v ((φ w).symm (ctr w)) ∈ Metric.ball (ctr v) r
      rw [extChartAt_to_inv, hφw]
      exact hζ₀
    filter_upwards [hchg, hzt, hzs, hzb] with ζ h1 h2 h3 h4
    have hd := (hΦ _ h4).comp ζ (analyticAt_transition v w h2 h3).differentiableAt.hasDerivAt
    rw [h1]
    exact hd
  · have hmem : ∀ᶠ t in 𝓝 t₀, segPath v hr hz t ∈ (φ w).source := by
      have hc := (segPath v hr hz).continuous.continuousAt (x := t₀)
      rw [ContinuousAt, hpt] at hc
      exact hc.eventually (extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) w)
    filter_upwards [hmem] with t ht
    rw [hpt]
    show Φ (seg v z t) = Φ (φ v ((φ w).symm (φ w (segPath v hr hz t))))
    rw [(φ w).left_inv ht, segPath_apply, (φ v).right_inv (hr (seg_mem_ball v hz t))]

theorem pathIntegral_segPath (hF : ChartCompatible F) (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    {η : Ω[F⁄ℂ]} (hη : η ∈ regularDifferentials ℂ F) (v : Place ℂ F) {r : ℝ}
    (hr : Metric.ball (ctr v) r ⊆ (φ v).target)
    (hreg : ∀ ζ ∈ Metric.ball (ctr v) r,
      v.differentialCoeff η ∈ ((φ v).symm ζ).toValuationSubring ∧
        v.dCoordFn ∈ ((φ v).symm ζ).toValuationSubring)
    {Φ : ℂ → ℂ} (hΦ : ∀ ζ ∈ Metric.ball (ctr v) r, HasDerivAt Φ (v.readDifferential η ζ) ζ)
    {z : ℂ} (hz : z ∈ Metric.ball (ctr v) r) :
    pathIntegral η (segPath v hr hz) = Φ z - Φ (ctr v) := by
  rw [pathIntegral_eq_of_isPrimitiveAlong (isPrimitiveAlong_segPath hF hgen hη v hr hreg hΦ hz)]
  show Φ (seg v z 1) - Φ (seg v z 0) = _
  rw [seg_one, seg_zero]

omit [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem exists_ball_primitives (hF : ChartCompatible F) (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    {n : ℕ} (η : Fin n → Ω[F⁄ℂ]) (hη : ∀ i, η i ∈ regularDifferentials ℂ F) (v : Place ℂ F) :
    ∃ r > 0, Metric.ball (ctr v) r ⊆ (φ v).target ∧
      (∀ i, ∀ ζ ∈ Metric.ball (ctr v) r,
        v.differentialCoeff (η i) ∈ ((φ v).symm ζ).toValuationSubring ∧
          v.dCoordFn ∈ ((φ v).symm ζ).toValuationSubring) ∧
      ∃ Φ : Fin n → ℂ → ℂ, ∀ i, ∀ ζ ∈ Metric.ball (ctr v) r,
        HasDerivAt (Φ i) (v.readDifferential (η i) ζ) ζ := by
  haveI := hgen
  have h1 : ∀ᶠ ζ in 𝓝 (ctr v), ζ ∈ (φ v).target := extChartAt_target_mem_nhds v
  have h2 : ∀ᶠ ζ in 𝓝 (ctr v), v.dCoordFn ∈ ((φ v).symm ζ).toValuationSubring :=
    eventually_mem_chart v (dCoordFn_mem v)
  have h3 : ∀ᶠ ζ in 𝓝 (ctr v), ∀ i,
      v.differentialCoeff (η i) ∈ ((φ v).symm ζ).toValuationSubring ∧
        AnalyticAt ℂ (v.readDifferential (η i)) ζ :=
    eventually_all.2 fun i =>
      (eventually_mem_chart v (differentialCoeff_mem (hη i) v)).and
        (analyticAt_readDifferential hF v (differentialCoeff_mem (hη i) v)).eventually_analyticAt
  obtain ⟨r, hr0, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and (h2.and h3))
  refine ⟨r, hr0, fun ζ hζ => (hball ζ hζ).1, fun i ζ hζ =>
    ⟨((hball ζ hζ).2.2 i).1, (hball ζ hζ).2.1⟩, ?_⟩
  have hex : ∀ i, ∃ Φ : ℂ → ℂ, ∀ ζ ∈ Metric.ball (ctr v) r,
      HasDerivAt Φ (v.readDifferential (η i) ζ) ζ := fun i => by
    have hd : DifferentiableOn ℂ (v.readDifferential (η i)) (Metric.ball (ctr v) r) :=
      fun ζ hζ => ((hball ζ hζ).2.2 i).2.differentiableAt.differentiableWithinAt
    exact hd.isExactOn_ball
  choose Φ hΦ using hex
  exact ⟨Φ, hΦ⟩

end Segment

section Global

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def lin {n : ℕ} (c : Fin n → ℂ) (b : Fin n → Ω[F⁄ℂ]) {P Q : Place ℂ F} (σ : Path P Q) : ℂ :=
  ∑ i, c i * pathIntegral (b i) σ

theorem lin_symm {n : ℕ} (c : Fin n → ℂ) (b : Fin n → Ω[F⁄ℂ]) {P Q : Place ℂ F} (σ : Path P Q) :
    lin c b σ.symm = -lin c b σ := by
  simp only [lin, pathIntegral_symm, mul_neg, Finset.sum_neg_distrib]

theorem lin_trans {n : ℕ} (c : Fin n → ℂ) (b : Fin n → Ω[F⁄ℂ])
    (hprim : ∀ i, ∀ {P Q : Place ℂ F} (γ : Path P Q), ∃ g, IsPrimitiveAlong (b i) γ g)
    {P Q R : Place ℂ F} (σ : Path P Q) (τ : Path Q R) :
    lin c b (σ.trans τ) = lin c b σ + lin c b τ := by
  simp only [lin, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pathIntegral_trans (hprim i σ) (hprim i τ)]

variable [PathConnectedSpace (Place ℂ F)]

def U {n : ℕ} (c : Fin n → ℂ) (b : Fin n → Ω[F⁄ℂ]) (P₀ P : Place ℂ F) : ℝ :=
  (lin c b (PathConnectedSpace.somePath P₀ P)).re

theorem U_eq {n : ℕ} (c : Fin n → ℂ) (b : Fin n → Ω[F⁄ℂ])
    (hprim : ∀ i, ∀ {P Q : Place ℂ F} (γ : Path P Q), ∃ g, IsPrimitiveAlong (b i) γ g)
    (hc : ∀ (P : Place ℂ F) (γ : Path P P), (lin c b γ).re = 0)
    (P₀ : Place ℂ F) {P : Place ℂ F} (σ : Path P₀ P) : U c b P₀ P = (lin c b σ).re := by
  have h := hc P₀ ((PathConnectedSpace.somePath P₀ P).trans σ.symm)
  rw [lin_trans c b hprim, lin_symm, Complex.add_re, Complex.neg_re] at h
  unfold U
  linarith

variable [IsCurveOver ℂ F] [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

theorem U_local (hF : ChartCompatible F) (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    {n : ℕ} (c : Fin n → ℂ) (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    (hprim : ∀ i, ∀ {P Q : Place ℂ F} (γ : Path P Q), ∃ g, IsPrimitiveAlong (b i) γ g)
    (hc : ∀ (P : Place ℂ F) (γ : Path P P), (lin c b γ).re = 0)
    (P₀ v : Place ℂ F) :
    ∃ r > 0, ∃ Φ : ℂ → ℂ,
      (∀ ζ ∈ Metric.ball (ctr v) r, HasDerivAt Φ (∑ i, c i * v.readDifferential (b i) ζ) ζ) ∧
      ∀ ζ ∈ Metric.ball (ctr v) r,
        U c b P₀ ((φ v).symm ζ) = U c b P₀ v + ((Φ ζ).re - (Φ (ctr v)).re) := by
  obtain ⟨r, hr0, hrt, hreg, Φ, hΦ⟩ := exists_ball_primitives hF hgen b hb v
  refine ⟨r, hr0, fun ζ => ∑ i, c i * Φ i ζ, fun ζ hζ => ?_, fun ζ hζ => ?_⟩
  · exact HasDerivAt.fun_sum fun i _ => (hΦ i ζ hζ).const_mul (c i)
  · rw [U_eq c b hprim hc P₀ ((PathConnectedSpace.somePath P₀ v).trans (segPath v hrt hζ)),
      lin_trans c b hprim, Complex.add_re]
    unfold U
    congr 1
    have hlin : lin c b (segPath v hrt hζ) = ∑ i, c i * Φ i ζ - ∑ i, c i * Φ i (ctr v) := by
      simp only [lin, ← Finset.sum_sub_distrib, ← mul_sub]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pathIntegral_segPath hF hgen (hb i) v hrt (hreg i) (hΦ i) hζ]
    rw [hlin, Complex.sub_re]

theorem continuous_U (hF : ChartCompatible F) (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    {n : ℕ} (c : Fin n → ℂ) (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    (hprim : ∀ i, ∀ {P Q : Place ℂ F} (γ : Path P Q), ∃ g, IsPrimitiveAlong (b i) γ g)
    (hc : ∀ (P : Place ℂ F) (γ : Path P P), (lin c b γ).re = 0)
    (P₀ : Place ℂ F) : Continuous (U c b P₀) := by
  refine continuous_iff_continuousAt.2 fun v => ?_
  obtain ⟨r, hr0, Φ, hΦ, hU⟩ := U_local hF hgen c b hb hprim hc P₀ v
  have hev : ∀ᶠ P in 𝓝 v, P ∈ (φ v).source ∧ φ v P ∈ Metric.ball (ctr v) r := by
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) v,
      (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) v).preimage_mem_nhds
        (Metric.ball_mem_nhds _ hr0)] with P h1 h2
    exact ⟨h1, h2⟩
  have heq : (fun P => U c b P₀ v + ((Φ (φ v P)).re - (Φ (ctr v)).re)) =ᶠ[𝓝 v] U c b P₀ := by
    filter_upwards [hev] with P hP
    have h := hU (φ v P) hP.2
    rw [(φ v).left_inv hP.1] at h
    exact h.symm
  have hΦc : ContinuousAt Φ (φ v v) := (hΦ _ (Metric.mem_ball_self hr0)).continuousAt
  have hcont : ContinuousAt (fun P => U c b P₀ v + ((Φ (φ v P)).re - (Φ (ctr v)).re)) v := by
    refine continuousAt_const.add (ContinuousAt.sub ?_ continuousAt_const)
    exact Complex.continuous_re.continuousAt.comp
      (ContinuousAt.comp hΦc (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) v))
  exact hcont.congr heq

variable [CompactSpace (Place ℂ F)]

theorem coeff_eq_zero (hF : ChartCompatible F) (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    {n : ℕ} (c : Fin n → ℂ) (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    (hli : LinearIndependent ℂ b)
    (hprim : ∀ i, ∀ {P Q : Place ℂ F} (γ : Path P Q), ∃ g, IsPrimitiveAlong (b i) γ g)
    (hc : ∀ (P : Place ℂ F) (γ : Path P P), (lin c b γ).re = 0) : c = 0 := by
  haveI := hgen
  obtain ⟨P₀⟩ : Nonempty (Place ℂ F) := inferInstance

  obtain ⟨P₁, -, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
    (continuous_U hF hgen c b hb hprim hc P₀).continuousOn
  obtain ⟨r, hr0, Φ, hΦ, hU⟩ := U_local hF hgen c b hb hprim hc P₀ P₁

  have hlocmax : IsLocalMax (fun ζ => (Φ ζ).re) (ctr P₁) := by
    filter_upwards [Metric.ball_mem_nhds (ctr P₁) hr0] with ζ hζ
    have h1 := hU ζ hζ
    have h2 : U c b P₀ ((φ P₁).symm ζ) ≤ U c b P₀ P₁ := hmax (mem_univ _)
    linarith
  have hdiff : DifferentiableOn ℂ Φ (Metric.ball (ctr P₁) r) := fun ζ hζ =>
    (hΦ ζ hζ).differentiableAt.differentiableWithinAt
  have han : AnalyticAt ℂ Φ (ctr P₁) := hdiff.analyticAt (Metric.ball_mem_nhds _ hr0)
  have hconst := eventually_eq_of_isLocalMax_re han hlocmax

  have hzero : ∀ᶠ ζ in 𝓝 (ctr P₁), ∑ i, c i * P₁.readDifferential (b i) ζ = 0 := by
    filter_upwards [hconst.eventually_nhds, Metric.ball_mem_nhds (ctr P₁) hr0] with ζ hζ hζb
    have h1 : HasDerivAt Φ 0 ζ := by
      refine (hasDerivAt_const ζ (Φ (ctr P₁))).congr_of_eventuallyEq ?_
      filter_upwards [hζ] with ζ' hζ' using hζ'
    exact (hΦ ζ hζb).unique h1
  have hsum := readDifferential_sum_smul hF hgen P₁ Finset.univ c b hb
  have hR0 : ∀ᶠ ζ in 𝓝 (ctr P₁), P₁.readDifferential (∑ i, c i • b i) ζ = 0 := by
    filter_upwards [hsum, hzero] with ζ h1 h2
    rw [h1, h2]

  have hω : ∑ i, c i • b i = 0 := eq_zero_of_readDifferential_eventually_eq_zero hF P₁ _ hR0
  funext i
  exact Fintype.linearIndependent_iff.1 hli c hω i

end Global

section Functional

variable {n : ℕ}

def coefVec (ℓ : (Fin n → ℂ) →ₗ[ℝ] ℝ) (i : Fin n) : ℂ :=
  (ℓ (Pi.single i 1) : ℂ) - Complex.I * (ℓ (Pi.single i Complex.I) : ℂ)

theorem apply_eq_re_sum (ℓ : (Fin n → ℂ) →ₗ[ℝ] ℝ) (w : Fin n → ℂ) :
    ℓ w = (∑ i, coefVec ℓ i * w i).re := by
  classical
  have hw : w = ∑ i, ((w i).re • (Pi.single i (1 : ℂ) : Fin n → ℂ) +
      (w i).im • (Pi.single i Complex.I : Fin n → ℂ)) := by
    ext j
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
      Complex.real_smul, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact (Complex.re_add_im (w j)).symm
  conv_lhs => rw [hw]
  simp only [map_sum, map_add, map_smul, smul_eq_mul, Complex.re_sum, coefVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im]
  ring

end Functional

end AlgebraicCurve.SpanRealProof
p2m_reactivate "P2MW.S_AlgebraicCurve_span_real_pathPeriodLattice_eq_top.AlgebraicCurve P2MW.S_AlgebraicCurve_span_real_pathPeriodLattice_eq_top.AlgebraicCurve.SpanRealProof"
p2m_reactivate "P2MW.S_AlgebraicCurve_span_real_pathPeriodLattice_eq_top.AlgebraicCurve"

open AlgebraicCurve.SpanRealProof in

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F)) :
    Submodule.span ℝ (pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])) : Set (Fin n → ℂ)) = ⊤ := by
  obtain ⟨x, hx, hxfd⟩ := id hfg
  haveI := essFiniteType_of_transcendental_of_finiteDimensional hx hxfd
  have hgen : ∀ v : Place ℂ F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have hF' : ChartCompatible F := hF
  haveI : LocallyPathConnectedSpace (Place ℂ F) := ChartedSpace.locallyPathConnectedSpace ℂ (Place ℂ F)
  haveI : PathConnectedSpace (Place ℂ F) := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  set b' : Fin n → Ω[F⁄ℂ] := fun i => (b i : Ω[F⁄ℂ]) with hb'_def
  have hb' : ∀ i, b' i ∈ regularDifferentials ℂ F := fun i => (b i).2
  have hli : LinearIndependent ℂ b' :=
    b.linearIndependent.map' (regularDifferentials ℂ F).subtype (Submodule.ker_subtype _)
  have hprim : ∀ i, ∀ {P Q : Place ℂ F} (γ : Path P Q), ∃ g, IsPrimitiveAlong (b' i) γ g :=
    fun i P Q γ =>
      (exists_isPrimitiveAlong_of_mem_regularDifferentials F hfg hF (b' i) (hb' i) γ).1
  by_contra htop
  obtain ⟨ℓ, hℓ0, hℓbot⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.2 htop) inferInstance

  have hloop : ∀ (P : Place ℂ F) (γ : Path P P), ℓ (fun i => pathIntegral (b' i) γ) = 0 := by
    intro P γ
    have hmem : (fun i => pathIntegral (b' i) γ) ∈
        Submodule.span ℝ (pathPeriodLattice b' : Set (Fin n → ℂ)) :=
      Submodule.subset_span (mem_pathPeriodLattice_of_loop b' γ)
    have h : ℓ (fun i => pathIntegral (b' i) γ) ∈
        Submodule.map ℓ (Submodule.span ℝ (pathPeriodLattice b' : Set (Fin n → ℂ))) :=
      Submodule.mem_map_of_mem hmem
    rw [hℓbot, Submodule.mem_bot] at h
    exact h

  have hc : ∀ (P : Place ℂ F) (γ : Path P P), (lin (coefVec ℓ) b' γ).re = 0 := by
    intro P γ
    have h := hloop P γ
    rw [apply_eq_re_sum] at h
    exact h
  have hc0 : coefVec ℓ = 0 := coeff_eq_zero hF' hgen (coefVec ℓ) b' hb' hli hprim hc
  refine hℓ0 (LinearMap.ext fun w => ?_)
  rw [apply_eq_re_sum ℓ w, hc0]
  simp

end
p2m_reactivate "P2MW.S_AlgebraicCurve_span_real_pathPeriodLattice_eq_top.AlgebraicCurve P2MW.S_AlgebraicCurve_span_real_pathPeriodLattice_eq_top.AlgebraicCurve.SpanRealProof"

end S_AlgebraicCurve_span_real_pathPeriodLattice_eq_top
end P2MW
export P2MW.S_AlgebraicCurve_span_real_pathPeriodLattice_eq_top (solution)
