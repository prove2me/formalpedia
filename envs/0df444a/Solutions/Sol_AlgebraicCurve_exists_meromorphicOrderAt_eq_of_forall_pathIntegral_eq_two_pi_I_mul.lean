-- Prove2me | solution 1 for AlgebraicCurve.exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c7e41feb-7dfc-54a2-b158-6a27950ac97a

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
import Theorems.Thm_AlgebraicCurve_exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg
import Theorems.Thm_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul.AlgebraicCurve Filter Topology Set"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.FiniteResidue Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite IsCurveOver Place.ordDifferential Place.evalAt Place.evalAt_one Place.chartRead_apply IsPrimitiveAlong pathIntegral Place.analyticAt_evalAt_extChartAt_symm_of_mem dCoordGenerates_of_isCurveOver essFiniteType_of_transcendental_of_finiteDimensional exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential"
namespace ExpIntegralProof
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

theorem evalAt_sub (w : Place K F) (hw : w.IsRational) {f g : F}
    (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f - g) = w.evalAt f - w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw (sub_mem hf hg), map_sub, w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_sub]
  rfl

theorem ord_pos_of_evalAt_eq_zero (w : Place K F) (hw : w.IsRational) {f : F}
    (hf : f ∈ w.toValuationSubring) (hf0 : f ≠ 0) (h0 : w.evalAt f = 0) : 0 < w.ord f := by
  have hres : IsLocalRing.residue w.toValuationSubring ⟨f, hf⟩ = 0 := by
    have h := w.algebraMap_evalAt hw hf
    rw [h0, map_zero] at h
    exact h.symm
  have ha : (⟨f, hf⟩ : w.toValuationSubring) ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  have hu : ¬IsUnit (⟨f, hf⟩ : w.toValuationSubring) := by
    rw [IsLocalRing.residue_eq_zero_iff] at hres
    exact (IsLocalRing.mem_maximalIdeal _).1 hres
  have key := ord_pos_of_not_isUnit w ha hu
  exact key

theorem evalAt_ne_zero_of_ord_eq_zero (w : Place K F) (hw : w.IsRational) {f : F} (hf0 : f ≠ 0)
    (h : w.ord f = 0) : w.evalAt f ≠ 0 := fun h0 =>
  absurd (ord_pos_of_evalAt_eq_zero w hw (mem_of_ord_nonneg w h.ge) hf0 h0) (by omega)

theorem dCoordFn_mem (v : Place K F) : v.dCoordFn ∈ v.toValuationSubring :=
  mem_of_ord_nonneg v (by rw [v.ord_dCoordFn]; exact zero_le_one)

theorem dCoordFn_ne_zero (v : Place K F) : v.dCoordFn ≠ 0 := by
  intro h
  have := v.ord_dCoordFn
  rw [h, v.ord_zero] at this
  exact zero_ne_one this

theorem ordDifferential_nonneg_of_evalAt_eq_zero (v : Place K F) (hv : v.IsRational)
    {θ : Ω[F⁄K]} (hθ : -1 ≤ v.ordDifferential θ)
    (hres : v.evalAt (v.dCoordFn * v.differentialCoeff θ) = 0) : 0 ≤ v.ordDifferential θ := by
  by_contra hlt
  have hm1 : v.ordDifferential θ = -1 := by omega
  have hh0 : v.differentialCoeff θ ≠ 0 := by
    intro h0
    rw [Place.ordDifferential, h0, v.ord_zero] at hm1
    omega
  have hord : v.ord (v.dCoordFn * v.differentialCoeff θ) = 0 := by
    rw [v.ord_mul (dCoordFn_ne_zero v) hh0, v.ord_dCoordFn]
    change 1 + v.ordDifferential θ = 0
    omega
  exact evalAt_ne_zero_of_ord_eq_zero v hv (mul_ne_zero (dCoordFn_ne_zero v) hh0) hord hres

theorem differentialCoeff_mem_of_ordDifferential_nonneg (v : Place K F) {θ : Ω[F⁄K]}
    (h : 0 ≤ v.ordDifferential θ) : v.differentialCoeff θ ∈ v.toValuationSubring := by
  by_cases h0 : v.differentialCoeff θ = 0
  · rw [h0]; exact zero_mem _
  · exact mem_of_ord_nonneg v h

theorem dCoordFn_mul_differentialCoeff_mem (v : Place K F) {θ : Ω[F⁄K]}
    (hθ : -1 ≤ v.ordDifferential θ) :
    v.dCoordFn * v.differentialCoeff θ ∈ v.toValuationSubring := by
  by_cases hh0 : v.differentialCoeff θ = 0
  · rw [hh0, mul_zero]; exact zero_mem _
  · apply mem_of_ord_nonneg
    rw [v.ord_mul (dCoordFn_ne_zero v) hh0, v.ord_dCoordFn]
    change 0 ≤ 1 + v.ordDifferential θ
    omega

theorem sub_smul_inv_mem (v : Place K F) (hv : v.IsRational) {θ : Ω[F⁄K]} {m : K}
    (hθ : -1 ≤ v.ordDifferential θ)
    (hres : v.evalAt (v.dCoordFn * v.differentialCoeff θ) = m) :
    v.differentialCoeff θ - algebraMap K F m * v.dCoordFn⁻¹ ∈ v.toValuationSubring := by
  set π := v.dCoordFn with hπ_def
  set h := v.differentialCoeff θ with hh_def
  have hπ0 : π ≠ 0 := dCoordFn_ne_zero v
  have hπh : π * h ∈ v.toValuationSubring := dCoordFn_mul_differentialCoeff_mem v hθ
  have hc : π * h - algebraMap K F m ∈ v.toValuationSubring :=
    sub_mem hπh (v.algebraMap_mem' m)
  have hval : v.evalAt (π * h - algebraMap K F m) = 0 := by
    rw [evalAt_sub v hv hπh (v.algebraMap_mem' m), hres, evalAt_algebraMap', sub_self]
  have hid : h - algebraMap K F m * π⁻¹ = (π * h - algebraMap K F m) * π⁻¹ := by
    field_simp
  rw [hid]
  by_cases h0 : π * h - algebraMap K F m = 0
  · rw [h0, zero_mul]; exact zero_mem _
  · apply mem_of_ord_nonneg
    have hpos := ord_pos_of_evalAt_eq_zero v hv hc h0 hval
    rw [v.ord_mul h0 (inv_ne_zero hπ0), v.ord_inv, v.ord_dCoordFn]
    omega

end Algebra

section Surface

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

abbrev φ (v : Place ℂ F) : PartialEquiv (Place ℂ F) ℂ := extChartAt 𝓘(ℂ, ℂ) v

abbrev ctr (v : Place ℂ F) : ℂ := extChartAt 𝓘(ℂ, ℂ) v v

abbrev pf (w : Place ℂ F) : Filter ℂ := 𝓝[≠] (ctr w)

def ChartCompatible (F : Type*) [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] : Prop :=
  ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
    MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) ∧
    meromorphicOrderAt
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ)

theorem chartRead_algebraMap (w : Place ℂ F) (a : ℂ) :
    w.chartRead (algebraMap ℂ F a) = fun _ => a :=
  funext fun _ => evalAt_algebraMap' _ a

theorem chartRead_one (w : Place ℂ F) : w.chartRead (1 : F) = 1 :=
  funext fun _ => Place.evalAt_one _

variable [IsCurveOver ℂ F]

omit [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] in
theorem isRational (w : Place ℂ F) : w.IsRational := isRational_of_isAlgClosed w

variable [T2Space (Place ℂ F)]

omit [ChartedSpace ℂ (Place ℂ F)] [IsCurveOver ℂ F] in

theorem eventually_nhdsWithin_compl_not_mem {S : Set (Place ℂ F)} (hS : S.Finite)
    (w : Place ℂ F) : ∀ᶠ u in 𝓝[≠] w, u ∉ S := by
  have hfin : (S \ {w}).Finite := hS.subset diff_subset
  have hopen : IsOpen (S \ {w})ᶜ := hfin.isClosed.isOpen_compl
  have hmem : w ∈ (S \ {w})ᶜ := fun h => h.2 rfl
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hopen.mem_nhds hmem] with u hu hne
  intro huS
  exact hu ⟨huS, hne⟩

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] in

theorem eventually_pf_of_eventually_nhdsWithin {P : Place ℂ F → Prop} (w : Place ℂ F)
    (h : ∀ᶠ u in 𝓝[≠] w, P u) : ∀ᶠ z in pf w, P ((φ w).symm z) := by
  rw [eventually_nhdsWithin_iff] at h
  have h1 : ∀ᶠ z in 𝓝 (ctr w), (φ w).symm z ≠ w → P ((φ w).symm z) := by
    have hc : ContinuousAt (φ w).symm (ctr w) := continuousAt_extChartAt_symm w
    have h' : ∀ᶠ u in 𝓝 ((φ w).symm (ctr w)), u ≠ w → P u := by
      rw [extChartAt_to_inv]; exact h
    exact hc.eventually h'
  have h2 : ∀ᶠ z in 𝓝 (ctr w), z ∈ (φ w).target := extChartAt_target_mem_nhds w
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h1, h2] with z hz hzt hne
  refine hz fun heq => hne ?_
  have : φ w ((φ w).symm z) = z := (φ w).right_inv hzt
  rw [mem_singleton_iff, ← this, heq]

theorem eventually_mem_punctured (f : F) (w : Place ℂ F) :
    ∀ᶠ z in pf w, f ∈ ((φ w).symm z).toValuationSubring := by
  by_cases hf0 : f = 0
  · exact Eventually.of_forall fun z => by rw [hf0]; exact zero_mem _
  refine eventually_pf_of_eventually_nhdsWithin (P := fun u => f ∈ u.toValuationSubring) w ?_
  filter_upwards [eventually_nhdsWithin_compl_not_mem (finite_setOf_not_mem (K := ℂ) hf0) w]
    with u hu
  simpa using hu

theorem chartRead_mul (w : Place ℂ F) (f g : F) :
    w.chartRead (f * g) =ᶠ[pf w] w.chartRead f * w.chartRead g := by
  filter_upwards [eventually_mem_punctured f w, eventually_mem_punctured g w] with z hf hg
  exact evalAt_mul _ (isRational _) hf hg

theorem chartRead_add (w : Place ℂ F) (f g : F) :
    w.chartRead (f + g) =ᶠ[pf w] w.chartRead f + w.chartRead g := by
  filter_upwards [eventually_mem_punctured f w, eventually_mem_punctured g w] with z hf hg
  exact evalAt_add _ (isRational _) hf hg

theorem chartRead_inv (w : Place ℂ F) {f : F} (hf : f ≠ 0) :
    w.chartRead f⁻¹ =ᶠ[pf w] (w.chartRead f)⁻¹ := by
  have h := chartRead_mul w f⁻¹ f
  rw [inv_mul_cancel₀ hf, chartRead_one] at h
  filter_upwards [h] with z hz
  rw [Pi.one_apply, Pi.mul_apply] at hz
  exact eq_inv_of_mul_eq_one_left hz.symm

theorem analyticAt_chartRead_center (hF : ChartCompatible F) (v : Place ℂ F) {f : F}
    (hf : f ∈ v.toValuationSubring) : AnalyticAt ℂ (v.chartRead f) (ctr v) :=
  AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF v hf

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] in

theorem chartRead_dCoordFn_eq (hF : ChartCompatible F) (w : Place ℂ F) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u (ctr w) ∧ u (ctr w) ≠ 0 ∧
      ∀ᶠ z in pf w, w.chartRead w.dCoordFn z = (z - ctr w) * u z := by
  obtain ⟨hmer, hord⟩ := hF w.dCoordFn (dCoordFn_ne_zero w) w
  rw [w.ord_dCoordFn] at hord
  obtain ⟨u, hu, hu0, hev⟩ := (meromorphicOrderAt_eq_int_iff hmer).1 (by exact_mod_cast hord)
  refine ⟨u, hu, hu0, ?_⟩
  filter_upwards [hev] with z hz
  rw [Place.chartRead_apply, hz, zpow_one, smul_eq_mul]

end Surface

section PathCalculus

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

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

theorem pathIntegral_of_not_exists {η : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    (h : ¬ ∃ g, IsPrimitiveAlong η γ g) : pathIntegral η γ = 0 := by
  rw [pathIntegral, dif_neg h]

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

theorem exists_isPrimitiveAlong_symm_iff {η : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q} :
    (∃ g, IsPrimitiveAlong η γ.symm g) ↔ ∃ g, IsPrimitiveAlong η γ g := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g ∘ unitInterval.symm, by simpa only [Path.symm_symm] using isPrimitiveAlong_symm hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g ∘ unitInterval.symm, isPrimitiveAlong_symm hg⟩

theorem pathIntegral_symm (η : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) :
    pathIntegral η γ.symm = -pathIntegral η γ := by
  by_cases h : ∃ g, IsPrimitiveAlong η γ g
  · obtain ⟨g, hg⟩ := h
    rw [pathIntegral_eq_of_isPrimitiveAlong hg, pathIntegral_eq_of_isPrimitiveAlong (isPrimitiveAlong_symm hg)]
    simp only [Function.comp_apply, unitInterval.symm_one, unitInterval.symm_zero]
    ring
  · rw [pathIntegral_of_not_exists h, pathIntegral_of_not_exists
      (mt exists_isPrimitiveAlong_symm_iff.mp h), neg_zero]

def transPrimitive (g h : unitInterval → ℂ) : unitInterval → ℂ := fun t =>
  if (t : ℝ) ≤ 1 / 2 then Set.IccExtend zero_le_one g (2 * t)
  else Set.IccExtend zero_le_one h (2 * t - 1) + (g 1 - h 0)

theorem transPrimitive_zero (g h : unitInterval → ℂ) : transPrimitive g h 0 = g 0 := by
  simp [transPrimitive]

theorem transPrimitive_one (g h : unitInterval → ℂ) :
    transPrimitive g h 1 = h 1 + (g 1 - h 0) := by
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

theorem pathIntegral_trans {η : Ω[F⁄ℂ]} {P Q R : Place ℂ F} {γ : Path P Q} {δ : Path Q R}
    (hγ : ∃ g, IsPrimitiveAlong η γ g) (hδ : ∃ h, IsPrimitiveAlong η δ h) :
    pathIntegral η (γ.trans δ) = pathIntegral η γ + pathIntegral η δ := by
  obtain ⟨g, hg⟩ := hγ
  obtain ⟨h, hh⟩ := hδ
  rw [pathIntegral_eq_of_isPrimitiveAlong (isPrimitiveAlong_trans hg hh), pathIntegral_eq_of_isPrimitiveAlong hg,
    pathIntegral_eq_of_isPrimitiveAlong hh, transPrimitive_one, transPrimitive_zero]
  ring

end PathCalculus

section Topology

theorem isPathConnected_ball_diff_singleton (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsPathConnected (Metric.ball c r \ {c}) := by
  let f : ℂ → ℂ := fun y => c + ((r / (1 + ‖y‖) : ℝ) : ℂ) * y
  have hf : Continuous f := by
    have h1 : Continuous fun y : ℂ => (r / (1 + ‖y‖) : ℝ) :=
      continuous_const.div (continuous_const.add continuous_norm) fun y => by positivity
    exact continuous_const.add ((Complex.continuous_ofReal.comp h1).mul continuous_id)
  have hsrc : IsPathConnected ({0}ᶜ : Set ℂ) :=
    isPathConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat) 0
  have himg : f '' {0}ᶜ = Metric.ball c r \ {c} := by
    apply Subset.antisymm
    · rintro - ⟨y, hy, rfl⟩
      have hy0 : y ≠ 0 := hy
      have hny : 0 < ‖y‖ := norm_pos_iff.2 hy0
      have hcoef : 0 < r / (1 + ‖y‖) := by positivity
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm]
        simp only [f, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hcoef]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      · intro h
        rw [mem_singleton_iff] at h
        have : ((r / (1 + ‖y‖) : ℝ) : ℂ) * y = 0 := by
          have := congrArg (· - c) h
          simpa [f] using this
        rcases mul_eq_zero.1 this with h1 | h1
        · exact hcoef.ne' (by exact_mod_cast h1)
        · exact hy0 h1
    · rintro w ⟨hw, hwc⟩
      rw [Metric.mem_ball, dist_eq_norm] at hw
      set d : ℂ := w - c with hd
      have hd0 : d ≠ 0 := fun h => hwc (by rw [mem_singleton_iff]; exact sub_eq_zero.1 h)
      have hnd : 0 < ‖d‖ := norm_pos_iff.2 hd0
      have hrd : 0 < r - ‖d‖ := sub_pos.2 hw
      refine ⟨(((r - ‖d‖)⁻¹ : ℝ) : ℂ) * d, ?_, ?_⟩
      · show (((r - ‖d‖)⁻¹ : ℝ) : ℂ) * d ∈ ({0}ᶜ : Set ℂ)
        rw [mem_compl_iff, mem_singleton_iff]
        exact mul_ne_zero (by exact_mod_cast (inv_pos.2 hrd).ne') hd0
      · have hnorm : ‖(((r - ‖d‖)⁻¹ : ℝ) : ℂ) * d‖ = ‖d‖ / (r - ‖d‖) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hrd)]
          ring
        have hcoef : r / (1 + ‖(((r - ‖d‖)⁻¹ : ℝ) : ℂ) * d‖) = r - ‖d‖ := by
          rw [hnorm]
          field_simp
          ring
        show c + ((r / (1 + ‖(((r - ‖d‖)⁻¹ : ℝ) : ℂ) * d‖) : ℝ) : ℂ) *
            ((((r - ‖d‖)⁻¹ : ℝ) : ℂ) * d) = w
        rw [hcoef, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hrd.ne', Complex.ofReal_one,
          one_mul, hd, add_sub_cancel]
  rw [← himg]
  exact hsrc.image hf

variable {X : Type*} [TopologicalSpace X]

theorem isPreconnected_compl_of_forall_nhd [PreconnectedSpace X] {S : Set X} (hS : IsClosed S)
    (hN : ∀ s ∈ S, ∃ N : Set X, IsOpen N ∧ s ∈ N ∧ N \ {s} ⊆ Sᶜ ∧ IsPreconnected (N \ {s})) :
    IsPreconnected Sᶜ := by
  classical
  choose! N hNo hNs hNsub hNpc using hN
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hsuv hdisj

  have hdich : ∀ s ∈ S, N s \ {s} ⊆ u ∨ N s \ {s} ⊆ v := by
    intro s hs
    refine (isPreconnected_iff_subset_of_disjoint.1 (hNpc s hs)) u v hu hv
      ((hNsub s hs).trans hsuv) ?_
    rw [← subset_empty_iff, ← hdisj]
    exact inter_subset_inter_left _ (hNsub s hs)

  have hNS : ∀ s ∈ S, ∀ x ∈ N s, x ∈ S → x = s := by
    intro s hs x hx hxS
    by_contra hne
    exact hNsub s hs ⟨hx, hne⟩ hxS

  set A : Set X := {s | s ∈ S ∧ N s \ {s} ⊆ u} with hA_def
  set B : Set X := {s | s ∈ S ∧ ¬ (N s \ {s} ⊆ u)} with hB_def
  set U : Set X := (u ∩ Sᶜ) ∪ ⋃ s ∈ A, N s with hU_def
  set V : Set X := (v ∩ Sᶜ) ∪ ⋃ s ∈ B, N s with hV_def
  have hBv : ∀ s ∈ B, N s \ {s} ⊆ v := fun s hs => (hdich s hs.1).resolve_left hs.2
  have hUo : IsOpen U :=
    (hu.inter hS.isOpen_compl).union (isOpen_biUnion fun s hs => hNo s hs.1)
  have hVo : IsOpen V :=
    (hv.inter hS.isOpen_compl).union (isOpen_biUnion fun s hs => hNo s hs.1)
  have hcover : univ ⊆ U ∪ V := by
    intro x _
    by_cases hxS : x ∈ S
    · by_cases hxu : N x \ {x} ⊆ u
      · exact Or.inl (Or.inr (mem_biUnion (show x ∈ A from ⟨hxS, hxu⟩) (hNs x hxS)))
      · exact Or.inr (Or.inr (mem_biUnion (show x ∈ B from ⟨hxS, hxu⟩) (hNs x hxS)))
    · rcases hsuv hxS with h | h
      · exact Or.inl (Or.inl ⟨h, hxS⟩)
      · exact Or.inr (Or.inl ⟨h, hxS⟩)
  have hdisj' : univ ∩ (U ∩ V) = ∅ := by
    rw [univ_inter, ← subset_empty_iff]
    rintro x ⟨hxU, hxV⟩
    have hoff : ∀ {x}, x ∈ Sᶜ → x ∈ u → x ∈ v → False := fun hxS hxu hxv => by
      have : _ ∈ Sᶜ ∩ (u ∩ v) := ⟨hxS, hxu, hxv⟩
      rw [hdisj] at this
      exact this

    have hxu : x ∈ Sᶜ → x ∈ u := by
      intro hxS
      rcases hxU with ⟨h, -⟩ | h
      · exact h
      · rw [mem_iUnion₂] at h
        obtain ⟨s, hsA, hxs⟩ := h
        exact hsA.2 ⟨hxs, fun heq => hxS (by rw [mem_singleton_iff] at heq; rw [heq]; exact hsA.1)⟩
    have hxv : x ∈ Sᶜ → x ∈ v := by
      intro hxS
      rcases hxV with ⟨h, -⟩ | h
      · exact h
      · rw [mem_iUnion₂] at h
        obtain ⟨s, hsB, hxs⟩ := h
        exact hBv s hsB ⟨hxs, fun heq => hxS (by rw [mem_singleton_iff] at heq; rw [heq]; exact hsB.1)⟩
    by_cases hxS : x ∈ S
    ·
      have hxA : x ∈ A := by
        rcases hxU with ⟨-, h⟩ | h
        · exact absurd hxS h
        · rw [mem_iUnion₂] at h
          obtain ⟨s, hsA, hxs⟩ := h
          rw [hNS s hsA.1 x hxs hxS]
          exact hsA
      have hxB : x ∈ B := by
        rcases hxV with ⟨-, h⟩ | h
        · exact absurd hxS h
        · rw [mem_iUnion₂] at h
          obtain ⟨s, hsB, hxs⟩ := h
          rw [hNS s hsB.1 x hxs hxS]
          exact hsB
      exact hxB.2 hxA.2
    · exact hoff hxS (hxu hxS) (hxv hxS)
  rcases (isPreconnected_iff_subset_of_disjoint.1 isPreconnected_univ) U V hUo hVo hcover hdisj'
    with h | h
  · left
    intro x hxS
    rcases h (mem_univ x) with ⟨hxu, -⟩ | hx
    · exact hxu
    · rw [mem_iUnion₂] at hx
      obtain ⟨s, hsA, hxs⟩ := hx
      exact hsA.2 ⟨hxs, fun heq => hxS (by rw [mem_singleton_iff] at heq; rw [heq]; exact hsA.1)⟩
  · right
    intro x hxS
    rcases h (mem_univ x) with ⟨hxv, -⟩ | hx
    · exact hxv
    · rw [mem_iUnion₂] at hx
      obtain ⟨s, hsB, hxs⟩ := hx
      exact hBv s hsB ⟨hxs, fun heq => hxS (by rw [mem_singleton_iff] at heq; rw [heq]; exact hsB.1)⟩

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def disc (v : Place ℂ F) (r : ℝ) : Set (Place ℂ F) :=
  (φ v).source ∩ (φ v) ⁻¹' Metric.ball (ctr v) r

theorem isOpen_disc (v : Place ℂ F) (r : ℝ) : IsOpen (disc v r) :=
  isOpen_extChartAt_preimage' v Metric.isOpen_ball

theorem mem_disc (v : Place ℂ F) {r : ℝ} (hr : 0 < r) : v ∈ disc v r :=
  ⟨mem_extChartAt_source v, Metric.mem_ball_self hr⟩

theorem symm_mem_disc (v : Place ℂ F) {r : ℝ} {z : ℂ} (hz : z ∈ Metric.ball (ctr v) r)
    (hzt : z ∈ (φ v).target) : (φ v).symm z ∈ disc v r := by
  refine ⟨(φ v).map_target hzt, ?_⟩
  show φ v ((φ v).symm z) ∈ Metric.ball (ctr v) r
  rw [(φ v).right_inv hzt]
  exact hz

theorem disc_eq_image (v : Place ℂ F) {r : ℝ} (hB : Metric.ball (ctr v) r ⊆ (φ v).target) :
    disc v r = (φ v).symm '' Metric.ball (ctr v) r :=
  ((φ v).symm_image_eq_source_inter_preimage hB).symm

theorem disc_diff_eq_image (v : Place ℂ F) {r : ℝ} (hB : Metric.ball (ctr v) r ⊆ (φ v).target) :
    disc v r \ {v} = (φ v).symm '' (Metric.ball (ctr v) r \ {ctr v}) := by
  ext x
  constructor
  · rintro ⟨⟨hxs, hxb⟩, hxv⟩
    refine ⟨φ v x, ⟨hxb, fun heq => hxv ?_⟩, (φ v).left_inv hxs⟩
    rw [mem_singleton_iff] at heq ⊢
    exact (φ v).injOn hxs (mem_extChartAt_source v) heq
  · rintro ⟨z, ⟨hzb, hzc⟩, rfl⟩
    refine ⟨symm_mem_disc v hzb (hB hzb), fun heq => hzc ?_⟩
    rw [mem_singleton_iff] at heq ⊢
    rw [← (φ v).right_inv (hB hzb), heq]

theorem isPathConnected_disc_diff (v : Place ℂ F) {r : ℝ} (hr : 0 < r)
    (hB : Metric.ball (ctr v) r ⊆ (φ v).target) : IsPathConnected (disc v r \ {v}) := by
  rw [disc_diff_eq_image v hB]
  exact (isPathConnected_ball_diff_singleton (ctr v) hr).image'
    ((continuousOn_extChartAt_symm v).mono (diff_subset.trans hB))

theorem exists_ball_of_eventually (v : Place ℂ F) {P : ℂ → Prop} (h : ∀ᶠ z in 𝓝 (ctr v), P z) :
    ∃ r > 0, Metric.ball (ctr v) r ⊆ (φ v).target ∧ ∀ z ∈ Metric.ball (ctr v) r, P z := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h.and (extChartAt_target_mem_nhds v))
  exact ⟨r, hr, fun z hz => (hball z hz).2, fun z hz => (hball z hz).1⟩

theorem exists_ball_of_eventually_pf (v : Place ℂ F) {P : ℂ → Prop} (h : ∀ᶠ z in pf v, P z) :
    ∃ r > 0, Metric.ball (ctr v) r ⊆ (φ v).target ∧
      ∀ z ∈ Metric.ball (ctr v) r, z ≠ ctr v → P z := by
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨r, hr, hB, hball⟩ := exists_ball_of_eventually v h
  exact ⟨r, hr, hB, fun z hz hne => hball z hz hne⟩

variable [T2Space (Place ℂ F)]

theorem isPathConnected_compl_of_finite [ConnectedSpace (Place ℂ F)] {S : Set (Place ℂ F)}
    (hS : S.Finite) (hne : Sᶜ.Nonempty) : IsPathConnected Sᶜ := by
  haveI : LocallyPathConnectedSpace (Place ℂ F) := ChartedSpace.locallyPathConnectedSpace ℂ _
  refine (hS.isClosed.isOpen_compl.isConnected_iff_isPathConnected).1 ⟨hne, ?_⟩
  refine isPreconnected_compl_of_forall_nhd hS.isClosed fun s hs => ?_
  obtain ⟨r, hr, hB, hball⟩ := exists_ball_of_eventually_pf s
    (eventually_pf_of_eventually_nhdsWithin (P := fun u => u ∉ S) s
      (eventually_nhdsWithin_compl_not_mem hS s))
  refine ⟨disc s r, isOpen_disc s r, mem_disc s hr, ?_, (isPathConnected_disc_diff s hr hB).isConnected.isPreconnected⟩
  rw [disc_diff_eq_image s hB]
  rintro - ⟨z, ⟨hzb, hzc⟩, rfl⟩
  exact hball z hzb hzc

end Topology

section Main

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]

structure Setup (F : Type*) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] where
  hfg : ∃ x : F, Transcendental ℂ x ∧
    FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F
  hF : ChartCompatible F
  D : Divisor ℂ F
  θ : Ω[F⁄ℂ]
  hθ : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ
  hres : ∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = (D v : ℂ)
  hper : ∀ (P : Place ℂ F) (γ : Path P P), (∀ t, D (γ t) = 0) →
    ∃ m : ℤ, pathIntegral θ γ = 2 * Real.pi * Complex.I * m
  P₀ : Place ℂ F
  hP₀ : D P₀ = 0

namespace Setup

variable (X : Setup F)

def S : Set (Place ℂ F) := (X.D.support : Set (Place ℂ F))

omit [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)] in
theorem not_mem_S_iff {v : Place ℂ F} : v ∉ X.S ↔ X.D v = 0 := by
  simp [S, Finsupp.mem_support_iff]

omit [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)] in
theorem S_finite : X.S.Finite := X.D.support.finite_toSet

omit [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)] in
theorem P₀_not_mem : X.P₀ ∉ X.S := X.not_mem_S_iff.2 X.hP₀

omit [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)] in
include X in
theorem dCoordGenerates (v : Place ℂ F) : v.DCoordGenerates := by
  obtain ⟨x, hx, hxfd⟩ := X.hfg
  haveI := essFiniteType_of_transcendental_of_finiteDimensional hx hxfd
  exact dCoordGenerates_of_isCurveOver v

omit [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)] in

theorem ordDifferential_nonneg {v : Place ℂ F} (hv : v ∉ X.S) : 0 ≤ v.ordDifferential X.θ := by
  refine ordDifferential_nonneg_of_evalAt_eq_zero v (isRational v) (X.hθ v) ?_
  rw [X.hres v, X.not_mem_S_iff.1 hv, Int.cast_zero]

omit [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)] in
theorem coeff_mem {v : Place ℂ F} (hv : v ∉ X.S) :
    v.differentialCoeff X.θ ∈ v.toValuationSubring :=
  differentialCoeff_mem_of_ordDifferential_nonneg v (X.ordDifferential_nonneg hv)

omit [ConnectedSpace (Place ℂ F)] in

theorem exists_isPrimitiveAlong {P Q : Place ℂ F} (γ : Path P Q) (hγ : ∀ t, γ t ∉ X.S) :
    ∃ g, IsPrimitiveAlong X.θ γ g :=
  (AlgebraicCurve.exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg F X.hfg X.hF X.θ γ
    fun t => X.ordDifferential_nonneg (hγ t)).1

omit [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem isPathConnected_compl_S : IsPathConnected X.Sᶜ :=
  isPathConnected_compl_of_finite X.S_finite ⟨X.P₀, X.P₀_not_mem⟩

omit [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem joinedIn {P : Place ℂ F} (hP : P ∉ X.S) : JoinedIn X.Sᶜ X.P₀ P :=
  X.isPathConnected_compl_S.joinedIn X.P₀ X.P₀_not_mem P hP

open Classical in

def expInt (P : Place ℂ F) : ℂ :=
  if h : JoinedIn X.Sᶜ X.P₀ P then Complex.exp (pathIntegral X.θ h.somePath) else 0

omit [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem expInt_eq {P : Place ℂ F} (hP : P ∉ X.S) :
    X.expInt P = Complex.exp (pathIntegral X.θ (X.joinedIn hP).somePath) := by
  rw [expInt, dif_pos (X.joinedIn hP)]

omit [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem expInt_ne_zero {P : Place ℂ F} (hP : P ∉ X.S) : X.expInt P ≠ 0 := by
  rw [X.expInt_eq hP]
  exact Complex.exp_ne_zero _

structure LocalPrimitive (v : Place ℂ F) (W : Set ℂ) (Φ : ℂ → ℂ) : Prop where
  convex : Convex ℝ W
  subset_target : W ⊆ (φ v).target
  not_mem : ∀ z ∈ W, (φ v).symm z ∉ X.S
  coeff_mem : ∀ z ∈ W, v.differentialCoeff X.θ ∈ ((φ v).symm z).toValuationSubring
  unif_mem : ∀ z ∈ W, v.dCoordFn ∈ ((φ v).symm z).toValuationSubring
  hasDerivAt : ∀ z ∈ W, HasDerivAt Φ (v.readDifferential X.θ z) z

omit [ConnectedSpace (Place ℂ F)] in

theorem LocalPrimitive.exists_path {v : Place ℂ F} {W : Set ℂ} (hW : IsOpen W) {Φ : ℂ → ℂ}
    (h : X.LocalPrimitive v W Φ) {z₀ z₁ : ℂ} (hz₀ : z₀ ∈ W) (hz₁ : z₁ ∈ W) :
    ∃ σ : Path ((φ v).symm z₀) ((φ v).symm z₁), (∀ t, σ t ∉ X.S) ∧
      (∃ g, IsPrimitiveAlong X.θ σ g) ∧ pathIntegral X.θ σ = Φ z₁ - Φ z₀ := by
  haveI := X.dCoordGenerates

  set seg : Path z₀ z₁ := Path.segment z₀ z₁ with hseg
  have hsegW : ∀ t, seg t ∈ W := fun t => by
    rw [hseg, Path.segment_apply]
    exact h.convex.lineMap_mem hz₀ hz₁ ⟨t.2.1, t.2.2⟩
  have hcont : ContinuousOn (φ v).symm (range seg) := by
    refine (continuousOn_extChartAt_symm v).mono ?_
    rintro - ⟨t, rfl⟩
    exact h.subset_target (hsegW t)
  set σ : Path ((φ v).symm z₀) ((φ v).symm z₁) := seg.map' hcont with hσ
  have hσt : ∀ t, σ t = (φ v).symm (seg t) := fun t => rfl

  set U : Set (Place ℂ F) := (φ v).source ∩ (φ v) ⁻¹' W with hU
  have hUo : IsOpen U := isOpen_extChartAt_preimage' v hW
  have hUsrc : U ⊆ (φ v).source := inter_subset_left
  have hUsymm : ∀ u ∈ U, (φ v).symm (φ v u) = u := fun u hu => (φ v).left_inv hu.1
  have hσU : ∀ t, σ t ∈ U := fun t => by
    rw [hσt]
    refine ⟨(φ v).map_target (h.subset_target (hsegW t)), ?_⟩
    show φ v ((φ v).symm (seg t)) ∈ W
    rw [(φ v).right_inv (h.subset_target (hsegW t))]
    exact hsegW t
  have hprim : IsPrimitiveAlong X.θ σ (fun t => Φ (φ v (σ t))) := by
    refine AlgebraicCurve.isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential F X.hfg
      X.hF X.θ v U hUo hUsrc ?_ ?_ ?_ Φ ?_ σ hσU
    · intro u hu
      have := X.ordDifferential_nonneg (h.not_mem (φ v u) hu.2)
      rwa [hUsymm u hu] at this
    · intro u hu
      have := h.coeff_mem (φ v u) hu.2
      rwa [hUsymm u hu] at this
    · intro u hu
      have := h.unif_mem (φ v u) hu.2
      rwa [hUsymm u hu] at this
    · intro u hu
      exact h.hasDerivAt (φ v u) hu.2
  refine ⟨σ, fun t => ?_, ⟨_, hprim⟩, ?_⟩
  · rw [hσt]
    exact h.not_mem _ (hsegW t)
  · rw [pathIntegral_eq_of_isPrimitiveAlong hprim]
    simp only [Path.target, Path.source]
    rw [(φ v).right_inv (h.subset_target hz₁), (φ v).right_inv (h.subset_target hz₀)]

theorem expInt_symm_eq {v : Place ℂ F} {W : Set ℂ} (hW : IsOpen W) {Φ : ℂ → ℂ}
    (h : X.LocalPrimitive v W Φ) {z₀ z₁ : ℂ} (hz₀ : z₀ ∈ W) (hz₁ : z₁ ∈ W) :
    X.expInt ((φ v).symm z₁) = X.expInt ((φ v).symm z₀) * Complex.exp (Φ z₁ - Φ z₀) := by
  have hP₀ : (φ v).symm z₀ ∉ X.S := h.not_mem z₀ hz₀
  have hP₁ : (φ v).symm z₁ ∉ X.S := h.not_mem z₁ hz₁
  obtain ⟨σ, hσS, hσprim, hσint⟩ := h.exists_path X hW hz₀ hz₁
  set j₀ := (X.joinedIn hP₀).somePath with hj₀
  set j₁ := (X.joinedIn hP₁).somePath with hj₁
  have hj₀S : ∀ t, j₀ t ∉ X.S := fun t => (X.joinedIn hP₀).somePath_mem t
  have hj₁S : ∀ t, j₁ t ∉ X.S := fun t => (X.joinedIn hP₁).somePath_mem t

  set L : Path X.P₀ X.P₀ := (j₀.trans σ).trans j₁.symm with hL
  have hrange : range L ⊆ X.Sᶜ := by
    rw [hL, Path.trans_range, Path.trans_range, Path.symm_range]
    rintro x ((⟨t', rfl⟩ | ⟨t', rfl⟩) | ⟨t', rfl⟩)
    exacts [hj₀S t', hσS t', hj₁S t']
  have hLS : ∀ t, X.D (L t) = 0 := fun t => X.not_mem_S_iff.1 (hrange ⟨t, rfl⟩)
  obtain ⟨m, hm⟩ := X.hper X.P₀ L hLS
  obtain ⟨g₀, hg₀⟩ := X.exists_isPrimitiveAlong j₀ hj₀S
  obtain ⟨g₁, hg₁⟩ := X.exists_isPrimitiveAlong j₁ hj₁S
  obtain ⟨gσ, hgσ⟩ := hσprim
  have hsplit : pathIntegral X.θ L =
      pathIntegral X.θ j₀ + (Φ z₁ - Φ z₀) - pathIntegral X.θ j₁ := by
    rw [hL, pathIntegral_trans ⟨_, isPrimitiveAlong_trans hg₀ hgσ⟩ ⟨_, isPrimitiveAlong_symm hg₁⟩,
      pathIntegral_trans ⟨_, hg₀⟩ ⟨_, hgσ⟩, pathIntegral_symm, hσint]
    ring
  have hkey : pathIntegral X.θ j₁ =
      pathIntegral X.θ j₀ + (Φ z₁ - Φ z₀) + (-m : ℤ) * (2 * Real.pi * Complex.I) := by
    rw [hsplit] at hm
    push_cast
    linear_combination -hm
  rw [X.expInt_eq hP₁, X.expInt_eq hP₀, ← hj₀, ← hj₁, hkey, Complex.exp_add, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem meromorphicAt_expInt (s : Place ℂ F) :
    MeromorphicAt (fun z => X.expInt ((φ s).symm z)) (ctr s) ∧
      meromorphicOrderAt (fun z => X.expInt ((φ s).symm z)) (ctr s) = (X.D s : WithTop ℤ) := by
  haveI := X.dCoordGenerates

  set c : ℂ := ctr s with hc_def
  set m : ℤ := X.D s with hm_def
  set π : F := s.dCoordFn with hπ_def
  set h : F := s.differentialCoeff X.θ with hh_def
  set b : F := h - algebraMap ℂ F (m : ℂ) * π⁻¹ with hb_def
  have hb : b ∈ s.toValuationSubring := sub_smul_inv_mem s (isRational s) (X.hθ s) (X.hres s)
  set p : ℂ → ℂ := s.chartRead π with hp_def
  set rb : ℂ → ℂ := s.chartRead b with hrb_def
  set R : ℂ → ℂ := s.readDifferential X.θ with hR_def
  set R' : ℂ → ℂ := fun z => ((m : ℂ) * (p z)⁻¹ + rb z) * deriv p z with hR'_def
  have hπ0 : π ≠ 0 := dCoordFn_ne_zero s

  obtain ⟨u, hu_an, hu0, hpu⟩ := chartRead_dCoordFn_eq X.hF s
  have hp_an : AnalyticAt ℂ p c := analyticAt_chartRead_center X.hF s (dCoordFn_mem s)
  have hrb_an : AnalyticAt ℂ rb c := analyticAt_chartRead_center X.hF s hb

  have hR_eq : ∀ᶠ z in pf s, R z = R' z := by
    have hsum : h = algebraMap ℂ F (m : ℂ) * π⁻¹ + b := by rw [hb_def]; ring
    have e1 := chartRead_add s (algebraMap ℂ F (m : ℂ) * π⁻¹) b
    have e2 := chartRead_mul s (algebraMap ℂ F (m : ℂ)) π⁻¹
    have e3 := chartRead_inv s hπ0
    filter_upwards [e1, e2, e3] with z h1 h2 h3
    show s.chartRead (s.differentialCoeff X.θ) z * deriv (s.chartRead s.dCoordFn) z = _
    rw [← hh_def, hsum, h1, Pi.add_apply, h2, Pi.mul_apply, h3, Pi.inv_apply,
      chartRead_algebraMap]

  have hfull : ∀ᶠ z in 𝓝 c,
      AnalyticAt ℂ p z ∧ AnalyticAt ℂ rb z ∧ AnalyticAt ℂ u z ∧ u z ≠ 0 :=
    (hp_an.eventually_analyticAt.and hrb_an.eventually_analyticAt).and
      (hu_an.eventually_analyticAt.and (hu_an.continuousAt.eventually_ne hu0)) |>.mono
      fun z hz => ⟨hz.1.1, hz.1.2, hz.2.1, hz.2.2⟩
  have hpunct : ∀ᶠ z in pf s, R z = R' z ∧ (φ s).symm z ∉ X.S ∧
      h ∈ ((φ s).symm z).toValuationSubring ∧ π ∈ ((φ s).symm z).toValuationSubring ∧
      p z = (z - c) * u z :=
    hR_eq.and ((eventually_pf_of_eventually_nhdsWithin (P := fun u => u ∉ X.S) s
      (eventually_nhdsWithin_compl_not_mem X.S_finite s)).and
      ((eventually_mem_punctured h s).and ((eventually_mem_punctured π s).and hpu)))
  rw [eventually_nhdsWithin_iff] at hpunct
  obtain ⟨r, hr, hB, hball⟩ := exists_ball_of_eventually s (hfull.and hpunct)
  have hA : ∀ z ∈ Metric.ball c r,
      AnalyticAt ℂ p z ∧ AnalyticAt ℂ rb z ∧ AnalyticAt ℂ u z ∧ u z ≠ 0 := fun z hz => (hball z hz).1
  have hP : ∀ z ∈ Metric.ball c r, z ≠ c → R z = R' z ∧ (φ s).symm z ∉ X.S ∧
      h ∈ ((φ s).symm z).toValuationSubring ∧ π ∈ ((φ s).symm z).toValuationSubring ∧
      p z = (z - c) * u z := fun z hz hne => (hball z hz).2 hne
  have hp_ne : ∀ z ∈ Metric.ball c r, z ≠ c → p z ≠ 0 := fun z hz hne => by
    rw [(hP z hz hne).2.2.2.2]
    exact mul_ne_zero (sub_ne_zero.2 hne) (hA z hz).2.2.2

  have hΨ'diff : DifferentiableOn ℂ (fun z => rb z * deriv p z) (Metric.ball c r) := fun z hz =>
    ((hA z hz).2.1.mul (hA z hz).1.deriv).differentiableAt.differentiableWithinAt
  obtain ⟨Ψ, hΨ⟩ := hΨ'diff.isExactOn_ball
  set M : ℂ → ℂ := fun z => p z ^ m * Complex.exp (Ψ z) with hM_def
  have hM_ne : ∀ z ∈ Metric.ball c r, z ≠ c → M z ≠ 0 := fun z hz hne =>
    mul_ne_zero (zpow_ne_zero _ (hp_ne z hz hne)) (Complex.exp_ne_zero _)
  have hM_deriv : ∀ z ∈ Metric.ball c r, z ≠ c → HasDerivAt M (R' z * M z) z := by
    intro z hz hne
    have hp0 := hp_ne z hz hne
    have hdp : HasDerivAt p (deriv p z) z := (hA z hz).1.differentiableAt.hasDerivAt
    have h1 : HasDerivAt (fun z => p z ^ m) ((m : ℂ) * p z ^ (m - 1) * deriv p z) z :=
      (hasDerivAt_zpow m (p z) (Or.inl hp0)).comp z hdp
    have h2 : HasDerivAt (fun z => Complex.exp (Ψ z))
        (Complex.exp (Ψ z) * (rb z * deriv p z)) z := (hΨ z hz).cexp
    have h3 := h1.mul h2
    refine h3.congr_deriv ?_
    simp only [hR'_def, hM_def]
    rw [zpow_sub_one₀ hp0]
    field_simp

  set f : ℂ → ℂ := fun z => X.expInt ((φ s).symm z) with hf_def
  set H : ℂ → ℂ := fun z => f z / M z with hH_def
  have hloc : ∀ z₀ ∈ Metric.ball c r, z₀ ≠ c → ∀ᶠ z in 𝓝 z₀, H z = H z₀ := by
    intro z₀ hz₀ hne₀

    have hopen : IsOpen (Metric.ball c r \ {c}) := Metric.isOpen_ball.sdiff isClosed_singleton
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hopen z₀ ⟨hz₀, hne₀⟩
    have hW : ∀ z ∈ Metric.ball z₀ ρ, z ∈ Metric.ball c r ∧ z ≠ c := fun z hz =>
      ⟨(hρsub hz).1, (hρsub hz).2⟩

    have hR'diff : ∀ z ∈ Metric.ball z₀ ρ, DifferentiableAt ℂ R' z := by
      intro z hz
      obtain ⟨hzB, hzc⟩ := hW z hz
      have hz' := hA z hzB
      exact (((differentiableAt_const _).mul (hz'.1.differentiableAt.inv (hp_ne z hzB hzc))).add
        hz'.2.1.differentiableAt).mul hz'.1.deriv.differentiableAt
    have hRdiff : DifferentiableOn ℂ R (Metric.ball z₀ ρ) := by
      intro z hz
      have heq : R =ᶠ[𝓝 z] R' := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
        exact (hP w (hW w hw).1 (hW w hw).2).1
      exact (heq.differentiableAt_iff.2 (hR'diff z hz)).differentiableWithinAt
    obtain ⟨Φ₁, hΦ₁⟩ := hRdiff.isExactOn_ball
    have hLP : X.LocalPrimitive s (Metric.ball z₀ ρ) Φ₁ :=
      { convex := convex_ball _ _
        subset_target := fun z hz => hB (hW z hz).1
        not_mem := fun z hz => (hP z (hW z hz).1 (hW z hz).2).2.1
        coeff_mem := fun z hz => (hP z (hW z hz).1 (hW z hz).2).2.2.1
        unif_mem := fun z hz => (hP z (hW z hz).1 (hW z hz).2).2.2.2.1
        hasDerivAt := hΦ₁ }

    have hMloc : ∀ z ∈ Metric.ball z₀ ρ, M z = M z₀ * Complex.exp (Φ₁ z - Φ₁ z₀) := by
      set N : ℂ → ℂ := fun z => M z * Complex.exp (-(Φ₁ z - Φ₁ z₀)) with hN_def
      have hNd : ∀ z ∈ Metric.ball z₀ ρ, HasDerivAt N 0 z := by
        intro z hz
        obtain ⟨hzB, hzc⟩ := hW z hz
        have h1 := hM_deriv z hzB hzc
        have h2 : HasDerivAt (fun z => Complex.exp (-(Φ₁ z - Φ₁ z₀)))
            (Complex.exp (-(Φ₁ z - Φ₁ z₀)) * (-(R z))) z := by
          have := ((hΦ₁ z hz).sub_const (Φ₁ z₀)).neg.cexp
          simpa using this
        have h3 := h1.mul h2
        have hRR : R z = R' z := (hP z hzB hzc).1
        refine h3.congr_deriv ?_
        rw [hRR]
        ring
      have hNconst : ∀ z ∈ Metric.ball z₀ ρ, N z = N z₀ := fun z hz =>
        Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z₀ ρ).isPreconnected
          (fun w hw => (hNd w hw).differentiableAt.differentiableWithinAt)
          (fun w hw => (hNd w hw).deriv) hz (Metric.mem_ball_self hρ)
      intro z hz
      have key := hNconst z hz
      simp only [hN_def, sub_self, neg_zero, Complex.exp_zero, mul_one] at key
      calc M z = M z * Complex.exp (-(Φ₁ z - Φ₁ z₀)) * Complex.exp (Φ₁ z - Φ₁ z₀) := by
            rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
        _ = M z₀ * Complex.exp (Φ₁ z - Φ₁ z₀) := by rw [key]
    filter_upwards [Metric.ball_mem_nhds z₀ hρ] with z hz
    have hfz : f z = f z₀ * Complex.exp (Φ₁ z - Φ₁ z₀) :=
      X.expInt_symm_eq Metric.isOpen_ball hLP (Metric.mem_ball_self hρ) hz
    show f z / M z = f z₀ / M z₀
    rw [hfz, hMloc z hz, mul_div_mul_right _ _ (Complex.exp_ne_zero _)]

  have hconst : ∀ z ∈ Metric.ball c r, z ≠ c → ∀ w ∈ Metric.ball c r, w ≠ c → H z = H w := by
    haveI : PreconnectedSpace ↥(Metric.ball c r \ {c}) := Subtype.preconnectedSpace
      (isPathConnected_ball_diff_singleton c hr).isConnected.isPreconnected
    have hlc : IsLocallyConstant (fun q : ↥(Metric.ball c r \ {c}) => H q) := by
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun q => ?_
      have hq := hloc q.1 q.2.1 q.2.2
      exact continuous_subtype_val.continuousAt.eventually hq
    intro z hz hzc w hw hwc
    exact hlc.apply_eq_of_preconnectedSpace ⟨z, hz, hzc⟩ ⟨w, hw, hwc⟩

  set z₁ : ℂ := c + (r / 2 : ℝ) with hz₁_def
  have hz₁ : z₁ ∈ Metric.ball c r := by
    rw [Metric.mem_ball, dist_eq_norm, hz₁_def, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hz₁c : z₁ ≠ c := by
    rw [hz₁_def, Ne, add_eq_left]
    exact_mod_cast (by positivity : (r / 2 : ℝ) ≠ 0)
  set K : ℂ := H z₁ with hK_def
  have hK0 : K ≠ 0 :=
    div_ne_zero (X.expInt_ne_zero (hP z₁ hz₁ hz₁c).2.1) (hM_ne z₁ hz₁ hz₁c)
  have hfKM : ∀ z ∈ Metric.ball c r, z ≠ c → f z = K * M z := by
    intro z hz hzc
    have hHz : f z / M z = K := hconst z hz hzc z₁ hz₁ hz₁c
    rw [← hHz, div_mul_cancel₀ _ (hM_ne z hz hzc)]

  set G : ℂ → ℂ := fun z => K * u z ^ m * Complex.exp (Ψ z) with hG_def
  have hΨ_an : AnalyticAt ℂ Ψ c := DifferentiableOn.analyticAt
    (fun z hz => (hΨ z hz).differentiableAt.differentiableWithinAt) (Metric.ball_mem_nhds c hr)
  have hG_an : AnalyticAt ℂ G c := by
    have h1 : AnalyticAt ℂ (fun z => u z ^ m) c := hu_an.zpow hu0
    have h2 : AnalyticAt ℂ (fun z => Complex.exp (Ψ z)) c := hΨ_an.cexp
    exact (analyticAt_const.mul h1).mul h2
  have hG0 : G c ≠ 0 :=
    mul_ne_zero (mul_ne_zero hK0 (zpow_ne_zero _ hu0)) (Complex.exp_ne_zero _)
  have hev : ∀ᶠ z in 𝓝[≠] c, f z = (z - c) ^ m • G z := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds c hr] with z hz hzc
    rw [hfKM z hz hzc]
    simp only [hM_def, hG_def, smul_eq_mul]
    rw [(hP z hz hzc).2.2.2.2, mul_zpow]
    ring
  have hmero : MeromorphicAt f c := by
    have h1 : MeromorphicAt (fun z => (z - c) ^ m • G z) c :=
      ((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow m).smul hG_an.meromorphicAt
    exact h1.congr (hev.mono fun z hz => hz.symm)
  exact ⟨hmero, (meromorphicOrderAt_eq_int_iff hmero).2 ⟨G, hG_an, hG0, hev⟩⟩

end Setup

end Main

end AlgebraicCurve.ExpIntegralProof

open AlgebraicCurve.ExpIntegralProof in

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
    (D : Divisor ℂ F) (θ : Ω[F⁄ℂ]) (hθ : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ)
    (hres : ∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ F) (γ : Path P P), (∀ t, D (γ t) = 0) →
      ∃ m : ℤ, pathIntegral θ γ = 2 * Real.pi * Complex.I * m) :
    ∃ g : Place ℂ F → ℂ, ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) v).symm z))
          (extChartAt 𝓘(ℂ, ℂ) v v) = (D v : WithTop ℤ) := by
  have hF' : ChartCompatible F := hF

  obtain ⟨v⟩ := (inferInstance : Nonempty (Place ℂ F))
  have hSfin : ((D.support : Set (Place ℂ F))).Finite := D.support.finite_toSet
  obtain ⟨z, hz⟩ := (eventually_pf_of_eventually_nhdsWithin
    (P := fun u => u ∉ (D.support : Set (Place ℂ F))) v
    (eventually_nhdsWithin_compl_not_mem hSfin v)).exists
  let X : Setup F :=
    { hfg := hfg, hF := hF', D := D, θ := θ, hθ := hθ, hres := hres, hper := hper
      P₀ := (φ v).symm z
      hP₀ := by simpa [Finsupp.mem_support_iff] using hz }
  exact ⟨X.expInt, fun w => X.meromorphicAt_expInt w⟩

end
end S_AlgebraicCurve_exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul
end P2MW
export P2MW.S_AlgebraicCurve_exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul (solution)
