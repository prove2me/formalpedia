-- Prove2me | solution 1 for AlgebraicCurve.isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/cef088b4-3e79-57ce-8afa-0b67731875f8

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential.AlgebraicCurve Filter Topology Set"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.FiniteResidue HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite IsCurveOver Place.evalAt Place.evalAt_one regularDifferentials Place.chartRead_apply Place.readDifferential_apply IsPrimitiveAlong Place.analyticAt_evalAt_extChartAt_symm_of_mem dCoordGenerates_of_isCurveOver essFiniteType_of_transcendental_of_finiteDimensional"
namespace ChartPrimitiveTransportProof
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

end Derivation

end AlgebraicCurve.ChartPrimitiveTransportProof
p2m_reactivate "P2MW.S_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential.AlgebraicCurve P2MW.S_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential.AlgebraicCurve.ChartPrimitiveTransportProof"
p2m_reactivate "P2MW.S_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential.AlgebraicCurve"

open AlgebraicCurve.ChartPrimitiveTransportProof in

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (η : Ω[F⁄ℂ]) (v : Place ℂ F) (U : Set (Place ℂ F)) (hU : IsOpen U)
    (hUv : U ⊆ (extChartAt 𝓘(ℂ, ℂ) v).source)
    (hηU : ∀ u ∈ U, 0 ≤ u.ordDifferential η)
    (hcoeff : ∀ u ∈ U, v.differentialCoeff η ∈ u.toValuationSubring)
    (hunif : ∀ u ∈ U, v.dCoordFn ∈ u.toValuationSubring)
    (Φ : ℂ → ℂ)
    (hΦ : ∀ u ∈ U, HasDerivAt Φ (v.readDifferential η (extChartAt 𝓘(ℂ, ℂ) v u))
      (extChartAt 𝓘(ℂ, ℂ) v u))
    {P Q : Place ℂ F} (γ : Path P Q) (hγ : ∀ t, γ t ∈ U) :
    IsPrimitiveAlong η γ (fun t => Φ (extChartAt 𝓘(ℂ, ℂ) v (γ t))) := by
  obtain ⟨x, hx, hxfd⟩ := hfg
  haveI := essFiniteType_of_transcendental_of_finiteDimensional hx hxfd
  haveI : ∀ w : Place ℂ F, w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have hF' : ChartCompatible F := hF
  intro t₀

  set w : Place ℂ F := γ t₀ with hw_def
  have hwU : w ∈ U := hγ t₀
  have hwsrc : w ∈ (φ v).source := hUv hwU
  have hhw : w.differentialCoeff η ∈ w.toValuationSubring := by
    by_cases h0 : w.differentialCoeff η = 0
    · rw [h0]; exact zero_mem _
    · exact mem_of_ord_nonneg _ (hηU w hwU)
  refine ⟨Φ ∘ (φ v ∘ (φ w).symm), ?_, ?_⟩
  ·
    have hchg := readDifferential_change hF' (v := v) (w := w) hwsrc hhw (hcoeff w hwU)
      (hunif w hwU)
    have hzt : ∀ᶠ z in 𝓝 (ctr w), z ∈ (φ w).target := extChartAt_target_mem_nhds _
    have hzU : ∀ᶠ z in 𝓝 (ctr w), (φ w).symm z ∈ U := by
      refine (continuousAt_extChartAt_symm w).preimage_mem_nhds (hU.mem_nhds ?_)
      rw [extChartAt_to_inv]
      exact hwU
    filter_upwards [hchg, hzt, hzU] with z hz hzt hzU
    have hzs : (φ w).symm z ∈ (φ v).source := hUv hzU
    have hd := (hΦ _ hzU).comp z
      (analyticAt_transition v w hzt hzs).differentiableAt.hasDerivAt
    rw [hz]
    exact hd
  ·
    have hmem : ∀ᶠ t in 𝓝 t₀, γ t ∈ (φ w).source :=
      Filter.Tendsto.eventually (γ.continuous.continuousAt (x := t₀))
        (extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) w)
    filter_upwards [hmem] with t ht
    show Φ (φ v (γ t)) = Φ ((φ v) ((φ w).symm (φ w (γ t))))
    rw [(φ w).left_inv ht]

end
end S_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential
end P2MW
export P2MW.S_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential (solution)
