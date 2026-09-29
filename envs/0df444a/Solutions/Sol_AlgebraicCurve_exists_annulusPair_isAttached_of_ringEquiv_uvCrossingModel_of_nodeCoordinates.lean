-- Prove2me | solution 1 for AlgebraicCurve.exists_annulusPair_isAttached_of_ringEquiv_uvCrossingModel_of_nodeCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4182965d-7aeb-5a3b-8402-16c3a44e01e2

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_exists_mem_and_evalAt_eq
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_eq_of_mem_of_evalAt_eq
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_ord_sub_evalAt_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_annulusPair_isAttached_of_ringEquiv_uvCrossingModel_of_nodeCoordinates

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_annulusPair_isAttached_of_ringEquiv_uvCrossingModel_of_nodeCoordinates.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Annulus Annulus.IsAttached Place Place.ord Place.ord_zero Place.ord_one Place.ord_inv Place.evalAt_one Place.evalAt_ne_zero_of_ord_eq_zero Place.evalAt_algebraMap_eq Place.mem_toValuationSubring_of_ord_nonneg_alt RegularProlongation IsCurveOver NodeAnnulusEngine.exists_mem_and_evalAt_eq NodeAnnulusEngine.eq_of_mem_of_evalAt_eq NodeAnnulusEngine.ord_sub_evalAt_eq_one"
namespace NodeAnnulusEngine
p2m_export "AlgebraicCurve.NodeAnnulusEngine" "exists_mem_and_evalAt_eq eq_of_mem_of_evalAt_eq ord_sub_evalAt_eq_one"
p2m_open "AlgebraicCurve.NodeAnnulusEngine AlgebraicCurve"

section PlaceHelpers

private theorem vsub_inv_mem {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
    (hu : IsUnit (⟨f, hf⟩ : O)) : f⁻¹ ∈ O :=
  O.mem_of_valuation_le_one _ (by
    rw [map_inv₀, show O.valuation f = 1 from (O.valuation_eq_one_iff ⟨f, hf⟩).mp hu, inv_one])

private theorem vsub_isUnit_of_inv_mem {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
    (hf0 : f ≠ 0) (hi : f⁻¹ ∈ O) : IsUnit (⟨f, hf⟩ : O) :=
  isUnit_iff_exists_inv.mpr ⟨⟨f⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ hf0)⟩

private theorem vsub_ne_zero_of_isUnit {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
    (hu : IsUnit (⟨f, hf⟩ : O)) : f ≠ 0 := by
  rintro rfl
  have h0 : (⟨0, hf⟩ : O) = 0 := Subtype.ext rfl
  rw [h0] at hu
  exact not_isUnit_zero hu

private theorem vsub_not_isUnit_algebraMap {L F : Type*} [Field L] [Field F] [Algebra L F] (A : ValuationSubring L)
    (O : ValuationSubring F) (hO : ∀ c : L, algebraMap L F c ∈ O ↔ c ∈ A) (a : ↥A)
    (ha : a ∈ maximalIdeal ↥A) : ¬ IsUnit (⟨algebraMap L F (a : L), (hO a).mpr a.2⟩ : O) := by
  intro hu
  have hi := vsub_inv_mem O _ hu
  rw [← map_inv₀, hO] at hi
  apply (IsLocalRing.mem_maximalIdeal _).mp ha
  rcases eq_or_ne a 0 with rfl | ha0
  · exfalso
    have : (⟨algebraMap L F ((0 : ↥A) : L), (hO _).mpr (0 : ↥A).2⟩ : O) = 0 := Subtype.ext (by simp)
    rw [this] at hu
    exact not_isUnit_zero hu
  have ha0' : (a : L) ≠ 0 := fun h => ha0 (Subtype.ext h)
  exact isUnit_iff_exists_inv.mpr ⟨⟨(a : L)⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ ha0')⟩

private theorem isUnit_transfer {L : Type*} [Field L] (A : ValuationSubring L) {a b : L} (hab : a = b) (ha : a ∈ A)
    (hu : IsUnit (⟨a, ha⟩ : ↥A)) : ∃ h : b ∈ A, IsUnit (⟨b, h⟩ : ↥A) := by
  subst hab
  exact ⟨ha, hu⟩

private theorem vsub_zpow_mem_of_isUnit {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
    (hu : IsUnit (⟨f, hf⟩ : O)) (n : ℤ) : f ^ n ∈ O := by
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem hf m
  · rw [zpow_negSucc]
    refine vsub_inv_mem _ (pow_mem hf _) ?_
    have : (⟨f ^ (m + 1), pow_mem hf (m + 1)⟩ : O) = ⟨f, hf⟩ ^ (m + 1) := Subtype.ext (by simp)
    rw [this]
    exact hu.pow _

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  have hle : v.adicValuation f ≤ 1 := by
    rw [show f = ((⟨f, hf⟩ : v.toValuationSubring) : F) from rfl, v.adicValuation_coe]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero hf0
  have h1 := (WithZero.log_le_log hne one_ne_zero).mpr hle
  rw [WithZero.log_one] at h1
  simp only [Place.ord]
  omega

private theorem isUnit_iff_ord_eq_zero {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  rw [← v.adicValuation_coe_eq_one_iff ⟨f, hf⟩]
  simp only [Place.ord]
  constructor
  · intro h
    rw [h, WithZero.log_one, neg_zero]
  · intro h
    have hne := v.adicValuation_ne_zero hf0
    have hlog : WithZero.log (v.adicValuation f) = 0 := by omega
    rw [← WithZero.exp_log hne, hlog, WithZero.exp_zero]

private theorem one_le_ord_of_not_isUnit {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0)
    (hu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring)) : 1 ≤ v.ord f := by
  have h0 := ord_nonneg_of_mem v hf
  have h1 : v.ord f ≠ 0 := fun h => hu ((isUnit_iff_ord_eq_zero v hf hf0).mpr h)
  omega

private theorem evalAt_eq_zero_iff_not_isUnit (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = 0 ↔ ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  rw [← residue_ne_zero_iff_isUnit, not_not, ← v.algebraMap_evalAt hv hf,
    map_eq_zero_iff _ (algebraMap K v.ResidueField).injective]

private theorem evalAt_zero' : v.evalAt (0 : F) = 0 := by
  have h := v.evalAt_algebraMap_eq (0 : K)
  rwa [map_zero] at h

private theorem evalAt_eq_zero_of_ord_ne_zero (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.ord f ≠ 0) : v.evalAt f = 0 := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact evalAt_zero' v
  exact (evalAt_eq_zero_iff_not_isUnit v hv hf).mpr fun hu => h ((isUnit_iff_ord_eq_zero v hf hf0).mp hu)

private theorem ord_eq_zero_of_evalAt_ne_zero (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  by_contra h'
  exact h (evalAt_eq_zero_of_ord_ne_zero v hv hf h')

private theorem isUnit_of_evalAt_ne_zero (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  by_contra h'
  exact h ((evalAt_eq_zero_iff_not_isUnit v hv hf).mpr h')

private theorem evalAt_add_of_mem (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

private theorem evalAt_neg_of_mem (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (-f) = -v.evalAt f := by
  apply v.algebraMap_residueField_injective
  rw [map_neg, v.algebraMap_evalAt hv (neg_mem hf), v.algebraMap_evalAt hv hf, ← map_neg]
  rfl

private theorem evalAt_sub_of_mem (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  rw [sub_eq_add_neg, evalAt_add_of_mem v hv hf (neg_mem hg), evalAt_neg_of_mem v hv hg, ← sub_eq_add_neg]

private theorem evalAt_pow_of_mem (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp [Place.evalAt_one]
  | succ n ih => rw [pow_succ, v.evalAt_mul_of_mem hv (pow_mem hf n) hf, ih, pow_succ]

private theorem evalAt_inv_of_isUnit (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) : v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hf0 := vsub_ne_zero_of_isUnit _ hf hu
  have hi := vsub_inv_mem v.toValuationSubring hf hu
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← v.evalAt_mul_of_mem hv hf hi, mul_inv_cancel₀ hf0, Place.evalAt_one]

private theorem isUnit_pow_mk {f : F} (hf : f ∈ v.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) (n : ℕ) :
    IsUnit (⟨f ^ n, pow_mem hf n⟩ : v.toValuationSubring) := by
  have : (⟨f ^ n, pow_mem hf n⟩ : v.toValuationSubring) = ⟨f, hf⟩ ^ n := Subtype.ext (by simp)
  rw [this]
  exact hu.pow n

private theorem zpow_mem_of_isUnit {f : F} (hf : f ∈ v.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) (n : ℤ) : f ^ n ∈ v.toValuationSubring := by
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem hf m
  · rw [zpow_negSucc]
    exact vsub_inv_mem _ _ (isUnit_pow_mk v hf hu (m + 1))

private theorem evalAt_zpow_of_isUnit (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) (n : ℤ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, evalAt_pow_of_mem v hv hf]
  · rw [zpow_negSucc, zpow_negSucc, ← evalAt_pow_of_mem v hv hf,
      evalAt_inv_of_isUnit v hv (pow_mem hf _) (isUnit_pow_mk v hf hu (m + 1))]

private theorem ord_algebraMap (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hc' : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  apply (isUnit_iff_ord_eq_zero v (v.algebraMap_mem' c) hc').mp
  refine vsub_isUnit_of_inv_mem _ _ hc' ?_
  rw [← map_inv₀]
  exact v.algebraMap_mem' c⁻¹

private theorem isUnit_algebraMap_mk {c : K} (hc : c ≠ 0) :
    IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
  (isUnit_iff_ord_eq_zero v _ ((map_ne_zero _).mpr hc)).mpr (ord_algebraMap v c)

private theorem ord_smul_const {c : K} (hc : c ≠ 0) {f : F} (hf : f ≠ 0) : v.ord (c • f) = v.ord f := by
  rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).mpr hc) hf, ord_algebraMap v, zero_add]

end PlaceHelpers

section ChartHelpers

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar] (Cc : RegularProlongation A F Fbar)

private theorem chart_isUnit_of_residue_ne_zero {f : Cc.integers} (hf : Cc.residue f ≠ 0) : IsUnit f := by
  by_contra h
  apply hf
  have hmem : f ∈ maximalIdeal Cc.integers := (IsLocalRing.mem_maximalIdeal f).mpr h
  rw [← Cc.ker_residue] at hmem
  exact hmem

private theorem chart_residue_ne_zero_of_isUnit {f : Cc.integers} (hf : IsUnit f) : Cc.residue f ≠ 0 := by
  intro h0
  have hmem : f ∈ RingHom.ker Cc.residue := h0
  rw [Cc.ker_residue] at hmem
  exact (IsLocalRing.mem_maximalIdeal f).mp hmem hf

private theorem chart_residue_eq_zero_iff {f : Cc.integers} : Cc.residue f = 0 ↔ ¬ IsUnit f :=
  ⟨fun h hu => chart_residue_ne_zero_of_isUnit Cc hu h,
   fun h => by_contra fun h' => h (chart_isUnit_of_residue_ne_zero Cc h')⟩

private theorem chart_residue_add {f g : F} (hf : f ∈ Cc.integers) (hg : g ∈ Cc.integers) :
    Cc.residue ⟨f + g, add_mem hf hg⟩ = Cc.residue ⟨f, hf⟩ + Cc.residue ⟨g, hg⟩ := by
  rw [← map_add]; rfl

private theorem chart_residue_mul {f g : F} (hf : f ∈ Cc.integers) (hg : g ∈ Cc.integers) :
    Cc.residue ⟨f * g, mul_mem hf hg⟩ = Cc.residue ⟨f, hf⟩ * Cc.residue ⟨g, hg⟩ := by
  rw [← map_mul]; rfl

private theorem chart_residue_one : Cc.residue ⟨1, one_mem _⟩ = 1 := by
  rw [← map_one Cc.residue]; rfl

private theorem chart_residue_pow {f : F} (hf : f ∈ Cc.integers) (n : ℕ) :
    Cc.residue ⟨f ^ n, pow_mem hf n⟩ = Cc.residue ⟨f, hf⟩ ^ n := by
  rw [← map_pow]; rfl

private theorem chart_algebraMap_mem (a : ↥A) : algebraMap L F (a : L) ∈ Cc.integers :=
  (Cc.algebraMap_mem_iff (a : L)).mpr a.2

private theorem chart_residue_const (a : ↥A) :
    Cc.residue ⟨algebraMap L F (a : L), chart_algebraMap_mem Cc a⟩ =
      algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  Cc.residue_algebraMap a

private theorem chart_residue_smul_eq_zero_of_mem_maximalIdeal {f : F} (hf : f ∈ Cc.integers) (a : ↥A)
    (ha : a ∈ maximalIdeal ↥A) (h : (a : L) • f ∈ Cc.integers) : Cc.residue ⟨(a : L) • f, h⟩ = 0 := by
  have : (⟨(a : L) • f, h⟩ : Cc.integers) = ⟨algebraMap L F (a : L), chart_algebraMap_mem Cc a⟩ * ⟨f, hf⟩ :=
    Subtype.ext (Algebra.smul_def (a : L) f)
  rw [this, map_mul, chart_residue_const, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero, zero_mul]

private theorem chart_inv_mem {f : F} (hf : f ∈ Cc.integers) (hu : IsUnit (⟨f, hf⟩ : Cc.integers)) :
    f⁻¹ ∈ Cc.integers := vsub_inv_mem _ hf hu

private theorem chart_residue_inv {f : F} (hf : f ∈ Cc.integers) (hu : IsUnit (⟨f, hf⟩ : Cc.integers)) :
    Cc.residue ⟨f⁻¹, chart_inv_mem Cc hf hu⟩ = (Cc.residue ⟨f, hf⟩)⁻¹ := by
  have hf0 := vsub_ne_zero_of_isUnit _ hf hu
  symm; apply inv_eq_of_mul_eq_one_right
  rw [← chart_residue_mul, ← chart_residue_one Cc]
  congr 1
  exact Subtype.ext (mul_inv_cancel₀ hf0)

private theorem chart_smul_const_ne_zero {f : F} {c : L} (hc : c • f ∈ Cc.integers)
    (h : Cc.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply h
  have : (⟨(0 : L) • f, hc⟩ : Cc.integers) = 0 := Subtype.ext (by simp)
  rw [this, map_zero]

private theorem chart_zpow_mem {f : F} (hf : f ∈ Cc.integers) (hu : IsUnit (⟨f, hf⟩ : Cc.integers)) (n : ℤ) :
    f ^ n ∈ Cc.integers := vsub_zpow_mem_of_isUnit _ hf hu n

private theorem chart_residue_zpow {f : F} (hf : f ∈ Cc.integers) (hu : IsUnit (⟨f, hf⟩ : Cc.integers)) (n : ℤ) :
    Cc.residue ⟨f ^ n, chart_zpow_mem Cc hf hu n⟩ = (Cc.residue ⟨f, hf⟩) ^ n := by
  rcases n with m | m
  · have : (⟨f ^ (Int.ofNat m), chart_zpow_mem Cc hf hu _⟩ : Cc.integers) = ⟨f ^ m, pow_mem hf m⟩ :=
      Subtype.ext (by simp)
    rw [this, chart_residue_pow, Int.ofNat_eq_natCast, zpow_natCast]
  · have hpu : IsUnit (⟨f ^ (m + 1), pow_mem hf (m + 1)⟩ : Cc.integers) := by
      have : (⟨f ^ (m + 1), pow_mem hf (m + 1)⟩ : Cc.integers) = ⟨f, hf⟩ ^ (m + 1) := Subtype.ext (by simp)
      rw [this]; exact hu.pow _
    have : (⟨f ^ (Int.negSucc m), chart_zpow_mem Cc hf hu _⟩ : Cc.integers) =
        ⟨(f ^ (m + 1))⁻¹, chart_inv_mem Cc _ hpu⟩ := Subtype.ext (by simp [zpow_negSucc])
    rw [this, chart_residue_inv Cc (pow_mem hf _) hpu, chart_residue_pow, zpow_negSucc]

end ChartHelpers

section End

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
  {Fb' : Type*} [Field Fb'] [Algebra (ResidueField A) Fb']

private structure EndHyp (O : RegularProlongation A F Fb) (O' : RegularProlongation A F Fb')
    (xo : Place (ResidueField A) Fb) (xo' : Place (ResidueField A) Fb')
    (S : Set (Place L F)) (𝒩 : Subring F) (z : F) : Prop where
  hrat : ∀ P ∈ S, P.IsRational
  h𝒩 : ∀ f : F, f ∈ 𝒩 ↔ f ∈ O.integers ∧ f ∈ O'.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring
  hval : ∀ f ∈ 𝒩, ∀ P ∈ S, P.evalAt f ∈ A
  hreg : ∀ (f : F) (h : f ∈ O.integers), f ∈ 𝒩 → O.residue ⟨f, h⟩ ≠ 0 → 0 ≤ xo.ord (O.residue ⟨f, h⟩)
  hord : ∀ (f : F) (h : f ∈ O.integers) (h' : f ∈ O'.integers),
    O.residue ⟨f, h⟩ ≠ 0 → O'.residue ⟨f, h'⟩ ≠ 0 →
      {P : Place L F | P ∈ S ∧ P.ord f ≠ 0}.Finite ∧
      ∑ᶠ P ∈ S, P.ord f = xo.ord (O.residue ⟨f, h⟩) + xo'.ord (O'.residue ⟨f, h'⟩)
  hxr : xo.IsRational
  hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n
  hz : z ∈ 𝒩
  hz' : O'.residue ⟨z, ((h𝒩 z).1 hz).2.1⟩ = 0
  hzo : O.residue ⟨z, ((h𝒩 z).1 hz).1⟩ ≠ 0
  hzo1 : xo.ord (O.residue ⟨z, ((h𝒩 z).1 hz).1⟩) = 1
  hzm : ∀ P ∈ S, ∃ h : P.evalAt z ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A
  hz0 : ∀ P ∈ S, P.evalAt z ≠ 0

variable {O : RegularProlongation A F Fb} {O' : RegularProlongation A F Fb'}
  {xo : Place (ResidueField A) Fb} {xo' : Place (ResidueField A) Fb'}
  {S : Set (Place L F)} {𝒩 : Subring F} {z : F}
  (EH : EndHyp O O' xo xo' S 𝒩 z)

include EH

private theorem memO {f : F} (hf : f ∈ 𝒩) : f ∈ O.integers := ((EH.h𝒩 f).1 hf).1
private theorem memO' {f : F} (hf : f ∈ 𝒩) : f ∈ O'.integers := ((EH.h𝒩 f).1 hf).2.1
private theorem memPl {f : F} (hf : f ∈ 𝒩) {P : Place L F} (hP : P ∈ S) : f ∈ P.toValuationSubring :=
  ((EH.h𝒩 f).1 hf).2.2 P hP
private theorem const_mem𝒩 (a : ↥A) : algebraMap L F (a : L) ∈ 𝒩 :=
  (EH.h𝒩 _).2 ⟨chart_algebraMap_mem O a, chart_algebraMap_mem O' a, fun P _ => P.algebraMap_mem' (a : L)⟩

private theorem z_isUnit_O : IsUnit (⟨z, memO EH EH.hz⟩ : O.integers) := chart_isUnit_of_residue_ne_zero O EH.hzo
private theorem z_ne_zero' : z ≠ 0 := vsub_ne_zero_of_isUnit _ _ (z_isUnit_O EH)
private theorem z_isUnit_P {P : Place L F} (hP : P ∈ S) : IsUnit (⟨z, memPl EH EH.hz hP⟩ : P.toValuationSubring) :=
  isUnit_of_evalAt_ne_zero P (EH.hrat P hP) _ (EH.hz0 P hP)
private theorem ord_z_eq_zero {P : Place L F} (hP : P ∈ S) : P.ord z = 0 :=
  ord_eq_zero_of_evalAt_ne_zero P (EH.hrat P hP) (memPl EH EH.hz hP) (EH.hz0 P hP)

omit EH in
private theorem isUnit_one_add_of_mem_maximalIdeal' (m : ↥A) (hm : m ∈ maximalIdeal ↥A) : IsUnit (1 + m) := by
  by_contra hnu
  have h1 : (1 + m) ∈ maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have : (1 : ↥A) ∈ maximalIdeal ↥A := by
    have := sub_mem h1 hm
    rwa [add_sub_cancel_right] at this
  exact (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top ((Ideal.eq_top_iff_one _).mpr this)

omit EH in

private theorem smul_const_inv_mem (Oc : RegularProlongation A F Fb') {g : F} (hg : g ∈ Oc.integers)
    (hg0 : Oc.residue ⟨g, hg⟩ = 0) {c : L} (hc : c • g ∈ Oc.integers) (hcres : Oc.residue ⟨c • g, hc⟩ ≠ 0) :
    ∃ hci : c⁻¹ ∈ A, (⟨c⁻¹, hci⟩ : ↥A) ∈ maximalIdeal ↥A ∧ c ≠ 0 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hcres
    have : (⟨(0 : L) • g, hc⟩ : Oc.integers) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]
  have hcA : c ∉ A := by
    intro hcA
    apply hcres
    have : (⟨c • g, hc⟩ : Oc.integers) = ⟨algebraMap L F c, (Oc.algebraMap_mem_iff c).mpr hcA⟩ * ⟨g, hg⟩ :=
      Subtype.ext (Algebra.smul_def c g)
    rw [this, map_mul, hg0, mul_zero]
  have hci : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
  refine ⟨hci, ?_, hc0⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hcA
  have := vsub_inv_mem A hci hu
  rwa [inv_inv] at this

private theorem no_unit_value {G : F} (hG : G ∈ 𝒩) (hG' : O'.residue ⟨G, memO' EH hG⟩ = 0)
    (hGo : O.residue ⟨G, memO EH hG⟩ ≠ 0) {P₀ : Place L F} (hP₀ : P₀ ∈ S)
    (hunit : IsUnit (⟨P₀.evalAt G, EH.hval G hG P₀ hP₀⟩ : ↥A)) : False := by
  have hGO := memO EH hG
  have hGO' := memO' EH hG
  have hG0 : G ≠ 0 := vsub_ne_zero_of_isUnit _ hGO (chart_isUnit_of_residue_ne_zero O hGo)
  have hz0 : z ≠ 0 := z_ne_zero' EH
  obtain ⟨e, heG, heres⟩ := O'.exists_smul_mem G hG0
  obtain ⟨e', he'z, he'res⟩ := O'.exists_smul_mem z hz0
  obtain ⟨heA, hem, he0⟩ := smul_const_inv_mem O' hGO' hG' heG heres
  obtain ⟨he'A, he'm, he'0⟩ := smul_const_inv_mem O' (memO' EH EH.hz) EH.hz' he'z he'res
  have hb0 : (⟨e'⁻¹, he'A⟩ : ↥A) ≠ 0 := fun h => inv_ne_zero he'0 (by
    have h' := congrArg Subtype.val h
    simpa using h')
  obtain ⟨t, r, hr⟩ := EH.hrk ⟨e⁻¹, heA⟩ ⟨e'⁻¹, he'A⟩ hem hb0
  have hrL : (e⁻¹) ^ t = e'⁻¹ * (r : L) := by
    have h' := congrArg Subtype.val hr
    simpa using h'

  set Zf := G ^ t * z⁻¹ with hZf
  have hZ_O' : Zf ∈ O'.integers := by
    have hunit' : IsUnit (⟨e' • z, he'z⟩ : O'.integers) := chart_isUnit_of_residue_ne_zero O' he'res
    have hmem : (e • G) ^ t * (e' • z)⁻¹ * algebraMap L F (r : L) ∈ O'.integers :=
      mul_mem (mul_mem (pow_mem heG t) (chart_inv_mem O' he'z hunit')) (chart_algebraMap_mem O' r)
    have heq : Zf = (e • G) ^ t * (e' • z)⁻¹ * algebraMap L F (r : L) := by
      have hrF : algebraMap L F (r : L) = algebraMap L F e' * ((algebraMap L F e)⁻¹) ^ t := by
        have : (r : L) = e' * (e⁻¹) ^ t := by
          rw [hrL, ← mul_assoc, mul_inv_cancel₀ he'0, one_mul]
        rw [this, map_mul, map_pow, map_inv₀]
      rw [hZf, hrF, Algebra.smul_def, Algebra.smul_def, mul_pow, mul_inv]
      have hE : algebraMap L F e ≠ 0 := (map_ne_zero _).mpr he0
      have hE' : algebraMap L F e' ≠ 0 := (map_ne_zero _).mpr he'0
      have h1 : (algebraMap L F e) ^ t * ((algebraMap L F e)⁻¹) ^ t = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hE, one_pow]
      have h2 : (algebraMap L F e')⁻¹ * algebraMap L F e' = 1 := inv_mul_cancel₀ hE'
      calc G ^ t * z⁻¹ = G ^ t * z⁻¹ * 1 * 1 := by ring
        _ = G ^ t * z⁻¹ * ((algebraMap L F e) ^ t * ((algebraMap L F e)⁻¹) ^ t) *
              ((algebraMap L F e')⁻¹ * algebraMap L F e') := by rw [h1, h2]
        _ = _ := by ring
    rw [heq]
    exact hmem
  have hZ_O : Zf ∈ O.integers := mul_mem (pow_mem hGO t) (chart_inv_mem O _ (z_isUnit_O EH))
  have hZ_P : ∀ P ∈ S, Zf ∈ P.toValuationSubring := fun P hP =>
    mul_mem (pow_mem (memPl EH hG hP) t) (vsub_inv_mem _ (memPl EH EH.hz hP) (z_isUnit_P EH hP))
  have hZ𝒩 : Zf ∈ 𝒩 := (EH.h𝒩 Zf).2 ⟨hZ_O, hZ_O', hZ_P⟩
  have hZA := EH.hval Zf hZ𝒩 P₀ hP₀
  have hr0 := EH.hrat P₀ hP₀
  have hGt : P₀.evalAt G ^ t = P₀.evalAt Zf * P₀.evalAt z := by
    rw [← evalAt_pow_of_mem P₀ hr0 (memPl EH hG hP₀),
      ← P₀.evalAt_mul_of_mem hr0 (hZ_P P₀ hP₀) (memPl EH EH.hz hP₀)]
    congr 1
    rw [hZf, mul_assoc, inv_mul_cancel₀ hz0, mul_one]
  obtain ⟨hzA, hzm⟩ := EH.hzm P₀ hP₀
  have hmem : (⟨P₀.evalAt G, EH.hval G hG P₀ hP₀⟩ : ↥A) ^ t ∈ maximalIdeal ↥A := by
    have : (⟨P₀.evalAt G, EH.hval G hG P₀ hP₀⟩ : ↥A) ^ t = ⟨P₀.evalAt Zf, hZA⟩ * ⟨P₀.evalAt z, hzA⟩ :=
      Subtype.ext (by simpa using hGt)
    rw [this]
    exact Ideal.mul_mem_left _ _ hzm
  exact (IsLocalRing.mem_maximalIdeal _).mp hmem (hunit.pow t)

private theorem exists_evalAt_eq_zero {f : F} (hf : f ∈ 𝒩) (h1 : O.residue ⟨f, memO EH hf⟩ ≠ 0)
    (h2 : O'.residue ⟨f, memO' EH hf⟩ ≠ 0) (h3 : 1 ≤ xo.ord (O.residue ⟨f, memO EH hf⟩))
    (h4 : 0 ≤ xo'.ord (O'.residue ⟨f, memO' EH hf⟩)) : ∃ P ∈ S, P.evalAt f = 0 := by
  obtain ⟨-, hsum⟩ := EH.hord f (memO EH hf) (memO' EH hf) h1 h2
  by_contra hne
  push Not at hne
  have h0 : ∑ᶠ P ∈ S, P.ord f = 0 :=
    finsum_mem_of_eqOn_zero (fun P hP => ord_eq_zero_of_evalAt_ne_zero P (EH.hrat P hP) (memPl EH hf hP) (hne P hP))
  rw [h0] at hsum
  omega

private theorem branch_cross {G : F} (hG : G ∈ 𝒩) (hG' : O'.residue ⟨G, memO' EH hG⟩ = 0)
    (hGo : O.residue ⟨G, memO EH hG⟩ ≠ 0) (hGo0 : xo.ord (O.residue ⟨G, memO EH hG⟩) = 0)
    (hGS : ∀ P ∈ S, P.ord G = 0) : False := by
  have hGO := memO EH hG
  have hGO' := memO' EH hG
  set ρ := O.residue ⟨G, hGO⟩ with hρ
  have hρmem : ρ ∈ xo.toValuationSubring := Place.mem_toValuationSubring_of_ord_nonneg_alt xo hGo (by rw [hGo0])
  have hβ : xo.evalAt ρ ≠ 0 := Place.evalAt_ne_zero_of_ord_eq_zero xo EH.hxr hGo hGo0
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := ↥A) (-xo.evalAt ρ)
  have hres_a : IsLocalRing.residue (↥A) a ≠ 0 := by rw [ha]; exact neg_ne_zero.mpr hβ
  have haU : IsUnit a := (IsLocalRing.residue_ne_zero_iff_isUnit a).mp hres_a

  have haF𝒩 : algebraMap L F (a : L) ∈ 𝒩 := const_mem𝒩 EH a
  have haO := chart_algebraMap_mem O a
  have haO' := chart_algebraMap_mem O' a
  have hcbar : algebraMap (ResidueField A) Fb (IsLocalRing.residue (↥A) a) ≠ 0 := (map_ne_zero _).mpr hres_a
  have hcbar' : algebraMap (ResidueField A) Fb' (IsLocalRing.residue (↥A) a) ≠ 0 := (map_ne_zero _).mpr hres_a

  have hG₁ : G + algebraMap L F (a : L) ∈ 𝒩 := add_mem hG haF𝒩
  have hres'G₁ : O'.residue ⟨G + algebraMap L F (a : L), memO' EH hG₁⟩ =
      algebraMap (ResidueField A) Fb' (IsLocalRing.residue (↥A) a) := by
    rw [show (⟨G + algebraMap L F (a : L), memO' EH hG₁⟩ : O'.integers) = ⟨G, hGO'⟩ + ⟨_, haO'⟩ from rfl,
      map_add, hG', zero_add, chart_residue_const]
  have hresG₁ : O.residue ⟨G + algebraMap L F (a : L), memO EH hG₁⟩ =
      ρ + algebraMap (ResidueField A) Fb (IsLocalRing.residue (↥A) a) := by
    rw [show (⟨G + algebraMap L F (a : L), memO EH hG₁⟩ : O.integers) = ⟨G, hGO⟩ + ⟨_, haO⟩ from rfl,
      map_add, chart_residue_const]

  have hvalG₁ : ∀ P ∈ S, P.evalAt (G + algebraMap L F (a : L)) = P.evalAt G + (a : L) := fun P hP => by
    rw [evalAt_add_of_mem P (EH.hrat P hP) (memPl EH hG hP) (P.algebraMap_mem' _), Place.evalAt_algebraMap_eq]
  by_cases hc : ρ + algebraMap (ResidueField A) Fb (IsLocalRing.residue (↥A) a) = 0
  ·
    have haz : algebraMap L F (a : L) * z ∈ 𝒩 := mul_mem haF𝒩 EH.hz
    have hG₂ : G + algebraMap L F (a : L) + algebraMap L F (a : L) * z ∈ 𝒩 := add_mem hG₁ haz
    have hresaz : O.residue ⟨algebraMap L F (a : L) * z, memO EH haz⟩ =
        algebraMap (ResidueField A) Fb (IsLocalRing.residue (↥A) a) * O.residue ⟨z, memO EH EH.hz⟩ := by
      rw [show (⟨algebraMap L F (a : L) * z, memO EH haz⟩ : O.integers) = ⟨_, haO⟩ * ⟨z, memO EH EH.hz⟩ from rfl,
        map_mul, chart_residue_const]
    have hres'az : O'.residue ⟨algebraMap L F (a : L) * z, memO' EH haz⟩ = 0 := by
      rw [show (⟨algebraMap L F (a : L) * z, memO' EH haz⟩ : O'.integers) = ⟨_, haO'⟩ * ⟨z, memO' EH EH.hz⟩ from rfl,
        map_mul, EH.hz', mul_zero]
    have hresG₂ : O.residue ⟨_, memO EH hG₂⟩ =
        algebraMap (ResidueField A) Fb (IsLocalRing.residue (↥A) a) * O.residue ⟨z, memO EH EH.hz⟩ := by
      rw [show (⟨_, memO EH hG₂⟩ : O.integers) = ⟨_, memO EH hG₁⟩ + ⟨_, memO EH haz⟩ from rfl, map_add,
        hresG₁, hc, zero_add, hresaz]
    have hres'G₂ : O'.residue ⟨_, memO' EH hG₂⟩ = algebraMap (ResidueField A) Fb' (IsLocalRing.residue (↥A) a) := by
      rw [show (⟨_, memO' EH hG₂⟩ : O'.integers) = ⟨_, memO' EH hG₁⟩ + ⟨_, memO' EH haz⟩ from rfl, map_add,
        hres'G₁, hres'az, add_zero]
    have h1 : O.residue ⟨_, memO EH hG₂⟩ ≠ 0 := by rw [hresG₂]; exact mul_ne_zero hcbar EH.hzo
    have h2 : O'.residue ⟨_, memO' EH hG₂⟩ ≠ 0 := by rw [hres'G₂]; exact hcbar'
    have h3 : 1 ≤ xo.ord (O.residue ⟨_, memO EH hG₂⟩) := by
      rw [hresG₂, xo.ord_mul hcbar EH.hzo, ord_algebraMap, EH.hzo1]
      norm_num
    have h4 : 0 ≤ xo'.ord (O'.residue ⟨_, memO' EH hG₂⟩) := by
      rw [hres'G₂, ord_algebraMap]
    obtain ⟨P₀, hP₀, hzero⟩ := exists_evalAt_eq_zero EH hG₂ h1 h2 h3 h4
    have hr0 := EH.hrat P₀ hP₀
    obtain ⟨hzA, hzm⟩ := EH.hzm P₀ hP₀

    have hval : P₀.evalAt G = -((a : L) * (1 + P₀.evalAt z)) := by
      rw [evalAt_add_of_mem P₀ hr0 (memPl EH hG₁ hP₀) (memPl EH haz hP₀), hvalG₁ P₀ hP₀,
        P₀.evalAt_mul_of_mem hr0 (P₀.algebraMap_mem' _) (memPl EH EH.hz hP₀), Place.evalAt_algebraMap_eq] at hzero
      linear_combination hzero
    apply no_unit_value EH hG hG' hGo hP₀
    have : (⟨P₀.evalAt G, EH.hval G hG P₀ hP₀⟩ : ↥A) = -(a * (1 + ⟨P₀.evalAt z, hzA⟩)) := Subtype.ext (by
      simpa using hval)
    rw [this]
    exact (haU.mul (isUnit_one_add_of_mem_maximalIdeal' _ hzm)).neg
  ·
    have h1 : O.residue ⟨_, memO EH hG₁⟩ ≠ 0 := by rw [hresG₁]; exact hc
    have h2 : O'.residue ⟨_, memO' EH hG₁⟩ ≠ 0 := by rw [hres'G₁]; exact hcbar'
    have h3 : 1 ≤ xo.ord (O.residue ⟨_, memO EH hG₁⟩) := by
      rw [hresG₁]
      have hmem : ρ + algebraMap (ResidueField A) Fb (IsLocalRing.residue (↥A) a) ∈ xo.toValuationSubring :=
        add_mem hρmem (xo.algebraMap_mem' _)
      refine one_le_ord_of_not_isUnit xo hmem hc ?_
      rw [← evalAt_eq_zero_iff_not_isUnit xo EH.hxr hmem, evalAt_add_of_mem xo EH.hxr hρmem (xo.algebraMap_mem' _),
        Place.evalAt_algebraMap_eq, ha, add_neg_cancel]
    have h4 : 0 ≤ xo'.ord (O'.residue ⟨_, memO' EH hG₁⟩) := by
      rw [hres'G₁, ord_algebraMap]
    obtain ⟨P₀, hP₀, hzero⟩ := exists_evalAt_eq_zero EH hG₁ h1 h2 h3 h4
    have hval : P₀.evalAt G = -(a : L) := by
      rw [hvalG₁ P₀ hP₀] at hzero
      linear_combination hzero
    apply no_unit_value EH hG hG' hGo hP₀
    have : (⟨P₀.evalAt G, EH.hval G hG P₀ hP₀⟩ : ↥A) = -a := Subtype.ext (by simpa using hval)
    rw [this]
    exact haU.neg

private theorem values_isUnit {g : F} (hgO : g ∈ O.integers) (hgu : IsUnit (⟨g, hgO⟩ : O.integers))
    (hg0 : xo.ord (O.residue ⟨g, hgO⟩) = 0) (hgS : ∀ P ∈ S, P.ord g = 0) {P : Place L F} (hP : P ∈ S) :
    ∃ h : P.evalAt g ∈ A, IsUnit (⟨_, h⟩ : ↥A) := by
  have hgres : O.residue ⟨g, hgO⟩ ≠ 0 := chart_residue_ne_zero_of_isUnit O hgu
  have hg_ne : g ≠ 0 := vsub_ne_zero_of_isUnit _ hgO hgu
  have hginvO : g⁻¹ ∈ O.integers := chart_inv_mem O hgO hgu
  have hgP : ∀ Q ∈ S, g ∈ Q.toValuationSubring := fun Q hQ =>
    Place.mem_toValuationSubring_of_ord_nonneg_alt Q hg_ne (by rw [hgS Q hQ])
  have hgPu : ∀ (Q : Place L F) (hQ : Q ∈ S), IsUnit (⟨g, hgP Q hQ⟩ : Q.toValuationSubring) := fun Q hQ =>
    (isUnit_iff_ord_eq_zero Q (hgP Q hQ) hg_ne).mpr (hgS Q hQ)
  have hginvP : ∀ Q ∈ S, g⁻¹ ∈ Q.toValuationSubring := fun Q hQ => vsub_inv_mem _ _ (hgPu Q hQ)
  obtain ⟨d, hdg, hdres⟩ := O'.exists_smul_mem g hg_ne
  have hdgu : IsUnit (⟨d • g, hdg⟩ : O'.integers) := chart_isUnit_of_residue_ne_zero O' hdres
  have hd0 : d ≠ 0 := chart_smul_const_ne_zero O' hdg hdres
  have hdF0 : algebraMap L F d ≠ 0 := (map_ne_zero _).mpr hd0
  have hginv_eq : g⁻¹ = algebraMap L F d * (d • g)⁻¹ := by
    rw [Algebra.smul_def, mul_inv, ← mul_assoc, mul_inv_cancel₀ hdF0, one_mul]
  have hg_eq : g = algebraMap L F d⁻¹ * (d • g) := by
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd0, map_one, one_mul]
  by_cases hdA : d ∈ A
  · have hginvO' : g⁻¹ ∈ O'.integers := by
      rw [hginv_eq]; exact mul_mem ((O'.algebraMap_mem_iff _).mpr hdA) (chart_inv_mem O' hdg hdgu)
    by_cases hdu : IsUnit (⟨d, hdA⟩ : ↥A)
    ·
      have hdinvA : d⁻¹ ∈ A := vsub_inv_mem A hdA hdu
      have hgO' : g ∈ O'.integers := by
        rw [hg_eq]; exact mul_mem ((O'.algebraMap_mem_iff _).mpr hdinvA) hdg
      have hg𝒩 : g ∈ 𝒩 := (EH.h𝒩 g).2 ⟨hgO, hgO', hgP⟩
      have hginv𝒩 : g⁻¹ ∈ 𝒩 := (EH.h𝒩 g⁻¹).2 ⟨hginvO, hginvO', hginvP⟩
      have h1 := EH.hval g hg𝒩 P hP
      have h2 := EH.hval g⁻¹ hginv𝒩 P hP
      refine ⟨h1, isUnit_iff_exists_inv.mpr ⟨⟨_, h2⟩, Subtype.ext ?_⟩⟩
      show P.evalAt g * P.evalAt g⁻¹ = 1
      rw [← P.evalAt_mul_of_mem (EH.hrat P hP) (hgP P hP) (hginvP P hP), mul_inv_cancel₀ hg_ne,
        Place.evalAt_one]
    ·
      exfalso
      have hdm : (⟨d, hdA⟩ : ↥A) ∈ maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr hdu
      have hres' : O'.residue ⟨g⁻¹, hginvO'⟩ = 0 := by
        have : (⟨g⁻¹, hginvO'⟩ : O'.integers) =
            ⟨algebraMap L F ((⟨d, hdA⟩ : ↥A) : L), chart_algebraMap_mem O' ⟨d, hdA⟩⟩ *
              ⟨(d • g)⁻¹, chart_inv_mem O' hdg hdgu⟩ := Subtype.ext hginv_eq
        rw [this, map_mul, chart_residue_const, (IsLocalRing.residue_eq_zero_iff _).mpr hdm, map_zero, zero_mul]
      have hginv𝒩 : g⁻¹ ∈ 𝒩 := (EH.h𝒩 _).2 ⟨hginvO, hginvO', hginvP⟩
      refine branch_cross EH hginv𝒩 hres' ?_ ?_ (fun Q hQ => by rw [Place.ord_inv, hgS Q hQ, neg_zero])
      · rw [chart_residue_inv O hgO hgu]; exact inv_ne_zero hgres
      · rw [chart_residue_inv O hgO hgu, Place.ord_inv, hg0, neg_zero]
  ·
    exfalso
    have hdinvA : d⁻¹ ∈ A := (A.mem_or_inv_mem d).resolve_left hdA
    have hdinvm : (⟨d⁻¹, hdinvA⟩ : ↥A) ∈ maximalIdeal ↥A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply hdA
      have := vsub_inv_mem A hdinvA hu
      rwa [inv_inv] at this
    have hgO' : g ∈ O'.integers := by
      rw [hg_eq]; exact mul_mem ((O'.algebraMap_mem_iff _).mpr hdinvA) hdg
    have hres' : O'.residue ⟨g, hgO'⟩ = 0 := by
      have : (⟨g, hgO'⟩ : O'.integers) =
          ⟨algebraMap L F ((⟨d⁻¹, hdinvA⟩ : ↥A) : L), chart_algebraMap_mem O' ⟨d⁻¹, hdinvA⟩⟩ * ⟨d • g, hdg⟩ :=
        Subtype.ext hg_eq
      rw [this, map_mul, chart_residue_const, (IsLocalRing.residue_eq_zero_iff _).mpr hdinvm, map_zero, zero_mul]
    have hg𝒩 : g ∈ 𝒩 := (EH.h𝒩 g).2 ⟨hgO, hgO', hgP⟩
    exact branch_cross EH hg𝒩 hres' hgres hg0 hgS

private theorem slope_law {f : F} (hf : f ∈ O.integers) (hfres : O.residue ⟨f, hf⟩ ≠ 0) (hfS : ∀ P ∈ S, P.ord f = 0)
    {P : Place L F} (hP : P ∈ S) :
    ∃ h : P.evalAt f * (P.evalAt z) ^ (-(xo.ord (O.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A) := by
  set m := xo.ord (O.residue ⟨f, hf⟩) with hm
  have hzO := memO EH EH.hz
  have hzu := z_isUnit_O EH
  have hz0 := z_ne_zero' EH
  have hf0 : f ≠ 0 := vsub_ne_zero_of_isUnit _ hf (chart_isUnit_of_residue_ne_zero O hfres)
  have hzmO : z ^ (-m) ∈ O.integers := chart_zpow_mem O hzO hzu (-m)
  have hg : f * z ^ (-m) ∈ O.integers := mul_mem hf hzmO
  have hgres : O.residue ⟨f * z ^ (-m), hg⟩ = O.residue ⟨f, hf⟩ * (O.residue ⟨z, hzO⟩) ^ (-m) := by
    rw [show (⟨f * z ^ (-m), hg⟩ : O.integers) = ⟨f, hf⟩ * ⟨z ^ (-m), hzmO⟩ from rfl, map_mul,
      chart_residue_zpow O hzO hzu]
  have hgres_ne : O.residue ⟨_, hg⟩ ≠ 0 := by
    rw [hgres]; exact mul_ne_zero hfres (zpow_ne_zero _ EH.hzo)
  have hgu : IsUnit (⟨_, hg⟩ : O.integers) := chart_isUnit_of_residue_ne_zero O hgres_ne
  have hg0 : xo.ord (O.residue ⟨_, hg⟩) = 0 := by
    rw [hgres, xo.ord_mul hfres (zpow_ne_zero _ EH.hzo), xo.ord_zpow, EH.hzo1, ← hm]; ring
  have hgS : ∀ Q ∈ S, Q.ord (f * z ^ (-m)) = 0 := fun Q hQ => by
    rw [Q.ord_mul hf0 (zpow_ne_zero _ hz0), Q.ord_zpow, hfS Q hQ, ord_z_eq_zero EH hQ]; ring
  obtain ⟨hA, hU⟩ := values_isUnit EH hg hgu hg0 hgS hP
  refine isUnit_transfer A ?_ hA hU
  have hfP : f ∈ P.toValuationSubring := Place.mem_toValuationSubring_of_ord_nonneg_alt P hf0 (by rw [hfS P hP])
  rw [P.evalAt_mul_of_mem (EH.hrat P hP) hfP
      (zpow_mem_of_isUnit P (memPl EH EH.hz hP) (z_isUnit_P EH hP) _),
    evalAt_zpow_of_isUnit P (EH.hrat P hP) (memPl EH EH.hz hP) (z_isUnit_P EH hP)]

private theorem unit_principle {f : F} (hf0 : f ≠ 0) (hfS : ∀ P ∈ S, P.ord f = 0) :
    ∃ (m : ℤ) (c : L), c ≠ 0 ∧
      ∀ P ∈ S, ∃ h : P.evalAt f * c⁻¹ * (P.evalAt z) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : ↥A) := by
  obtain ⟨d, hdf, hdres⟩ := O.exists_smul_mem f hf0
  have hd0 : d ≠ 0 := chart_smul_const_ne_zero O hdf hdres
  refine ⟨xo.ord (O.residue ⟨d • f, hdf⟩), d⁻¹, inv_ne_zero hd0, fun P hP => ?_⟩
  have hdfS : ∀ Q ∈ S, Q.ord (d • f) = 0 := fun Q hQ => by rw [ord_smul_const Q hd0 hf0, hfS Q hQ]
  obtain ⟨hA, hU⟩ := slope_law EH hdf hdres hdfS hP
  refine isUnit_transfer A ?_ hA hU
  have hfP : f ∈ P.toValuationSubring := Place.mem_toValuationSubring_of_ord_nonneg_alt P hf0 (by rw [hfS P hP])
  have hev : P.evalAt (d • f) = P.evalAt f * d := by
    rw [Algebra.smul_def, P.evalAt_mul_of_mem (EH.hrat P hP) (P.algebraMap_mem' d) hfP,
      Place.evalAt_algebraMap_eq, mul_comm d]
  rw [inv_inv, hev]

end End

section Frame

private structure NodeHyp {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (x₁ : Place (ResidueField A) Fbar₁) (x₂ : Place (ResidueField A) Fbar₂)
    (S : Set (Place L F)) (𝒩 : Subring F) (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀]
    (C : Subring L) (ϖ : ↥C)
    {W : Type*} [CommRing W] (π : W) (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) (E : ℕ)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (x y : ↥𝒩₀) (E₀ : ℕ) (u : ↥𝒩₀) : Prop where
  hrat : ∀ P ∈ S, P.IsRational
  h𝒩 : ∀ f : F, f ∈ 𝒩 ↔ f ∈ R₁.integers ∧ f ∈ R₂.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring
  hval : ∀ f ∈ 𝒩, ∀ P ∈ S, P.evalAt f ∈ A
  hreg : ∀ (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers), f ∈ 𝒩 →
    (R₁.residue ⟨f, h₁⟩ ≠ 0 → 0 ≤ x₁.ord (R₁.residue ⟨f, h₁⟩)) ∧
    (R₂.residue ⟨f, h₂⟩ ≠ 0 → 0 ≤ x₂.ord (R₂.residue ⟨f, h₂⟩))
  hord : ∀ (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers),
    R₁.residue ⟨f, h₁⟩ ≠ 0 → R₂.residue ⟨f, h₂⟩ ≠ 0 →
      {P : Place L F | P ∈ S ∧ P.ord f ≠ 0}.Finite ∧
      ∑ᶠ P ∈ S, P.ord f = x₁.ord (R₁.residue ⟨f, h₁⟩) + x₂.ord (R₂.residue ⟨f, h₂⟩)
  h𝒩₀ : 𝒩₀ ≤ 𝒩
  hS : ∀ P : Place L F, P ∈ S ↔
    (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
    (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)
  hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
    (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F)
  hC : ∀ c : L, c ∈ C → c ∈ A
  hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀
  hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d'
  hϖ0 : ((ϖ : ↥C) : L) ≠ 0
  hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩)
  hπ : Irreducible π
  hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩
  hE : 1 ≤ E
  hconst : ∀ o : W, ι (σ o) = const (π ^ E) o
  hres₁ : ∀ (f : ↥𝒩₀) (n : ℕ), R₁.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ f.2)).1⟩ ≠ 0 →
    x₁.ord (R₁.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ f.2)).1⟩) = (n : ℤ) →
      ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
        ι (algebraMap ↥𝒩₀ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)}
  hres₂ : ∀ (f : ↥𝒩₀) (n : ℕ), R₂.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ f.2)).2.1⟩ ≠ 0 →
    x₂.ord (R₂.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ f.2)).2.1⟩) = (n : ℤ) →
      ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
        ι (algebraMap ↥𝒩₀ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)}
  x_fst : R₁.residue ⟨x, ((h𝒩 x).1 (h𝒩₀ x.2)).1⟩ = 0
  x_snd : x₂.ord (R₂.residue ⟨x, ((h𝒩 x).1 (h𝒩₀ x.2)).2.1⟩) = 1
  y_snd : R₂.residue ⟨y, ((h𝒩 y).1 (h𝒩₀ y.2)).2.1⟩ = 0
  y_fst : x₁.ord (R₁.residue ⟨y, ((h𝒩 y).1 (h𝒩₀ y.2)).1⟩) = 1
  hu : IsUnit u
  hxy : x * y = ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ ^ E₀ * u
  hx₁r : x₁.IsRational
  hx₂r : x₂.IsRational
  hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField A) Fbar₂]
    {R₁ : RegularProlongation A F Fbar₁} {R₂ : RegularProlongation A F Fbar₂}
    {x₁ : Place (ResidueField A) Fbar₁} {x₂ : Place (ResidueField A) Fbar₂}
    {S : Set (Place L F)} {𝒩 𝒩₀ : Subring F} [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
    {C : Subring L} {ϖ : ↥C}
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    {π : W} {σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀} {E : ℕ}
    {ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E)}
    {x y : ↥𝒩₀} {E₀ : ℕ} {u : ↥𝒩₀}
    (H : NodeHyp A R₁ R₂ x₁ x₂ S 𝒩 𝒩₀ C ϖ π σ E ι x y E₀ u)

set_option quotPrecheck false in
local notation "ϖL" => ((ϖ : ↥C) : L)
set_option quotPrecheck false in
local notation "ϖA" => (⟨((ϖ : ↥C) : L), H.hC ϖ ϖ.2⟩ : ↥A)
set_option quotPrecheck false in
local notation "ϖN" => (⟨algebraMap L F ((ϖ : ↥C) : L), H.hCmem ϖ ϖ.2⟩ : ↥𝒩₀)

include H

private theorem memR₁ (f : ↥𝒩₀) : (f : F) ∈ R₁.integers := ((H.h𝒩 f).1 (H.h𝒩₀ f.2)).1
private theorem memR₂ (f : ↥𝒩₀) : (f : F) ∈ R₂.integers := ((H.h𝒩 f).1 (H.h𝒩₀ f.2)).2.1
private theorem memP (f : ↥𝒩₀) {P : Place L F} (hP : P ∈ S) : (f : F) ∈ P.toValuationSubring :=
  ((H.hS P).1 hP).1 f f.2

private theorem isUnit_R₁_of_isUnit {g : ↥𝒩₀} (hg : IsUnit g) : IsUnit (⟨(g : F), memR₁ H g⟩ : R₁.integers) := by
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hg
  exact isUnit_iff_exists_inv.mpr ⟨⟨(w : F), memR₁ H w⟩, Subtype.ext (by
    have h' := congrArg Subtype.val hw
    simpa using h')⟩

private theorem isUnit_R₂_of_isUnit {g : ↥𝒩₀} (hg : IsUnit g) : IsUnit (⟨(g : F), memR₂ H g⟩ : R₂.integers) := by
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hg
  exact isUnit_iff_exists_inv.mpr ⟨⟨(w : F), memR₂ H w⟩, Subtype.ext (by
    have h' := congrArg Subtype.val hw
    simpa using h')⟩

private theorem isUnit_P_of_isUnit {g : ↥𝒩₀} (hg : IsUnit g) {P : Place L F} (hP : P ∈ S) :
    IsUnit (⟨(g : F), memP H g hP⟩ : P.toValuationSubring) := by
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hg
  exact isUnit_iff_exists_inv.mpr ⟨⟨(w : F), memP H w hP⟩, Subtype.ext (by
    have h' := congrArg Subtype.val hw
    simpa using h')⟩

private theorem ϖA_mem : ϖA ∈ maximalIdeal ↥A := by
  rw [← IsLocalRing.residue_eq_zero_iff]
  exact (H.hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩

private theorem ϖA_ne_zero : ϖA ≠ 0 := fun h => H.hϖ0 (by
  have h' := congrArg Subtype.val h
  simpa using h')

private theorem not_isUnit_ϖN : ¬ IsUnit ϖN := fun h =>
  vsub_not_isUnit_algebraMap A R₁.integers R₁.algebraMap_mem_iff ϖA (ϖA_mem H) (isUnit_R₁_of_isUnit H h)

private theorem not_isUnit_x : ¬ IsUnit x := fun h =>
  chart_residue_ne_zero_of_isUnit R₁ (isUnit_R₁_of_isUnit H h) H.x_fst

private theorem not_isUnit_y : ¬ IsUnit y := fun h =>
  chart_residue_ne_zero_of_isUnit R₂ (isUnit_R₂_of_isUnit H h) H.y_snd

private theorem one_le_E₀ : 1 ≤ E₀ := by
  rcases Nat.eq_zero_or_pos E₀ with h0 | hpos
  · exfalso
    subst h0
    have hxy := H.hxy
    simp only [pow_zero, one_mul] at hxy
    exact not_isUnit_x H (isUnit_of_mul_isUnit_left (hxy ▸ H.hu))
  · exact hpos

private theorem isUnit_evalAt_of_isUnit {g : ↥𝒩₀} (hg : IsUnit g) {P : Place L F} (hP : P ∈ S) :
    ∃ h : P.evalAt (g : F) ∈ A, IsUnit (⟨_, h⟩ : ↥A) := by
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hg
  have hgA := H.hval _ (H.h𝒩₀ g.2) P hP
  have hwA := H.hval _ (H.h𝒩₀ w.2) P hP
  refine ⟨hgA, isUnit_iff_exists_inv.mpr ⟨⟨_, hwA⟩, Subtype.ext ?_⟩⟩
  show P.evalAt (g : F) * P.evalAt (w : F) = 1
  rw [← P.evalAt_mul_of_mem (H.hrat P hP) (memP H g hP) (memP H w hP), ← Subring.coe_mul, hw]
  simp [Place.evalAt_one]

private theorem evalAt_mem_maximalIdeal_of_not_isUnit {g : ↥𝒩₀} (hg : ¬ IsUnit g) {P : Place L F} (hP : P ∈ S) :
    ∃ h : P.evalAt (g : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A :=
  ((H.hS P).1 hP).2 g hg

private theorem coe_ϖN_pow (n : ℕ) : ((ϖN ^ n : ↥𝒩₀) : F) = algebraMap L F (ϖL ^ n) := by
  simp [map_pow]

private theorem evalAt_x_mul_evalAt_y {P : Place L F} (hP : P ∈ S) :
    P.evalAt (x : F) * P.evalAt (y : F) = ϖL ^ E₀ * P.evalAt (u : F) := by
  have hr := H.hrat P hP
  rw [← P.evalAt_mul_of_mem hr (memP H x hP) (memP H y hP), ← Subring.coe_mul, H.hxy, Subring.coe_mul,
    P.evalAt_mul_of_mem hr (memP H _ hP) (memP H u hP), coe_ϖN_pow H, Place.evalAt_algebraMap_eq]

private theorem evalAt_u_ne_zero {P : Place L F} (hP : P ∈ S) : P.evalAt (u : F) ≠ 0 := by
  obtain ⟨huA, huU⟩ := isUnit_evalAt_of_isUnit H H.hu hP
  intro h'
  have : (⟨P.evalAt (u : F), huA⟩ : ↥A) = 0 := Subtype.ext h'
  rw [this] at huU
  exact not_isUnit_zero huU

private theorem evalAt_y_ne_zero {P : Place L F} (hP : P ∈ S) : P.evalAt (y : F) ≠ 0 := by
  intro h0
  have h := evalAt_x_mul_evalAt_y H hP
  rw [h0, mul_zero] at h
  exact mul_ne_zero (pow_ne_zero _ H.hϖ0) (evalAt_u_ne_zero H hP) h.symm

private theorem evalAt_x_ne_zero {P : Place L F} (hP : P ∈ S) : P.evalAt (x : F) ≠ 0 := by
  intro h0
  have h := evalAt_x_mul_evalAt_y H hP
  rw [h0, zero_mul] at h
  exact mul_ne_zero (pow_ne_zero _ H.hϖ0) (evalAt_u_ne_zero H hP) h.symm

private theorem y_ne_zero : (y : F) ≠ 0 := fun h => by
  have hy0 : y = 0 := Subtype.ext h
  have h1 : ϖN ^ E₀ * u = 0 := by rw [← H.hxy, hy0, mul_zero]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact H.hϖ0 (by
      have h3 := congrArg (fun t : ↥𝒩₀ => (t : F)) h2
      simp only [SubmonoidClass.coe_pow, ZeroMemClass.coe_zero, map_pow] at h3
      rw [← map_pow, map_eq_zero] at h3
      exact (pow_eq_zero_iff (Nat.one_le_iff_ne_zero.mp (one_le_E₀ H))).mp h3)
  · exact not_isUnit_zero (h2 ▸ H.hu)

private theorem x_ne_zero : (x : F) ≠ 0 := fun h => by
  have hx0 : x = 0 := Subtype.ext h
  have h1 : ϖN ^ E₀ * u = 0 := by rw [← H.hxy, hx0, zero_mul]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact H.hϖ0 (by
      have h3 := congrArg (fun t : ↥𝒩₀ => (t : F)) h2
      simp only [SubmonoidClass.coe_pow, ZeroMemClass.coe_zero, map_pow] at h3
      rw [← map_pow, map_eq_zero] at h3
      exact (pow_eq_zero_iff (Nat.one_le_iff_ne_zero.mp (one_le_E₀ H))).mp h3)
  · exact not_isUnit_zero (h2 ▸ H.hu)

private theorem modulus_mem : ∃ h : ϖL ^ E₀ ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A := by
  refine ⟨pow_mem (H.hC ϖ ϖ.2) E₀, ?_⟩
  have : (⟨ϖL ^ E₀, pow_mem (H.hC ϖ ϖ.2) E₀⟩ : ↥A) = ϖA ^ E₀ := Subtype.ext (by simp)
  rw [this]
  exact Ideal.pow_mem_of_mem _ (ϖA_mem H) _ (one_le_E₀ H)

private theorem mem_dom_clause {P : Place L F} (hP : P ∈ S) :
    P.IsRational ∧ (y : F) ∈ P.toValuationSubring ∧
    (∃ h : P.evalAt (y : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A) ∧ P.evalAt (y : F) ≠ 0 ∧
    ∃ m ∈ maximalIdeal ↥A, (ϖL ^ E₀ : L) = P.evalAt (y : F) * (m : L) := by
  refine ⟨H.hrat P hP, memP H y hP, evalAt_mem_maximalIdeal_of_not_isUnit H (not_isUnit_y H) hP,
    evalAt_y_ne_zero H hP, ?_⟩
  obtain ⟨hxA, hxm⟩ := evalAt_mem_maximalIdeal_of_not_isUnit H (not_isUnit_x H) hP
  obtain ⟨huA, huU⟩ := isUnit_evalAt_of_isUnit H H.hu hP
  obtain ⟨w, hw⟩ := huU
  refine ⟨⟨P.evalAt (x : F), hxA⟩ * ↑w⁻¹, Ideal.mul_mem_right _ _ hxm, ?_⟩
  have h := evalAt_x_mul_evalAt_y H hP
  have hwv : ((w⁻¹ : (↥A)ˣ) : ↥A) * (⟨P.evalAt (u : F), huA⟩ : ↥A) = 1 := by rw [← hw, Units.inv_mul]
  have hwv' : (((w⁻¹ : (↥A)ˣ) : ↥A) : L) * P.evalAt (u : F) = 1 := by
    have := congrArg Subtype.val hwv
    simpa using this
  rw [MulMemClass.coe_mul]
  calc (ϖL ^ E₀ : L) = ϖL ^ E₀ * ((((w⁻¹ : (↥A)ˣ) : ↥A) : L) * P.evalAt (u : F)) := by rw [hwv', mul_one]
    _ = (P.evalAt (x : F) * P.evalAt (y : F)) * (((w⁻¹ : (↥A)ˣ) : ↥A) : L) := by rw [h]; ring
    _ = P.evalAt (y : F) * (P.evalAt (x : F) * (((w⁻¹ : (↥A)ˣ) : ↥A) : L)) := by ring

private theorem residue₁_y_ne_zero : R₁.residue ⟨(y : F), memR₁ H y⟩ ≠ 0 := fun h => by
  have h1 := H.y_fst
  rw [h, Place.ord_zero] at h1
  exact zero_ne_one h1

private theorem residue₂_x_ne_zero : R₂.residue ⟨(x : F), memR₂ H x⟩ ≠ 0 := fun h => by
  have h1 := H.x_snd
  rw [h, Place.ord_zero] at h1
  exact zero_ne_one h1

private theorem endHyp₁ : EndHyp R₁ R₂ x₁ x₂ S 𝒩 ((y : ↥𝒩₀) : F) :=
  { hrat := H.hrat
    h𝒩 := H.h𝒩
    hval := H.hval
    hreg := fun f h hf hne => (H.hreg f h ((H.h𝒩 f).1 hf).2.1 hf).1 hne
    hord := H.hord
    hxr := H.hx₁r
    hrk := H.hrk
    hz := H.h𝒩₀ y.2
    hz' := H.y_snd
    hzo := residue₁_y_ne_zero H
    hzo1 := H.y_fst
    hzm := fun P hP => evalAt_mem_maximalIdeal_of_not_isUnit H (not_isUnit_y H) hP
    hz0 := fun P hP => evalAt_y_ne_zero H hP }

private theorem ord_residue₂_of_isUnit {g : ↥𝒩₀} (hg : IsUnit g) : x₂.ord (R₂.residue ⟨(g : F), memR₂ H g⟩) = 0 := by
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hg
  have h1 : R₂.residue ⟨(g : F), memR₂ H g⟩ * R₂.residue ⟨(w : F), memR₂ H w⟩ = 1 := by
    rw [← chart_residue_mul, ← chart_residue_one R₂]
    congr 1
    exact Subtype.ext (by
      have h' := congrArg Subtype.val hw
      simpa using h')
  have hg0 : R₂.residue ⟨(g : F), memR₂ H g⟩ ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have hw0 : R₂.residue ⟨(w : F), memR₂ H w⟩ ≠ 0 := right_ne_zero_of_mul_eq_one h1
  have hsum : x₂.ord (R₂.residue ⟨(g : F), memR₂ H g⟩) + x₂.ord (R₂.residue ⟨(w : F), memR₂ H w⟩) = 0 := by
    rw [← x₂.ord_mul hg0 hw0, h1, Place.ord_one]
  have h0g := (H.hreg _ (memR₁ H g) (memR₂ H g) (H.h𝒩₀ g.2)).2 hg0
  have h0w := (H.hreg _ (memR₁ H w) (memR₂ H w) (H.h𝒩₀ w.2)).2 hw0
  omega

private theorem residue₁_xw (w : ↥𝒩₀) : R₁.residue ⟨((x * w : ↥𝒩₀) : F), memR₁ H (x * w)⟩ = 0 := by
  rw [show (⟨((x * w : ↥𝒩₀) : F), memR₁ H (x * w)⟩ : R₁.integers) = ⟨(x : F), memR₁ H x⟩ * ⟨(w : F), memR₁ H w⟩
    from Subtype.ext (Subring.coe_mul _ _ _), map_mul, H.x_fst, zero_mul]

private theorem residue₂_xw (w : ↥𝒩₀) : R₂.residue ⟨((x * w : ↥𝒩₀) : F), memR₂ H (x * w)⟩ =
    R₂.residue ⟨(x : F), memR₂ H x⟩ * R₂.residue ⟨(w : F), memR₂ H w⟩ := by
  rw [show (⟨((x * w : ↥𝒩₀) : F), memR₂ H (x * w)⟩ : R₂.integers) = ⟨(x : F), memR₂ H x⟩ * ⟨(w : F), memR₂ H w⟩
    from Subtype.ext (Subring.coe_mul _ _ _), map_mul]

private theorem endHyp₂ {w : ↥𝒩₀} (hw : IsUnit w) : EndHyp R₂ R₁ x₂ x₁ S 𝒩 ((x * w : ↥𝒩₀) : F) :=
  { hrat := H.hrat
    h𝒩 := fun f => (H.h𝒩 f).trans ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩
    hval := H.hval
    hreg := fun f h hf hne => (H.hreg f ((H.h𝒩 f).1 hf).1 h hf).2 hne
    hord := fun f h h' hne hne' => by
      obtain ⟨hfin, hsum⟩ := H.hord f h' h hne' hne
      exact ⟨hfin, by rw [hsum, add_comm]⟩
    hxr := H.hx₂r
    hrk := H.hrk
    hz := H.h𝒩₀ (x * w).2
    hz' := residue₁_xw H w
    hzo := by
      rw [residue₂_xw H w]
      exact mul_ne_zero (residue₂_x_ne_zero H) (chart_residue_ne_zero_of_isUnit R₂ (isUnit_R₂_of_isUnit H hw))
    hzo1 := by
      rw [residue₂_xw H w, x₂.ord_mul (residue₂_x_ne_zero H)
        (chart_residue_ne_zero_of_isUnit R₂ (isUnit_R₂_of_isUnit H hw)), H.x_snd, ord_residue₂_of_isUnit H hw]
      norm_num
    hzm := fun P hP => evalAt_mem_maximalIdeal_of_not_isUnit H
      (fun h => not_isUnit_x H (isUnit_of_mul_isUnit_left h)) hP
    hz0 := fun P hP => by
      rw [Subring.coe_mul, P.evalAt_mul_of_mem (H.hrat P hP) (memP H x hP) (memP H w hP)]
      obtain ⟨hwA, hwU⟩ := isUnit_evalAt_of_isUnit H hw hP
      refine mul_ne_zero (evalAt_x_ne_zero H hP) fun h0 => ?_
      have : (⟨P.evalAt (w : F), hwA⟩ : ↥A) = 0 := Subtype.ext h0
      rw [this] at hwU
      exact not_isUnit_zero hwU }

private theorem main
    (hE : ∀ c : ↥A, c ∈ maximalIdeal ↥A → (c : L) ≠ 0 →
      (∃ m ∈ maximalIdeal ↥A, (ϖL ^ E₀) = (c : L) * (m : L)) → ∃ P ∈ S, P.evalAt ((y : ↥𝒩₀) : F) = (c : L))
    (hU : ∀ P Q : Place L F, P ∈ S → Q ∈ S →
      P.evalAt ((y : ↥𝒩₀) : F) = Q.evalAt ((y : ↥𝒩₀) : F) → P = Q)
    (hZ : ∀ P : Place L F, P ∈ S →
      P.ord (((y : ↥𝒩₀) : F) - algebraMap L F (P.evalAt ((y : ↥𝒩₀) : F))) = 1) :
    ∃ An An' : Annulus A F,
      (∀ P : Place L F, P ∈ An.dom ↔ P ∈ S) ∧
      An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
      ((An.modulus : L) = ϖL ^ E₀) ∧ ((An.modulus : L) ≠ 0) ∧
      An.param = ((y : ↥𝒩₀) : F) ∧
      An'.param * An.param = algebraMap L F (An.modulus : L) ∧
      (∃ hz : An.param ∈ R₁.integers, x₁.ord (R₁.residue ⟨An.param, hz⟩) = 1 ∧
        ∀ (f : F) (hf : f ∈ R₁.integers), R₁.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord f = 0) →
          ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(x₁.ord (R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ hz : An'.param ∈ R₂.integers, x₂.ord (R₂.residue ⟨An'.param, hz⟩) = 1 ∧
        ∀ (f : F) (hf : f ∈ R₂.integers), R₂.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An'.dom, P.ord f = 0) →
          ∀ P ∈ An'.dom,
            ∃ h : P.evalAt f * (P.evalAt An'.param) ^ (-(x₂.ord (R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) := by
  obtain ⟨hmodA, hmodm⟩ := modulus_mem H
  have hmod0 : (ϖL ^ E₀ : L) ≠ 0 := pow_ne_zero _ H.hϖ0

  obtain ⟨uu, huu⟩ := H.hu
  set w : ↥𝒩₀ := ((uu⁻¹ : (↥𝒩₀)ˣ) : ↥𝒩₀) with hwdef
  have hw : IsUnit w := (uu⁻¹).isUnit
  have huw : u * w = 1 := by rw [← huu, hwdef, Units.mul_inv]
  have hxwy : (x * w) * y = ϖN ^ E₀ := by
    rw [mul_assoc, mul_comm w y, ← mul_assoc, H.hxy, mul_assoc, huw, mul_one]
  have hxwyF : ((x * w : ↥𝒩₀) : F) * ((y : ↥𝒩₀) : F) = algebraMap L F (ϖL ^ E₀) := by
    rw [← Subring.coe_mul, hxwy, coe_ϖN_pow H]
  have E₁ := endHyp₁ H
  have E₂ := endHyp₂ H hw

  have hev : ∀ P ∈ S, P.evalAt ((x * w : ↥𝒩₀) : F) * P.evalAt ((y : ↥𝒩₀) : F) = ϖL ^ E₀ := fun P hP => by
    rw [← P.evalAt_mul_of_mem (H.hrat P hP) (memP H _ hP) (memP H y hP), hxwyF, Place.evalAt_algebraMap_eq]

  let An : Annulus A F :=
  { dom := S
    param := ((y : ↥𝒩₀) : F)
    modulus := ⟨ϖL ^ E₀, hmodA⟩
    modulus_mem := hmodm
    mem_dom := fun P hP => mem_dom_clause H hP
    existsUnique_evalAt_eq := fun c hc hc0 hdiv => by
      obtain ⟨P, hP, hPc⟩ := hE c hc hc0 hdiv
      exact ⟨P, ⟨hP, hPc⟩, fun Q hQ => hU Q P hQ.1 hP (hQ.2.trans hPc.symm)⟩
    ord_param_sub := fun P hP => hZ P hP
    unit_principle := fun f hf0 hfS => unit_principle E₁ hf0 hfS }

  let An' : Annulus A F :=
  { dom := S
    param := ((x * w : ↥𝒩₀) : F)
    modulus := ⟨ϖL ^ E₀, hmodA⟩
    modulus_mem := hmodm
    mem_dom := fun P hP => by
      obtain ⟨hyA, hym⟩ := evalAt_mem_maximalIdeal_of_not_isUnit H (not_isUnit_y H) hP
      exact ⟨H.hrat P hP, memP H _ hP, E₂.hzm P hP, E₂.hz0 P hP, ⟨P.evalAt ((y : ↥𝒩₀) : F), hyA⟩, hym,
        (hev P hP).symm⟩
    existsUnique_evalAt_eq := fun c hc hc0 hdiv => by
      obtain ⟨m, hm, hcm⟩ := hdiv
      have hcm : ϖL ^ E₀ = (c : L) * (m : L) := hcm
      have hm0 : (m : L) ≠ 0 := fun h => hmod0 (by rw [hcm, h, mul_zero])
      obtain ⟨P, hP, hPm⟩ := hE m hm hm0 ⟨c, hc, by rw [hcm, mul_comm]⟩
      have key : ∀ Q ∈ S, (Q.evalAt ((x * w : ↥𝒩₀) : F) = (c : L) ↔ Q.evalAt ((y : ↥𝒩₀) : F) = (m : L)) := by
        intro Q hQ
        have h := hev Q hQ
        rw [hcm] at h
        constructor
        · intro hq
          rw [hq] at h
          exact mul_left_cancel₀ hc0 h
        · intro hq
          rw [hq] at h
          exact mul_right_cancel₀ hm0 h
      refine ⟨P, ⟨hP, (key P hP).2 hPm⟩, fun Q hQ => hU Q P hQ.1 hP (((key Q hQ.1).1 hQ.2).trans hPm.symm)⟩
    ord_param_sub := fun P hP => by
      have hr := H.hrat P hP
      have hy0 := y_ne_zero H
      have hc0 := evalAt_y_ne_zero H hP
      have h1 := hZ P hP
      set c := P.evalAt ((y : ↥𝒩₀) : F) with hc
      have hsub0 : ((y : ↥𝒩₀) : F) - algebraMap L F c ≠ 0 := fun h => by
        rw [h, Place.ord_zero] at h1
        exact zero_ne_one h1

      have hxw : ((x * w : ↥𝒩₀) : F) = algebraMap L F (ϖL ^ E₀) * ((y : ↥𝒩₀) : F)⁻¹ :=
        (eq_mul_inv_iff_mul_eq₀ hy0).mpr hxwyF
      have hxwP : P.evalAt ((x * w : ↥𝒩₀) : F) = ϖL ^ E₀ * c⁻¹ :=
        (eq_mul_inv_iff_mul_eq₀ hc0).mpr (hev P hP)
      have heq : ((x * w : ↥𝒩₀) : F) - algebraMap L F (P.evalAt ((x * w : ↥𝒩₀) : F)) =
          (-(algebraMap L F (ϖL ^ E₀ * c⁻¹) * ((y : ↥𝒩₀) : F)⁻¹)) * (((y : ↥𝒩₀) : F) - algebraMap L F c) := by
        rw [hxwP, hxw, map_mul, map_inv₀]
        have hcF : algebraMap L F c ≠ 0 := (map_ne_zero _).mpr hc0
        field_simp
        ring
      rw [heq, P.ord_mul (neg_ne_zero.mpr (mul_ne_zero ((map_ne_zero _).mpr (mul_ne_zero hmod0 (inv_ne_zero hc0)))
        (inv_ne_zero hy0))) hsub0, h1, ← neg_one_mul, P.ord_mul (by norm_num) (mul_ne_zero ((map_ne_zero _).mpr
        (mul_ne_zero hmod0 (inv_ne_zero hc0))) (inv_ne_zero hy0)),
        P.ord_mul ((map_ne_zero _).mpr (mul_ne_zero hmod0 (inv_ne_zero hc0))) (inv_ne_zero hy0),
        ord_algebraMap, Place.ord_inv, ord_eq_zero_of_evalAt_ne_zero P hr (memP H y hP) hc0,
        show (-1 : F) = algebraMap L F (-1) from by rw [map_neg, map_one], ord_algebraMap]
      norm_num
    unit_principle := fun f hf0 hfS => unit_principle E₂ hf0 hfS }
  refine ⟨An, An', fun P => Iff.rfl, rfl, rfl, rfl, hmod0, rfl, hxwyF, ?_, ?_⟩
  · exact ⟨memR₁ H y, H.y_fst, fun f hf hres hfS P hP => slope_law E₁ hf hres hfS hP⟩
  · exact ⟨memR₂ H (x * w), E₂.hzo1, fun f hf hres hfS P hP => slope_law E₂ hf hres hfS hP⟩

end Frame

end AlgebraicCurve.NodeAnnulusEngine

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Annulus Annulus.IsAttached Place Place.ord Place.ord_zero Place.ord_one Place.ord_inv Place.evalAt_one Place.evalAt_ne_zero_of_ord_eq_zero Place.evalAt_algebraMap_eq Place.mem_toValuationSubring_of_ord_nonneg_alt RegularProlongation IsCurveOver NodeAnnulusEngine.exists_mem_and_evalAt_eq NodeAnnulusEngine.eq_of_mem_of_evalAt_eq NodeAnnulusEngine.ord_sub_evalAt_eq_one" end AlgebraicCurve
p2m_open_scoped "AlgebraicCurve" in
theorem AlgebraicCurve.exists_annulusPair_isAttached_of_ringEquiv_uvCrossingModel_of_nodeCoordinates
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (x₁ : Place (ResidueField A) Fbar₁) (x₂ : Place (ResidueField A) Fbar₂)

    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩 : Subring F)
    (h𝒩 : ∀ f : F, f ∈ 𝒩 ↔ f ∈ R₁.integers ∧ f ∈ R₂.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring)
    (hval : ∀ f ∈ 𝒩, ∀ P ∈ S, P.evalAt f ∈ A)

    (hreg : ∀ (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers), f ∈ 𝒩 →
      (R₁.residue ⟨f, h₁⟩ ≠ 0 → 0 ≤ x₁.ord (R₁.residue ⟨f, h₁⟩)) ∧
      (R₂.residue ⟨f, h₂⟩ ≠ 0 → 0 ≤ x₂.ord (R₂.residue ⟨f, h₂⟩)))
    (hord : ∀ (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers),
      R₁.residue ⟨f, h₁⟩ ≠ 0 → R₂.residue ⟨f, h₂⟩ ≠ 0 →
        {P : Place L F | P ∈ S ∧ P.ord f ≠ 0}.Finite ∧
        ∑ᶠ P ∈ S, P.ord f = x₁.ord (R₁.residue ⟨f, h₁⟩) + x₂.ord (R₂.residue ⟨f, h₂⟩))

    (𝒩₀ : Subring F) (h𝒩₀ : 𝒩₀ ≤ 𝒩) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]

    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))

    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))
    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)

    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)

    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)

    (hx₁r : x₁.IsRational) (hx₂r : x₂.IsRational)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))

    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (hres₁ : ∀ (f : ↥𝒩₀) (n : ℕ), R₁.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ f.2)).1⟩ ≠ 0 →
      x₁.ord (R₁.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ f.2)).1⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥𝒩₀ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hres₂ : ∀ (f : ↥𝒩₀) (n : ℕ), R₂.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ f.2)).2.1⟩ ≠ 0 →
      x₂.ord (R₂.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ f.2)).2.1⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥𝒩₀ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})

    (x y : ↥𝒩₀)
    (x_fst : R₁.residue ⟨x, ((h𝒩 x).1 (h𝒩₀ x.2)).1⟩ = 0)
    (x_snd : x₂.ord (R₂.residue ⟨x, ((h𝒩 x).1 (h𝒩₀ x.2)).2.1⟩) = 1)
    (y_snd : R₂.residue ⟨y, ((h𝒩 y).1 (h𝒩₀ y.2)).2.1⟩ = 0)
    (y_fst : x₁.ord (R₁.residue ⟨y, ((h𝒩 y).1 (h𝒩₀ y.2)).1⟩) = 1)
    (E₀ : ℕ) (u : ↥𝒩₀) (hu : IsUnit u)
    (hxy : x * y = ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ ^ E₀ * u) :
    ∃ An An' : Annulus A F,
      (∀ P : Place L F, P ∈ An.dom ↔ P ∈ S) ∧
      An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
      ((An.modulus : L) = ((ϖ : ↥C) : L) ^ E₀) ∧ ((An.modulus : L) ≠ 0) ∧
      An.param = ((y : ↥𝒩₀) : F) ∧
      An'.param * An.param = algebraMap L F (An.modulus : L) ∧

      (∃ hz : An.param ∈ R₁.integers, x₁.ord (R₁.residue ⟨An.param, hz⟩) = 1 ∧
        ∀ (f : F) (hf : f ∈ R₁.integers), R₁.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord f = 0) →
          ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(x₁.ord (R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧

      (∃ hz : An'.param ∈ R₂.integers, x₂.ord (R₂.residue ⟨An'.param, hz⟩) = 1 ∧
        ∀ (f : F) (hf : f ∈ R₂.integers), R₂.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An'.dom, P.ord f = 0) →
          ∀ P ∈ An'.dom,
            ∃ h : P.evalAt f * (P.evalAt An'.param) ^ (-(x₂.ord (R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) := by
  have H : AlgebraicCurve.NodeAnnulusEngine.NodeHyp A R₁ R₂ x₁ x₂ S 𝒩 𝒩₀ C ϖ π σ E ι x y E₀ u :=
    ⟨hrat, h𝒩, hval, hreg, hord, h𝒩₀, hS, hgen, hC, hCmem, hϖ, hϖ0, hres, hπ, hσπ, hE, hconst,
      hres₁, hres₂, x_fst, x_snd, y_snd, y_fst, hu, hxy, hx₁r, hx₂r, hrk⟩
  exact AlgebraicCurve.NodeAnnulusEngine.main H
    (AlgebraicCurve.NodeAnnulusEngine.exists_mem_and_evalAt_eq A R₁ R₂ x₁ x₂ S hrat 𝒩 h𝒩 hval hreg hord
      𝒩₀ h𝒩₀ hS hgen C hC hCmem ϖ hϖ hϖ0 halg hrk hx₁r hx₂r hres π hπ σ hσπ E hE ι hconst hres₁ hres₂ x y
      x_fst x_snd y_snd y_fst E₀ u hu hxy)
    (AlgebraicCurve.NodeAnnulusEngine.eq_of_mem_of_evalAt_eq A R₁ R₂ x₁ x₂ S hrat 𝒩 h𝒩 hval hreg hord
      𝒩₀ h𝒩₀ hS hgen C hC hCmem ϖ hϖ hϖ0 halg hrk hx₁r hx₂r hres π hπ σ hσπ E hE ι hconst hres₁ hres₂ x y
      x_fst x_snd y_snd y_fst E₀ u hu hxy)
    (AlgebraicCurve.NodeAnnulusEngine.ord_sub_evalAt_eq_one A R₁ R₂ x₁ x₂ S hrat 𝒩 h𝒩 hval hreg hord
      𝒩₀ h𝒩₀ hS hgen C hC hCmem ϖ hϖ hϖ0 halg hrk hx₁r hx₂r hres π hπ σ hσπ E hE ι hconst hres₁ hres₂ x y
      x_fst x_snd y_snd y_fst E₀ u hu hxy)

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (x₁ : Place (ResidueField A) Fbar₁) (x₂ : Place (ResidueField A) Fbar₂)

    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩 : Subring F)
    (h𝒩 : ∀ f : F, f ∈ 𝒩 ↔ f ∈ R₁.integers ∧ f ∈ R₂.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring)
    (hval : ∀ f ∈ 𝒩, ∀ P ∈ S, P.evalAt f ∈ A)

    (hreg : ∀ (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers), f ∈ 𝒩 →
      (R₁.residue ⟨f, h₁⟩ ≠ 0 → 0 ≤ x₁.ord (R₁.residue ⟨f, h₁⟩)) ∧
      (R₂.residue ⟨f, h₂⟩ ≠ 0 → 0 ≤ x₂.ord (R₂.residue ⟨f, h₂⟩)))
    (hord : ∀ (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers),
      R₁.residue ⟨f, h₁⟩ ≠ 0 → R₂.residue ⟨f, h₂⟩ ≠ 0 →
        {P : Place L F | P ∈ S ∧ P.ord f ≠ 0}.Finite ∧
        ∑ᶠ P ∈ S, P.ord f = x₁.ord (R₁.residue ⟨f, h₁⟩) + x₂.ord (R₂.residue ⟨f, h₂⟩))

    (𝒩₀ : Subring F) (h𝒩₀ : 𝒩₀ ≤ 𝒩) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]

    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))

    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))
    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)

    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)

    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)

    (hx₁r : x₁.IsRational) (hx₂r : x₂.IsRational)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))

    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (hres₁ : ∀ (f : ↥𝒩₀) (n : ℕ), R₁.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ f.2)).1⟩ ≠ 0 →
      x₁.ord (R₁.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ f.2)).1⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥𝒩₀ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hres₂ : ∀ (f : ↥𝒩₀) (n : ℕ), R₂.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ f.2)).2.1⟩ ≠ 0 →
      x₂.ord (R₂.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ f.2)).2.1⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥𝒩₀ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})

    (x y : ↥𝒩₀)
    (x_fst : R₁.residue ⟨x, ((h𝒩 x).1 (h𝒩₀ x.2)).1⟩ = 0)
    (x_snd : x₂.ord (R₂.residue ⟨x, ((h𝒩 x).1 (h𝒩₀ x.2)).2.1⟩) = 1)
    (y_snd : R₂.residue ⟨y, ((h𝒩 y).1 (h𝒩₀ y.2)).2.1⟩ = 0)
    (y_fst : x₁.ord (R₁.residue ⟨y, ((h𝒩 y).1 (h𝒩₀ y.2)).1⟩) = 1)
    (E₀ : ℕ) (u : ↥𝒩₀) (hu : IsUnit u)
    (hxy : x * y = ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ ^ E₀ * u) :
    ∃ An An' : Annulus A F,
      (∀ P : Place L F, P ∈ An.dom ↔ P ∈ S) ∧
      An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
      ((An.modulus : L) = ((ϖ : ↥C) : L) ^ E₀) ∧ ((An.modulus : L) ≠ 0) ∧
      An.param = ((y : ↥𝒩₀) : F) ∧
      An'.param * An.param = algebraMap L F (An.modulus : L) ∧

      (∃ hz : An.param ∈ R₁.integers, x₁.ord (R₁.residue ⟨An.param, hz⟩) = 1 ∧
        ∀ (f : F) (hf : f ∈ R₁.integers), R₁.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord f = 0) →
          ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(x₁.ord (R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧

      (∃ hz : An'.param ∈ R₂.integers, x₂.ord (R₂.residue ⟨An'.param, hz⟩) = 1 ∧
        ∀ (f : F) (hf : f ∈ R₂.integers), R₂.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An'.dom, P.ord f = 0) →
          ∀ P ∈ An'.dom,
            ∃ h : P.evalAt f * (P.evalAt An'.param) ^ (-(x₂.ord (R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) :=
  AlgebraicCurve.exists_annulusPair_isAttached_of_ringEquiv_uvCrossingModel_of_nodeCoordinates A R₁ R₂ x₁ x₂ S hrat 𝒩 h𝒩 hval hreg hord 𝒩₀ h𝒩₀ hS hgen C hC hCmem ϖ hϖ hϖ0 halg hrk hx₁r hx₂r hres π hπ σ hσπ E hE ι hconst hres₁ hres₂ x y x_fst x_snd y_snd y_fst E₀ u hu hxy

end S_AlgebraicCurve_exists_annulusPair_isAttached_of_ringEquiv_uvCrossingModel_of_nodeCoordinates
end P2MW
export P2MW.S_AlgebraicCurve_exists_annulusPair_isAttached_of_ringEquiv_uvCrossingModel_of_nodeCoordinates (solution)
