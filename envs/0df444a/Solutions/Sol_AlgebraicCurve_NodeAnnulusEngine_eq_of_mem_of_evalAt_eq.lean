-- Prove2me | solution 1 for AlgebraicCurve.NodeAnnulusEngine.eq_of_mem_of_evalAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/b81e7a94-0d92-5fe7-ad21-ea4567a0e1f4

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_NodeAnnulusEngine_eq_of_mem_of_evalAt_eq

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_eq_of_mem_of_evalAt_eq.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Place.ord_zero Place.evalAt_one RegularProlongation IsCurveOver Place.evalAt_algebraMap_eq"
namespace NodeAnnulusEngine
namespace ZeroCount
p2m_open "AlgebraicCurve"

section PlaceHelpers

theorem vsub_inv_mem {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
    (hu : IsUnit (⟨f, hf⟩ : O)) : f⁻¹ ∈ O :=
  O.mem_of_valuation_le_one _ (by
    rw [map_inv₀, show O.valuation f = 1 from (O.valuation_eq_one_iff ⟨f, hf⟩).mp hu, inv_one])

theorem vsub_isUnit_of_inv_mem {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
    (hf0 : f ≠ 0) (hi : f⁻¹ ∈ O) : IsUnit (⟨f, hf⟩ : O) :=
  isUnit_iff_exists_inv.mpr ⟨⟨f⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ hf0)⟩

theorem vsub_ne_zero_of_isUnit {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
    (hu : IsUnit (⟨f, hf⟩ : O)) : f ≠ 0 := by
  rintro rfl
  have h0 : (⟨0, hf⟩ : O) = 0 := Subtype.ext rfl
  rw [h0] at hu
  exact not_isUnit_zero hu

theorem vsub_not_isUnit_algebraMap {L F : Type*} [Field L] [Field F] [Algebra L F] (A : ValuationSubring L)
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

theorem isUnit_transfer {L : Type*} [Field L] (A : ValuationSubring L) {a b : L} (hab : a = b) (ha : a ∈ A)
    (hu : IsUnit (⟨a, ha⟩ : ↥A)) : ∃ h : b ∈ A, IsUnit (⟨b, h⟩ : ↥A) := by
  subst hab
  exact ⟨ha, hu⟩

theorem vsub_zpow_mem_of_isUnit {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
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

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

theorem isUnit_iff_ord_eq_zero {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
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

theorem one_le_ord_of_not_isUnit {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0)
    (hu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring)) : 1 ≤ v.ord f := by
  have h0 := ord_nonneg_of_mem v hf
  have h1 : v.ord f ≠ 0 := fun h => hu ((isUnit_iff_ord_eq_zero v hf hf0).mpr h)
  omega

theorem evalAt_eq_zero_iff_not_isUnit (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = 0 ↔ ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  rw [← residue_ne_zero_iff_isUnit, not_not, ← v.algebraMap_evalAt hv hf,
    map_eq_zero_iff _ (algebraMap K v.ResidueField).injective]

theorem evalAt_zero' : v.evalAt (0 : F) = 0 := by
  have h := v.evalAt_algebraMap_eq (0 : K)
  rwa [map_zero] at h

theorem evalAt_eq_zero_of_ord_ne_zero (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.ord f ≠ 0) : v.evalAt f = 0 := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact evalAt_zero' v
  exact (evalAt_eq_zero_iff_not_isUnit v hv hf).mpr fun hu => h ((isUnit_iff_ord_eq_zero v hf hf0).mp hu)

theorem ord_eq_zero_of_evalAt_ne_zero (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  by_contra h'
  exact h (evalAt_eq_zero_of_ord_ne_zero v hv hf h')

theorem isUnit_of_evalAt_ne_zero (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  by_contra h'
  exact h ((evalAt_eq_zero_iff_not_isUnit v hv hf).mpr h')

theorem evalAt_add_of_mem (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem evalAt_neg_of_mem (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (-f) = -v.evalAt f := by
  apply v.algebraMap_residueField_injective
  rw [map_neg, v.algebraMap_evalAt hv (neg_mem hf), v.algebraMap_evalAt hv hf, ← map_neg]
  rfl

theorem evalAt_sub_of_mem (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  rw [sub_eq_add_neg, evalAt_add_of_mem v hv hf (neg_mem hg), evalAt_neg_of_mem v hv hg, ← sub_eq_add_neg]

theorem evalAt_pow_of_mem (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp [Place.evalAt_one]
  | succ n ih => rw [pow_succ, v.evalAt_mul_of_mem hv (pow_mem hf n) hf, ih, pow_succ]

theorem evalAt_inv_of_isUnit (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) : v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hf0 := vsub_ne_zero_of_isUnit _ hf hu
  have hi := vsub_inv_mem v.toValuationSubring hf hu
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← v.evalAt_mul_of_mem hv hf hi, mul_inv_cancel₀ hf0, Place.evalAt_one]

theorem isUnit_pow_mk {f : F} (hf : f ∈ v.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) (n : ℕ) :
    IsUnit (⟨f ^ n, pow_mem hf n⟩ : v.toValuationSubring) := by
  have : (⟨f ^ n, pow_mem hf n⟩ : v.toValuationSubring) = ⟨f, hf⟩ ^ n := Subtype.ext (by simp)
  rw [this]
  exact hu.pow n

theorem zpow_mem_of_isUnit {f : F} (hf : f ∈ v.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) (n : ℤ) : f ^ n ∈ v.toValuationSubring := by
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem hf m
  · rw [zpow_negSucc]
    exact vsub_inv_mem _ _ (isUnit_pow_mk v hf hu (m + 1))

theorem evalAt_zpow_of_isUnit (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) (n : ℤ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, evalAt_pow_of_mem v hv hf]
  · rw [zpow_negSucc, zpow_negSucc, ← evalAt_pow_of_mem v hv hf,
      evalAt_inv_of_isUnit v hv (pow_mem hf _) (isUnit_pow_mk v hf hu (m + 1))]

theorem ord_algebraMap (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hc' : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  apply (isUnit_iff_ord_eq_zero v (v.algebraMap_mem' c) hc').mp
  refine vsub_isUnit_of_inv_mem _ _ hc' ?_
  rw [← map_inv₀]
  exact v.algebraMap_mem' c⁻¹

theorem isUnit_algebraMap_mk {c : K} (hc : c ≠ 0) :
    IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
  (isUnit_iff_ord_eq_zero v _ ((map_ne_zero _).mpr hc)).mpr (ord_algebraMap v c)

theorem ord_smul_const {c : K} (hc : c ≠ 0) {f : F} (hf : f ≠ 0) : v.ord (c • f) = v.ord f := by
  rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).mpr hc) hf, ord_algebraMap v, zero_add]

end PlaceHelpers

section ChartHelpers

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar] (Cc : RegularProlongation A F Fbar)

theorem chart_isUnit_of_residue_ne_zero {f : Cc.integers} (hf : Cc.residue f ≠ 0) : IsUnit f := by
  by_contra h
  apply hf
  have hmem : f ∈ maximalIdeal Cc.integers := (IsLocalRing.mem_maximalIdeal f).mpr h
  rw [← Cc.ker_residue] at hmem
  exact hmem

theorem chart_residue_ne_zero_of_isUnit {f : Cc.integers} (hf : IsUnit f) : Cc.residue f ≠ 0 := by
  intro h0
  have hmem : f ∈ RingHom.ker Cc.residue := h0
  rw [Cc.ker_residue] at hmem
  exact (IsLocalRing.mem_maximalIdeal f).mp hmem hf

theorem chart_residue_eq_zero_iff {f : Cc.integers} : Cc.residue f = 0 ↔ ¬ IsUnit f :=
  ⟨fun h hu => chart_residue_ne_zero_of_isUnit Cc hu h,
   fun h => by_contra fun h' => h (chart_isUnit_of_residue_ne_zero Cc h')⟩

theorem chart_residue_add {f g : F} (hf : f ∈ Cc.integers) (hg : g ∈ Cc.integers) :
    Cc.residue ⟨f + g, add_mem hf hg⟩ = Cc.residue ⟨f, hf⟩ + Cc.residue ⟨g, hg⟩ := by
  rw [← map_add]; rfl

theorem chart_residue_mul {f g : F} (hf : f ∈ Cc.integers) (hg : g ∈ Cc.integers) :
    Cc.residue ⟨f * g, mul_mem hf hg⟩ = Cc.residue ⟨f, hf⟩ * Cc.residue ⟨g, hg⟩ := by
  rw [← map_mul]; rfl

theorem chart_residue_one : Cc.residue ⟨1, one_mem _⟩ = 1 := by
  rw [← map_one Cc.residue]; rfl

theorem chart_residue_pow {f : F} (hf : f ∈ Cc.integers) (n : ℕ) :
    Cc.residue ⟨f ^ n, pow_mem hf n⟩ = Cc.residue ⟨f, hf⟩ ^ n := by
  rw [← map_pow]; rfl

theorem chart_algebraMap_mem (a : ↥A) : algebraMap L F (a : L) ∈ Cc.integers :=
  (Cc.algebraMap_mem_iff (a : L)).mpr a.2

theorem chart_residue_const (a : ↥A) :
    Cc.residue ⟨algebraMap L F (a : L), chart_algebraMap_mem Cc a⟩ =
      algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  Cc.residue_algebraMap a

theorem chart_residue_smul_eq_zero_of_mem_maximalIdeal {f : F} (hf : f ∈ Cc.integers) (a : ↥A)
    (ha : a ∈ maximalIdeal ↥A) (h : (a : L) • f ∈ Cc.integers) : Cc.residue ⟨(a : L) • f, h⟩ = 0 := by
  have : (⟨(a : L) • f, h⟩ : Cc.integers) = ⟨algebraMap L F (a : L), chart_algebraMap_mem Cc a⟩ * ⟨f, hf⟩ :=
    Subtype.ext (Algebra.smul_def (a : L) f)
  rw [this, map_mul, chart_residue_const, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero, zero_mul]

theorem chart_inv_mem {f : F} (hf : f ∈ Cc.integers) (hu : IsUnit (⟨f, hf⟩ : Cc.integers)) :
    f⁻¹ ∈ Cc.integers := vsub_inv_mem _ hf hu

theorem chart_residue_inv {f : F} (hf : f ∈ Cc.integers) (hu : IsUnit (⟨f, hf⟩ : Cc.integers)) :
    Cc.residue ⟨f⁻¹, chart_inv_mem Cc hf hu⟩ = (Cc.residue ⟨f, hf⟩)⁻¹ := by
  have hf0 := vsub_ne_zero_of_isUnit _ hf hu
  symm; apply inv_eq_of_mul_eq_one_right
  rw [← chart_residue_mul, ← chart_residue_one Cc]
  congr 1
  exact Subtype.ext (mul_inv_cancel₀ hf0)

theorem chart_smul_const_ne_zero {f : F} {c : L} (hc : c • f ∈ Cc.integers)
    (h : Cc.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply h
  have : (⟨(0 : L) • f, hc⟩ : Cc.integers) = 0 := Subtype.ext (by simp)
  rw [this, map_zero]

theorem chart_zpow_mem {f : F} (hf : f ∈ Cc.integers) (hu : IsUnit (⟨f, hf⟩ : Cc.integers)) (n : ℤ) :
    f ^ n ∈ Cc.integers := vsub_zpow_mem_of_isUnit _ hf hu n

theorem chart_residue_zpow {f : F} (hf : f ∈ Cc.integers) (hu : IsUnit (⟨f, hf⟩ : Cc.integers)) (n : ℤ) :
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

section ChartHelpers2

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar] (Cc : RegularProlongation A F Fbar)

theorem chart_residue_sub {f g : F} (hf : f ∈ Cc.integers) (hg : g ∈ Cc.integers) :
    Cc.residue ⟨f - g, sub_mem hf hg⟩ = Cc.residue ⟨f, hf⟩ - Cc.residue ⟨g, hg⟩ := by
  rw [← map_sub]; rfl

theorem chart_residue_congr {f g : F} (hfg : f = g) (hf : f ∈ Cc.integers) (hg : g ∈ Cc.integers) :
    Cc.residue ⟨f, hf⟩ = Cc.residue ⟨g, hg⟩ := by
  subst hfg; rfl

theorem chart_residue_const_eq_zero (a : ↥A) (ha : a ∈ maximalIdeal ↥A) :
    Cc.residue ⟨algebraMap L F (a : L), chart_algebraMap_mem Cc a⟩ = 0 := by
  rw [chart_residue_const, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero]

end ChartHelpers2

section Frame

structure ZH {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (x₁ : Place (ResidueField A) Fbar₁) (x₂ : Place (ResidueField A) Fbar₂)
    (S : Set (Place L F)) (𝒩 : Subring F) (𝒩₀ : Subring F)
    (ϖL : L) (hϖN : algebraMap L F ϖL ∈ 𝒩₀)
    (x y : ↥𝒩₀) (E₀ : ℕ) (u : ↥𝒩₀) : Prop where
  hrat : ∀ P ∈ S, P.IsRational
  h𝒩 : ∀ f : F, f ∈ 𝒩 ↔ f ∈ R₁.integers ∧ f ∈ R₂.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring
  hval : ∀ f ∈ 𝒩, ∀ P ∈ S, P.evalAt f ∈ A
  hord : ∀ (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers),
    R₁.residue ⟨f, h₁⟩ ≠ 0 → R₂.residue ⟨f, h₂⟩ ≠ 0 →
      {P : Place L F | P ∈ S ∧ P.ord f ≠ 0}.Finite ∧
      ∑ᶠ P ∈ S, P.ord f = x₁.ord (R₁.residue ⟨f, h₁⟩) + x₂.ord (R₂.residue ⟨f, h₂⟩)
  h𝒩₀ : 𝒩₀ ≤ 𝒩
  hS : ∀ P : Place L F, P ∈ S ↔
    (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
    (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)
  hϖ0 : ϖL ≠ 0
  x_fst : R₁.residue ⟨x, ((h𝒩 x).1 (h𝒩₀ x.2)).1⟩ = 0
  x_snd : x₂.ord (R₂.residue ⟨x, ((h𝒩 x).1 (h𝒩₀ x.2)).2.1⟩) = 1
  y_snd : R₂.residue ⟨y, ((h𝒩 y).1 (h𝒩₀ y.2)).2.1⟩ = 0
  y_fst : x₁.ord (R₁.residue ⟨y, ((h𝒩 y).1 (h𝒩₀ y.2)).1⟩) = 1
  hu : IsUnit u
  hxy : x * y = ⟨algebraMap L F ϖL, hϖN⟩ ^ E₀ * u

structure Adm {L : Type*} [Field L] (A : ValuationSubring L) (ϖL : L) (E₀ : ℕ) (a : ↥A) : Prop where
  mem : a ∈ maximalIdeal ↥A
  ne0 : (a : L) ≠ 0
  cof : ∃ m : ↥A, m ∈ maximalIdeal ↥A ∧ (ϖL ^ E₀ : L) = (a : L) * (m : L)

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField A) Fbar₂]
    {R₁ : RegularProlongation A F Fbar₁} {R₂ : RegularProlongation A F Fbar₂}
    {x₁ : Place (ResidueField A) Fbar₁} {x₂ : Place (ResidueField A) Fbar₂}
    {S : Set (Place L F)} {𝒩 𝒩₀ : Subring F}
    {ϖL : L} {hϖN : algebraMap L F ϖL ∈ 𝒩₀}
    {x y : ↥𝒩₀} {E₀ : ℕ} {u : ↥𝒩₀}
    (H : ZH A R₁ R₂ x₁ x₂ S 𝒩 𝒩₀ ϖL hϖN x y E₀ u)

include H

theorem memR₁ (f : ↥𝒩₀) : (f : F) ∈ R₁.integers := ((H.h𝒩 f).1 (H.h𝒩₀ f.2)).1
theorem memR₂ (f : ↥𝒩₀) : (f : F) ∈ R₂.integers := ((H.h𝒩 f).1 (H.h𝒩₀ f.2)).2.1
theorem memP (f : ↥𝒩₀) {P : Place L F} (hP : P ∈ S) : (f : F) ∈ P.toValuationSubring :=
  ((H.hS P).1 hP).1 f f.2

theorem isUnit_R₁_of_isUnit {g : ↥𝒩₀} (hg : IsUnit g) : IsUnit (⟨(g : F), memR₁ H g⟩ : R₁.integers) := by
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hg
  exact isUnit_iff_exists_inv.mpr ⟨⟨(w : F), memR₁ H w⟩, Subtype.ext (by
    have h' := congrArg Subtype.val hw
    simpa using h')⟩

theorem isUnit_R₂_of_isUnit {g : ↥𝒩₀} (hg : IsUnit g) : IsUnit (⟨(g : F), memR₂ H g⟩ : R₂.integers) := by
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hg
  exact isUnit_iff_exists_inv.mpr ⟨⟨(w : F), memR₂ H w⟩, Subtype.ext (by
    have h' := congrArg Subtype.val hw
    simpa using h')⟩

theorem not_isUnit_x : ¬ IsUnit x := fun h =>
  chart_residue_ne_zero_of_isUnit R₁ (isUnit_R₁_of_isUnit H h) H.x_fst

theorem not_isUnit_y : ¬ IsUnit y := fun h =>
  chart_residue_ne_zero_of_isUnit R₂ (isUnit_R₂_of_isUnit H h) H.y_snd

theorem isUnit_evalAt_of_isUnit {g : ↥𝒩₀} (hg : IsUnit g) {P : Place L F} (hP : P ∈ S) :
    ∃ h : P.evalAt (g : F) ∈ A, IsUnit (⟨_, h⟩ : ↥A) := by
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hg
  have hgA := H.hval _ (H.h𝒩₀ g.2) P hP
  have hwA := H.hval _ (H.h𝒩₀ w.2) P hP
  refine ⟨hgA, isUnit_iff_exists_inv.mpr ⟨⟨_, hwA⟩, Subtype.ext ?_⟩⟩
  show P.evalAt (g : F) * P.evalAt (w : F) = 1
  rw [← P.evalAt_mul_of_mem (H.hrat P hP) (memP H g hP) (memP H w hP), ← Subring.coe_mul, hw]
  simp [Place.evalAt_one]

theorem evalAt_mem_maximalIdeal_of_not_isUnit {g : ↥𝒩₀} (hg : ¬ IsUnit g) {P : Place L F} (hP : P ∈ S) :
    ∃ h : P.evalAt (g : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A :=
  ((H.hS P).1 hP).2 g hg

theorem coe_ϖN_pow (n : ℕ) :
    (((⟨algebraMap L F ϖL, hϖN⟩ : ↥𝒩₀) ^ n : ↥𝒩₀) : F) = algebraMap L F (ϖL ^ n) := by
  simp [map_pow]

theorem x_mul_y : (x : F) * (y : F) = algebraMap L F (ϖL ^ E₀) * (u : F) := by
  have h := congrArg (fun t : ↥𝒩₀ => (t : F)) H.hxy
  simp only [Subring.coe_mul] at h
  rw [h, coe_ϖN_pow H]

theorem evalAt_x_mul_evalAt_y {P : Place L F} (hP : P ∈ S) :
    P.evalAt (x : F) * P.evalAt (y : F) = ϖL ^ E₀ * P.evalAt (u : F) := by
  have hr := H.hrat P hP
  rw [← P.evalAt_mul_of_mem hr (memP H x hP) (memP H y hP), x_mul_y H,
    P.evalAt_mul_of_mem hr (P.algebraMap_mem' _) (memP H u hP), Place.evalAt_algebraMap_eq]

theorem evalAt_u_ne_zero {P : Place L F} (hP : P ∈ S) : P.evalAt (u : F) ≠ 0 := by
  obtain ⟨huA, huU⟩ := isUnit_evalAt_of_isUnit H H.hu hP
  intro h'
  have : (⟨P.evalAt (u : F), huA⟩ : ↥A) = 0 := Subtype.ext h'
  rw [this] at huU
  exact not_isUnit_zero huU

theorem evalAt_y_ne_zero {P : Place L F} (hP : P ∈ S) : P.evalAt (y : F) ≠ 0 := by
  intro h0
  have h := evalAt_x_mul_evalAt_y H hP
  rw [h0, mul_zero] at h
  exact mul_ne_zero (pow_ne_zero _ H.hϖ0) (evalAt_u_ne_zero H hP) h.symm

theorem u_ne_zero : (u : F) ≠ 0 := fun h => by
  have : u = 0 := Subtype.ext h
  exact not_isUnit_zero (this ▸ H.hu)

theorem x_ne_zero : (x : F) ≠ 0 := fun h => by
  have h1 := x_mul_y H
  rw [h, zero_mul] at h1
  exact mul_ne_zero ((map_ne_zero _).mpr (pow_ne_zero _ H.hϖ0)) (u_ne_zero H) h1.symm

theorem residue₁_y_ne_zero : R₁.residue ⟨(y : F), memR₁ H y⟩ ≠ 0 := fun h => by
  have h1 := H.y_fst
  rw [h, Place.ord_zero] at h1
  exact zero_ne_one h1

theorem residue₂_x_ne_zero : R₂.residue ⟨(x : F), memR₂ H x⟩ ≠ 0 := fun h => by
  have h1 := H.x_snd
  rw [h, Place.ord_zero] at h1
  exact zero_ne_one h1

theorem x_isUnit_R₂ : IsUnit (⟨(x : F), memR₂ H x⟩ : R₂.integers) :=
  chart_isUnit_of_residue_ne_zero R₂ (residue₂_x_ne_zero H)

theorem y_eq : (y : F) = algebraMap L F (ϖL ^ E₀) * (u : F) * (x : F)⁻¹ := by
  have h := x_mul_y H
  have hx := x_ne_zero H
  field_simp
  linear_combination h

theorem admissible_evalAt_y {P : Place L F} (hP : P ∈ S) :
    ∃ hA : P.evalAt (y : F) ∈ A, (⟨_, hA⟩ : ↥A) ∈ maximalIdeal ↥A ∧ P.evalAt (y : F) ≠ 0 ∧
      ∃ m ∈ maximalIdeal ↥A, (ϖL ^ E₀ : L) = P.evalAt (y : F) * (m : L) := by
  obtain ⟨hyA, hym⟩ := evalAt_mem_maximalIdeal_of_not_isUnit H (not_isUnit_y H) hP
  refine ⟨hyA, hym, evalAt_y_ne_zero H hP, ?_⟩
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

theorem ysub_memR₁ (a : ↥A) : (y : F) - algebraMap L F (a : L) ∈ R₁.integers :=
  sub_mem (memR₁ H y) (chart_algebraMap_mem R₁ a)

theorem residue₁_ysub (a : ↥A) (ha : a ∈ maximalIdeal ↥A) :
    R₁.residue ⟨(y : F) - algebraMap L F (a : L), ysub_memR₁ H a⟩ = R₁.residue ⟨(y : F), memR₁ H y⟩ := by
  rw [chart_residue_sub R₁ (memR₁ H y) (chart_algebraMap_mem R₁ a), chart_residue_const_eq_zero R₁ a ha, sub_zero]

theorem ysub_isUnit_R₁ (a : ↥A) (ha : a ∈ maximalIdeal ↥A) :
    IsUnit (⟨(y : F) - algebraMap L F (a : L), ysub_memR₁ H a⟩ : R₁.integers) :=
  chart_isUnit_of_residue_ne_zero R₁ (by rw [residue₁_ysub H a ha]; exact residue₁_y_ne_zero H)

theorem ysub_ne_zero (a : ↥A) (ha : a ∈ maximalIdeal ↥A) : (y : F) - algebraMap L F (a : L) ≠ 0 :=
  vsub_ne_zero_of_isUnit _ _ (ysub_isUnit_R₁ H a ha)

theorem wfun_memR₂ (m : ↥A) : algebraMap L F (m : L) * (u : F) * (x : F)⁻¹ ∈ R₂.integers :=
  mul_mem (mul_mem (chart_algebraMap_mem R₂ m) (memR₂ H u)) (chart_inv_mem R₂ (memR₂ H x) (x_isUnit_R₂ H))

theorem residue₂_wfun (m : ↥A) (hm : m ∈ maximalIdeal ↥A) :
    R₂.residue ⟨algebraMap L F (m : L) * (u : F) * (x : F)⁻¹, wfun_memR₂ H m⟩ = 0 := by
  rw [chart_residue_mul R₂ (mul_mem (chart_algebraMap_mem R₂ m) (memR₂ H u)) (chart_inv_mem R₂ (memR₂ H x) (x_isUnit_R₂ H)),
    chart_residue_mul R₂ (chart_algebraMap_mem R₂ m) (memR₂ H u), chart_residue_const_eq_zero R₂ m hm, zero_mul, zero_mul]

theorem wsub_memR₂ (m : ↥A) : algebraMap L F (m : L) * (u : F) * (x : F)⁻¹ - 1 ∈ R₂.integers :=
  sub_mem (wfun_memR₂ H m) (one_mem _)

theorem residue₂_wsub (m : ↥A) (hm : m ∈ maximalIdeal ↥A) :
    R₂.residue ⟨algebraMap L F (m : L) * (u : F) * (x : F)⁻¹ - 1, wsub_memR₂ H m⟩ = -1 := by
  rw [chart_residue_sub R₂ (wfun_memR₂ H m) (one_mem _), residue₂_wfun H m hm, chart_residue_one, zero_sub]

theorem wsub_isUnit_R₂ (m : ↥A) (hm : m ∈ maximalIdeal ↥A) :
    IsUnit (⟨algebraMap L F (m : L) * (u : F) * (x : F)⁻¹ - 1, wsub_memR₂ H m⟩ : R₂.integers) :=
  chart_isUnit_of_residue_ne_zero R₂ (by rw [residue₂_wsub H m hm]; exact neg_ne_zero.mpr one_ne_zero)

theorem ysub_eq_mul_wsub (a m : ↥A) (ham : (ϖL ^ E₀ : L) = (a : L) * (m : L)) :
    (y : F) - algebraMap L F (a : L) =
      algebraMap L F (a : L) * (algebraMap L F (m : L) * (u : F) * (x : F)⁻¹ - 1) := by
  rw [y_eq H, ham, map_mul]
  ring

theorem ysub_memP (a : L) {P : Place L F} (hP : P ∈ S) : (y : F) - algebraMap L F a ∈ P.toValuationSubring :=
  sub_mem (memP H y hP) (P.algebraMap_mem' a)

theorem evalAt_ysub (a : L) {P : Place L F} (hP : P ∈ S) :
    P.evalAt ((y : F) - algebraMap L F a) = P.evalAt (y : F) - a := by
  rw [evalAt_sub_of_mem P (H.hrat P hP) (memP H y hP) (P.algebraMap_mem' a), Place.evalAt_algebraMap_eq]

theorem ord_ysub_nonneg (a : L) {P : Place L F} (hP : P ∈ S) : 0 ≤ P.ord ((y : F) - algebraMap L F a) :=
  ord_nonneg_of_mem P (ysub_memP H a hP)

theorem ord_ysub_ne_zero_iff (a : ↥A) (ha : a ∈ maximalIdeal ↥A) {P : Place L F} (hP : P ∈ S) :
    P.ord ((y : F) - algebraMap L F (a : L)) ≠ 0 ↔ P.evalAt (y : F) = (a : L) := by
  constructor
  · intro h
    have := evalAt_eq_zero_of_ord_ne_zero P (H.hrat P hP) (ysub_memP H (a : L) hP) h
    rw [evalAt_ysub H (a : L) hP] at this
    exact sub_eq_zero.mp this
  · intro h h0
    have hu := (isUnit_iff_ord_eq_zero P (ysub_memP H (a : L) hP) (ysub_ne_zero H a ha)).mpr h0
    have hne : P.evalAt ((y : F) - algebraMap L F (a : L)) ≠ 0 := fun h' =>
      ((evalAt_eq_zero_iff_not_isUnit P (H.hrat P hP) (ysub_memP H (a : L) hP)).mp h') hu
    rw [evalAt_ysub H (a : L) hP, h, sub_self] at hne
    exact hne rfl

theorem ord_ysub_eq_zero_or (a b : ↥A) (ha : a ∈ maximalIdeal ↥A) (hb : b ∈ maximalIdeal ↥A) (hab : a ≠ b)
    {P : Place L F} (hP : P ∈ S) :
    P.ord ((y : F) - algebraMap L F (a : L)) = 0 ∨ P.ord ((y : F) - algebraMap L F (b : L)) = 0 := by
  by_contra h
  rw [not_or] at h
  have ha' := (ord_ysub_ne_zero_iff H a ha hP).mp h.1
  have hb' := (ord_ysub_ne_zero_iff H b hb hP).mp h.2
  exact hab (Subtype.ext (ha'.symm.trans hb'))

noncomputable def gq (c d : ↥A) (n : ℕ) : F :=
  ((y : F) - algebraMap L F (d : L)) ^ n * ((y : F) - algebraMap L F (c : L))⁻¹

theorem gq_memR₁ {c : ↥A} (hc : Adm A ϖL E₀ c) (d : ↥A) (n : ℕ) : gq (y := y) c d n ∈ R₁.integers :=
  mul_mem (pow_mem (ysub_memR₁ H d) n) (chart_inv_mem R₁ (ysub_memR₁ H c) (ysub_isUnit_R₁ H c hc.mem))

theorem residue₁_gq {c d : ↥A} (hc : Adm A ϖL E₀ c) (hd : Adm A ϖL E₀ d) {n : ℕ} (hn1 : 1 ≤ n) :
    R₁.residue ⟨gq (y := y) c d n, gq_memR₁ H hc d n⟩ = R₁.residue ⟨(y : F), memR₁ H y⟩ ^ (n - 1) := by
  have hU := ysub_isUnit_R₁ H c hc.mem
  rw [show (⟨gq (y := y) c d n, gq_memR₁ H hc d n⟩ : R₁.integers) =
      ⟨((y : F) - algebraMap L F (d : L)) ^ n, pow_mem (ysub_memR₁ H d) n⟩ *
        ⟨((y : F) - algebraMap L F (c : L))⁻¹, chart_inv_mem R₁ (ysub_memR₁ H c) hU⟩ from rfl,
    map_mul, chart_residue_pow R₁ (ysub_memR₁ H d) n, chart_residue_inv R₁ _ hU, residue₁_ysub H d hd.mem,
    residue₁_ysub H c hc.mem]
  have hne := residue₁_y_ne_zero H
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, mul_assoc, mul_inv_cancel₀ hne, mul_one]

theorem residue₁_gq_ne_zero {c d : ↥A} (hc : Adm A ϖL E₀ c) (hd : Adm A ϖL E₀ d) {n : ℕ} (hn1 : 1 ≤ n) :
    R₁.residue ⟨gq (y := y) c d n, gq_memR₁ H hc d n⟩ ≠ 0 := by
  rw [residue₁_gq H hc hd hn1]
  exact pow_ne_zero _ (residue₁_y_ne_zero H)

theorem ord₁_residue₁_gq {c d : ↥A} (hc : Adm A ϖL E₀ c) (hd : Adm A ϖL E₀ d) {n : ℕ} (hn1 : 1 ≤ n) :
    x₁.ord (R₁.residue ⟨gq (y := y) c d n, gq_memR₁ H hc d n⟩) = (n : ℤ) - 1 := by
  rw [residue₁_gq H hc hd hn1, ← zpow_natCast, x₁.ord_zpow, H.y_fst, mul_one]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp

theorem gq_eq_wform {c d : ↥A} {n : ℕ} (mc md : ↥A) (hcm : (ϖL ^ E₀ : L) = (c : L) * (mc : L))
    (hdm : (ϖL ^ E₀ : L) = (d : L) * (md : L)) (hc0 : (c : L) ≠ 0) (hdn : (d : L) ^ n = (c : L)) :
    gq (y := y) c d n =
      (algebraMap L F (md : L) * (u : F) * (x : F)⁻¹ - 1) ^ n *
        (algebraMap L F (mc : L) * (u : F) * (x : F)⁻¹ - 1)⁻¹ := by
  unfold gq
  rw [ysub_eq_mul_wsub H d md hdm, ysub_eq_mul_wsub H c mc hcm, mul_pow, ← map_pow, hdn, mul_inv]
  have hcF : algebraMap L F (c : L) ≠ 0 := (map_ne_zero _).mpr hc0
  field_simp

theorem wform_memR₂ {mc : ↥A} (hmc : mc ∈ maximalIdeal ↥A) (md : ↥A) (n : ℕ) :
    (algebraMap L F (md : L) * (u : F) * (x : F)⁻¹ - 1) ^ n *
        (algebraMap L F (mc : L) * (u : F) * (x : F)⁻¹ - 1)⁻¹ ∈ R₂.integers :=
  mul_mem (pow_mem (wsub_memR₂ H md) n) (chart_inv_mem R₂ (wsub_memR₂ H mc) (wsub_isUnit_R₂ H mc hmc))

theorem residue₂_wform {mc md : ↥A} (hmc : mc ∈ maximalIdeal ↥A) (hmd : md ∈ maximalIdeal ↥A) (n : ℕ) :
    R₂.residue ⟨_, wform_memR₂ H hmc md n⟩ = (-1) ^ (n + 1) := by
  have hU := wsub_isUnit_R₂ H mc hmc
  rw [show (⟨_, wform_memR₂ H hmc md n⟩ : R₂.integers) =
      ⟨(algebraMap L F (md : L) * (u : F) * (x : F)⁻¹ - 1) ^ n, pow_mem (wsub_memR₂ H md) n⟩ *
        ⟨(algebraMap L F (mc : L) * (u : F) * (x : F)⁻¹ - 1)⁻¹, chart_inv_mem R₂ (wsub_memR₂ H mc) hU⟩ from rfl,
    map_mul, chart_residue_pow R₂ (wsub_memR₂ H md) n, chart_residue_inv R₂ _ hU, residue₂_wsub H md hmd, residue₂_wsub H mc hmc,
    inv_neg, inv_one, pow_succ]

theorem gq_end₂ {c d : ↥A} (hc : Adm A ϖL E₀ c) (hd : Adm A ϖL E₀ d) {n : ℕ} (hdn : (d : L) ^ n = (c : L)) :
    ∃ h₂ : gq (y := y) c d n ∈ R₂.integers, R₂.residue ⟨_, h₂⟩ ≠ 0 ∧ x₂.ord (R₂.residue ⟨_, h₂⟩) = 0 := by
  obtain ⟨mc, hmc, hcm⟩ := hc.cof
  obtain ⟨md, hmd, hdm⟩ := hd.cof
  have heq := gq_eq_wform H mc md hcm hdm hc.ne0 hdn
  have h₂ : gq (y := y) c d n ∈ R₂.integers := heq ▸ wform_memR₂ H hmc md n
  have hres : R₂.residue ⟨_, h₂⟩ = (-1) ^ (n + 1) := by
    rw [chart_residue_congr R₂ heq h₂ (wform_memR₂ H hmc md n), residue₂_wform H hmc hmd n]
  refine ⟨h₂, ?_, ?_⟩
  · rw [hres]; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  · rw [hres, show ((-1 : Fbar₂) ^ (n + 1)) = algebraMap (ResidueField A) Fbar₂ ((-1) ^ (n + 1)) by simp,
      ord_algebraMap]

theorem ord_gq {c d : ↥A} (hc : c ∈ maximalIdeal ↥A) (hd : d ∈ maximalIdeal ↥A) (n : ℕ) {P : Place L F} (hP : P ∈ S) :
    P.ord (gq (y := y) c d n) =
      (n : ℤ) * P.ord ((y : F) - algebraMap L F (d : L)) - P.ord ((y : F) - algebraMap L F (c : L)) := by
  unfold gq
  rw [P.ord_mul (pow_ne_zero _ (ysub_ne_zero H d hd)) (inv_ne_zero (ysub_ne_zero H c hc)), P.ord_inv,
    ← zpow_natCast, P.ord_zpow]
  ring

noncomputable def Z (S : Set (Place L F)) (y : ↥𝒩₀) (a : L) : ℤ := ∑ᶠ P ∈ S, P.ord ((y : F) - algebraMap L F a)

theorem Z_nonneg (a : L) : 0 ≤ Z S y a :=
  finsum_nonneg fun P => finsum_nonneg fun hP => ord_ysub_nonneg H a hP

omit H in

theorem setOf_eq_inter_support (T : Set (Place L F)) (f : Place L F → ℤ) :
    {P : Place L F | P ∈ T ∧ f P ≠ 0} = T ∩ Function.support f := by
  ext P; simp [Function.mem_support]

omit H in

theorem finsum_mem_neg' (f : Place L F → ℤ) (T : Set (Place L F)) : ∑ᶠ P ∈ T, -f P = -∑ᶠ P ∈ T, f P := by
  rw [← finsum_neg_distrib]
  exact finsum_congr fun P => finsum_neg_distrib _

theorem adm_root {c d : ↥A} (hc : Adm A ϖL E₀ c) {n : ℕ} (hn1 : 1 ≤ n) (hdn : (d : L) ^ n = (c : L)) :
    Adm A ϖL E₀ d := by
  have hdn' : d ^ n = c := Subtype.ext (by simpa using hdn)
  have hd : d ∈ maximalIdeal ↥A := by
    have : d ^ n ∈ maximalIdeal ↥A := hdn' ▸ hc.mem
    exact (IsLocalRing.maximalIdeal.isMaximal ↥A).isPrime.mem_of_pow_mem n this
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m, hm, hcm⟩ := hc.cof
  refine ⟨hd, ?_, ⟨d ^ k * m, Ideal.mul_mem_left _ _ hm, ?_⟩⟩
  · intro h0
    apply hc.ne0
    rw [← hdn, h0, zero_pow (by omega)]
  · rw [hcm, ← hdn]
    push_cast
    ring

theorem relation {c d : ↥A} (hc : Adm A ϖL E₀ c) {n : ℕ} (hn : 2 ≤ n) (hdn : (d : L) ^ n = (c : L)) :
    (S ∩ Function.support fun P => P.ord ((y : F) - algebraMap L F (d : L))).Finite ∧
    (S ∩ Function.support fun P => P.ord ((y : F) - algebraMap L F (c : L))).Finite ∧
    (n : ℤ) * Z S y (d : L) - Z S y (c : L) = (n : ℤ) - 1 := by
  have hn1 : 1 ≤ n := by omega
  have hd : Adm A ϖL E₀ d := adm_root H hc hn1 hdn
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hcd : c ≠ d := by
    intro hcd
    subst hcd

    have h1 : (c : L) ^ k = 1 := by
      have : (c : L) ^ k * (c : L) = 1 * (c : L) := by rw [one_mul, ← pow_succ, ← hk, hdn]
      exact mul_right_cancel₀ hc.ne0 this
    have hcu : IsUnit (c : ↥A) := by
      have h1' : c ^ k = 1 := Subtype.ext (by simpa using h1)
      exact IsUnit.of_pow_eq_one h1' (by omega)
    exact (IsLocalRing.mem_maximalIdeal _).mp hc.mem hcu

  obtain ⟨h₂, hres₂, hord₂⟩ := gq_end₂ H hc hd hdn
  obtain ⟨hfin, hsum⟩ := H.hord (gq (y := y) c d n) (gq_memR₁ H hc d n) h₂
    (residue₁_gq_ne_zero H hc hd hn1) hres₂
  rw [ord₁_residue₁_gq H hc hd hn1, hord₂, add_zero] at hsum
  rw [setOf_eq_inter_support] at hfin

  have hordgq : ∀ P ∈ S, P.ord (gq (y := y) c d n) =
      (n : ℤ) * P.ord ((y : F) - algebraMap L F (d : L)) - P.ord ((y : F) - algebraMap L F (c : L)) :=
    fun P hP => ord_gq H hc.mem hd.mem n hP
  have hsubd : (S ∩ Function.support fun P => P.ord ((y : F) - algebraMap L F (d : L))) ⊆
      S ∩ Function.support fun P => P.ord (gq (y := y) c d n) := by
    rintro P ⟨hP, hP'⟩
    refine ⟨hP, ?_⟩
    rw [Function.mem_support] at hP' ⊢
    rw [hordgq P hP]
    rcases ord_ysub_eq_zero_or H c d hc.mem hd.mem hcd hP with h0 | h0
    · rw [h0, sub_zero]
      exact mul_ne_zero (by exact_mod_cast (show n ≠ 0 by omega)) hP'
    · exact absurd h0 hP'
  have hsubc : (S ∩ Function.support fun P => P.ord ((y : F) - algebraMap L F (c : L))) ⊆
      S ∩ Function.support fun P => P.ord (gq (y := y) c d n) := by
    rintro P ⟨hP, hP'⟩
    refine ⟨hP, ?_⟩
    rw [Function.mem_support] at hP' ⊢
    rw [hordgq P hP]
    rcases ord_ysub_eq_zero_or H c d hc.mem hd.mem hcd hP with h0 | h0
    · exact absurd h0 hP'
    · rw [h0, mul_zero, zero_sub]
      exact neg_ne_zero.mpr hP'
  have hfind := hfin.subset hsubd
  have hfinc := hfin.subset hsubc
  refine ⟨hfind, hfinc, ?_⟩

  have hfind' : (S ∩ Function.support fun P => (n : ℤ) * P.ord ((y : F) - algebraMap L F (d : L))).Finite := by
    refine hfind.subset ?_
    rintro P ⟨hP, hP'⟩
    exact ⟨hP, fun h => hP' (by simp [h])⟩
  have hfinc' : (S ∩ Function.support fun P => -P.ord ((y : F) - algebraMap L F (c : L))).Finite := by
    refine hfinc.subset ?_
    rintro P ⟨hP, hP'⟩
    exact ⟨hP, fun h => hP' (by simpa using h)⟩
  have e2 : ∑ᶠ P ∈ S, P.ord (gq (y := y) c d n) =
      ∑ᶠ P ∈ S, ((n : ℤ) * P.ord ((y : F) - algebraMap L F (d : L)) + -P.ord ((y : F) - algebraMap L F (c : L))) :=
    finsum_mem_congr rfl fun P hP => by rw [hordgq P hP, sub_eq_add_neg]
  have e3 := finsum_mem_add_distrib' hfind' hfinc'
  have e4 := mul_finsum_mem (fun P => P.ord ((y : F) - algebraMap L F (d : L))) (n : ℤ) (s := S)
  have e5 := finsum_mem_neg' (fun P => P.ord ((y : F) - algebraMap L F (c : L))) S
  unfold Z
  linarith

theorem Z_eq_one [IsAlgClosed L] {c : ↥A} (hc : Adm A ϖL E₀ c) :
    (S ∩ Function.support fun P => P.ord ((y : F) - algebraMap L F (c : L))).Finite ∧ Z S y (c : L) = 1 := by

  have root : ∀ n : ℕ, 1 ≤ n → ∃ d : ↥A, (d : L) ^ n = (c : L) := by
    intro n hn
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (c : L) (by omega : 0 < n)
    have hzA : z ∈ A := by
      by_contra hzA
      have hzi : z⁻¹ ∈ A := (A.mem_or_inv_mem z).resolve_left hzA
      have hz0 : z ≠ 0 := by rintro rfl; exact hzA A.zero_mem

      have h1 : (c : ↥A) * ⟨z⁻¹, hzi⟩ ^ n = 1 := Subtype.ext (by
        simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, OneMemClass.coe_one]
        rw [← hz, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hz0)])
      exact (IsLocalRing.mem_maximalIdeal _).mp hc.mem (IsUnit.of_mul_eq_one _ h1)
    exact ⟨⟨z, hzA⟩, hz⟩
  set Zc := Z S y (c : L) with hZc
  have hZc0 : 0 ≤ Zc := Z_nonneg H _

  obtain ⟨d₂, hd₂⟩ := root 2 (by norm_num)
  obtain ⟨-, hfinc, h2⟩ := relation H hc le_rfl hd₂
  have hZd₂ := Z_nonneg H (d₂ : L)
  have hZc1 : 1 ≤ Zc := by omega
  refine ⟨hfinc, ?_⟩

  obtain ⟨dN, hdN⟩ := root (Zc.toNat + 1) (by omega)
  obtain ⟨-, -, hN⟩ := relation H hc (show 2 ≤ Zc.toNat + 1 by omega) hdN
  have hZdN := Z_nonneg H (dN : L)
  have hcast : ((Zc.toNat + 1 : ℕ) : ℤ) = Zc + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Int.toNat_of_nonneg hZc0]
  rw [hcast] at hN

  set ZdN := Z S y (dN : L)
  have hkey : (Zc + 1) * ZdN = 2 * Zc := by linarith
  rcases lt_trichotomy ZdN 1 with hlt | heq | hgt
  · have : ZdN = 0 := by omega
    rw [this] at hkey; omega
  · rw [heq] at hkey; omega
  · nlinarith

theorem exists_evalAt_eq [IsAlgClosed L] {c : ↥A} (hc : Adm A ϖL E₀ c) : ∃ P ∈ S, P.evalAt (y : F) = (c : L) := by
  obtain ⟨-, hZ⟩ := Z_eq_one H hc
  by_contra hne
  push Not at hne
  have h0 : Z S y (c : L) = 0 := by
    unfold Z
    refine finsum_mem_of_eqOn_zero fun P hP => ?_
    by_contra h
    exact hne P hP ((ord_ysub_ne_zero_iff H c hc.mem hP).mp h)
  omega

theorem eq_of_evalAt_eq [IsAlgClosed L] {P Q : Place L F} (hP : P ∈ S) (hQ : Q ∈ S)
    (hPQ : P.evalAt (y : F) = Q.evalAt (y : F)) : P = Q := by
  classical
  obtain ⟨hA, hm, h0, cof⟩ := admissible_evalAt_y H hP
  set c : ↥A := ⟨P.evalAt (y : F), hA⟩ with hc
  have hadm : Adm A ϖL E₀ c := ⟨hm, h0, cof⟩
  obtain ⟨hfin, hZ⟩ := Z_eq_one H hadm
  by_contra hne
  have hPord : P.ord ((y : F) - algebraMap L F (c : L)) ≠ 0 := (ord_ysub_ne_zero_iff H c hm hP).mpr rfl
  have hQord : Q.ord ((y : F) - algebraMap L F (c : L)) ≠ 0 := (ord_ysub_ne_zero_iff H c hm hQ).mpr hPQ.symm
  have hP1 : 1 ≤ P.ord ((y : F) - algebraMap L F (c : L)) := by
    have := ord_ysub_nonneg H (c : L) hP; omega
  have hQ1 : 1 ≤ Q.ord ((y : F) - algebraMap L F (c : L)) := by
    have := ord_ysub_nonneg H (c : L) hQ; omega

  have hsum : Z S y (c : L) = ∑ R ∈ hfin.toFinset, R.ord ((y : F) - algebraMap L F (c : L)) := by
    unfold Z
    rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum]
  have hPmem : P ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]; exact ⟨hP, hPord⟩
  have hQmem : Q ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]; exact ⟨hQ, hQord⟩
  have hsub : ({P, Q} : Finset (Place L F)) ⊆ hfin.toFinset := by
    intro R hR
    rw [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl
    · exact hPmem
    · exact hQmem
  have hle : ∑ R ∈ ({P, Q} : Finset (Place L F)), R.ord ((y : F) - algebraMap L F (c : L)) ≤
      ∑ R ∈ hfin.toFinset, R.ord ((y : F) - algebraMap L F (c : L)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun R hR _ => by
      rw [Set.Finite.mem_toFinset] at hR
      exact ord_ysub_nonneg H (c : L) hR.1
  rw [Finset.sum_pair hne] at hle
  omega

theorem ord_sub_evalAt [IsAlgClosed L] {P : Place L F} (hP : P ∈ S) :
    P.ord ((y : F) - algebraMap L F (P.evalAt (y : F))) = 1 := by
  obtain ⟨hA, hm, h0, cof⟩ := admissible_evalAt_y H hP
  set c : ↥A := ⟨P.evalAt (y : F), hA⟩ with hc
  have hadm : Adm A ϖL E₀ c := ⟨hm, h0, cof⟩
  obtain ⟨hfin, hZ⟩ := Z_eq_one H hadm
  have hPord : P.ord ((y : F) - algebraMap L F (c : L)) ≠ 0 := (ord_ysub_ne_zero_iff H c hm hP).mpr rfl
  have hP1 : 1 ≤ P.ord ((y : F) - algebraMap L F (c : L)) := by
    have := ord_ysub_nonneg H (c : L) hP; omega
  have hsum : Z S y (c : L) = ∑ R ∈ hfin.toFinset, R.ord ((y : F) - algebraMap L F (c : L)) := by
    unfold Z
    rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum]
  have hPmem : P ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]; exact ⟨hP, hPord⟩
  have hle : P.ord ((y : F) - algebraMap L F (c : L)) ≤
      ∑ R ∈ hfin.toFinset, R.ord ((y : F) - algebraMap L F (c : L)) :=
    Finset.single_le_sum (fun R hR => by
      rw [Set.Finite.mem_toFinset] at hR
      exact ord_ysub_nonneg H (c : L) hR.1) hPmem
  show P.ord ((y : F) - algebraMap L F (c : L)) = 1
  omega

end Frame

end AlgebraicCurve.NodeAnnulusEngine.ZeroCount

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
    ∀ P Q : Place L F, P ∈ S → Q ∈ S →
      P.evalAt ((y : ↥𝒩₀) : F) = Q.evalAt ((y : ↥𝒩₀) : F) → P = Q := by
  have H : AlgebraicCurve.NodeAnnulusEngine.ZeroCount.ZH A R₁ R₂ x₁ x₂ S 𝒩 𝒩₀ ((ϖ : ↥C) : L) (hCmem ϖ ϖ.2) x y E₀ u :=
    ⟨hrat, h𝒩, hval, hord, h𝒩₀, hS, hϖ0, x_fst, x_snd, y_snd, y_fst, hu, hxy⟩
  intro P Q hP hQ hPQ
  exact AlgebraicCurve.NodeAnnulusEngine.ZeroCount.eq_of_evalAt_eq H hP hQ hPQ

end S_AlgebraicCurve_NodeAnnulusEngine_eq_of_mem_of_evalAt_eq
end P2MW
export P2MW.S_AlgebraicCurve_NodeAnnulusEngine_eq_of_mem_of_evalAt_eq (solution)
