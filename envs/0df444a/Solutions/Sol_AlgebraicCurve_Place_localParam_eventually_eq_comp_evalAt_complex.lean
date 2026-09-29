-- Prove2me | solution 1 for AlgebraicCurve.Place.localParam_eventually_eq_comp_evalAt_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/91e00f6a-417b-5ce8-9e38-5144557f8090

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex.AlgebraicCurve Filter Set Metric Topology"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.ord Place.ord_zero Place.ord_mul Place.ord_inv IsCurveOver IsCurveOver.finiteResidue Place.evalAt Place.evalAt_one"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe adicValuation_coe_eq_one_iff ord ord_zero ord_mul ord_inv exists_unit_mul_zpow algebraMap_mem' toValuationSubring IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt evalAt_one"
namespace BranchUniqueness
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

section Prelim

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adicValuation_le_one_of_mem (v : Place K F) {x : F} (hx : x ∈ v.toValuationSubring) :
    v.adicValuation x ≤ 1 := by
  have h := (v.adicValuation_coe ⟨x, hx⟩).trans_le
    (v.heightOneSpectrum.intValuation_le_one ⟨x, hx⟩)
  simpa using h

theorem adicValuation_eq_exp_neg_ord (v : Place K F) {f : F} (hf : f ≠ 0) :
    v.adicValuation f = WithZero.exp (-v.ord f) := by
  unfold Place.ord
  rw [neg_neg, WithZero.exp_log (v.adicValuation_ne_zero hf)]

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  by_cases hf0 : f = 0
  · simp [hf0]
  have h := adicValuation_le_one_of_mem v hf
  rw [adicValuation_eq_exp_neg_ord v hf0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

theorem ord_pos_of_mem_maximalIdeal (v : Place K F) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring)
    (hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring) :
    0 < v.ord f := by
  have hle : v.adicValuation f ≤ 1 := adicValuation_le_one_of_mem v hf
  have hne : v.adicValuation f ≠ 1 := by
    intro h1
    have hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring) :=
      (v.adicValuation_coe_eq_one_iff ⟨f, hf⟩).mp h1
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hmax) hu
  have hlt : v.adicValuation f < 1 := lt_of_le_of_ne hle hne
  rw [adicValuation_eq_exp_neg_ord v hf0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  omega

theorem residue_eq_zero_of_ord_pos (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : 0 < v.ord f) :
    IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
  intro hu
  have h1 : v.adicValuation f = 1 := (v.adicValuation_coe_eq_one_iff ⟨f, hf⟩).mpr hu
  by_cases hf0 : f = 0
  · subst hf0; simp at h
  rw [adicValuation_eq_exp_neg_ord v hf0, ← WithZero.exp_zero] at h1
  have := WithZero.exp_injective h1
  omega

theorem isRational_of_isCurveOver [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem evalAt_algebraMap (v : Place K F) (c : K) : v.evalAt (algebraMap K F c) = c := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' c)]
  have : (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring c := Subtype.ext (v.coe_algebraMap c).symm
  rw [this]
  exact v.residueInv_algebraMap c

theorem residue_algebraMap (v : Place K F) (c : K) :
    IsLocalRing.residue v.toValuationSubring ⟨algebraMap K F c, v.algebraMap_mem' c⟩
      = algebraMap K v.ResidueField c := by
  have : (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring c := Subtype.ext (v.coe_algebraMap c).symm
  rw [this]; rfl

theorem evalAt_sub_algebraMap (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (c : K) :
    v.evalAt (f - algebraMap K F c) = v.evalAt f - c := by
  have hc : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hfc : f - algebraMap K F c ∈ v.toValuationSubring := sub_mem hf hc
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv hfc, map_sub, v.algebraMap_evalAt hv hf, ← residue_algebraMap v c,
    ← map_sub]
  rfl

theorem evalAt_mul (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv (mul_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

theorem evalAt_eq_zero_of_ord_pos (v : Place K F) {f : F} (hf0 : f ≠ 0) (h : 0 < v.ord f) :
    v.evalAt f = 0 := by
  have hf : f ∈ v.toValuationSubring := mem_of_ord_nonneg v hf0 h.le
  rw [v.evalAt_of_mem hf, residue_eq_zero_of_ord_pos v hf h, ← map_zero (algebraMap K _),
    v.residueInv_algebraMap]

theorem ord_pos_of_evalAt_eq_zero (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) (h0 : v.evalAt f = 0) : 0 < v.ord f := by
  refine ord_pos_of_mem_maximalIdeal v hf0 hf ?_
  rw [← IsLocalRing.residue_eq_zero_iff, ← v.algebraMap_evalAt hv hf, h0, map_zero]

theorem evalAt_eq_of_ord_sub_algebraMap_eq_one (w : Place K F) (hw : w.IsRational) (t : F) (c : K)
    (h : w.ord (t - algebraMap K F c) = 1) : w.evalAt t = c := by
  have hne : t - algebraMap K F c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact zero_ne_one h
  have hmem : t - algebraMap K F c ∈ w.toValuationSubring := mem_of_ord_nonneg w hne (by omega)
  have ht : t ∈ w.toValuationSubring := by
    simpa using add_mem hmem (w.algebraMap_mem' c)
  have h0 : w.evalAt (t - algebraMap K F c) = 0 := evalAt_eq_zero_of_ord_pos w hne (by omega)
  rw [evalAt_sub_algebraMap w hw ht c] at h0
  exact sub_eq_zero.mp h0

theorem mem_of_ord_sub_algebraMap_eq_one (w : Place K F) (t : F) (c : K)
    (h : w.ord (t - algebraMap K F c) = 1) : t ∈ w.toValuationSubring := by
  have hne : t - algebraMap K F c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact zero_ne_one h
  have hmem : t - algebraMap K F c ∈ w.toValuationSubring := mem_of_ord_nonneg w hne (by omega)
  simpa using add_mem hmem (w.algebraMap_mem' c)

theorem ne_zero_of_ord_eq_one (w : Place K F) {t : F} (h : w.ord t = 1) : t ≠ 0 := by
  intro h0; rw [h0, Place.ord_zero] at h; exact zero_ne_one h

end Prelim

section Prelim2

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.evalAt f = 0 := dif_neg hf

theorem evalAt_zero (v : Place K F) : v.evalAt (0 : F) = 0 := by
  simpa using evalAt_algebraMap v (0 : K)

theorem evalAt_add (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem evalAt_eq_inv_evalAt_inv (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f⁻¹ ∈ v.toValuationSubring) : v.evalAt f = (v.evalAt f⁻¹)⁻¹ := by
  rcases (ord_nonneg_of_mem v hf).eq_or_lt with h0 | hpos
  ·
    have hf' : f ∈ v.toValuationSubring :=
      mem_of_ord_nonneg v hf0 (by rw [Place.ord_inv] at h0; omega)
    have h1 : v.evalAt f * v.evalAt f⁻¹ = 1 := by
      rw [← evalAt_mul v hv hf' hf, mul_inv_cancel₀ hf0, Place.evalAt_one]
    exact eq_inv_of_mul_eq_one_left h1
  ·
    have hnot : f ∉ v.toValuationSubring := by
      intro hmem
      have := ord_nonneg_of_mem v hmem
      rw [Place.ord_inv] at hpos; omega
    rw [evalAt_of_not_mem v hnot, evalAt_eq_zero_of_ord_pos v (inv_ne_zero hf0) hpos, inv_zero]

theorem eq_of_forall_ord_eq {v w : Place K F} (h : ∀ f : F, f ≠ 0 → v.ord f = w.ord f) :
    v = w := by
  apply Place.ext
  refine SetLike.ext fun f => ?_
  by_cases hf : f = 0
  · subst hf; simp
  exact ⟨fun hm => mem_of_ord_nonneg w hf (h f hf ▸ ord_nonneg_of_mem v hm),
    fun hm => mem_of_ord_nonneg v hf ((h f hf).symm ▸ ord_nonneg_of_mem w hm)⟩

end Prelim2

section Param

variable {F : Type*} [Field F] [Algebra ℂ F]

def Pkg (γ : ℂ → Place ℂ F) (U : Set ℂ) : Prop :=
  ∀ f : F, f ≠ 0 → ∀ z ∈ U,
    MeromorphicAt (fun u : ℂ => (γ u).evalAt f) z ∧
    meromorphicOrderAt (fun u : ℂ => (γ u).evalAt f) z = ((γ z).ord f : WithTop ℤ) ∧
    (0 ≤ (γ z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ u).evalAt f) z)

variable {γ : ℂ → Place ℂ F} {U : Set ℂ} {z : ℂ}

theorem Pkg.analyticAt (hP : Pkg γ U) (hz : z ∈ U) {g : F} (hg : g ∈ (γ z).toValuationSubring) :
    AnalyticAt ℂ (fun u : ℂ => (γ u).evalAt g) z := by
  by_cases hg0 : g = 0
  · subst hg0
    simp only [evalAt_zero]
    exact analyticAt_const
  exact (hP g hg0 z hz).2.2 (ord_nonneg_of_mem _ hg)

theorem Pkg.eventually_mem (hP : Pkg γ U) (hU : U ∈ 𝓝 z) {g : F}
    (hg : g ∈ (γ z).toValuationSubring) : ∀ᶠ u in 𝓝 z, g ∈ (γ u).toValuationSubring := by
  by_cases hg0 : g = 0
  · exact Eventually.of_forall fun u => by rw [hg0]; exact zero_mem _
  filter_upwards [(hP.analyticAt (mem_of_mem_nhds hU) hg).eventually_analyticAt, hU]
    with u hu huU
  have h := (hP g hg0 u huU).2.1
  have hnn : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun u : ℂ => (γ u).evalAt g) u :=
    hu.meromorphicOrderAt_nonneg
  rw [h] at hnn
  exact mem_of_ord_nonneg _ hg0 (by exact_mod_cast hnn)

theorem Pkg.meromorphicOrderAt_sub_const [IsCurveOver ℂ F] (hP : Pkg γ U) (hU : U ∈ 𝓝 z) {t : F}
    (htm : t ∈ (γ z).toValuationSubring) (c : ℂ) (htc : t - algebraMap ℂ F c ≠ 0) :
    meromorphicOrderAt (fun u : ℂ => (γ u).evalAt t - c) z
      = ((γ z).ord (t - algebraMap ℂ F c) : WithTop ℤ) := by
  rw [← (hP _ htc z (mem_of_mem_nhds hU)).2.1]
  apply meromorphicOrderAt_congr
  refine ((hP.eventually_mem hU htm).mono fun u hu => ?_).filter_mono nhdsWithin_le_nhds
  exact (evalAt_sub_algebraMap _ (isRational_of_isCurveOver _) hu c).symm

omit [Algebra ℂ F] in

theorem evalAt_decomp {K : Type*} [Field K] [Algebra K F] (w : Place K F) (hw : w.IsRational)
    {t f₁ : F} (ht : t ∈ w.toValuationSubring) (hf₁ : f₁ ∈ w.toValuationSubring) (c z₀ : K) :
    w.evalAt (algebraMap K F c + (t - algebraMap K F z₀) * f₁)
      = c + (w.evalAt t - z₀) * w.evalAt f₁ := by
  have h1 : t - algebraMap K F z₀ ∈ w.toValuationSubring := sub_mem ht (w.algebraMap_mem' z₀)
  rw [evalAt_add w hw (w.algebraMap_mem' c) (mul_mem h1 hf₁), evalAt_algebraMap,
    evalAt_mul w hw h1 hf₁, evalAt_sub_algebraMap w hw ht]

end Param

section Main

variable (F : Type*) [Field F] [Algebra ℂ F]

structure Setup where

  γ : ℂ → Place ℂ F

  γ' : ℂ → Place ℂ F

  t : F

  U : Set ℂ
  U' : Set ℂ

  z₀ : ℂ
  z₀' : ℂ
  hU : U ∈ 𝓝 z₀
  hU' : U' ∈ 𝓝 z₀'
  h₀ : γ' z₀' = γ z₀
  ht : ∀ z ∈ U, (γ z).ord (t - algebraMap ℂ F z) = 1
  hγ : Pkg γ U
  hγ' : Pkg γ' U'

variable {F} [IsCurveOver ℂ F] (S : Setup F)

namespace Setup

def h (u : ℂ) : ℂ := (S.γ' u).evalAt S.t

def D (f : F) (u : ℂ) : ℂ := (S.γ' u).evalAt f - (S.γ (S.h u)).evalAt f

theorem isRational (w : Place ℂ F) : w.IsRational := isRational_of_isCurveOver w

omit [IsCurveOver ℂ F] in
theorem z₀_mem : S.z₀ ∈ S.U := mem_of_mem_nhds S.hU

omit [IsCurveOver ℂ F] in
theorem z₀'_mem : S.z₀' ∈ S.U' := mem_of_mem_nhds S.hU'

omit [IsCurveOver ℂ F] in
theorem sub_ne_zero : S.t - algebraMap ℂ F S.z₀ ≠ 0 :=
  ne_zero_of_ord_eq_one _ (S.ht S.z₀ S.z₀_mem)

omit [IsCurveOver ℂ F] in
theorem t_mem : S.t ∈ (S.γ S.z₀).toValuationSubring :=
  mem_of_ord_sub_algebraMap_eq_one _ _ _ (S.ht S.z₀ S.z₀_mem)

omit [IsCurveOver ℂ F] in
theorem t_mem' : S.t ∈ (S.γ' S.z₀').toValuationSubring := by rw [S.h₀]; exact S.t_mem

theorem h_self : S.h S.z₀' = S.z₀ := by
  unfold h; rw [S.h₀]
  exact evalAt_eq_of_ord_sub_algebraMap_eq_one _ (isRational _) _ _ (S.ht S.z₀ S.z₀_mem)

omit [IsCurveOver ℂ F] in
theorem analyticAt_h : AnalyticAt ℂ S.h S.z₀' := S.hγ'.analyticAt S.z₀'_mem S.t_mem'

theorem tendsto_h : Tendsto S.h (𝓝 S.z₀') (𝓝 S.z₀) := by
  simpa only [S.h_self] using S.analyticAt_h.continuousAt.tendsto

theorem order_h : meromorphicOrderAt (fun u : ℂ => S.h u - S.z₀) S.z₀' = 1 := by
  have := S.hγ'.meromorphicOrderAt_sub_const S.hU' S.t_mem' S.z₀ S.sub_ne_zero
  rw [S.h₀, S.ht S.z₀ S.z₀_mem] at this
  exact_mod_cast this

omit [IsCurveOver ℂ F] in

theorem eventually_mem' {g : F} (hg : g ∈ (S.γ S.z₀).toValuationSubring) :
    ∀ᶠ u in 𝓝 S.z₀', g ∈ (S.γ' u).toValuationSubring :=
  S.hγ'.eventually_mem S.hU' (by rw [S.h₀]; exact hg)

theorem eventually_mem {g : F} (hg : g ∈ (S.γ S.z₀).toValuationSubring) :
    ∀ᶠ u in 𝓝 S.z₀', g ∈ (S.γ (S.h u)).toValuationSubring :=
  S.tendsto_h.eventually (S.hγ.eventually_mem S.hU hg)

theorem eventually_h_mem : ∀ᶠ u in 𝓝 S.z₀', S.h u ∈ S.U := S.tendsto_h.eventually S.hU

theorem analyticAt_D {f : F} (hf : f ∈ (S.γ S.z₀).toValuationSubring) :
    AnalyticAt ℂ (S.D f) S.z₀' := by
  have h1 : AnalyticAt ℂ (fun u : ℂ => (S.γ' u).evalAt f) S.z₀' :=
    S.hγ'.analyticAt S.z₀'_mem (by rw [S.h₀]; exact hf)
  have h2 : AnalyticAt ℂ (fun z : ℂ => (S.γ z).evalAt f) (S.h S.z₀') := by
    rw [S.h_self]; exact S.hγ.analyticAt S.z₀_mem hf
  exact h1.sub (h2.comp S.analyticAt_h)

theorem decomp {f : F} (hf : f ∈ (S.γ S.z₀).toValuationSubring) :
    ∃ f₁ ∈ (S.γ S.z₀).toValuationSubring,
      f = algebraMap ℂ F ((S.γ S.z₀).evalAt f) + (S.t - algebraMap ℂ F S.z₀) * f₁ := by
  set w₀ := S.γ S.z₀
  set c := w₀.evalAt f
  refine ⟨(f - algebraMap ℂ F c) / (S.t - algebraMap ℂ F S.z₀), ?_, ?_⟩
  · by_cases hfc : f - algebraMap ℂ F c = 0
    · rw [hfc, zero_div]; exact zero_mem _
    have hpos : 0 < w₀.ord (f - algebraMap ℂ F c) := by
      refine ord_pos_of_evalAt_eq_zero _ (isRational _) hfc (sub_mem hf (w₀.algebraMap_mem' c)) ?_
      rw [evalAt_sub_algebraMap _ (isRational _) hf, sub_self]
    refine mem_of_ord_nonneg _ (div_ne_zero hfc S.sub_ne_zero) ?_
    rw [div_eq_mul_inv, Place.ord_mul _ hfc (inv_ne_zero S.sub_ne_zero), Place.ord_inv,
      S.ht S.z₀ S.z₀_mem]
    omega
  · rw [mul_div_cancel₀ _ S.sub_ne_zero]; ring

theorem D_step {f : F} (hf : f ∈ (S.γ S.z₀).toValuationSubring) :
    ∃ f₁ ∈ (S.γ S.z₀).toValuationSubring,
      S.D f =ᶠ[𝓝 S.z₀'] fun u => (S.h u - S.z₀) * S.D f₁ u := by
  obtain ⟨f₁, hf₁, hdec⟩ := S.decomp hf
  refine ⟨f₁, hf₁, ?_⟩
  filter_upwards [S.eventually_mem' S.t_mem, S.eventually_mem' hf₁, S.eventually_mem S.t_mem,
    S.eventually_mem hf₁, S.eventually_h_mem] with u ht' hf₁' ht hf₁u hhu
  have hval : (S.γ (S.h u)).evalAt S.t = S.h u :=
    evalAt_eq_of_ord_sub_algebraMap_eq_one _ (isRational _) _ _ (S.ht _ hhu)
  unfold D
  conv_lhs => rw [hdec]
  rw [evalAt_decomp _ (isRational _) ht' hf₁', evalAt_decomp _ (isRational _) ht hf₁u, hval]
  unfold h
  ring

omit [IsCurveOver ℂ F] in
theorem meromorphicAt_h_sub : MeromorphicAt (fun u : ℂ => S.h u - S.z₀) S.z₀' :=
  (S.analyticAt_h.sub analyticAt_const).meromorphicAt

theorem le_order (N : ℕ) : ∀ {f : F}, f ∈ (S.γ S.z₀).toValuationSubring →
    ((N : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (S.D f) S.z₀' := by
  induction N with
  | zero =>
    intro f hf
    simpa using (S.analyticAt_D hf).meromorphicOrderAt_nonneg
  | succ N ih =>
    intro f hf
    obtain ⟨f₁, hf₁, heq⟩ := S.D_step hf
    rw [meromorphicOrderAt_congr (heq.filter_mono nhdsWithin_le_nhds),
      show (fun u => (S.h u - S.z₀) * S.D f₁ u) = (fun u => S.h u - S.z₀) * S.D f₁ from rfl,
      meromorphicOrderAt_mul S.meromorphicAt_h_sub (S.analyticAt_D hf₁).meromorphicAt, S.order_h]
    have := ih hf₁
    calc (((N + 1 : ℕ) : ℤ) : WithTop ℤ) = 1 + ((N : ℤ) : WithTop ℤ) := by
          push_cast; rw [add_comm]
      _ ≤ 1 + meromorphicOrderAt (S.D f₁) S.z₀' := by
          rw [add_comm 1, add_comm 1]; exact add_le_add_left this 1

theorem order_eq_top {f : F} (hf : f ∈ (S.γ S.z₀).toValuationSubring) :
    meromorphicOrderAt (S.D f) S.z₀' = ⊤ := by
  by_contra hne
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  have h := S.le_order (m.toNat + 1) hf
  rw [← hm, WithTop.coe_le_coe] at h
  omega

theorem eventuallyEq_of_mem {f : F} (hf : f ∈ (S.γ S.z₀).toValuationSubring) :
    ∀ᶠ u in 𝓝[≠] S.z₀', (S.γ' u).evalAt f = (S.γ (S.h u)).evalAt f :=
  (meromorphicOrderAt_eq_top_iff.mp (S.order_eq_top hf)).mono fun _ hu => sub_eq_zero.mp hu

theorem eventuallyEq {f : F} (hf : f ≠ 0) :
    ∀ᶠ u in 𝓝[≠] S.z₀', (S.γ' u).evalAt f = (S.γ (S.h u)).evalAt f := by
  rcases (S.γ S.z₀).toValuationSubring.mem_or_inv_mem f with hmem | hinv
  · exact S.eventuallyEq_of_mem hmem
  filter_upwards [S.eventuallyEq_of_mem hinv,
    (S.eventually_mem' hinv).filter_mono nhdsWithin_le_nhds,
    (S.eventually_mem hinv).filter_mono nhdsWithin_le_nhds] with u h1 h2 h3
  rw [evalAt_eq_inv_evalAt_inv _ (isRational _) hf h2,
    evalAt_eq_inv_evalAt_inv _ (isRational _) hf h3, h1]

theorem order_eq_top' {f : F} (hf : f ≠ 0) : meromorphicOrderAt (S.D f) S.z₀' = ⊤ :=
  meromorphicOrderAt_eq_top_iff.mpr ((S.eventuallyEq hf).mono fun _ hu => sub_eq_zero.mpr hu)

theorem analyticOrderAt_eq_one {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x)
    (h1 : meromorphicOrderAt g x = 1) : analyticOrderAt g x = 1 := by
  rw [hg.meromorphicOrderAt_eq] at h1
  induction ha : analyticOrderAt g x using ENat.recTopCoe with
  | top => rw [ha] at h1; simp at h1
  | coe n =>
    rw [ha] at h1
    have : ((n : ℤ) : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) := by simpa using h1
    have hn : (n : ℤ) = 1 := WithTop.coe_eq_coe.mp this
    have : n = 1 := by exact_mod_cast hn
    subst this; rfl

theorem deriv_h_ne_zero : deriv S.h S.z₀' ≠ 0 := by
  set g : ℂ → ℂ := fun u => S.h u - S.z₀ with hg_def
  have hg : AnalyticAt ℂ g S.z₀' := S.analyticAt_h.sub analyticAt_const
  have h1 : analyticOrderAt g S.z₀' = 0 + 1 := by
    rw [zero_add]; exact analyticOrderAt_eq_one hg S.order_h
  have h2 : analyticOrderAt (deriv g) S.z₀' = (0 : ℕ) := analyticOrderAt_deriv_of_pos hg h1
  have h3 : deriv g S.z₀' ≠ 0 := by
    have := (hg.deriv).analyticOrderAt_eq_zero.mp (by exact_mod_cast h2)
    exact this
  simpa [hg_def] using h3

theorem eventually_good : ∀ᶠ u in 𝓝 S.z₀',
    u ∈ S.U' ∧ S.h u ∈ S.U ∧ AnalyticAt ℂ S.h u ∧ deriv S.h u ≠ 0 := by
  filter_upwards [S.hU', S.eventually_h_mem, S.analyticAt_h.eventually_analyticAt,
    S.analyticAt_h.deriv.continuousAt.eventually_ne S.deriv_h_ne_zero] with u h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

omit [IsCurveOver ℂ F] in

theorem meromorphicAt_D {f : F} (hf : f ≠ 0) {u : ℂ} (hu' : u ∈ S.U') (hu : S.h u ∈ S.U)
    (han : AnalyticAt ℂ S.h u) : MeromorphicAt (S.D f) u :=
  (S.hγ' f hf u hu').1.sub ((S.hγ f hf (S.h u) hu).1.comp_analyticAt han)

omit [IsCurveOver ℂ F] in

theorem ord_eq_of_order_eq_top {f : F} (hf : f ≠ 0) {u : ℂ} (hu' : u ∈ S.U') (hu : S.h u ∈ S.U)
    (han : AnalyticAt ℂ S.h u) (hder : deriv S.h u ≠ 0)
    (htop : meromorphicOrderAt (S.D f) u = ⊤) : (S.γ' u).ord f = (S.γ (S.h u)).ord f := by
  have hev : (fun v : ℂ => (S.γ' v).evalAt f)
      =ᶠ[𝓝[≠] u] (fun z : ℂ => (S.γ z).evalAt f) ∘ S.h :=
    (meromorphicOrderAt_eq_top_iff.mp htop).mono fun _ hv => sub_eq_zero.mp hv
  have h := meromorphicOrderAt_congr hev
  rw [meromorphicOrderAt_comp_of_deriv_ne_zero han hder, (S.hγ' f hf u hu').2.1,
    (S.hγ f hf (S.h u) hu).2.1] at h
  exact_mod_cast h

theorem main : ∀ᶠ u in 𝓝 S.z₀', S.γ' u = S.γ ((S.γ' u).evalAt S.t) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp S.eventually_good
  have hW : ball S.z₀' r ∈ 𝓝 S.z₀' := ball_mem_nhds _ hr
  filter_upwards [hW] with u hu
  obtain ⟨hu', huU, han, hder⟩ := hball u hu
  refine eq_of_forall_ord_eq fun f hf => S.ord_eq_of_order_eq_top hf hu' huU han hder ?_

  by_contra hne
  have hOn : MeromorphicOn (S.D f) (ball S.z₀' r) := fun v hv =>
    S.meromorphicAt_D hf (hball v hv).1 (hball v hv).2.1 (hball v hv).2.2.1
  exact hOn.meromorphicOrderAt_ne_top_of_isPreconnected (convex_ball _ _).isPreconnected hu
    (mem_ball_self hr) hne (S.order_eq_top' hf)

end Setup

end Main

end AlgebraicCurve.Place.BranchUniqueness

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex.AlgebraicCurve AlgebraicCurve.Place.BranchUniqueness in
open scoped Topology in

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    (γ γ' : ℂ → Place ℂ F) (t : F) (U U' : Set ℂ) (z₀ z₀' : ℂ)
    (hU : U ∈ 𝓝 z₀) (hU' : U' ∈ 𝓝 z₀') (h₀ : γ' z₀' = γ z₀)
    (ht : ∀ z ∈ U, (γ z).ord (t - algebraMap ℂ F z) = 1)
    (hγ : ∀ f : F, f ≠ 0 → ∀ z ∈ U,
        MeromorphicAt (fun u : ℂ => (γ u).evalAt f) z ∧
        meromorphicOrderAt (fun u : ℂ => (γ u).evalAt f) z = ((γ z).ord f : WithTop ℤ) ∧
        (0 ≤ (γ z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ u).evalAt f) z))
    (hγ' : ∀ f : F, f ≠ 0 → ∀ z ∈ U',
        MeromorphicAt (fun u : ℂ => (γ' u).evalAt f) z ∧
        meromorphicOrderAt (fun u : ℂ => (γ' u).evalAt f) z = ((γ' z).ord f : WithTop ℤ) ∧
        (0 ≤ (γ' z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ' u).evalAt f) z)) :
    ∀ᶠ z in 𝓝 z₀', γ' z = γ ((γ' z).evalAt t) :=
  Setup.main ⟨γ, γ', t, U, U', z₀, z₀', hU, hU', h₀, ht, hγ, hγ'⟩

end S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex
end P2MW
export P2MW.S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex (solution)
