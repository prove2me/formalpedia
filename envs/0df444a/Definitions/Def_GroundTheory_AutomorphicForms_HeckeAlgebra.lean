-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
-- name    : GroundTheory_AutomorphicForms_HeckeAlgebra
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:07.410871+00:00
-- url     : https://prove2.me/theorems/357c6962-cfc7-4be8-95d1-bf0ed98c2c58
-- title:
--   Hecke Algebra
-- statement:
--   Definitions and structural lemmas for Hecke Algebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeAlgebra.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarCosets
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Theorems.Thm_GroundTheory_Automorphic_exists_forall_mul_left
import Theorems.Thm_GroundTheory_Automorphic_exists_forall_mul_left_mul_right
import Theorems.Thm_GroundTheory_Automorphic_exists_forall_mul_right
import Theorems.Thm_GroundTheory_Automorphic_integral_eq_smul_finsum_coset
import Theorems.Thm_GroundTheory_Automorphic_isCompact_inf_left
import Theorems.Thm_GroundTheory_Automorphic_isCompact_isOpen_fiber
import Theorems.Thm_GroundTheory_Automorphic_mem_locallyConstantCompactSupport_of_forall_mul_right
import Theorems.Thm_GroundTheory_Automorphic_mem_smoothVectors_iff
import Theorems.Thm_GroundTheory_Automorphic_range_finite_of_mem_locallyConstantCompactSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
section Cosets
variable (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
theorem finite_image_mk_of_isCompact (K : OpenSubgroup G) {A : Set G} (hA : IsCompact A) :
    (QuotientGroup.mk '' A : Set (G ⧸ (K : Subgroup G))).Finite :=
  (hA.image QuotientGroup.continuous_mk).finite_of_discrete
theorem integral_eq_smul_sum_coset (K : OpenSubgroup G) (hKc : IsCompact (K : Set G))
    {A : Set G} (hA : IsCompact A) {f : G → ℂ} (hfA : ∀ y, f y ≠ 0 → y ∈ A)
    (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    ∫ g, f g ∂μ = μ.real (K : Set G) •
      ∑ p ∈ (finite_image_mk_of_isCompact K hA).toFinset, f p.out := by
  have hf : HasCompactSupport f :=
    HasCompactSupport.intro hA fun y hy => by
      by_contra h
      exact hy (hfA y h)
  rw [integral_eq_smul_finsum_coset μ K hKc hf hK,
    finsum_eq_sum_of_support_subset _ (s := (finite_image_mk_of_isCompact K hA).toFinset)]
  intro p hp
  rw [Set.Finite.coe_toFinset]
  exact ⟨p.out, hfA _ hp, QuotientGroup.out_eq' p⟩
theorem integral_integral_swap_of_coset (K : OpenSubgroup G) (hKc : IsCompact (K : Set G))
    {A B : Set G} (hA : IsCompact A) (hB : IsCompact B) {F : G → G → ℂ}
    (hF : ∀ y z, F y z ≠ 0 → y ∈ A ∧ z ∈ B)
    (h₁ : ∀ y z, ∀ k ∈ K, F (y * k) z = F y z) (h₂ : ∀ y z, ∀ k ∈ K, F y (z * k) = F y z) :
    ∫ y, ∫ z, F y z ∂μ ∂μ = ∫ z, ∫ y, F y z ∂μ ∂μ := by
  set SA := (finite_image_mk_of_isCompact K hA).toFinset
  set SB := (finite_image_mk_of_isCompact K hB).toFinset
  set c := μ.real (K : Set G)
  have e₁ : ∀ y, ∫ z, F y z ∂μ = c • ∑ q ∈ SB, F y q.out := fun y =>
    integral_eq_smul_sum_coset μ K hKc hB (fun z hz => (hF y z hz).2) (fun z k hk => h₂ y z k hk)
  have e₂ : ∀ z, ∫ y, F y z ∂μ = c • ∑ p ∈ SA, F p.out z := fun z =>
    integral_eq_smul_sum_coset μ K hKc hA (fun y hy => (hF y z hy).1) (fun y k hk => h₁ y z k hk)
  have sA : ∀ y, c • ∑ q ∈ SB, F y q.out ≠ 0 → y ∈ A := by
    intro y hy
    by_contra hyA
    apply hy
    rw [Finset.sum_eq_zero, smul_zero]
    intro q _
    by_contra h
    exact hyA (hF _ _ h).1
  have sB : ∀ z, c • ∑ p ∈ SA, F p.out z ≠ 0 → z ∈ B := by
    intro z hz
    by_contra hzB
    apply hz
    rw [Finset.sum_eq_zero, smul_zero]
    intro p _
    by_contra h
    exact hzB (hF _ _ h).2
  have iA : ∀ y, ∀ k ∈ K, c • ∑ q ∈ SB, F (y * k) q.out = c • ∑ q ∈ SB, F y q.out :=
    fun y k hk => by simp only [h₁ y _ k hk]
  have iB : ∀ z, ∀ k ∈ K, c • ∑ p ∈ SA, F p.out (z * k) = c • ∑ p ∈ SA, F p.out z :=
    fun z k hk => by simp only [h₂ _ z k hk]
  simp_rw [e₁, e₂]
  rw [integral_eq_smul_sum_coset μ K hKc hA sA iA, integral_eq_smul_sum_coset μ K hKc hB sB iB]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
end Cosets
section Convolution
variable (μ : Measure G)
def groupConv (f₁ f₂ : G → ℂ) (x : G) : ℂ := ∫ y, f₁ y * f₂ (y⁻¹ * x) ∂μ
def ltrans (g : G) (f : G → ℂ) : G → ℂ := fun x => f (g⁻¹ * x)
omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
theorem ltrans_apply (g : G) (f : G → ℂ) (x : G) : ltrans g f x = f (g⁻¹ * x) := rfl
omit [MeasurableSpace G] [BorelSpace G] in

theorem ltrans_mem (g : G) {f : G → ℂ} (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ) :
    ltrans g f ∈ locallyConstantCompactSupport G ℂ ℂ :=
  ⟨hf.1.comp_continuous (continuous_const.mul continuous_id),
    hf.2.comp_homeomorph (Homeomorph.mulLeft g⁻¹)⟩
variable {μ}
theorem groupConv_mul_right {f₁ f₂ : G → ℂ} {k : G} (hk : ∀ g, f₂ (g * k) = f₂ g) (x : G) :
    groupConv μ f₁ f₂ (x * k) = groupConv μ f₁ f₂ x := by
  simp only [groupConv, ← mul_assoc, hk]
variable (μ) in

theorem groupConv_mem [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {f₁ f₂ : G → ℂ} (hf₁ : f₁ ∈ locallyConstantCompactSupport G ℂ ℂ)
    (hf₂ : f₂ ∈ locallyConstantCompactSupport G ℂ ℂ) :
    groupConv μ f₁ f₂ ∈ locallyConstantCompactSupport G ℂ ℂ := by
  obtain ⟨K, -, hK⟩ := exists_forall_mul_right hf₂
  refine mem_locallyConstantCompactSupport_of_forall_mul_right K ?_ fun x k hk =>
    groupConv_mul_right (fun g => hK g k hk) x
  refine HasCompactSupport.intro (hf₁.2.mul hf₂.2) fun x hx => ?_
  have : ∀ y, f₁ y * f₂ (y⁻¹ * x) = 0 := by
    intro y
    by_contra h
    apply hx
    have h' := mul_ne_zero_iff.1 h
    exact ⟨y, subset_tsupport _ h'.1, y⁻¹ * x, subset_tsupport _ h'.2, mul_inv_cancel_left y x⟩
  simp only [groupConv, this, integral_zero]
omit [IsTopologicalGroup G] in

theorem integrable_mul_of_mem [IsFiniteMeasureOnCompacts μ] {f : G → ℂ}
    (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ) {h : G → ℂ} (hh : Continuous h) :
    Integrable (fun g => f g * h g) μ :=
  (hf.1.continuous.mul hh).integrable_of_hasCompactSupport (hf.2.mul_right (f' := h))
end Convolution
section Action
variable (μ : Measure G) {V : Type*} [AddCommGroup V] [Module ℂ V]
def heckeAct (ρ : Representation ℂ G V) (f : G → ℂ) (v : V) : V :=
  ∑ᶠ w : V, ((μ.real {g | f g • ρ g v = w} : ℝ) : ℂ) • w
variable {μ} {ρ : Representation ℂ G V}
omit [MeasurableSpace G] [BorelSpace G] in

theorem isLocallyConstant_orbit {v : V} (hv : v ∈ smoothVectors ρ) :
    IsLocallyConstant fun g => ρ g v := by
  refine (IsLocallyConstant.iff_exists_open (fun g => ρ g v)).2 fun g =>
    ⟨g • (stabilizerOf ρ v : Set G), hv.smul g, Set.mem_smul_set.2 ⟨1, one_mem (stabilizerOf ρ v), by simp⟩, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  simp only [smul_eq_mul, map_mul, Module.End.mul_apply, mem_stabilizerOf.1 hs]
omit [MeasurableSpace G] [BorelSpace G] in

theorem continuous_dual_orbit {v : V} (hv : v ∈ smoothVectors ρ) (φ : Module.Dual ℂ V) :
    Continuous fun g => φ (ρ g v) :=
  ((isLocallyConstant_orbit hv).comp φ).continuous
omit [MeasurableSpace G] [BorelSpace G] in

theorem smul_orbit_mem {f : G → ℂ} (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ) {v : V}
    (hv : v ∈ smoothVectors ρ) :
    (fun g => f g • ρ g v) ∈ locallyConstantCompactSupport G ℂ V :=
  ⟨hf.1.comp₂ (isLocallyConstant_orbit hv) (fun a b => a • b), hf.2.smul_right⟩
omit [IsTopologicalGroup G] [BorelSpace G] in

theorem heckeAct_eq_sum {f : G → ℂ} {v : V} (hfin : (range fun g => f g • ρ g v).Finite) :
    heckeAct μ ρ f v = ∑ w ∈ hfin.toFinset, ((μ.real {g | f g • ρ g v = w} : ℝ) : ℂ) • w := by
  refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
  rw [Set.Finite.coe_toFinset]
  by_contra h
  apply hw
  have : {g | f g • ρ g v = w} = ∅ := by
    ext g
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    exact fun hg => h ⟨g, hg⟩
  simp [this]
variable (μ) in

theorem dual_heckeAct [IsFiniteMeasureOnCompacts μ] {f : G → ℂ}
    (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ) {v : V} (hv : v ∈ smoothVectors ρ)
    (φ : Module.Dual ℂ V) :
    φ (heckeAct μ ρ f v) = ∫ g, f g * φ (ρ g v) ∂μ := by
  have hF := smul_orbit_mem hf hv
  have hfin := range_finite_of_mem_locallyConstantCompactSupport hF
  have hpt : ∀ g, f g * φ (ρ g v) =
      ∑ w ∈ hfin.toFinset, {x | f x • ρ x v = w}.indicator (fun _ => φ w) g := by
    intro g
    rw [Finset.sum_eq_single (f g • ρ g v)]
    · rw [Set.indicator_of_mem (show g ∈ {x | f x • ρ x v = f g • ρ g v} from rfl), map_smul,
        smul_eq_mul]
    · intro b _ hb
      exact Set.indicator_of_notMem (fun h => hb h.symm) _
    · intro h
      exact absurd ((Set.Finite.mem_toFinset hfin).2 (Set.mem_range_self g)) h
  have hmeas : ∀ w, MeasurableSet {x | f x • ρ x v = w} := fun w =>
    (hF.1.isOpen_fiber w).measurableSet
  rw [heckeAct_eq_sum hfin, map_sum, integral_congr_ae (Eventually.of_forall hpt),
    integral_finsetSum]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [integral_indicator_const _ (hmeas w), map_smul, smul_eq_mul, Complex.real_smul]
  · intro w _
    by_cases hw : w = 0
    · subst hw
      simp only [map_zero]
      exact (integrable_zero G ℂ μ).indicator (hmeas 0)
    · exact (integrable_indicator_iff (hmeas w)).2
        (integrableOn_const (isCompact_isOpen_fiber hF hw).1.measure_lt_top.ne)
theorem eq_of_forall_dual {x y : V} (h : ∀ φ : Module.Dual ℂ V, φ x = φ y) : x = y := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  rw [map_sub, h φ, sub_self]
variable [IsFiniteMeasureOnCompacts μ]
theorem heckeAct_add_left {f₁ f₂ : G → ℂ} (hf₁ : f₁ ∈ locallyConstantCompactSupport G ℂ ℂ)
    (hf₂ : f₂ ∈ locallyConstantCompactSupport G ℂ ℂ) {v : V} (hv : v ∈ smoothVectors ρ) :
    heckeAct μ ρ (f₁ + f₂) v = heckeAct μ ρ f₁ v + heckeAct μ ρ f₂ v := by
  refine eq_of_forall_dual fun φ => ?_
  rw [map_add, dual_heckeAct μ (add_mem hf₁ hf₂) hv, dual_heckeAct μ hf₁ hv,
    dual_heckeAct μ hf₂ hv, ← integral_add (integrable_mul_of_mem hf₁ (continuous_dual_orbit hv φ))
      (integrable_mul_of_mem hf₂ (continuous_dual_orbit hv φ))]
  simp only [Pi.add_apply, add_mul]
theorem heckeAct_smul_left (c : ℂ) {f : G → ℂ} (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ)
    {v : V} (hv : v ∈ smoothVectors ρ) : heckeAct μ ρ (c • f) v = c • heckeAct μ ρ f v := by
  refine eq_of_forall_dual fun φ => ?_
  rw [map_smul, dual_heckeAct μ (Submodule.smul_mem _ c hf) hv, dual_heckeAct μ hf hv, smul_eq_mul,
    ← integral_const_mul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
theorem heckeAct_zero_left {v : V} (hv : v ∈ smoothVectors ρ) : heckeAct μ ρ 0 v = 0 := by
  have := heckeAct_smul_left (μ := μ) 0 (zero_mem _) hv
  rwa [zero_smul, zero_smul] at this
theorem heckeAct_add_right {f : G → ℂ} (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ)
    {v w : V} (hv : v ∈ smoothVectors ρ) (hw : w ∈ smoothVectors ρ) :
    heckeAct μ ρ f (v + w) = heckeAct μ ρ f v + heckeAct μ ρ f w := by
  refine eq_of_forall_dual fun φ => ?_
  rw [map_add, dual_heckeAct μ hf (add_mem hv hw), dual_heckeAct μ hf hv, dual_heckeAct μ hf hw,
    ← integral_add (integrable_mul_of_mem hf (continuous_dual_orbit hv φ))
      (integrable_mul_of_mem hf (continuous_dual_orbit hw φ))]
  simp only [map_add, mul_add]
theorem heckeAct_smul_right {f : G → ℂ} (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ) (c : ℂ)
    {v : V} (hv : v ∈ smoothVectors ρ) : heckeAct μ ρ f (c • v) = c • heckeAct μ ρ f v := by
  refine eq_of_forall_dual fun φ => ?_
  rw [map_smul, dual_heckeAct μ hf (Submodule.smul_mem _ c hv), dual_heckeAct μ hf hv,
    smul_eq_mul, ← integral_const_mul]
  simp only [map_smul, smul_eq_mul]
  congr 1
  funext g
  ring
theorem heckeAct_zero_right {f : G → ℂ} (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ) :
    heckeAct μ ρ f 0 = 0 := by
  have := heckeAct_smul_right (μ := μ) (ρ := ρ) hf 0 (zero_mem _)
  rwa [zero_smul, zero_smul] at this
variable [μ.IsMulLeftInvariant]
theorem heckeAct_ltrans (g : G) {f : G → ℂ} (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ)
    {v : V} (hv : v ∈ smoothVectors ρ) : ρ g (heckeAct μ ρ f v) = heckeAct μ ρ (ltrans g f) v := by
  refine eq_of_forall_dual fun φ => ?_
  have := dual_heckeAct μ hf hv (φ ∘ₗ ρ g)
  simp only [LinearMap.comp_apply] at this
  rw [this, dual_heckeAct μ (ltrans_mem g hf) hv,
    ← integral_mul_left_eq_self (fun y => ltrans g f y * φ (ρ y v)) g]
  simp only [ltrans_apply, inv_mul_cancel_left, map_mul, Module.End.mul_apply]
theorem heckeAct_mem_fixedVectors {K : Subgroup G} {f : G → ℂ}
    (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ) (hK : ∀ k ∈ K, ∀ x, f (k * x) = f x) {v : V}
    (hv : v ∈ smoothVectors ρ) : heckeAct μ ρ f v ∈ fixedVectors ρ K := by
  intro k hk
  rw [heckeAct_ltrans k hf hv]
  congr 1
  funext x
  exact hK k⁻¹ (inv_mem hk) x
variable [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
theorem heckeAct_mem_smoothVectors {f : G → ℂ} (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ)
    {v : V} (hv : v ∈ smoothVectors ρ) : heckeAct μ ρ f v ∈ smoothVectors ρ := by
  obtain ⟨K, hKc, hK⟩ := exists_forall_mul_left hf
  exact (mem_smoothVectors_iff ρ).2 ⟨K, hKc, K.isOpen, heckeAct_mem_fixedVectors hf hK hv⟩
theorem heckeAct_groupConv {f₁ f₂ : G → ℂ} (hf₁ : f₁ ∈ locallyConstantCompactSupport G ℂ ℂ)
    (hf₂ : f₂ ∈ locallyConstantCompactSupport G ℂ ℂ) {v : V} (hv : v ∈ smoothVectors ρ) :
    heckeAct μ ρ (groupConv μ f₁ f₂) v = heckeAct μ ρ f₁ (heckeAct μ ρ f₂ v) := by
  obtain ⟨K₁, hK₁c, hK₁⟩ := exists_forall_mul_right hf₁
  obtain ⟨K₂, -, hK₂⟩ := exists_forall_mul_left_mul_right hf₂
  obtain ⟨K₃, -, hK₃o, hK₃⟩ := (mem_smoothVectors_iff ρ).1 hv
  let K : OpenSubgroup G := K₁ ⊓ K₂ ⊓ ⟨K₃, hK₃o⟩
  have hKc : IsCompact (K : Set G) := isCompact_inf_left (isCompact_inf_left hK₁c)
  have m₁ : ∀ k ∈ K, k ∈ K₁ := fun k hk => (OpenSubgroup.mem_inf.1 (OpenSubgroup.mem_inf.1 hk).1).1
  have m₂ : ∀ k ∈ K, k ∈ K₂ := fun k hk => (OpenSubgroup.mem_inf.1 (OpenSubgroup.mem_inf.1 hk).1).2
  have m₃ : ∀ k ∈ K, k ∈ K₃ := fun k hk => (OpenSubgroup.mem_inf.1 hk).2
  refine eq_of_forall_dual fun φ => ?_
  rw [dual_heckeAct μ (groupConv_mem μ hf₁ hf₂) hv,
    dual_heckeAct μ hf₁ (heckeAct_mem_smoothVectors hf₂ hv)]
  have inner : ∀ y, φ (ρ y (heckeAct μ ρ f₂ v)) = ∫ z, f₂ (y⁻¹ * z) * φ (ρ z v) ∂μ := fun y => by
    rw [heckeAct_ltrans y hf₂ hv, dual_heckeAct μ (ltrans_mem y hf₂) hv]
    rfl
  simp_rw [inner, groupConv, ← integral_mul_const, ← integral_const_mul, ← mul_assoc]
  refine (integral_integral_swap_of_coset μ K hKc hf₁.2 (hf₁.2.mul hf₂.2) ?_ ?_ ?_).symm
  · intro y z h
    have h' := mul_ne_zero_iff.1 (mul_ne_zero_iff.1 h).1
    exact ⟨subset_tsupport _ h'.1, y, subset_tsupport _ h'.1, y⁻¹ * z, subset_tsupport _ h'.2,
      mul_inv_cancel_left y z⟩
  · intro y z k hk
    have e₂ : f₂ ((y * k)⁻¹ * z) = f₂ (y⁻¹ * z) := by
      have := hK₂ k⁻¹ (inv_mem (m₂ k hk)) (y⁻¹ * z) 1 (one_mem _)
      rwa [mul_one, ← mul_assoc, ← mul_inv_rev] at this
    rw [hK₁ y k (m₁ k hk), e₂]
  · intro y z k hk
    have e₂ : f₂ (y⁻¹ * (z * k)) = f₂ (y⁻¹ * z) := by
      have := hK₂ 1 (one_mem _) (y⁻¹ * z) k (m₂ k hk)
      rwa [one_mul, mul_assoc] at this
    rw [e₂, map_mul, Module.End.mul_apply, hK₃ k (m₃ k hk)]
end Action
variable [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
def HeckeAlgebra (μ : Measure G) : Type _ := locallyConstantCompactSupport G ℂ ℂ
namespace HeckeAlgebra
variable {μ : Measure G}
instance : AddCommGroup (HeckeAlgebra μ) :=
  inferInstanceAs (AddCommGroup (locallyConstantCompactSupport G ℂ ℂ))
instance : Module ℂ (HeckeAlgebra μ) :=
  inferInstanceAs (Module ℂ (locallyConstantCompactSupport G ℂ ℂ))
instance : FunLike (HeckeAlgebra μ) G ℂ where
  coe f := (show locallyConstantCompactSupport G ℂ ℂ from f).1
  coe_injective _ _ h := Subtype.ext h
theorem mem (f : HeckeAlgebra μ) : (f : G → ℂ) ∈ locallyConstantCompactSupport G ℂ ℂ :=
  (show locallyConstantCompactSupport G ℂ ℂ from f).2
variable (μ) in

def mk (f : G → ℂ) (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ) : HeckeAlgebra μ :=
  (⟨f, hf⟩ : locallyConstantCompactSupport G ℂ ℂ)
@[simp]
theorem coe_mk (f : G → ℂ) (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ) :
    (mk μ f hf : G → ℂ) = f := rfl
@[ext]
theorem ext {f g : HeckeAlgebra μ} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h
@[simp] theorem coe_add (f g : HeckeAlgebra μ) : ((f + g : HeckeAlgebra μ) : G → ℂ) = f + g := rfl
@[simp] theorem coe_zero : ((0 : HeckeAlgebra μ) : G → ℂ) = 0 := rfl
@[simp] theorem coe_smul (c : ℂ) (f : HeckeAlgebra μ) :
    ((c • f : HeckeAlgebra μ) : G → ℂ) = c • (f : G → ℂ) := rfl
@[simp] theorem coe_neg (f : HeckeAlgebra μ) : ((-f : HeckeAlgebra μ) : G → ℂ) = -f := rfl
@[simp] theorem coe_sub (f g : HeckeAlgebra μ) : ((f - g : HeckeAlgebra μ) : G → ℂ) = f - g := rfl
instance : Mul (HeckeAlgebra μ) := ⟨fun f g => mk μ (groupConv μ f g) (groupConv_mem μ f.mem g.mem)⟩
theorem coe_mul (f g : HeckeAlgebra μ) : ((f * g : HeckeAlgebra μ) : G → ℂ) = groupConv μ f g :=
  rfl
variable (μ) in

def evalₗ (x : G) : Module.Dual ℂ (HeckeAlgebra μ) where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
variable (μ) in

def leftReg : Representation ℂ G (HeckeAlgebra μ) where
  toFun g :=
    { toFun := fun f => mk μ (ltrans g f) (ltrans_mem g f.mem)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext f x
    change f (1⁻¹ * x) = f x
    simp
  map_mul' g h := by
    ext f x
    change f ((g * h)⁻¹ * x) = f (h⁻¹ * (g⁻¹ * x))
    simp [mul_inv_rev, mul_assoc]
theorem leftReg_apply (g : G) (f : HeckeAlgebra μ) (x : G) : leftReg μ g f x = f (g⁻¹ * x) := rfl
theorem mem_fixedVectors_leftReg {K : Subgroup G} {f : HeckeAlgebra μ} :
    f ∈ fixedVectors (leftReg μ) K ↔ ∀ k ∈ K, ∀ x, f (k * x) = f x := by
  constructor
  · intro h k hk x
    have := congrArg (fun φ : HeckeAlgebra μ => φ x) (h k⁻¹ (inv_mem hk))
    simpa [leftReg_apply] using this
  · intro h k hk
    ext x
    rw [leftReg_apply]
    exact h k⁻¹ (inv_mem hk) x
theorem isSmooth_leftReg : IsSmooth (leftReg μ) := by
  intro f
  obtain ⟨K, -, hK⟩ := exists_forall_mul_left f.mem
  exact Subgroup.isOpen_mono (H₁ := (K : Subgroup G))
    (fun k hk => mem_fixedVectors_leftReg.2 hK k hk) K.isOpen
theorem heckeAct_leftReg [IsFiniteMeasureOnCompacts μ] (f φ : HeckeAlgebra μ) :
    heckeAct μ (leftReg μ) f φ = f * φ := by
  ext x
  exact dual_heckeAct μ f.mem (isSmooth_leftReg φ) (evalₗ μ x)
variable [μ.IsHaarMeasure]
instance : NonUnitalRing (HeckeAlgebra μ) :=
  { (inferInstance : AddCommGroup (HeckeAlgebra μ)) with
    left_distrib := fun a b c => by
      rw [← heckeAct_leftReg, ← heckeAct_leftReg, ← heckeAct_leftReg,
        heckeAct_add_right a.mem (isSmooth_leftReg b) (isSmooth_leftReg c)]
    right_distrib := fun a b c => by
      rw [← heckeAct_leftReg, ← heckeAct_leftReg, ← heckeAct_leftReg, coe_add,
        heckeAct_add_left a.mem b.mem (isSmooth_leftReg c)]
    zero_mul := fun a => by
      rw [← heckeAct_leftReg, coe_zero, heckeAct_zero_left (isSmooth_leftReg a)]
    mul_zero := fun a => by
      rw [← heckeAct_leftReg, heckeAct_zero_right a.mem]
    mul_assoc := fun a b c => by
      rw [← heckeAct_leftReg, coe_mul, heckeAct_groupConv a.mem b.mem (isSmooth_leftReg c),
        heckeAct_leftReg, heckeAct_leftReg] }
instance : IsScalarTower ℂ (HeckeAlgebra μ) (HeckeAlgebra μ) where
  smul_assoc c a b := by
    change (c • a) * b = c • (a * b)
    rw [← heckeAct_leftReg, ← heckeAct_leftReg, coe_smul,
      heckeAct_smul_left c a.mem (isSmooth_leftReg b)]
instance : SMulCommClass ℂ (HeckeAlgebra μ) (HeckeAlgebra μ) where
  smul_comm c a b := by
    change c • (a * b) = a * (c • b)
    rw [← heckeAct_leftReg, ← heckeAct_leftReg,
      heckeAct_smul_right a.mem c (isSmooth_leftReg b)]
end HeckeAlgebra
end GroundTheory.Automorphic


