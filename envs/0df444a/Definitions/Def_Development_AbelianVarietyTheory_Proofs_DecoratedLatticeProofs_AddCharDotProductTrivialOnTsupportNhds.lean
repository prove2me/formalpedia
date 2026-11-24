-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_AddCharDotProductTrivialOnTsupportNhds
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_AddCharDotProductTrivialOnTsupportNhds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:21.315294+00:00
-- url     : https://prove2.me/theorems/35a36c6c-3cef-48f3-8715-e05d4de552dc
-- title:
--   Add Char Dot Product Trivial On Tsupport Nhds
-- statement:
--   Definitions and structural lemmas for Add Char Dot Product Trivial On Tsupport Nhds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/AddCharDotProductTrivialOnTsupportNhds.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_exists_box_invariant
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_exists_box_subset
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isCompact_box
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isOpen_box
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_isLocallyConstant
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_WeilM_HaarUniq_exists_decomp
import Theorems.Thm_GlobalTheory_WeilM_HaarUniq_indicator_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix
open scoped Topology
noncomputable section
namespace GlobalTheory.HeisLine
open GlobalTheory.SplitWeil.FourierPi
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]
def boxSub (s : kˣ) : OpenAddSubgroup (n → k) where
  carrier := box n s
  add_mem' ha hb := fun i _ => add_mem_cball (ha i trivial) (hb i trivial)
  zero_mem' := fun i _ => by simp [cball]
  neg_mem' ha := fun i _ => neg_mem_cball (ha i trivial)
  isOpen' := isOpen_box s
variable [MeasurableSpace k] [BorelSpace k]
theorem measureReal_box_ne (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (s : kˣ) :
    (μ.real (box n s) : ℂ) ≠ 0 := by
  have h1 : μ (box n s) ≠ 0 := ((isOpen_box s).measure_pos μ ⟨0, fun i _ => by simp [cball]⟩).ne'
  have h2 : μ (box n s) ≠ ⊤ := (isCompact_box s).measure_lt_top.ne
  exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨h1, h2⟩
theorem decomp_integral (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (s : kˣ) {φ : (n → k) → ℂ}
    (hφ : φ ∈ SB (n → k)) (hinv : ∀ t ∈ box n s, ∀ x, φ (x + t) = φ x) :
    ∃ S : Finset (n → k), (∀ y, φ y = ∑ x ∈ S, φ x * (box n s).indicator (fun _ => (1:ℂ)) (y - x)) ∧
      ∀ F : (n → k) → ℂ, (∀ t ∈ box n s, ∀ x, F (x + t) = F x) →
        ∫ y, φ y * F y ∂μ = (μ.real (box n s) : ℂ) * ∑ x ∈ S, φ x * F x := by
  classical
  haveI := secondCountable k
  obtain ⟨S, hS⟩ := GlobalTheory.WeilM.HaarUniq.exists_decomp (boxSub (n := n) s) hφ.2 hinv
  have hinj : ∀ q ∈ S, ∀ q' ∈ S, Quotient.out q = Quotient.out q' → q = q' := fun q _ q' _ h => by
    simpa using congrArg (QuotientAddGroup.mk (s := (boxSub (n := n) s).toAddSubgroup)) h
  have hpt : ∀ y, φ y = ∑ x ∈ S.image Quotient.out, φ x * (box n s).indicator (fun _ => (1:ℂ)) (y - x) := by
    intro y
    rw [Finset.sum_image hinj]
    have := congrFun hS y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [sub_eq_add_neg]
    rfl
  refine ⟨S.image Quotient.out, hpt, fun F hF => ?_⟩
  have h1 : ∀ y, φ y * F y = ∑ x ∈ S.image Quotient.out,
      (φ x * F x) * (box n s).indicator (fun _ => (1:ℂ)) (y - x) := by
    intro y
    rw [hpt y, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hy : y - x ∈ box n s
    · have := hF (y - x) hy x
      rw [add_sub_cancel] at this
      rw [this]; ring
    · simp [Set.indicator_of_notMem hy]
  have hint : ∀ x : n → k, Integrable (fun y => (box n s).indicator (fun _ => (1:ℂ)) (y - x)) μ := by
    intro x
    have : Integrable ((box n s).indicator (fun _ => (1:ℂ))) μ :=
      (integrable_indicator_iff (isOpen_box _).measurableSet).mpr
        (integrableOn_const (isCompact_box _).measure_lt_top.ne)
    exact this.comp_sub_right x
  rw [integral_congr_ae (Filter.Eventually.of_forall h1)]
  have h2 : ∀ x : n → k, ∫ y, (box n s).indicator (fun _ => (1:ℂ)) (y - x) ∂μ = (μ.real (box n s) : ℂ) := by
    intro x
    rw [integral_sub_right_eq_self (fun y => (box n s).indicator (fun _ => (1:ℂ)) y) x,
      integral_indicator_const _ (isOpen_box _).measurableSet]
    simp
  rw [integral_finsetSum _ fun x _ => (hint x).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_const_mul, h2, mul_comm]
variable {χ : AddChar k Circle} {c : kˣ}
omit [MeasurableSpace k] [BorelSpace k] in
theorem addChar_dotProduct_trivial_on_tsupport_nhds (hχ : HasConductor χ c) {g : (n → k) → ℂ} (hg : g ∈ SB (n → k)) :
    {t : n → k | ∀ η ∈ tsupport g, χ (η ⬝ᵥ t) = 1} ∈ 𝓝 (0 : n → k) := by
  have h1 : ∀ᶠ t in 𝓝 (0 : n → k), ∀ η ∈ tsupport g, χ (η ⬝ᵥ t) = 1 := by
    refine IsCompact.eventually_forall_of_forall_eventually hg.2 fun η _ => ?_
    have h2 : IsLocallyConstant fun q : (n → k) × (n → k) => χ (q.2 ⬝ᵥ q.1) :=
      hχ.isLocallyConstant.comp_continuous (continuous_snd.dotProduct continuous_fst)
    filter_upwards [h2.eventually_eq ((0 : n → k), η)] with q hq
    simpa using hq
  exact h1
omit [MeasurableSpace k] [BorelSpace k] in
theorem box_nhds (s : kˣ) : box n s ∈ 𝓝 (0 : n → k) :=
  (isOpen_box s).mem_nhds fun i _ => by simp [cball]
omit [MeasurableSpace k] [BorelSpace k] in
theorem invariant_nhds {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    {t : n → k | ∀ x, f (x + t) = f x} ∈ 𝓝 (0 : n → k) := by
  obtain ⟨s, hs⟩ := exists_box_invariant hf
  exact Filter.mem_of_superset (box_nhds s) fun t ht => hs t ht
omit [MeasurableSpace k] [BorelSpace k] in
theorem tr_mem {a : (n → k) → ℂ} (ha : a ∈ SB (n → k)) (x : n → k) :
    (fun y => a (y - x)) ∈ SB (n → k) :=
  ⟨ha.1.comp_continuous (continuous_id.sub continuous_const), ha.2.comp_homeomorph (Homeomorph.subRight x)⟩
omit [MeasurableSpace k] [BorelSpace k] in
theorem mc_mem (hχ : HasConductor χ c) {b : (n → k) → ℂ} (hb : b ∈ SB (n → k)) (x : n → k) :
    (fun η => (χ (η ⬝ᵥ x) : ℂ) * b η) ∈ SB (n → k) := by
  refine ⟨?_, hb.2.mul_left⟩
  have h1 : IsLocallyConstant fun η : n → k => (χ (η ⬝ᵥ x) : ℂ) :=
    (hχ.isLocallyConstant.comp_continuous (continuous_id.dotProduct continuous_const)).comp _
  exact h1.mul hb.1
theorem law_integrated (hχ : HasConductor χ c) (μ : Measure (n → k)) [μ.IsAddHaarMeasure]
    (B : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ)
    (h2 : ∀ (a a' b b' : SB (n → k)) (t : n → k), (∀ y, a'.1 y = a.1 (y - t)) →
      (∀ η, b'.1 η = (χ (η ⬝ᵥ t) : ℂ) * b.1 η) → B a' b = B a b')
    (a b φ a' b' : SB (n → k)) (ha' : ∀ y, a'.1 y = ∫ t, φ.1 t * a.1 (y - t) ∂μ)
    (hb' : ∀ η, b'.1 η = (∫ t, φ.1 t * (χ (η ⬝ᵥ t) : ℂ) ∂μ) * b.1 η) : B a' b = B a b' := by
  classical
  obtain ⟨s, hs⟩ := exists_box_subset (Filter.inter_mem (invariant_nhds φ.2)
    (Filter.inter_mem (invariant_nhds a.2) (addChar_dotProduct_trivial_on_tsupport_nhds hχ b.2)))
  obtain ⟨S, -, hint⟩ := decomp_integral μ s φ.2 fun t ht x => (hs ht).1 x
  set m : ℂ := (μ.real (box n s) : ℂ)
  have hnegmem : ∀ t ∈ box n s, -t ∈ box n s := fun t ht i _ => neg_mem_cball (ht i trivial)
  have ea : a' = ∑ x ∈ S, (m * φ.1 x) • (⟨_, tr_mem a.2 x⟩ : SB (n → k)) := by
    apply Subtype.ext
    funext y
    rw [Submodule.coe_sum, Finset.sum_apply, ha' y]
    rw [hint (fun t => a.1 (y - t)) fun t ht x => by
      have := (hs (hnegmem t ht)).2.1 (y - x)
      rw [← this]; abel_nf]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have eb : b' = ∑ x ∈ S, (m * φ.1 x) • (⟨_, mc_mem hχ b.2 x⟩ : SB (n → k)) := by
    apply Subtype.ext
    funext η
    rw [Submodule.coe_sum, Finset.sum_apply, hb' η]
    by_cases hη : η ∈ tsupport b.1
    · rw [hint (fun t => (χ (η ⬝ᵥ t) : ℂ)) fun t ht x => by
        rw [dotProduct_add, AddChar.map_add_eq_mul, (hs ht).2.2 η hη, mul_one]]
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
      ring
    · have h0 : b.1 η = 0 := image_eq_zero_of_notMem_tsupport hη
      simp [h0]
  rw [ea, eb, map_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, LinearMap.smul_apply, map_smul]
  congr 1
  exact h2 a _ b _ x (fun y => rfl) (fun η => rfl)
omit [MeasurableSpace k] [BorelSpace k] in
theorem box_mono {s s' : kˣ} (h : valuation k (s : k) ≤ valuation k (s' : k)) : box n s ⊆ box n s' :=
  fun x hx i _ => show valuation k (x i) ≤ valuation k (s' : k) from le_trans (hx i trivial) h
omit [MeasurableSpace k] [BorelSpace k] in
theorem box_total (s s' : kˣ) : box n s ⊆ box n s' ∨ box n s' ⊆ box n s :=
  (le_total (valuation k (s : k)) (valuation k (s' : k))).imp box_mono box_mono
omit [MeasurableSpace k] [BorelSpace k] in
theorem ind_add (s : kˣ) {t : n → k} (ht : t ∈ box n s) (z : n → k) :
    (box n s).indicator (fun _ => (1 : ℂ)) (z + t) = (box n s).indicator (fun _ => (1 : ℂ)) z := by
  have h : z + t ∈ box n s ↔ z ∈ box n s :=
    add_mem_cancel_right (H := (boxSub (n := n) s).toAddSubgroup) ht
  by_cases hz : z ∈ box n s
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (h.2 hz)]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h' => hz (h.1 h'))]
omit [MeasurableSpace k] [BorelSpace k] in
theorem ind_mem (s : kˣ) : (box n s).indicator (fun _ => (1 : ℂ)) ∈ SB (n → k) := by
  haveI := t2Space k
  exact GlobalTheory.WeilM.HaarUniq.indicator_mem (boxSub (n := n) s) (isCompact_box s)
def ind (s : kˣ) : SB (n → k) := ⟨_, ind_mem (n := n) s⟩
theorem conv_ind (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (s : kˣ) {φ : (n → k) → ℂ}
    (hφ : φ ∈ SB (n → k)) (hinv : ∀ t ∈ box n s, ∀ x, φ (x + t) = φ x) (y : n → k) :
    ∫ t, φ t * (box n s).indicator (fun _ => (1 : ℂ)) (y - t) ∂μ = (μ.real (box n s) : ℂ) * φ y := by
  obtain ⟨S, hpt, hint⟩ := decomp_integral μ s hφ hinv
  rw [hint _ fun t ht x => by
    rw [show y - (x + t) = (y - x) + -t by abel, ind_add s (show -t ∈ box n s from fun i _ => neg_mem_cball (ht i trivial))],
    hpt y]
def admitted (χ : AddChar k Circle) (s : kˣ) (g : (n → k) → ℂ) : Prop :=
  ∀ η, g η ≠ 0 → ∀ t ∈ box n s, χ (η ⬝ᵥ t) = 1
omit [MeasurableSpace k] [BorelSpace k] in
theorem isAdmissibleBoxForCharacter_of_subset {s : kˣ} {g : (n → k) → ℂ}
    (h : box n s ⊆ {t : n → k | ∀ η ∈ tsupport g, χ (η ⬝ᵥ t) = 1}) : admitted χ s g :=
  fun η hη t ht => h ht η (subset_tsupport _ hη)
theorem ratio_indep (hχ : HasConductor χ c) (μ : Measure (n → k)) [μ.IsAddHaarMeasure]
    (B : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ)
    (h2 : ∀ (a a' b b' : SB (n → k)) (t : n → k), (∀ y, a'.1 y = a.1 (y - t)) →
      (∀ η, b'.1 η = (χ (η ⬝ᵥ t) : ℂ) * b.1 η) → B a' b = B a b')
    {s s' : kˣ} (g : SB (n → k)) (hs : admitted χ s g.1) (hss : box n s' ⊆ box n s) :
    (μ.real (box n s) : ℂ)⁻¹ * B (ind s) g = (μ.real (box n s') : ℂ)⁻¹ * B (ind s') g := by
  haveI := secondCountable k
  have key := law_integrated hχ μ B h2 (ind s') g (ind s) ((μ.real (box n s') : ℂ) • ind s)
    ((μ.real (box n s) : ℂ) • g) (fun y => by
      show (μ.real (box n s') : ℂ) * (box n s).indicator (fun _ => (1 : ℂ)) y =
        ∫ t, (box n s).indicator (fun _ => (1 : ℂ)) t * (box n s').indicator (fun _ => (1 : ℂ)) (y - t) ∂μ
      rw [conv_ind μ s' (ind_mem s) (fun t ht x => ind_add s (hss ht) x) y]) (fun η => by
      show (μ.real (box n s) : ℂ) * g.1 η = _
      by_cases hη : g.1 η = 0
      · simp [hη]
      · congr 1
        have : ∀ t, (ind s).1 t * (χ (η ⬝ᵥ t) : ℂ) = (box n s).indicator (fun _ => (1 : ℂ)) t := by
          intro t
          by_cases ht : t ∈ box n s
          · rw [hs η hη t ht]; simp [ind]
          · simp [ind, Set.indicator_of_notMem ht]
        simp only [this]
        rw [integral_indicator_const _ (isOpen_box _).measurableSet]
        simp)
  rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at key
  have h1 := measureReal_box_ne μ s
  have h1' := measureReal_box_ne μ s'
  field_simp
  linear_combination key
omit [MeasurableSpace k] [BorelSpace k] in
theorem exists_adm (hχ : HasConductor χ c) (g : SB (n → k)) : ∃ s : kˣ, admitted χ s g.1 := by
  obtain ⟨s, hs⟩ := exists_box_subset (addChar_dotProduct_trivial_on_tsupport_nhds hχ g.2)
  exact ⟨s, isAdmissibleBoxForCharacter_of_subset hs⟩
open Classical in

def ell (χ : AddChar k Circle) (μ : Measure (n → k)) (B : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ)
    (g : SB (n → k)) : ℂ :=
  if h : ∃ s : kˣ, admitted χ s g.1 then (μ.real (box n h.choose) : ℂ)⁻¹ * B (ind h.choose) g else 0
section Form
variable (hχ : HasConductor χ c) (μ : Measure (n → k)) [μ.IsAddHaarMeasure]
    (B : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ)
    (h2 : ∀ (a a' b b' : SB (n → k)) (t : n → k), (∀ y, a'.1 y = a.1 (y - t)) →
      (∀ η, b'.1 η = (χ (η ⬝ᵥ t) : ℂ) * b.1 η) → B a' b = B a b')
include hχ h2
theorem ell_eq {s : kˣ} (g : SB (n → k)) (hs : admitted χ s g.1) :
    ell χ μ B g = (μ.real (box n s) : ℂ)⁻¹ * B (ind s) g := by
  have h : ∃ s : kˣ, admitted χ s g.1 := ⟨s, hs⟩
  rw [ell, dif_pos h]
  rcases box_total (n := n) h.choose s with h1 | h1
  · exact (ratio_indep hχ μ B h2 g hs h1).symm
  · exact ratio_indep hχ μ B h2 g h.choose_spec h1
def ellL : SB (n → k) →ₗ[ℂ] ℂ where
  toFun := ell χ μ B
  map_add' g g' := by
    obtain ⟨s, hs⟩ := exists_box_subset (Filter.inter_mem (addChar_dotProduct_trivial_on_tsupport_nhds hχ g.2) (addChar_dotProduct_trivial_on_tsupport_nhds hχ g'.2))
    have a1 : admitted χ s g.1 := isAdmissibleBoxForCharacter_of_subset fun t ht => (hs ht).1
    have a2 : admitted χ s g'.1 := isAdmissibleBoxForCharacter_of_subset fun t ht => (hs ht).2
    have a3 : admitted χ s (g + g').1 := fun η hη t ht => by
      by_cases h : g.1 η = 0
      · have : g'.1 η ≠ 0 := by
          intro h'
          apply hη
          simp [h, h']
        exact a2 η this t ht
      · exact a1 η h t ht
    rw [ell_eq hχ μ B h2 _ a1, ell_eq hχ μ B h2 _ a2, ell_eq hχ μ B h2 _ a3, map_add]
    ring
  map_smul' z g := by
    obtain ⟨s, hs⟩ := exists_adm hχ g
    have a3 : admitted χ s (z • g).1 := fun η hη t ht => hs η (fun h => hη (by simp [h])) t ht
    rw [ell_eq hχ μ B h2 _ hs, ell_eq hχ μ B h2 _ a3, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul]
    ring
end Form
end GlobalTheory.HeisLine


