-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:03:13.288328+00:00
-- url     : https://prove2.me/theorems/f6401863-b458-41bb-be2c-e43ebdf4b08f
-- title:
--   PPrime Filtration Restrict
-- statement:
--   Definitions and structural lemmas for PPrime Filtration Restrict, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationRestrict.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio_3a0d7bd51278

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
section Residue
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
  {K' : Type w} [Field K'] [Algebra S K'] (ψ : chartRing S x (singleChart hj) →ₐ[S] K')
abbrev reducedPt : Fin (N + 1) → K' := fun i => ψ (ratio hj i)
def RegularAt (a : Ω) : Prop :=
  ∃ b c : chartRing S x (singleChart hj), ψ c ≠ 0 ∧ a * (c : Ω) = b
open Classical in

def residueAt (a : Ω) : K' :=
  if h : RegularAt hj ψ a then ψ h.choose / ψ h.choose_spec.choose else 0
theorem residue_wellDefined {a : Ω} {b c b0 c0 : chartRing S x (singleChart hj)} (hc : ψ c ≠ 0)
    (h : a * (c : Ω) = b) (hc0 : ψ c0 ≠ 0) (h0 : a * (c0 : Ω) = b0) : ψ b0 / ψ c0 = ψ b / ψ c := by
  rw [div_eq_div_iff hc0 hc]
  have : b0 * c = b * c0 := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, ← h0, ← h]
    ring
  rw [← map_mul, ← map_mul, this]
theorem residueAt_eq {a : Ω} {b c : chartRing S x (singleChart hj)} (hc : ψ c ≠ 0)
    (h : a * (c : Ω) = b) : residueAt hj ψ a = ψ b / ψ c := by
  have hr : RegularAt hj ψ a := ⟨b, c, hc, h⟩
  rw [residueAt, dif_pos hr]
  exact residue_wellDefined hj ψ hc h hr.choose_spec.choose_spec.1 hr.choose_spec.choose_spec.2
theorem residueAt_of_mem (a : chartRing S x (singleChart hj)) : residueAt hj ψ (a : Ω) = ψ a := by
  rw [residueAt_eq hj ψ (b := a) (c := 1) (by rw [map_one]; exact one_ne_zero)
    (by rw [Subalgebra.coe_one, mul_one]), map_one, div_one]
theorem residueAt_one : residueAt hj ψ (1 : Ω) = 1 := by
  have := residueAt_of_mem hj ψ 1
  rwa [Subalgebra.coe_one, map_one] at this
theorem residueAt_zero : residueAt hj ψ (0 : Ω) = 0 := by
  have := residueAt_of_mem hj ψ 0
  rwa [Subalgebra.coe_zero, map_zero] at this
variable {hj ψ} in
theorem RegularAt.add {a a' : Ω} (h : RegularAt hj ψ a) (h' : RegularAt hj ψ a') :
    RegularAt hj ψ (a + a') ∧ residueAt hj ψ (a + a') = residueAt hj ψ a + residueAt hj ψ a' := by
  obtain ⟨b, c, hc, hbc⟩ := h
  obtain ⟨b', c', hc', hbc'⟩ := h'
  have hcc : ψ (c * c') ≠ 0 := by rw [map_mul]; exact mul_ne_zero hc hc'
  have he : (a + a') * ((c * c' : chartRing S x (singleChart hj)) : Ω) = (b * c' + b' * c : chartRing S x (singleChart hj)) := by
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, ← hbc, ← hbc']
    ring
  refine ⟨⟨_, _, hcc, he⟩, ?_⟩
  rw [residueAt_eq hj ψ hcc he, residueAt_eq hj ψ hc hbc, residueAt_eq hj ψ hc' hbc', map_add,
    map_mul, map_mul, map_mul, div_add_div _ _ hc hc']
  ring
variable {hj ψ} in
theorem RegularAt.mul {a a' : Ω} (h : RegularAt hj ψ a) (h' : RegularAt hj ψ a') :
    RegularAt hj ψ (a * a') ∧ residueAt hj ψ (a * a') = residueAt hj ψ a * residueAt hj ψ a' := by
  obtain ⟨b, c, hc, hbc⟩ := h
  obtain ⟨b', c', hc', hbc'⟩ := h'
  have hcc : ψ (c * c') ≠ 0 := by rw [map_mul]; exact mul_ne_zero hc hc'
  have he : (a * a') * ((c * c' : chartRing S x (singleChart hj)) : Ω) = (b * b' : chartRing S x (singleChart hj)) := by
    simp only [Subalgebra.coe_mul, ← hbc, ← hbc']
    ring
  refine ⟨⟨_, _, hcc, he⟩, ?_⟩
  rw [residueAt_eq hj ψ hcc he, residueAt_eq hj ψ hc hbc, residueAt_eq hj ψ hc' hbc', map_mul,
    map_mul, div_mul_div_comm]
variable {hj ψ} in
theorem RegularAt.inv {a : Ω} (h : RegularAt hj ψ a) (hne : residueAt hj ψ a ≠ 0) :
    a ≠ 0 ∧ RegularAt hj ψ a⁻¹ ∧ residueAt hj ψ a⁻¹ = (residueAt hj ψ a)⁻¹ := by
  obtain ⟨b, c, hc, hbc⟩ := h
  rw [residueAt_eq hj ψ hc hbc] at hne ⊢
  have hb : ψ b ≠ 0 := fun h0 => hne (by rw [h0, zero_div])
  have ha : a ≠ 0 := by
    rintro rfl
    apply hb
    have : b = 0 := Subtype.ext (by rw [← hbc, zero_mul]; rfl)
    rw [this, map_zero]
  have he : a⁻¹ * (b : Ω) = c := by rw [← hbc, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  exact ⟨ha, ⟨c, b, hb, he⟩, by rw [residueAt_eq hj ψ hb he, inv_div]⟩
theorem ratio_self : ψ (ratio (S := S) hj j) = 1 := by
  have : ratio (S := S) hj j = 1 := Subtype.ext (div_self hj)
  rw [this, map_one]
variable (hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0)
include hxy in

theorem regularAt_chart (K : Chart (reducedPt hj ψ)) {f s : Poly S N} {e : ℕ} (hs : s ∈ monos K.1)
    (hf : f.IsHomogeneous e) (hse : s.IsHomogeneous e) :
    RegularAt hj ψ (aeval x f / aeval x s) ∧
      residueAt hj ψ (aeval x f / aeval x s) =
        aeval (reducedPt hj ψ) f / aeval (reducedPt hj ψ) s := by
  have hsx : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos (liftChart hxy K) hs
  have hsy : aeval (reducedPt hj ψ) s ≠ 0 := eval_ne_zero_of_mem_monos K hs
  have hψ : ∀ g : Poly S N, ψ (aeval (ratio hj) g) = aeval (reducedPt hj ψ) g :=
    fun g => comp_aeval_apply (ratio hj) ψ g
  have hc : ψ (aeval (ratio hj) s) ≠ 0 := by rw [hψ]; exact hsy
  have h : aeval x f / aeval x s * ((aeval (ratio hj) s : chartRing S x (singleChart hj)) : Ω) =
      (aeval (ratio hj) f : chartRing S x (singleChart hj)) := by
    rw [coe_aeval_ratio hj hse, coe_aeval_ratio hj hf]
    field_simp
  exact ⟨⟨_, _, hc, h⟩, by rw [residueAt_eq hj ψ hc h, hψ, hψ]⟩
theorem regularAt_mem_chart (K : Chart (reducedPt hj ψ)) (a : chartRing S x (liftChart hxy K)) :
    RegularAt hj ψ (a : Ω) ∧ residueAt hj ψ (a : Ω) ∈ chartRing S (reducedPt hj ψ) K := by
  obtain ⟨f, s, e, hs, hf, hse, ha⟩ := a.2
  rw [ha]
  obtain ⟨h1, h2⟩ := regularAt_chart hj ψ hxy K hs hf hse
  exact ⟨h1, h2 ▸ ⟨f, s, e, hs, hf, hse, rfl⟩⟩
theorem residueAt_ne_zero_of_isUnit (K : Chart (reducedPt hj ψ)) {a : chartRing S x (liftChart hxy K)}
    (ha : IsUnit a) : residueAt hj ψ (a : Ω) ≠ 0 := by
  obtain ⟨u, rfl⟩ := ha
  have h1 := regularAt_mem_chart hj ψ hxy K u
  have h2 := regularAt_mem_chart hj ψ hxy K ↑u⁻¹
  have hmul : ((u : chartRing S x (liftChart hxy K)) : Ω) *
      ((↑u⁻¹ : chartRing S x (liftChart hxy K)) : Ω) = 1 := by
    have := congrArg Subtype.val u.mul_inv
    exact this
  have := (h1.1.mul h2.1).2
  rw [hmul, residueAt_one] at this
  intro h0
  rw [h0, zero_mul] at this
  exact one_ne_zero this
def chartIns (K : Chart (reducedPt hj ψ)) : Chart (reducedPt hj ψ) :=
  ⟨insert j K.1, Finset.insert_nonempty _ _, Finset.insert_subset_iff.mpr
    ⟨(mem_support _).mpr (by change ψ (ratio hj j) ≠ 0; rw [ratio_self hj ψ]; exact one_ne_zero),
      K.2.2⟩⟩
variable (Q : LineBundle S x) {q0 q1 : Ω} {Q1 : Submodule (chartRing S x (singleChart hj)) Ω}
  {c0 : chartRing S x (singleChart hj)}
theorem ne_zero_of_generator (hc : (c0 : Ω) = q0 * q1) (hψ : ψ c0 ≠ 0) : q0 ≠ 0 := by
  rintro rfl
  apply hψ
  have : c0 = 0 := Subtype.ext (by rw [hc, zero_mul]; rfl)
  rw [this, map_zero]
theorem regularAt_div (hc : (c0 : Ω) = q0 * q1) (hψ : ψ c0 ≠ 0)
    (hQ1 : Q.sub (singleChart hj) * Q1 = 1) (hq1 : q1 ∈ Q1)
    (K : Chart (reducedPt hj ψ)) {q : Ω} (hq : q ∈ Q.sub (liftChart hxy K)) :
    RegularAt hj ψ (q / q0) := by
  have hsub : (singleChart hj).1 ⊆ (liftChart hxy (chartIns hj ψ K)).1 :=
    Finset.singleton_subset_iff.mpr (Finset.mem_insert_self j K.1)
  have hKsub : (liftChart hxy K).1 ⊆ (liftChart hxy (chartIns hj ψ K)).1 := Finset.subset_insert j K.1
  have hq' := Q.mono _ _ hKsub q hq
  obtain ⟨a, ha, haq⟩ := (Q.mem_iff _ _ hsub q).mp hq'
  have hψa : ψ a ≠ 0 := by
    have := residueAt_ne_zero_of_isUnit hj ψ hxy (chartIns hj ψ K) ha
    rwa [show ((chartIncl hsub a : chartRing S x _) : Ω) = (a : Ω) from rfl, residueAt_of_mem] at this
  have hm := Submodule.mul_mem_mul haq hq1
  rw [hQ1] at hm
  obtain ⟨b, hb⟩ := Submodule.mem_one.mp hm
  have hb' : (b : Ω) = (a : Ω) * q * q1 := hb
  have hq00 := ne_zero_of_generator hj ψ hc hψ
  refine ⟨b, a * c0, by rw [map_mul]; exact mul_ne_zero hψa hψ, ?_⟩
  rw [Subalgebra.coe_mul, hc, hb']
  field_simp
theorem regularAt_mul_generator (hq0 : q0 ∈ Q.sub (singleChart hj)) (K : Chart (reducedPt hj ψ))
    {Qinv : Submodule (chartRing S x (liftChart hxy K)) Ω} (hinv : Q.sub (liftChart hxy K) * Qinv = 1)
    {q' : Ω} (hq' : q' ∈ Qinv) : RegularAt hj ψ (q' * q0) := by
  have hsub : (singleChart hj).1 ⊆ (liftChart hxy (chartIns hj ψ K)).1 :=
    Finset.singleton_subset_iff.mpr (Finset.mem_insert_self j K.1)
  have hKsub : (liftChart hxy K).1 ⊆ (liftChart hxy (chartIns hj ψ K)).1 := Finset.subset_insert j K.1
  have hq0' := Q.mono _ _ hsub q0 hq0
  obtain ⟨α, hα, hαq⟩ := (Q.mem_iff _ _ hKsub q0).mp hq0'
  have hm := Submodule.mul_mem_mul hαq hq'
  rw [hinv] at hm
  obtain ⟨β, hβ⟩ := Submodule.mem_one.mp hm
  have hβ' : (β : Ω) = (α : Ω) * q0 * q' := hβ
  have hαne : residueAt hj ψ (α : Ω) ≠ 0 :=
    residueAt_ne_zero_of_isUnit hj ψ hxy (chartIns hj ψ K) (a := chartIncl hKsub α) hα
  have hα' := regularAt_mem_chart hj ψ hxy K α
  have hβr := regularAt_mem_chart hj ψ hxy K β
  obtain ⟨hα0, hinvr, -⟩ := hα'.1.inv hαne
  have he : q' * q0 = (β : Ω) * (α : Ω)⁻¹ := by
    rw [hβ']
    field_simp
  rw [he]
  exact (hβr.1.mul hinvr).1
def restrictSub (q0 : Ω) (K : Chart (reducedPt hj ψ)) : Submodule (chartRing S (reducedPt hj ψ) K) K' :=
  Submodule.span _ ((fun q => residueAt hj ψ (q / q0)) '' (Q.sub (liftChart hxy K) : Set Ω))
theorem restrictSub_mono (q0 : Ω) (K L : Chart (reducedPt hj ψ)) (h : K.1 ⊆ L.1) (z : K')
    (hz : z ∈ restrictSub hj ψ hxy Q q0 K) : z ∈ restrictSub hj ψ hxy Q q0 L := by
  refine Submodule.span_induction (p := fun z _ => z ∈ restrictSub hj ψ hxy Q q0 L) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, rfl⟩
    exact Submodule.subset_span ⟨q, Q.mono (liftChart hxy K) (liftChart hxy L) h q hq, rfl⟩
  · exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    exact Submodule.smul_mem _ (chartIncl h a) hz
def restrictBundle (hq0 : q0 ∈ Q.sub (singleChart hj)) (hc : (c0 : Ω) = q0 * q1) (hψ : ψ c0 ≠ 0)
    (hQ1 : Q.sub (singleChart hj) * Q1 = 1) (hq1 : q1 ∈ Q1) : LineBundle S (reducedPt hj ψ) where
  sub := restrictSub hj ψ hxy Q q0
  mono := restrictSub_mono hj ψ hxy Q q0
  mem_iff K L h z := by
    have hq00 := ne_zero_of_generator hj ψ hc hψ
    constructor
    · intro hz
      refine Submodule.span_induction (p := fun z _ => ∃ a : chartRing S (reducedPt hj ψ) K,
        IsUnit (chartIncl h a) ∧ (a : K') • z ∈ restrictSub hj ψ hxy Q q0 K) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨q, hq, rfl⟩
        obtain ⟨α, hα, hαq⟩ := (Q.mem_iff (liftChart hxy K) (liftChart hxy L) h q).mp hq
        obtain ⟨u, hu⟩ := hα
        have hα1 := regularAt_mem_chart hj ψ hxy K α
        have hv := regularAt_mem_chart hj ψ hxy L ↑u⁻¹
        have hqr := regularAt_div hj ψ hxy Q hc hψ hQ1 hq1 L hq
        refine ⟨⟨_, hα1.2⟩, ?_, ?_⟩
        · refine IsUnit.of_mul_eq_one (a := chartIncl h ⟨_, hα1.2⟩) ⟨_, hv.2⟩ (Subtype.ext ?_)
          change residueAt hj ψ (α : Ω) * residueAt hj ψ ((↑u⁻¹ : chartRing S x (liftChart hxy L)) : Ω) = 1
          have hmul : (α : Ω) * ((↑u⁻¹ : chartRing S x (liftChart hxy L)) : Ω) = 1 := by
            have h1 := congrArg Subtype.val u.mul_inv
            rw [hu] at h1
            exact h1
          rw [← (hα1.1.mul hv.1).2, hmul, residueAt_one]
        · change residueAt hj ψ (α : Ω) * residueAt hj ψ (q / q0) ∈ _
          rw [← (hα1.1.mul hqr).2, ← mul_div_assoc]
          exact Submodule.subset_span ⟨_, hαq, rfl⟩
      · exact ⟨1, by rw [map_one]; exact isUnit_one, by rw [smul_zero]; exact Submodule.zero_mem _⟩
      · rintro z1 z2 _ _ ⟨a1, ha1, h1⟩ ⟨a2, ha2, h2⟩
        refine ⟨a1 * a2, by rw [map_mul]; exact ha1.mul ha2, ?_⟩
        have : ((a1 * a2 : chartRing S (reducedPt hj ψ) K) : K') • (z1 + z2) =
            a2 • ((a1 : K') • z1) + a1 • ((a2 : K') • z2) := by
          change (a1 : K') * a2 * (z1 + z2) = (a2 : K') * ((a1 : K') * z1) + (a1 : K') * ((a2 : K') * z2)
          ring
        rw [this]
        exact add_mem (Submodule.smul_mem _ a2 h1) (Submodule.smul_mem _ a1 h2)
      · rintro b z _ ⟨a, ha, haz⟩
        obtain ⟨a0, ha0, ha0b⟩ := exists_isUnit_mul_mem h b
        refine ⟨a0 * a, by rw [map_mul]; exact ha0.mul ha, ?_⟩
        have : ((a0 * a : chartRing S (reducedPt hj ψ) K) : K') • (b • z) =
            (⟨_, ha0b⟩ : chartRing S (reducedPt hj ψ) K) • ((a : K') • z) := by
          change (a0 : K') * a * (b * z) = (a0 * b) * (a * z)
          ring
        rw [this]
        exact Submodule.smul_mem _ _ haz
    · rintro ⟨a, ⟨u, hu⟩, haz⟩
      have hL := restrictSub_mono hj ψ hxy Q q0 K L h _ haz
      have hinv : ((↑u⁻¹ : chartRing S (reducedPt hj ψ) L) : K') * (a : K') = 1 := by
        have h1 := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at h1
        exact h1
      have hz : z = (↑u⁻¹ : chartRing S (reducedPt hj ψ) L) • ((a : K') • z) := by
        rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
      rw [hz]
      exact Submodule.smul_mem _ _ hL
  fg K := by
    classical
    obtain ⟨T, hT⟩ := Q.fg (liftChart hxy K)
    have memQ : ∀ q ∈ Submodule.span (chartRing S x (liftChart hxy K)) (T : Set Ω),
        q ∈ Q.sub (liftChart hxy K) := fun q hq => by rwa [hT] at hq
    have hq00 := ne_zero_of_generator hj ψ hc hψ
    refine ⟨T.image (fun q => residueAt hj ψ (q / q0)), ?_⟩
    rw [Finset.coe_image]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨q, hq, rfl⟩
      exact Submodule.subset_span ⟨q, memQ q (Submodule.subset_span hq), rfl⟩
    · change restrictSub hj ψ hxy Q q0 K ≤ _
      rw [restrictSub, Submodule.span_le]
      rintro _ ⟨q, hq, rfl⟩
      rw [← hT] at hq
      refine Submodule.span_induction (p := fun q _ => residueAt hj ψ (q / q0) ∈
        Submodule.span (chartRing S (reducedPt hj ψ) K)
          ((fun q => residueAt hj ψ (q / q0)) '' (T : Set Ω))) ?_ ?_ ?_ ?_ hq
      · intro q hq
        exact Submodule.subset_span ⟨q, hq, rfl⟩
      · rw [zero_div, residueAt_zero]
        exact Submodule.zero_mem _
      · intro q q' hq hq' h1 h2
        rw [add_div, ((regularAt_div hj ψ hxy Q hc hψ hQ1 hq1 K (memQ q hq)).add
          (regularAt_div hj ψ hxy Q hc hψ hQ1 hq1 K (memQ q' hq'))).2]
        exact Submodule.add_mem _ h1 h2
      · intro a q hq h1
        have ha := regularAt_mem_chart hj ψ hxy K a
        rw [show (a • q) / q0 = (a : Ω) * (q / q0) from mul_div_assoc _ _ _,
          (ha.1.mul (regularAt_div hj ψ hxy Q hc hψ hQ1 hq1 K (memQ q hq))).2]
        exact Submodule.smul_mem _ ⟨_, ha.2⟩ h1
  invertible K := by
    obtain ⟨Qinv, hinv⟩ := Q.invertible (liftChart hxy K)
    have hq00 := ne_zero_of_generator hj ψ hc hψ
    refine ⟨Submodule.span _ ((fun q' => residueAt hj ψ (q' * q0)) '' (Qinv : Set Ω)),
      le_antisymm ?_ ?_⟩
    · change restrictSub hj ψ hxy Q q0 K * _ ≤ _
      rw [restrictSub, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨q, hq, rfl⟩, _, ⟨q', hq', rfl⟩, rfl⟩
      have hqq := Submodule.mul_mem_mul hq hq'
      rw [hinv] at hqq
      obtain ⟨γ, hγ⟩ := Submodule.mem_one.mp hqq
      have hγ' : (γ : Ω) = q * q' := hγ
      have hγr := regularAt_mem_chart hj ψ hxy K γ
      change residueAt hj ψ (q / q0) * residueAt hj ψ (q' * q0) ∈ _
      rw [← ((regularAt_div hj ψ hxy Q hc hψ hQ1 hq1 K hq).mul
        (regularAt_mul_generator hj ψ hxy Q hq0 K hinv hq')).2]
      have : q / q0 * (q' * q0) = (γ : Ω) := by
        rw [hγ']
        field_simp
      rw [this]
      exact Submodule.mem_one.mpr ⟨⟨_, hγr.2⟩, rfl⟩
    · rw [Submodule.one_le]
      have h1 : (1 : Ω) ∈ Q.sub (liftChart hxy K) * Qinv := by
        rw [hinv]
        exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      have key : RegularAt hj ψ 1 ∧ residueAt hj ψ 1 ∈ restrictSub hj ψ hxy Q q0 K *
          Submodule.span _ ((fun q' => residueAt hj ψ (q' * q0)) '' (Qinv : Set Ω)) := by
        refine Submodule.mul_induction_on (C := fun z => RegularAt hj ψ z ∧ residueAt hj ψ z ∈
          restrictSub hj ψ hxy Q q0 K *
            Submodule.span _ ((fun q' => residueAt hj ψ (q' * q0)) '' (Qinv : Set Ω))) h1 ?_ ?_
        · intro m hm n hn
          have hr1 := regularAt_div hj ψ hxy Q hc hψ hQ1 hq1 K hm
          have hr2 := regularAt_mul_generator hj ψ hxy Q hq0 K hinv hn
          have he : m * n = m / q0 * (n * q0) := by
            field_simp
          rw [he]
          exact ⟨(hr1.mul hr2).1, by
            rw [(hr1.mul hr2).2]
            exact Submodule.mul_mem_mul (Submodule.subset_span ⟨m, hm, rfl⟩)
              (Submodule.subset_span ⟨n, hn, rfl⟩)⟩
        · rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
          exact ⟨(ha1.add hb1).1, by rw [(ha1.add hb1).2]; exact Submodule.add_mem _ ha2 hb2⟩
      rw [← residueAt_one hj ψ]
      exact key.2
end Residue
end
end GroundTheory.Heights₂.Heights.Kleiman


