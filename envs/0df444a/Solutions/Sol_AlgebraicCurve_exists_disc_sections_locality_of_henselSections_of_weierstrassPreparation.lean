-- Prove2me | solution 1 for AlgebraicCurve.exists_disc_sections_locality_of_henselSections_of_weierstrassPreparation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e500b7f7-4a77-5bf5-ad75-59f4cecf4f95

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_disc_sections_locality_of_henselSections_of_weierstrassPreparation

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace SmoothDisc

section Generic

variable {K F : Type} [Field K] [Field F] [Algebra K F]

theorem evalAt_zero (P : Place K F) : P.evalAt (0 : F) = 0 := by
  rw [P.evalAt_of_mem (zero_mem _)]
  have h0 : (⟨(0 : F), zero_mem _⟩ : P.toValuationSubring) = 0 := rfl
  rw [h0, map_zero, ← map_zero (algebraMap K P.ResidueField), P.residueInv_algebraMap]

theorem evalAt_add (P : Place K F) (hP : P.IsRational) {f g : F} (hf : f ∈ P.toValuationSubring)
    (hg : g ∈ P.toValuationSubring) : P.evalAt (f + g) = P.evalAt f + P.evalAt g := by
  apply P.algebraMap_residueField_injective
  rw [map_add, P.algebraMap_evalAt hP (add_mem hf hg), P.algebraMap_evalAt hP hf,
    P.algebraMap_evalAt hP hg, ← map_add]
  rfl

theorem evalAt_eq_zero_iff (P : Place K F) (hP : P.IsRational) {f : F} (hf : f ∈ P.toValuationSubring) :
    P.evalAt f = 0 ↔ (⟨f, hf⟩ : P.toValuationSubring) ∈ maximalIdeal P.toValuationSubring := by
  rw [← IsLocalRing.residue_eq_zero_iff, ← P.algebraMap_evalAt hP hf, map_eq_zero_iff _ (RingHom.injective _)]

theorem isUnit_iff_inv_mem (O : Subring F) (g : ↥O) :
    IsUnit g ↔ (g : F) ≠ 0 ∧ (g : F)⁻¹ ∈ O := by
  constructor
  · rintro ⟨u, rfl⟩
    have h2 : ((u : ↥O) : F) * (((u⁻¹ : (↥O)ˣ) : ↥O) : F) = 1 := congrArg Subtype.val u.mul_inv
    have hne : ((u : ↥O) : F) ≠ 0 := fun h0 => by rw [h0, zero_mul] at h2; exact zero_ne_one h2
    exact ⟨hne, by rw [(eq_inv_of_mul_eq_one_right h2).symm]; exact Subtype.coe_prop _⟩
  · rintro ⟨hne, hinv⟩
    exact ⟨⟨g, ⟨(g : F)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hne), Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩

theorem ord_nonneg_of_mem (P : Place K F) {f : F} (hf : f ∈ P.toValuationSubring) : 0 ≤ P.ord f := by
  by_cases hf0 : f = 0
  · rw [hf0, P.ord_zero]
  · have hle : P.adicValuation f ≤ 1 := by
      rw [show f = ((⟨f, hf⟩ : P.toValuationSubring) : F) from rfl, P.adicValuation_coe]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
    have hne : P.adicValuation f ≠ 0 := P.adicValuation_ne_zero hf0
    have hlog : WithZero.log (P.adicValuation f) ≤ 0 := by
      rw [WithZero.log_le_iff_le_exp hne]; exact hle
    show 0 ≤ -(WithZero.log (P.adicValuation f))
    omega

theorem ord_pos_iff_evalAt_eq_zero (P : Place K F) (hP : P.IsRational) {f : F} (hf : f ∈ P.toValuationSubring)
    (hf0 : f ≠ 0) : 0 < P.ord f ↔ P.evalAt f = 0 := by
  rw [evalAt_eq_zero_iff P hP hf, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hpos hu
    obtain ⟨u, hu⟩ := hu
    have := P.ord_coe_unit u
    rw [hu] at this
    change P.ord f = 0 at this
    omega
  · intro hnu
    have h0 := ord_nonneg_of_mem P hf
    rcases h0.lt_or_eq with h | h
    · exact h
    · exact absurd (P.isUnit_mk_of_ord_eq_zero hf0 h.symm) hnu

theorem ord_eq_zero_of_isUnit (P : Place K F) {f : F} (hf : f ∈ P.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : P.toValuationSubring)) : P.ord f = 0 := by
  obtain ⟨u, hu⟩ := hu
  have := P.ord_coe_unit u
  rwa [hu] at this

end Generic

section PlaceOfSection

variable {L : Type} [Field L] (A : ValuationSubring L) {F : Type} [Field F] [Algebra L F]

theorem exists_place_of_section
    (S : Subring F) (ι : ↥A →+* ↥S) (hι : ∀ a : ↥A, ((ι a : ↥S) : F) = algebraMap L F (a : L))
    (t : ↥S)
    (hfrac : ∀ f : F, ∃ g h : ↥S, (h : F) ≠ 0 ∧ f * (h : F) = (g : F))
    (B : ValuationSubring F) (hBA : ∀ c : L, algebraMap L F c ∈ B ↔ c ∈ A) (hSB : ∀ f : ↥S, (f : F) ∈ B)
    (hunitB : ∀ f : ↥S, f ∉ (maximalIdeal ↥A).map ι → (f : F) ≠ 0 ∧ (f : F)⁻¹ ∈ B)
    (hB : ∀ f : F, f ∈ B → ∃ g h : ↥S, h ∉ (maximalIdeal ↥A).map ι ∧ f * (h : F) = (g : F))
    (h𝔮B : ∀ g : ↥S, g ∈ (maximalIdeal ↥A).map ι → (g : F)⁻¹ ∉ B ∨ (g : F) = 0)
    (htq : t ∉ (maximalIdeal ↥A).map ι)
    (he1 : ∀ f : F, f ≠ 0 → ∃ c : L, c ≠ 0 ∧ algebraMap L F c * f ∈ B ∧ (algebraMap L F c * f)⁻¹ ∈ B)
    (hprep : ∀ h : ↥S, h ∉ (maximalIdeal ↥A).map ι →
      ∃ (n : ℕ) (u : (↥S)ˣ) (r : Fin n → ↥A), (∀ i, r i ∈ maximalIdeal ↥A) ∧
        h = (u : ↥S) * ∏ i, (t - ι (r i)))
    (χ : ↥S →+* ↥A) (hχι : ∀ a : ↥A, χ (ι a) = a) (hc : χ t ∈ maximalIdeal ↥A)
    (hkerχ : RingHom.ker χ = Ideal.span {t - ι (χ t)}) :
    ∃ P : Place L F, P.IsRational ∧
      (∀ f : F, f ∈ P.toValuationSubring ↔ ∃ g h : ↥S, χ h ≠ 0 ∧ f * (h : F) = (g : F)) ∧
      (∀ f : ↥S, P.evalAt (f : F) = ((χ f : ↥A) : L)) ∧
      (∀ P' : Place L F, P'.IsRational →
        (∀ f : ↥S, (f : F) ∈ P'.toValuationSubring ∧ P'.evalAt (f : F) = ((χ f : ↥A) : L)) → P' = P) := by
  classical
  set c : ↥A := χ t with hcdef
  set π : ↥S := t - ι c with hπdef
  set 𝔭 : Ideal ↥S := RingHom.ker χ with h𝔭def
  haveI h𝔭p : 𝔭.IsPrime := RingHom.ker_isPrime χ
  have hmem𝔭 : ∀ g : ↥S, g ∈ 𝔭 ↔ χ g = 0 := fun g => RingHom.mem_ker
  have hπ𝔭 : π ∈ 𝔭 := by rw [hmem𝔭, hπdef, map_sub, hχι, hcdef, sub_self]
  have h𝔭span : ∀ g : ↥S, g ∈ 𝔭 → ∃ g₁ : ↥S, g = π * g₁ := by
    intro g hg
    have hg' : g ∈ Ideal.span {t - ι (χ t)} := by rw [← hkerχ]; exact hg
    obtain ⟨g₁, rfl⟩ := Ideal.mem_span_singleton'.mp hg'
    exact ⟨g₁, by rw [hπdef, hcdef, mul_comm]⟩
  have hιc𝔮 : ι c ∈ (maximalIdeal ↥A).map ι := Ideal.mem_map_of_mem _ hc
  have hπ𝔮 : π ∉ (maximalIdeal ↥A).map ι := by
    intro h
    apply htq
    have : t = π + ι c := by rw [hπdef]; ring
    rw [this]; exact Ideal.add_mem _ h hιc𝔮
  have hπ0 : (π : F) ≠ 0 := (hunitB π hπ𝔮).1
  have hπ0' : π ≠ 0 := fun h => hπ0 (by rw [h]; rfl)
  have hιa𝔭 : ∀ a : ↥A, a ≠ 0 → ι a ∉ 𝔭 := by
    intro a ha h; rw [hmem𝔭, hχι] at h; exact ha h
  have hunit𝔭 : ∀ u : (↥S)ˣ, (u : ↥S) ∉ 𝔭 := fun u h =>
    h𝔭p.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)
  have hne0 : ∀ h : ↥S, h ∉ 𝔭 → (h : F) ≠ 0 := by
    intro h hh h0
    apply hh
    have : h = 0 := Subtype.ext h0
    rw [this]; exact Ideal.zero_mem _

  let Vset : Set F := {f | ∃ g h : ↥S, h ∉ 𝔭 ∧ f * (h : F) = (g : F)}
  have hVmem : ∀ f : F, f ∈ Vset ↔ ∃ g h : ↥S, h ∉ 𝔭 ∧ f * (h : F) = (g : F) := fun f => Iff.rfl
  have hV_of_frac : ∀ (g h : ↥S), h ∉ 𝔭 → (g : F) / (h : F) ∈ Vset := fun g h hh =>
    ⟨g, h, hh, by rw [div_mul_cancel₀ _ (hne0 h hh)]⟩
  have hSV : ∀ g : ↥S, (g : F) ∈ Vset := fun g => ⟨g, 1, fun h => h𝔭p.ne_top ((Ideal.eq_top_iff_one _).mpr h),
    by simp⟩
  have hVmul : ∀ f₁ f₂ : F, f₁ ∈ Vset → f₂ ∈ Vset → f₁ * f₂ ∈ Vset := by
    rintro f₁ f₂ ⟨g₁, h₁, hh₁, e₁⟩ ⟨g₂, h₂, hh₂, e₂⟩
    refine ⟨g₁ * g₂, h₁ * h₂, fun h => (h𝔭p.mem_or_mem h).elim hh₁ hh₂, ?_⟩
    simp only [Subring.coe_mul]
    calc f₁ * f₂ * ((h₁ : F) * h₂) = (f₁ * h₁) * (f₂ * h₂) := by ring
      _ = g₁ * g₂ := by rw [e₁, e₂]
  have hVadd : ∀ f₁ f₂ : F, f₁ ∈ Vset → f₂ ∈ Vset → f₁ + f₂ ∈ Vset := by
    rintro f₁ f₂ ⟨g₁, h₁, hh₁, e₁⟩ ⟨g₂, h₂, hh₂, e₂⟩
    refine ⟨g₁ * h₂ + g₂ * h₁, h₁ * h₂, fun h => (h𝔭p.mem_or_mem h).elim hh₁ hh₂, ?_⟩
    simp only [Subring.coe_mul, Subring.coe_add]
    calc (f₁ + f₂) * ((h₁ : F) * h₂) = (f₁ * h₁) * h₂ + (f₂ * h₂) * h₁ := by ring
      _ = g₁ * h₂ + g₂ * h₁ := by rw [e₁, e₂]
  have hVneg : ∀ f : F, f ∈ Vset → -f ∈ Vset := by
    rintro f ⟨g, h, hh, e⟩
    exact ⟨-g, h, hh, by simp only [Subring.coe_neg]; rw [neg_mul, e]⟩
  have hVinv : ∀ h : ↥S, h ∉ 𝔭 → ((h : F))⁻¹ ∈ Vset := fun h hh =>
    ⟨1, h, hh, by rw [inv_mul_cancel₀ (hne0 h hh)]; simp⟩

  have hπinv : (π : F)⁻¹ ∉ Vset := by
    rintro ⟨g, h, hh, e⟩
    apply hh
    have e' : (h : F) = π * g := by
      have := congrArg (fun z => (π : F) * z) e
      rw [← mul_assoc, mul_inv_cancel₀ hπ0, one_mul] at this
      exact this
    have : h = π * g := Subtype.ext (by rw [e']; rfl)
    rw [this]
    exact Ideal.mul_mem_right _ _ hπ𝔭

  have hfactor : ∀ r : ↥A, r ∈ maximalIdeal ↥A → r ≠ c →
      ((t - ι r : ↥S) : F) ∈ Vset ∧ (((t - ι r : ↥S) : F))⁻¹ ∈ Vset := by
    intro r _ hrc
    have hnot : (t - ι r) ∉ 𝔭 := by
      rw [hmem𝔭, map_sub, hχι, ← hcdef, sub_eq_zero]
      exact fun h => hrc h.symm
    exact ⟨hSV _, hVinv _ hnot⟩
  have hprodNF : ∀ (n : ℕ) (r : Fin n → ↥A), (∀ i, r i ∈ maximalIdeal ↥A) →
      ∃ (k : ℕ) (w : F), w ∈ Vset ∧ w⁻¹ ∈ Vset ∧
        ((∏ i, (t - ι (r i)) : ↥S) : F) = (π : F) ^ k * w := by
    intro n
    induction n with
    | zero =>
      intro r _
      have h1 : (1 : F) ∈ Vset := by simpa using hSV 1
      exact ⟨0, 1, h1, by rw [inv_one]; exact h1, by simp⟩
    | succ n ih =>
      intro r hr
      obtain ⟨k, w, hw, hwi, e⟩ := ih (fun i => r i.succ) (fun i => hr i.succ)
      rw [Fin.prod_univ_succ]
      by_cases h0 : r 0 = c
      · refine ⟨k + 1, w, hw, hwi, ?_⟩
        rw [Subring.coe_mul, e, h0, pow_succ]
        change (π : F) * ((π : F) ^ k * w) = (π : F) ^ k * π * w
        ring
      · obtain ⟨h1, h2⟩ := hfactor (r 0) (hr 0) h0
        refine ⟨k, ((t - ι (r 0) : ↥S) : F) * w, hVmul _ _ h1 hw, ?_, ?_⟩
        · rw [mul_inv]; exact hVmul _ _ h2 hwi
        · rw [Subring.coe_mul, e]; ring
  have hVpow : ∀ n : ℕ, (π : F) ^ n ∈ Vset := by
    intro n
    induction n with
    | zero => simpa using hSV 1
    | succ n ih => rw [pow_succ]; exact hVmul _ _ ih (hSV π)
  have hVzpow : ∀ e : ℤ, 0 ≤ e → (π : F) ^ e ∈ Vset := by
    intro e he
    rw [show e = ((e.toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg he).symm, zpow_natCast]
    exact hVpow _
  have hVunit_S : ∀ u : (↥S)ˣ, ((u : ↥S) : F) ∈ Vset ∧ (((u : ↥S) : F))⁻¹ ∈ Vset :=
    fun u => ⟨hSV _, hVinv _ (hunit𝔭 u)⟩
  have hVunit_ι : ∀ a : ↥A, a ≠ 0 → ((ι a : ↥S) : F) ∈ Vset ∧ (((ι a : ↥S) : F))⁻¹ ∈ Vset :=
    fun a ha => ⟨hSV _, hVinv _ (hιa𝔭 a ha)⟩

  have hnot𝔮_of_unitB : ∀ g : ↥S, (g : F) ≠ 0 → (g : F)⁻¹ ∈ B → g ∉ (maximalIdeal ↥A).map ι := by
    intro g hg0 hgi hg
    rcases h𝔮B g hg with h | h
    · exact h hgi
    · exact hg0 h

  have hNF_S : ∀ s : ↥S, s ≠ 0 → ∃ (e : ℤ) (w : F), w ∈ Vset ∧ w⁻¹ ∈ Vset ∧ (s : F) = (π : F) ^ e * w := by
    intro s hs
    have hs0 : (s : F) ≠ 0 := fun h => hs (Subtype.ext h)
    obtain ⟨d, hd0, hds, hdsi⟩ := he1 (s : F) hs0

    have ha : d⁻¹ ∈ A := by
      rcases A.mem_or_inv_mem d with h | h
      · have : algebraMap L F d⁻¹ ∈ B := by
          have e : algebraMap L F d⁻¹ = (s : F) * (algebraMap L F d * (s : F))⁻¹ := by
            rw [map_inv₀, mul_inv, ← mul_assoc, mul_comm (s : F), mul_assoc, mul_inv_cancel₀ hs0, mul_one]
          rw [e]; exact mul_mem (hSB s) hdsi
        exact (hBA _).mp this
      · exact h
    set a : ↥A := ⟨d⁻¹, ha⟩ with hadef
    have ha0 : a ≠ 0 := fun h => inv_ne_zero hd0 (congrArg Subtype.val h)

    obtain ⟨g₁, h₁, hh₁, ebh⟩ := hB _ hds
    have hh₁0 : (h₁ : F) ≠ 0 := (hunitB h₁ hh₁).1
    have hb0 : algebraMap L F d * (s : F) ≠ 0 := mul_ne_zero ((map_ne_zero _).mpr hd0) hs0
    have hg₁0 : (g₁ : F) ≠ 0 := by rw [← ebh]; exact mul_ne_zero hb0 hh₁0
    have hg₁ : g₁ ∉ (maximalIdeal ↥A).map ι := by
      apply hnot𝔮_of_unitB g₁ hg₁0
      have e : ((g₁ : F))⁻¹ = ((h₁ : F))⁻¹ * (algebraMap L F d * (s : F))⁻¹ := by
        rw [← ebh, mul_inv, mul_comm]
      rw [e]; exact mul_mem (hunitB h₁ hh₁).2 hdsi
    obtain ⟨n₁, u₁, r₁, hr₁, eg₁⟩ := hprep g₁ hg₁
    obtain ⟨n₂, u₂, r₂, hr₂, eh₁⟩ := hprep h₁ hh₁
    obtain ⟨k₁, w₁, hw₁, hw₁i, ew₁⟩ := hprodNF n₁ r₁ hr₁
    obtain ⟨k₂, w₂, hw₂, hw₂i, ew₂⟩ := hprodNF n₂ r₂ hr₂
    have eg₁F : (g₁ : F) = ((u₁ : ↥S) : F) * ((π : F) ^ k₁ * w₁) := by
      rw [eg₁, Subring.coe_mul, ew₁]
    have eh₁F : (h₁ : F) = ((u₂ : ↥S) : F) * ((π : F) ^ k₂ * w₂) := by
      rw [eh₁, Subring.coe_mul, ew₂]

    have hw₂0 : w₂ ≠ 0 := by
      intro h0; apply hh₁0; rw [eh₁F, h0, mul_zero, mul_zero]
    have hu₂0 : ((u₂ : ↥S) : F) ≠ 0 := hne0 _ (hunit𝔭 u₂)
    refine ⟨(k₁ : ℤ) - (k₂ : ℤ), ((ι a : ↥S) : F) * (((u₁ : ↥S) : F) * w₁) * (((u₂ : ↥S) : F) * w₂)⁻¹, ?_, ?_, ?_⟩
    · exact hVmul _ _ (hVmul _ _ (hVunit_ι a ha0).1 (hVmul _ _ (hVunit_S u₁).1 hw₁))
        (by rw [mul_inv]; exact hVmul _ _ (hVunit_S u₂).2 hw₂i)
    · rw [mul_inv, mul_inv, inv_inv]
      exact hVmul _ _ (hVmul _ _ (hVunit_ι a ha0).2 (by rw [mul_inv]; exact hVmul _ _ (hVunit_S u₁).2 hw₁i))
        (hVmul _ _ (hVunit_S u₂).1 hw₂)
    ·
      have hsF : (s : F) = algebraMap L F (a : L) * (g₁ : F) / (h₁ : F) := by
        rw [eq_div_iff hh₁0, ← ebh, hadef]
        change (s : F) * (h₁ : F) = algebraMap L F d⁻¹ * (algebraMap L F d * (s : F) * (h₁ : F))
        rw [map_inv₀, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).mpr hd0), one_mul]
      rw [hsF, ← hι a, eg₁F, eh₁F, zpow_sub₀ hπ0, zpow_natCast, zpow_natCast]
      field_simp

  have hNF : ∀ f : F, f ≠ 0 → ∃ (e : ℤ) (w : F), w ∈ Vset ∧ w⁻¹ ∈ Vset ∧ f = (π : F) ^ e * w := by
    intro f hf
    obtain ⟨g₀, h₀, hh₀, e₀⟩ := hfrac f
    have hg₀ : g₀ ≠ 0 := by
      intro h; rw [h] at e₀; exact mul_ne_zero hf hh₀ (by simpa using e₀)
    have hh₀' : h₀ ≠ 0 := fun h => hh₀ (by rw [h]; rfl)
    obtain ⟨e₁, w₁, hw₁, hw₁i, ew₁⟩ := hNF_S g₀ hg₀
    obtain ⟨e₂, w₂, hw₂, hw₂i, ew₂⟩ := hNF_S h₀ hh₀'
    have hw₂0 : w₂ ≠ 0 := by intro h0; apply hh₀; rw [ew₂, h0, mul_zero]
    refine ⟨e₁ - e₂, w₁ * w₂⁻¹, hVmul _ _ hw₁ hw₂i, by rw [mul_inv, inv_inv]; exact hVmul _ _ hw₁i hw₂, ?_⟩
    have hfF : f = (g₀ : F) / (h₀ : F) := by rw [eq_div_iff hh₀, e₀]
    rw [hfF, ew₁, ew₂, zpow_sub₀ hπ0]
    field_simp

  have hwne : ∀ (f : F) (e : ℤ) (w : F), f ≠ 0 → f = (π : F) ^ e * w → w ≠ 0 := by
    rintro f e w hf rfl rfl
    exact hf (by rw [mul_zero])
  have hexp : ∀ (e : ℤ) (w : F), w ≠ 0 → w⁻¹ ∈ Vset → (π : F) ^ e * w ∈ Vset → 0 ≤ e := by
    intro e w hw0 hwi hmem
    by_contra hneg
    push Not at hneg
    apply hπinv
    have e1 : ((π : F))⁻¹ = (π : F) ^ (-e - 1) * ((π : F) ^ e * w) * w⁻¹ := by
      rw [mul_assoc, mul_assoc, mul_inv_cancel₀ hw0, mul_one, ← zpow_add₀ hπ0]
      have : -e - 1 + e = -1 := by ring
      rw [this, zpow_neg_one]
    rw [e1]
    exact hVmul _ _ (hVmul _ _ (hVzpow _ (by omega)) hmem) hwi

  let V : ValuationSubring F :=
    { carrier := Vset
      mul_mem' := fun {f₁ f₂} h₁ h₂ => hVmul _ _ h₁ h₂
      one_mem' := by simpa using hSV 1
      add_mem' := fun {f₁ f₂} h₁ h₂ => hVadd _ _ h₁ h₂
      zero_mem' := by simpa using hSV 0
      neg_mem' := fun {f} hf => hVneg _ hf
      mem_or_inv_mem' := by
        intro f
        change f ∈ Vset ∨ f⁻¹ ∈ Vset
        by_cases hf0 : f = 0
        · left; rw [hf0]; simpa using hSV 0
        obtain ⟨e, w, hw, hwi, ef⟩ := hNF f hf0
        rcases le_or_gt 0 e with he | he
        · left; rw [ef]; exact hVmul _ _ (hVzpow e he) hw
        · right
          rw [ef, mul_inv, ← zpow_neg]
          exact hVmul _ _ (hVzpow _ (by omega)) hwi }
  have hVmem' : ∀ f : F, f ∈ V ↔ f ∈ Vset := fun f => Iff.rfl

  have hVunit : ∀ (f : F) (hf : f ∈ V), IsUnit (⟨f, hf⟩ : ↥V) ↔ f ≠ 0 ∧ f⁻¹ ∈ Vset := fun f hf =>
    isUnit_iff_inv_mem V.toSubring ⟨f, hf⟩
  have hπV : (π : F) ∈ V := hSV π
  set πV : ↥V := ⟨(π : F), hπV⟩ with hπVdef
  have hπV_notunit : ¬ IsUnit πV := fun h => hπinv ((hVunit _ hπV).mp h).2
  have hπV0 : πV ≠ 0 := fun h => hπ0 (congrArg Subtype.val h)

  have hNF_V : ∀ x : ↥V, x ≠ 0 → ∃ (n : ℕ) (w : (↥V)ˣ), x = πV ^ n * (w : ↥V) := by
    intro x hx
    have hx0 : (x : F) ≠ 0 := fun h => hx (Subtype.ext h)
    obtain ⟨e, w, hw, hwi, ex⟩ := hNF (x : F) hx0
    have hw0 : w ≠ 0 := hwne _ _ _ hx0 ex
    have he : 0 ≤ e := hexp e w hw0 hwi (by rw [← ex]; exact x.2)
    have hwu : IsUnit (⟨w, hw⟩ : ↥V) := (hVunit w hw).mpr ⟨hw0, hwi⟩
    refine ⟨e.toNat, hwu.unit, Subtype.ext ?_⟩
    change (x : F) = (π : F) ^ e.toNat * w
    rw [ex, ← zpow_natCast, Int.toNat_of_nonneg he]
  have hcoeNF : ∀ (x : ↥V) (n : ℕ) (w : (↥V)ˣ), x = πV ^ n * (w : ↥V) →
      (x : F) = (π : F) ^ n * ((w : ↥V) : F) := by
    intro x n w e
    have := congrArg Subtype.val e
    simpa only [MulMemClass.coe_mul, SubmonoidClass.coe_pow] using this
  have hVunitF : ∀ w : (↥V)ˣ, ((w : ↥V) : F) ∈ Vset ∧ (((w : ↥V) : F))⁻¹ ∈ Vset ∧ ((w : ↥V) : F) ≠ 0 := by
    intro w
    have h := (hVunit _ (w : ↥V).2).mp (by simpa using w.isUnit)
    exact ⟨(w : ↥V).2, h.2, h.1⟩
  have hirrV : Irreducible πV := by
    refine ⟨hπV_notunit, ?_⟩
    intro x y hxy
    have hx0 : x ≠ 0 := by rintro rfl; exact hπV0 (by rw [hxy, zero_mul])
    have hy0 : y ≠ 0 := by rintro rfl; exact hπV0 (by rw [hxy, mul_zero])
    obtain ⟨n₁, w₁, ex⟩ := hNF_V x hx0
    obtain ⟨n₂, w₂, ey⟩ := hNF_V y hy0
    by_contra hnu
    push Not at hnu
    obtain ⟨hxu, hyu⟩ := hnu
    have hn₁ : n₁ ≠ 0 := by rintro rfl; apply hxu; rw [ex, pow_zero, one_mul]; exact w₁.isUnit
    have hn₂ : n₂ ≠ 0 := by rintro rfl; apply hyu; rw [ey, pow_zero, one_mul]; exact w₂.isUnit

    apply hπinv
    set W : F := ((w₁ : ↥V) : F) * ((w₂ : ↥V) : F) with hW
    have hWV : W ∈ Vset := hVmul _ _ (hVunitF w₁).1 (hVunitF w₂).1
    have eπ : (π : F) = (π : F) ^ (n₁ + n₂) * W := by
      have h1 : ((πV : ↥V) : F) = (x : F) * (y : F) := by rw [hxy]; rfl
      have h2 : ((πV : ↥V) : F) = (π : F) := rfl
      rw [h2, hcoeNF x n₁ w₁ ex, hcoeNF y n₂ w₂ ey] at h1
      rw [hW, pow_add]
      exact h1.trans (by ring)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n₁ + n₂ = m + 2 := ⟨n₁ + n₂ - 2, by omega⟩
    have e1 : (1 : F) = (π : F) ^ (m + 1) * W := by
      apply mul_left_cancel₀ hπ0
      conv_lhs => rw [mul_one, eπ, hm]
      ring
    have e2 : ((π : F))⁻¹ = (π : F) ^ m * W := by
      symm
      apply eq_inv_of_mul_eq_one_left
      rw [e1]; ring
    rw [e2]
    exact hVmul _ _ (hVpow m) hWV
  haveI : IsDiscreteValuationRing ↥V :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
      ⟨πV, hirrV, fun {x} hx => by
        obtain ⟨n, w, e⟩ := hNF_V x hx
        exact ⟨n, ⟨w, e.symm⟩⟩⟩

  have hconstV : ∀ x : L, algebraMap L F x ∈ V := by
    intro x
    by_cases hx0 : x = 0
    · rw [hx0, map_zero]; exact zero_mem _
    rcases A.mem_or_inv_mem x with hx | hx
    · have : algebraMap L F x = ((ι ⟨x, hx⟩ : ↥S) : F) := (hι ⟨x, hx⟩).symm
      rw [this]; exact hSV _
    · have hne : (⟨x⁻¹, hx⟩ : ↥A) ≠ 0 := fun h => inv_ne_zero hx0 (congrArg Subtype.val h)
      have : algebraMap L F x = (((ι ⟨x⁻¹, hx⟩ : ↥S) : F))⁻¹ := by
        rw [hι, ← map_inv₀]; simp
      rw [this]; exact (hVunit_ι _ hne).2
  have hVtop : V ≠ ⊤ := fun h => hπinv (by rw [← hVmem']; rw [h]; exact ValuationSubring.mem_top _)

  obtain ⟨P, hPV⟩ : ∃ P : Place L F, P.toValuationSubring = V :=
    ⟨{ toValuationSubring := V
       algebraMap_mem' := hconstV
       ne_top' := hVtop
       isPrincipalIdealRing' := inferInstance }, rfl⟩
  have hPmem : ∀ f : F, f ∈ P.toValuationSubring ↔ ∃ g h : ↥S, h ∉ 𝔭 ∧ f * (h : F) = (g : F) := by
    intro f; rw [hPV]; exact Iff.rfl
  have hPmem' : ∀ f : F, f ∈ P.toValuationSubring ↔ ∃ g h : ↥S, χ h ≠ 0 ∧ f * (h : F) = (g : F) := by
    intro f
    rw [hPmem]
    simp only [hmem𝔭]

  have hπP_nonunit : ∀ (z : F) (hz : z ∈ Vset), (⟨(π : F) * z, mul_mem (hPV ▸ hπV : (π : F) ∈ P.toValuationSubring)
      ((hPmem z).mpr hz)⟩ : ↥P.toValuationSubring) ∈ maximalIdeal ↥P.toValuationSubring := by
    intro z hz
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h2 := ((isUnit_iff_inv_mem P.toValuationSubring.toSubring _).mp hu)
    obtain ⟨hne, hinv⟩ := h2
    change ((π : F) * z)⁻¹ ∈ P.toValuationSubring at hinv
    apply hπinv
    have hz0 : z ≠ 0 := fun h0 => hne (by change (π : F) * z = 0; rw [h0, mul_zero])
    have e : ((π : F))⁻¹ = z * ((π : F) * z)⁻¹ := by
      rw [mul_inv, ← mul_assoc, mul_comm z, mul_assoc, mul_inv_cancel₀ hz0, mul_one]
    rw [e]
    exact hVmul _ _ hz ((hPmem _).mp hinv)
  have hval : ∀ (f : F) (g h : ↥S) (hh : h ∉ 𝔭) (e : f * (h : F) = (g : F)),
      ∃ hf : f ∈ P.toValuationSubring,
        IsLocalRing.residue ↥P.toValuationSubring ⟨f, hf⟩ =
          algebraMap L P.ResidueField (((χ g : ↥A) : L) / ((χ h : ↥A) : L)) := by
    intro f g h hh e
    have hf : f ∈ P.toValuationSubring := (hPmem f).mpr ⟨g, h, hh, e⟩
    refine ⟨hf, ?_⟩
    have hχh0 : ((χ h : ↥A) : L) ≠ 0 := by
      intro h0; apply hh; rw [hmem𝔭]; exact Subtype.ext h0
    have hh0 : (h : F) ≠ 0 := hne0 h hh

    set N : ↥S := g * ι (χ h) - h * ι (χ g) with hN
    have hN𝔭 : N ∈ 𝔭 := by
      rw [hmem𝔭, hN, map_sub, map_mul, map_mul, hχι, hχι]; ring
    obtain ⟨N₁, hN₁⟩ := h𝔭span N hN𝔭
    have hd : h * ι (χ h) ∉ 𝔭 := fun hd => (h𝔭p.mem_or_mem hd).elim hh (hιa𝔭 _ (fun h0 => hχh0 (by rw [h0]; rfl)))
    set v : L := ((χ g : ↥A) : L) / ((χ h : ↥A) : L) with hv
    have hdiff : f - algebraMap L F v = (π : F) * ((N₁ : F) / ((h * ι (χ h) : ↥S) : F)) := by
      have hfgh : f = (g : F) / (h : F) := by rw [eq_div_iff hh0, e]
      have hιh : ((ι (χ h) : ↥S) : F) = algebraMap L F ((χ h : ↥A) : L) := hι _
      have hιg : ((ι (χ g) : ↥S) : F) = algebraMap L F ((χ g : ↥A) : L) := hι _
      have hιh0 : ((ι (χ h) : ↥S) : F) ≠ 0 := by rw [hιh]; exact (map_ne_zero _).mpr hχh0
      have hNF' : (N : F) = (π : F) * (N₁ : F) := by rw [hN₁]; rfl
      have hNF'' : (N : F) = (g : F) * ((ι (χ h) : ↥S) : F) - (h : F) * ((ι (χ g) : ↥S) : F) := by
        rw [hN]; simp only [AddSubgroupClass.coe_sub, Subring.coe_mul]
      rw [hfgh, hv, map_div₀, ← hιh, ← hιg, mul_div_assoc']
      rw [← hNF', hNF'', Subring.coe_mul]
      field_simp
    have hzV : (N₁ : F) / ((h * ι (χ h) : ↥S) : F) ∈ Vset := hV_of_frac _ _ hd
    have hmax := hπP_nonunit _ hzV
    have hcv : algebraMap L F v ∈ P.toValuationSubring := P.algebraMap_mem' v
    have hsub : (⟨f, hf⟩ : ↥P.toValuationSubring) - ⟨algebraMap L F v, hcv⟩ ∈ maximalIdeal ↥P.toValuationSubring := by
      have : (⟨f, hf⟩ : ↥P.toValuationSubring) - ⟨algebraMap L F v, hcv⟩ =
          ⟨(π : F) * ((N₁ : F) / ((h * ι (χ h) : ↥S) : F)), mul_mem (hPV ▸ hπV) ((hPmem _).mpr hzV)⟩ :=
        Subtype.ext hdiff
      rw [this]; exact hmax
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hsub
    rw [hsub, IsScalarTower.algebraMap_apply L ↥P.toValuationSubring P.ResidueField]
    congr 1
  have hrat : P.IsRational := by
    intro q
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective q
    obtain ⟨g, h, hh, e⟩ := (hPmem _).mp z.2
    obtain ⟨hf, hres⟩ := hval (z : F) g h hh e
    exact ⟨_, by rw [← hres]⟩
  have hevalfrac : ∀ (f : F) (g h : ↥S), h ∉ 𝔭 → f * (h : F) = (g : F) →
      P.evalAt f = ((χ g : ↥A) : L) / ((χ h : ↥A) : L) := by
    intro f g h hh e
    obtain ⟨hf, hres⟩ := hval f g h hh e
    rw [P.evalAt_of_mem hf, hres, P.residueInv_algebraMap]
  have hevalS : ∀ f : ↥S, P.evalAt (f : F) = ((χ f : ↥A) : L) := by
    intro f
    have h1 : (1 : ↥S) ∉ 𝔭 := fun h => h𝔭p.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    rw [hevalfrac (f : F) f 1 h1 (by simp), map_one]
    simp
  refine ⟨P, hrat, hPmem', hevalS, ?_⟩

  intro P' hP' hP'S
  have hle : ∀ z : F, z ∈ Vset → z ∈ P'.toValuationSubring := by
    rintro z ⟨g, h, hh, e⟩
    have hhP' : (h : F) ∈ P'.toValuationSubring := (hP'S h).1
    have hev : P'.evalAt (h : F) ≠ 0 := by
      rw [(hP'S h).2]
      intro h0; apply hh; rw [hmem𝔭]; exact Subtype.ext h0
    have hu : IsUnit (⟨(h : F), hhP'⟩ : ↥P'.toValuationSubring) := by
      by_contra hnu
      exact hev ((evalAt_eq_zero_iff P' hP' hhP').mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
    obtain ⟨-, hinv⟩ := (isUnit_iff_inv_mem P'.toValuationSubring.toSubring _).mp hu
    have ez : z = (g : F) * ((h : F))⁻¹ := by rw [← e, mul_assoc, mul_inv_cancel₀ (hne0 h hh), mul_one]
    rw [ez]
    exact mul_mem (hP'S g).1 hinv
  apply Place.ext
  rw [hPV]
  by_contra hneq
  have hlt : ∃ z : F, z ∈ P'.toValuationSubring ∧ z ∉ Vset := by
    by_contra hall
    push Not at hall
    exact hneq (le_antisymm (fun z hz => hall z hz) (fun z hz => hle z hz))
  obtain ⟨z, hzP', hzV⟩ := hlt
  have hz0 : z ≠ 0 := fun h0 => hzV (h0 ▸ (by simpa using hSV 0))
  obtain ⟨e, w, hw, hwi, ez⟩ := hNF z hz0
  have hw0 : w ≠ 0 := hwne _ _ _ hz0 ez
  have he : e < 0 := by
    by_contra hge; push Not at hge
    exact hzV (by rw [ez]; exact hVmul _ _ (hVzpow e hge) hw)

  have hπinvP' : ((π : F))⁻¹ ∈ P'.toValuationSubring := by
    have e1 : ((π : F))⁻¹ = (π : F) ^ (-e - 1) * z * w⁻¹ := by
      rw [ez, mul_assoc, mul_assoc, mul_inv_cancel₀ hw0, mul_one, ← zpow_add₀ hπ0]
      have : -e - 1 + e = -1 := by ring
      rw [this, zpow_neg_one]
    rw [e1]
    exact mul_mem (mul_mem (hle _ (hVzpow _ (by omega))) hzP') (hle _ hwi)
  apply P'.ne_top'
  apply eq_top_iff.mpr
  intro y _
  by_cases hy0 : y = 0
  · rw [hy0]; exact zero_mem _
  obtain ⟨e', w', hw', -, ey⟩ := hNF y hy0
  rw [ey]
  refine mul_mem ?_ (hle _ hw')
  rcases le_or_gt 0 e' with he' | he'
  · exact hle _ (hVzpow e' he')
  · rw [show e' = -((-e').toNat : ℤ) by omega, zpow_neg, zpow_natCast, ← inv_pow]
    exact pow_mem hπinvP' _

end PlaceOfSection

end SmoothDisc

open SmoothDisc in
theorem solution
    {L : Type} [Field L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F]
    (S : Subring F) (hS : IsLocalRing ↥S)
    (ι : ↥A →+* ↥S) (hι : ∀ a : ↥A, ((ι a : ↥S) : F) = algebraMap L F (a : L))
    (χ₀ : ↥S →+* ResidueField ↥A)
    (hχ₀C : ∀ a : ↥A, χ₀ (ι a) = IsLocalRing.residue ↥A a)
    (hmax : ∀ f : ↥S, f ∈ maximalIdeal ↥S ↔ χ₀ f = 0)
    (t : ↥S)
    (hfrac : ∀ f : F, ∃ g h : ↥S, (h : F) ≠ 0 ∧ f * (h : F) = (g : F))
    (B : ValuationSubring F) (hBA : ∀ c : L, algebraMap L F c ∈ B ↔ c ∈ A) (hSB : ∀ f : ↥S, (f : F) ∈ B)
    (hunitB : ∀ f : ↥S, f ∉ (maximalIdeal ↥A).map ι → (f : F) ≠ 0 ∧ (f : F)⁻¹ ∈ B)
    (hB : ∀ f : F, f ∈ B → ∃ g h : ↥S, h ∉ (maximalIdeal ↥A).map ι ∧ f * (h : F) = (g : F))
    (hprime : ((maximalIdeal ↥A).map ι).IsPrime) (htq : t ∉ (maximalIdeal ↥A).map ι)
    (he1 : ∀ f : F, f ≠ 0 → ∃ c : L, c ≠ 0 ∧ algebraMap L F c * f ∈ B ∧ (algebraMap L F c * f)⁻¹ ∈ B)
    (hhensel : ∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
      ∃! χ : ↥S →+* ↥A, (∀ a : ↥A, χ (ι a) = a) ∧ (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ t = c)
    (hker : ∀ χ : ↥S →+* ↥A, (∀ a : ↥A, χ (ι a) = a) → (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) →
      RingHom.ker χ = Ideal.span {t - ι (χ t)})
    (hprep : ∀ h : ↥S, h ∉ (maximalIdeal ↥A).map ι →
      ∃ (n : ℕ) (u : (↥S)ˣ) (r : Fin n → ↥A), (∀ i, r i ∈ maximalIdeal ↥A) ∧
        h = (u : ↥S) * ∏ i, (t - ι (r i))) :
    ∃ D : Set (Place L F),
      (∀ P, P ∈ D ↔ (P.IsRational ∧ (∀ f : ↥S, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
        (∀ f : ↥S, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0))) ∧
      (∀ χ : ↥S →+* ↥A, (∀ a : ↥A, χ (ι a) = a) → (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) →
        ∃! P, P ∈ D ∧ ∀ f : ↥S, P.evalAt (f : F) = ((χ f : ↥A) : L)) ∧
      (∀ P ∈ D, ∀ f : F, f ∈ P.toValuationSubring ↔
        ∃ g h : ↥S, P.evalAt (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧
      (∀ f : F, f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
        ∃ (c : L) (u : (↥S)ˣ), c ≠ 0 ∧ algebraMap L F c * f = ((u : ↥S) : F)) ∧
      (∀ f : F, f ∈ B → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S) := by
  classical
  set 𝔮 : Ideal ↥S := (maximalIdeal ↥A).map ι with h𝔮def

  obtain ⟨χz, ⟨hz1, hz2, hz3⟩, -⟩ := hhensel 0 (map_zero _)
  have hχ₀t : χ₀ t = 0 := by rw [← hz2 t, hz3, map_zero]

  have h𝔮B : ∀ g : ↥S, g ∈ 𝔮 → (g : F)⁻¹ ∉ B ∨ (g : F) = 0 := by
    let jB : ↥S →+* ↥B :=
      { toFun := fun f => ⟨(f : F), hSB f⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hle : 𝔮 ≤ (maximalIdeal ↥B).comap jB := by
      change (maximalIdeal ↥A).map ι ≤ _
      rw [Ideal.map_le_iff_le_comap]
      intro m hm
      rw [Ideal.mem_comap, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨hne, hinv⟩ := (isUnit_iff_inv_mem B.toSubring _).mp hu
      change ((ι m : ↥S) : F) ≠ 0 at hne
      change (((ι m : ↥S) : F))⁻¹ ∈ B at hinv
      rw [hι] at hne hinv
      rw [← map_inv₀, hBA] at hinv
      have hm0 : ((m : ↥A) : L) ≠ 0 := fun h0 => hne (by rw [h0, map_zero])
      have hunitA : IsUnit (m : ↥A) :=
        IsUnit.of_mul_eq_one (b := ⟨((m : ↥A) : L)⁻¹, hinv⟩) (Subtype.ext (mul_inv_cancel₀ hm0))
      exact (IsLocalRing.mem_maximalIdeal _).mp hm hunitA
    intro g hg
    have hg' : ¬ IsUnit (jB g) := (IsLocalRing.mem_maximalIdeal _).mp (hle hg)
    rw [isUnit_iff_inv_mem B.toSubring] at hg'
    change ¬ ((g : F) ≠ 0 ∧ ((g : F))⁻¹ ∈ B) at hg'
    by_cases h0 : (g : F) = 0
    · exact Or.inr h0
    · exact Or.inl (fun h => hg' ⟨h0, h⟩)

  have hcχ : ∀ χ : ↥S →+* ↥A, (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) → χ t ∈ maximalIdeal ↥A := by
    intro χ h2
    rw [← IsLocalRing.residue_eq_zero_iff, h2, hχ₀t]

  have hplace : ∀ χ : ↥S →+* ↥A, (∀ a : ↥A, χ (ι a) = a) →
      (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) →
      ∃ P : Place L F, P.IsRational ∧
        (∀ f : F, f ∈ P.toValuationSubring ↔ ∃ g h : ↥S, χ h ≠ 0 ∧ f * (h : F) = (g : F)) ∧
        (∀ f : ↥S, P.evalAt (f : F) = ((χ f : ↥A) : L)) ∧
        (∀ P' : Place L F, P'.IsRational →
          (∀ f : ↥S, (f : F) ∈ P'.toValuationSubring ∧ P'.evalAt (f : F) = ((χ f : ↥A) : L)) → P' = P) :=
    fun χ h1 h2 => exists_place_of_section A S ι hι t hfrac B hBA hSB hunitB hB h𝔮B htq he1 hprep χ h1
      (hcχ χ h2) (hker χ h1 h2)

  set D : Set (Place L F) := {P | P.IsRational ∧ (∀ f : ↥S, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
    (∀ f : ↥S, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0)} with hDdef
  have hDmem : ∀ P, P ∈ D ↔ (P.IsRational ∧ (∀ f : ↥S, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
    (∀ f : ↥S, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0)) := fun P => Iff.rfl

  have hplaceD : ∀ (χ : ↥S →+* ↥A) (P : Place L F), (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) →
      P.IsRational → (∀ f : F, f ∈ P.toValuationSubring ↔ ∃ g h : ↥S, χ h ≠ 0 ∧ f * (h : F) = (g : F)) →
      (∀ f : ↥S, P.evalAt (f : F) = ((χ f : ↥A) : L)) → P ∈ D := by
    intro χ P h2 hrat hPmem hev
    refine ⟨hrat, fun f => ⟨(hPmem f).mpr ⟨f, 1, by rw [map_one]; exact one_ne_zero, by simp⟩, ?_⟩, fun f => ?_⟩
    · rw [hev]; exact (χ f).2
    · rw [hev, ← h2 f, IsLocalRing.residue_eq_zero_iff]
      have : ((χ f : ↥A) : L) = ((⟨((χ f : ↥A) : L), (χ f).2⟩ : ↥A) : L) := rfl
      exact (ValuationSubring.valuation_lt_one_iff A (χ f)).symm
  refine ⟨D, hDmem, ?_, ?_, ?_, ?_⟩
  ·
    intro χ h1 h2
    obtain ⟨P, hrat, hPmem, hev, huniq⟩ := hplace χ h1 h2
    refine ⟨P, ⟨hplaceD χ P h2 hrat hPmem hev, hev⟩, ?_⟩
    rintro P' ⟨hP'D, hP'ev⟩
    exact huniq P' hP'D.1 (fun f => ⟨(hP'D.2.1 f).1, hP'ev f⟩)
  ·
    intro P hP f
    obtain ⟨hrat, hint, hval⟩ := hP
    let χP : ↥S →+* ↥A :=
      { toFun := fun g => ⟨P.evalAt (g : F), (hint g).2⟩
        map_one' := Subtype.ext (by simp [Place.evalAt_one])
        map_mul' := fun g₁ g₂ => Subtype.ext (by
          change P.evalAt ((g₁ * g₂ : ↥S) : F) = P.evalAt (g₁ : F) * P.evalAt (g₂ : F)
          rw [Subring.coe_mul, P.evalAt_mul_of_mem hrat (hint g₁).1 (hint g₂).1])
        map_zero' := Subtype.ext (by change P.evalAt ((0 : ↥S) : F) = 0; simp [evalAt_zero])
        map_add' := fun g₁ g₂ => Subtype.ext (by
          change P.evalAt ((g₁ + g₂ : ↥S) : F) = P.evalAt (g₁ : F) + P.evalAt (g₂ : F)
          rw [Subring.coe_add, evalAt_add P hrat (hint g₁).1 (hint g₂).1]) }
    have hχP : ∀ g : ↥S, ((χP g : ↥A) : L) = P.evalAt (g : F) := fun _ => rfl
    have h1 : ∀ a : ↥A, χP (ι a) = a := fun a => Subtype.ext (by rw [hχP, hι, Place.evalAt_algebraMap_eq])
    have h2 : ∀ g : ↥S, IsLocalRing.residue ↥A (χP g) = χ₀ g := by
      intro g
      obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective (χ₀ g)
      have h0 : χ₀ (g - ι a₀) = 0 := by rw [map_sub, hχ₀C, ha₀, sub_self]
      have hlt := (hval (g - ι a₀)).mpr h0
      have hmem : χP (g - ι a₀) ∈ maximalIdeal ↥A := by
        rw [ValuationSubring.valuation_lt_one_iff]; exact hlt
      rw [map_sub, h1, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hmem
      rw [hmem, ha₀]
    obtain ⟨P₁, hrat₁, hPmem₁, hev₁, huniq₁⟩ := hplace χP h1 h2
    have hPP₁ : P = P₁ := huniq₁ P hrat (fun g => ⟨(hint g).1, (hχP g).symm⟩)
    rw [hPP₁, hPmem₁]
    constructor
    · rintro ⟨g, h, hh, e⟩
      refine ⟨g, h, ?_, e⟩
      rw [← hPP₁] at *
      intro h0; apply hh; exact Subtype.ext h0
    · rintro ⟨g, h, hh, e⟩
      refine ⟨g, h, fun h0 => hh ?_, e⟩
      rw [hPP₁]  at *
      have := congrArg Subtype.val h0
      rw [hev₁ h] at *
      exact this
  ·
    intro f hf0 hordf

    have hordS : ∀ P ∈ D, ∀ u : (↥S)ˣ, P.ord (((u : ↥S) : F)) = 0 := by
      intro P hP u
      have hu : IsUnit (⟨((u : ↥S) : F), (hP.2.1 _).1⟩ : ↥P.toValuationSubring) := by
        rw [isUnit_iff_inv_mem P.toValuationSubring.toSubring]
        refine ⟨fun h0 => ?_, ?_⟩
        · have : (u : ↥S) = 0 := Subtype.ext h0
          exact u.ne_zero this
        · have e : (((u : ↥S) : F))⁻¹ = (((u⁻¹ : (↥S)ˣ) : ↥S) : F) := by
            symm; apply eq_inv_of_mul_eq_one_right
            exact congrArg Subtype.val u.mul_inv
          rw [e]; exact (hP.2.1 _).1
      exact ord_eq_zero_of_isUnit P _ hu
    have hordc : ∀ (P : Place L F) (c : L), c ≠ 0 → P.ord (algebraMap L F c) = 0 := by
      intro P c hc
      have hu : IsUnit (⟨algebraMap L F c, P.algebraMap_mem' c⟩ : ↥P.toValuationSubring) := by
        rw [isUnit_iff_inv_mem P.toValuationSubring.toSubring]
        exact ⟨(map_ne_zero _).mpr hc, by rw [← map_inv₀]; exact P.algebraMap_mem' _⟩
      exact ord_eq_zero_of_isUnit P _ hu
    have hfac0 : ∀ r : ↥A, r ∈ maximalIdeal ↥A → ((t - ι r : ↥S) : F) ≠ 0 := by
      intro r hr
      refine (hunitB _ (fun h => htq ?_)).1
      have : t = (t - ι r) + ι r := by ring
      rw [this]; exact Ideal.add_mem _ h (Ideal.mem_map_of_mem _ hr)
    have hprod0 : ∀ (n : ℕ) (r : Fin n → ↥A), (∀ i, r i ∈ maximalIdeal ↥A) →
        ((∏ i, (t - ι (r i)) : ↥S) : F) ≠ 0 := by
      intro n r hr
      rw [SubmonoidClass.coe_finset_prod]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => hfac0 (r i) (hr i))

    have hordprod : ∀ (P : Place L F) (n : ℕ) (r : Fin n → ↥A), (∀ i, r i ∈ maximalIdeal ↥A) →
        (∀ i, P.ord ((t - ι (r i) : ↥S) : F) = 0) → P.ord ((∏ i, (t - ι (r i)) : ↥S) : F) = 0 := by
      intro P n
      induction n with
      | zero => intro r _ _; simp
      | succ n ih =>
        intro r hr h0
        rw [Fin.prod_univ_succ, Subring.coe_mul, P.ord_mul (hfac0 _ (hr 0)) (hprod0 n _ (fun i => hr i.succ)),
          h0 0, ih (fun i => r i.succ) (fun i => hr i.succ) (fun i => h0 i.succ), add_zero]

    have key2 : ∀ (n₁ : ℕ) (r₁ : Fin n₁ → ↥A), (∀ i, r₁ i ∈ maximalIdeal ↥A) →
        ∀ (n₂ : ℕ) (r₂ : Fin n₂ → ↥A), (∀ j, r₂ j ∈ maximalIdeal ↥A) →
        (∀ P ∈ D, P.ord (((∏ i, (t - ι (r₁ i)) : ↥S) : F) / ((∏ j, (t - ι (r₂ j)) : ↥S) : F)) = 0) →
        ((∏ i, (t - ι (r₁ i)) : ↥S) : F) = ((∏ j, (t - ι (r₂ j)) : ↥S) : F) := by
      intro n₁
      induction n₁ with
      | zero =>
        intro r₁ _ n₂ r₂ hr₂ hord
        cases n₂ with
        | zero => simp
        | succ k =>
          exfalso
          obtain ⟨χ, ⟨h1, h2, h3⟩, -⟩ := hhensel (r₂ 0) ((IsLocalRing.residue_eq_zero_iff _).mpr (hr₂ 0))
          obtain ⟨P, hrat, hPmem, hev, -⟩ := hplace χ h1 h2
          have hPD := hplaceD χ P h2 hrat hPmem hev
          have hden := hprod0 (k + 1) r₂ hr₂
          have h0 := hord P hPD
          simp only [Finset.univ_eq_empty, Finset.prod_empty, OneMemClass.coe_one, one_div, P.ord_inv] at h0

          have hpos : 0 < P.ord ((∏ j, (t - ι (r₂ j)) : ↥S) : F) := by
            rw [Fin.prod_univ_succ, Subring.coe_mul, P.ord_mul (hfac0 _ (hr₂ 0)) (hprod0 k _ (fun i => hr₂ i.succ))]
            have h1' : 0 < P.ord ((t - ι (r₂ 0) : ↥S) : F) := by
              rw [ord_pos_iff_evalAt_eq_zero P hrat (hPD.2.1 _).1 (hfac0 _ (hr₂ 0)), hev, map_sub, h1, h3, sub_self]
              rfl
            have h2' := ord_nonneg_of_mem P (hPD.2.1 (∏ i : Fin k, (t - ι (r₂ i.succ)))).1
            omega
          omega
      | succ k ih =>
        intro r₁ hr₁ n₂ r₂ hr₂ hord
        obtain ⟨χ, ⟨h1, h2, h3⟩, -⟩ := hhensel (r₁ 0) ((IsLocalRing.residue_eq_zero_iff _).mpr (hr₁ 0))
        obtain ⟨P, hrat, hPmem, hev, -⟩ := hplace χ h1 h2
        have hPD := hplaceD χ P h2 hrat hPmem hev
        have hnum0 := hprod0 (k + 1) r₁ hr₁
        have hden0 := hprod0 n₂ r₂ hr₂
        have h0 := hord P hPD
        rw [div_eq_mul_inv, P.ord_mul hnum0 (inv_ne_zero hden0), P.ord_inv] at h0

        have hposnum : 0 < P.ord ((∏ i, (t - ι (r₁ i)) : ↥S) : F) := by
          rw [Fin.prod_univ_succ, Subring.coe_mul, P.ord_mul (hfac0 _ (hr₁ 0)) (hprod0 k _ (fun i => hr₁ i.succ))]
          have h1' : 0 < P.ord ((t - ι (r₁ 0) : ↥S) : F) := by
            rw [ord_pos_iff_evalAt_eq_zero P hrat (hPD.2.1 _).1 (hfac0 _ (hr₁ 0)), hev, map_sub, h1, h3, sub_self]
            rfl
          have h2' := ord_nonneg_of_mem P (hPD.2.1 (∏ i : Fin k, (t - ι (r₁ i.succ)))).1
          omega

        have hex : ∃ j, P.ord ((t - ι (r₂ j) : ↥S) : F) ≠ 0 := by
          by_contra hall
          push Not at hall
          have := hordprod P n₂ r₂ hr₂ hall
          omega
        obtain ⟨j, hj⟩ := hex
        have hj' : r₂ j = r₁ 0 := by
          have hpos : 0 < P.ord ((t - ι (r₂ j) : ↥S) : F) := by
            have := ord_nonneg_of_mem P (hPD.2.1 (t - ι (r₂ j))).1
            omega
          rw [ord_pos_iff_evalAt_eq_zero P hrat (hPD.2.1 _).1 (hfac0 _ (hr₂ j)), hev, map_sub, h1, h3] at hpos
          have : r₁ 0 - r₂ j = 0 := Subtype.ext hpos
          exact (sub_eq_zero.mp this).symm

        cases n₂ with
        | zero => exact j.elim0
        | succ m =>
          have eden : (∏ i, (t - ι (r₂ i)) : ↥S) = (t - ι (r₂ j)) * ∏ i : Fin m, (t - ι (r₂ (j.succAbove i))) :=
            Fin.prod_univ_succAbove _ j
          have enum : (∏ i, (t - ι (r₁ i)) : ↥S) = (t - ι (r₁ 0)) * ∏ i : Fin k, (t - ι (r₁ i.succ)) :=
            Fin.prod_univ_succ _
          have hQ : ((∏ i : Fin k, (t - ι (r₁ i.succ)) : ↥S) : F) =
              ((∏ i : Fin m, (t - ι (r₂ (j.succAbove i))) : ↥S) : F) := by
            apply ih (fun i => r₁ i.succ) (fun i => hr₁ i.succ) m (fun i => r₂ (j.succAbove i))
              (fun i => hr₂ (j.succAbove i))
            intro P' hP'
            have := hord P' hP'
            rw [enum, eden, hj', Subring.coe_mul, Subring.coe_mul, mul_div_mul_left _ _ (hfac0 _ (hr₁ 0))] at this
            exact this
          rw [enum, eden, hj', Subring.coe_mul, Subring.coe_mul, hQ]

    obtain ⟨c, hc0, hcf, hcfi⟩ := he1 f hf0
    obtain ⟨g₁, h₁, hh₁, e₁⟩ := hB _ hcf
    have hh₁0 : (h₁ : F) ≠ 0 := (hunitB h₁ hh₁).1
    have hcf0 : algebraMap L F c * f ≠ 0 := mul_ne_zero ((map_ne_zero _).mpr hc0) hf0
    have hg₁0 : (g₁ : F) ≠ 0 := by rw [← e₁]; exact mul_ne_zero hcf0 hh₁0
    have hg₁ : g₁ ∉ 𝔮 := by
      intro hg
      rcases h𝔮B g₁ hg with h | h
      · apply h
        have e : ((g₁ : F))⁻¹ = ((h₁ : F))⁻¹ * (algebraMap L F c * f)⁻¹ := by rw [← e₁, mul_inv, mul_comm]
        rw [e]; exact mul_mem (hunitB h₁ hh₁).2 hcfi
      · exact hg₁0 h
    obtain ⟨n₁, u₁, r₁, hr₁, eg₁⟩ := hprep g₁ hg₁
    obtain ⟨n₂, u₂, r₂, hr₂, eh₁⟩ := hprep h₁ hh₁
    have hu₁0 : ((u₁ : ↥S) : F) ≠ 0 := fun h0 => u₁.ne_zero (Subtype.ext h0)
    have hu₂0 : ((u₂ : ↥S) : F) ≠ 0 := fun h0 => u₂.ne_zero (Subtype.ext h0)
    set N₁ : ↥S := ∏ i, (t - ι (r₁ i)) with hN₁
    set N₂ : ↥S := ∏ i, (t - ι (r₂ i)) with hN₂
    have hN₁0 : (N₁ : F) ≠ 0 := hprod0 n₁ r₁ hr₁
    have hN₂0 : (N₂ : F) ≠ 0 := hprod0 n₂ r₂ hr₂

    have hquot : (N₁ : F) / (N₂ : F) = (algebraMap L F c * f) * ((u₂ : ↥S) : F) / ((u₁ : ↥S) : F) := by
      have e2 : algebraMap L F c * f = ((u₁ : ↥S) : F) * (N₁ : F) / (((u₂ : ↥S) : F) * (N₂ : F)) := by
        rw [eq_div_iff (mul_ne_zero hu₂0 hN₂0)]
        have : (h₁ : F) = ((u₂ : ↥S) : F) * (N₂ : F) := by rw [eh₁, Subring.coe_mul]
        rw [← this, e₁, eg₁, Subring.coe_mul]
      rw [e2]; field_simp
    have hordq : ∀ P ∈ D, P.ord ((N₁ : F) / (N₂ : F)) = 0 := by
      intro P hP
      rw [hquot, div_eq_mul_inv, P.ord_mul (mul_ne_zero hcf0 hu₂0) (inv_ne_zero hu₁0), P.ord_inv,
        P.ord_mul hcf0 hu₂0, P.ord_mul ((map_ne_zero _).mpr hc0) hf0, hordc P c hc0, hordf P hP,
        hordS P hP u₂, hordS P hP u₁]
      simp
    have hNN : (N₁ : F) = (N₂ : F) := key2 n₁ r₁ hr₁ n₂ r₂ hr₂ hordq
    refine ⟨c, u₁ * u₂⁻¹, hc0, ?_⟩
    have e3 : (N₁ : F) / (N₂ : F) = 1 := by rw [hNN, div_self hN₂0]
    rw [e3, eq_div_iff hu₁0, one_mul] at hquot
    have e4 : (((u₁ * u₂⁻¹ : (↥S)ˣ) : ↥S) : F) = ((u₁ : ↥S) : F) * (((u₂ : ↥S) : F))⁻¹ := by
      rw [Units.val_mul, Subring.coe_mul]
      congr 1
      exact (eq_inv_of_mul_eq_one_right (congrArg Subtype.val u₂.mul_inv)).symm.symm
    rw [e4, hquot, mul_assoc, mul_inv_cancel₀ hu₂0, mul_one]
  ·
    intro f hfB hfD
    have hfac0 : ∀ r : ↥A, r ∈ maximalIdeal ↥A → ((t - ι r : ↥S) : F) ≠ 0 := by
      intro r hr
      refine (hunitB _ (fun h => htq ?_)).1
      have : t = (t - ι r) + ι r := by ring
      rw [this]; exact Ideal.add_mem _ h (Ideal.mem_map_of_mem _ hr)
    have key : ∀ (n : ℕ) (r : Fin n → ↥A), (∀ i, r i ∈ maximalIdeal ↥A) → ∀ (g : ↥S) (f : F),
        (∀ P ∈ D, f ∈ P.toValuationSubring) → f * ((∏ i, (t - ι (r i)) : ↥S) : F) = (g : F) → f ∈ S := by
      intro n
      induction n with
      | zero =>
        intro r _ g f _ e
        simp only [Finset.univ_eq_empty, Finset.prod_empty, OneMemClass.coe_one, mul_one] at e
        rw [e]; exact g.2
      | succ n ih =>
        intro r hr g f hfD e
        obtain ⟨χ, ⟨h1, h2, h3⟩, -⟩ := hhensel (r 0) ((IsLocalRing.residue_eq_zero_iff _).mpr (hr 0))
        obtain ⟨P, hrat, hPmem, hev, -⟩ := hplace χ h1 h2
        have hPD := hplaceD χ P h2 hrat hPmem hev
        obtain ⟨g', h', hh', e'⟩ := (hPmem f).mp (hfD P hPD)
        set Q : ↥S := ∏ i : Fin n, (t - ι (r i.succ)) with hQ
        have eprod : (∏ i, (t - ι (r i)) : ↥S) = (t - ι (r 0)) * Q := Fin.prod_univ_succ _
        have hχt0 : χ (t - ι (r 0)) = 0 := by rw [map_sub, h1, h3, sub_self]
        have eg : (g : F) * (h' : F) = (g' : F) * (((t - ι (r 0)) * Q : ↥S) : F) := by
          rw [← e, ← e', eprod]; ring
        have eg' : g * h' = g' * ((t - ι (r 0)) * Q) := Subtype.ext (by
          change (g : F) * (h' : F) = (g' : F) * (((t - ι (r 0)) * Q : ↥S) : F)
          exact eg)
        have hχg : χ g = 0 := by
          have := congrArg χ eg'
          rw [map_mul, map_mul, map_mul, hχt0, zero_mul, mul_zero] at this
          exact (mul_eq_zero.mp this).resolve_right hh'
        have hgker : g ∈ Ideal.span {t - ι (χ t)} := by rw [← hker χ h1 h2]; exact hχg
        rw [h3] at hgker
        obtain ⟨g₁, hg₁⟩ := Ideal.mem_span_singleton'.mp hgker
        have hne : ((t - ι (r 0) : ↥S) : F) ≠ 0 := hfac0 (r 0) (hr 0)
        apply ih (fun i => r i.succ) (fun i => hr i.succ) g₁ f hfD
        apply mul_left_cancel₀ hne
        calc ((t - ι (r 0) : ↥S) : F) * (f * (Q : F)) = f * (((t - ι (r 0)) * Q : ↥S) : F) := by
              rw [Subring.coe_mul]; ring
          _ = (g : F) := by rw [← eprod, e]
          _ = ((t - ι (r 0) : ↥S) : F) * (g₁ : F) := by rw [← hg₁, Subring.coe_mul, mul_comm]
    obtain ⟨g, h, hh, e⟩ := hB f hfB
    obtain ⟨n, u, r, hr, eh⟩ := hprep h hh
    have hfu : f * ((u : ↥S) : F) ∈ S := by
      apply key n r hr g (f * ((u : ↥S) : F)) (fun P hP => mul_mem (hfD P hP) (hP.2.1 _).1)
      rw [mul_assoc, ← Subring.coe_mul, ← eh, e]
    have e2 : f = (f * ((u : ↥S) : F)) * (((u⁻¹ : (↥S)ˣ) : ↥S) : F) := by
      rw [mul_assoc, ← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one, mul_one]
    rw [e2]
    exact mul_mem hfu (SetLike.coe_mem _)

end S_AlgebraicCurve_exists_disc_sections_locality_of_henselSections_of_weierstrassPreparation
end P2MW
export P2MW.S_AlgebraicCurve_exists_disc_sections_locality_of_henselSections_of_weierstrassPreparation (solution)
