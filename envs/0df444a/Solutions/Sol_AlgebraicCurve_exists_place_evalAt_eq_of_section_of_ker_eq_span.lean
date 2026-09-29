-- Prove2me | solution 1 for AlgebraicCurve.exists_place_evalAt_eq_of_section_of_ker_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/69a42590-3b68-5109-8200-b432eacaec27

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_place_evalAt_eq_of_section_of_ker_eq_span

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

set_option maxHeartbeats 6400000 in
theorem solution
    {L F : Type} [Field L] [Field F] [Algebra L F] (A : ValuationSubring L)
    (S : Subring F) [IsLocalRing ↥S]
    (hAS : ∀ a : ↥A, algebraMap L F (a : L) ∈ S)
    (hfrac : ∀ f : F, ∃ a b : ↥S, (b : F) ≠ 0 ∧ f * (b : F) = (a : F))
    (T : ↥S) (c : ↥A) (hTc : (T : F) ≠ algebraMap L F (c : L))
    (χ : ↥S →+* ↥A) (hχa : ∀ a : ↥A, χ ⟨algebraMap L F (a : L), hAS a⟩ = a) (hχT : χ T = c)
    (hker : RingHom.ker χ = Ideal.span {T - ⟨algebraMap L F (c : L), hAS c⟩})
    (hnoeth : ∀ O : Subring F, (∀ f : F, f ∈ O ↔ ∃ a b : ↥S, b ∉ RingHom.ker χ ∧ f * (b : F) = (a : F)) →
      IsNoetherianRing ↥O) :
    ∃ P : Place L F,
      (∀ f : F, f ∈ P.toValuationSubring ↔ ∃ a b : ↥S, b ∉ RingHom.ker χ ∧ f * (b : F) = (a : F)) ∧
      (∀ g : ↥S, P.evalAt (g : F) = ((χ g : ↥A) : L)) ∧
      (∀ g : F, g ∈ S → g ∈ P.toValuationSubring ∧ ∃ h : P.evalAt g ∈ A,
        (IsUnit (⟨P.evalAt g, h⟩ : ↥A) ↔ ∃ g' ∈ S, g * g' = 1)) ∧
      P.evalAt (T : F) = (c : L) ∧
      (∀ s : F, s ∈ S → P.evalAt s = 0 →
        ∃ s' : F, s' ∈ S ∧ s = ((T : F) - algebraMap L F (c : L)) * s') := by
  classical
  set 𝔭 : Ideal ↥S := RingHom.ker χ with h𝔭
  set κc : ↥S := ⟨algebraMap L F (c : L), hAS c⟩ with hκc
  set π : ↥S := T - κc with hπdef
  have hχκ : ∀ a : ↥A, χ ⟨algebraMap L F (a : L), hAS a⟩ = a := hχa
  have hχπ : χ π = 0 := by rw [hπdef, map_sub, hχT, hκc, hχκ, sub_self]
  have hπ𝔭 : π ∈ 𝔭 := by rw [h𝔭, RingHom.mem_ker]; exact hχπ
  have hπF : (π : F) = (T : F) - algebraMap L F (c : L) := by
    first
      | rfl
      | (simp only [hπdef, hκc]; push_cast; rfl)
  have hπ0 : (π : F) ≠ 0 := by
    intro h0; apply hTc
    rw [hπF] at h0
    exact sub_eq_zero.mp h0
  have h𝔭prime : 𝔭.IsPrime := by rw [h𝔭]; exact RingHom.ker_isPrime χ
  have hmem𝔭 : ∀ s : ↥S, s ∈ 𝔭 ↔ χ s = 0 := fun s => by rw [h𝔭, RingHom.mem_ker]
  have h1𝔭 : (1 : ↥S) ∉ 𝔭 := by rw [hmem𝔭, map_one]; exact one_ne_zero

  let PO : F → Prop := fun f => ∃ a b : ↥S, b ∉ 𝔭 ∧ f * (b : F) = (a : F)
  have hb0 : ∀ b : ↥S, b ∉ 𝔭 → (b : F) ≠ 0 := by
    intro b hb h0; apply hb; rw [show b = 0 from Subtype.ext h0]; exact 𝔭.zero_mem
  let O : Subring F :=
    { carrier := {f | PO f}
      mul_mem' := by
        rintro f g ⟨a, b, hb, hfb⟩ ⟨a', b', hb', hgb⟩
        refine ⟨a * a', b * b', fun h => (h𝔭prime.mem_or_mem h).elim hb hb', ?_⟩
        push_cast; rw [← hfb, ← hgb]; ring
      one_mem' := ⟨1, 1, h1𝔭, by push_cast; ring⟩
      add_mem' := by
        rintro f g ⟨a, b, hb, hfb⟩ ⟨a', b', hb', hgb⟩
        refine ⟨a * b' + a' * b, b * b', fun h => (h𝔭prime.mem_or_mem h).elim hb hb', ?_⟩
        push_cast; rw [← hfb, ← hgb]; ring
      zero_mem' := ⟨0, 1, h1𝔭, by push_cast; ring⟩
      neg_mem' := by
        rintro f ⟨a, b, hb, hfb⟩
        exact ⟨-a, b, hb, by push_cast; rw [← hfb]; ring⟩ }
  have hO : ∀ f : F, f ∈ O ↔ ∃ a b : ↥S, b ∉ 𝔭 ∧ f * (b : F) = (a : F) := fun f => Iff.rfl
  have hSO : ∀ s : ↥S, (s : F) ∈ O := fun s => ⟨s, 1, h1𝔭, by push_cast; ring⟩
  haveI hOnoeth : IsNoetherianRing ↥O := hnoeth O (fun f => by rw [hO, h𝔭])

  have hunitO : ∀ (a b : ↥S), a ∉ 𝔭 → b ∉ 𝔭 → ∀ (hf : (a : F) / (b : F) ∈ O), IsUnit (⟨(a : F) / (b : F), hf⟩ : ↥O) := by
    intro a b ha hb hf
    have hg : (b : F) / (a : F) ∈ O := ⟨b, a, ha, by rw [div_mul_cancel₀ _ (hb0 a ha)]⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hg⟩, Subtype.ext ?_⟩
    show (a : F) / (b : F) * ((b : F) / (a : F)) = 1
    rw [div_mul_div_comm, mul_comm (b : F), div_self (mul_ne_zero (hb0 a ha) (hb0 b hb))]
  have hrepr : ∀ f : ↥O, ∃ a b : ↥S, b ∉ 𝔭 ∧ (f : F) = (a : F) / (b : F) := by
    intro f
    obtain ⟨a, b, hb, hfb⟩ := (hO _).mp f.2
    exact ⟨a, b, hb, by rw [eq_div_iff (hb0 b hb)]; exact hfb⟩
  have hnonunit : ∀ (f : ↥O) (a b : ↥S), b ∉ 𝔭 → (f : F) = (a : F) / (b : F) → ¬ IsUnit f → a ∈ 𝔭 := by
    intro f a b hb hf hnu
    by_contra ha
    exact hnu (by have := hunitO a b ha hb (by rw [← hf]; exact f.2); rwa [show (⟨(a : F) / (b : F), _⟩ : ↥O) = f from Subtype.ext hf.symm] at this)
  have hunit_mem : ∀ (f : ↥O) (a b : ↥S), b ∉ 𝔭 → (f : F) = (a : F) / (b : F) → IsUnit f → a ∉ 𝔭 := by
    intro f a b hb hf hu ha

    obtain ⟨g, hg⟩ := isUnit_iff_exists_inv.mp hu
    obtain ⟨a', b', hb', hg'⟩ := hrepr g
    have e1 : (a : F) * (a' : F) = (b : F) * (b' : F) := by
      have : (f : F) * (g : F) = 1 := by
        have := congrArg Subtype.val hg; push_cast at this; exact this
      rw [hf, hg', div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (hb0 b hb) (hb0 b' hb'))] at this
      exact this
    have e2 : a * a' = b * b' := Subtype.ext (by push_cast; exact e1)
    have : b * b' ∈ 𝔭 := by rw [← e2]; exact 𝔭.mul_mem_right _ ha
    exact (h𝔭prime.mem_or_mem this).elim hb hb'

  haveI hOlocal : IsLocalRing ↥O := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f => ?_
    obtain ⟨a, b, hb, hf⟩ := hrepr f
    by_cases ha : a ∈ 𝔭
    · right
      have h1f : ((1 - f : ↥O) : F) = ((b - a : ↥S) : F) / (b : F) := by
        push_cast; rw [hf, sub_div, div_self (hb0 b hb)]
      have hba : b - a ∉ 𝔭 := fun h => hb (by simpa using 𝔭.add_mem h ha)
      have := hunitO (b - a) b hba hb (by rw [← h1f]; exact (1 - f).2)
      rwa [show (⟨((b - a : ↥S) : F) / (b : F), _⟩ : ↥O) = 1 - f from Subtype.ext h1f.symm] at this
    · left
      have := hunitO a b ha hb (by rw [← hf]; exact f.2)
      rwa [show (⟨(a : F) / (b : F), _⟩ : ↥O) = f from Subtype.ext hf.symm] at this

  let πO : ↥O := ⟨(π : F), hSO π⟩
  have hπOnu : ¬ IsUnit πO := by
    intro hu
    exact hunit_mem πO π 1 h1𝔭 (by show (π : F) = (π : F) / ((1 : ↥S) : F); push_cast; simp) hu hπ𝔭
  have hmaxO : maximalIdeal ↥O = Ideal.span {πO} := by
    apply le_antisymm
    · intro f hf
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hf
      obtain ⟨a, b, hb, hfab⟩ := hrepr f
      have ha : a ∈ 𝔭 := hnonunit f a b hb hfab hf
      rw [hker, Ideal.mem_span_singleton] at ha
      obtain ⟨s, hs⟩ := ha
      rw [Ideal.mem_span_singleton]
      refine ⟨⟨(s : F) / (b : F), ⟨s, b, hb, by rw [div_mul_cancel₀ _ (hb0 b hb)]⟩⟩, Subtype.ext ?_⟩
      show (f : F) = (π : F) * ((s : F) / (b : F))
      rw [hfab, hs]; push_cast; rw [hπdef, hκc]; push_cast; ring
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hπOnu
  have hnotfield : ¬ IsField ↥O := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    intro h
    have : πO ∈ maximalIdeal ↥O := (IsLocalRing.mem_maximalIdeal _).mpr hπOnu
    rw [h] at this
    exact hπ0 (congrArg Subtype.val ((Submodule.mem_bot _).mp this))
  have hprinc : (maximalIdeal ↥O).IsPrincipal := ⟨⟨πO, by rw [hmaxO, Ideal.submodule_span_eq]⟩⟩
  haveI hOdvr : IsDiscreteValuationRing ↥O := ((IsDiscreteValuationRing.TFAE ↥O hnotfield).out 4 0).mp hprinc

  have hval : ∀ x : F, x ∈ O ∨ x⁻¹ ∈ O := by
    intro x
    obtain ⟨a, b, hb0', hab⟩ := hfrac x
    have haO : (a : F) ∈ O := hSO a
    have hbO : (b : F) ∈ O := hSO b
    rcases ValuationRing.dvd_total (⟨(a : F), haO⟩ : ↥O) ⟨(b : F), hbO⟩ with ⟨q, hq⟩ | ⟨q, hq⟩
    ·
      right
      have hq' : (b : F) = (a : F) * (q : F) := congrArg Subtype.val hq
      have ha0 : (a : F) ≠ 0 := by intro h; rw [h, zero_mul] at hq'; exact hb0' hq'
      have hx : x = (a : F) / (b : F) := by rw [eq_div_iff hb0']; exact hab
      have : x⁻¹ = (q : F) := by
        rw [hx, inv_div, hq', mul_div_cancel_left₀ _ ha0]
      rw [this]; exact q.2
    · left
      have hq' : (a : F) = (b : F) * (q : F) := congrArg Subtype.val hq
      have : x = (q : F) := by
        have := hab; rw [hq'] at this
        exact mul_right_cancel₀ hb0' (by rw [this]; ring)
      rw [this]; exact q.2
  let OV : ValuationSubring F := { O with mem_or_inv_mem' := hval }
  have hOV : ∀ f : F, f ∈ OV ↔ f ∈ O := fun f => Iff.rfl
  have hconstO : ∀ x : L, algebraMap L F x ∈ OV := by
    intro x
    rcases A.mem_or_inv_mem x with hx | hx
    · exact hSO ⟨_, hAS ⟨x, hx⟩⟩
    · rcases eq_or_ne x 0 with rfl | hx0
      · rw [map_zero]; exact OV.zero_mem
      refine ⟨1, ⟨algebraMap L F (((⟨x⁻¹, hx⟩ : ↥A)) : L), hAS ⟨x⁻¹, hx⟩⟩, ?_, ?_⟩
      · rw [hmem𝔭, hχκ ⟨x⁻¹, hx⟩]; exact fun h => inv_ne_zero hx0 (congrArg Subtype.val h)
      · show algebraMap L F x * algebraMap L F x⁻¹ = ((1 : ↥S) : F)
        rw [← map_mul, mul_inv_cancel₀ hx0, map_one]; rfl
  have hOVtop : OV ≠ ⊤ := by
    intro h
    have : (π : F)⁻¹ ∈ OV := h.symm ▸ ValuationSubring.mem_top _
    apply hπOnu
    refine isUnit_iff_exists_inv.mpr ⟨⟨(π : F)⁻¹, this⟩, Subtype.ext ?_⟩
    show (π : F) * (π : F)⁻¹ = 1
    exact mul_inv_cancel₀ hπ0

  have hOVpir : IsPrincipalIdealRing ↥OV := (inferInstance : IsPrincipalIdealRing ↥O)
  let P : Place L F := ⟨OV, hconstO, hOVtop, hOVpir⟩

  have hevalχ : ∀ g : ↥S, P.evalAt (g : F) = ((χ g : ↥A) : L) := by
    intro g
    have hgO : (g : F) ∈ P.toValuationSubring := hSO g
    have hcO : algebraMap L F ((χ g : ↥A) : L) ∈ P.toValuationSubring := P.algebraMap_mem' _

    have hdiff : (⟨(g : F), hgO⟩ - ⟨algebraMap L F ((χ g : ↥A) : L), hcO⟩ : ↥P.toValuationSubring) ∈
        maximalIdeal ↥P.toValuationSubring := by
      have hk : g - ⟨algebraMap L F ((χ g : ↥A) : L), hAS (χ g)⟩ ∈ 𝔭 := by
        rw [hmem𝔭, map_sub, hχκ, sub_self]
      rw [hker, Ideal.mem_span_singleton] at hk
      obtain ⟨s, hs⟩ := hk
      show (⟨(g : F), hgO⟩ - ⟨algebraMap L F ((χ g : ↥A) : L), hcO⟩ : ↥O) ∈ maximalIdeal ↥O
      rw [hmaxO, Ideal.mem_span_singleton]
      refine ⟨⟨(s : F), hSO s⟩, Subtype.ext ?_⟩
      show (g : F) - algebraMap L F ((χ g : ↥A) : L) = (π : F) * (s : F)
      have := congrArg Subtype.val hs
      push_cast at this ⊢
      rw [← this]
    rw [P.evalAt_of_mem hgO]
    have e1 : IsLocalRing.residue ↥P.toValuationSubring ⟨(g : F), hgO⟩ =
        IsLocalRing.residue ↥P.toValuationSubring ⟨algebraMap L F ((χ g : ↥A) : L), hcO⟩ := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hdiff
    rw [e1, ← P.evalAt_of_mem hcO]
    exact AlgebraicCurve.Place.evalAt_algebraMap P _

  have hunitχ : ∀ g : ↥S, IsUnit (χ g) ↔ IsUnit g := by
    intro g
    constructor
    · intro hu
      by_contra hg

      have hJ : (maximalIdeal ↥A).comap χ = maximalIdeal ↥S := by
        have hmax' : ((maximalIdeal ↥A).comap χ).IsMaximal := by
          refine Ideal.comap_isMaximal_of_surjective χ (fun a => ⟨⟨algebraMap L F (a : L), hAS a⟩, hχκ a⟩)
        exact IsLocalRing.eq_maximalIdeal hmax'
      have : g ∈ (maximalIdeal ↥A).comap χ := by rw [hJ]; exact (IsLocalRing.mem_maximalIdeal _).mpr hg
      exact (IsLocalRing.mem_maximalIdeal _).mp this hu
    · intro hu; exact hu.map χ
  refine ⟨P, fun f => by rw [hOV f, hO, h𝔭], hevalχ, ?_, ?_, ?_⟩
  · intro g hg
    refine ⟨hSO ⟨g, hg⟩, ?_⟩
    have hev : P.evalAt g = ((χ ⟨g, hg⟩ : ↥A) : L) := hevalχ ⟨g, hg⟩
    refine ⟨by rw [hev]; exact (χ ⟨g, hg⟩).2, ?_⟩
    have : (⟨P.evalAt g, by rw [hev]; exact (χ ⟨g, hg⟩).2⟩ : ↥A) = χ ⟨g, hg⟩ := Subtype.ext hev
    rw [this, hunitχ]
    constructor
    · intro hu
      obtain ⟨u, hu'⟩ := hu
      refine ⟨((u⁻¹ : (↥S)ˣ) : ↥S), ((u⁻¹ : (↥S)ˣ) : ↥S).2, ?_⟩
      have := congrArg Subtype.val u.mul_inv
      rw [hu'] at this; exact this
    · rintro ⟨g', hg', hgg'⟩
      exact isUnit_iff_exists_inv.mpr ⟨⟨g', hg'⟩, Subtype.ext hgg'⟩
  · rw [hevalχ, hχT]
  · intro s hs h0
    have h1 : χ ⟨s, hs⟩ = 0 := by
      have := hevalχ ⟨s, hs⟩
      rw [h0] at this
      exact Subtype.ext (by simpa using this.symm)
    have h2 : (⟨s, hs⟩ : ↥S) ∈ 𝔭 := (hmem𝔭 _).mpr h1
    rw [hker, Ideal.mem_span_singleton] at h2
    obtain ⟨s', hs'⟩ := h2
    refine ⟨(s' : F), s'.2, ?_⟩
    have := congrArg Subtype.val hs'
    push_cast at this
    rw [hπF] at this
    exact this

end S_AlgebraicCurve_exists_place_evalAt_eq_of_section_of_ker_eq_span
end P2MW
export P2MW.S_AlgebraicCurve_exists_place_evalAt_eq_of_section_of_ker_eq_span (solution)
