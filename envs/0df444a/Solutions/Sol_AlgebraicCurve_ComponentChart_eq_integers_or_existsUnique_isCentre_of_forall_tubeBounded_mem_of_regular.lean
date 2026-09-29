-- Prove2me | solution 1 for AlgebraicCurve.ComponentChart.eq_integers_or_existsUnique_isCentre_of_forall_tubeBounded_mem_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5a8176e0-02b7-56e5-8c53-0f2e9c3cbc8c

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_AlgebraicCurve_AffinoidCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ComponentChart_eq_integers_or_existsUnique_isCentre_of_forall_tubeBounded_mem_of_regular

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped Pointwise

theorem solution {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (N : Finset (Place (ResidueField A) Fbar))
    (hC : C.HasAffinoidLifting N) (hdict : ComponentChart.HasPlaceDictionary (A := A) N)
    (hreg : ∀ (f : F) (hf : f ∈ C.integers), C.tubeBounded f →
      ∀ Q : Place (ResidueField A) Fbar, Q ∉ N → C.residue ⟨f, hf⟩ ∈ Q.toValuationSubring)
    (hdim : ∀ 𝔭 : Ideal (ComponentChart.regOff (A := A) N), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭.IsMaximal)
    (hN : N.Nonempty) (hrat : ∀ P ∈ C.dom, P.IsRational)
    (O : ValuationSubring F) (hO : ∀ x : L, algebraMap L F x ∈ O ↔ x ∈ A)
    (hRO : ∀ f : F, C.tubeBounded f → f ∈ O) :
    O = C.integers ∨ ∃! Q : Place (ResidueField A) Fbar, C.IsCentre N O Q := by
  classical
  obtain ⟨hRint, hlift, hloc⟩ := hC
  obtain ⟨hdict1, hdict2⟩ := hdict

  have hnu : ∀ (O' : ValuationSubring F) (g : F), g ∈ O'.nonunits ↔ g = 0 ∨ g⁻¹ ∉ O' := by
    intro O' g
    rw [ValuationSubring.mem_nonunits_iff]
    rcases eq_or_ne g 0 with rfl | hg
    · simp
    · rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le,
        one_lt_inv₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hg))]
      simp [hg]
  have hmax : ∀ g : F, (∃ h : g ∈ O, (⟨g, h⟩ : O) ∈ maximalIdeal O) ↔ g ∈ O.nonunits := fun g =>
    ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.symm
  have hN_add : ∀ f₁ f₂ : F, f₁ ∈ O.nonunits → f₂ ∈ O.nonunits → f₁ + f₂ ∈ O.nonunits := by
    intro f₁ f₂ h₁ h₂
    obtain ⟨h₁', hm₁⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h₁
    obtain ⟨h₂', hm₂⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h₂
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨O.add_mem _ _ h₁' h₂', Ideal.add_mem _ hm₁ hm₂⟩
  have hN_mul : ∀ f₁ f₂ : F, f₁ ∈ O → f₂ ∈ O.nonunits → f₁ * f₂ ∈ O.nonunits := by
    intro f₁ f₂ h₁ h₂
    obtain ⟨h₂', hm₂⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h₂
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
      ⟨O.mul_mem _ _ h₁ h₂', Ideal.mul_mem_left _ ⟨f₁, h₁⟩ hm₂⟩
  have hN_neg : ∀ f : F, f ∈ O.nonunits → -f ∈ O.nonunits := by
    intro f h
    obtain ⟨h', hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨O.neg_mem _ h', neg_mem hm⟩
  have hN_prime : ∀ f₁ f₂ : F, f₁ ∈ O → f₂ ∈ O → f₁ * f₂ ∈ O.nonunits → f₁ ∈ O.nonunits ∨ f₂ ∈ O.nonunits := by
    intro f₁ f₂ h₁ h₂ h
    obtain ⟨h', hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
    have hm' : (⟨f₁, h₁⟩ : O) * ⟨f₂, h₂⟩ ∈ maximalIdeal O := by
      have e : (⟨f₁, h₁⟩ : O) * ⟨f₂, h₂⟩ = ⟨f₁ * f₂, h'⟩ := Subtype.ext rfl
      rw [e]; exact hm
    rcases (maximalIdeal.isMaximal O).isPrime.mem_or_mem hm' with h | h
    · exact Or.inl (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨h₁, h⟩)
    · exact Or.inr (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨h₂, h⟩)
  have hone : (1 : F) ∉ O.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff, map_one]; exact lt_irrefl 1

  have tbC : ∀ f : F, f ∈ C.integers → (∀ P ∈ C.dom, f ∈ P.toValuationSubring) → C.tubeBounded f := by
    intro f hf hall P hP
    obtain ⟨_, hA, _⟩ := C.pointwise P hP (hrat P hP) f hf (fun w hw _ => hall w hw)
    exact ⟨hall P hP, hA⟩
  have tb_mem : ∀ f : F, C.tubeBounded f → ∀ P ∈ C.dom, f ∈ P.toValuationSubring := fun f h P hP => (h P hP).1
  have tb_add : ∀ f g : F, C.tubeBounded f → C.tubeBounded g → C.tubeBounded (f + g) := fun f g hf hg =>
    tbC _ (C.integers.add_mem _ _ (hRint f hf) (hRint g hg)) fun P hP =>
      P.toValuationSubring.add_mem _ _ (tb_mem f hf P hP) (tb_mem g hg P hP)
  have tb_mul : ∀ f g : F, C.tubeBounded f → C.tubeBounded g → C.tubeBounded (f * g) := fun f g hf hg =>
    tbC _ (C.integers.mul_mem _ _ (hRint f hf) (hRint g hg)) fun P hP =>
      P.toValuationSubring.mul_mem _ _ (tb_mem f hf P hP) (tb_mem g hg P hP)
  have tb_neg : ∀ f : F, C.tubeBounded f → C.tubeBounded (-f) := fun f hf =>
    tbC _ (C.integers.neg_mem _ (hRint f hf)) fun P hP => P.toValuationSubring.neg_mem _ (tb_mem f hf P hP)
  have tb_sub : ∀ f g : F, C.tubeBounded f → C.tubeBounded g → C.tubeBounded (f - g) := fun f g hf hg => by
    rw [sub_eq_add_neg]; exact tb_add _ _ hf (tb_neg _ hg)
  have tb_zero : C.tubeBounded 0 := tbC _ C.integers.zero_mem fun P _ => P.toValuationSubring.zero_mem
  have tb_one : C.tubeBounded 1 := tbC _ C.integers.one_mem fun P _ => P.toValuationSubring.one_mem

  have res_congr : ∀ (f : F) (h₁ h₂ : f ∈ C.integers), C.residue ⟨f, h₁⟩ = C.residue ⟨f, h₂⟩ := fun _ _ _ => rfl
  have res_add : ∀ (f g : F) (hf : f ∈ C.integers) (hg : g ∈ C.integers),
      C.residue ⟨f + g, C.integers.add_mem _ _ hf hg⟩ = C.residue ⟨f, hf⟩ + C.residue ⟨g, hg⟩ := fun f g hf hg => by
    rw [← map_add]; rfl
  have res_mul : ∀ (f g : F) (hf : f ∈ C.integers) (hg : g ∈ C.integers),
      C.residue ⟨f * g, C.integers.mul_mem _ _ hf hg⟩ = C.residue ⟨f, hf⟩ * C.residue ⟨g, hg⟩ := fun f g hf hg => by
    rw [← map_mul]; rfl
  have res_sub : ∀ (f g : F) (hf : f ∈ C.integers) (hg : g ∈ C.integers),
      C.residue ⟨f - g, C.integers.sub_mem hf hg⟩ = C.residue ⟨f, hf⟩ - C.residue ⟨g, hg⟩ := fun f g hf hg => by
    rw [← map_sub]; rfl
  have res_zero_iff : ∀ (f : F) (hf : f ∈ C.integers), C.residue ⟨f, hf⟩ = 0 ↔ (⟨f, hf⟩ : C.integers) ∈ maximalIdeal C.integers :=
    fun f hf => by rw [← RingHom.mem_ker, C.ker_residue]

  have small : ∀ (f : F) (hf : f ∈ C.integers), C.tubeBounded f → C.residue ⟨f, hf⟩ = 0 → f ∈ O.nonunits := by
    intro f hf htb hres
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [ValuationSubring.mem_nonunits_iff, map_zero]; exact zero_lt_one
    obtain ⟨c, hcf, hcres⟩ := C.exists_smul_mem f hf0
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hcres
      have e : (⟨(0 : L) • f, hcf⟩ : C.integers) = 0 := Subtype.ext (zero_smul _ _)
      rw [e, map_zero]
    have hcf' : c • f = algebraMap L F c * f := Algebra.smul_def c f

    have htbc : C.tubeBounded (c • f) := tbC _ hcf fun P hP => by
      rw [hcf']; exact P.toValuationSubring.mul_mem _ _ (P.algebraMap_mem' c) (tb_mem f htb P hP)
    have hcO : c • f ∈ O := hRO _ htbc

    have hcC : algebraMap L F c ∉ C.integers := by
      intro hc
      apply hcres
      have hm : (⟨f, hf⟩ : C.integers) ∈ maximalIdeal C.integers := (res_zero_iff f hf).mp hres
      have e : (⟨c • f, hcf⟩ : C.integers) = ⟨algebraMap L F c, hc⟩ * ⟨f, hf⟩ := Subtype.ext hcf'
      rw [res_zero_iff, e]
      exact Ideal.mul_mem_left _ _ hm
    have hcA : c ∉ A := fun h => hcC ((C.algebraMap_mem_iff c).mpr h)
    have hcO' : algebraMap L F c ∉ O := fun h => hcA ((hO c).mp h)
    have hinv : algebraMap L F c⁻¹ ∈ O.nonunits := by
      rw [hnu]; right; rw [map_inv₀, inv_inv]; exact hcO'
    have e : f = (c • f) * algebraMap L F c⁻¹ := by
      rw [hcf', map_inv₀, mul_comm, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).mpr hc0), one_mul]
    rw [e]
    exact hN_mul _ _ hcO hinv

  have small_congr : ∀ (f g : F) (hf : f ∈ C.integers) (hg : g ∈ C.integers), C.tubeBounded f → C.tubeBounded g →
      C.residue ⟨f, hf⟩ = C.residue ⟨g, hg⟩ → g ∈ O.nonunits → f ∈ O.nonunits := by
    intro f g hf hg htf htg hres hgO
    have hd : f - g ∈ O.nonunits :=
      small _ (C.integers.sub_mem hf hg) (tb_sub _ _ htf htg) (by rw [res_sub f g hf hg, hres, sub_self])
    have e : f = (f - g) + g := by ring
    rw [e]; exact hN_add _ _ hd hgO

  have mem_regOff : ∀ g : Fbar, g ∈ ComponentChart.regOff (A := A) N ↔
      ∀ Q : Place (ResidueField A) Fbar, Q ∉ N → g ∈ Q.toValuationSubring := by
    intro g
    simp only [ComponentChart.regOff, Subring.mem_iInf]
    exact ⟨fun h Q hQ => h Q hQ, fun h Q hQ => h Q hQ⟩

  let Pbar : Ideal (ComponentChart.regOff (A := A) N) :=
    { carrier := {g | ∃ (f : F) (hf : f ∈ C.integers), C.tubeBounded f ∧ f ∈ O.nonunits ∧ C.residue ⟨f, hf⟩ = (g : Fbar)}
      zero_mem' := ⟨0, C.integers.zero_mem, tb_zero, by rw [ValuationSubring.mem_nonunits_iff, map_zero]; exact zero_lt_one,
        by rw [show (⟨(0 : F), C.integers.zero_mem⟩ : C.integers) = 0 from rfl, map_zero]; rfl⟩
      add_mem' := by
        rintro a b ⟨f₁, h₁, t₁, n₁, r₁⟩ ⟨f₂, h₂, t₂, n₂, r₂⟩
        exact ⟨f₁ + f₂, C.integers.add_mem _ _ h₁ h₂, tb_add _ _ t₁ t₂, hN_add _ _ n₁ n₂, by rw [res_add f₁ f₂ h₁ h₂, r₁, r₂]; rfl⟩
      smul_mem' := by
        rintro c a ⟨f, hf, t, n, r⟩
        obtain ⟨fc, hfc, tfc, rfc⟩ := hlift (c : Fbar) ((mem_regOff _).mp c.2)
        refine ⟨fc * f, C.integers.mul_mem _ _ hfc hf, tb_mul _ _ tfc t, hN_mul _ _ (hRO _ tfc) n, ?_⟩
        rw [res_mul fc f hfc hf, rfc, r, smul_eq_mul]; rfl }
  have mem_Pbar : ∀ g : ComponentChart.regOff (A := A) N, g ∈ Pbar ↔
      ∃ (f : F) (hf : f ∈ C.integers), C.tubeBounded f ∧ f ∈ O.nonunits ∧ C.residue ⟨f, hf⟩ = (g : Fbar) := fun g => Iff.rfl

  have res_mem_Pbar : ∀ (f : F) (hf : f ∈ C.integers) (htb : C.tubeBounded f)
      (hg : C.residue ⟨f, hf⟩ ∈ ComponentChart.regOff (A := A) N),
      (⟨C.residue ⟨f, hf⟩, hg⟩ : ComponentChart.regOff (A := A) N) ∈ Pbar ↔ f ∈ O.nonunits := by
    intro f hf htb hg
    constructor
    · rintro ⟨f', hf', t', n', r'⟩
      exact small_congr f f' hf hf' htb t' r'.symm n'
    · intro hn; exact ⟨f, hf, htb, hn, rfl⟩

  have hP_ne_top : Pbar ≠ ⊤ := by
    intro h
    have h1 : (1 : ComponentChart.regOff (A := A) N) ∈ Pbar := h ▸ Submodule.mem_top
    obtain ⟨f, hf, t, n, r⟩ := h1
    have : (1 : F) ∈ O.nonunits := by
      refine small_congr 1 f C.integers.one_mem hf tb_one t ?_ n
      rw [r]; rw [show (⟨(1 : F), C.integers.one_mem⟩ : C.integers) = 1 from rfl, map_one]; rfl
    exact hone this

  have hP_prime : Pbar.IsPrime := by
    refine Ideal.isPrime_iff.mpr ⟨hP_ne_top, ?_⟩
    rintro a b ⟨f, hf, t, n, r⟩
    obtain ⟨fa, hfa, ta, ra⟩ := hlift (a : Fbar) ((mem_regOff _).mp a.2)
    obtain ⟨fb, hfb, tb', rb⟩ := hlift (b : Fbar) ((mem_regOff _).mp b.2)
    have hprod : fa * fb ∈ O.nonunits := by
      refine small_congr (fa * fb) f (C.integers.mul_mem _ _ hfa hfb) hf (tb_mul _ _ ta tb') t ?_ n
      rw [res_mul fa fb hfa hfb, ra, rb, r]; rfl
    rcases hN_prime _ _ (hRO _ ta) (hRO _ tb') hprod with h | h
    · exact Or.inl ⟨fa, hfa, ta, h, ra⟩
    · exact Or.inr ⟨fb, hfb, tb', h, rb⟩

  by_cases hbot : Pbar = ⊥
  · left

    have hCO : ∀ h : F, h ∈ C.integers → h ∈ O := by
      intro h hh
      obtain ⟨r, s, hs, tr, ts, hres, hrs⟩ := hloc h hh
      have hs0 : s ≠ 0 := by
        rintro rfl; apply hres
        rw [show (⟨(0 : F), hs⟩ : C.integers) = 0 from rfl, map_zero]
      have hsu : s ∉ O.nonunits := by
        intro hsn
        have hg : C.residue ⟨s, hs⟩ ∈ ComponentChart.regOff (A := A) N := (mem_regOff _).mpr (hreg s hs ts)
        have hm : (⟨C.residue ⟨s, hs⟩, hg⟩ : ComponentChart.regOff (A := A) N) ∈ Pbar := (res_mem_Pbar s hs ts hg).mpr hsn
        rw [hbot, Ideal.mem_bot] at hm
        exact hres (congrArg Subtype.val hm)
      have hsinv : s⁻¹ ∈ O := by
        have := (hnu O s).not.mp hsu
        push Not at this
        exact this.2
      have e : h = r * s⁻¹ := by rw [← hrs, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
      rw [e]; exact O.mul_mem _ _ (hRO _ tr) hsinv

    have hOC : ∀ x : F, x ∈ O → x ∈ C.integers := by
      intro x hx
      by_contra hxC
      have hx0 : x ≠ 0 := by rintro rfl; exact hxC C.integers.zero_mem
      obtain ⟨c, hcx, hcres⟩ := C.exists_smul_mem x hx0
      have hc0 : c ≠ 0 := by
        rintro rfl; apply hcres
        rw [show (⟨(0 : L) • x, hcx⟩ : C.integers) = 0 from Subtype.ext (zero_smul _ _), map_zero]

      have hunit : (c • x)⁻¹ ∈ C.integers := by
        by_contra hni
        apply hcres
        rw [res_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff, hnu]
        exact Or.inr hni

      have hcx0 : c • x ≠ 0 := smul_ne_zero hc0 hx0
      have e1 : algebraMap L F c⁻¹ = x * (c • x)⁻¹ := by
        rw [Algebra.smul_def, mul_inv, ← mul_assoc, mul_comm x, mul_assoc, mul_inv_cancel₀ hx0, mul_one, map_inv₀]
      have hcinvO : algebraMap L F c⁻¹ ∈ O := by rw [e1]; exact O.mul_mem _ _ hx (hCO _ hunit)
      have hcinvA : c⁻¹ ∈ A := (hO _).mp hcinvO
      have hcinvC : algebraMap L F c⁻¹ ∈ C.integers := (C.algebraMap_mem_iff _).mpr hcinvA
      apply hxC
      have e2 : x = algebraMap L F c⁻¹ * (c • x) := by
        rw [Algebra.smul_def, map_inv₀, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).mpr hc0), one_mul]
      rw [e2]; exact C.integers.mul_mem _ _ hcinvC hcx
    exact le_antisymm (fun x hx => hOC x hx) (fun x hx => hCO x hx)

  · right
    have hPmax : Pbar.IsMaximal := hdim Pbar hP_prime hbot
    obtain ⟨Q, ⟨hQN, hQ⟩, huniq⟩ := hdict1 Pbar hPmax

    have centre_iff : ∀ Q' : Place (ResidueField A) Fbar, Q' ∉ N →
        (C.IsCentre N O Q' ↔ ∀ g : ComponentChart.regOff (A := A) N, g ∈ Pbar ↔ ((g : Fbar) = 0 ∨ 0 < Q'.ord (g : Fbar))) := by
      intro Q' hQ'N
      constructor
      · rintro ⟨-, hc⟩ g
        obtain ⟨f, hf, t, r⟩ := hlift (g : Fbar) ((mem_regOff _).mp g.2)
        have e : g = ⟨C.residue ⟨f, hf⟩, r.symm ▸ g.2⟩ := Subtype.ext r.symm
        rw [e, res_mem_Pbar f hf t, ← hmax]
        exact (hc f hf t).symm
      · intro hc
        refine ⟨hQ'N, fun f hf t => ?_⟩
        have hg : C.residue ⟨f, hf⟩ ∈ ComponentChart.regOff (A := A) N := (mem_regOff _).mpr (hreg f hf t)
        rw [hmax, ← res_mem_Pbar f hf t hg, hc]
    refine ⟨Q, (centre_iff Q hQN).mpr hQ, fun Q' hQ' => ?_⟩
    exact huniq Q' ⟨hQ'.1, (centre_iff Q' hQ'.1).mp hQ'⟩

end S_AlgebraicCurve_ComponentChart_eq_integers_or_existsUnique_isCentre_of_forall_tubeBounded_mem_of_regular
end P2MW
export P2MW.S_AlgebraicCurve_ComponentChart_eq_integers_or_existsUnique_isCentre_of_forall_tubeBounded_mem_of_regular (solution)
