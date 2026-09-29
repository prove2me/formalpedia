-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_mem_disc_forall_evalAt_eq_zero_iff_dvd_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/0436045b-3f1f-5db5-9abf-f5d84adf16f5

import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_IsCurveOver

import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_mem_iff_adjoin_sup_of_linearDisjoint
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_mem_disc_forall_evalAt_eq_zero_iff_dvd_of_prime

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace BPAux

open AlgebraicCurve

variable {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']

theorem evalAt_add_of_mem (v : Place K' F') (hv : v.IsRational) {f g : F'}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem evalAt_eq_zero_iff_mem_maximalIdeal (v : Place K' F') (hv : v.IsRational) {g : F'}
    (hg : g ∈ v.toValuationSubring) :
    v.evalAt g = 0 ↔ (⟨g, hg⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [← IsLocalRing.residue_eq_zero_iff, ← v.algebraMap_evalAt hv hg]
  constructor
  · intro h; rw [h, map_zero]
  · intro h
    exact (algebraMap K' v.ResidueField).injective (by rw [h, map_zero])

theorem mem_of_isIntegral {L' : Type*} [Field L'] (A : ValuationSubring L') {x : L'}
    (n : ℕ) (a : Fin n → L') (ha : ∀ i, a i ∈ A) (hx : x ^ n + ∑ i : Fin n, a i * x ^ (i : ℕ) = 0) (hn : 0 < n) :
    x ∈ A := by
  by_contra hxA
  have hx0 : x ≠ 0 := fun h => hxA (h ▸ A.zero_mem)
  have hinv : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hxA

  have hinv_lt : A.valuation x⁻¹ < 1 := by
    rw [map_inv₀, inv_lt_one₀ (lt_of_le_of_ne zero_le' ((map_ne_zero A.valuation).mpr hx0).symm)]
    exact lt_of_not_ge fun h => hxA ((A.valuation_le_one_iff x).mp h)

  have hone : (1 : L') = -∑ i : Fin n, a i * (x⁻¹) ^ (n - (i : ℕ)) := by
    have hxn : x ^ n ≠ 0 := pow_ne_zero _ hx0
    have h1 : x ^ n * (1 + ∑ i : Fin n, a i * (x⁻¹) ^ (n - (i : ℕ))) = 0 := by
      rw [mul_add, mul_one, Finset.mul_sum, ← hx]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : (i : ℕ) ≤ n := le_of_lt i.2
      rw [inv_pow, ← mul_assoc, mul_comm (x ^ n), mul_assoc]
      congr 1
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hx0, ← zpow_natCast]
      congr 1; push_cast; omega
    have := (mul_eq_zero.mp h1).resolve_left hxn
    linear_combination this
  have hlt : A.valuation (1 : L') < 1 := by
    rw [hone, Valuation.map_neg]
    apply A.valuation.map_sum_lt one_ne_zero
    intro i _
    rw [map_mul, map_pow]
    have hexp : 0 < n - (i : ℕ) := Nat.sub_pos_of_lt i.2
    calc A.valuation (a i) * A.valuation x⁻¹ ^ (n - (i : ℕ)) ≤ 1 * A.valuation x⁻¹ ^ (n - (i : ℕ)) := by
          gcongr; exact (A.valuation_le_one_iff _).mpr (ha i)
      _ = A.valuation x⁻¹ ^ (n - (i : ℕ)) := one_mul _
      _ < 1 := pow_lt_one₀ zero_le' hinv_lt hexp.ne'
  rw [map_one] at hlt
  exact lt_irrefl _ hlt

end BPAux

open BPAux AlgebraicCurve.GaussReduction in
set_option maxHeartbeats 3200000 in

theorem solution
    {k₀ L F : Type} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra k₀ F] [Algebra L F] [IsScalarTower k₀ L F]
    [CharZero L] [IsAlgClosed L] [IsCurveOver L F]
    (F₀ : IntermediateField k₀ F)
    (hgen : IntermediateField.adjoin k₀ (Set.range (algebraMap L F)) ⊔ F₀ = ⊤)
    (A : ValuationSubring L)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)

    (K₁ : IntermediateField k₀ L) (halg : ∀ x : L, IsAlgebraic ↥K₁ x)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : L) ∈ A)
    (hκ₁ : Function.Surjective (fun a : ↥A₁ => IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩))

    (S₁ : Subring F) (φ₁ : Polynomial ↥A₁ →+* ↥S₁) (χ₁ : ↥S₁ →+* ResidueField ↥A) (D₁ : Set (Place L F))
    (hAS : ∀ a : ↥A₁, algebraMap L F ((a : ↥K₁) : L) ∈ S₁)
    (hφC : ∀ a : ↥A₁, ((φ₁ (Polynomial.C a) : ↥S₁) : F) = algebraMap L F ((a : ↥K₁) : L))
    (hχC : ∀ a : ↥A₁, χ₁ (φ₁ (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩)
    (hχt : χ₁ (φ₁ Polynomial.X) = 0)
    (hD : ∀ P, P ∈ D₁ ↔ (P.IsRational ∧
      (∀ f : ↥S₁, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
      (∀ f : ↥S₁, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₁ f = 0)))

    (ht : ∀ c : ↥A₁, φ₁ Polynomial.X ≠ φ₁ (Polynomial.C c))
    (hlocal : IsLocalRing ↥S₁) (hmax : ∀ f : ↥S₁, f ∈ maximalIdeal ↥S₁ ↔ χ₁ f = 0)
    (hnoeth : IsNoetherianRing ↥S₁) (hufd : UniqueFactorizationMonoid ↥S₁)
    (hS₁F₁ : ∀ f : F, f ∈ S₁ → f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)
    (hfrac : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ → ∃ g h : ↥S₁, (h : F) ≠ 0 ∧ f * (h : F) = (g : F))
    (hld : ∀ (m : ℕ) (c : Fin m → L) (a : Fin m → F), (∀ i, a i ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀) →
      LinearIndependent ↥K₁ c → ∑ i, algebraMap L F (c i) * a i = 0 → ∀ i, a i = 0)
    (hdvr : ∀ O : ValuationSubring F, (∀ x : L, algebraMap L F x ∈ O) → O ≠ ⊤ → IsPrincipalIdealRing ↥O)
    (ϖ : ↥A₁) (hϖ : maximalIdeal ↥A₁ = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0)
    (hprime : Prime (φ₁ (Polynomial.C ϖ)))
    (hRint : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ →
      (f ∈ R.integers ↔ ∃ g h : ↥S₁, ¬ (φ₁ (Polynomial.C ϖ) ∣ h) ∧ f * (h : F) = (g : F)))

    (hker : ∀ χ : ↥S₁ →+* ↥A₁, (∀ a : ↥A₁, χ (φ₁ (Polynomial.C a)) = a) →
      (∀ f : ↥S₁, IsLocalRing.residue ↥A ⟨((χ f : ↥K₁) : L), (hA₁ _).mp (χ f).2⟩ = χ₁ f) →
      RingHom.ker χ = Ideal.span {φ₁ Polynomial.X - φ₁ (Polynomial.C (χ (φ₁ Polynomial.X)))})

    (hbranch : ∀ p : ↥S₁, Prime p → ¬ Associated p (φ₁ (Polynomial.C ϖ)) →
      ∀ x : ↥S₁, ∃ r : Polynomial ↥A₁, r.Monic ∧ p ∣ (r.map (φ₁.comp Polynomial.C)).eval x)
    (p : ↥S₁) (hp : Prime p) (hpϖ : ¬ Associated p (φ₁ (Polynomial.C ϖ))) :
    ∃ P : Place L F, P ∈ D₁ ∧ (∀ f : ↥S₁, P.evalAt (f : F) = 0 ↔ p ∣ f) := by
  classical
  haveI := hlocal
  haveI := hnoeth
  haveI := hufd
  have hpirr : Irreducible p := hp.irreducible
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp0F : (p : F) ≠ 0 := fun h => hp0 (Subtype.ext h)
  set ϖ' : ↥S₁ := φ₁ (Polynomial.C ϖ) with hϖ'
  have hpϖ' : ¬ p ∣ ϖ' := fun h => hpϖ (hp.associated_of_dvd hprime h)

  have hφval : ∀ a : ↥A₁, ((φ₁ (Polynomial.C a) : ↥S₁) : F) = algebraMap L F ((a : ↥K₁) : L) := hφC
  have hφne : ∀ a : ↥A₁, a ≠ 0 → φ₁ (Polynomial.C a) ≠ 0 := by
    intro a ha h0
    apply ha
    have h1 : algebraMap L F ((a : ↥K₁) : L) = 0 := by rw [← hφval, h0]; rfl
    have h2 : ((a : ↥K₁) : L) = 0 := (map_eq_zero_iff _ (algebraMap L F).injective).mp h1
    exact Subtype.ext (Subtype.ext h2)
  have hAp : ∀ a : ↥A₁, a ≠ 0 → ¬ p ∣ φ₁ (Polynomial.C a) := by
    intro a ha hdvd

    have hpow : ∀ n : ℕ, ∃ c : ↥A₁, a = ϖ ^ n * c := by
      intro n
      induction n with
      | zero => exact ⟨a, by rw [pow_zero, one_mul]⟩
      | succ n ih =>
        obtain ⟨c, hc⟩ := ih

        have hcunit : ¬ IsUnit c := by
          intro hu
          apply hpϖ'
          have h1 : p ∣ ϖ' ^ n * φ₁ (Polynomial.C c) := by
            have : φ₁ (Polynomial.C a) = ϖ' ^ n * φ₁ (Polynomial.C c) := by
              rw [hc, map_mul, map_pow, map_mul, map_pow]
            rw [← this]; exact hdvd
          have h2 : p ∣ ϖ' ^ n := by
            rcases hp.dvd_or_dvd h1 with h | h
            · exact h
            · exfalso
              exact hp.not_unit (isUnit_of_dvd_unit h ((hu.map (Polynomial.C : ↥A₁ →+* Polynomial ↥A₁)).map φ₁))
          exact hp.dvd_of_dvd_pow h2
        have hcmax : c ∈ maximalIdeal ↥A₁ := (IsLocalRing.mem_maximalIdeal c).mpr hcunit
        rw [hϖ, Ideal.mem_span_singleton] at hcmax
        obtain ⟨c', hc'⟩ := hcmax
        exact ⟨c', by rw [hc, hc', pow_succ]; ring⟩

    obtain ⟨m, b, hb, hab⟩ := WfDvdMonoid.max_power_factor (hφne a ha) hprime.irreducible
    obtain ⟨c, hc⟩ := hpow (m + 1)
    apply hb
    have h1 : ϖ' ^ (m + 1) ∣ ϖ' ^ m * b := by
      rw [← hab, hc, map_mul, map_pow, map_mul, map_pow]
      exact Dvd.intro _ rfl
    rw [pow_succ] at h1
    exact (mul_dvd_mul_iff_left (pow_ne_zero m hprime.ne_zero)).mp h1

  let V : ValuationSubring ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀) :=
    { carrier := {f | ∃ g h : ↥S₁, ¬ p ∣ h ∧ (f : F) * (h : F) = (g : F)}
      mul_mem' := by
        rintro f₁ f₂ ⟨g₁, h₁, hh₁, e₁⟩ ⟨g₂, h₂, hh₂, e₂⟩
        refine ⟨g₁ * g₂, h₁ * h₂, fun hd => (hp.dvd_or_dvd hd).elim hh₁ hh₂, ?_⟩
        push_cast
        rw [mul_mul_mul_comm, e₁, e₂]
      one_mem' := ⟨1, 1, fun hd => hp.not_unit (isUnit_of_dvd_one hd), by push_cast; ring⟩
      add_mem' := by
        rintro f₁ f₂ ⟨g₁, h₁, hh₁, e₁⟩ ⟨g₂, h₂, hh₂, e₂⟩
        refine ⟨g₁ * h₂ + g₂ * h₁, h₁ * h₂, fun hd => (hp.dvd_or_dvd hd).elim hh₁ hh₂, ?_⟩
        push_cast; linear_combination h₂ * e₁ + h₁ * e₂
      zero_mem' := ⟨0, 1, fun hd => hp.not_unit (isUnit_of_dvd_one hd), by push_cast; ring⟩
      neg_mem' := by
        rintro f ⟨g, h, hh, e⟩
        exact ⟨-g, h, hh, by push_cast; linear_combination (-1 : F) * e⟩
      mem_or_inv_mem' := by
        intro f
        obtain ⟨g, h, hh0, hfh⟩ := hfrac (f : F) f.2
        by_cases hg0 : g = 0
        · left
          refine ⟨0, 1, fun hd => hp.not_unit (isUnit_of_dvd_one hd), ?_⟩
          have hf0 : (f : F) = 0 := by
            have : (f : F) * (h : F) = 0 := by rw [hfh, hg0]; rfl
            exact (mul_eq_zero.mp this).resolve_right hh0
          push_cast; rw [hf0]; ring
        have hh0' : h ≠ 0 := fun h0 => hh0 (by rw [h0]; rfl)
        obtain ⟨m, g', hg', hgeq⟩ := WfDvdMonoid.max_power_factor hg0 hpirr
        obtain ⟨n, h', hh', hheq⟩ := WfDvdMonoid.max_power_factor hh0' hpirr

        by_cases hmn : n ≤ m
        · left
          refine ⟨p ^ (m - n) * g', h', hh', ?_⟩
          have : (f : F) * (h : F) * (h' : F) = (g : F) * (h' : F) := by rw [hfh]
          apply mul_right_cancel₀ (show ((p : ↥S₁) : F) ^ n ≠ 0 from pow_ne_zero _ hp0F)
          have e1 : (h : F) = (p : F) ^ n * (h' : F) := by rw [hheq]; push_cast; ring
          have e2 : (g : F) = (p : F) ^ m * (g' : F) := by rw [hgeq]; push_cast; ring
          push_cast
          rw [show m = (m - n) + n by omega] at e2
          calc (f : F) * (h' : F) * (p : F) ^ n = (f : F) * (h : F) := by rw [e1]; ring
            _ = (g : F) := hfh
            _ = (p : F) ^ (m - n) * (g' : F) * (p : F) ^ n := by rw [e2, pow_add]; ring
        · right
          push Not at hmn
          refine ⟨p ^ (n - m) * h', g', hg', ?_⟩
          have hfF0 : (f : F) ≠ 0 := by
            intro h0; apply hg0; apply Subtype.ext
            have : (g : F) = 0 := by rw [← hfh, h0, zero_mul]
            exact this
          have e1 : (h : F) = (p : F) ^ n * (h' : F) := by rw [hheq]; push_cast; ring
          have e2 : (g : F) = (p : F) ^ m * (g' : F) := by rw [hgeq]; push_cast; ring
          have key : (f : F) * ((p : F) ^ (n - m) * (h' : F)) = (g' : F) := by
            apply mul_left_cancel₀ (pow_ne_zero m hp0F)
            calc (p : F) ^ m * ((f : F) * ((p : F) ^ (n - m) * (h' : F)))
                = (f : F) * ((p : F) ^ ((n - m) + m) * (h' : F)) := by rw [pow_add]; ring
              _ = (f : F) * (h : F) := by rw [e1, show (n - m) + m = n by omega]
              _ = (g : F) := hfh
              _ = (p : F) ^ m * (g' : F) := e2
          push_cast
          rw [← key, ← mul_assoc, inv_mul_cancel₀ hfF0, one_mul] }
  have hVmem : ∀ f : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), f ∈ V ↔ ∃ g h : ↥S₁, ¬ p ∣ h ∧ (f : F) * (h : F) = (g : F) := fun f => Iff.rfl

  have hSV : ∀ f : ↥S₁, (⟨(f : F), hS₁F₁ _ f.2⟩ : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)) ∈ V := fun f =>
    ⟨f, 1, fun hd => hp.not_unit (isUnit_of_dvd_one hd), by push_cast; ring⟩

  have hK₁V : ∀ (x : ↥K₁) (hx : algebraMap L F (x : L) ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀),
      (⟨algebraMap L F (x : L), hx⟩ : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)) ∈ V := by
    intro x hxm
    rcases A₁.mem_or_inv_mem x with hx | hx
    · refine ⟨φ₁ (Polynomial.C ⟨x, hx⟩), 1, fun hd => hp.not_unit (isUnit_of_dvd_one hd), ?_⟩
      rw [hφval]; push_cast; ring
    · by_cases hx0 : x = 0
      · refine ⟨0, 1, fun hd => hp.not_unit (isUnit_of_dvd_one hd), ?_⟩
        simp [hx0]
      have hxL : (x : L) ≠ 0 := fun h => hx0 (Subtype.ext h)
      have hxi0 : (⟨x⁻¹, hx⟩ : ↥A₁) ≠ 0 := fun h => by
        apply hx0; have := congrArg Subtype.val h; simpa using this
      refine ⟨1, φ₁ (Polynomial.C ⟨x⁻¹, hx⟩), hAp _ hxi0, ?_⟩
      have hcoe : (((⟨x⁻¹, hx⟩ : ↥A₁) : ↥K₁) : L) = ((x : L))⁻¹ := by push_cast; rfl
      rw [hφval, hcoe, OneMemClass.coe_one]
      show algebraMap L F (x : L) * algebraMap L F ((x : L))⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hxL, map_one]

  have hVtop : V ≠ ⊤ := by
    intro htop
    have hpi : (⟨(p : F), hS₁F₁ _ p.2⟩ : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀))⁻¹ ∈ V := htop.symm ▸ ValuationSubring.mem_top _
    obtain ⟨g, h, hh, e⟩ := hpi
    apply hh
    refine ⟨g, Subtype.ext ?_⟩
    push_cast at e ⊢
    rw [← e, ← mul_assoc, mul_inv_cancel₀ hp0F, one_mul]

  obtain ⟨P, hP⟩ := AlgebraicCurve.Place.exists_forall_mem_iff_adjoin_sup_of_linearDisjoint F₀ K₁ hgen hld hdvr V hK₁V hVtop
  have hPrat : P.IsRational :=
    (AlgebraicCurve.Place.isRational_iff_deg_eq_one P).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed P)
  have hSP : ∀ f : ↥S₁, (f : F) ∈ P.toValuationSubring := fun f => (hP ⟨(f : F), hS₁F₁ _ f.2⟩).mpr (hSV f)

  have hcentre : ∀ f : ↥S₁, P.evalAt (f : F) = 0 ↔ p ∣ f := by
    intro f
    rw [evalAt_eq_zero_iff_mem_maximalIdeal P hPrat (hSP f), IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hnu
      by_contra hpf
      apply hnu
      by_cases hf0 : (f : F) = 0
      · exfalso; apply hpf; rw [show f = 0 from Subtype.ext hf0]; exact dvd_zero p
      have hinvV : (⟨(f : F), hS₁F₁ _ f.2⟩ : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀))⁻¹ ∈ V :=
        ⟨1, f, hpf, by push_cast; rw [inv_mul_cancel₀ hf0]⟩
      have hinvP : ((f : F))⁻¹ ∈ P.toValuationSubring := by
        have := (hP _).mpr hinvV; simpa using this
      exact IsUnit.of_mul_eq_one (b := ⟨_, hinvP⟩) (Subtype.ext (mul_inv_cancel₀ hf0))
    · intro hpf hu

      have hf0 : (f : F) ≠ 0 := by
        intro h0
        obtain ⟨u, hu'⟩ := hu
        exact u.ne_zero (Subtype.ext (by rw [hu']; exact h0))
      obtain ⟨u, hu'⟩ := hu
      have hinvP : ((f : F))⁻¹ ∈ P.toValuationSubring := by
        have h1 : (((u⁻¹ : (P.toValuationSubring)ˣ) : P.toValuationSubring) : F) = ((f : F))⁻¹ := by
          have h2 := congrArg (fun w : P.toValuationSubring => (w : F)) u.inv_mul
          rw [hu'] at h2
          simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h2
          exact eq_inv_of_mul_eq_one_left h2
        rw [← h1]; exact SetLike.coe_mem _
      have hinvV : (⟨(f : F), hS₁F₁ _ f.2⟩ : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀))⁻¹ ∈ V := by
        apply (hP _).mp; simpa using hinvP
      obtain ⟨g, h, hh, e⟩ := hinvV
      apply hh
      have hhfg : h = f * g := by
        apply Subtype.ext
        push_cast at e ⊢
        rw [← e, ← mul_assoc, mul_inv_cancel₀ hf0, one_mul]
      rw [hhfg]
      exact Dvd.dvd.mul_right hpf g

  let ψL : ↥S₁ →+* L :=
    { toFun := fun f => P.evalAt (f : F)
      map_one' := by simp [Place.evalAt_one]
      map_mul' := fun a b => by
        simp only [Subring.coe_mul]; exact evalAt_mul_of_mem P hPrat (hSP a) (hSP b)
      map_zero' := by
        simp only [Subring.coe_zero]
        have := evalAt_algebraMap_const P hPrat (0 : L); rwa [map_zero] at this
      map_add' := fun a b => by
        simp only [Subring.coe_add]; exact evalAt_add_of_mem P hPrat (hSP a) (hSP b) }
  have hψL : ∀ f : ↥S₁, ψL f = P.evalAt (f : F) := fun f => rfl
  have hψLC : ∀ a : ↥A₁, ψL (φ₁ (Polynomial.C a)) = ((a : ↥K₁) : L) := by
    intro a
    rw [hψL, hφval]
    exact evalAt_algebraMap_const P hPrat (((a : ↥K₁) : L))
  have hinclA : ∀ a : ↥A₁, ((a : ↥K₁) : L) ∈ A := fun a => (hA₁ a).mp a.2

  have hvalA : ∀ f : ↥S₁, P.evalAt (f : F) ∈ A := by
    intro f
    obtain ⟨q, hqm, hqdvd⟩ := hbranch p hp hpϖ f
    have hzero : ψL ((q.map (φ₁.comp Polynomial.C)).eval f) = 0 := by
      rw [hψL]; exact (hcentre _).mpr hqdvd
    rw [Polynomial.eval_map, Polynomial.hom_eval₂] at hzero

    set n := q.natDegree with hn
    have hn0 : n ≠ 0 := by
      intro hn0
      have hq1 : q = 1 := Polynomial.eq_one_of_monic_natDegree_zero hqm (by rw [← hn, hn0])
      apply hp.not_unit
      apply isUnit_of_dvd_one
      have := hqdvd
      rwa [hq1, Polynomial.map_one, Polynomial.eval_one] at this
    rw [Polynomial.eval₂_eq_sum_range, ← hn, Finset.sum_range_succ, hqm.coeff_natDegree, map_one, one_mul,
      Finset.sum_range] at hzero
    have hrel : (ψL f : L) ^ n + ∑ i : Fin n, ((ψL.comp (φ₁.comp Polynomial.C)) (q.coeff i)) * (ψL f) ^ (i : ℕ) = 0 := by
      rw [← hzero]; ring
    have hrelL : ((ψL f : L) : L) ^ n + ∑ i : Fin n,
        (((q.coeff i : ↥K₁) : L) : L) * (ψL f) ^ (i : ℕ) = 0 := by
      rw [← hrel]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, hψLC]
    exact mem_of_isIntegral A n (fun i => ((q.coeff i : ↥K₁) : L)) (fun i => hinclA _)
      hrelL (Nat.pos_of_ne_zero hn0)

  let ψA : ↥S₁ →+* ↥A := ψL.codRestrict A.toSubring (fun f => hvalA f)
  have hψA : ∀ f : ↥S₁, ((ψA f : ↥A) : L) = P.evalAt (f : F) := fun f => rfl
  have hψAC : ∀ a : ↥A₁, ψA (φ₁ (Polynomial.C a)) = ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩ :=
    fun a => Subtype.ext (hψLC a)
  let θ : ↥S₁ →+* IsLocalRing.ResidueField ↥A := (IsLocalRing.residue ↥A).comp ψA
  have hθC : ∀ a : ↥A₁, θ (φ₁ (Polynomial.C a)) = χ₁ (φ₁ (Polynomial.C a)) := by
    intro a; rw [hχC]; show IsLocalRing.residue ↥A (ψA _) = _; rw [hψAC]
  have hθsurj : Function.Surjective θ := by
    intro z
    obtain ⟨a, ha⟩ := hκ₁ z
    exact ⟨φ₁ (Polynomial.C a), by rw [hθC, hχC]; exact ha⟩
  have hkerθ : RingHom.ker θ = maximalIdeal ↥S₁ :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective θ hθsurj)
  have hθχ : ∀ f : ↥S₁, θ f = χ₁ f := by
    intro f
    obtain ⟨a, ha⟩ := hκ₁ (χ₁ f)
    have hdiff : f - φ₁ (Polynomial.C a) ∈ RingHom.ker θ := by
      rw [hkerθ, hmax, map_sub, hχC, sub_eq_zero]
      exact ha.symm
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hdiff
    rw [hdiff, hθC, hχC]; exact ha
  refine ⟨P, (hD P).mpr ⟨hPrat, fun f => ⟨hSP f, hvalA f⟩, fun f => ?_⟩, hcentre⟩
  rw [← hψA, ← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff, ← hθχ]
  rfl

end S_AlgebraicCurve_RegularProlongation_exists_mem_disc_forall_evalAt_eq_zero_iff_dvd_of_prime
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_mem_disc_forall_evalAt_eq_zero_iff_dvd_of_prime (solution)
