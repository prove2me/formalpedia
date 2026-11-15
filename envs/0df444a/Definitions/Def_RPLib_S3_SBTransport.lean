-- Prove2me | Definitions.Def_RPLib_S3_SBTransport
-- name    : RPLib_S3_SBTransport
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:28:17.635693+00:00
-- url     : https://prove2.me/theorems/45368581-57de-4ed1-bf2a-ea741066fabf
-- title:
--   Weight-two Ramanujan-Petersson library: Transport of places along automorphisms of a function field (obligation O1)
-- statement:
--   Transport of places along automorphisms of a function field (obligation O1).
--
--   `σ : F ≃ₐ[RatFunc Fq] F` restricts to ring automorphisms of `Rfin` and `Rinf`, hence permutes the
--   places (`placeMap σ`), preserving degrees and valuations: `v_{σ P} (σ f) = v_P f`. These are the
--   hypotheses `hτ`, `hπ` of `twisted_stepanov` (SB_Core) for `τ = σ`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_SBCore
import Definitions.Def_RPLib_S3_RRD

/-!
# Transport of places along automorphisms of a function field (obligation O1)

`σ : F ≃ₐ[RatFunc Fq] F` restricts to ring automorphisms of `Rfin` and `Rinf`, hence permutes the
places (`placeMap σ`), preserving degrees and valuations: `v_{σ P} (σ f) = v_P f`. These are the
hypotheses `hτ`, `hπ` of `twisted_stepanov` (SB_Core) for `τ = σ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial

namespace RamanujanPetersson.ZetaSB

open RR

/-- Elements of `ℤᵐ⁰` below `1` are determined by their comparisons with `exp (-n)`. -/
theorem le_of_forall_le_exp_neg {x y : ℤᵐ⁰} (hy : y ≤ 1)
    (h : ∀ n : ℕ, y ≤ exp (-(n : ℤ)) → x ≤ exp (-(n : ℤ))) : x ≤ y := by
  rcases eq_or_ne y 0 with rfl | hy0
  · by_contra hx
    have hx0 : x ≠ 0 := by rintro rfl; exact hx le_rfl
    obtain ⟨a, rfl⟩ : ∃ a : ℤ, x = exp a := ⟨_, (exp_log hx0).symm⟩
    have h1 := h (1 - a).toNat zero_le
    rw [exp_le_exp] at h1
    omega
  · obtain ⟨b, rfl⟩ : ∃ b : ℤ, y = exp b := ⟨_, (exp_log hy0).symm⟩
    have hl : b ≤ 0 := by rw [← exp_zero, exp_le_exp] at hy; exact hy
    have h1 := h (-b).toNat (by rw [Int.toNat_of_nonneg (by omega), neg_neg])
    rwa [Int.toNat_of_nonneg (by omega), neg_neg] at h1

theorem eq_of_forall_le_exp_neg_iff {x y : ℤᵐ⁰} (hx : x ≤ 1) (hy : y ≤ 1)
    (h : ∀ n : ℕ, x ≤ exp (-(n : ℤ)) ↔ y ≤ exp (-(n : ℤ))) : x = y :=
  le_antisymm (le_of_forall_le_exp_neg hy fun n hn => (h n).mpr hn)
    (le_of_forall_le_exp_neg hx fun n hn => (h n).mp hn)

section Generic

variable {S : Type*} [CommRing S] [IsDedekindDomain S]
variable {K : Type*} [Field K] [Algebra S K] [IsFractionRing S K]

theorem equiv_asIdeal (e : S ≃+* S) (P : HeightOneSpectrum S) :
    (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal = P.asIdeal.map e := by
  rw [← Ideal.comap_symm]; rfl

theorem mem_equiv_pow_iff (e : S ≃+* S) (P : HeightOneSpectrum S) (r : S) (n : ℕ) :
    e r ∈ (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal ^ n ↔ r ∈ P.asIdeal ^ n := by
  rw [equiv_asIdeal, ← Ideal.map_pow, ← Ideal.comap_symm, Ideal.mem_comap]
  simp

theorem intValuation_equiv (e : S ≃+* S) (P : HeightOneSpectrum S) (r : S) :
    (HeightOneSpectrum.equivOfRingEquiv e P).intValuation (e r) = P.intValuation r := by
  refine eq_of_forall_le_exp_neg_iff (HeightOneSpectrum.intValuation_le_one _ _)
    (HeightOneSpectrum.intValuation_le_one _ _) fun n => ?_
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
    mem_equiv_pow_iff]

/-- Valuations are transported along a ring automorphism `σ` of `K` restricting to `e` on `S`. -/
theorem valuation_equiv (e : S ≃+* S) (σ : K →+* K)
    (hσ : ∀ r : S, σ (algebraMap S K r) = algebraMap S K (e r)) (P : HeightOneSpectrum S) (f : K) :
    (HeightOneSpectrum.equivOfRingEquiv e P).valuation K (σ f) = P.valuation K f := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) f
  rw [map_div₀, hσ, hσ, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_equiv, intValuation_equiv]

variable (Fq : Type*) [Field Fq] [Fintype Fq] [Algebra Fq S] [Places.FiniteQuot S]

theorem deg_equiv (e : S ≃+* S) (P : HeightOneSpectrum S) :
    Places.deg Fq (HeightOneSpectrum.equivOfRingEquiv e P) = Places.deg Fq P := by
  have hc : Nat.card (S ⧸ (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal) =
      Nat.card (S ⧸ P.asIdeal) :=
    (Nat.card_congr (Ideal.quotientEquiv P.asIdeal _ e (equiv_asIdeal e P)).toEquiv).symm
  rw [Places.card_residue_eq Fq, Places.card_residue_eq Fq] at hc
  exact Nat.pow_right_injective (Fintype.one_lt_card_iff_nontrivial.mpr inferInstance) hc

end Generic

section FF

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- `σ` restricted to the finite integral closure `Rfin`. -/
noncomputable def finEquiv (σ : F ≃ₐ[RatFunc Fq] F) : Places.Rfin Fq F ≃+* Places.Rfin Fq F :=
  ((σ.restrictScalars Fq[X]).mapIntegralClosure :
    integralClosure Fq[X] F ≃ₐ[Fq[X]] integralClosure Fq[X] F).toRingEquiv

/-- `σ` restricted to the infinite integral closure `Rinf`. -/
noncomputable def infEquiv (σ : F ≃ₐ[RatFunc Fq] F) : Places.Rinf Fq F ≃+* Places.Rinf Fq F :=
  ((σ.restrictScalars (Places.Oinf Fq)).mapIntegralClosure :
    integralClosure (Places.Oinf Fq) F ≃ₐ[Places.Oinf Fq] integralClosure (Places.Oinf Fq) F).toRingEquiv

@[simp] theorem coe_finEquiv (σ : F ≃ₐ[RatFunc Fq] F) (r : Places.Rfin Fq F) :
    ((finEquiv σ r : Places.Rfin Fq F) : F) = σ r := rfl

@[simp] theorem coe_infEquiv (σ : F ≃ₐ[RatFunc Fq] F) (r : Places.Rinf Fq F) :
    ((infEquiv σ r : Places.Rinf Fq F) : F) = σ r := rfl

/-- The permutation of the places induced by `σ`. -/
noncomputable def placeMap (σ : F ≃ₐ[RatFunc Fq] F) : Places.Place Fq F ≃ Places.Place Fq F :=
  Equiv.sumCongr (HeightOneSpectrum.equivOfRingEquiv (finEquiv σ))
    (HeightOneSpectrum.equivOfRingEquiv (infEquiv σ))

theorem ffv_placeMap (σ : F ≃ₐ[RatFunc Fq] F) (P : Places.Place Fq F) (f : F) :
    ffv Fq F (placeMap σ P) (σ f) = ffv Fq F P f := by
  rcases P with P | P
  · exact valuation_equiv (finEquiv σ) (σ : F →+* F) (fun r => rfl) P f
  · exact valuation_equiv (infEquiv σ) (σ : F →+* F) (fun r => rfl) P f

theorem deg_placeMap (σ : F ≃ₐ[RatFunc Fq] F) (P : Places.Place Fq F) :
    (placeMap σ P).deg = P.deg := by
  rcases P with P | P
  · exact deg_equiv Fq (finEquiv σ) P
  · exact deg_equiv Fq (infEquiv σ) P

/-- The twisted Stepanov bound for an automorphism `σ` of `F` over `RatFunc Fq`. -/
theorem twisted_stepanovF [DecidableEq (Places.Place Fq F)] (σ : F ≃ₐ[RatFunc Fq] F) (p : ℕ) [Fact p.Prime] [CharP F p]
    (k Q0 : ℕ) (hQ0def : Q0 = p ^ k) (P0 : Places.Place Fq F) (hP0 : P0.deg = ellF Fq F 0) (B : ℕ)
    (hB : ellF Fq F 0 * Q0 + 2 * genusF Fq F ≤ ellF Fq F 0 * B)
    (hQ0 : (genusF Fq F + ellF Fq F 0) ^ 2 < ellF Fq F 0 ^ 2 * Q0) (T : Finset (Places.Place Fq F))
    (hT : ∀ P ∈ T, P ≠ P0 → ∀ f : F, ffv Fq F P f ≤ 1 → ffv Fq F P (σ f - f ^ (Q0 ^ 2)) < 1) :
    Q0 * ∑ P ∈ T.erase P0, P.deg ≤ ellF Fq F 0 * (Q0 * (Q0 - 1) + Q0 ^ 2 * B) := by
  exact twisted_stepanov ffData_axioms p k Q0 hQ0def (σ : F →+* F) (placeMap σ)
    (fun P f => ffv_placeMap σ P f) (fun P => deg_placeMap σ P) P0 hP0 B hB hQ0 T hT

end FF

end RamanujanPetersson.ZetaSB


