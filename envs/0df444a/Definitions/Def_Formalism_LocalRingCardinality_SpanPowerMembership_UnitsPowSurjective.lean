-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_UnitsPowSurjective
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_UnitsPowSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:36:03.266648+00:00
-- url     : https://prove2.me/theorems/7ca7cec0-75cc-4888-bcb3-eb4f20ca2f15
-- title:
--   Units Pow Surjective
-- statement:
--   Definitions and structural lemmas for Units Pow Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/UnitsPowSurjective.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂
open Cardinal
section ToC
variable (p : ℕ) [Fact p.Prime]
theorem teich_charZero : CharZero (WittVector p (AlgebraicClosure (ZMod p))) := by
  let f : ℤ_[p] →+* WittVector p (AlgebraicClosure (ZMod p)) :=
    (WittVector.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).comp
      (WittVector.equiv p).symm.toRingHom
  have hf : Function.Injective f :=
    (WittVector.map_injective _ (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective).comp
      (WittVector.equiv p).symm.injective
  exact charZero_of_injective_ringHom hf
theorem teich_card_Fbar : #(AlgebraicClosure (ZMod p)) = ℵ₀ := by
  apply le_antisymm
  · refine (Algebra.IsAlgebraic.cardinalMk_le_max (ZMod p) (AlgebraicClosure (ZMod p))).trans ?_
    exact max_le (Cardinal.mk_le_aleph0) le_rfl
  · exact Cardinal.aleph0_le_mk _
def teichCoeffEquiv (R : Type) : WittVector p R ≃ (ℕ → R) where
  toFun x := x.coeff
  invFun f := WittVector.mk p f
  left_inv x := by ext n; rfl
  right_inv f := by funext n; rfl
theorem mk_wittVector : #(WittVector p (AlgebraicClosure (ZMod p))) = 𝔠 := by
  rw [Cardinal.mk_congr (teichCoeffEquiv p (AlgebraicClosure (ZMod p)))]
  simp [teich_card_Fbar]
abbrev TeichOm : Type :=
  AlgebraicClosure (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))
theorem teich_card_Om : #(TeichOm p) = 𝔠 := by
  have hK : #(FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) = 𝔠 := by
    rw [Cardinal.mk_fractionRing, mk_wittVector]
  apply le_antisymm
  · refine (Algebra.IsAlgebraic.cardinalMk_le_max
      (FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) (TeichOm p)).trans ?_
    rw [hK]
    exact max_le le_rfl Cardinal.aleph0_le_continuum
  · rw [← hK]
    exact Cardinal.mk_le_of_injective
      (algebraMap (FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) (TeichOm p)).injective
def teichWOm : WittVector p (AlgebraicClosure (ZMod p)) →+* TeichOm p :=
  (algebraMap (FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) (TeichOm p)).comp
    (algebraMap (WittVector p (AlgebraicClosure (ZMod p)))
      (FractionRing (WittVector p (AlgebraicClosure (ZMod p)))))
theorem teichWOm_injective : Function.Injective (teichWOm p) :=
  (algebraMap (FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) (TeichOm p)).injective.comp
    (IsFractionRing.injective (WittVector p (AlgebraicClosure (ZMod p)))
      (FractionRing (WittVector p (AlgebraicClosure (ZMod p)))))
theorem teich_Om_charZero : CharZero (TeichOm p) :=
  haveI := teich_charZero p
  charZero_of_injective_ringHom (teichWOm_injective p)
theorem teich_Om_equiv : Nonempty (TeichOm p ≃+* ℂ) := by
  have := teich_Om_charZero p
  apply IsAlgClosed.ringEquiv_of_equiv_of_charZero
  · rw [teich_card_Om]; exact Cardinal.aleph0_lt_continuum
  · apply Cardinal.eq.1
    rw [teich_card_Om, Cardinal.mk_complex]
def teichToC : AlgebraicClosure (ZMod p) →* ℂ :=
  (((teich_Om_equiv p).some.toRingHom.comp (teichWOm p) :
      WittVector p (AlgebraicClosure (ZMod p)) →+* ℂ) :
      WittVector p (AlgebraicClosure (ZMod p)) →* ℂ).comp (WittVector.teichmuller p)
theorem teichToC_injective : Function.Injective (teichToC p) := by
  intro x y h
  have h1 : WittVector.teichmuller p x = WittVector.teichmuller p y :=
    teichWOm_injective p ((teich_Om_equiv p).some.injective h)
  have h2 := congrArg (fun w => w.coeff 0) h1
  simpa [WittVector.teichmuller_coeff_zero] using h2
end ToC
section ExtZero
open Classical in

def extZeroHom {K L : Type*} [Field K] [Field L] (χ : Kˣ →* Lˣ) : K →* L where
  toFun x := if h : x = 0 then 0 else (χ (Units.mk0 x h) : L)
  map_one' := by
    have h1 : Units.mk0 (1 : K) one_ne_zero = 1 := by ext; rfl
    simp [h1]
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    have h1 : Units.mk0 (x * y) hxy = Units.mk0 x hx * Units.mk0 y hy := by ext; rfl
    simp [hx, hy, h1]
end ExtZero
section Iota
theorem units_pow_surjective (L : Type*) [Field L] [IsAlgClosed L] {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (fun a : Lˣ => a ^ n) := by
  intro u
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : L) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hz
    exact u.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, by ext; simpa using hz⟩
@[instance_reducible] def unitsDivisible (L : Type*) [Field L] [IsAlgClosed L] : DivisibleBy (Additive Lˣ) ℤ :=
  divisibleByOfSMulRightSurj (Additive Lˣ) ℤ (by
    intro n hn a
    obtain ⟨b, hb⟩ := units_pow_surjective L (n := n.natAbs) (Int.natAbs_ne_zero.2 hn) (Additive.toMul a)
    rcases Int.natAbs_eq n with h | h
    · refine ⟨Additive.ofMul b, ?_⟩
      show n • Additive.ofMul b = a
      rw [h, natCast_zsmul, ← ofMul_pow]
      exact congrArg Additive.ofMul hb
    · refine ⟨Additive.ofMul b⁻¹, ?_⟩
      show n • Additive.ofMul b⁻¹ = a
      rw [h, neg_zsmul, natCast_zsmul, ← ofMul_pow, inv_pow, ofMul_inv, neg_neg]
      exact congrArg Additive.ofMul hb)
variable (g l : ℕ) [Fact g.Prime] [Fact l.Prime]
def primeToSub : Subgroup (AlgebraicClosure (ZMod g))ˣ where
  carrier := {x | (orderOf x).Coprime l}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    exact Nat.Coprime.coprime_dvd_left ((Commute.all a b).orderOf_mul_dvd_lcm)
      (Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul _ _) (Nat.Coprime.mul_left ha hb))
  inv_mem' := by
    intro a ha
    simpa using ha
def teichU (p : ℕ) [Fact p.Prime] : (AlgebraicClosure (ZMod p))ˣ →* ℂˣ := Units.map (teichToC p)
theorem teichU_injective (p : ℕ) [Fact p.Prime] : Function.Injective (teichU p) :=
  Units.map_injective (teichToC_injective p)
theorem teichU_range {N : ℕ} (hN : N.Coprime l) (hN0 : N ≠ 0) (z : ℂˣ) (hz : z ^ N = 1) :
    z ∈ (teichU l).range := by
  have : NeZero N := ⟨hN0⟩
  have : NeZero (N : AlgebraicClosure (ZMod l)) := by
    refine ⟨fun h => ?_⟩
    have h2 : (l : ℕ) ∣ N := (CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod l)) l N).1 h
    have h3 : l ∣ Nat.gcd N l := Nat.dvd_gcd h2 dvd_rfl
    rw [hN] at h3
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h3)
  have hcard : Nat.card (rootsOfUnity N (AlgebraicClosure (ZMod l))) = N :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure (ZMod l)) N
  have hcardC : Nat.card (rootsOfUnity N ℂ) = N := Complex.card_rootsOfUnity N
  let r : rootsOfUnity N (AlgebraicClosure (ZMod l)) → rootsOfUnity N ℂ := fun y =>
    ⟨teichU l y.1, by
      rw [mem_rootsOfUnity, ← map_pow, (mem_rootsOfUnity _ _).1 y.2, map_one]⟩
  have hr : Function.Injective r := by
    intro a b hab
    exact Subtype.ext (teichU_injective l (congrArg Subtype.val hab))
  have : Finite (rootsOfUnity N ℂ) := Nat.finite_of_card_ne_zero (by rw [hcardC]; exact hN0)
  have : Finite (rootsOfUnity N (AlgebraicClosure (ZMod l))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN0)
  have hbij : Function.Bijective r :=
    (Nat.bijective_iff_injective_and_card r).2 ⟨hr, by rw [hcard, hcardC]⟩
  obtain ⟨y, hy⟩ := hbij.2 ⟨z, (mem_rootsOfUnity _ _).2 hz⟩
  exact ⟨y.1, congrArg Subtype.val hy⟩
def iotaSub : primeToSub g l →* (AlgebraicClosure (ZMod l))ˣ :=
  ((MonoidHom.ofInjective (teichU_injective l)).symm.toMonoidHom).comp
    (((teichU g).comp (primeToSub g l).subtype).codRestrict (teichU l).range (by
      intro x
      have hx : (orderOf x.1).Coprime l := x.2
      have h0 : orderOf x.1 ≠ 0 := by
        intro h
        rw [h, Nat.coprime_zero_left] at hx
        exact (Fact.out : l.Prime).one_lt.ne' hx
      refine teichU_range l hx h0 _ ?_
      show (teichU g x.1) ^ orderOf x.1 = 1
      rw [← map_pow, pow_orderOf_eq_one, map_one]))
theorem iotaU_exists : ∃ χ : (AlgebraicClosure (ZMod g))ˣ →* (AlgebraicClosure (ZMod l))ˣ,
    ∀ x : primeToSub g l, χ x.1 = iotaSub g l x := by
  let _ := unitsDivisible (AlgebraicClosure (ZMod l))
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive (AlgebraicClosure (ZMod l))ˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive (primeToSub g l).subtype)
    (fun a b hab => Subtype.ext (congrArg Additive.toMul hab : _))
    (MonoidHom.toAdditive (iotaSub g l))
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  have := DFunLike.congr_fun hh (Additive.ofMul x)
  exact congrArg Additive.toMul this
def teichIota : AlgebraicClosure (ZMod g) →* AlgebraicClosure (ZMod l) :=
  extZeroHom (iotaU_exists g l).choose
end Iota
end Formalism.BasicNotions.Examples₂


