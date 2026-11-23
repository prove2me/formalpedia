-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_MapEqPadicPowCyclotomicCharacter
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_MapEqPadicPowCyclotomicCharacter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:17:23.112886+00:00
-- url     : https://prove2.me/theorems/c6b8a64a-0d10-403b-8da0-aee04516d7b7
-- title:
--   Map Eq Padic Pow Cyclotomic Character
-- statement:
--   Definitions and structural lemmas for Map Eq Padic Pow Cyclotomic Character, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap


set_option autoImplicit false
noncomputable section
open Ideal
namespace Reformulated.AutPerF
universe u v
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
namespace Tilt
variable (p R) in

def seqEquiv : Perfection R p ≃* Tilt p R := Perfection.quotientMulEquiv p (span {(p : R)})
def seq (n : ℕ) : Tilt p R →* R :=
  (Perfection.coeffMonoidHom R p n).comp (seqEquiv p R).symm.toMonoidHom
def ofSeq (x : ℕ → R) (h : ∀ n, x (n + 1) ^ p = x n) : Tilt p R := seqEquiv p R ⟨x, h⟩
@[simp] theorem seq_ofSeq (x : ℕ → R) (h : ∀ n, x (n + 1) ^ p = x n) (n : ℕ) :
    seq n (ofSeq x h : Tilt p R) = x n := by
  exact congrArg (Perfection.coeffMonoidHom R p n) ((seqEquiv p R).symm_apply_apply ⟨x, h⟩)
theorem seq_zero (y : Tilt p R) : seq 0 y = PreTilt.untilt y :=
  Perfection.coeff_zero_symm_quotientMulEquiv y
@[simp] theorem untilt_ofSeq (x : ℕ → R) (h : ∀ n, x (n + 1) ^ p = x n) :
    PreTilt.untilt (ofSeq x h : Tilt p R) = x 0 := by
  rw [← seq_zero, seq_ofSeq]
theorem seq_succ_pow (y : Tilt p R) (n : ℕ) : seq (n + 1) y ^ p = seq n y :=
  Perfection.coeffMonoidHom_pow_p' ((seqEquiv p R).symm y) n
theorem seq_add_pow (y : Tilt p R) (m n : ℕ) : seq (m + n) y ^ p ^ n = seq m y :=
  Perfection.coeffMonoidHom_pow_p_pow' ((seqEquiv p R).symm y) m n
theorem seq_pow_self (y : Tilt p R) (n : ℕ) : seq n y ^ p ^ n = PreTilt.untilt y := by
  rw [← seq_zero, ← seq_add_pow y 0 n, zero_add]
theorem ext_seq {x y : Tilt p R} (h : ∀ n, seq n x = seq n y) : x = y :=
  (seqEquiv p R).symm.injective (Perfection.extMonoid h)
theorem seq_frobeniusEquiv_symm (y : Tilt p R) (n : ℕ) :
    seq n ((frobeniusEquiv (Tilt p R) p).symm y) = seq (n + 1) y := by
  conv_rhs => rw [← frobeniusEquiv_symm_pow_p (Tilt p R) p y, map_pow, seq_succ_pow]
end Tilt
namespace tateModule
open Tilt
theorem untilt_eq_one (η : tateModule p R) : PreTilt.untilt η.1 = 1 := η.2
theorem seq_pow_eq_one (η : tateModule p R) (n : ℕ) : seq n η.1 ^ p ^ n = 1 := by
  rw [seq_pow_self, untilt_eq_one]
theorem ext_seq {x y : tateModule p R} (h : ∀ n, seq n x.1 = seq n y.1) : x = y :=
  Subtype.ext (Tilt.ext_seq h)
theorem seq_pow_congr (η : tateModule p R) {n a b : ℕ} (h : (a : ZMod (p ^ n)) = b) :
    seq n η.1 ^ a = seq n η.1 ^ b :=
  pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff _ _ _).1 h) (seq_pow_eq_one η n)
omit [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] in
theorem cast_val_toZModPow (a : ℤ_[p]) (n : ℕ) :
    (((PadicInt.toZModPow n a).val : ℕ) : ZMod (p ^ n)) = PadicInt.toZModPow n a :=
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  ZMod.natCast_zmod_val _
def padicPow (η : tateModule p R) (a : ℤ_[p]) : tateModule p R :=
  ⟨ofSeq (fun n => seq n η.1 ^ (PadicInt.toZModPow n a).val) (fun n => by
    rw [← pow_mul, mul_comm, pow_mul, seq_succ_pow]
    apply seq_pow_congr
    haveI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    rw [cast_val_toZModPow, ZMod.natCast_val, PadicInt.cast_toZModPow _ _ n.le_succ]), by
    change PreTilt.untilt _ = 1
    rw [untilt_ofSeq, seq_zero, untilt_eq_one, one_pow]⟩
theorem seq_padicPow (η : tateModule p R) (a : ℤ_[p]) (n : ℕ) :
    seq n (padicPow η a).1 = seq n η.1 ^ (PadicInt.toZModPow n a).val := seq_ofSeq _ _ n
theorem seq_padicPow_of_eq (η : tateModule p R) {a : ℤ_[p]} {n m : ℕ}
    (h : PadicInt.toZModPow n a = m) : seq n (padicPow η a).1 = seq n η.1 ^ m := by
  rw [seq_padicPow]
  exact seq_pow_congr η (by rw [cast_val_toZModPow, h])
@[simp] theorem padicPow_natCast (η : tateModule p R) (m : ℕ) : padicPow η m = η ^ m :=
  ext_seq fun n => by
    rw [seq_padicPow_of_eq η (map_natCast _ m), SubmonoidClass.coe_pow, map_pow]
@[simp] theorem padicPow_zero (η : tateModule p R) : padicPow η 0 = 1 := by
  simpa using padicPow_natCast η 0
@[simp] theorem padicPow_one (η : tateModule p R) : padicPow η 1 = η := by
  simpa using padicPow_natCast η 1
theorem padicPow_add (η : tateModule p R) (a b : ℤ_[p]) :
    padicPow η (a + b) = padicPow η a * padicPow η b :=
  ext_seq fun n => by
    rw [Submonoid.coe_mul, map_mul, seq_padicPow η a, seq_padicPow η b, ← pow_add]
    apply seq_padicPow_of_eq
    rw [Nat.cast_add, cast_val_toZModPow, cast_val_toZModPow, map_add]
theorem padicPow_mul (η : tateModule p R) (a b : ℤ_[p]) :
    padicPow η (a * b) = padicPow (padicPow η a) b :=
  ext_seq fun n => by
    rw [seq_padicPow _ b, seq_padicPow η a, ← pow_mul]
    apply seq_padicPow_of_eq
    rw [Nat.cast_mul, cast_val_toZModPow, cast_val_toZModPow, map_mul]
theorem mul_padicPow (η η' : tateModule p R) (a : ℤ_[p]) :
    padicPow (η * η') a = padicPow η a * padicPow η' a :=
  ext_seq fun n => by
    simp only [Submonoid.coe_mul, map_mul, seq_padicPow, mul_pow]
@[simp] theorem one_padicPow (a : ℤ_[p]) : padicPow (1 : tateModule p R) a = 1 :=
  ext_seq fun n => by simp [seq_padicPow]
instance : CommGroup (tateModule p R) :=
  { (inferInstance : CommMonoid (tateModule p R)) with
    inv := fun η => padicPow η (-1)
    inv_mul_cancel := fun η => by
      conv_lhs => rw [← padicPow_one η, ← padicPow_mul, ← padicPow_add]
      simp }
instance : Module ℤ_[p] (Additive (tateModule p R)) where
  smul a η := Additive.ofMul (padicPow η.toMul a)
  one_smul η := padicPow_one _
  mul_smul a b η := by
    change Additive.ofMul (padicPow η.toMul (a * b)) = _
    rw [mul_comm, padicPow_mul]; rfl
  smul_zero a := one_padicPow a
  smul_add a η η' := mul_padicPow _ _ a
  add_smul a b η := padicPow_add _ a b
  zero_smul η := padicPow_zero _
end tateModule
open Tilt tateModule
theorem isPrimitive_iff (ε : tateModule p R) : IsPrimitive ε ↔ seq 1 ε.1 ≠ 1 := by
  rw [IsPrimitive, ← seq_zero, seq_frobeniusEquiv_symm]
theorem IsPrimitive.isPrimitiveRoot {ε : tateModule p R} (hε : IsPrimitive ε) (n : ℕ) :
    IsPrimitiveRoot (seq n ε.1) (p ^ n) := by
  rcases n with _ | n
  · rw [seq_zero, untilt_eq_one, pow_zero]; exact IsPrimitiveRoot.one
  · rw [← orderOf_eq_prime_pow (x := seq (n + 1) ε.1) _ (seq_pow_eq_one ε _)]
    · exact IsPrimitiveRoot.orderOf _
    · rw [add_comm, seq_add_pow]; exact (isPrimitive_iff ε).1 hε
theorem IsPrimitive.padicPow_injective {ε : tateModule p R} (hε : IsPrimitive ε) :
    Function.Injective (padicPow ε) := by
  intro a b h
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  apply ZMod.val_injective
  apply (hε.isPrimitiveRoot n).pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [← seq_padicPow, ← seq_padicPow, h]
section Domain
variable [IsDomain R]
theorem IsPrimitive.padicPow_surjective {ε : tateModule p R} (hε : IsPrimitive ε) :
    Function.Surjective (padicPow ε) := by
  intro η
  have h : ∀ n, ∃ i : ℕ, seq n ε.1 ^ i = seq n η.1 := fun n => by
    haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    obtain ⟨i, -, hi⟩ := (hε.isPrimitiveRoot n).eq_pow_of_pow_eq_one (seq_pow_eq_one η n)
    exact ⟨i, hi⟩
  choose i hi using h
  have hd : ∀ n, (p : ℤ) ^ n ∣ (i (n + 1) : ℤ) - i n := fun n => by
    have h1 : seq n ε.1 ^ i n = seq n ε.1 ^ i (n + 1) := by
      rw [hi, ← seq_succ_pow η.1, ← hi, ← seq_succ_pow ε.1 n, ← pow_mul, ← pow_mul, mul_comm]
    have hf : IsOfFinOrder (seq n ε.1) :=
      (hε.isPrimitiveRoot n).isOfFinOrder (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    rw [hf.pow_eq_pow_iff_modEq, ← (hε.isPrimitiveRoot n).eq_orderOf] at h1
    exact_mod_cast h1.dvd
  refine ⟨PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
    (fun n => (i n : ℤ)) p hd), tateModule.ext_seq fun n => ?_⟩
  rw [← hi]
  apply seq_padicPow_of_eq
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ _ hd]
  simp
def IsPrimitive.padicPowEquiv {ε : tateModule p R} (hε : IsPrimitive ε) :
    Multiplicative ℤ_[p] ≃* tateModule p R :=
  MulEquiv.ofBijective
    ({ toFun := fun a => padicPow ε a.toAdd
       map_one' := padicPow_zero ε
       map_mul' := fun a b => padicPow_add ε a.toAdd b.toAdd } :
      Multiplicative ℤ_[p] →* tateModule p R)
    ⟨fun _ _ h => hε.padicPow_injective h, fun η => hε.padicPow_surjective η⟩
@[simp] theorem IsPrimitive.padicPowEquiv_apply {ε : tateModule p R} (hε : IsPrimitive ε)
    (a : ℤ_[p]) : hε.padicPowEquiv (Multiplicative.ofAdd a) = padicPow ε a := rfl
def IsPrimitive.linearEquiv {ε : tateModule p R} (hε : IsPrimitive ε) :
    ℤ_[p] ≃ₗ[ℤ_[p]] Additive (tateModule p R) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[p] _ (Additive.ofMul ε))
    ⟨fun _ _ h => hε.padicPow_injective h, fun η => hε.padicPow_surjective η.toMul⟩
end Domain
section Good
variable [IsDomain R] [ValuationRing R] [IsAlgClosed (FractionRing R)]
omit [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] in
theorem exists_pow_eq (x : R) {n : ℕ} (hn : 0 < n) : ∃ y : R, y ^ n = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap R (FractionRing R) x) hn
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) hn
    (x := z) (by rw [hz]; exact isIntegral_algebraMap)
  exact ⟨y, IsFractionRing.injective R (FractionRing R) (by rw [map_pow, hz])⟩
theorem Tilt.seq_surjective (n : ℕ) : Function.Surjective (seq n : Tilt p R → R) := by
  have h0 : ∀ x : R, ∃ y : Tilt p R, seq 0 y = x := fun x => by
    choose r hr using fun z : R => exists_pow_eq z (Fact.out : p.Prime).pos
    exact ⟨ofSeq (fun n => r^[n] x) (fun n => by rw [Function.iterate_succ_apply', hr]),
      seq_ofSeq _ _ 0⟩
  intro x
  obtain ⟨y, hy⟩ := h0 x
  exact ⟨y ^ p ^ n, by rw [map_pow, ← hy, ← seq_add_pow y 0 n, zero_add]⟩
theorem Tilt.untilt_surjective_of_isAlgClosed : Function.Surjective (PreTilt.untilt : Tilt p R → R) := fun x => by
  obtain ⟨y, hy⟩ := Tilt.seq_surjective (p := p) 0 x
  exact ⟨y, by rw [← seq_zero, hy]⟩
instance : Nonempty (PFlat p R) :=
  let ⟨y, hy⟩ := Tilt.untilt_surjective_of_isAlgClosed (p := p) (p : R)
  ⟨⟨y, hy⟩⟩
variable (p R) in

def pflat : PFlat p R := Classical.arbitrary _
variable [CharZero R]
variable (p R) in
theorem exists_isPrimitive : ∃ ε : tateModule p R, IsPrimitive ε := by
  haveI : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  haveI : NeZero (p : FractionRing R) := ⟨by exact_mod_cast (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (FractionRing R) p
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R)
    (Fact.out : p.Prime).pos (x := ζ) (by rw [hζ.pow_eq_one]; exact isIntegral_one)
  have hz := hζ.of_map_of_injective (IsFractionRing.injective R (FractionRing R))
  obtain ⟨y, hy⟩ := Tilt.seq_surjective (p := p) 1 z
  refine ⟨⟨y, ?_⟩, ?_⟩
  · change PreTilt.untilt y = 1
    rw [← seq_zero, ← seq_succ_pow, zero_add, hy, hz.pow_eq_one]
  · rw [isPrimitive_iff]
    change seq 1 y ≠ 1
    rw [hy]
    exact hz.ne_one (Fact.out : p.Prime).one_lt
variable (p R) in

def eps : tateModule p R := (exists_isPrimitive p R).choose
end Good
namespace PFlat
theorem ext {ϖ ϖ' : PFlat p R} (h : ϖ.1 = ϖ'.1) : ϖ = ϖ' := Subtype.ext h
@[simp] theorem twist_val (η : tateModule p R) (ϖ : PFlat p R) : (ϖ.twist η).1 = η.1 * ϖ.1 := rfl
@[simp] theorem twist_one (ϖ : PFlat p R) : ϖ.twist 1 = ϖ := ext (one_mul _)
theorem seq_pow (ϖ : PFlat p R) (n : ℕ) : seq n ϖ.1 ^ p ^ n = (p : R) := by
  rw [seq_pow_self, ϖ.2]
variable [IsDomain R] [CharZero R]
theorem seq_ne_zero (ϖ : PFlat p R) (n : ℕ) : seq n ϖ.1 ≠ 0 := fun h => by
  have := seq_pow ϖ n
  rw [h, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)] at this
  exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this.symm)
variable [ValuationRing R]
theorem twist_surjective (ϖ : PFlat p R) : Function.Surjective fun η => ϖ.twist η := by
  intro ϖ'
  have hd : ∀ n, seq n ϖ.1 ∣ seq n ϖ'.1 := fun n => by
    rw [← IsIntegrallyClosed.pow_dvd_pow_iff (pow_ne_zero n (Fact.out : p.Prime).ne_zero),
      seq_pow, seq_pow]
  choose c hc using hd
  have hp : ∀ n, c (n + 1) ^ p = c n := fun n => by
    apply mul_left_cancel₀ (seq_ne_zero ϖ n)
    rw [← hc, ← seq_succ_pow ϖ.1, ← mul_pow, ← hc, seq_succ_pow]
  refine ⟨⟨ofSeq c hp, ?_⟩, ext (Tilt.ext_seq fun n => ?_)⟩
  · change PreTilt.untilt _ = 1
    rw [untilt_ofSeq]
    apply mul_left_cancel₀ (seq_ne_zero ϖ 0)
    rw [← hc, mul_one, seq_zero, seq_zero, ϖ.2, ϖ'.2]
  · change seq n (ofSeq c hp * ϖ.1) = _
    rw [map_mul, seq_ofSeq, hc, mul_comm]
def div (ϖ' ϖ : PFlat p R) : tateModule p R := (twist_surjective ϖ ϖ').choose
end PFlat
end Reformulated.AutPerF


