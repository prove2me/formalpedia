-- Prove2me | solution 1 for APSCounting893.Main.scaled_odd_rational_bit_polynomial_time
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T20:39:01.451272+00:00
-- url     : https://prove2.me/submissions/f696413f-152f-41ca-8184-82bf38bcef12

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Fold
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Words
import Mathlib
import Mathlib.Data.ZMod.Basic
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0
set_option autoImplicit false
namespace APSCounting893.Main

/-- Binary repeated squaring keeps every running value reduced modulo max(2,p). -/
def modularPowerStep (p : ℕ) (state : ℕ × ℕ) (b : Bool) : ℕ × ℕ :=
  (if b then state.1*state.2%max 2 p else state.1%max 2 p,
    state.2*state.2%max 2 p)

def modularPower (a e p : ℕ) : ℕ :=
  (e.bits.foldl (modularPowerStep p) (1%max 2 p,a%max 2 p)).1

end APSCounting893.Main
end Component_0

section Component_1
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace APSCounting893.Main
open Turing.MultiTapeTM

lemma modularPowerStep_bound (p : ℕ) (z : ℕ × ℕ) (b : Bool) :
    (modularPowerStep p z b).1 < max 2 p ∧ (modularPowerStep p z b).2 < max 2 p := by
  have hp : 0 < max 2 p := lt_of_lt_of_le (by decide : 0<2) (le_max_left _ _)
  cases b <;> exact ⟨Nat.mod_lt _ hp,Nat.mod_lt _ hp⟩

lemma modularPowerFold_bound (p : ℕ) (w : List Bool) (z : ℕ × ℕ)
    (hz : z.1 < max 2 p ∧ z.2 < max 2 p) :
    (w.foldl (modularPowerStep p) z).1 < max 2 p ∧
      (w.foldl (modularPowerStep p) z).2 < max 2 p := by
  induction w generalizing z with
  | nil => exact hz
  | cons b w ih => exact ih _ (modularPowerStep_bound p z b)

lemma modularPowerFold_cast (p : ℕ) (w : List Bool) (z : ℕ × ℕ) :
    ((w.foldl (modularPowerStep p) z).1 : ZMod (max 2 p))=
      (z.1 : ZMod (max 2 p))*(z.2 : ZMod (max 2 p))^(ofBits w) := by
  induction w generalizing z with
  | nil => simp [ofBits]
  | cons b w ih =>
    rw [List.foldl_cons,ih]
    cases b with
    | false =>
      simp only [modularPowerStep,Bool.false_eq_true,ite_false,ofBits,List.foldr_cons,Nat.bit_false,
        ZMod.natCast_mod,Nat.cast_mul]
      rw [←pow_two,←pow_mul]
    | true =>
      simp only [modularPowerStep,ite_true,ofBits,List.foldr_cons,Nat.bit_true,
        ZMod.natCast_mod,Nat.cast_mul]
      rw [←pow_two,←pow_mul,pow_succ]
      ring

lemma modularPowerFold_value (p : ℕ) (w : List Bool) (z : ℕ × ℕ) :
    (w.foldl (modularPowerStep p) z).1 % max 2 p=
      (z.1*z.2^(ofBits w))%max 2 p := by
  have hh := modularPowerFold_cast p w z
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp (by simpa only [Nat.cast_mul,Nat.cast_pow] using hh)

lemma modularPower_eq_pow_mod (a e p : ℕ) : modularPower a e p=a^e%max 2 p := by
  have hp : 0 < max 2 p := lt_of_lt_of_le (by decide : 0<2) (le_max_left _ _)
  have hb := (modularPowerFold_bound p e.bits (1%max 2 p,a%max 2 p)
    ⟨Nat.mod_lt _ hp,Nat.mod_lt _ hp⟩).1
  change modularPower a e p < max 2 p at hb
  have hv : (modularPower a e p : ZMod (max 2 p))=(a : ZMod (max 2 p))^e := by
    simpa only [modularPower,ofBits,Nat.foldr_bit_bits,ZMod.natCast_mod,Nat.cast_one,one_mul]
      using modularPowerFold_cast p e.bits (1%max 2 p,a%max 2 p)
  have hh := (ZMod.natCast_eq_natCast_iff' (modularPower a e p) (a^e) (max 2 p)).mp
    (by simpa only [Nat.cast_pow] using hv)
  rwa [Nat.mod_eq_of_lt hb] at hh

end APSCounting893.Main
end Component_1

section Component_2
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace APSCounting893.Main

lemma odd_division_even_numerator_parity (x p : ℕ) (hp : Odd p) (hx : x%2=0) :
    (x/p)%2=(x%p)%2 := by
  have hpm : p%2=1 := Nat.odd_iff.mp hp
  have he := congrArg (fun n : ℕ => n%2) (Nat.mod_add_div x p)
  rw [Nat.add_mod,Nat.mul_mod,hpm,one_mul,hx] at he
  have hq := Nat.mod_lt (x/p) (by decide : 0<2)
  have hr := Nat.mod_lt (x%p) (by decide : 0<2)
  omega

lemma scaled_odd_rational_parity (a p s : ℕ) (hp : Odd p) (hs : 0 < s) :
    ((a*2^s)/p)%2=((a%p)*(modularPower 2 s p))%max 2 p%2 := by
  have hp0 : 0 < p := by obtain ⟨k,hk⟩ := hp;omega
  by_cases hp1 : p=1
  · subst p
    simp only [Nat.mod_one,zero_mul,Nat.zero_mod,Nat.div_one]
    have he : (a*2^s)%2=0 := by
      obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
      rw [pow_succ,←Nat.mul_assoc,Nat.mul_mod_left]
    exact he
  · have hP : max 2 p=p := max_eq_right (by omega)
    rw [hP,modularPower_eq_pow_mod,hP]
    rw [odd_division_even_numerator_parity _ p hp]
    · exact congrArg (fun n : ℕ => n%2) (Nat.mul_mod a (2^s) p)
    · obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
      rw [pow_succ,←Nat.mul_assoc,Nat.mul_mod_left]

end APSCounting893.Main
end Component_2

section Component_3
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace APSCounting893.Main

lemma scaled_rational_shift (a p H q : ℕ) (hq : q ≤ H) :
    (a*2^H/p)/2^q=a*2^(H-q)/p := by
  have he : 2^H=2^(H-q)*2^q := by rw [←pow_add,Nat.sub_add_cancel hq]
  rw [Nat.div_right_comm,he,←Nat.mul_assoc,Nat.mul_div_cancel _ (by positivity : 0<2^q)]

lemma scaled_odd_rational_bit (a p H q : ℕ) (hp : Odd p) (hq : q < H) :
    (a*2^H/p).testBit q =
      decide (((a%p)*modularPower 2 (H-q) p)%max 2 p%2=1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq,scaled_rational_shift a p H q hq.le,
    scaled_odd_rational_parity a p (H-q) hp (by omega)]

lemma scaled_rational_high_shift (a p H q : ℕ) (hq : H ≤ q) :
    (a*2^H/p)/2^q=(a/2^(q-H))/p := by
  have he : 2^q=2^H*2^(q-H) := by rw [←pow_add,Nat.add_sub_of_le hq]
  rw [Nat.div_right_comm,he,←Nat.div_div_eq_div_mul,Nat.mul_div_cancel _ (by positivity : 0<2^H)]

end APSCounting893.Main
end Component_3

section Component_4
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_power_modulus : ComputableTidilyInPolyTime (fun p : ℕ => max 2 p) encNat encNat := by
  have hi := id' (encIn:=encNat)
  have hc := binary_le' (const 2) hi
  have hh := ite_decide hc hi (const 2)
  apply hh.of_enc_eq
  intro p
  by_cases hp : 2 ≤ p
  · simp only [if_pos hp,max_eq_right hp]
  · simp only [if_neg hp,max_eq_left (by omega : p ≤ 2)]

lemma native_modularPowerStep : ComputableTidilyInPolyTime
    (fun q : (ℕ × (ℕ × ℕ)) × Bool => modularPowerStep q.1.1 q.1.2 q.2)
    (encPair (encPair encNat (encPair encNat encNat)) encBool) (encPair encNat encNat) := by
  have hi := id' (encIn:=encPair (encPair encNat (encPair encNat encNat)) encBool)
  have hp := native_power_modulus.comp hi.fst'.fst'
  have hs := hi.fst'.snd'.fst'
  have ht := hi.fst'.snd'.snd'
  have hyes := binary_mod' (binary_mul' hs ht) hp
  have hno := binary_mod' hs hp
  have hfirst := hi.snd'.cond hyes hno
  have hsecond := binary_mod' (binary_mul' ht ht) hp
  exact hfirst.prod hsecond

lemma power_modulus_bits (p : ℕ) : (max 2 p).bits.length ≤ p.bits.length+2 := by
  by_cases hp : 2 ≤ p
  · rw [max_eq_right hp];omega
  · rw [max_eq_left (by omega : p ≤ 2)]
    change 2 ≤ p.bits.length+2
    omega

lemma modularPowerStep_encoding_bound (p : ℕ) (z : ℕ × ℕ) (b : Bool) :
    (encPair encNat encNat (modularPowerStep p z b)).length ≤ 3*p.bits.length+7 := by
  have hz := modularPowerStep_bound p z b
  have hsize (v : ℕ) (hv : v < max 2 p) : v.bits.length ≤ p.bits.length+2 := by
    have hh : v.bits.length ≤ (max 2 p).bits.length := by
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.le_of_lt hv)
    exact hh.trans (power_modulus_bits p)
  have h1 := hsize _ hz.1
  have h2 := hsize _ hz.2
  simp only [length_encPair,encNat_apply]
  omega

lemma native_modularPower : ComputableTidilyInPolyTime
    (fun q : ℕ × (ℕ × ℕ) => modularPower q.2.1 q.2.2 q.1)
    (encPair encNat (encPair encNat encNat)) encNat := by
  let encI := encPair encNat (encPair encNat encNat)
  have hinput := id' (encIn:=encI)
  have hp := native_power_modulus.comp hinput.fst'
  have hinit := (binary_mod' (const 1) hp).prod (binary_mod' hinput.snd'.fst' hp)
  have hlist := natBits.comp hinput.snd'.snd'
  have hi := fst (encPair encI (encPair encNat encNat)) encBool
  have hb := snd (encPair encI (encPair encNat encNat)) encBool
  have hstep := native_modularPowerStep.comp ((hi.fst'.fst'.prod hi.snd').prod hb)
  have hfold : ComputableTidilyInPolyTime
      (fun q : ℕ × (ℕ × ℕ) => q.2.2.bits.foldl (modularPowerStep q.1)
        (1%max 2 q.1,q.2.1%max 2 q.1)) encI (encPair encNat encNat) := by
    apply foldlWithInput_of_bounded_growth (growth:=fun q : ℕ × (ℕ × ℕ) => 3*q.1.bits.length+7)
      hinit ⟨hlist,hstep,inferInstance,inferInstance⟩
    refine ⟨PolyBounded.of_forall_le 10 1 ?_,?_⟩
    · intro q
      have hp := length_le_encPair_left encNat (encPair encNat encNat) q
      simp only [encNat_apply] at hp
      simp only [pow_one]
      dsimp only [encI]
      omega
    · intro q z b _
      exact (modularPowerStep_encoding_bound q.1 z b).trans (Nat.le_add_left _ _)
  exact hfold.fst'

end APSCounting893.Main
end Component_4

section Component_5
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def scaledRationalBit (a p H q : ℕ) : Bool :=
  if q<H then decide (((a%p)*modularPower 2 (H-q) p)%max 2 p%2=1)
  else decide (((a >>> (q-H))/p)%2=1)

lemma scaledRationalBit_correct (a p H q : ℕ) (hp : Odd p) :
    scaledRationalBit a p H q=(a*2^H/p).testBit q := by
  unfold scaledRationalBit
  split_ifs with h
  · exact (scaled_odd_rational_bit a p H q hp h).symm
  · rw [Nat.testBit_eq_decide_div_mod_eq,scaled_rational_high_shift a p H q (by omega),Nat.shiftRight_eq_div_pow]

lemma native_scaledRationalBit : ComputableTidilyInPolyTime
    (fun x : ℕ × (ℕ × (ℕ × ℕ)) => scaledRationalBit x.1 x.2.1 x.2.2.1 x.2.2.2)
    (encPair encNat (encPair encNat (encPair encNat encNat))) encBool := by
  have hi := id' (encIn:=encPair encNat (encPair encNat (encPair encNat encNat)))
  have ha := hi.fst'
  have hp := hi.snd'.fst'
  have hH := hi.snd'.snd'.fst'
  have hq := hi.snd'.snd'.snd'
  have hcmp := binary_lt' hq hH
  have hpower := native_modularPower.comp (hp.prod ((const 2).prod (binary_sub' hH hq)))
  have hlowval := binary_mod' (binary_mod' (binary_mul' (binary_mod' ha hp) hpower)
    (native_power_modulus.comp hp)) (const 2)
  have hlow := decide_eq' hlowval (const 1)
  have hshift := (Turing.MultiTapeTM.ComputableInPolyTime.binary_shiftRight).tidy.comp
    (ha.prod (binary_sub' hq hH))
  have hhighval := binary_mod' (binary_div' hshift hp) (const 2)
  have hhigh := decide_eq' hhighval (const 1)
  have hh := ite_decide hcmp hlow hhigh
  exact hh.of_enc_eq (fun x => rfl)

end APSCounting893.Main
end Component_5

open APSCounting893.Main
theorem solution :
    ∃ f : ℕ × (ℕ × (ℕ × ℕ)) → Bool,
      Turing.MultiTapeTM.ComputableInPolyTime f
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encNat
          (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encNat
            (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encNat Turing.MultiTapeTM.encNat)))
        Turing.MultiTapeTM.encBool ∧
      ∀ a p H q : ℕ,Odd p → f (a,p,H,q)=(a*2^H/p).testBit q := by
  exact ⟨fun x => scaledRationalBit x.1 x.2.1 x.2.2.1 x.2.2.2,
    native_scaledRationalBit.computableInPolyTime,fun a p H q hp => scaledRationalBit_correct a p H q hp⟩
