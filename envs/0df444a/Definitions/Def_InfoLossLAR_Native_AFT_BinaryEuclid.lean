-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_BinaryEuclid
-- name    : InfoLossLAR_Native_AFT_BinaryEuclid
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:08:55.657763+00:00
-- url     : https://prove2.me/theorems/847b4a60-7a65-4721-9734-9127c79a7512
-- title:
--   Normalized binary remainders and bounded Euclidean iteration
-- statement:
--   The remainder operation composes binary long division with normalization. A Euclidean routine iterates two remainder steps per round with an explicit finite fuel parameter, and the complete gcd routine chooses fuel from the supplied bit length. Its decoded output is
--
--   $$v(\operatorname{gcd}(a,b))=\gcd(v(a),v(b)).$$
--
--   The accompanying remainder identities relate the digit computation to natural-number Euclidean arithmetic.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/BinaryEuclid.lean; migrated native SHA256 f2b5cd61f49c972cdeacf5c09e583aecc496d37c79d424a492a703bec2e2df66; retained source units selected by Lean oracle.

import Definitions.Def_InfoLossLAR_Native_AFT_BinaryDivision
import Definitions.Def_InfoLossLAR_Native_AFT_BinaryNormalization
import Mathlib



/-! A binary implementation of Euclid with an explicit linear-in-bitlength
iteration bound. Each iteration performs two long divisions, which halves
the second nonzero operand. -/
namespace AFT.BinaryArithmetic

def remainder (as bs : List Bool) : Result :=
  let division := divide as bs
  let normal := normalize division.remainder
  ⟨normal.digits,division.work+normal.work⟩

theorem remainder_value (as bs : List Bool) (hb : 0 < value bs) :
    value (remainder as bs).digits=value as%value bs := by
  exact (normalize_value _).trans (divide_value as bs hb).2







def gcdAux : ℕ → List Bool → List Bool → Result
  | 0,as,_ => ⟨as,2⟩
  | fuel+1,as,bs =>
    match bs with
    | [] => ⟨as,2⟩
    | _::_ =>
      let first := remainder as bs
      match first.digits with
      | [] => ⟨bs,first.work+3⟩
      | _::_ =>
        let second := remainder bs first.digits
        let rest := gcdAux fuel first.digits second.digits
        ⟨rest.digits,first.work+second.work+rest.work+4⟩

theorem second_remainder_half {first second : ℕ} (hs : 0 < second) (hlt : second < first) :
    2*(first%second) < first := by
  by_cases hh : 2*second ≤ first
  · have hm := Nat.mod_lt first hs
    omega
  · rw [Nat.mod_eq_sub_mod hlt.le,Nat.mod_eq_of_lt (by omega : first-second < second)]
    omega

/-- Euclid's two-step invariant; the fuel is logarithmic, never an operand
value used as a unary iteration budget. -/
theorem gcdAux_value (fuel : ℕ) (as bs : List Bool)
    (hbn : bs.length=(value bs).size) (hsmall : value bs < 2^fuel) :
    value (gcdAux fuel as bs).digits=Nat.gcd (value as) (value bs) := by
  induction fuel generalizing as bs with
  | zero =>
    have hb : value bs=0 := by simpa using hsmall
    simp [gcdAux,hb]
  | succ fuel ih =>
    cases bs with
    | nil => simp [gcdAux,value]
    | cons b tail =>
      have hb : 0 < value (b::tail) := by
        by_contra hn
        have hz : value (b::tail)=0 := by omega
        simp [hz] at hbn
      have hfirst := remainder_value as (b::tail) hb
      have hfirstn : (remainder as (b::tail)).digits.length=(value (remainder as (b::tail)).digits).size := by
        exact (normalize_length _).trans (congrArg Nat.size (normalize_value _)).symm
      simp only [gcdAux]
      split <;> rename_i he
      · have hz : value as%value (b::tail)=0 := by rw [he,value] at hfirst;omega
        rw [Nat.gcd_comm,Nat.gcd_rec,hz,Nat.gcd_zero_left]
      · have hf : 0 < value (remainder as (b::tail)).digits := by
          by_contra hn
          have hz : value (remainder as (b::tail)).digits=0 := by omega
          rw [hz,Nat.size_zero,he] at hfirstn
          simp at hfirstn
        have hsecond := remainder_value (b::tail) (remainder as (b::tail)).digits hf
        have hn : (remainder (b::tail) (remainder as (b::tail)).digits).digits.length=
            (value (remainder (b::tail) (remainder as (b::tail)).digits).digits).size := by
          exact (normalize_length _).trans (congrArg Nat.size (normalize_value _)).symm
        have hhalf := second_remainder_half hf (by rw [hfirst];exact Nat.mod_lt _ hb)
        have hbound : value (remainder (b::tail) (remainder as (b::tail)).digits).digits < 2^fuel := by
          rw [hsecond]
          rw [pow_succ] at hsmall
          omega
        have hi := ih (remainder as (b::tail)).digits (remainder (b::tail) (remainder as (b::tail)).digits).digits hn hbound
        rw [hi,hfirst,hsecond,hfirst]
        calc
          _ = Nat.gcd (value (b::tail)%(value as%value (b::tail))) (value as%value (b::tail)) := Nat.gcd_comm ..
          _ = Nat.gcd (value as%value (b::tail)) (value (b::tail)) := (Nat.gcd_rec _ _).symm
          _ = Nat.gcd (value (b::tail)) (value as) := (Nat.gcd_rec _ _).symm
          _ = _ := Nat.gcd_comm ..



/-- This code uses the input-list length as its logarithmic fuel bound. -/
def gcd (as bs : List Bool) : Result :=
  let na := normalize as
  let nb := normalize bs
  let result := gcdAux (bs.length+1) na.digits nb.digits
  ⟨result.digits,na.work+nb.work+result.work+bs.length+1⟩

theorem gcd_value (as bs : List Bool) : value (gcd as bs).digits=Nat.gcd (value as) (value bs) := by
  have hn : (normalize bs).digits.length=(value (normalize bs).digits).size := by
    rw [normalize_length,normalize_value]
  have hv : value (normalize bs).digits < 2^(bs.length+1) := by
    rw [normalize_value]
    exact (value_lt bs).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  simpa only [gcd,normalize_value] using gcdAux_value (bs.length+1) (normalize as).digits (normalize bs).digits hn hv



end AFT.BinaryArithmetic


