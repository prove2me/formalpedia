-- Prove2me | Definitions.Def_Yukon_34c6baedbec234911ae26a26
-- name    : Yukon_34c6baedbec234911ae26a26
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:30:36.509582+00:00
-- url     : https://prove2.me/theorems/d90f4d41-fddb-495a-b0a2-ebfa4f7f9ca7
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberCountingArithmetic6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberCountingArithmetic6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberCountingArithmetic6814.lean
--
--   yukon-proof-operation:foundation-direct-a44e15cfe1ef07566920e55909bcf0344059aa77faadea30bffd472c66375d53
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZDVmZDg0YWM0NDE5ZTA1YzRkYmMwNWZlMGE3NTc0ZDEwNzcyNzQxNjRiMDRlMGM3MTlhZjlkZTVmMWQzZmIxZSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWE0NGUxNWNmZTFlZjA3NTY2OTIwZTU1OTA5YmNmMDM0NDA1OWFhNzdmYWFkZWEzMGJmZmQ0NzJjNjYzNzVkNTMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8zNGM2YmFlZGJlYzIzNDkxMWFlMjZhMjYiLCJ2IjoyfQ]

import Definitions.Def_Yukon_8bce6c5c34a90d671d777e22

import Definitions.Def_Yukon_0e3496485be9a551c983331b









































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.AsymmetricChainPolynomial80889
open scoped BigOperators
open RCN238 RCN223 RCN260 RCN313 RCN294 BoundaryTailChainHelper AsymmetricHelper
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def stage (y z d j : ℕ) : UnequalParameters :=
  ⟨262144,131071,181255,y,d-j,z,y,d,z⟩

def charge (y z d : ℕ) : ℕ :=
  (∑ j ∈ Finset.Ico 1 d, leftRegularCountCap (stage y z d j)) + 9000000000000

def kTerm (y z : ℕ) : ℕ :=
  131073 * (z + y + 524284*y*z) + 50184*80890*y
def mTerm (y z : ℕ) : ℕ := 131073*131071*y*z

theorem stageNumerator (y z d j : ℕ) (hj : j ≤ d) :
    leftRegularNumerator (stage y z d j) =
      (2*d-j)*kTerm y z + (2*(d-j)-1)*2*mTerm y z := by
  simp only [stage, leftRegularNumerator, UnequalParameters.gap,
    UnequalParameters.errors, UnequalParameters.leftAgreement,
    UnequalParameters.mixedCost, dot]
  norm_num only
  have hsub : (d-j)+d = 2*d-j := by omega
  dsimp [kTerm, mTerm]
  calc
    _ = ((d-j)+d) * (131073*(z+y+524284*y*z)+50184*80890*y) +
        (2*(d-j)-1)*2*(131073*131071*y*z) := by ring
    _ = _ := by rw [hsub]

def numerator (y z d : ℕ) : ℕ :=
  (d-1)*(3*d*kTerm y z + 4*mTerm y z*(d-1)) + 2*50184*9000000000000

theorem sum_stage_numerators (y z d : ℕ) (hd : d ≤ 40) :
    2 * (∑ j ∈ Finset.Ico 1 d, leftRegularNumerator (stage y z d j)) =
      (d-1)*(3*d*kTerm y z + 4*mTerm y z*(d-1)) := by
  have heq : (∑ j ∈ Finset.Ico 1 d, leftRegularNumerator (stage y z d j)) =
      ∑ j ∈ Finset.Ico 1 d, ((2*d-j)*kTerm y z + (2*(d-j)-1)*(2*mTerm y z)) := by
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [Nat.mul_assoc] using stageNumerator y z d j (Finset.mem_Ico.mp hj).2.le
  have hsum : 2 * (∑ j ∈ Finset.Ico 1 d, (2*d-j)) = 3*d*(d-1) := by
    interval_cases d <;> decide +kernel
  have hsum' : (∑ j ∈ Finset.Ico 1 d, (2*(d-j)-1)) = (d-1)*(d-1) := by
    interval_cases d <;> decide +kernel
  rw [heq, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hsum']
  nlinarith only [congrArg (fun x => x * kTerm y z) hsum]

theorem charge_mul_le (y z d : ℕ) (hd : d ≤ 40) :
    charge y z d * (2*50184) ≤ numerator y z d := by
  have hsum : (∑ j ∈ Finset.Ico 1 d, leftRegularCountCap (stage y z d j))*50184 ≤
      ∑ j ∈ Finset.Ico 1 d, leftRegularNumerator (stage y z d j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    simp only [leftRegularCountCap, UnequalParameters.gap, stage,
      (show (181255 - 131071 : ℕ) = 50184 by decide +kernel)]
    exact Nat.div_mul_le_self _ _
  have heq := sum_stage_numerators y z d hd
  dsimp [charge, numerator]
  nlinarith


/-- Endpoint domination for a convex quadratic after division by its positive index. -/
theorem quadratic_between (A C W r d : ℤ)
    (hA : 0 ≤ A) (hd : 1 ≤ d) (hdr : d ≤ r)
    (h1 : A + C ≤ W) (hr : A*r*r+C ≤ W*r) :
    A*d*d+C ≤ W*d := by
  by_cases hreq : r = 1
  · have hdeq : d = 1 := by omega
    simpa [hdeq] using h1
  have hr1 : 0 < r-1 := by omega
  have hp := mul_le_mul_of_nonneg_right h1 (show 0 ≤ r-d by omega)
  have hq := mul_le_mul_of_nonneg_right hr (show 0 ≤ d-1 by omega)
  have hc : 0 ≤ A*(r-1)*(d-1)*(r-d) :=
    mul_nonneg (mul_nonneg (mul_nonneg hA (by omega)) (by omega)) (by omega)
  have hm : (r-1)*(A*d*d+C) ≤ (r-1)*(W*d) := by nlinarith
  exact (mul_le_mul_iff_right₀ hr1).mp hm

theorem numerator_identity (y z d : ℕ) (hd : 1 ≤ d) :
    (numerator y z d : ℤ) + d*(3*(kTerm y z : ℤ)+8*(mTerm y z : ℤ)) =
      (3*(kTerm y z : ℤ)+4*(mTerm y z : ℤ))*d*d +
        4*(mTerm y z : ℤ)+2*50184*9000000000000 := by
  unfold numerator
  have h2 : 1 ≤ 2*d := by omega
  push_cast [Nat.cast_sub hd, Nat.cast_sub h2]
  ring

theorem charge_le_of_endpoints (y z d r u : ℕ)
    (hd : 1 ≤ d) (hdr : d ≤ r) (hr : r ≤ 40)
    (htail : 9000000000000 ≤ u)
    (hend : numerator y z r ≤ r*(2*50184)*u) :
    charge y z d ≤ d*u := by
  have hn1 := numerator_identity y z 1 (by decide +kernel)
  have hnr := numerator_identity y z r (by omega)
  have hnd := numerator_identity y z d hd
  have he : (numerator y z d : ℤ) ≤ d*(2*50184)*(u : ℤ) := by
    have htc : (9000000000000 : ℤ) ≤ u := by exact_mod_cast htail
    have hec : (numerator y z r : ℤ) ≤ r*(2*50184)*(u : ℤ) := by exact_mod_cast hend
    have h := quadratic_between
      (3*(kTerm y z : ℤ)+4*(mTerm y z : ℤ))
      (4*(mTerm y z : ℤ)+2*50184*9000000000000)
      ((2*50184)*(u : ℤ)+3*(kTerm y z : ℤ)+8*(mTerm y z : ℤ))
      r d (by positivity) (by exact_mod_cast hd) (by exact_mod_cast hdr)
      (by nlinarith) (by nlinarith)
    nlinarith
  have hn : numerator y z d ≤ d*(2*50184)*u := by exact_mod_cast he
  have hcharge := (charge_mul_le y z d (hdr.trans hr)).trans hn
  nlinarith


def zCoeff (y d : ℕ) : ℕ :=
  (d-1)*(3*d*131073*(1+524284*y)+4*131073*131071*y*(d-1))
def constant (y d : ℕ) : ℕ :=
  (d-1)*3*d*(131073+50184*80890)*y + 2*50184*9000000000000

theorem numerator_linear (y z d : ℕ) :
    numerator y z d = zCoeff y d*z + constant y d := by
  unfold numerator kTerm mTerm zCoeff constant
  ring

def unitSlope (y d : ℕ) : ℕ := zCoeff y d / (2*50184*d) + 1
def unitConstant (y d : ℕ) : ℕ := constant y d / (2*50184*d) + 1
def unit (y z d : ℕ) : ℕ :=
  max 9000000000000 (unitSlope y d*z + unitConstant y d)

public theorem le_roundUp_mul (a b : ℕ) (hb : 0 < b) : a ≤ (a/b+1)*b := by
  have hm := Nat.mod_lt a hb
  have he := Nat.mod_add_div a b
  nlinarith

theorem unit_end (y z r : ℕ) (hr : 1 ≤ r) :
    numerator y z r ≤ r*(2*50184)*unit y z r := by
  have hb : 0 < 2*50184*r := by omega
  have ha := le_roundUp_mul (zCoeff y r) (2*50184*r) hb
  have hc := le_roundUp_mul (constant y r) (2*50184*r) hb
  have ham := Nat.mul_le_mul_right z ha
  have hmax : unitSlope y r*z + unitConstant y r ≤ unit y z r := le_max_right _ _
  rw [numerator_linear]
  change zCoeff y r*z + constant y r ≤ _
  dsimp [unitSlope, unitConstant] at hmax
  norm_num only [Nat.reduceMul] at ha hc ham ⊢
  nlinarith [Nat.mul_le_mul_left (100466*r) hmax]

theorem charge_le_unit (y z d r : ℕ) (hd : 1 ≤ d) (hdr : d ≤ r) (hr : r ≤ 40) :
    charge y z d ≤ d*unit y z r :=
  charge_le_of_endpoints y z d r (unit y z r) hd hdr hr
    (le_max_left _ _) (unit_end y z r (by omega))

end ProximityPrize.SubmissionLower.AsymmetricChainPolynomial80889


