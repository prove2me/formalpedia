-- Prove2me | Definitions.Def_Yukon_8aef1041375ab73b49f5291c
-- name    : Yukon_8aef1041375ab73b49f5291c
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:30:31.129309+00:00
-- url     : https://prove2.me/theorems/c0d0122b-6455-4c31-9a11-02fe426b4056
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberPairArithmetic6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberPairArithmetic6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberPairArithmetic6814.lean
--
--   yukon-proof-operation:foundation-direct-ff95e08ba8945f0d9dd828a9355ab8a5d005972e4b773882ec334232fd999ef8
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNGUxMmVlMGIzZDZjYWU4YzczNjRlMWZjNmM3MTIwM2NkYjQ0MDYxZTY5ZTYyZWVkYjI2YzViMTRmZDllMTljYyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWZmOTVlMDhiYTg5NDVmMGQ5ZGQ4MjhhOTM1NWFiOGE1ZDAwNTk3MmU0Yjc3Mzg4MmVjMzM0MjMyZmQ5OTllZjgiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl84YWVmMTA0MTM3NWFiNzNiNDlmNTI5MWMiLCJ2IjoyfQ]

import Definitions.Def_Yukon_0e3496485be9a551c983331b









































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Per-cell pair charge. The residual pair `(Q, T) = (QB/H, QA/H)` only has the
complement of the universal flag `(r, y, t)` of `H` left in the `B` and `TCap`
boxes, and its count needs only the carrier's (left) agreement caps. The
numerator is affine in `t`; `line` is the integer affine majorant that the
ledger runs check at their endpoints. -/
namespace ProximityPrize.SubmissionLower.PairCell6814
open RCN260 RCN294 AsymmetricHelper
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Left box `(185-y, 40-r, 35527-t)`, right box `(312-y, 70-r, 10715-t)`. -/
def parameters (r y t : ℕ) : UnequalParameters :=
  ⟨262144,131071,181255,185-y,40-r,35527-t,312-y,70-r,10715-t⟩

def cap (r y t : ℕ) : ℕ := leftRegularCountCap (parameters r y t)

def constant (r y : ℕ) : ℕ := leftRegularNumerator (parameters r y 0)

def slope (r y : ℕ) : ℕ :=
  131073*((1+2*131071*(185-y))*((40-r)+(70-r)) +
    131071*(2*(40-r)-1)*((185-y)+(312-y)) +
    2*131071*((185-y)*(70-r)+(40-r)*(312-y)))

theorem numerator_affine (r y t : ℕ) (ht : t ≤ 10715) :
    leftRegularNumerator (parameters r y t) + slope r y * t = constant r y := by
  have ht' : t ≤ 35527 := by omega
  simp only [constant, slope, parameters, leftRegularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.leftAgreement, UnequalParameters.mixedCost,
    dot, Nat.sub_zero]
  zify [ht, ht']
  ring

def line (r y t : ℕ) : ℤ :=
  ((constant r y / 50184 : ℕ) : ℤ) - ((slope r y / 50184 : ℕ) : ℤ) * (t : ℤ)

theorem cap_le_line (r y t : ℕ) (ht : t ≤ 10715) : (cap r y t : ℤ) ≤ line r y t := by
  have he := numerator_affine r y t ht
  have h1 := Nat.div_mul_le_self (leftRegularNumerator (parameters r y t)) 50184
  have h2 := Nat.div_add_mod (constant r y) 50184
  have h3 := Nat.mod_lt (constant r y) (show 0 < 50184 by norm_num)
  have h4 := Nat.mul_le_mul_right t (Nat.div_mul_le_self (slope r y) 50184)
  have hn : cap r y t + slope r y / 50184 * t ≤ constant r y / 50184 := by
    have hc : cap r y t = leftRegularNumerator (parameters r y t) / 50184 := by
      simp only [cap, leftRegularCountCap, parameters, UnequalParameters.gap]
    have h5 : slope r y / 50184 * 50184 * t = 50184 * (slope r y / 50184 * t) := by ring
    rw [h5] at h4
    rw [hc]
    generalize slope r y / 50184 * t = P at *
    generalize slope r y * t = S at *
    omega
  unfold line
  have hn' := (Nat.cast_le (α := ℤ)).mpr hn
  rw [Nat.cast_add, Nat.cast_mul] at hn'
  linarith

end ProximityPrize.SubmissionLower.PairCell6814


