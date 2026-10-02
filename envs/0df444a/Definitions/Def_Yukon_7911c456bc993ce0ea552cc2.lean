-- Prove2me | Definitions.Def_Yukon_7911c456bc993ce0ea552cc2
-- name    : Yukon_7911c456bc993ce0ea552cc2
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:50:50.285831+00:00
-- url     : https://prove2.me/theorems/f8bf0e03-7409-4575-b1dc-f71394a76e5a
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.FoldChainArithmetic6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.FoldChainArithmetic6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/FoldChainArithmetic6814.lean
--
--   yukon-proof-operation:foundation-direct-beeeba6dd1de6d6d06b658056dccbca4e4e464d7aebc754956f04f1bd288b42d
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYjU1ZWE2Mjc2MmM4ZjFkMmQ3M2Y2NjlkOWRlNmQ5YjBmN2M2MzM3YzJkNTk0MTkzMWVkMWViNThkOGYwMjE1ZCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWJlZWViYTZkZDFkZTZkNmQwNmI2NTgwNTZkY2NiY2E0ZTRlNDY0ZDdhZWJjNzU0OTU2ZjA0ZjFiZDI4OGI0MmQiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl83OTExYzQ1NmJjOTkzY2UwZWE1NTJjYzIiLCJ2IjoyfQ]

import Definitions.Def_Yukon_34c6baedbec234911ae26a26









































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Arithmetic of the fold-chain charge. A factor of `R`-degree `d ≥ 2` is
charged `|foldSeeds| + |tailSeeds|`, and `gap` times that is at most
`foldNumerator y z d`: the first derivative stage, the jump seeds and the tail.
This numerator is affine in `d`, so its two endpoints `d = 2` and `d = r` bound
every intermediate `d` after division by `d`. -/

namespace ProximityPrize.SubmissionLower.FoldChainPolynomial6814
open scoped BigOperators
open RCN238 RCN223 RCN260 RCN313 RCN294 BoundaryTailChainHelper AsymmetricHelper
  AsymmetricChainPolynomial80889
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The carrier box against the first-stage mixed cost: the zero-point cost of
the jump seeds. -/
theorem stageDot (y z d : ℕ) (hd : 1 ≤ d) :
    dot ⟨y, d-1, z⟩ (stage y z d 1).mixedCost = y*z*(6*d-4) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e+1 := ⟨d-1, by omega⟩
  simp only [stage, dot, UnequalParameters.mixedCost, Nat.add_sub_cancel]
  rw [show 6*(e+1)-4 = 6*e+2 by omega]
  ring

def foldNumerator (y z d : ℕ) : ℕ :=
  leftRegularNumerator (stage y z d 1) + 50184*(y*z*(6*d-4)) + 50184*9000000000000

theorem foldNumerator_int (y z d : ℕ) (hd : 2 ≤ d) :
    (foldNumerator y z d : ℤ) =
      (2*(kTerm y z : ℤ)+4*(mTerm y z : ℤ)+6*50184*(y : ℤ)*z)*d +
        (50184*9000000000000-(kTerm y z : ℤ)-6*(mTerm y z : ℤ)-4*50184*(y : ℤ)*z) := by
  unfold foldNumerator
  rw [stageNumerator y z d 1 (by omega)]
  have e1 : ((2*d-1 : ℕ) : ℤ) = 2*(d : ℤ)-1 := by omega
  have e2 : ((2*(d-1)-1 : ℕ) : ℤ) = 2*(d : ℤ)-3 := by omega
  have e3 : ((6*d-4 : ℕ) : ℤ) = 6*(d : ℤ)-4 := by omega
  push_cast [e1, e2, e3]
  ring

/-- Affine interpolation between the endpoints `d = 2` and `d = r`. -/
theorem foldNumerator_between (y z d r u : ℕ) (hd : 2 ≤ d) (hdr : d ≤ r)
    (h2 : foldNumerator y z 2 ≤ 2*50184*u) (hr : foldNumerator y z r ≤ r*50184*u) :
    foldNumerator y z d ≤ d*50184*u := by
  by_cases hr2 : r = 2
  · have hd2 : d = 2 := by omega
    subst hd2
    exact h2
  have hk2 := foldNumerator_int y z 2 le_rfl
  have hkr := foldNumerator_int y z r (by omega)
  have hkd := foldNumerator_int y z d hd
  have h2' : (foldNumerator y z 2 : ℤ) ≤ 2*50184*(u : ℤ) := by exact_mod_cast h2
  have hr' : (foldNumerator y z r : ℤ) ≤ (r : ℤ)*50184*(u : ℤ) := by exact_mod_cast hr
  have hid : ((r : ℤ)-2)*((foldNumerator y z d : ℤ)-(d : ℤ)*50184*u) =
      ((r : ℤ)-d)*((foldNumerator y z 2 : ℤ)-2*50184*u) +
        ((d : ℤ)-2)*((foldNumerator y z r : ℤ)-(r : ℤ)*50184*u) := by
    rw [hk2, hkr, hkd]
    push_cast
    ring
  have hA := mul_nonpos_of_nonneg_of_nonpos (show (0 : ℤ) ≤ (r : ℤ)-d by omega)
    (show (foldNumerator y z 2 : ℤ)-2*50184*u ≤ 0 by linarith)
  have hB := mul_nonpos_of_nonneg_of_nonpos (show (0 : ℤ) ≤ (d : ℤ)-2 by omega)
    (show (foldNumerator y z r : ℤ)-(r : ℤ)*50184*u ≤ 0 by linarith)
  have hprod : ((r : ℤ)-2)*((foldNumerator y z d : ℤ)-(d : ℤ)*50184*u) ≤ 0 := by
    rw [hid]
    linarith
  have hpos : (0 : ℤ) < (r : ℤ)-2 := by omega
  have hle : (foldNumerator y z d : ℤ)-(d : ℤ)*50184*u ≤ 0 := by
    by_contra hc
    have := mul_pos hpos (lt_of_not_ge hc)
    linarith
  have hfin : (foldNumerator y z d : ℤ) ≤ (d : ℤ)*50184*u := by linarith
  exact_mod_cast hfin

def foldZCoeff (y d : ℕ) : ℕ :=
  (2*d-1)*131073*(1+524284*y) + (2*d-3)*2*131073*131071*y + 50184*y*(6*d-4)
def foldConstant (y d : ℕ) : ℕ :=
  (2*d-1)*(131073+50184*80890)*y + 50184*9000000000000

theorem foldNumerator_linear (y z d : ℕ) (hd : 1 ≤ d) :
    foldNumerator y z d = foldZCoeff y d*z + foldConstant y d := by
  unfold foldNumerator
  rw [stageNumerator y z d 1 hd, show 2*(d-1)-1 = 2*d-3 by omega]
  unfold kTerm mTerm foldZCoeff foldConstant
  ring

def foldSlope (y d : ℕ) : ℕ := foldZCoeff y d / (50184*d) + 1
def foldConst (y d : ℕ) : ℕ := foldConstant y d / (50184*d) + 1
def foldPiece (y z d : ℕ) : ℕ := foldSlope y d*z + foldConst y d

/-- Per-unit fold-chain charge for factors of `R`-degree at most `r`. -/
def foldUnit (y z r : ℕ) : ℕ :=
  if r < 2 then 9000000000000 else
    max 9000000000000 (max (foldPiece y z 2) (foldPiece y z r))

public theorem le_roundUp_mul (a b : ℕ) (hb : 0 < b) : a ≤ (a/b+1)*b := by
  have hm := Nat.mod_lt a hb
  have he := Nat.mod_add_div a b
  nlinarith

theorem foldPiece_end (y z d : ℕ) (hd : 1 ≤ d) :
    foldNumerator y z d ≤ d*50184*foldPiece y z d := by
  have hb : 0 < 50184*d := by omega
  have ha := le_roundUp_mul (foldZCoeff y d) (50184*d) hb
  have hc := le_roundUp_mul (foldConstant y d) (50184*d) hb
  have ham := Nat.mul_le_mul_right z ha
  rw [foldNumerator_linear y z d hd]
  unfold foldPiece foldSlope foldConst
  nlinarith

theorem tail_le_foldUnit (y z r : ℕ) : 9000000000000 ≤ foldUnit y z r := by
  unfold foldUnit
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

theorem foldNumerator_le_unit (y z d r : ℕ) (hd : 2 ≤ d) (hdr : d ≤ r) :
    foldNumerator y z d ≤ d*50184*foldUnit y z r := by
  have hr : ¬ r < 2 := by omega
  have h2 : foldPiece y z 2 ≤ foldUnit y z r := by
    unfold foldUnit
    rw [if_neg hr]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hrr : foldPiece y z r ≤ foldUnit y z r := by
    unfold foldUnit
    rw [if_neg hr]
    exact (le_max_right _ _).trans (le_max_right _ _)
  apply foldNumerator_between y z d r (foldUnit y z r) hd hdr
  · exact (foldPiece_end y z 2 (by decide)).trans (Nat.mul_le_mul_left _ h2)
  · exact (foldPiece_end y z r (by omega)).trans (Nat.mul_le_mul_left _ hrr)

end ProximityPrize.SubmissionLower.FoldChainPolynomial6814


