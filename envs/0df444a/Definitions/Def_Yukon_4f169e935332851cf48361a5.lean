-- Prove2me | Definitions.Def_Yukon_4f169e935332851cf48361a5
-- name    : Yukon_4f169e935332851cf48361a5
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T07:42:15.8185+00:00
-- url     : https://prove2.me/theorems/2a12b73b-6943-4782-8e2d-976fdfde22eb
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceNativeEnvelope6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceNativeEnvelope6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceNativeEnvelope6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-30aa6488feec29d9ea168c6c13aa35eb895ebcbc06c87854fd037e304fcf4ac3
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNzRjNmFjMGYxNjdkZDc0Y2RjNzBiYmUzNzljNzU0ZDQxOWY1NDViM2I0Nzk5MDY1YTNhODExZGNmYzM3MzhlMSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtMzBhYTY0ODhmZWVjMjlkOWVhMTY4YzZjMTNhYTM1ZWI4OTVlYmNiYzA2Yzg3ODU0ZmQwMzdlMzA0ZmNmNGFjMyIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzRmMTY5ZTkzNTMzMjg1MWNmNDgzNjFhNSIsInYiOjJ9]

import Definitions.Def_Yukon_4a0b8ca13aa8ab32899f444d













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Exact nonlinear unique-owner arithmetic for just two retained profiles.
This is a checked-cell ledger bound; it is not a global score claim. -/
namespace ProximityPrize.SubmissionLower.MovingSourceNativeEnvelope6814
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open RCN095 SecondJetRelaxedFlag

def copies3 (m : ℕ) : ℕ := (m+2)/m
def copies7 (m : ℕ) : ℕ := (m+6)/m
def capS (m : ℕ) : ℕ := min (14/copies3 m) (24/copies7 m)
def capB (m : ℕ) : ℕ := min (31/copies3 m) (53/copies7 m)
def capU (m : ℕ) : ℕ := min (98/copies3 m) (177/copies7 m)
def capT (m : ℕ) : ℕ := min (995/copies3 m) (3429/copies7 m)
def nativeFlag (m s : ℕ) : FlagDegree := budgetFlag (capB m) (capU m) (capT m) m s
def parentFlag : FlagDegree := ⟨3504,45,12⟩
def coefficientZ3 : ℕ := 4*131072*(131074*3504)+3*65539*(131073*3504)
def coefficientU3 : ℕ := 4*131072*(131074*45-131072)+3*65539*(131073*45)
def coefficientA3 : ℕ := 4*131072*(131074*11)+3*65539*(131073*12-1)

def scaledMain (m s : ℕ) : ℕ := 3*126275387074424400*m+
  coefficientZ3*flagMixed parentFlag unitZFlag (nativeFlag m s)+
  coefficientU3*flagMixed parentFlag unitYZFlag (nativeFlag m s)+
  coefficientA3*flagMixed parentFlag unitAllFlag (nativeFlag m s)

theorem copies3_le (m e : ℕ) (hm : 0<m) (h : 3≤e*m) : copies3 m≤e := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hm).mpr
  nlinarith

theorem copies7_le (m e : ℕ) (hm : 0<m) (h : 7≤e*m) : copies7 m≤e := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hm).mpr
  nlinarith

theorem copies3_pos (m : ℕ) (hm : 0<m) : 0<copies3 m := by
  change 0<(m+2)/m
  exact Nat.div_pos (by omega) hm

theorem copies7_pos (m : ℕ) (hm : 0<m) : 0<copies7 m := by
  change 0<(m+6)/m
  exact Nat.div_pos (by omega) hm

theorem budget_caps (m : ℕ) : capB m≤capU m ∧ capU m≤capT m := by
  constructor
  · exact min_le_min (Nat.div_le_div_right (by omega)) (Nat.div_le_div_right (by omega))
  · exact min_le_min (Nat.div_le_div_right (by omega)) (Nat.div_le_div_right (by omega))

/-- 15x15 guarded small-Nat cases; no polynomial spaces or rational
arithmetic are evaluated. The valid set contains 73 nonlinear envelopes. -/
theorem finite_native_receipt : ∀ m s : Fin 15,
    0<m.val → 2≤s.val → m.val≤s.val → s.val≤capS m.val → 2*s.val≤capB m.val →
    4*scaledMain m.val s.val≤3*1036142808586141401*m.val := by
  decide +kernel

theorem nonlinear_native_main_fits (m s : ℕ)
    (hm : 0<m) (hs : 2≤s) (hms : m≤s) (hcap : s≤capS m) (hB : 2*s≤capB m) :
    scaledMain m s<3*272069082261391681*m := by
  have hs14 : s≤14 := by
    have h3 := copies3_pos m hm
    have h := hcap.trans (min_le_left (14/copies3 m) (24/copies7 m))
    have hd := Nat.div_le_self 14 (copies3 m)
    omega
  have hh := finite_native_receipt ⟨m,by omega⟩ ⟨s,by omega⟩ hm hs hms hcap hB
  change 4*scaledMain m s≤3*1036142808586141401*m at hh
  nlinarith








end ProximityPrize.SubmissionLower.MovingSourceNativeEnvelope6814


