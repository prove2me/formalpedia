-- Prove2me | Definitions.Def_Yukon_223642192d853991eed59b0f
-- name    : Yukon_223642192d853991eed59b0f
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T15:49:12.418155+00:00
-- url     : https://prove2.me/theorems/e63d3f3c-4ca9-4bd0-9f18-24ad6214f980
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberPackingCheck6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberPackingCheck6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberPackingCheck6814.lean
--
--   yukon-proof-operation:certificate-split-253975d52ed4f2f19528f0f37f2bf5b00bef8833de9fc2ae79604f2468cb86b1
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNGFhMzdkMTk5NTg1YzFmYzhkN2FkNzVhODZkYjZhNjYxOGU2NmM5MzljYWY2ZWY2YWU3OTYzYjcwNjExYjExMSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LTI1Mzk3NWQ1MmVkNGYyZjE5NTI4ZjBmMzdmMmJmNWIwMGJlZjg4MzNkZTlmYzJhZTc5NjA0ZjI0NjhjYjg2YjEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8yMjM2NDIxOTJkODUzOTkxZWVkNTliMGYiLCJ2IjoyfQ]

import Definitions.Def_Yukon_00eaa103b8a7ea0cbec8d6c9









































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingFiberPackingCheck6814
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- Scan two list spines once, without indexed lookup at every comparison. -/
def shifted (a : Nat) : List Nat → List Nat → Bool
  | [],_ => true
  | _,[] => true
  | b::bs,c::cs => decide (a+b≤c) && shifted a bs cs

/-- Check every pair whose combined index remains in the output budget. -/
def convolution : List Nat → List Nat → List Nat → Bool
  | [],_,_ => true
  | _,_,[] => true
  | a::xs,ys,c::cs => shifted a ys (c::cs) && convolution xs ys cs

theorem shifted_sound (a : Nat) (xs ys : List Nat) (h : shifted a xs ys=true)
    (i : Nat) (hi : i<xs.length) (hj : i<ys.length) :
    a+(xs[i]?).getD 0 ≤ (ys[i]?).getD 0 := by
  induction xs generalizing ys i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_nil] at hj; omega
    | cons y ys =>
      simp only [shifted,Bool.and_eq_true,decide_eq_true_eq] at h
      cases i with
      | zero => simpa using h.1
      | succ i =>
        have hh := ih ys h.2 i (by simpa using hi) (by simpa using hj)
        simpa using hh

theorem convolution_sound (xs ys zs : List Nat) (h : convolution xs ys zs=true)
    (i j : Nat) (hi : i<xs.length) (hj : j<ys.length) (hk : i+j<zs.length) :
    (xs[i]?).getD 0+(ys[j]?).getD 0 ≤ (zs[i+j]?).getD 0 := by
  induction xs generalizing zs i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons x xs ih =>
    cases zs with
    | nil => simp only [List.length_nil] at hk; omega
    | cons z zs =>
      simp only [convolution,Bool.and_eq_true] at h
      cases i with
      | zero =>
        simpa using shifted_sound x ys (z::zs) h.1 j hj (by simpa using hk)
      | succ i =>
        have hh := ih zs h.2 i (by simpa using hi) (by simpa [Nat.succ_add] using hk)
        simpa [Nat.succ_add] using hh



end ProximityPrize.SubmissionLower.MovingFiberPackingCheck6814


