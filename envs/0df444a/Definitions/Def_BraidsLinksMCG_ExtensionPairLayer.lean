-- Prove2me | Definitions.Def_BraidsLinksMCG_ExtensionPairLayer
-- name    : BraidsLinksMCG_ExtensionPairLayer
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-24T07:50:29.636723+00:00
-- url     : https://prove2.me/theorems/3ed703ab-4406-43ae-8826-19ebee928046
-- title:
--   The moving points of the elementary half-twist and their avoidance properties
-- statement:
--   Layer 1 of the strand-extension geometry: the left and right moving points of the elementary half-twist about the midpoint n + 3/2, the point interpolating between the right moving point and the puncture j + 3/2, and the endpoint, positivity and avoidance properties of those points.
-- source:
--   Extracted from the local geometry prefix of the open target BraidsLinksMCG.extensionBoundaryHomotopy_inline_child_v4 and split into layers so each layer compiles on its own; tactic fixes come from the recorded remote compile diagnostics of publish jobs 7515e489-bd93-4876-9076-f273b44cf0c6 and d3313e2b-560a-4513-a6ac-3e1eb4eb83fe.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_strand_extension_v1

/-!
Layer 1 of the strand-extension geometry build.

This layer contains only the two moving points of the elementary half-twist, the
interpolating approach point, and their endpoint and avoidance properties. It is
published on its own so that each layer of the geometry is small enough to be
compiled and checked independently.
-/

open unitInterval BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension
open scoped unitInterval

namespace BraidsLinksMCG

noncomputable section

/-- The left moving point of the half-twist centred at `n + 3/2`. -/
def extensionPairLeft (n : ℕ) (s : I) : ℂ :=
  twistPoint ((n : ℝ) + 3 / 2) (-1) (s : ℝ)

/-- The right moving point of the half-twist centred at `n + 3/2`. -/
def extensionPairRight (n : ℕ) (s : I) : ℂ :=
  twistPoint ((n : ℝ) + 3 / 2) 1 (s : ℝ)

/-- The point that interpolates, at height `x.2`, between the right moving point
at parameter `x.1` and the puncture `j + 3/2`. -/
def extensionApproach (n : ℕ) (j : Fin n) (x : I × I) : ℂ :=
  (((1 - (x.2 : ℝ) : ℝ) : ℂ) * extensionPairRight n x.1) +
    (((x.2 : ℝ) : ℂ) * ((((j : ℕ) : ℝ) + 3 / 2 : ℝ) : ℂ)) +
    (((x.2 : ℝ) * (1 - (x.2 : ℝ)) : ℂ) * Complex.I)

lemma extensionPairLeft_re_lower (n : ℕ) (s : I) :
    (n : ℝ) + 1 ≤ (extensionPairLeft n s).re := by
  have hre : (extensionPairLeft n s).re =
      (n : ℝ) + 3 / 2 + (-1) * Real.cos (Real.pi * (s : ℝ)) / 2 := by
    simp [extensionPairLeft, twistPoint_re]
  rw [hre]
  nlinarith [Real.cos_le_one (Real.pi * (s : ℝ))]

lemma extensionPairRight_re_lower (n : ℕ) (s : I) :
    (n : ℝ) + 1 ≤ (extensionPairRight n s).re := by
  have hre : (extensionPairRight n s).re =
      (n : ℝ) + 3 / 2 + Real.cos (Real.pi * (s : ℝ)) / 2 := by
    simp [extensionPairRight, twistPoint_re]
  rw [hre]
  nlinarith [Real.neg_one_le_cos (Real.pi * (s : ℝ))]

lemma extensionPairRight_im_nonneg (n : ℕ) (s : I) :
    0 ≤ (extensionPairRight n s).im := by
  have him : (extensionPairRight n s).im = Real.sin (Real.pi * (s : ℝ)) / 2 := by
    simp [extensionPairRight, twistPoint_im]
  rw [him]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (mul_nonneg Real.pi_pos.le s.2.1)
    (by nlinarith [Real.pi_pos, s.2.2] : Real.pi * (s : ℝ) ≤ Real.pi)
  linarith

lemma extensionPairLeft_im_nonpos (n : ℕ) (s : I) :
    (extensionPairLeft n s).im ≤ 0 := by
  have him : (extensionPairLeft n s).im = (-1) * Real.sin (Real.pi * (s : ℝ)) / 2 := by
    simp [extensionPairLeft, twistPoint_im]
  rw [him]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (mul_nonneg Real.pi_pos.le s.2.1)
    (by nlinarith [Real.pi_pos, s.2.2] : Real.pi * (s : ℝ) ≤ Real.pi)
  linarith

lemma extensionPairLeft_ne_fixed (n : ℕ) (s : I) (k : Fin n) :
    extensionPairLeft n s ≠ ((k : ℕ) + 1 : ℂ) := by
  intro h
  have hRe : (extensionPairLeft n s).re = ((k : ℕ) : ℝ) + 1 := by
    simpa using congrArg Complex.re h
  have hA := extensionPairLeft_re_lower n s
  have hkNat : (k : ℕ) + 1 ≤ n := Nat.succ_le_of_lt k.isLt
  have hk : ((k : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hkNat
  linarith

lemma extensionPairRight_ne_fixed (n : ℕ) (s : I) (k : Fin n) :
    extensionPairRight n s ≠ ((k : ℕ) + 1 : ℂ) := by
  intro h
  have hRe : (extensionPairRight n s).re = ((k : ℕ) : ℝ) + 1 := by
    simpa using congrArg Complex.re h
  have hB := extensionPairRight_re_lower n s
  have hkNat : (k : ℕ) + 1 ≤ n := Nat.succ_le_of_lt k.isLt
  have hk : ((k : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hkNat
  linarith

lemma extensionApproach_im (n : ℕ) (j : Fin n) (x : I × I) :
    (extensionApproach n j x).im =
      (1 - (x.2 : ℝ)) * (extensionPairRight n x.1).im +
        (x.2 : ℝ) * (1 - (x.2 : ℝ)) := by
  unfold extensionApproach
  simp <;> ring

lemma extensionApproach_im_pos (n : ℕ) (j : Fin n) (x : I × I)
    (h0 : 0 < (x.2 : ℝ)) (h1 : (x.2 : ℝ) < 1) :
    0 < (extensionApproach n j x).im := by
  rw [extensionApproach_im]
  have hb := extensionPairRight_im_nonneg n x.1
  have hu : 0 < (x.2 : ℝ) * (1 - (x.2 : ℝ)) := mul_pos h0 (by linarith)
  have h1' : 0 ≤ 1 - (x.2 : ℝ) := by linarith
  have h2 : 0 ≤ (1 - (x.2 : ℝ)) * (extensionPairRight n x.1).im := mul_nonneg h1' hb
  linarith

lemma extensionApproach_zero (n : ℕ) (j : Fin n) (s : I) :
    extensionApproach n j (s, 0) = extensionPairRight n s := by
  simp [extensionApproach]

lemma extensionApproach_one (n : ℕ) (j : Fin n) (s : I) :
    extensionApproach n j (s, 1) = ((((j : ℕ) : ℝ) + 3 / 2 : ℝ) : ℂ) := by
  simp [extensionApproach]

lemma extensionApproach_safe (n : ℕ) (j : Fin n) (x : I × I) (k : Fin n) :
    extensionApproach n j x ≠ ((k : ℕ) + 1 : ℂ) := by
  rcases eq_or_lt_of_le x.2.2.1 with huZero | huPositive
  · have hu' : x.2 = 0 := Subtype.ext huZero.symm
    have hx : x = (x.1, 0) := Prod.ext rfl hu'
    rw [hx, extensionApproach_zero]
    intro h
    have hRe : (extensionPairRight n x.1).re = ((k : ℕ) : ℝ) + 1 := by
      simpa using congrArg Complex.re h
    have hB := extensionPairRight_re_lower n x.1
    have hkNat : (k : ℕ) + 1 ≤ n := Nat.succ_le_of_lt k.isLt
    have hk : ((k : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hkNat
    linarith
  · rcases eq_or_lt_of_le x.2.2.2 with huOne | huBelowOne
    · have hu' : x.2 = 1 := Subtype.ext huOne
      have hx : x = (x.1, 1) := Prod.ext rfl hu'
      rw [hx, extensionApproach_one]
      intro h
      have hRe : ((j : ℕ) : ℝ) + 3 / 2 = ((k : ℕ) : ℝ) + 1 := by
        simpa using congrArg Complex.re h
      refine half_ne ((j : ℕ) + 1) (k : ℕ) ?_
      push_cast
      linarith
    · apply not_puncture_of_im_ne _
        (ne_of_gt (extensionApproach_im_pos n j x huPositive huBelowOne)) k

lemma extensionApproach_ne_pairLeft (n : ℕ) (j : Fin n) (x : I × I) :
    extensionApproach n j x ≠ extensionPairLeft n x.1 := by
  rcases eq_or_lt_of_le x.2.2.1 with huZero | huPositive
  · have hu' : x.2 = 0 := Subtype.ext huZero.symm
    have hx : x = (x.1, 0) := Prod.ext rfl hu'
    rw [hx, extensionApproach_zero]
    exact (twistPoint_ne_twistPoint ((n : ℝ) + 3 / 2) (x.1 : ℝ)).symm
  · rcases eq_or_lt_of_le x.2.2.2 with huOne | huBelowOne
    · have hu' : x.2 = 1 := Subtype.ext huOne
      have hx : x = (x.1, 1) := Prod.ext rfl hu'
      rw [hx, extensionApproach_one]
      intro h
      have hRe : ((j : ℕ) : ℝ) + 3 / 2 = (extensionPairLeft n x.1).re := by
        simpa using congrArg Complex.re h
      have hA := extensionPairLeft_re_lower n x.1
      have hjNat : (j : ℕ) + 1 ≤ n := Nat.succ_le_of_lt j.isLt
      have hj : ((j : ℕ) : ℝ) + 3 / 2 ≤ (n : ℝ) + 1 / 2 := by
        have hj' : ((j : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hjNat
        linarith
      linarith
    · intro h
      have hIm : (extensionApproach n j x).im = (extensionPairLeft n x.1).im :=
        congrArg Complex.im h
      have hPos := extensionApproach_im_pos n j x huPositive huBelowOne
      have hNonpos := extensionPairLeft_im_nonpos n x.1
      linarith

lemma twistPoint_plus_one_zero_re (c : ℝ) :
    (twistPoint c 1 0).re = c + 1 / 2 := by
  rw [twistPoint_re]
  norm_num [Real.cos_zero] <;> ring

lemma twistPoint_minus_one_zero_re (c : ℝ) :
    (twistPoint c (-1) 0).re = c - 1 / 2 := by
  rw [twistPoint_re]
  norm_num [Real.cos_zero] <;> ring

lemma twistPoint_plus_one_pi_re (c : ℝ) :
    (twistPoint c 1 1).re = c - 1 / 2 := by
  rw [twistPoint_re]
  simp [Real.cos_pi] <;> ring

lemma twistPoint_minus_one_pi_re (c : ℝ) :
    (twistPoint c (-1) 1).re = c + 1 / 2 := by
  rw [twistPoint_re]
  simp [Real.cos_pi] <;> ring

lemma twistPoint_zero_im (c s : ℝ) :
    (twistPoint c s 0).im = 0 := by
  rw [twistPoint_im]
  simp [Real.sin_zero]

lemma twistPoint_one_im (c s : ℝ) :
    (twistPoint c s 1).im = 0 := by
  rw [twistPoint_im]
  simp [Real.sin_pi]

end

end BraidsLinksMCG


