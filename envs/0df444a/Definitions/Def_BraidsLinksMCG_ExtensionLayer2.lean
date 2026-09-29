-- Prove2me | Definitions.Def_BraidsLinksMCG_ExtensionLayer2
-- name    : BraidsLinksMCG_ExtensionLayer2
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-24T10:19:27.712295+00:00
-- url     : https://prove2.me/theorems/96bdcc3a-4947-4ae6-8c8c-52d13f250078
-- title:
--   Endpoint and boundary values for the elementary half-twist geometry
-- statement:
--   Layer 2 (pointwise part) of the strand-extension geometry: the left and right moving points of the elementary half-twist are n+1 and n+2 at the start of the interval and swap at the end, the interpolating point agrees with the approach functions of the n+1-st and n-th punctured plane on the two boundary edges of the square, and the circle around the j-th puncture stays strictly to the left of the left moving point.
-- source:
--   Extracted from the local geometry prefix of the open target BraidsLinksMCG.extensionBoundaryHomotopy_inline_child_v4 (39872516-612f-4cb5-9ca6-4ee965218a2f); split into layers so each layer compiles independently. Layer 1 is the published BraidsLinksMCG_ExtensionPairLayer (3ed703ab-4406-43ae-8826-19ebee928046). The path-family material of the original prefix was excluded because the remote compiler showed it to be ill-typed as written (publish job 0f7d5ef7-d22d-444f-aca9-aa090eb364c5).

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_strand_extension_v1
import Definitions.Def_BraidsLinksMCG_ExtensionPairLayer

/-!
Layer 2 of the strand-extension geometry build (pointwise part).

Built on the published layer `BraidsLinksMCG_ExtensionPairLayer`.  It records where the
two moving points of the elementary half-twist sit at the two ends of the interval, where
the interpolating point sits on the two boundary edges of the square, and that the circle
around the `j`-th puncture stays to the left of the left moving point.
-/

open unitInterval BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension
open scoped unitInterval

namespace BraidsLinksMCG

noncomputable section
lemma circleFun_re_le_mid (n : ℕ) (j : Fin n) (t : ℝ) :
    (circleFun n j t).re ≤ ((j : ℕ) : ℝ) + 3 / 2 := by
  have hcos : Real.cos (2 * Real.pi * t) ≤ 1 := Real.cos_le_one _
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hre : (circleFun n j t).re =
      ((j : ℕ) : ℝ) + 1 + (1 / 2) * Real.cos (2 * Real.pi * t) := by
    rw [circleFun, Complex.exp_ofReal_mul_I, hhalf]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
      Complex.natCast_re, Complex.one_re]
    ring
  rw [hre]
  linarith

lemma circleFun_ne_pairLeft (n : ℕ) (j : Fin n) (s : I) (t : ℝ) :
    circleFun n j t ≠ extensionPairLeft n s := by
  intro h
  have hRe := congrArg Complex.re h
  have hc := circleFun_re_le_mid n j t
  have hA := extensionPairLeft_re_lower n s
  have hjNat : (j : ℕ) + 1 ≤ n := Nat.succ_le_of_lt j.isLt
  have hj : ((j : ℕ) : ℝ) + 3 / 2 ≤ (n : ℝ) + 1 / 2 := by
    have hj' : ((j : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hjNat
    linarith
  linarith

lemma extensionPairRight_zero (n : ℕ) :
    extensionPairRight n 0 = (((n : ℝ) + 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using
      (calc
        (extensionPairRight n 0).re =
            (twistPoint ((n : ℝ) + 3 / 2) 1 0).re := rfl
        _ = ((n : ℝ) + 3 / 2) + 1 / 2 := twistPoint_plus_one_zero_re _
        _ = (n : ℝ) + 2 := by push_cast; ring)
  · have hzero : ((0 : I) : ℝ) = 0 := rfl
    simpa only [Complex.ofReal_im] using
      (calc
        (extensionPairRight n 0).im =
            (twistPoint ((n : ℝ) + 3 / 2) 1 ((0 : I) : ℝ)).im := rfl
        _ = (twistPoint ((n : ℝ) + 3 / 2) 1 0).im := by rw [hzero]
        _ = 0 := twistPoint_zero_im ((n : ℝ) + 3 / 2) 1)

lemma extensionPairRight_one (n : ℕ) :
    extensionPairRight n 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using
      (calc
        (extensionPairRight n 1).re =
            (twistPoint ((n : ℝ) + 3 / 2) 1 1).re := rfl
        _ = ((n : ℝ) + 3 / 2) - 1 / 2 := twistPoint_plus_one_pi_re _
        _ = (n : ℝ) + 1 := by push_cast; ring)
  · have hone : ((1 : I) : ℝ) = 1 := rfl
    simpa only [Complex.ofReal_im] using
      (calc
        (extensionPairRight n 1).im =
            (twistPoint ((n : ℝ) + 3 / 2) 1 ((1 : I) : ℝ)).im := rfl
        _ = (twistPoint ((n : ℝ) + 3 / 2) 1 1).im := by rw [hone]
        _ = 0 := twistPoint_one_im ((n : ℝ) + 3 / 2) 1)

lemma extensionPairLeft_zero (n : ℕ) :
    extensionPairLeft n 0 = (((n : ℝ) + 1 : ℝ) : ℂ) := by
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using
      (calc
        (extensionPairLeft n 0).re =
            (twistPoint ((n : ℝ) + 3 / 2) (-1) 0).re := rfl
        _ = ((n : ℝ) + 3 / 2) - 1 / 2 := twistPoint_minus_one_zero_re _
        _ = (n : ℝ) + 1 := by push_cast; ring)
  · have hzero : ((0 : I) : ℝ) = 0 := rfl
    simpa only [Complex.ofReal_im] using
      (calc
        (extensionPairLeft n 0).im =
            (twistPoint ((n : ℝ) + 3 / 2) (-1) ((0 : I) : ℝ)).im := rfl
        _ = (twistPoint ((n : ℝ) + 3 / 2) (-1) 0).im := by rw [hzero]
        _ = 0 := twistPoint_zero_im ((n : ℝ) + 3 / 2) (-1))

lemma extensionPairLeft_one (n : ℕ) :
    extensionPairLeft n 1 = (((n : ℝ) + 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using
      (calc
        (extensionPairLeft n 1).re =
            (twistPoint ((n : ℝ) + 3 / 2) (-1) 1).re := rfl
        _ = ((n : ℝ) + 3 / 2) + 1 / 2 := twistPoint_minus_one_pi_re _
        _ = (n : ℝ) + 2 := by push_cast; ring)
  · have hone : ((1 : I) : ℝ) = 1 := rfl
    simpa only [Complex.ofReal_im] using
      (calc
        (extensionPairLeft n 1).im =
            (twistPoint ((n : ℝ) + 3 / 2) (-1) ((1 : I) : ℝ)).im := rfl
        _ = (twistPoint ((n : ℝ) + 3 / 2) (-1) 1).im := by rw [hone]
        _ = 0 := twistPoint_one_im ((n : ℝ) + 3 / 2) (-1))

lemma extensionApproach_at_left (n : ℕ) (j : Fin n) (u : I) :
    extensionApproach n j (0, u) = approachFun (n + 1) j.castSucc (u : ℝ) := by
  dsimp only [extensionApproach]
  rw [extensionPairRight_zero]
  apply Complex.ext
  · simp [approachFun, Fin.val_castSucc, Complex.add_re, Complex.mul_re] <;>
      push_cast <;> ring
  · simp [approachFun, Fin.val_castSucc, Complex.add_im, Complex.mul_im] <;> ring

lemma extensionApproach_at_right (n : ℕ) (j : Fin n) (u : I) :
    extensionApproach n j (1, u) = approachFun n j (u : ℝ) := by
  unfold extensionApproach approachFun
  rw [extensionPairRight_one]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    have him : ((((u : ℝ) : ℂ)) * (1 - (((u : ℝ) : ℂ)))).im = 0 := by
      simp only [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
        Complex.ofReal_im]
    rw [him]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    have hre : ((((u : ℝ) : ℂ)) * (1 - (((u : ℝ) : ℂ)))).re = (u : ℝ) * (1 - (u : ℝ)) := by
      simp only [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
        Complex.ofReal_re]
    rw [hre]
    ring

end

end BraidsLinksMCG


