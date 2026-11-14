-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_ResourceBound
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_ResourceBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:05:39.493202+00:00
-- url     : https://prove2.me/theorems/e110f628-fe47-440d-9bbe-8e43b839d1b5
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Universal.ResourceBound — Polynomial resource bounds for the universal simulator
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Universal.ResourceBound` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The resource functions of Christian Reitwiessner's universal simulator admit explicit polynomial
--   bounds in the encoded description length, encoded input length, clock length, and number of
--   simulated steps. These estimates are shared by unary-clock polynomial-time simulation and the
--   time-hierarchy construction.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.Universal.computableInO_universal`: a plain native machine certificate
--     for the strengthened time and space bounds, including a zero clock.
--
--   * `Turing.MultiTapeTM.Universal.runBound_mono`: the space bound grows with the number of steps.
--   * `Turing.MultiTapeTM.Universal.universal_bounds_le`: for `D, N, L ≤ B` and `1 ≤ J`, the time
--     expression is at most `100000 * (B + 1) ^ 4 * J ^ 2` and the space bound is at most
--     `200 * (B + 1) ^ 2 * J`.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_ResourceBound`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Universal/ResourceBound.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Machine
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Universal.ResourceBound` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial resource bounds for the universal simulator

The resource functions of Christian Reitwiessner's universal simulator admit explicit polynomial
bounds in the encoded description length, encoded input length, clock length, and number of
simulated steps. These estimates are shared by unary-clock polynomial-time simulation and the
time-hierarchy construction.

## Main results

* `Turing.MultiTapeTM.Universal.computableInO_universal`: a plain native machine certificate
  for the strengthened time and space bounds, including a zero clock.

* `Turing.MultiTapeTM.Universal.runBound_mono`: the space bound grows with the number of steps.
* `Turing.MultiTapeTM.Universal.universal_bounds_le`: for `D, N, L ≤ B` and `1 ≤ J`, the time
  expression is at most `100000 * (B + 1) ^ 4 * J ^ 2` and the space bound is at most
  `200 * (B + 1) ^ 2 * J`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.Universal

/-- The universal simulator's space bound grows with the number of simulated steps. -/
theorem runBound_mono {D N t t' : ℕ} (h : t ≤ t') : runBound D N t ≤ runBound D N t' := by
  unfold runBound ctxBound cfgBound tapeBound
  gcongr

/-- **The resources of the universal run.** If the encoded description, the encoded input and the
number of digits `L` of the clock have length at most `B`, the time of the universal function on
`J ≥ 1` steps is `O((B + 1) ^ 4 * J ^ 2)` and its space `O((B + 1) ^ 2 * J)`.
Here `B` includes the encoded input length, so this is not a fixed-machine quadratic-time
simulation bound when the input length varies. The buffered logarithmic-overhead simulation
requires a different tape representation. -/
theorem universal_bounds_le {D N J B L : ℕ} (hD : D ≤ B) (hN : N ≤ B) (hL : L ≤ B) (hJ : 1 ≤ J) :
    (J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2) ≤ 100000 * (B + 1) ^ 4 * J ^ 2 ∧
      runBound D N J ≤ 200 * (B + 1) ^ 2 * J := by
  set M := B + 1
  have hM1 : 1 ≤ M := by omega
  have hDM : D + 1 ≤ M := by omega
  have hNM : N + 1 ≤ M := by omega
  have hJM := Nat.le_mul_of_pos_left J hM1; have hMJ := Nat.le_mul_of_pos_right M hJ
  have hM2 := Nat.le_self_pow two_ne_zero M; have hM2J := Nat.le_mul_of_pos_right (M ^ 2) hJ
  have hMJM2J := Nat.mul_le_mul_right J hM2
  have htape : tapeBound D J ≤ 36 * (M * J) := by
    have := (Nat.mul_le_mul_left (3 * (2 * J)) (show 2 * D + 3 ≤ 5 * M by omega)).trans
      (le_of_eq (show 3 * (2 * J) * (5 * M) = 30 * (M * J) by ring))
    unfold tapeBound; omega
  have hcfg : cfgBound D N J ≤ 80 * (M ^ 2 * J) := by
    have := (Nat.mul_le_mul (by omega : D ≤ M)
      (show 2 * tapeBound D J + 1 ≤ 74 * (M * J) by omega)).trans
      (le_of_eq (show M * (74 * (M * J)) = 74 * (M ^ 2 * J) by ring))
    unfold cfgBound; omega
  have hctx : ctxBound D N J ≤ 89 * (M ^ 2 * J) := by unfold ctxBound; omega
  have hrun : runBound D N J ≤ 200 * M ^ 2 * J := by
    have := (Nat.mul_le_mul_left J (show 2 * D + 1 ≤ 2 * M by omega)).trans
      (le_of_eq (show J * (2 * M) = 2 * (M * J) by ring))
    have : 200 * (M ^ 2 * J) = 200 * M ^ 2 * J := by ring
    unfold runBound; omega
  refine ⟨?_, hrun⟩
  have hM34 := (Nat.pow_le_pow_right hM1 (by omega : 3 ≤ 4)).trans (Nat.le_mul_of_pos_right _ hJ)
  have hM4 := Nat.mul_le_mul_right J (Nat.pow_le_pow_right hM1 (by omega : 2 ≤ 4))
  have hstep : stepBound D N J ≤ 190 * (M ^ 4 * J) := by
    unfold stepBound
    have hfirst : (2 * D + 1) * (D + 1) * (ctxBound D N J + 1) ≤ 180 * (M ^ 4 * J) :=
      (Nat.mul_le_mul (Nat.mul_le_mul (show 2 * D + 1 ≤ 2 * M by omega) hDM)
        (show ctxBound D N J + 1 ≤ 90 * (M ^ 2 * J) by omega)).trans (le_of_eq (by ring))
    have hbits := length_encNat_le (N + 1)
    have hdigits : ((encNat (N + 1)).length + 1) ^ 2 ≤ 4 * M ^ 2 :=
      (Nat.pow_le_pow_left (show (encNat (N + 1)).length + 1 ≤ 2 * M by omega) 2).trans
        (le_of_eq (by ring))
    have hlookup : (N + 1) * ((encNat (N + 1)).length + 1) ^ 2 ≤ 4 * M ^ 3 :=
      (Nat.mul_le_mul hNM hdigits).trans (le_of_eq (by ring))
    omega
  have hL2 : (L + 1) ^ 2 ≤ M ^ 4 * J := (Nat.pow_le_pow_left (by omega) 2).trans (hM2J.trans hM4)
  have hsum : stepBound D N J + runBound D N J + (L + 1) ^ 2 ≤ 391 * (M ^ 4 * J) := by
    have : 200 * M ^ 2 * J = 200 * (M ^ 2 * J) := by ring
    omega
  calc (J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2)
      ≤ (2 * J) * (391 * (M ^ 4 * J)) := Nat.mul_le_mul (by omega) hsum
    _ = 782 * (M ^ 4 * J ^ 2) := by ring
    _ ≤ 100000 * (M ^ 4 * J ^ 2) := by omega
    _ = 100000 * M ^ 4 * J ^ 2 := by ring

/-- A plain native machine computes the clocked universal function within a quartic factor in
the complete encoded input length and a quadratic factor in the number of simulated steps.
The statement includes a zero clock. Its size factor includes the simulated input and binary
clock, so it does not assert fixed-machine quadratic simulation as those inputs vary. -/
theorem computableInO_universal :
    ComputableInO universal eIn eOut
      (fun i => ((eIn i).length + 1) ^ 4 * (i.2.2 + 1) ^ 2)
      (fun i => ((eIn i).length + 1) ^ 2 * (i.2.2 + 1)) := by
  have hbounds (i : Desc × List ℕ × ℕ) :=
    universal_bounds_le (D := descLen i.1) (N := (encList encUnary i.2.1).length)
      (L := (encNat i.2.2).length) (B := (eIn i).length) (J := i.2.2 + 1)
      (length_le_encPair_left _ _ i)
      ((length_le_encPair_left _ _ i.2).trans (length_le_encPair_right _ _ i))
      ((length_le_encPair_right _ _ i.2).trans (length_le_encPair_right _ _ i))
      (Nat.le_add_left 1 i.2.2)
  refine computableTidilyInO_universal.computableInO.mono 100001 (fun i => ?_) (fun i => ?_)
  · have hstep := stepBound_mono (D := descLen i.1) (N := (encList encUnary i.2.1).length)
      le_rfl le_rfl (Nat.le_add_right i.2.2 1)
    have hrun := runBound_mono (D := descLen i.1) (N := (encList encUnary i.2.1).length)
      (Nat.le_add_right i.2.2 1)
    have htime := (Nat.mul_le_mul (show i.2.2 + 1 ≤ i.2.2 + 1 + 1 by omega)
      (Nat.add_le_add_right (Nat.add_le_add hstep hrun) _)).trans (hbounds i).1
    have hinput : ((eIn i).length + 1) ^ 2 ≤ ((eIn i).length + 1) ^ 4 * (i.2.2 + 1) ^ 2 :=
      (Nat.pow_le_pow_right (by omega) (by omega : 2 ≤ 4)).trans
        (Nat.le_mul_of_pos_right _ (by positivity))
    have : 100000 * ((eIn i).length + 1) ^ 4 * (i.2.2 + 1) ^ 2 =
      100000 * (((eIn i).length + 1) ^ 4 * (i.2.2 + 1) ^ 2) := by ring
    omega
  · have hrun := (runBound_mono (D := descLen i.1) (N := (encList encUnary i.2.1).length)
      (Nat.le_add_right i.2.2 1)).trans (hbounds i).2
    have hinput : (eIn i).length ≤ ((eIn i).length + 1) ^ 2 * (i.2.2 + 1) :=
      (Nat.le_succ _).trans ((Nat.le_self_pow two_ne_zero _).trans
        (Nat.le_mul_of_pos_right _ (by omega)))
    have : 200 * ((eIn i).length + 1) ^ 2 * (i.2.2 + 1) =
      200 * (((eIn i).length + 1) ^ 2 * (i.2.2 + 1)) := by ring
    omega

end Turing.MultiTapeTM.Universal


