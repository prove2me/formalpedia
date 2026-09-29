-- Prove2me | Definitions.Def_syracuseDyadicPhase
-- name    : syracuseDyadicPhase
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-09T08:54:43.443111+00:00
-- url     : https://prove2.me/theorems/de3f94c5-b3db-4758-afa7-12a8043deb7d
-- title:
--   Integer dyadic Syracuse phase and centered representative
-- statement:
--   For n ≥ 1, j ≥ 1, ξ ∈ Z/(3^n)Z, and integer l, define the finite residue ξ·3^(2j−2)·2^(1−l) modulo 3^n, using the canonical unit represented by 2. Define centeredPhase to be the representative modulo one in (−1/2,1/2]. The Lean definition is total in all parameters; these are definitions only, with no phase recurrence, character identity, or cancellation estimate asserted.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, arXiv:1909.03562v7, Section 7.1, equations (7.7)–(7.9), https://arxiv.org/html/1909.03562v7.

import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

private lemma coprime_two_three_pow (n : ℕ) : Nat.Coprime 2 (3 ^ n) := by
  exact (by decide : Nat.Coprime 2 3).pow_right n

def syracuseDyadicUnit (n : ℕ) : (ZMod (3 ^ n))ˣ :=
  ZMod.unitOfCoprime 2 (coprime_two_three_pow n)

def syracuseDyadicInversePower (n : ℕ) (l : ℤ) : ZMod (3 ^ n) :=
  ((syracuseDyadicUnit n) ^ (-l) : (ZMod (3 ^ n))ˣ)

def syracuseDyadicPhase (n : ℕ) (ξ : ZMod (3 ^ n)) (j : ℕ) (l : ℤ) : ZMod (3 ^ n) :=
  ξ * (3 : ZMod (3 ^ n)) ^ (2 * (j - 1)) *
    syracuseDyadicInversePower n (l - 1)

def centeredPhase (x : ℝ) : ℝ :=
  toIocMod (show (0 : ℝ) < 1 by norm_num) (-(1 / 2 : ℝ)) x


