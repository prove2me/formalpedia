-- Prove2me | Definitions.Def_Cslib_254e30e_Foundations_Data_Nat_PolynomialBound
-- name    : Cslib_254e30e_Foundations_Data_Nat_PolynomialBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:18.304793+00:00
-- url     : https://prove2.me/theorems/06cce649-32fa-4c15-9e99-f540fc9f3f5d
-- title:
--   Cslib.Foundations.Data.Nat.PolynomialBound — Polynomial bounds on natural-valued functions
-- statement:
--   This is module `Cslib.Foundations.Data.Nat.PolynomialBound` of [CSLib](https://github.com/leanprover/cslib) (Apache-2.0), at commit `254e30e`: part of its development of multi-tape Turing machines. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states its running-time bounds on these machines.
--
--   `PolynomiallyBounded f` means that `f n ≤ n ^ d` eventually, for some fixed degree `d`.
--   This is equivalent to a real-valued `IsBigO` bound and to a bound `c * (n + 1) ^ d`
--   at every input. It is a growth condition and does not assert computability.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Cslib_254e30e_Foundations_Data_Nat_PolynomialBound`.
-- source:
--   https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Foundations/Data/Nat/PolynomialBound.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Order

set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Prove2me definition bundle for `Cslib.Foundations.Data.Nat.PolynomialBound` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial bounds on natural-valued functions

`PolynomiallyBounded f` means that `f n ≤ n ^ d` eventually, for some fixed degree `d`.
This is equivalent to a real-valued `IsBigO` bound and to a bound `c * (n + 1) ^ d`
at every input. It is a growth condition and does not assert computability.
-/

@[expose] public section

namespace Cslib

open Asymptotics Filter

/-- A function is polynomially bounded if a fixed power eventually bounds its values. -/
def PolynomiallyBounded (f : ℕ → ℕ) : Prop :=
  ∃ d : ℕ, f ≤ᶠ[atTop] (· ^ d)

/-- Polynomial growth is equivalent to a big-O bound after casting to the reals. -/
theorem polynomiallyBounded_iff_isBigO {f : ℕ → ℕ} :
    PolynomiallyBounded f ↔
      ∃ d : ℕ, (fun n => (f n : ℝ)) =O[atTop] (fun n => (n : ℝ) ^ d) := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, .of_bound' ?_⟩
    filter_upwards [hd] with n hn
    simpa using (show (f n : ℝ) ≤ (n : ℝ) ^ d by exact_mod_cast hn)
  · rintro ⟨d, hd⟩
    obtain ⟨c, _, hc⟩ := hd.exists_pos
    refine ⟨d + 1, ?_⟩
    filter_upwards [hc.bound, eventually_ge_atTop ⌈c⌉₊] with n hn hcn
    grw [Nat.le_ceil c, Real.norm_natCast, norm_pow, Real.norm_natCast, hcn, ← pow_succ'] at hn
    exact_mod_cast hn

/-- A polynomial bound can absorb every finite prefix into its constant factor. -/
theorem polynomiallyBounded_iff_le {f : ℕ → ℕ} :
    PolynomiallyBounded f ↔ ∃ c d : ℕ, ∀ n, f n ≤ c * (n + 1) ^ d := by
  constructor
  · simp_rw [PolynomiallyBounded, EventuallyLE, eventually_atTop]
    intro ⟨d, m, h⟩
    have ⟨c, hc⟩ := (Set.finite_Iio m).image f |>.exists_le
    use c + 1, d
    intro n
    obtain (hn | hn) := n.lt_or_ge m
    · grw [hc _ ⟨n, hn, rfl⟩, c.le_add_right 1, ← d.one_le_pow' n, mul_one]
    · grw [h n hn, n.le_add_right 1, ← Nat.le_add_left 1 c, one_mul]
  · rintro ⟨c, d, hf⟩
    refine ⟨d + 1, ?_⟩
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (c * 2 ^ d)] with n hn hc
    calc
      f n ≤ c * (n + 1) ^ d := hf n
      _ ≤ c * (2 * n) ^ d := by gcongr; lia
      _ = (c * 2 ^ d) * n ^ d := by rw [mul_pow, mul_assoc]
      _ ≤ n * n ^ d := Nat.mul_le_mul_right _ hc
      _ = n ^ (d + 1) := (pow_succ' n d).symm

end Cslib


