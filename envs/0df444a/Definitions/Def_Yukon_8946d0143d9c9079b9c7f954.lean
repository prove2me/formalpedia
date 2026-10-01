-- Prove2me | Definitions.Def_Yukon_8946d0143d9c9079b9c7f954
-- name    : Yukon_8946d0143d9c9079b9c7f954
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:38:14.355515+00:00
-- url     : https://prove2.me/theorems/3fc4e40c-575f-4ab8-b8ac-d504d190194a
-- title:
--   YukonModule.VCVio.CryptoFoundations.Asymptotics.Negligible.part0
-- statement:
--   Source module VCVio.CryptoFoundations.Asymptotics.Negligible.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/CryptoFoundations/Asymptotics/Negligible.lean
--
--   provider-v8:c9451c19c08c87c13576a9518b4fe3c28494b668396b5fcc5f85a4900b5e1819
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODpjOTQ1MWMxOWMwOGM4N2MxMzU3NmE5NTE4YjRmZTNjMjg0OTRiNjY4Mzk2YjVmY2M1Zjg1YTQ5MDBiNWUxODE5IiwiaGFzaCI6IjgxMTVhODA2NzcxMjU1NWJjNDhlZjEyNTRkNjQ3MjM5MDM0ZWFmOTFjZGI1NTIyNTgzOGQ3Zjk5MDgzNGFkMWQiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uXzg5NDZkMDE0M2Q5YzkwNzliOWM3Zjk1NCIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay


public import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# Negligible Functions

This file defines a simple wrapper around `SuperpolynomialDecay` for functions `ℕ → ℝ≥0∞`,
as this is usually the situation for cryptographic reductions.

## Main Results

- `negligible_zero`, `negligible_of_zero`: The zero function is negligible.
- `negligible_of_le`: Monotonicity — bounded by negligible is negligible.
- `negligible_add`: Sum of negligible functions is negligible.
- `negligible_sum`: Finite sum of negligible functions is negligible.
- `negligible_const_mul`: Constant multiple of negligible is negligible.
-/

@[expose] public section

open ENNReal Asymptotics Filter

/-- A function `f` is negligible if it decays faster than any polynomial function. -/
def negligible (f : ℕ → ℝ≥0∞) : Prop :=
  SuperpolynomialDecay atTop (fun x => ↑x) f

@[simp] theorem negligible_iff (f : ℕ → ℝ≥0∞) :
    negligible f ↔ SuperpolynomialDecay atTop (fun x => ↑x) f := Iff.rfl

lemma negligible_zero : negligible 0 := superpolynomialDecay_zero _ _

lemma negligible_of_zero {f : ℕ → ℝ≥0∞} (hf : ∀ n, f n = 0) : negligible f :=
  funext hf ▸ negligible_zero

/-- Negligibility is monotone: if `f ≤ g` pointwise and `g` is negligible, then `f` is. -/
theorem negligible_of_le {f g : ℕ → ℝ≥0∞} (hfg : ∀ n, f n ≤ g n) (hg : negligible g) :
    negligible f := fun p =>
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg p)
    (fun _ => zero_le) (fun n => mul_le_mul_of_nonneg_left (hfg n) zero_le)

/-- Sum of two negligible functions is negligible. -/
theorem negligible_add {f g : ℕ → ℝ≥0∞} (hf : negligible f) (hg : negligible g) :
    negligible (f + g) :=
  hf.add hg

/-- Constant multiple of a negligible function is negligible (requires `c ≠ ⊤`
because multiplication by `⊤` is discontinuous at `0` in `ℝ≥0∞`). -/
theorem negligible_const_mul {f : ℕ → ℝ≥0∞} (hf : negligible f)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    negligible (fun n => c * f n) := by
  intro p
  simpa only [mul_zero] using
    (ENNReal.Tendsto.const_mul (hf p) (.inr hc)).congr (fun n => by rw [mul_left_comm])

/-- A finite sum of negligible functions is negligible. -/
theorem negligible_sum {ι : Type*} {s : Finset ι} {f : ι → ℕ → ℝ≥0∞}
    (h : ∀ i ∈ s, negligible (f i)) :
    negligible (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction with
  | empty => exact negligible_zero
  | insert _ _ hnotin ih =>
    simp_rw [Finset.sum_insert hnotin]
    exact negligible_add
      (h _ (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- If `f` is negligible, then `fun n => (↑n)^d * f n` is negligible for any fixed `d`.
Absorbs polynomial powers of the parameter into the superpolynomial decay. -/
theorem negligible_pow_mul {f : ℕ → ℝ≥0∞} (hf : negligible f) (d : ℕ) :
    negligible (fun n => (↑n : ℝ≥0∞) ^ d * f n) :=
  hf.param_pow_mul d

/-- If `f` is negligible, then `fun n => ↑(p.eval n) * f n` is negligible for any polynomial `p`.
This is the key lemma for handling polynomial-loss security reductions. -/
theorem negligible_polynomial_mul {f : ℕ → ℝ≥0∞} (hf : negligible f)
    (p : Polynomial ℕ) :
    negligible (fun n => ↑(p.eval n) * f n) := by
  have heq : ∀ n, (↑(p.eval n) : ℝ≥0∞) * f n =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        ↑(p.coeff i) * ((↑n : ℝ≥0∞) ^ i * f n) := by
    intro n
    simp [Polynomial.eval_eq_sum_range, Finset.sum_mul, mul_assoc]
  simp_rw [heq]
  exact negligible_sum fun i _ =>
    negligible_const_mul (negligible_pow_mul hf i) (ENNReal.natCast_ne_top _)


