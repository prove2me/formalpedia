-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
-- name    : OAI_NumberTheory_ShortEgyptian_FirstDerivative
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:16:19.189197+00:00
-- url     : https://prove2.me/theorems/b1003475-85e6-4a27-822d-6d9d353e4d62
-- title:
--   The additive phase $e(x)=e^{2\pi i x}$ and its elementary identities
-- statement:
--   For a real number $x$ the file defines the additive phase
--
--   $$e(x)=\exp(2\pi i x)\in\mathbb{C},$$
--
--   the standard unitary character of the additive group $\mathbb{R}$, with period $1$. It records the following identities, valid for all $x,y\in\mathbb{R}$:
--
--   1. $|e(x)|=1$;
--   2. $e(x+y)=e(x)\,e(y)$ and $e(0)=1$;
--   3. $e(n)=1$ for every integer $n$;
--   4. $\operatorname{Re}e(x)=\cos(2\pi x)$ and $\operatorname{Im}e(x)=\sin(2\pi x)$.
--
--   Exponential sums $\sum_{n}e(f(n))$ built from this phase are the analytic core of the argument. They are estimated by a first-derivative (Kusmin–Landau type) test and by van der Corput differencing, applied in particular to $f(n)=Z/n$; averages of $e(lQt_i/u)$ over a family of integers $t_i$ measure how the residues $Qt_i \bmod u$ are distributed.
--
--   **Formalization Note** The Lean name is `phase`, with the simp lemmas `phase_norm`, `phase_add`, `phase_zero`, `phase_int`, `phase_re` and `phase_im`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/FirstDerivative.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/FirstDerivative.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ShortEgyptianFractions mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

noncomputable def phase (x : ℝ) : ℂ := Complex.exp (↑(2 * Real.pi * x) * Complex.I)

@[simp] theorem phase_norm (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp]

@[simp] theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp [phase, mul_add, add_mul, Complex.exp_add]

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

@[simp] theorem phase_int (n : ℤ) : phase n = 1 := by
  have heq : (↑(2 * Real.pi * (n : ℝ)) : ℂ) * Complex.I =
      (n : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  rw [phase, heq, Complex.exp_int_mul_two_pi_mul_I]

@[simp] theorem phase_re (x : ℝ) : (phase x).re = Real.cos (2 * Real.pi * x) := by
  simp [phase, Complex.exp_re]

@[simp] theorem phase_im (x : ℝ) : (phase x).im = Real.sin (2 * Real.pi * x) := by
  simp [phase, Complex.exp_im]

end ShortEgyptian

end OAI


