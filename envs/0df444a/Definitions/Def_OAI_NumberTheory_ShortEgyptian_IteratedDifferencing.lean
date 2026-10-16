-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
-- name    : OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:19:49.542139+00:00
-- url     : https://prove2.me/theorems/1b364ec1-aa8f-421e-812d-005ccfc6ac0b
-- title:
--   The phase of a difference: $e(x-y)=e(x)\,\overline{e(y)}$
-- statement:
--   Let $e(x)=\exp(2\pi i x)$ be the additive phase of a real number $x$, and let $\overline{w}$ be the complex conjugate of $w\in\mathbb{C}$. The only declaration of this definition file is the identity
--
--   $$e(x-y)=e(x)\,\overline{e(y)}\qquad\text{for all }x,y\in\mathbb{R}.$$
--
--   It turns the product of a phase and a conjugated phase into the phase of a difference. In repeated van der Corput differencing this converts correlations of the phases $e(f(n))$ into phase sums of differenced functions, so that after $r$ steps the sum $\sum_n e(f(n))$ is controlled by the sums $\sum_n e\bigl((\Delta_{h_1}\cdots\Delta_{h_r}f)(n)\bigr)$ of iterated differences, where $(\Delta_h g)(x)=g(x)-g(x+h)$.
--
--   **Formalization Note** The Lean statement is the simp lemma `phase_sub`, with complex conjugation written `starRingEnd ℂ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/IteratedDifferencing.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/IteratedDifferencing.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ShortEgyptianFractions mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

@[simp] theorem phase_sub (x y : ℝ) :
    phase (x - y) = phase x * (starRingEnd ℂ) (phase y) := by
  rw [sub_eq_add_neg, phase_add, phase_neg]

end ShortEgyptian

end OAI


