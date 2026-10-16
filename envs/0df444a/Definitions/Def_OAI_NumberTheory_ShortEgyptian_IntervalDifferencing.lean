-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
-- name    : OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:18:38.671913+00:00
-- url     : https://prove2.me/theorems/c6de06fc-2965-4004-a089-000148cc97d4
-- title:
--   The phase of $-x$ is the complex conjugate of the phase of $x$
-- statement:
--   Let $e(x)=\exp(2\pi i x)$ denote the additive phase of a real number $x$, and let $\overline{w}$ denote the complex conjugate of $w\in\mathbb{C}$. The only declaration of this definition file is the identity
--
--   $$e(-x)=\overline{e(x)}\qquad\text{for all }x\in\mathbb{R}.$$
--
--   It is the conjugation rule needed for van der Corput's differencing inequality, which bounds $\bigl|\sum_{p\le n\le q}a_n\bigr|^2$ for complex numbers $a_n$ of modulus at most $1$ in terms of the correlation sums $\sum_{n}a_{n+h}\overline{a_n}$ with $1\le h<L$. For phases $a_n=e(f(n))$ these correlations become phase sums $\sum_n e\bigl(f(n+h)-f(n)\bigr)$ of a differenced function.
--
--   **Formalization Note** The Lean statement is the simp lemma `phase_neg`, in which complex conjugation appears as `starRingEnd ℂ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/IntervalDifferencing.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/IntervalDifferencing.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ShortEgyptianFractions mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uκ uM

namespace ShortEgyptian

open scoped BigOperators
open Finset

@[simp] theorem phase_neg (x : ℝ) : phase (-x) = (starRingEnd ℂ) (phase x) := by
  rw [phase, phase, ← Complex.exp_conj]
  congr 1
  simp [map_ofNat]

end ShortEgyptian

end OAI


