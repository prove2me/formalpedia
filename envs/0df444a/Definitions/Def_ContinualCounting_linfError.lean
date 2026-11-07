-- Prove2me | Definitions.Def_ContinualCounting_linfError
-- name    : ContinualCounting_linfError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:48.887161+00:00
-- url     : https://prove2.me/theorems/d7d6264f-fbcc-4513-bfb2-e48075ef95f4
-- title:
--   The $\ell_\infty$ error $\mathrm{err}_\infty(M)$
-- statement:
--   The $\ell_\infty$ error of a mechanism $M$ for prefix sums is
--   $$\mathrm{err}_\infty(M)=\max_{x\in\{0,1\}^n}\mathbb E\big[\|M(x)-Ax\|_\infty\big].$$
--
--   This is the accuracy measure of Theorems 1 and 2 and of Lemma 2.
--
--   **Formalization Note** The norm of `Fin n → ℝ` is the sup norm. The value lies in $[0,\infty]$, computed with `lintegral`, so that a non-integrable error is $\infty$ and not a default $0$.
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), Theorem 1, p.2 (PDF p.3), and Lemma 2, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_ContinualCounting_prefixSum

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- **The `ℓ∞` error** `err∞(M) = max_{x ∈ {0,1}^n} E[∥M(x) − Ax∥∞]` (Bairaktari, Dahl, Larsen,
arXiv:2607.00876, sha256 986e6426…, Theorem 1, p.2, and Lemma 2, p.17).

**Formalization Note.** The norm of `Fin n → ℝ` in Mathlib is the sup norm, the paper's `∥·∥∞`. The
expectation is a `lintegral` of `enorm` with values in `ℝ≥0∞`, so a mechanism whose error is not
integrable has error `∞` rather than a junk `0`. The maximum over the finite set of inputs is a
`⨆` in `ℝ≥0∞`. -/
noncomputable def linfError {n : ℕ} (M : (Fin n → Bool) → Measure (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨆ x, ∫⁻ y, ‖y - prefixSum (bitVec x)‖ₑ ∂(M x)

end ContinualCounting


