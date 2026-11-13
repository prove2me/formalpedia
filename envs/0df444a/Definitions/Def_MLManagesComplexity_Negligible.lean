-- Prove2me | Definitions.Def_MLManagesComplexity_Negligible
-- name    : MLManagesComplexity_Negligible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:56.6892+00:00
-- url     : https://prove2.me/theorems/ef956e3d-9d2e-4e11-b5a5-ab419daea60a
-- title:
--   Negligible functions
-- statement:
--   A function $f:\mathbb N\to\mathbb R$ is **negligible** if $f(n)=o(1/n^k)$ for every $k$, that is,
--
--   $$
--   \lim_{n\to\infty} n^k f(n) = 0 \qquad\text{for every } k\in\mathbb N .
--   $$
--
--   The paper writes "$f(n)\le \mathrm{negl}(n)$" for "$f$ is bounded by a negligible function"; the statements of this mission write this as: there is a negligible real-valued $\nu$ with $f(n)\le\nu(n)$ for all $n$.
--
--   This is the asymptotic notion of "too small to matter" used in every security and indistinguishability statement of the paper.
--
--   **Formalization Note** No sign condition is imposed on $f$ (the paper imposes none).
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), §3 Preliminaries, p.4 (PDF p.5)

import Mathlib

set_option autoImplicit false

namespace MLManagesComplexity

/-- **Negligible function** (Fortnow, *How Does Machine Learning Manage Complexity?*,
arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), §3, printed p.4, PDF p.5:
"A function f(n) is negligible if f(n) = o(1/n^k) for all k."): for every exponent `k`,
`n^k · f(n) → 0` as `n → ∞`.

**Formalization Note** `f(n) = o(1/n^k)` is written as `n^k · f(n) → 0`; no sign condition is
imposed on `f`. The paper's abuse of notation "f(n) ≤ negl(n)" is rendered in the statements that
use it as `∃ ν, Negligible ν ∧ ∀ n, f n ≤ ν n`, with `ν` real valued. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ k * f n) Filter.atTop (nhds 0)

end MLManagesComplexity


