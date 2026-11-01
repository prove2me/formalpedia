-- Prove2me | Definitions.Def_SmoothNestedSim_IsAsympEquiv
-- name    : SmoothNestedSim_IsAsympEquiv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:16.636679+00:00
-- url     : https://prove2.me/theorems/55e26fc0-0895-41c5-b027-bd76d42cbdaa
-- title:
--   Same order $a_k \asymp b_k$
-- statement:
--   For two real sequences $(a_k)$ and $(b_k)$ we write $a_k\asymp b_k$ if there are constants $C,C'>0$ such that
--
--   $$
--   C' \le \frac{a_k}{b_k} \le C \qquad\text{for all $k$ large enough.}
--   $$
--
--   Theorem 1 prescribes its allocations of the simulation budget with this relation (for example $n\asymp\Gamma$, $m\asymp 1$, $\lambda\asymp\Gamma^{-1}$).
--
--   **Formalization Note** The paper uses $\asymp$ for positive sequences only; every use in this mission compares positive sequences.
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, §1.3, p.8 (definition of ≍)

import Mathlib

open Filter

namespace SmoothNestedSim

/-- **Same order `a_k ≍ b_k`** (Wang, Wang, Zhang, *Smooth Nested Simulation*,
arXiv:2201.02958v6, §1.3, p.8): "For two positive sequences `a_n` and `b_n`, we write …
`a_n ≍ b_n` if there exist some constants `C, C′ > 0` such that … `C′ ≤ a_n/b_n ≤ C` … for all
`n` large enough."

**Formalization Note.** The paper applies `≍` only to positive sequences; the definition is
stated for arbitrary real sequences, and every use in this mission compares positive ones
(sample sizes `≥ 1`, `λ > 0`, positive powers of the budget). -/
def IsAsympEquiv (a b : ℕ → ℝ) : Prop :=
  ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧ ∀ᶠ k in atTop, C' ≤ a k / b k ∧ a k / b k ≤ C

end SmoothNestedSim


