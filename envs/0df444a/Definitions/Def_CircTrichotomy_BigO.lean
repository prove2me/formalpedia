-- Prove2me | Definitions.Def_CircTrichotomy_BigO
-- name    : CircTrichotomy_BigO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:45.505899+00:00
-- url     : https://prove2.me/theorems/59054ae8-f234-4a3e-85d9-b085ac396d2f
-- title:
--   $f\in O(g)$
-- statement:
--   For functions $f,g$ on the positive integers with values in $\mathbb R_{\ge0}$, $f\in O(g)$ means that there is a constant $c>0$ with
--   $$f(n)\le c\,g(n)\quad\text{for all but finitely many } n.$$
--
--   This is the upper-bound notation of all size and depth bounds of the mission.
--
--   **Formalization Note** $f,g:\mathbb N\to\mathbb R$; "all but finitely many" is "for all $n\ge N$", so the value at $n=0$ is irrelevant.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.4.1, p.17

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

/-- **Big-O** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*,
arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.4.1, p.17): "Consider two
functions f, g : ℕ>0 → ℝ≥0. As usual, we write f ∈ O(g) if there exists c ∈ ℝ>0 such that
f(n) ≤ c·g(n) for all but finitely many n ∈ ℕ>0."

**Formalization Note** The functions are `ℕ → ℝ`; "for all but finitely many n" is
`∃ N, ∀ n ≥ N`, so the value at `n = 0` (outside the paper's domain ℕ>0) is never seen. -/
def BigO (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, f n ≤ c * g n

end CircTrichotomy


