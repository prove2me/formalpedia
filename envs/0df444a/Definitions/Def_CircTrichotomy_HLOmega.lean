-- Prove2me | Definitions.Def_CircTrichotomy_HLOmega
-- name    : CircTrichotomy_HLOmega
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:47.076206+00:00
-- url     : https://prove2.me/theorems/661ac8f7-6436-4aaf-ab18-3786278268d7
-- title:
--   Hardy–Littlewood $f\in\Omega(g)$
-- statement:
--   **Hardy–Littlewood $\Omega$.** For functions $f,g$ on the positive integers with values in $\mathbb R_{\ge0}$, $f\in\Omega(g)$ means that there is a constant $c>0$ with
--   $$f(n)\ge c\,g(n)\quad\text{for infinitely many } n.$$
--   Thus $f\in\Omega(g)$ iff $f\notin o(g)$.
--
--   This weaker lower-bound notion (not Knuth's "for all large $n$") is the one used in the trichotomy: a language may have trivial circuits at infinitely many lengths, e.g. when it has no words of odd length.
--
--   **Formalization Note** "Infinitely many $n$" is "for every $N$ there is $n\ge N$".
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition A.1, p.17

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

/-- **Hardy–Littlewood Ω** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular
Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition A.1,
p.17): "For two functions f, g : ℕ>0 → ℝ≥0 we write f ∈ Ω(g) if there exists c ∈ ℝ>0 such that
f(n) ≥ c · g(n) for infinitely many n ∈ ℕ>0."

**Formalization Note** "For infinitely many n" is `∀ N, ∃ n ≥ N`. This is the Hardy–Littlewood
Ω, not Knuth's (which would require the bound for all large n). -/
def HLOmega (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n ≥ N, c * g n ≤ f n

end CircTrichotomy


