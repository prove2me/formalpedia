-- Prove2me | Definitions.Def_RefWPHP_Supplement_IsNaturallyTight
-- name    : RefWPHP_Supplement_IsNaturallyTight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:21:21.565294+00:00
-- url     : https://prove2.me/theorems/505963bd-fb68-4b13-b2df-eadf7d676c37
-- title:
--   Definition 4.3 — naturally tight Resolution lower bounds
-- statement:
--   Let $\varphi = \{\varphi_n\}_{n \in \mathbb N}$ be a family of unsatisfiable CNF formulas, $\varphi_n$ with $N(n) = \mathrm{poly}(n)$ variables and $M(n) = \mathrm{poly}(n)$ clauses. The family **admits a naturally tight Resolution lower bound** $s : \mathbb N \to \mathbb N$ if $s(n) \ge n^{\Omega(1)}$ and there are constants $c \in \mathbb N$ and $\eta > 0$ such that for every large enough $n$:
--
--   1. every Resolution refutation of $\varphi_n$ has length at least $s(n)$; yet
--   2. some Resolution refutation of $\varphi_n$ has length at most $s(n)^c$ and depth at most $s(n)^{1-\eta}$.
--
--   The depth condition keeps the number of holes in the reduction of Theorem 3.2, which is proportional to $s/D$, polynomially large in $s$.
--
--   **Formalization Note** "$\mathrm{poly}(n)$" is $\le (n+2)^a$ for one exponent $a$; "$s(n) \ge n^{\Omega(1)}$" is the existence of a real $b > 0$ and $n_1$ with $n^b \le s(n)$ for all $n \ge n_1$. Refutations, length and depth are those of `ResRefutation`; the depth is compared with $s(n)^{1-\eta}$ as a real number.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), Definition 4.3, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_RefWPHP_Supplement_Unsat
import Definitions.Def_RefWPHP_Supplement_ResRefutation

namespace RefWPHP

namespace Supplement

/-- Definition 4.3 (Naturally tight lower bounds) of N. Arteche, *Resolution Lower Bounds versus
the Weak Pigeonhole Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), p.35
(PDF 37): a family `φ = {φ_n}` of unsatisfiable CNF formulas, `φ_n` with `N n = poly(n)` variables
and `M n = poly(n)` clauses, admits a naturally tight Resolution lower bound `s : ℕ → ℕ` if
`s(n) ≥ n^{Ω(1)}` and there are constants `c ∈ ℕ` and `η > 0` such that for every large enough `n`,

* (i) every Resolution refutation of `φ_n` has length at least `s(n)`; yet
* (ii) some Resolution refutation of `φ_n` has length at most `s(n)^c` and depth at most
  `s(n)^{1-η}`.

**Formalization Note.**
1. "`poly(n)`" is `≤ (n + 2)^a` for one exponent `a`; "`s(n) ≥ n^{Ω(1)}`" is: there are a real
   `b > 0` and `n₁` with `n^b ≤ s(n)` for `n ≥ n₁`.
2. Depth is compared as a real number with `s(n)^{1-η}`. -/
def IsNaturallyTight (N M : ℕ → ℕ) (φ : (n : ℕ) → Fin (M n) → Finset (Lit (N n)))
    (s : ℕ → ℕ) : Prop :=
  (∀ n, Unsat (φ n)) ∧
  (∃ a : ℕ, ∀ n, N n ≤ (n + 2) ^ a ∧ M n ≤ (n + 2) ^ a) ∧
  (∃ b : ℝ, 0 < b ∧ ∃ n₁ : ℕ, ∀ n ≥ n₁, (n : ℝ) ^ b ≤ (s n : ℝ)) ∧
  ∃ c : ℕ, ∃ η : ℝ, 0 < η ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    (∀ π : ResRefutation (φ n), s n ≤ π.length) ∧
    ∃ π : ResRefutation (φ n), π.length ≤ s n ^ c ∧
      ∃ D : ℕ, π.DepthAtMost D ∧ (D : ℝ) ≤ (s n : ℝ) ^ (1 - η)

end Supplement

end RefWPHP


