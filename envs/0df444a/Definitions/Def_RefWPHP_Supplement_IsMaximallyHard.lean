-- Prove2me | Definitions.Def_RefWPHP_Supplement_IsMaximallyHard
-- name    : RefWPHP_Supplement_IsMaximallyHard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:21:48.555546+00:00
-- url     : https://prove2.me/theorems/006568d3-fa45-4b76-abf9-90adcc2a8508
-- title:
--   Definition 4.2 — maximally hard families for Resolution, with explicit constant $\varepsilon$
-- statement:
--   Let $\varphi = \{\varphi_n\}_{n \in \mathbb N}$ be a family of unsatisfiable CNF formulas, $\varphi_n$ with $n$ variables and $M(n) = \mathrm{poly}(n)$ clauses, and let $\varepsilon > 0$. The family is **maximally hard with constant $\varepsilon$** if for every large enough $n$, every Resolution refutation of $\varphi_n$ has length at least
--
--   $$
--   2^{\varepsilon n}.
--   $$
--
--   The paper's maximally hard families ("length $2^{\Omega(n)}$") are those that are maximally hard with some constant $\varepsilon > 0$.
--
--   **Formalization Note** "$\mathrm{poly}(n)$ clauses" is $M(n) \le (n+2)^a$ for one exponent $a$. Refutations and their length are those of `ResRefutation`.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), Definition 4.2, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_RefWPHP_Supplement_Unsat
import Definitions.Def_RefWPHP_Supplement_ResRefutation

namespace RefWPHP

namespace Supplement

/-- Definition 4.2 (Maximally hard formulas) of N. Arteche, *Resolution Lower Bounds versus the
Weak Pigeonhole Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), p.35
(PDF 37), with the constant of `2^{Ω(n)}` made explicit: `IsMaximallyHard M φ ε` says that
`φ = {φ_n}` is a family of unsatisfiable CNF formulas, `φ_n` with `n` variables and `M n = poly(n)`
clauses, such that for every large enough `n` every Resolution refutation of `φ_n` has length at
least `2^{ε n}`. The paper's "maximally hard family" is `∃ ε > 0, IsMaximallyHard M φ ε`.

**Formalization Note.** "`poly(n)` clauses" is `M n ≤ (n + 2)^a` for one exponent `a`. -/
def IsMaximallyHard (M : ℕ → ℕ) (φ : (n : ℕ) → Fin (M n) → Finset (Lit n)) (ε : ℝ) : Prop :=
  (∀ n, Unsat (φ n)) ∧
  (∃ a : ℕ, ∀ n, M n ≤ (n + 2) ^ a) ∧
  0 < ε ∧
  ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ π : ResRefutation (φ n), (2 : ℝ) ^ (ε * n) ≤ (π.length : ℝ)

end Supplement

end RefWPHP


