-- Prove2me | Definitions.Def_ZKSheafPCP_IsPolynomial
-- name    : ZKSheafPCP_IsPolynomial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:09:40.873238+00:00
-- url     : https://prove2.me/theorems/1b7f2b17-2614-451c-965a-51bb9bff1fe9
-- title:
--   Polynomial and polynomially bounded functions $\mathbb N\to\mathbb N$
-- statement:
--   A function $f:\mathbb N\to\mathbb N$ is **polynomial** if there is a real polynomial $p$ with $f(n)=p(n)$ for every $n\in\mathbb N$. It is **polynomially bounded** if $f(n)\le (n+2)^K$ for some $K$ and every $n$.
--
--   The first notion is the hypothesis on the time bound $T$ and the query bound $b$ in the main theorem. The second is the meaning of "polynomial" for running times and coin lengths.
--
--   **Formalization Note** The polynomial is real, so that $n(n-1)/2$ and $n^2-n$ are included; polynomials with natural coefficients would narrow the domain of the theorem.
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Theorem 9.2, p.42; Definition 3.24, p.13

import Mathlib

namespace ZKSheafPCP

/-- "Polynomial" for a function `b, T : ℕ → ℕ` (Zeilberger, O'Connor, Gur, Spooner, *Zero-Knowledge
PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes*, STOC 2027 submission, manuscript sha256
ac5e528f…, Theorem 9.2, p.42: "For every polynomial `b, T : ℕ → ℕ`").

**Formalization Note** A polynomial is a function with values in `ℕ` that agrees on `ℕ` with a real
polynomial, so `n(n-1)/2` and `n² - n` are included. `ℕ[X]` would narrow the domain. -/
def IsPolynomial (f : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℝ, ∀ n : ℕ, (f n : ℝ) = p.eval (n : ℝ)

/-- A polynomially bounded function: `f n ≤ (n + 2) ^ K` for some `K`. This is the meaning of "poly"
for running times and coin lengths (Definition 3.24, p.13: "PPT"). -/
def PolyBdd (f : ℕ → ℕ) : Prop :=
  ∃ K : ℕ, ∀ n : ℕ, f n ≤ (n + 2) ^ K

end ZKSheafPCP


