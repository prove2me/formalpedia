-- Prove2me | Definitions.Def_BertsekasShreve_FiniteHorizon_Assumptions
-- name    : BertsekasShreve_FiniteHorizon_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:15:08.14457+00:00
-- url     : https://prove2.me/theorems/ddd58691-12ca-46db-b168-75fe172b9c64
-- title:
--   Assumptions F.1, F.2 and F.3 of Chapter 3
-- statement:
--   Three assumptions on the mapping $H$ of a model $(S,C,U,H)$, each sufficient for parts of the finite-horizon theory.
--
--   **Assumption F.1.** If $\{J_k\}\subset F$ satisfies $J_{k+1}\le J_k$ for all $k$ and $H(x,u,J_1)<\infty$ for all $x\in S$, $u\in U(x)$, then
--   $$\lim_{k\to\infty}H(x,u,J_k)=H\Bigl(x,u,\lim_{k\to\infty}J_k\Bigr)\qquad\forall x\in S,\ u\in U(x).$$
--
--   **Assumption F.2.** There is a scalar $\alpha\in(0,\infty)$ such that for all scalars $r\in(0,\infty)$ and all $J\in F$,
--   $$H(x,u,J)\le H(x,u,J+r)\le H(x,u,J)+\alpha r\qquad\forall x\in S,\ u\in U(x).$$
--   The inequality for a given $\alpha$ is recorded separately so that results can name the constant.
--
--   **Assumption F.3.** There is a scalar $\beta\in(0,\infty)$ such that if $J\in F$, $\{J_n\}\subset F$ and $\{\varepsilon_n\}\subset R$ satisfy $\sum_{n=1}^\infty\varepsilon_n<\infty$, $\varepsilon_n>0$; $J=\lim_{n}J_n$, $J\le J_n$; $J_n(x)\le J(x)+\varepsilon_n$ for $n\ge1$ and $x$ with $J(x)>-\infty$; $J_n(x)\le J_{n-1}(x)+\varepsilon_n$ for $n\ge2$ and $x$ with $J(x)=-\infty$; and $H(x,u,J_1)<\infty$ for all $x\in S$, $u\in U(x)$; then there is a sequence $\{\mu_n\}\subset M$ with $\lim_n T_{\mu_n}(J_n)=T(J)$ and
--   $$T_{\mu_n}(J_n)(x)\le\begin{cases}T(J)(x)+\beta\varepsilon_n,& n\ge1,\ T(J)(x)>-\infty,\\ T_{\mu_{n-1}}(J_{n-1})(x)+\beta\varepsilon_n,& n\ge2,\ T(J)(x)=-\infty.\end{cases}$$
--
--   F.1 is a continuity property of $H$ along decreasing sequences, F.2 a uniform bound on the effect of a constant shift, and F.3 a quantitative selection property; the book shows that each specific model of Section 2.3 satisfies at least one of them.
--
--   **Formalization Note** In F.1 the sequence is indexed from $0$, so the finiteness hypothesis is placed on its first term `J 0` (the book's $J_1$); because both limits depend only on the tail of the sequence, this is the same assumption. The limit $\lim_k J_k$ is a pointwise limit in `EReal`, given as a function `Jlim` with `Tendsto`. In F.3 sequences are indexed by `ℕ` with index $0$ unused; $\sum_{n\ge1}\varepsilon_n<\infty$ is `Summable (fun n => ε (n+1))`. Adding the real number $r$ or $\varepsilon_n$ to an extended real is the usual operation (no $\infty-\infty$ arises).
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 39, Assumption F.1; p. 40, Assumptions F.2 and F.3

import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model

namespace BertsekasShreve.FiniteHorizon

open Filter Topology

namespace Model

variable {S C : Type*} (m : Model S C)

/-- Assumption F.1 (p. 39): if `{J_k} ⊂ F` satisfies `J_{k+1} ≤ J_k` for all `k` and
`H(x, u, J₁) < ∞` for all `x ∈ S`, `u ∈ U(x)` (the first term of the sequence), then
`lim_{k→∞} H(x, u, J_k) = H(x, u, lim_{k→∞} J_k)` for all `x ∈ S`, `u ∈ U(x)`.
The sequence is indexed from `0` here, so its first term is `J 0`; `Jlim` is its pointwise
limit, which exists in `R*` because the sequence is nonincreasing. -/
def AssumptionF1 : Prop :=
  ∀ J : ℕ → S → EReal, (∀ k, J (k + 1) ≤ J k) →
    (∀ x, ∀ u ∈ m.U x, m.H x u (J 0) < ⊤) →
    ∀ Jlim : S → EReal, (∀ x, Tendsto (fun k => J k x) atTop (𝓝 (Jlim x))) →
      ∀ x, ∀ u ∈ m.U x, Tendsto (fun k => m.H x u (J k)) atTop (𝓝 (m.H x u Jlim))

/-- The inequality of Assumption F.2 for a given scalar `α`: for all scalars `r ∈ (0, ∞)` and
`J ∈ F`, `H(x, u, J) ≤ H(x, u, J + r) ≤ H(x, u, J) + α r` for all `x ∈ S`, `u ∈ U(x)`. -/
def F2With (α : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ J : S → EReal, ∀ x, ∀ u ∈ m.U x,
    m.H x u J ≤ m.H x u (fun y => J y + (r : EReal)) ∧
      m.H x u (fun y => J y + (r : EReal)) ≤ m.H x u J + ((α * r : ℝ) : EReal)

/-- Assumption F.2 (p. 40): there exists a scalar `α ∈ (0, ∞)` for which `F2With α` holds. -/
def AssumptionF2 : Prop := ∃ α : ℝ, 0 < α ∧ m.F2With α

/-- Assumption F.3 (p. 40), with all sequences indexed by `n = 1, 2, …` (index `0` unused).
There is a scalar `β ∈ (0, ∞)` such that if `J ∈ F`, `{J_n} ⊂ F` and `{ε_n} ⊂ R` satisfy
`∑_{n=1}^∞ ε_n < ∞`, `ε_n > 0`; `J = lim J_n`, `J ≤ J_n`;
`J_n(x) ≤ J(x) + ε_n` (`n ≥ 1`, `J(x) > −∞`), `J_n(x) ≤ J_{n−1}(x) + ε_n` (`n ≥ 2`, `J(x) = −∞`);
and `H(x, u, J₁) < ∞` for all `x ∈ S`, `u ∈ U(x)`, then there is a sequence `{μ_n} ⊂ M` with
`lim T_{μ_n}(J_n) = T(J)`,
`T_{μ_n}(J_n)(x) ≤ T(J)(x) + β ε_n` (`n ≥ 1`, `T(J)(x) > −∞`), and
`T_{μ_n}(J_n)(x) ≤ T_{μ_{n−1}}(J_{n−1})(x) + β ε_n` (`n ≥ 2`, `T(J)(x) = −∞`). -/
def AssumptionF3 : Prop :=
  ∃ β : ℝ, 0 < β ∧
    ∀ (J : S → EReal) (Js : ℕ → S → EReal) (ε : ℕ → ℝ),
      Summable (fun n => ε (n + 1)) →
      (∀ n, 1 ≤ n → 0 < ε n) →
      (∀ x, Tendsto (fun n => Js n x) atTop (𝓝 (J x))) →
      (∀ n, 1 ≤ n → J ≤ Js n) →
      (∀ n, 1 ≤ n → ∀ x, J x ≠ ⊥ → Js n x ≤ J x + (ε n : EReal)) →
      (∀ n, 2 ≤ n → ∀ x, J x = ⊥ → Js n x ≤ Js (n - 1) x + (ε n : EReal)) →
      (∀ x, ∀ u ∈ m.U x, m.H x u (Js 1) < ⊤) →
      ∃ μs : ℕ → m.Selector,
        (∀ x, Tendsto (fun n => m.Tmu (μs n) (Js n) x) atTop (𝓝 (m.T J x))) ∧
        (∀ n, 1 ≤ n → ∀ x, m.T J x ≠ ⊥ →
          m.Tmu (μs n) (Js n) x ≤ m.T J x + ((β * ε n : ℝ) : EReal)) ∧
        (∀ n, 2 ≤ n → ∀ x, m.T J x = ⊥ →
          m.Tmu (μs n) (Js n) x ≤
            m.Tmu (μs (n - 1)) (Js (n - 1)) x + ((β * ε n : ℝ) : EReal))

end Model

end BertsekasShreve.FiniteHorizon


