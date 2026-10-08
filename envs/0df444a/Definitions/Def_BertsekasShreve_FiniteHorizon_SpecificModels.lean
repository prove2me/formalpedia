-- Prove2me | Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels
-- name    : BertsekasShreve_FiniteHorizon_SpecificModels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:51:32.279183+00:00
-- url     : https://prove2.me/theorems/0d5f0630-b9fe-466f-a955-823bf20fa0f4
-- title:
--   The multiplicative-cost mapping (Section 2.3.4) and the minimax mapping (Section 2.3.5), with the book's ∞ − ∞ = ∞
-- statement:
--   Two concrete mappings $H$ from Section 2.3, written with the book's arithmetic in $R^*$.
--
--   **Book addition.** $a\oplus b=a+b$, except that $\infty-\infty=-\infty+\infty=\infty$ (Section 2.1, item (6)). Mathlib's `EReal` instead sets $(-\infty)+\infty=-\infty$; $\oplus$ differs from it only on that pair.
--
--   **Expectation on a countable set** (Section 2.3.2). For a probability distribution $p$ on a countable set $W$ and $z:W\to R^*$,
--   $$E\{z(w)\}=\sum_{w}p(w)z^+(w)-\sum_{w}p(w)z^-(w),\qquad z^+=\max\{0,z\},\ z^-=\max\{0,-z\},$$
--   with $\infty-\infty=\infty$.
--
--   **Multiplicative cost** (Section 2.3.4, eq. (26) of Chapter 2 = eq. (33) of Chapter 3). With $p(\cdot\mid x,u)$ a probability distribution on the countable set $W$, $g:S\times C\times W\to R^*$ and $f:S\times C\times W\to S$,
--   $$H(x,u,J)=E\{g(x,u,w)J[f(x,u,w)]\mid x,u\}.$$
--
--   **Minimax control** (Section 2.3.5, eq. (29) of Chapter 2 = eq. (34) of Chapter 3). With $W(x,u)\subseteq W$, $g:S\times C\times W\to[-\infty,\infty]$, $f:S\times C\times W\to S$ and a scalar $\alpha$,
--   $$H(x,u,J)=\sup_{w\in W(x,u)}\{g(x,u,w)+\alpha J[f(x,u,w)]\}.$$
--
--   These mappings are the inputs of Propositions 3.6 and 3.7; the hypotheses the book places on them ($g\ge0$, $W(x,u)\ne\emptyset$, $\alpha>0$) are stated in those theorems.
--
--   **Formalization Note** $p(\cdot\mid x,u)$ is a Mathlib `PMF W` (values in $[0,\infty]$ summing to $1$); the two series are `tsum`s in $[0,\infty]$, $z^\pm$ is `EReal.toENNReal` of $\pm z$, and the difference is $+\infty$ when the positive series is infinite. Products use `EReal` multiplication, which has $0\cdot(\pm\infty)=0$ and the book's sign rules. The type $W$ carries no countability assumption in Lean: a `PMF` has countable support, so the two series coincide with the book's sums over a countable $W$, and for a countable $W$ (the book's case) nothing changes.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 26, Section 2.1, item (6); p. 31, Section 2.3.2 (definition of E); p. 37, Section 2.3.4, eq. (26) of Chapter 2; p. 38, Section 2.3.5, eq. (29) of Chapter 2

import Mathlib

namespace BertsekasShreve.FiniteHorizon

open scoped ENNReal

/-- Addition in `R*` with the book's convention `∞ − ∞ = −∞ + ∞ = ∞` (Section 2.1, item (6),
p. 26). It differs from `EReal`'s `+`, where `⊥ + ⊤ = ⊥`, only on that pair. -/
noncomputable def badd (a b : EReal) : EReal := if a = ⊤ ∨ b = ⊤ then ⊤ else a + b

/-- Expected value with respect to a probability distribution `p` on a countable set `W`
(Section 2.3.2, p. 31): `E{z(w)} = ∑ p(w) z⁺(w) − ∑ p(w) z⁻(w)`, with
`z⁺ = max{0, z}`, `z⁻ = max{0, −z}` and the convention `∞ − ∞ = ∞`. -/
noncomputable def expect {W : Type*} (p : PMF W) (z : W → EReal) : EReal :=
  let P : ℝ≥0∞ := ∑' w, p w * (z w).toENNReal
  let Q : ℝ≥0∞ := ∑' w, p w * (-(z w)).toENNReal
  if P = ⊤ then ⊤ else (P : EReal) - (Q : EReal)

/-- The mapping of the multiplicative cost model, eq. (26) of Chapter 2 (Section 2.3.4,
p. 37) = eq. (33) of Chapter 3:
`H(x, u, J) = E{g(x, u, w) J[f(x, u, w)] | x, u}`, where `w` ranges over a countable set `W`
with probability distribution `p(· | x, u)`, `g : S C W → R*` and `f : S C W → S`. -/
noncomputable def multiplicativeH {S C W : Type*} (p : S → C → PMF W)
    (g : S → C → W → EReal) (f : S → C → W → S) : S → C → (S → EReal) → EReal :=
  fun x u J => expect (p x u) (fun w => g x u w * J (f x u w))

/-- The mapping of the minimax control model, eq. (29) of Chapter 2 (Section 2.3.5, p. 38) =
eq. (34) of Chapter 3:
`H(x, u, J) = sup_{w ∈ W(x,u)} {g(x, u, w) + α J[f(x, u, w)]}`, where `W(x, u) ⊆ W`,
`g : S C W → [−∞, ∞]`, `f : S C W → S`, `α` a scalar, and the sum uses the book's
convention `∞ − ∞ = ∞` (`badd`). -/
noncomputable def minimaxH {S C W : Type*} (Wset : S → C → Set W) (g : S → C → W → EReal)
    (f : S → C → W → S) (α : ℝ) : S → C → (S → EReal) → EReal :=
  fun x u J => ⨆ w ∈ Wset x u, badd (g x u w) ((α : EReal) * J (f x u w))

end BertsekasShreve.FiniteHorizon


