-- Prove2me | Definitions.Def_QuerySampleRev_Supplement_IsMHR
-- name    : QuerySampleRev_Supplement_IsMHR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:16:57.563338+00:00
-- url     : https://prove2.me/theorems/b307dd1f-16b9-40a9-b2dd-a5c935ae608c
-- title:
--   MHR distributions (Definition 2): convex cumulative hazard $H(p)=-\log Q(p)$
-- statement:
--   A value distribution with sale probability $Q$ satisfies the **monotone-hazard-rate (MHR)** condition if its cumulative hazard
--   $$
--   H(p)=-\log Q(p),\qquad\text{with value }+\infty\text{ when }Q(p)=0,
--   $$
--   is convex on $[0,\infty)$: for all $x,y\ge0$ and $\theta\in[0,1]$,
--   $$
--   H(\theta x+(1-\theta)y)\le\theta H(x)+(1-\theta)H(y),
--   $$
--   where the right-hand side may be $+\infty$. MHR distributions are regular and quasi-MHR; they are the family of Theorems 26, 27, 39 and 40.
--
--   **Formalization Note** $H$ takes values in the extended reals and the chord inequality is evaluated there ($0\cdot(+\infty)=0$). No density is assumed, so distributions with atoms or bounded support (a point mass, a uniform law on $[0,a]$) are admitted, as Definition 2 allows; the hazard-rate formulation is only an equivalent form for laws with a positive density.
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Definition 2, p.12 (PDF p.14), with the convention 'value +∞ when Q(p) = 0' of Definition 3 (λ = 0)

import Mathlib
import Definitions.Def_QuerySampleRev_rStar

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev.Supplement

open QuerySampleRev

/-- **Cumulative hazard `H(p) = −log Q(p)`.** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue
Maximization* (manuscript, sha256 c31ea3d3…), Definition 2, p.12 (PDF 14): "its cumulative hazard function,
denoted by `H(p) ≜ − log Q(p)`"; Definition 3 with `λ = 0`, p.12: "with value `+∞` when `Q(p) = 0`".

**Formalization Note.** Valued in `EReal`: `⊤` when `Q(p) = μ([p, ∞)) = 0`, the real number `−log Q(p)`
(natural logarithm) otherwise. -/
noncomputable def cumHazard (μ : Measure ℝ) (p : ℝ) : EReal :=
  if saleProb μ p = 0 then ⊤ else ((-Real.log (saleProb μ p).toReal : ℝ) : EReal)

/-- **MHR distribution.** Same source, Definition 2 (MHR Distributions), p.12 (PDF 14): "A distribution `F`
satisfies the monotone-hazard-rate (MHR) condition if its cumulative hazard function, denoted by
`H(p) ≜ − log Q(p)`, is convex"; Definition 3 (`λ = 0`): convex "with value `+∞` when `Q(p) = 0`".

`IsMHR μ` says that `H` is convex on the price range `[0, ∞)` as an extended-real function: for all
`x, y ≥ 0` and `θ ∈ [0, 1]`, `H(θx + (1 − θ)y) ≤ θ H(x) + (1 − θ) H(y)`, where the right side may be `+∞`.

**Formalization Note.** The chord inequality is stated in `EReal`, where `0 · ⊤ = 0` and `θ · ⊤ = ⊤` for
`θ > 0`, so the usual convention for extended-valued convex functions applies; no density is assumed, so
laws with atoms or bounded support (a point mass, the uniform law on `[0, a]`) are admitted, as the paper's
Definition 2 allows. -/
def IsMHR (μ : Measure ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
    cumHazard μ (θ * x + (1 - θ) * y) ≤
      ((θ : ℝ) : EReal) * cumHazard μ x + ((1 - θ : ℝ) : EReal) * cumHazard μ y

end QuerySampleRev.Supplement


