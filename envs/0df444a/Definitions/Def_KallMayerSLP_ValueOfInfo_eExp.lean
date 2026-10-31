-- Prove2me | Definitions.Def_KallMayerSLP_ValueOfInfo_eExp
-- name    : KallMayerSLP_ValueOfInfo_eExp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:12:37.433458+00:00
-- url     : https://prove2.me/theorems/4999d9c2-8b42-437d-a3ea-eeb7c20c6dcd
-- title:
--   Expectation $\mathbb E_\xi[f(\xi)]$ of an extended-real cost
-- statement:
--   Let $\mu=\mathbb P_\xi$ be the law of the random vector $\xi$ on $\mathbb R^r$ and $f:\mathbb R^r\to[-\infty,+\infty]$ a cost that may take the values $+\infty$ (an infeasible second stage) and $-\infty$ (an unbounded second stage). With $f^+=\max(f,0)$ and $f^-=\max(-f,0)$,
--
--   $$
--   \mathbb E_\xi[f(\xi)]=\begin{cases}+\infty, & \text{if } \int f^+\,d\mu=+\infty,\\ \int f^+\,d\mu-\int f^-\,d\mu, & \text{otherwise.}\end{cases}
--   $$
--
--   The book (p.200) notes that the expected recourse is $+\infty$ if the second stage is infeasible with positive probability, and undefined if moreover it equals $-\infty$ with positive probability, and that such a decision "is not to be chosen". The value $+\infty$ in the undefined case encodes exactly this exclusion in the minimization defining $RS$.
--
--   **Formalization Note** $f^\pm$ are $[0,\infty]$-valued and integrated with the Lebesgue integral `∫⁻`, so a non-integrable cost is never silently sent to $0$. When $\int f^+d\mu<\infty$ this is the usual expectation, with value in $[-\infty,\infty)$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, §2, p.200 (PDF 209): expected recourse 𝒬(x̂) = +∞ or undefined

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.ValueOfInfo

/-- **Expectation `𝔼_ξ[f(ξ)]` of an extended-real-valued cost.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, p.200 (PDF 209): the recourse
function may equal `+∞` (infeasible second stage) or `−∞` (unbounded second stage), and then
"either `𝒬(x̂) := 𝔼_ξ[Q(x̂; …)] = +∞`, or else the expected recourse `𝒬(x̂)` [is] undefined if with
positive probability `Q = −∞` results simultaneously. Clearly in anyone of these situations `x̂` is
not to be chosen".

For a law `μ` of `ξ` on `ℝʳ` and `f : ℝʳ → [−∞, +∞]` this is `∫ f⁺ dμ − ∫ f⁻ dμ`, with the value
`+∞` whenever `∫ f⁺ dμ = +∞` (in particular in the undefined case `∞ − ∞`).

**Formalization Note.** `f⁺ = max(f, 0)` and `f⁻ = max(−f, 0)` are taken as `ℝ≥0∞`-valued
(`EReal.toENNReal`), and their integrals are Lebesgue integrals `∫⁻`, so no integrability
hypothesis is hidden in the definition (a non-integrable cost is not silently sent to `0`). The
book leaves `∞ − ∞` undefined and excludes such decisions from the minimization; the value `+∞`
encodes exactly that exclusion in the minimizations `RS`, and in `WS`, `EEV` it is the
monotone ("upper") convention. When `f⁺` is integrable this is the usual expectation in
`[−∞, +∞)`. -/
noncomputable def eExp {r : ℕ} (μ : Measure (Fin r → ℝ)) (f : (Fin r → ℝ) → EReal) : EReal :=
  if ∫⁻ ξ, (f ξ).toENNReal ∂μ = ∞ then ⊤
  else ((∫⁻ ξ, (f ξ).toENNReal ∂μ : ℝ≥0∞) : EReal) - ((∫⁻ ξ, (-f ξ).toENNReal ∂μ : ℝ≥0∞) : EReal)

end KallMayerSLP.ValueOfInfo


