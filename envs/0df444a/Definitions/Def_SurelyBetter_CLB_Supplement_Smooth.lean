-- Prove2me | Definitions.Def_SurelyBetter_CLB_Supplement_Smooth
-- name    : SurelyBetter_CLB_Supplement_Smooth
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:47:47.658738+00:00
-- url     : https://prove2.me/theorems/579b1503-9f00-4b07-8635-6ad15683aede
-- title:
--   (5), p. 7622 — the smooth ambiguity functional ∫ φ(∑ₛ u(f(s))p(s)) dμ(p)
-- statement:
--   Let $S$ be a finite set of states and $\Delta(S)=\{p\in\mathbb R^S: p(s)\ge0,\ \sum_s p(s)=1\}$ the probability measures on $S$, with its Borel $\sigma$-algebra. For a function $\phi:\mathbb R\to\mathbb R$ and a measure $\mu$ on $\Delta(S)$ (the second-order belief), the **smooth ambiguity functional** of Klibanoff, Marinacci and Mukerji (2005), representation (5), evaluated at the utility profile $v=u\circ f$ of an act $f$, is
--   $$V_{\phi,\mu}(v)=\int_{\Delta(S)}\phi\Big(\sum_{s\in S}v(s)\,p(s)\Big)\,d\mu(p).$$
--
--   The model's assumptions — $\phi$ continuous and strictly increasing on the range of $u$, $\mu$ a countably additive probability measure — are not part of the definition; Theorems 3 and 4 state them as hypotheses.
--
--   **Formalization Note** $\Delta(S)$ is Mathlib's `stdSimplex ℝ S` with the subspace $\sigma$-algebra of the product Borel $\sigma$-algebra, and the integral is the Bochner integral. For profiles with values in $[0,\infty)$, the integrand is a continuous function of $p$ on the compact simplex whenever $\phi$ is continuous on $[0,\infty)$, so the integral is a genuine (bounded) integral and not Lean's junk value.
-- source:
--   Ghili & Klibanoff, If It Is Surely Better, Do It More? Implications for Preferences Under Ambiguity, Management Science 67(12) (2021), p. 7622, §2.2, representation (5)

import Mathlib

namespace SurelyBetter.CLB.Supplement
open MeasureTheory

/-- (5), p. 7622: the smooth ambiguity functional evaluated at a utility profile `v = u ∘ f`,
`∫ φ(∑ₛ v(s) p(s)) dμ(p)`, where `μ` is a measure on the probability measures over the finite
state space `S`, i.e. on the standard simplex `Δ(S)` with its Borel σ-algebra. -/
noncomputable def smoothV {S : Type*} [Fintype S] (φ : ℝ → ℝ)
    (μ : Measure (stdSimplex ℝ S)) (v : S → ℝ) : ℝ :=
  ∫ p, φ (∑ s, v s * (p : S → ℝ) s) ∂μ

end SurelyBetter.CLB.Supplement


