-- Prove2me | Definitions.Def_ModelRiskOT_PrimalOpt_PCompactness
-- name    : ModelRiskOT_PrimalOpt_PCompactness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:51:35.467339+00:00
-- url     : https://prove2.me/theorems/fa67807b-7c8b-4291-b68f-6ff9baed156b
-- title:
--   Property 1 (P-Compactness) of Proposition 9 (p. 26)
-- statement:
--   Let $S$ be a Polish space, $\mu$ a probability measure on $S$, $c$ a cost, $f$ a function and $\lambda^*\ge0$ a multiplier, with $\varphi_{\lambda^*}(x)=\sup_{y}\{f(y)-\lambda^*c(x,y)\}$. For a set $K\subseteq S$ and $\gamma>0$ put
--   $$\Gamma(K,\gamma)=\bigl\{(x,y)\in K\times S:\ f(y)-\lambda^*c(x,y)\ge\varphi_{\lambda^*}(x)-\gamma\bigr\}.$$
--   The pair $(c,f)$ has **Property (P-Compactness)** at $\lambda^*$ if for every $\varepsilon>0$ there is a compact $K_\varepsilon\subseteq S$ with $\mu(K_\varepsilon)>1-\varepsilon$ and some $\gamma\in(0,\infty)$ such that the closure $\mathrm{cl}(\Gamma(K_\varepsilon,\gamma))$ is compact in $S\times S$.
--
--   The property says that the near-maximizers $y$ of $f(y)-\lambda^*c(x,y)$ stay in a compact region when $x$ ranges over a set of large $\mu$-mass; it is what makes nearly optimal transport plans tight.
--
--   **Formalization Note** The constant $\gamma$ may depend on $\varepsilon$, which is how the proof of Proposition 9 uses it. The inequality defining $\Gamma$ is evaluated in $\overline{\mathbb R}$, so a point $x$ with $\varphi_{\lambda^*}(x)=+\infty$ contributes nothing to $\Gamma$. The bound $\mu(K_\varepsilon)>1-\varepsilon$ is stated on the real value of $\mu(K_\varepsilon)$, which is finite.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 26, Proposition 9, Property 1 (P-Compactness)

import Mathlib
import Definitions.Def_ModelRiskOT_PrimalOpt_Basic

namespace ModelRiskOT.PrimalOpt

open MeasureTheory

/-- The set `Γ = {(x, y) ∈ K × S : f(y) − λ c(x, y) ≥ φ_λ(x) − γ}` of Property 1 (p. 26), computed in
`EReal` (a point `x` with `φ_λ(x) = +∞` contributes nothing). -/
def gammaSet {S : Type*} (c : S → S → ℝ) (f : S → ℝ) (lam : ℝ) (K : Set S) (γ : ℝ) :
    Set (S × S) :=
  {p | p.1 ∈ K ∧ phiLam c f lam p.1 - (γ : EReal) ≤ ((f p.2 - lam * c p.1 p.2 : ℝ) : EReal)}

/-- **Property 1 (P-Compactness)** of Proposition 9 (p. 26), for the multiplier `λ = λ*`: for every
`ε > 0` there is a compact `K_ε ⊆ S` with `μ(K_ε) > 1 − ε` and some `γ ∈ (0, ∞)` (which may depend
on `ε`) such that the closure of `Γ_ε = {(x, y) ∈ K_ε × S : f(y) − λ* c(x, y) ≥ φ_{λ*}(x) − γ}` is
compact. -/
def PCompactness {S : Type*} [TopologicalSpace S] [MeasurableSpace S] (c : S → S → ℝ)
    (f : S → ℝ) (μ : Measure S) (lam : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : Set S, IsCompact K ∧ 1 - ε < (μ K).toReal ∧
    ∃ γ : ℝ, 0 < γ ∧ IsCompact (closure (gammaSet c f lam K γ))

end ModelRiskOT.PrimalOpt


