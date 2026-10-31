-- Prove2me | Definitions.Def_ScarceIdeas_IsBellmanFixedPoint
-- name    : ScarceIdeas_IsBellmanFixedPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:53.087534+00:00
-- url     : https://prove2.me/theorems/589bfb47-8b8b-4b19-9159-707fad0a5f4a
-- title:
--   Fixed point of the discrete-time Bellman operator, equations (17)–(18)
-- statement:
--   For a time step $\Delta t$, a function $W$ is a **fixed point of the Bellman operator** $T(\Delta t)$ when it lies in the space $S$ of continuous functions from $\phi\in\mathbb R_+$ to $[0,v/r-\underline c]$ and, for every $\phi\ge0$,
--
--   $$W(\phi)=\max_{p\in[\underline c,\overline c]}\Bigl\{m_1(\phi)\Delta t\int_{\underline c}^{p}\Bigl(\frac vr-c\Bigr)f(c)\,dc+\bigl(1-m_1(\phi)\Delta tF(p)\bigr)(1-r\Delta t)\,W\bigl(\phi+F(p)\Delta t\bigr)\Bigr\}.$$
--
--   This is the discrete-time value $V^{\Delta t}$ of the recursion (17)–(18): the current payoff of a viable idea plus the discounted continuation payoff if no idea is invested.
--
--   **Formalization Note** The maximum is stated with `IsGreatest`, so it exists and equals $W(\phi)$. The restriction to small $\Delta t$ is made where the definition is used.
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, §4.2, (17)–(18), p.21; Appendix, proof of Theorem 3, Part 1, p.36

import Mathlib
import Definitions.Def_ScarceIdeas_moment
import Definitions.Def_ScarceIdeas_costCDF

namespace ScarceIdeas

/-- **Fixed point of the discrete-time Bellman operator `T(Δt)`, equations (17)–(18).**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
§4.2, (17)–(18), p.21, and Appendix, proof of Theorem 3, Part 1, p.36 (the space `S` and the
operator `T(Δt)`).

`IsBellmanFixedPoint r v cL cH f h0 Δt W` says that `W` lies in the space `S` of continuous
functions from `ϕ ∈ ℝ₊` to `[0, v/r − c̲]`, and that for every `ϕ ≥ 0`

$$W(\phi)=\max_{p\in[\underline c,\overline c]}\Bigl\{m_1(\phi)\Delta t
\int_{\underline c}^{p}\Bigl(\frac vr-c\Bigr)f(c)\,dc
+\bigl(1-m_1(\phi)\Delta tF(p)\bigr)(1-r\Delta t)\,W\bigl(\phi+F(p)\Delta t\bigr)\Bigr\}.$$

This is the page's `V^{Δt}`, with `Δϕ = F(p)Δt` from (18).

**Formalization Note** `IsGreatest` says the maximum exists and equals `W ϕ`. Only the values of
`W` on `[0, ∞)` enter. The paper uses the operator for small `Δt`; that restriction is made where
the definition is used. -/
def IsBellmanFixedPoint (r v cL cH : ℝ) (f h0 : ℝ → ℝ) (Δt : ℝ) (W : ℝ → ℝ) : Prop :=
  ContinuousOn W (Set.Ici 0) ∧ (∀ ϕ : ℝ, 0 ≤ ϕ → W ϕ ∈ Set.Icc 0 (v / r - cL)) ∧
    ∀ ϕ : ℝ, 0 ≤ ϕ →
      IsGreatest
        ((fun p => moment h0 1 ϕ * Δt * (∫ c in cL..p, (v / r - c) * f c) +
            (1 - moment h0 1 ϕ * Δt * costCDF cL f p) * (1 - r * Δt) *
              W (ϕ + costCDF cL f p * Δt)) '' Set.Icc cL cH) (W ϕ)

end ScarceIdeas


