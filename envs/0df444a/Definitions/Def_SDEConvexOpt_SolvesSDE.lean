-- Prove2me | Definitions.Def_SDEConvexOpt_SolvesSDE
-- name    : SDEConvexOpt_SolvesSDE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:25:43.224734+00:00
-- url     : https://prove2.me/theorems/2f9dff67-a815-4757-9c8c-75f037e83a36
-- title:
--   Strong solution of $dX=b(t,X)\,dt+\sigma(t,X)\,dW$, $X(0)=X_0$, on a filtered space
-- statement:
--   Let $b:\mathbb R_+\times\mathbb R^d\to\mathbb R^d$ and $\sigma:\mathbb R_+\times\mathbb R^d\to\mathbb R^{d\times m}$, let $W$ be an $m$-dimensional process and $X_0\in\mathbb R^d$. A process $X:\mathbb R_+\times\Omega\to\mathbb R^d$ solves
--   $$
--   dX(t)=b(t,X(t))\,dt+\sigma(t,X(t))\,dW(t),\qquad X(0)=X_0,
--   $$
--   on $(\Omega,\mathcal F,(\mathcal F_t),\mathbb P)$ when
--
--   1. every $X(t)$ is measurable, every path $t\mapsto X(t,\omega)$ is continuous, and $X$ is $(\mathcal F_t)$-adapted;
--   2. there is an $(\mathcal F_t)$-adapted matrix process $J$ with continuous paths whose entries are the Itô integrals $J_{ik}(t)=\int_0^t\sigma_{ik}(s,X(s))\,dW_k(s)$ for the filtration $(\mathcal F_t)$;
--   3. every path of the drift $s\mapsto b(s,X(s))$ is integrable on every $[0,t]$;
--   4. outside one null set, for all $t\ge0$ and every coordinate $i$,
--   $$
--   X_i(t)=X_{0,i}+\int_0^t b_i(s,X(s))\,ds+\sum_{k=1}^m J_{ik}(t).
--   $$
--
--   With $b(t,x)=-\nabla f(x)$ this is the dynamic (SDE); with general $(b,\sigma)=(F,G)$ it is (A.1).
--
--   **Formalization Note** The Itô integral is the published `EthierKurtz.HasBrownianItoIntegral` (bounded predictable dyadic step approximations converging in probability), for the same filtration. The definition mirrors the published `EthierKurtz.SolvesBrownianSDE`, which is not reused because its diffusion is $d\times d$ with a $d$-dimensional noise (it forces $m=d$) and its filtration is fixed. The paper's processes are continuous for almost every $\omega$ and are identified up to indistinguishability (p.7); the Lean solution has every path continuous, a representative that every class has when $\mathcal F_0$ contains the null sets. Adapted plus continuous gives the paper's progressive measurability.
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, (SDE), p.2; §2.2 ($S^0_d$), p.7; (A.1), p.34

import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_SDEConvexOpt_Diffusion

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SDEConvexOpt

open EthierKurtz

/-- `X` is a (strong) solution on `ℝ₊` of the stochastic differential equation
`dX(t) = b(t, X(t)) dt + σ(t, X(t)) dW(t)`, `X(0) = X₀`, driven by the `m`-dimensional process `W`
on the filtered probability space `(Ω, 𝓕, {𝓕ₜ}, ℙ)`
(Maulen S., Fadili, Attouch, arXiv:2207.02750v1, (SDE), p.2, and (A.1), p.34, with drift
`F = b`, diffusion `G = σ`; the solution class `S⁰_d` of p.7).

The clauses: every `X(t)` is measurable; every path `t ↦ X(t, ω)` is continuous; `X` is
`𝓕`-adapted; there is a process `J` of `d × m` matrices with continuous paths, adapted to `𝓕`,
whose entry `Jᵢₖ(t)` is the Itô integral `∫₀ᵗ σᵢₖ(s, X(s)) dWₖ(s)` (published
`EthierKurtz.HasBrownianItoIntegral`, for the same filtration `𝓕`); the drift is pathwise
integrable on every `[0, t]`; and outside one `ℙ`-null set, for all `t` and every coordinate `i`,
`Xᵢ(t) = X₀ᵢ + ∫₀ᵗ bᵢ(s, X(s)) ds + ∑ₖ Jᵢₖ(t)`.

**Formalization Note** This is the construction of the published
`EthierKurtz.SolvesBrownianSDE`, which is not reused because its diffusion is `d × d`, its noise
is `d`-dimensional (it forces `m = d`) and its filtration is fixed to the completed Brownian
past. Here the diffusion is `d × m` (`Diffusion d m`, Frobenius norm), `W` is `m`-dimensional and
the filtration `ℱ` is a parameter. Time is `ℝ≥0`; `X₀ ∈ ℝ^d` is deterministic (p.2). Adaptedness
plus continuous paths gives progressive measurability, the paper's `S⁰_d`. Paths are continuous
for every `ω` (the paper's "continuous" is "for almost all ω", p.7; with `𝓕₀` complete every such
solution is indistinguishable from one of these). -/
def SolvesSDE {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (b : ℝ≥0 × SDEState d → SDEState d) (σ : ℝ≥0 × SDEState d → Diffusion d m)
    (W : ℝ≥0 → Ω → SDEState m) (X₀ : SDEState d) (X : ℝ≥0 → Ω → SDEState d) : Prop :=
  (∀ t, Measurable (X t)) ∧
  (∀ ω, Continuous (fun t => X t ω)) ∧
  Adapted ℱ X ∧
  ∃ J : ℝ≥0 → Ω → Diffusion d m,
    (∀ ω, Continuous (fun t => J t ω)) ∧
    Adapted ℱ J ∧
    (∀ (i : Fin d) (k : Fin m), HasBrownianItoIntegral P ℱ
      (fun t ω => W t ω k) (fun t ω => σ (t, X t ω) (i, k)) (fun t ω => J t ω (i, k))) ∧
    (∀ (t : ℝ≥0) ω (i : Fin d), IntervalIntegrable
      (fun u : ℝ => b (u.toNNReal, X u.toNNReal ω) i) volume 0 t.val) ∧
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) (i : Fin d), X t ω i = X₀ i +
      (∫ u in (0 : ℝ)..t.val, b (u.toNNReal, X u.toNNReal ω) i) + ∑ k, J t ω (i, k)

end SDEConvexOpt


