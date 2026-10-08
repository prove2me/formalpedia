-- Prove2me | Definitions.Def_OptStopC1_TimeDeriv_Hypotheses
-- name    : OptStopC1_TimeDeriv_Hypotheses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:47.100969+00:00
-- url     : https://prove2.me/theorems/9bd974a1-0f7b-4db5-a44b-383c81c9a585
-- title:
--   Theorem 15, pp. 19–20 — the hypotheses (5.9)–(5.11) and the local conditions (5.12)–(5.13) at a boundary point
-- statement:
--   This file bundles the hypotheses of Theorem 15 of De Angelis and Peskir into two predicates: a global one and a local one at a point $z$.
--
--   **Global hypotheses.** For the finite-horizon problem (2.2) with generator coefficients $(\sigma,\mu,\nu)$:
--   1. the standing hypotheses of the model hold and the problem is well posed (the first entry time $\tau_D$ is optimal);
--   2. (5.9) $V$ is continuous on $[0,T]\times\mathbb R^{d-1}$ and continuously differentiable on $C$;
--   3. (5.10) $G$ is once continuously differentiable in $t$ and twice in $x$ on $[0,T]\times\mathbb R^{d-1}$, lies in the domain of $\mathbb L_X$, and the coefficient operator is the killed spatial generator of the flow when applied to $G(t,\cdot)$;
--   4. (5.11) there is a constant $K>0$ with
--   $$|\tilde H(t,x)-\tilde H(s,x)|\le K|t-s|\quad\text{and}\quad|\lambda(t,x)-\lambda(s,x)|\le K|t-s|$$
--   for all $t,s\in[0,T]$ and every $x\in\mathbb R^{d-1}$;
--   5. the spatial part is a continuous stochastic flow in the space variable.
--
--   **Local hypotheses at $z$.** There is $\varepsilon>0$ such that, for all $(t,x)\in b(z,\varepsilon)\cap([0,T]\times\mathbb R^{d-1})$:
--   1. (5.12) for every stopping time $\sigma$ with values in $[0,T-t]$, both expectations below exist and
--   $$\mathsf E\big[e^{-\Lambda^{t,x}_\sigma}G(t+\sigma,X^x_\sigma)\big]=G(t,x)+\mathsf E\Big[\int_0^\sigma e^{-\Lambda^{t,x}_s}(G_t+\mathbb L_XG)(t+s,X^x_s)\,ds\Big];$$
--   2. (5.13) the same $\varepsilon$ gives
--   $$\mathsf E\Big[\sup_{(t,x)\in b(z,\varepsilon)}\ \sup_{T-t-\varepsilon\le s\le T-t}e^{-\Lambda^{t,x}_s}\big|\tilde H(t+s,X^x_s)\big|\Big]<\infty .$$
--
--   Theorem 15 adds to these that $z\in\partial C$ is probabilistically regular for $D^\circ$.
--
--   **Formalization Note** (5.13) is rendered as an integrable majorant: there is an integrable $g$ with $e^{-\Lambda^{t,x}_s}|\tilde H(t+s,X^x_s)|\le g$ almost surely, simultaneously for all $(t,x)$ and $s\ge0$ in the window. This is equivalent to the finiteness of the outer expectation of the supremum, and needs no measurability of the supremum. The ball $b(z,\varepsilon)$ is the ball of the product (max) metric on $\mathbb R\times\mathbb R^{d-1}$. It is nested with the Euclidean ball up to a factor $\sqrt2$, and $\varepsilon$ is existential, so the two conditions are equivalent. (5.12) carries the integrability of both random variables, which the paper's identity presupposes. The points $(t,x)$ range over the domain $[0,T]\times\mathbb R^{d-1}$ of the problem. "Stopping times of $X$" are stopping times of the common filtration, which the paper calls equivalent (p. 3). (5.9) is `ContDiffOn ℝ 1 V C`, with $C$ relatively open in $[0,T]\times\mathbb R^{d-1}$.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, pp. 19–20, Theorem 15, (5.9)–(5.13)

import Mathlib
import Definitions.Def_OptStopC1_TimeDeriv_Flow
import Definitions.Def_OptStopC1_TimeDeriv_Problem
import Definitions.Def_OptStopC1_TimeDeriv_Generator

namespace OptStopC1.TimeDeriv

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StoppingProblem

variable {m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (M : StoppingProblem m Ω) (c : GenCoeffs m)

/-- The operator with coefficients `c` is the killed spatial generator of the process `X`,
applied to `G(t, ·)`. This is the semigroup meaning of the standing assumption (2.14), with
the time variable frozen; the separate time derivative is added in (5.11). -/
def GeneratorForG : Prop :=
  ∀ p ∈ domain m M.T, p.1 < M.T →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ M.T - p.1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) δ,
        Integrable (fun ω => Real.exp (-M.discount p s.toNNReal ω) *
          M.G (p.1, M.X p.2 s.toNNReal ω)) M.P) ∧
      HasDerivWithinAt
        (fun s : ℝ => ∫ ω, Real.exp (-M.discount p s.toNNReal ω) *
          M.G (p.1, M.X p.2 s.toNNReal ω) ∂M.P)
        (genX c M.lam M.G p) (Set.Icc 0 δ) 0

/-- The global hypotheses of Theorem 15 (pp. 19–20): the standing setting, well-posedness, and
1. (5.9) `V` is continuous on `[0, T] × ℝ^{d−1}` and continuously differentiable on `C`;
2. (5.10) `G` is `C^{1,2}` on `[0, T] × ℝ^{d−1}`, and `G` lies in the domain of `𝕃_X`;
3. (5.11) `t ↦ H̃(t, x)` and `t ↦ λ(t, x)` are Lipschitz on `[0, T]`, uniformly in `x`, with one
   constant `K > 0`;
4. the spatial part is a continuous stochastic flow in the space variable. -/
structure Thm15Global : Prop where
  standing : M.Standing
  well_posed : M.IsWellPosed
  value_cont : ContinuousOn M.value (domain m M.T)
  value_C1 : ContDiffOn ℝ 1 M.value M.contSet
  G_C12 : IsC12On M.T M.G
  G_gen_domain : InGenDomain c M.T M.G
  generator_for_G : M.GeneratorForG c
  lipschitz : ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Set.Icc 0 M.T, ∀ s ∈ Set.Icc 0 M.T, ∀ x : Space m,
    |Htilde c M.T M.lam M.G M.H (t, x) - Htilde c M.T M.lam M.G M.H (s, x)| ≤ K * |t - s| ∧
    |M.lam (t, x) - M.lam (s, x)| ≤ K * |t - s|
  cont_flow : IsContinuousFlow M.P M.T M.X

/-- The local hypotheses (5.12)–(5.13) of Theorem 15 at a point `z`: there is one `ε > 0` such that
1. (5.12) for every `(t, x) ∈ b(z, ε) ∩ ([0, T] × ℝ^{d−1})` and every stopping time `σ` with values
   in `[0, T − t]`, both random variables below are integrable and
   `E[e^{−Λ^{t,x}_σ} G(t+σ, X^x_σ)] = G(t, x) + E[∫_0^σ e^{−Λ^{t,x}_s} (G_t + 𝕃_X G)(t+s, X^x_s) ds]`;
2. (5.13) the random variable
   `sup_{(t,x) ∈ b(z,ε)} sup_{T−t−ε ≤ s ≤ T−t} e^{−Λ^{t,x}_s} |H̃(t+s, X^x_s)|` has an integrable
   majorant (the supremum over `s ≥ 0` in the window, `(t, x) ∈ [0, T] × ℝ^{d−1}`). -/
def Thm15AtPoint (z : ℝ × Space m) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    (∀ p ∈ Metric.ball z ε ∩ domain m M.T, ∀ σ : Ω → ℝ≥0, M.IsAdmissible p σ →
      Integrable (fun ω => Real.exp (-M.discount p (σ ω) ω) * M.G (p.1 + σ ω, M.X p.2 (σ ω) ω))
        M.P ∧
      Integrable (fun ω => ∫ u in (0 : ℝ)..(σ ω : ℝ), Real.exp (-M.discount p u.toNNReal ω) *
          (timeDeriv M.T M.G (p.1 + u, M.X p.2 u.toNNReal ω) +
            genX c M.lam M.G (p.1 + u, M.X p.2 u.toNNReal ω))) M.P ∧
      ∫ ω, Real.exp (-M.discount p (σ ω) ω) * M.G (p.1 + σ ω, M.X p.2 (σ ω) ω) ∂M.P =
        M.G p + ∫ ω, (∫ u in (0 : ℝ)..(σ ω : ℝ), Real.exp (-M.discount p u.toNNReal ω) *
          (timeDeriv M.T M.G (p.1 + u, M.X p.2 u.toNNReal ω) +
            genX c M.lam M.G (p.1 + u, M.X p.2 u.toNNReal ω))) ∂M.P) ∧
    (∃ g : Ω → ℝ, Integrable g M.P ∧ ∀ᵐ ω ∂M.P, ∀ p ∈ Metric.ball z ε ∩ domain m M.T,
      ∀ s : ℝ≥0, M.T - p.1 - ε ≤ (s : ℝ) → (s : ℝ) ≤ M.T - p.1 →
        Real.exp (-M.discount p s ω) * |Htilde c M.T M.lam M.G M.H (p.1 + s, M.X p.2 s ω)| ≤ g ω)

end StoppingProblem

end OptStopC1.TimeDeriv


