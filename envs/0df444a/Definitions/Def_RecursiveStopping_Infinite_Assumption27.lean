-- Prove2me | Definitions.Def_RecursiveStopping_Infinite_Assumption27
-- name    : RecursiveStopping_Infinite_Assumption27
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:42:13.588648+00:00
-- url     : https://prove2.me/theorems/4c6a7300-9f14-4cae-889d-bdd6962df61e
-- title:
--   Assumption 2.7 (infinite horizon)
-- statement:
--   For a flow $X$ on $\mathbb R^d$, a discount rate $r$ and payoffs $\varphi,\psi$:
--
--   The stochastic flow $x\mapsto X^x_t$ is $\mathsf P$-a.s. continuous for every $t\ge0$. Moreover,
--
--   1. there is $\rho\in(0,1)$ such that, for every $x\in\mathbb R^d$, the process
--   $$\widehat X_t:=e^{-2r(1-\rho)t}\big(1+|X^x_t|_d^2\big),\qquad t\ge0,$$
--   is an $\mathbb F$-supermartingale under $\mathsf P$;
--   2. for every compact $K\subset\mathbb R^d$, $\displaystyle\sup_{x\in K}\mathsf E\Big[\sup_{t\ge0}e^{-rt}|X^x_t|_d\Big]<\infty$;
--   3. for every $x$ and every sequence $x_n\to x$, $\displaystyle\lim_{n\to\infty}\mathsf E\Big[\sup_{t\ge0}e^{-rt}|X^{x_n}_t-X^x_t|_d\Big]=0$;
--   4. $\varphi,\psi\in\mathcal A_d$ and $\varphi\le\psi$.
--
--   These are the paper's standing assumptions on the process and the payoffs; (i) is the growth control behind every estimate in the weighted norm.
--
--   **Formalization Note** "$\mathsf P$-a.s. continuous for all $t\ge0$" is read as "for each $t$, $\mathsf P$-a.s.". Expectations in 2–3 are Lebesgue integrals of non-negative quantities.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, Assumption 2.7, p.8

import Mathlib
import Definitions.Def_RecursiveStopping_Infinite_InA

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace RecursiveStopping.Infinite

/-- **Assumption 2.7** of Colaneri & De Angelis, arXiv:1905.02650v4, p.8 (infinite horizon):
"The stochastic flow `x ↦ X^x_t` is `P`-a.s. continuous for all `t ≥ 0`. Moreover,
(i) there exists `ρ ∈ (0, 1)` such that the process `X̂_t := e^{−2r(1−ρ)t}(1 + |X_t|_d²)` is a
`P_x`-supermartingale for any `x ∈ ℝ^d`; (ii) for any compact `K ⊂ ℝ^d`,
`sup_{x∈K} E_x[sup_{t≥0} e^{−rt}|X_t|_d] < ∞`; (iii) for any `x` and any sequence `x_n → x`,
`lim_n E[sup_{t≥0} e^{−rt}|X^{x_n}_t − X^x_t|_d] = 0`; (iv) `ϕ` and `ψ` belong to `A_d`
(with `ϕ ≤ ψ`)."

**Formalization Note** "`P`-a.s. continuous for all `t ≥ 0`" is read as: for each `t`, `P`-a.s.
The supermartingale in (i) is with respect to `𝔽` under `P` (Mathlib's `Supermartingale`,
which includes adaptedness and integrability). The expectations in (ii)–(iii) are `lintegral`s
of non-negative quantities. -/
structure Assumption27 {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝔽 : Filtration ℝ≥0 mΩ)
    (X : EuclideanSpace ℝ (Fin d) → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (r : ℝ)
    (ϕ ψ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop where
  flow_cont : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, Continuous (fun x => X x t ω)
  supermart : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ x,
    Supermartingale (fun (t : ℝ≥0) ω => Real.exp (-2 * r * (1 - ρ) * (t : ℝ)) * (1 + ‖X x t ω‖ ^ 2)) 𝔽 P
  growth : ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K →
    (⨆ x ∈ K, ∫⁻ ω, ⨆ t : ℝ≥0, ENNReal.ofReal (Real.exp (-r * (t : ℝ)) * ‖X x t ω‖) ∂P) < ⊤
  stab : ∀ (x : EuclideanSpace ℝ (Fin d)) (xs : ℕ → EuclideanSpace ℝ (Fin d)),
    Tendsto xs atTop (𝓝 x) →
    Tendsto (fun n => ∫⁻ ω, ⨆ t : ℝ≥0,
      ENNReal.ofReal (Real.exp (-r * (t : ℝ)) * ‖X (xs n) t ω - X x t ω‖) ∂P) atTop (𝓝 0)
  phi_mem : InA ϕ
  psi_mem : InA ψ
  phi_le_psi : ∀ x, ϕ x ≤ ψ x

end RecursiveStopping.Infinite


