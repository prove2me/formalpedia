-- Prove2me | Definitions.Def_ChenBullwhip_Decentralized_IIDDemand
-- name    : ChenBullwhip_Decentralized_IIDDemand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:04:11.731016+00:00
-- url     : https://prove2.me/theorems/1dfe41cf-06ec-4dde-88a6-a570e9091fce
-- title:
--   I.i.d. symmetric demand $D_t = \mu + \epsilon_t$ (Eq. (1) with $\rho = 0$; Theorem 3.2)
-- statement:
--   Let $(\Omega, \mathcal F, P)$ be a probability space and let time be indexed by the integers $t \in \mathbb Z$. An **i.i.d. symmetric demand process** consists of a constant $\mu \in \mathbb R$, a standard deviation $\sigma > 0$ and error terms $\epsilon_t : \Omega \to \mathbb R$, $t \in \mathbb Z$, such that
--
--   1. the $\epsilon_t$ are measurable and mutually independent;
--   2. they are identically distributed, each with the law of $\epsilon_0$;
--   3. each $\epsilon_t$ is symmetric: $-\epsilon_t$ has the same law as $\epsilon_t$;
--   4. each $\epsilon_t$ is square integrable, with $E[\epsilon_t] = 0$ and $\operatorname{Var}(\epsilon_t) = \sigma^2$.
--
--   The demand seen by the retailer in period $t$ is
--
--   $$D_t = \mu + \epsilon_t .$$
--
--   This is the demand model of Theorem 3.2 of Chen, Drezner, Ryan and Simchi-Levi (2000), and the case $\rho = 0$ of their AR(1) model (1), in which "the demands are i.i.d. with mean $\mu$ and variance $\sigma^2$". It is the input of both the single-stage order process behind Eq. (6) and the decentralized multistage chain of Theorem 3.2.
--
--   **Formalization Note** Model (1) asks $\mu \ge 0$; Theorem 3.2 states no sign condition, and $\mu$ affects no variance, so no sign condition is imposed (a harmless generalization). The paper takes $\sigma > 0$ implicitly by dividing by $\operatorname{Var}(D) = \sigma^2$; here it is a field. Square integrability is stated so that every variance below is the genuine one (Mathlib's `variance` is $0$ off $L^2$). Time runs over $\mathbb Z$ so that every lagged demand $D_{t-i}$ exists.
-- source:
--   Chen, Drezner, Ryan and Simchi-Levi, Quantifying the Bullwhip Effect in a Simple Supply Chain, Management Science 46 (2000), p. 437, Eq. (1) and the remark "if ρ = 0"; p. 441, Theorem 3.2 (demand model)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ChenBullwhip.Decentralized

/-- I.i.d. customer demand, Chen–Drezner–Ryan–Simchi-Levi (2000), Eq. (1) with `ρ = 0` and the
demand model of Theorem 3.2: `D t = μ + ε t`, where the errors `ε t` (`t : ℤ`) are independent,
identically distributed, symmetric about `0`, square integrable, with mean `0` and variance
`σ²`, `σ > 0`. -/
structure IIDDemand {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) where
  /-- the constant mean demand `μ` -/
  mu : ℝ
  /-- the standard deviation `σ` of the error terms -/
  sigma : ℝ
  sigma_pos : 0 < sigma
  /-- the error terms `ε t` -/
  eps : ℤ → Ω → ℝ
  measurable_eps : ∀ t, Measurable (eps t)
  indep : iIndepFun eps P
  identDistrib : ∀ t, IdentDistrib (eps t) (eps 0) P P
  symmetric : ∀ t, IdentDistrib (eps t) (fun ω => -eps t ω) P P
  memLp : ∀ t, MemLp (eps t) 2 P
  mean_zero : ∀ t, ∫ ω, eps t ω ∂P = 0
  variance_eq : ∀ t, variance (eps t) P = sigma ^ 2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The demand seen by the retailer in period `t`: `D t = μ + ε t`. -/
def IIDDemand.D (X : IIDDemand P) (t : ℤ) (ω : Ω) : ℝ :=
  X.mu + X.eps t ω

end ChenBullwhip.Decentralized


