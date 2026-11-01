-- Prove2me | Definitions.Def_DRORSEquiv_Model
-- name    : DRORSEquiv_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:32.847387+00:00
-- url     : https://prove2.me/theorems/af535263-ddea-4cdb-bd39-a77f07c3b5dc
-- title:
--   Data of the empirical DRO and RS models
-- statement:
--   The **data** of the data-driven models of Wang, Ran, Zhou and He consist of
--
--   1. a feasible set $\mathcal X$ of decisions $x$ in a real vector space,
--   2. a support set $\mathcal Z$ of outcomes $z$,
--   3. a transport cost $\rho(z,z')$, the ground cost of the type-1 Wasserstein distance,
--   4. $S$ historical samples $\hat z_1,\dots,\hat z_S$, whose empirical distribution $\mathbb P^\dagger$ puts mass $1/S$ on each,
--   5. a cost function $f(x,z)$.
--
--   Every object of the mission (the worst-case loss, Problems (DRO) and (RS), $\kappa$, $Z_0$, $\bar\tau$, $\bar\theta$) is computed from these data.
--
--   **Formalization Note** The structure carries no hypotheses: convexity of $\mathcal X$ and of $f(\cdot,z)$, $S\ge1$, $\hat z_s\in\mathcal Z$, $\rho\ge0$ and $\rho(z,z)=0$ are hypotheses of the theorems that use them. The paper's standing assumptions of p.7 (Polish $(\mathcal Z,\rho)$, $f(x,\cdot)\in L^1(\mathbb P^\dagger)$, bounded growth rate) only serve the measure-level reformulations and are not part of the model. Samples are indexed by `Fin S`.
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), §2, pp.5–8 (data of Problems (DRO), (RS); empirical distribution p.6)

import Mathlib

namespace DRORSEquiv

/-- **The data of the empirical DRO / RS models** (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), §2, pp.5–8):
a feasible set `X` of decisions in a real vector space `E`, a support set `Z` of outcomes in a
type `Ω`, a transport cost `ρ : Ω → Ω → ℝ`, `S` historical samples `zhat s` (`s : Fin S`), and a
cost function `f : E → Ω → ℝ`.

**Formalization Note.** The structure carries no hypotheses. Convexity of `X` and of `f(·, z)`,
`0 < S`, `zhat s ∈ Z`, `ρ ≥ 0` and `ρ(z, z) = 0` are stated in each theorem that uses them.
The paper's standing assumptions of p.7 ((Z, ρ) Polish, f(x, ·) ∈ L¹(P†), bounded growth rate) are
not part of the model: they serve only the measure-level reformulations that precede Problems (DRO)
and (RS). Samples are indexed by `Fin S` (0-based) for the paper's `[S] = {1, …, S}`. -/
structure Model (E Ω : Type*) (S : ℕ) where
  /-- The feasible set `𝒳` of decisions. -/
  X : Set E
  /-- The support set `𝒵` of the uncertain outcome. -/
  Z : Set Ω
  /-- The transport cost `ρ(z, z')` of the Wasserstein distance. -/
  ρ : Ω → Ω → ℝ
  /-- The historical samples `ẑ_s`. -/
  zhat : Fin S → Ω
  /-- The cost function `f(x, z)`. -/
  f : E → Ω → ℝ

end DRORSEquiv


