-- Prove2me | Definitions.Def_LatentMixDRO_popR
-- name    : LatentMixDRO_popR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:23.616338+00:00
-- url     : https://prove2.me/theorems/4359e85a-a212-4e91-8882-52f429294571
-- title:
--   Population variational objective $R_{p,\epsilon,L}(\theta,\eta)$ (12)
-- statement:
--   With $q=p/(p-1)$ and $\epsilon>0$,
--
--   $$
--   R_{p,\epsilon,L}(\theta,\eta)=\sup_{h\in\mathcal H_{L,p}}\Big\{\mathbb E\Big[\frac{h(X)}{\epsilon}\big(\ell(\theta;(X,Y))-\eta\big)\Big]\ \Big|\ h\ge0,\ \big(\mathbb E[h(X)^q]\big)^{1/q}\le\epsilon\Big\}.
--   $$
--
--   This replaces the unknown conditional risk in the variational form (9) by the loss itself, at the price of restricting $h$ to a Hölder class.
--
--   **Formalization Note** The norm constraint uses `eLpNorm` rather than a Bochner integral of $h^q$, which would be $0$ for a non-integrable $h^q$. The set of values contains $0$ ($h=0$) and is bounded above under Assumption A1, so the real supremum is the true one. The constraint $h\ge0$ is on $\mathcal X$, which carries $P_X$.
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, display (12), p.10

import Mathlib
import Definitions.Def_LatentMixDRO_holderClass

open MeasureTheory

namespace LatentMixDRO

/-- The population variational objective
`R_{p,ε,L}(θ, η) = sup_{h ∈ H_{L,p}} {E[(h(X)/ε)(ℓ(θ; (X, Y)) - η)] | h ≥ 0, (E[h(X)^q])^{1/q} ≤ ε}`,
with `q = p/(p - 1)`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, display (12), p.10.

**Formalization Note.** The constraint uses `eLpNorm`, not a Bochner integral of `h^q`, which would
be `0` for a non-integrable `h^q` and make such `h` feasible by junk. The set is nonempty (`h = 0`)
and, under Assumption A1, bounded above by Hölder's inequality, so `sSup` is the true supremum. -/
noncomputable def popR {d : ℕ} {Θ : Type*} (P : Measure (EuclideanSpace ℝ (Fin d) × ℝ))
    (X : Set (EuclideanSpace ℝ (Fin d))) (ℓ : Θ → EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (p ε L : ℝ) (θ : Θ) (η : ℝ) : ℝ :=
  sSup {v | ∃ h ∈ holderClass X p L, (∀ x ∈ X, 0 ≤ h x) ∧
    eLpNorm h (ENNReal.ofReal (p / (p - 1))) (P.map Prod.fst) ≤ ENNReal.ofReal ε ∧
    v = ∫ u, h u.1 / ε * (ℓ θ u - η) ∂P}

end LatentMixDRO


