-- Prove2me | Definitions.Def_TwoEchelonCVRP_LowerBound_ExtRoutes
-- name    : TwoEchelonCVRP_LowerBound_ExtRoutes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T15:12:48.872814+00:00
-- url     : https://prove2.me/theorems/b457c9a0-0d21-431e-9afe-48021abcfa84
-- title:
--   §4: enlarged families $\hat{\mathcal R}_k \supseteq \mathcal R_k$ of non-elementary routes and the marginal costs (24)
-- statement:
--   For each satellite $k$ let $\hat{\mathcal R}_k \supseteq \mathcal R_k$ be a finite family of **not necessarily elementary** second-level routes: each route starts and ends at $k$ and visits a nonempty sequence of customers, possibly with repetitions, and has a cost $c_{kl}$; the routes of $\mathcal R_k$ belong to it with their own cost. For such a route, $a_{ikl}$ is the number of times it visits customer $i$, and $\hat{\mathcal R}_{ik}$ is the set of routes of $\hat{\mathcal R}_k$ visiting $i$.
--
--   For penalties $\lambda \in \mathbb R^{N_C}$, $\mu_k$, $\mu_0$, the marginal costs of expression (24) are
--   $$\beta_{ik} = q_i \min_{l \in \hat{\mathcal R}_{ik}} \left\{ \frac{c_{kl} - \sum_{i' \in N_C} a_{i'kl}\lambda_{i'} - \mu_k - \mu_0}{\sum_{i' \in N_C} a_{i'kl}q_{i'}} \right\}, \qquad i \in N_C,\ k \in N_S. \qquad (24)$$
--   The denominators are positive since every route visits a customer and demands are positive.
--
--   In the paper's bounding procedure, $\hat{\mathcal R}_k$ is a family of ng-routes, and (24) supplies the solution of (12) at every subgradient step.
--
--   **Formalization Note** The inclusion $\mathcal R_k \subseteq \hat{\mathcal R}_k$ is a map from $\mathcal R$ into the enlarged family preserving the satellite, the customer sequence and the cost. The cost of a route outside $\mathcal R$ is a free real number: the paper leaves it implicit and Theorem 4 does not depend on it. When $\hat{\mathcal R}_{ik}$ is empty, no route of $\mathcal R_k$ visits $i$, so $\beta_{ik}$ does not enter (12); it is then set to $0$.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 302, §4 and Theorem 4, Eq. (24)

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LowerBound_Model

namespace TwoEchelonCVRP.LowerBound

variable {I : Instance}

/-- An enlarged family `𝓡̂ = ⋃_k 𝓡̂_k ⊇ 𝓡` of not necessarily elementary second-level routes
(§4, p. 302). Route `t` starts and ends at satellite `sat t` and visits the customers `tour t` in
that order (nonempty; repetitions allowed); its cost is `cost t`. The map `emb` realises
`𝓡_k ⊆ 𝓡̂_k`: it sends each route of `RS` to a route of the family with the same satellite, the
same customer sequence and the same cost `c_{kl}`.

Formalization Note: the paper leaves the cost of a non-elementary route implicit; Theorem 4 holds
for any real costs on the additional routes, so `cost` is a free function. -/
structure ExtRoutes (RS : RouteSystem I) where
  T : Type
  [fintypeT : Fintype T]
  [decEqT : DecidableEq T]
  sat : T → Fin I.ns
  tour : T → List (Fin I.nc)
  tour_ne : ∀ t, tour t ≠ []
  cost : T → ℝ
  emb : RS.SR → T
  emb_sat : ∀ l, sat (emb l) = RS.sat l
  emb_tour : ∀ l, tour (emb l) = RS.tour2 l
  emb_cost : ∀ l, cost (emb l) = RS.c l

attribute [instance] ExtRoutes.fintypeT ExtRoutes.decEqT

variable {RS : RouteSystem I}

/-- `a_{ikl}` for an enlarged route: the number of visits of `t` to customer `i`. -/
def ExtRoutes.a (E : ExtRoutes RS) (i : Fin I.nc) (t : E.T) : ℕ := (E.tour t).count i

/-- `𝓡̂_{ik}`: the enlarged routes of satellite `k` that visit customer `i`. -/
def ExtRoutes.Rhat (E : ExtRoutes RS) (i : Fin I.nc) (k : Fin I.ns) : Finset E.T :=
  Finset.univ.filter (fun t => E.sat t = k ∧ i ∈ E.tour t)

/-- The ratio of (24) for route `t`:
`(c_{kl} − ∑_i a_{ikl} λ_i − μ_k − μ_0) / ∑_i a_{ikl} q_i` with `k = sat t`. -/
noncomputable def ExtRoutes.ratio (E : ExtRoutes RS) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ)
    (μ0 : ℝ) (t : E.T) : ℝ :=
  (E.cost t - ∑ i, (E.a i t : ℝ) * lam i - μ (E.sat t) - μ0) / ∑ i, (E.a i t : ℝ) * (I.q i : ℝ)

/-- The marginal costs of (24) (Theorem 4, p. 302):
`β_{ik} = q_i · min_{l ∈ 𝓡̂_{ik}} ratio(l)`. When `𝓡̂_{ik}` is empty no route of `𝓡_k` visits
`i`, so `β_{ik}` does not occur in (12); it is then set to `0`. -/
noncomputable def ExtRoutes.beta24 (E : ExtRoutes RS) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ)
    (μ0 : ℝ) (i : Fin I.nc) (k : Fin I.ns) : ℝ :=
  if h : (E.Rhat i k).Nonempty then (I.q i : ℝ) * (E.Rhat i k).inf' h (E.ratio lam μ μ0) else 0

end TwoEchelonCVRP.LowerBound


