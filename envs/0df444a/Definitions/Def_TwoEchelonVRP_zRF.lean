-- Prove2me | Definitions.Def_TwoEchelonVRP_zRF
-- name    : TwoEchelonVRP_zRF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:31:27.869394+00:00
-- url     : https://prove2.me/theorems/5bb7043d-8d5f-40a6-b0fe-39a5f458fdef
-- title:
--   Lagrangean relaxation RF$(\beta,\lambda,\mu)$ and its value $z(RF(\beta,\lambda,\mu))$
-- statement:
--   Relaxation **RF** uses binary variables $\xi_{ik}$, equal to one if customer $i$ is supplied from satellite $k$, and the variables $y_r$, $q_{kr}$ of F. Its feasible solutions satisfy
--
--   1. (14) $\sum_{k \in N_S} \xi_{ik} = 1$ for every customer $i$;
--   2. (15) $\sum_{r \in \mathcal M_k} q_{kr} = \sum_{i \in N_C} q_i \xi_{ik}$ for every satellite $k$;
--   3. (16) $\sum_{i \in N_C} q_i \xi_{ik} \le B_k$ for every satellite $k$;
--   4. (17) the constraints (6), (8), (10) and (11) of F, with $q_{kr} = 0$ for $k \notin R_r$;
--   5. (18) $\xi_{ik} \in \{0, 1\}$.
--
--   For multipliers $(\beta, \lambda, \mu, \mu_0)$ its value is
--
--   $$
--   z(RF(\beta,\lambda,\mu)) = \min \sum_{k \in N_S} \sum_{i \in N_C} \beta_{ik} \xi_{ik} + \sum_{r \in \mathcal M} g_r y_r + \sum_{i \in N_C} \lambda_i + \sum_{k \in N_S} m_k \mu_k + m^2 \mu_0 \qquad (13)
--   $$
--
--   over the feasible solutions. The feasible set does not depend on the multipliers.
--
--   **Formalization Note** $z(RF(\beta,\lambda,\mu))$ is the infimum in the extended reals of the objective values, $+\infty$ when RF is infeasible; the feasible set is finite, so otherwise it is a real minimum. The module declares `RFFeasible`, `objRF` and `zRF`.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Operations Research 61(2) (2013) 298–314, doi:10.1287/opre.1120.1153, §3.1, relaxation (RF), (13)–(18), p. 301

import Mathlib
import Definitions.Def_TwoEchelonVRP_Instance
import Definitions.Def_TwoEchelonVRP_Route1

namespace TwoEchelonVRP

/-- **Feasible solutions of relaxation RF.**
Baldacci et al., *An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem*,
Operations Research 61(2) (2013) 298–314, §3.1, (14)–(18), p. 301: "Problem RF involves binary
variables ξ_ik equal to one if customer i ∈ N_C is supplied from satellite k ∈ N_S (0 otherwise)
and variables y_r and q_kr, as defined for problem F." The constraints are
* (14) `Σ_{k ∈ N_S} ξ_ik = 1` for every customer `i`;
* (15) `Σ_{r ∈ 𝓜_k} q_kr = Σ_{i ∈ N_C} q_i ξ_ik` for every satellite `k`;
* (16) `Σ_{i ∈ N_C} q_i ξ_ik ≤ B_k` for every satellite `k`;
* (17) = (6) `Σ_r y_r ≤ m¹`, (8) `Σ_{k ∈ R_r} q_kr ≤ Q_1 y_r`, (10) `y_r ∈ {0, 1}`,
  (11) `q_kr ∈ ℤ₊` for `k ∈ R_r`, with `q_kr = 0` for `k ∉ R_r` as in F (p. 300);
* (18) `ξ_ik ∈ {0, 1}`.

**Formalization Note.** `ξ i k` is `ξ_ik`. The feasible set does not depend on the multipliers. -/
def RFFeasible {ns nc : ℕ} (I : Instance ns nc) (ξ : Fin nc → Fin ns → ℝ)
    (y : Route1 I → ℝ) (qd : Route1 I → Fin ns → ℝ) : Prop :=
  (∀ i, ∑ k, ξ i k = 1) ∧
    (∀ k, ∑ r ∈ Finset.univ.filter (fun r : Route1 I => k ∈ satSet r), qd r k
      = ∑ i, (I.q i : ℝ) * ξ i k) ∧
    (∀ k, ∑ i, (I.q i : ℝ) * ξ i k ≤ I.B k) ∧
    ∑ r, y r ≤ (I.m1 : ℝ) ∧
    (∀ r, ∑ k ∈ satSet r, qd r k ≤ (I.Q1 : ℝ) * y r) ∧
    (∀ r, y r = 0 ∨ y r = 1) ∧
    (∀ r, ∀ k ∈ satSet r, ∃ n : ℕ, qd r k = n) ∧
    (∀ r k, k ∉ satSet r → qd r k = 0) ∧
    (∀ i k, ξ i k = 0 ∨ ξ i k = 1)

/-- **Objective (13) of relaxation RF(β, λ, μ)**:
`Σ_{k∈N_S} Σ_{i∈N_C} β_ik ξ_ik + Σ_{r∈𝓜} g_r y_r + Σ_{i∈N_C} λ_i + Σ_{k∈N_S} m_k μ_k + m² μ_0`
(Baldacci et al., Operations Research 61(2) (2013), §3.1, (13), p. 301). -/
noncomputable def objRF {ns nc : ℕ} (I : Instance ns nc) (β : Fin nc → Fin ns → ℝ)
    (lam : Fin nc → ℝ) (μ : Fin ns → ℝ) (μ0 : ℝ) (ξ : Fin nc → Fin ns → ℝ) (y : Route1 I → ℝ) : ℝ :=
  ∑ k, ∑ i, β i k * ξ i k + ∑ r, cost1 I r * y r + ∑ i, lam i
    + ∑ k, (I.mSat k : ℝ) * μ k + (I.m2 : ℝ) * μ0

/-- **The Lagrangean bound** `z(RF(β, λ, μ))`.
Baldacci et al., Operations Research 61(2) (2013), §3.1, (RF), (13)–(18), p. 301:
`z(RF(β, λ, μ)) = min (13)` subject to (14)–(18).

**Formalization Note.** `z(RF(β, λ, μ))` is the infimum in `EReal` of the objective values of the
feasible solutions; it is `⊤` (`+∞`) when RF is infeasible. Its feasible set is finite, so when it
is nonempty the infimum is a minimum and is a real number. -/
noncomputable def zRF {ns nc : ℕ} (I : Instance ns nc) (β : Fin nc → Fin ns → ℝ)
    (lam : Fin nc → ℝ) (μ : Fin ns → ℝ) (μ0 : ℝ) : EReal :=
  sInf ((fun v : ℝ => (v : EReal)) ''
    {v | ∃ ξ y qd, RFFeasible I ξ y qd ∧ v = objRF I β lam μ μ0 ξ y})

end TwoEchelonVRP


