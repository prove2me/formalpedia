-- Prove2me | Definitions.Def_TwoEchelonVRP_MultFeasible
-- name    : TwoEchelonVRP_MultFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:30:36.705718+00:00
-- url     : https://prove2.me/theorems/31298360-4d0e-4fc5-9648-d678ea4df679
-- title:
--   Admissible Lagrangean multipliers: $\mu \le 0$ and inequalities (12)
-- statement:
--   Relaxation RF arises from F by relaxing constraints (2), (3) and (4) in a Lagrangean fashion with penalties $\lambda_i \in \mathbb R$ ($i \in N_C$), $\mu_k \le 0$ ($k \in N_S$) and $\mu_0 \le 0$, and by choosing **marginal routing costs** $\beta_{ik}$, the cost of serving customer $i$ from satellite $k$, as a solution of
--
--   $$
--   \sum_{i \in N_C} a_{ikl} \beta_{ik} \le c_{kl} - \sum_{i \in N_C} a_{ikl} \lambda_i - \mu_k - \mu_0, \qquad l \in \mathcal R_k,\ k \in N_S. \qquad (12)
--   $$
--
--   The multipliers $(\beta, \lambda, \mu, \mu_0)$ are **admissible** when $\mu_k \le 0$ for every $k$, $\mu_0 \le 0$, and (12) holds. Theorem 1 says that every admissible choice gives a lower bound $z(RF(\beta,\lambda,\mu))$ on the 2E-CVRP, and Theorem 2 maximizes this bound over the admissible choices.
--
--   **Formalization Note** `β i k` is $\beta_{ik}$, `lam i` is $\lambda_i$, `μ k` is $\mu_k$ and `μ0` is $\mu_0$; the paper's $\mu \in \mathbb R_-^{N_S+1}$ is the pair $(\mu, \mu_0)$. $a_{ikl}$ is `aCoef`.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Operations Research 61(2) (2013) 298–314, doi:10.1287/opre.1120.1153, §3.1, unnumbered text and inequalities (12), p. 301; Theorem 1, p. 301 ('λ ∈ ℝ^{N_C} and μ ∈ ℝ_−^{N_S+1}')

import Mathlib
import Definitions.Def_TwoEchelonVRP_Instance
import Definitions.Def_TwoEchelonVRP_Route2

namespace TwoEchelonVRP

/-- **Admissible multipliers of relaxation RF: penalties `λ`, `μ` and marginal routing costs `β`
satisfying (12).**
Baldacci et al., *An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem*,
Operations Research 61(2) (2013) 298–314, §3.1, (12), p. 301: "This relaxation derives from problem
F by relaxing, in a Lagrangean fashion, constraints (2)–(4) with penalties λ_i ∈ ℝ, i ∈ N_C,
μ_k ∈ ℝ_−, k ∈ N_S, and μ_0 ∈ ℝ_−, respectively, and by defining the marginal routing costs β_ik for
servicing customer i ∈ N_C from satellite k ∈ N_S as a solution of
Σ_{i∈N_C} a_ikl β_ik ≤ c_kl − Σ_{i∈N_C} a_ikl λ_i − μ_k − μ_0, l ∈ 𝓡_k, k ∈ N_S (12)".

`MultFeasible I β lam μ μ0` holds when `μ k ≤ 0` for every satellite `k`, `μ0 ≤ 0`, and (12) holds
for every satellite `k` and every route `l ∈ 𝓡_k`. `lam` is unrestricted.

**Formalization Note.** `β i k` is `β_ik`, `lam i` is `λ_i`, `μ k` is `μ_k` and `μ0` is `μ_0`;
Theorem 1's `μ ∈ ℝ_−^{N_S+1}` is the pair `(μ, μ0)`. `aCoef l i` is `a_ikl`. -/
def MultFeasible {ns nc : ℕ} (I : Instance ns nc) (β : Fin nc → Fin ns → ℝ) (lam : Fin nc → ℝ)
    (μ : Fin ns → ℝ) (μ0 : ℝ) : Prop :=
  (∀ k, μ k ≤ 0) ∧ μ0 ≤ 0 ∧
    ∀ (k : Fin ns) (l : Route2 I),
      ∑ i, aCoef l i * β i k ≤ cost2 I k l - ∑ i, aCoef l i * lam i - μ k - μ0

end TwoEchelonVRP


