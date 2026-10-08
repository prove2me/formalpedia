-- Prove2me | Definitions.Def_TwoEchelonCVRP_Config_Bounds
-- name    : TwoEchelonCVRP_Config_Bounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:09.968609+00:00
-- url     : https://prove2.me/theorems/78d284da-c134-49ec-965b-8f491f9f04c5
-- title:
--   §5.1: the bounds LB_R and LBW(M)
-- statement:
--   Fix multipliers $\lambda\in\mathbb R^{N_C}$, $\mu\in\mathbb R^{N_S}$, $\mu_0\in\mathbb R$ and a matrix $\beta=(\beta_{ik})_{i\in N_C,k\in N_S}$. Section 5.1 of Baldacci, Mingozzi, Roberti and Wolfler Calvo (2013) defines
--   $$\mathrm{LB}_R=\sum_{i\in N_C}\min_{k\in N_S}\beta_{ik}+\sum_{i\in N_C}\lambda_i+\sum_{k\in N_S}m_k\mu_k+m^2\mu_0,$$
--   and, for a set $M$ of first-level routes,
--   $$\mathrm{LBW}(M)=\sum_{i\in N_C}\min_{k\in N_S(M)}\beta_{ik}+\sum_{i\in N_C}\lambda_i+\sum_{k\in N_S(M)}m_k\mu_k+m^2\mu_0 .$$
--   The paper takes for $(\beta,\lambda,\mu,\mu_0)$ the vectors that produce its bound LD1; the theorems of the mission use only that $\mu\le0$, $\mu_0\le0$ and $\beta$ satisfies (12).
--
--   $\mathrm{LB}_R$ bounds the second-level routing cost of a solution from below, $\mathrm{LBW}(M)$ the optimal value of $F(M)$; both enter the pruning test of Proposition 1.
--
--   **Formalization Note** The minimum over $N_S$ requires at least one satellite, passed as the argument `hns : 0 < ns`; the minimum over $N_S(M)$ requires $N_S(M)\neq\emptyset$, passed as `hM`. Both are `Finset.inf'`, so no default value is ever used.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 305, §5.1, the definitions of LB_R and LBW(M)

import Mathlib
import Definitions.Def_TwoEchelonCVRP_Config_Configuration

namespace TwoEchelonCVRP.Config

variable {I : Instance}

/-- `LB_R` (§5.1, p. 305):
`LB_R = ∑_{i ∈ N_C} min_{k ∈ N_S} β_{ik} + ∑_{i ∈ N_C} λ_i + ∑_{k ∈ N_S} m_k μ_k + m^2 μ_0`.
The minimum over `N_S` needs at least one satellite (`hns`). -/
def LBR (hns : 0 < I.ns) (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ)
    (μ : Fin I.ns → ℝ) (μ0 : ℝ) : ℝ :=
  ∑ i, (Finset.univ : Finset (Fin I.ns)).inf'
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hns⟩⟩) (fun k => β i k)
    + ∑ i, lam i + ∑ k, (I.m k : ℝ) * μ k + (I.m2 : ℝ) * μ0

/-- `LBW(M)` (§5.1, p. 305):
`LBW(M) = ∑_{i ∈ N_C} min_{k ∈ N_S(M)} β_{ik} + ∑_{i ∈ N_C} λ_i + ∑_{k ∈ N_S(M)} m_k μ_k + m^2 μ_0`.
The minimum over `N_S(M)` needs `N_S(M)` nonempty (`hM`). -/
def LBW (RS : RouteSystem I) (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ)
    (μ : Fin I.ns → ℝ) (μ0 : ℝ) (M : Finset RS.FR) (hM : (NS RS M).Nonempty) : ℝ :=
  ∑ i, (NS RS M).inf' hM (fun k => β i k)
    + ∑ i, lam i + ∑ k ∈ NS RS M, (I.m k : ℝ) * μ k + (I.m2 : ℝ) * μ0

end TwoEchelonCVRP.Config


