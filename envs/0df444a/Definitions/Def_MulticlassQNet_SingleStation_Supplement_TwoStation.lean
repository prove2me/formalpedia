-- Prove2me | Definitions.Def_MulticlassQNet_SingleStation_Supplement_TwoStation
-- name    : MulticlassQNet_SingleStation_Supplement_TwoStation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:27:34.84844+00:00
-- url     : https://prove2.me/theorems/728633e4-577d-42e9-a9bb-8436a72d9a85
-- title:
--   §3 — the simple two-station network of Figure 1 as a three-class open network
-- statement:
--   The **two-station network** of §3 has two types of customers. Type 1 customers arrive as a Poisson stream of rate $\lambda_1$, are served at station 1 and then at station 2, and leave. Type 2 customers arrive as a Poisson stream of rate $\lambda_2$, are served only at station 1, and leave. The paper's three classes are
--
--   1. class 1: type 1 customers at station 1;
--   2. class 2: type 2 customers at station 1;
--   3. class 3: type 1 customers at station 2.
--
--   Service times are exponential. Both types have the same service rate $\mu_1$ at station 1, and class 3 is served at rate $\mu_2$ at station 2. In the notation of §2 this is the open network with $N=2$ stations, $R=3$ classes, $\sigma(1)=\sigma(2)=1$, $\sigma(3)=2$, routing $p_{13}=1$ and all other $p_{rs}=0$ (classes 2 and 3 exit), external arrival rates $(\lambda_{01},\lambda_{02},\lambda_{03})=(\lambda_1,\lambda_2,0)$ and service rates $(\mu_1,\mu_1,\mu_2)$.
--
--   This network is the illustrative example of §3; Theorems 3.1 and 3.2 bound its mean response times over all scheduling policies.
--
--   **Formalization Note** The network is an instance of the published `MulticlassQNet.FirstOrder.Network` with `N = 2`, `R = 3`; classes and stations are indexed from `0`, so the paper's class $r$ is index $r-1$. The construction takes the hypotheses $\lambda_1,\lambda_2\ge0$ and $\mu_1,\mu_2>0$ needed by the network record. The paper writes the second-station rate as $\mu_3$ on p. 8 and as $\mu_2$ in Theorems 3.1–3.2; it is one parameter here.
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), pp. 7–8, §3 and Figure 1

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network

namespace MulticlassQNet.SingleStation.Supplement

open MulticlassQNet.FirstOrder

/-- The two-station network of §3 (pp. 7–8, Figure 1) as an instance of the published open
network data. Classes (index base 0): `0` = type-1 customers at station 1 (the paper's class 1),
`1` = type-2 customers at station 1 (class 2), `2` = type-1 customers at station 2 (class 3).
Stations: `0` = station 1, `1` = station 2. Class 1 jobs are routed to class 3 with probability
one; classes 2 and 3 exit. External arrival rates are `λ₁, λ₂, 0`; service rates are the common
first-station rate `μ₁` for classes 1 and 2, and the second-station rate `μ₂` for class 3 (written
`μ₃` on p. 8). -/
def twoStation (lam1 lam2 mu1 mu2 : ℝ) (h1 : 0 ≤ lam1) (h2 : 0 ≤ lam2) (hm1 : 0 < mu1)
    (hm2 : 0 < mu2) : Network 2 3 where
  σ := ![0, 0, 1]
  p := fun r s => if r = 0 ∧ s = 2 then 1 else 0
  lam0 := ![lam1, lam2, 0]
  μ := ![mu1, mu1, mu2]
  p_nonneg := by
    intro r s
    split_ifs <;> norm_num
  p_row_sum_le_one := by
    intro r
    fin_cases r <;> simp
  lam0_nonneg := by
    intro r
    fin_cases r <;> simp [h1, h2]
  μ_pos := by
    intro r
    fin_cases r <;> simp [hm1, hm2]

end MulticlassQNet.SingleStation.Supplement


