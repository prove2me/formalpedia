-- Prove2me | Definitions.Def_MulticlassQNet_SingleStation_Supplement_ThirdMoments
-- name    : MulticlassQNet_SingleStation_Supplement_ThirdMoments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:29:36.767274+00:00
-- url     : https://prove2.me/theorems/0624cd35-a4ea-4728-8909-3230c8df76f7
-- title:
--   §7.1 — third-order moments H_rjk, M_jk, J_rjk, the modified Assumption A, and the cubic drift polynomial
-- statement:
--   Consider an open multiclass network with fixed routing (§2) and a sequencing policy whose Markov chain has invariant distribution $\pi$. The **modified Assumption A** of §7.1 requires that $\pi$ be the unique invariant distribution and that $E[n_r^3]<\infty$ for every class $r$. Besides $n_r=E[n_r]$ and $I_{rj}=E[1\{B_r\}n_j]$, §7.1 uses
--
--   $$H_{rjk}=E[1\{B_r\}n_jn_k],\qquad M_{jk}=E[n_jn_k],\qquad J_{rjk}=E[n_rn_jn_k].$$
--
--   For a vector $f=(f_1,\dots,f_R)$ of f-parameters, the traffic solution $\lambda$, and $p_{r0}=1-\sum_s p_{rs}$, the **cubic drift polynomial** is
--
--   $$\begin{aligned}
--   \Phi(f)={}&\sum_r\lambda_{0r}\Big[3f_r\sum_{j,k}f_jf_kM_{jk}+3f_r^2\sum_j f_jn_j+f_r^3\Big]
--   +3\sum_r\mu_r\Big\{\sum_s p_{rs}(f_s-f_r)-p_{r0}f_r\Big\}\sum_{j,k}f_jf_kH_{rjk}\\
--   &+3\sum_r\mu_r\Big\{\sum_s p_{rs}(f_s-f_r)^2+p_{r0}f_r^2\Big\}\sum_j f_jI_{rj}
--   +\sum_r\lambda_r\Big\{\sum_s p_{rs}(f_s-f_r)^3-p_{r0}f_r^3\Big\}.
--   \end{aligned}$$
--
--   It is the stationary expectation of the drift of $R^3$, $R=\sum_r f_rn_r$, written in these variables. Its coefficients are the left-hand sides of (48)–(50).
--
--   **Formalization Note** $H$ is `ThirdOrder.H P π`, $M$ is `secondMoment π`, $J$ is `thirdMoment π`; all are `tsum`s over $\mathbb N^R$. `cubicPoly` takes the variables as arguments, so it is a polynomial identity to be checked for the actual moments, not a constraint built into their definition.
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), p. 28, §7.1 (definitions of H, M, J and modified Assumption A); p. 29, proof of Theorem 7.1

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics

namespace MulticlassQNet.SingleStation.Supplement

open MulticlassQNet.FirstOrder

namespace ThirdOrder

variable {N R : ℕ} {net : Network N R} (P : Policy net)

/-- The modified Assumption A of §7.1 (p. 28): `π` is the unique invariant distribution of the
policy's chain and `E_π[n_r³] < ∞` for every class `r`. -/
def AssumptionA3 (π : (Fin R → ℕ) → ℝ) : Prop :=
  P.IsInvariant π ∧ (∀ π', P.IsInvariant π' → π' = π) ∧
    ∀ r, Summable (fun n => π n * ((n r : ℝ)) ^ 3)

/-- `H_{rjk} = E[1{B_r} n_j n_k]` (p. 28). -/
noncomputable def H (π : (Fin R → ℕ) → ℝ) (r j k : Fin R) : ℝ :=
  ∑' n, π n * P.busy n r * (n j : ℝ) * (n k : ℝ)

end ThirdOrder

/-- `M_{jk} = E[n_j n_k]` (p. 28). -/
noncomputable def secondMoment {R : ℕ} (π : (Fin R → ℕ) → ℝ) (j k : Fin R) : ℝ :=
  ∑' n, π n * (n j : ℝ) * (n k : ℝ)

/-- `J_{rjk} = E[n_r n_j n_k]` (p. 28). -/
noncomputable def thirdMoment {R : ℕ} (π : (Fin R → ℕ) → ℝ) (r j k : Fin R) : ℝ :=
  ∑' n, π n * (n r : ℝ) * (n j : ℝ) * (n k : ℝ)

/-- The cubic polynomial in the f-parameters `f` obtained (proof of Theorem 7.1, p. 29) by
taking stationary expectations in the drift of `R³`, `R = ∑_r f(r) n_r`, with `λ` the solution
of the traffic equations, `p_{r0} = 1 - ∑_s p_{rs}` the exit probability, and `n, I, H, M` the
variables `n_r, I_{rj}, H_{rjk}, M_{jk}`:
`∑_r λ_{0r}[3 f_r ∑_{j,k} f_j f_k M_{jk} + 3 f_r² ∑_j f_j n_j + f_r³]
 + 3 ∑_r μ_r {∑_s p_{rs}(f_s − f_r) − p_{r0} f_r} ∑_{j,k} f_j f_k H_{rjk}
 + 3 ∑_r μ_r {∑_s p_{rs}(f_s − f_r)² + p_{r0} f_r²} ∑_j f_j I_{rj}
 + ∑_r λ_r {∑_s p_{rs}(f_s − f_r)³ − p_{r0} f_r³}`. -/
def cubicPoly {N R : ℕ} (net : Network N R) (lam f n : Fin R → ℝ) (I : Fin R → Fin R → ℝ)
    (H : Fin R → Fin R → Fin R → ℝ) (M : Fin R → Fin R → ℝ) : ℝ :=
  ∑ r, net.lam0 r * (3 * f r * ∑ j, ∑ k, f j * f k * M j k + 3 * f r ^ 2 * ∑ j, f j * n j
      + f r ^ 3)
  + 3 * ∑ r, net.μ r * (∑ s, net.p r s * (f s - f r) - net.exitProb r * f r)
      * ∑ j, ∑ k, f j * f k * H r j k
  + 3 * ∑ r, net.μ r * (∑ s, net.p r s * (f s - f r) ^ 2 + net.exitProb r * f r ^ 2)
      * ∑ j, f j * I r j
  + ∑ r, lam r * (∑ s, net.p r s * (f s - f r) ^ 3 - net.exitProb r * f r ^ 3)

end MulticlassQNet.SingleStation.Supplement


