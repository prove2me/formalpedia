-- Prove2me | Definitions.Def_RollingProbeQN_Convex_iterData__5c24ab
-- name    : RollingProbeQN_Convex_iterData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:22:54.787199+00:00
-- url     : https://prove2.me/theorems/5c24abb1-0d1a-4538-93ff-06c66c1ec9e8
-- title:
--   One iteration of Algorithm 1 (RP-QNPE) against a gradient oracle
-- statement:
--   Given an oracle $G$ (in the theorems $G=\nabla f$) and the state at the start of iteration $k$, one iteration computes:
--
--   1. **Refresh (4).** The group $g_{i_k}$ with $i_k=(k\bmod\chi)+1$; $\tau_k=b/(\sqrt\chi\,L_2\,|g_{i_k}|\,(k+1)^2)$; $u_k=(G(x_k+\tau_kv_{g_{i_k}})-G(x_k))/\tau_k$; $M_ke_j=P_ju_k$ for $j\in g_{i_k}$ and $M_ke_j=M_{k-1}e_j$ otherwise; $B_k=\Pi_{\mathcal Z}((M_k+M_k^\top)/2)$.
--   2. **Certificate (5).** $\bar E_k=L_1$ for $k<\chi$, and for $k\ge\chi$
--   $$\bar E_k=\min\Big\{L_1,\ 2L_2\sum_{j=k-\chi+1}^{k-1}\delta_j+\frac{b}{(k-\chi+2)^2}\Big\}.$$
--   3. **Stepsize.** $\lambda_k$ from Subroutine 1.1 with inputs $A_k$, $\zeta_k=\|z_k-x_k\|$, $g_k=\|G(x_k)\|$, $\bar E_k$; $a_k=a(\lambda_k)$, $A_{k+1}=A_k+a_k$, $y_k=(A_kx_k+a_kz_k)/A_{k+1}$.
--   4. **Model step and momentum.** $r_k=-(B_k+\lambda_k^{-1}I)^{-1}G(y_k)$, $x_{k+1}=y_k+r_k$, $z_{k+1}=z_k-a_kG(x_{k+1})$.
--
--   **Formalization Note** $G(x_k)$ is the cached value, so one iteration calls the oracle at the probe point, at $y_k$ and at $x_{k+1}$ only. The refreshed group has 0-based label $k\bmod\chi$.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Algorithm 1, (4), (5), Subroutine 1.1, pp. 9–10

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_colProj
import Definitions.Def_RollingProbeQN_Convex_groupVec
import Definitions.Def_RollingProbeQN_Convex_groupCard
import Definitions.Def_RollingProbeQN_Convex_clipZ
import Definitions.Def_RollingProbeQN_Convex_aOf
import Definitions.Def_RollingProbeQN_Convex_yOf
import Definitions.Def_RollingProbeQN_Convex_subroutine11
import Definitions.Def_RollingProbeQN_Convex_modelStep
import Definitions.Def_RollingProbeQN_Convex_Config
import Definitions.Def_RollingProbeQN_Convex_RunState
import Definitions.Def_RollingProbeQN_Convex_IterData

namespace RollingProbeQN.Convex

/-- **Steps 1–4 of one iteration of Algorithm 1 against an oracle `G`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 1, (4), (5), Subroutine 1.1, pp. 9–10. From the state at the start of iteration
`k`:
1. (4): the refreshed group is `g_{i_k}` with `i_k = (k mod χ) + 1`;
   `τ_k = b/(√χ L2 |g_{i_k}| (k+1)²)`, `u_k = (∇f(x_k + τ_k v_{g_{i_k}}) − ∇f(x_k))/τ_k`,
   `M_k e_j = P_j u_k` for `j ∈ g_{i_k}` and `M_k e_j = M_{k−1} e_j` otherwise,
   `B_k = Π_Z((M_k + M_k^T)/2)`;
2. (5): `Ē_k = L1` for `k < χ`, and `Ē_k = min{L1, 2 L2 D̂_k + e_k}` for `k ≥ χ`, with
   `D̂_k = ∑_{j=k−χ+1}^{k−1} δ_j` and `e_k = b/(k − χ + 2)²`;
3. Subroutine 1.1 with inputs `A_k`, `ζ_k = ‖z_k − x_k‖`, `g_k = ‖∇f(x_k)‖`, `Ē_k` gives `λ_k`;
   `a_k = a(λ_k)`, `A_{k+1} = A_k + a_k`, `y_k = (A_k x_k + a_k z_k)/A_{k+1}`;
4. `r_k = −(B_k + λ_k^{−1} I)^{−1} ∇f(y_k)`, `x_{k+1} = y_k + r_k`, `z_{k+1} = z_k − a_k ∇f(x_{k+1})`.

**Formalization Note.** Every gradient is a call of the oracle `G` (reading R3); `∇f(x_k)` is the
cached `st.gx`, so an iteration calls `G` at the probe point, at `y_k` and at `x_{k+1}` only. The
refreshed group has 0-based label `k % χ` (reading R5). The window `{k−χ+1, …, k−1}` is
`Finset.Ico (k + 1 − χ) k`, used only for `k ≥ χ`, where the natural subtraction is exact. -/
noncomputable def iterData {d χ : ℕ} (cfg : Config d χ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (k : ℕ) (st : RunState d) :
    IterData d :=
  let τ : ℝ := cfg.b / (Real.sqrt χ * cfg.L₂ * (groupCard cfg.grp (k % χ) : ℝ) * ((k : ℝ) + 1) ^ 2)
  let probe : EuclideanSpace ℝ (Fin d) := st.x + τ • groupVec cfg.grp (k % χ)
  let u : EuclideanSpace ℝ (Fin d) := τ⁻¹ • (G probe - st.gx)
  let M : Matrix (Fin d) (Fin d) ℝ :=
    fun i j => if (cfg.grp j : ℕ) = k % χ then colProj cfg.S j u i else st.M i j
  let B : Matrix (Fin d) (Fin d) ℝ := clipZ cfg.L₁ ((1 / 2 : ℝ) • (M + M.transpose))
  let Ebar : ℝ := if k < χ then cfg.L₁ else
    min cfg.L₁ (2 * cfg.L₂ * (∑ j ∈ Finset.Ico (k + 1 - χ) k, st.δ j)
      + cfg.b / ((k : ℝ) - (χ : ℝ) + 2) ^ 2)
  let out : ℝ × ℕ := subroutine11 cfg.L₁ cfg.L₂ cfg.σ st.A ‖st.z - st.x‖ ‖st.gx‖ Ebar
  let a : ℝ := aOf st.A out.1
  let y : EuclideanSpace ℝ (Fin d) := yOf st.A st.x st.z out.1
  let r : EuclideanSpace ℝ (Fin d) := modelStep B out.1 (G y)
  let gx' : EuclideanSpace ℝ (Fin d) := G (y + r)
  { τ := τ, probe := probe, M := M, B := B, Ebar := Ebar, lam := out.1, nEval := out.2, a := a,
    A' := st.A + a, y := y, r := r, x' := y + r, gx' := gx', z' := st.z - a • gx' }

end RollingProbeQN.Convex


