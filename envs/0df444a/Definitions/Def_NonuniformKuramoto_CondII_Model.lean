-- Prove2me | Definitions.Def_NonuniformKuramoto_CondII_Model
-- name    : NonuniformKuramoto_CondII_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:42.032339+00:00
-- url     : https://prove2.me/theorems/67ac9948-bf1c-4d0f-a158-c1cbd7e6f223
-- title:
--   Non-uniform Kuramoto model (8) on lifts, the arc set ∆(γ), solutions, positive invariance, and the standing assumptions of §V.B
-- statement:
--   The **non-uniform Kuramoto model** of Dörfler and Bullo is the system of $n$ coupled phase oscillators
--   $$
--   D_i\dot\theta_i=\omega_i-\sum_{j=1}^n P_{ij}\sin(\theta_i-\theta_j+\varphi_{ij}),\qquad i\in\{1,\dots,n\},\tag{8}
--   $$
--   with time constants $D_i$, natural frequencies $\omega_i$, coupling weights $P_{ij}$ and phase shifts $\varphi_{ij}$. Angles live on the torus; here a configuration is represented by a real lift $\theta\in\mathbb R^n$, on which the right-hand side of (8) is $2\pi$-periodic in each coordinate.
--
--   1. The **arc set** $\Delta(\gamma)$ consists of the configurations with $\max_{i,j}|\theta_i-\theta_j|<\gamma$; on lifts, $\theta_i-\theta_j<\gamma$ for all $i,j$.
--   2. A **solution** on $[0,\infty)$ is a function $\theta:\mathbb R\to\mathbb R^n$ whose derivative (one-sided at $t=0$) at every $t\ge0$ equals the right-hand side of (8), divided by $D_i$, at $\theta(t)$.
--   3. A set $S$ is **positively invariant** if every solution with $\theta(0)\in S$ satisfies $\theta(t)\in S$ for all $t\ge0$.
--   4. The **standing assumptions** of §V.B: $n\ge2$; $D_i>0$; for $i\ne j$, $P_{ij}\ge0$ and $\varphi_{ij}\in[0,\pi/2[$; by convention $P_{ii}=\varphi_{ii}=0$; $P=P^T$ and the non-zero weights induce a connected graph; and $\varphi_{ij}=\varphi_{ji}$.
--
--   The model arises as the slow dynamics of a network-reduced power system, where $\varphi_{ij}$ encodes transfer conductances (losses). Every result of the mission is stated for its solutions under the standing assumptions.
--
--   **Formalization Note** Lifts: a configuration in $\Delta(\pi)$ has a lift whose coordinates differ by less than $\pi$, and along a continuous lifted trajectory the real differences are the geodesic ones, so statements about lifts are at least as strong as their torus versions. $\dot\theta$ always means the vector field evaluated along the solution. The symmetry $\varphi_{ij}=\varphi_{ji}$ is not written on the page; it is needed for $L(P_{ij}\cos\varphi_{ij})$ to be a symmetric Laplacian whose $\lambda_2$ is the algebraic connectivity used in (33), and it holds for the power network ($\varphi_{ij}=\arctan(\Re Y_{ij}/\Im Y_{ij})$ with $Y=Y^T$, p. 6). §V.B allows zero weights ("some weights $P_{ij}=P_{ji}$ can be zero", p. 23), hence $P_{ij}\ge0$ instead of p. 8's $P_{ij}>0$.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 8, (8) and its parameter assumptions; p. 5, ∆(γ); p. 16, (18) and §V's relaxed graph assumptions; p. 23, P = Pᵀ connected

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondI_Model

namespace NonuniformKuramoto.CondII

/-- Positive invariance of a set `S` of (lifted) configurations under (8): every solution that
starts in `S` stays in `S` for all `t ≥ 0`. -/
def IsPositivelyInvariant {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (S : (Fin n → ℝ) → Prop) : Prop :=
  ∀ θ : ℝ → Fin n → ℝ, NonuniformKuramoto.CondI.IsSolution D ω P ϕ θ → S (θ 0) → ∀ t, 0 ≤ t → S (θ t)

/-- The standing assumptions of §V.B (pp. 8, 16, 23) on the parameters of (8):
`n ≥ 2` oscillators; `D_i > 0`; `P_ij ≥ 0` and `ϕ_ij ∈ [0, π/2[` for `i ≠ j`; the conventions
`P_ii = ϕ_ii = 0`; `P = Pᵀ` with the non-zero weights inducing a connected graph; and the
symmetry `ϕ_ij = ϕ_ji`, which the section uses implicitly (the lossless coupling
`L(P_ij cos ϕ_ij)` is a symmetric Laplacian). -/
structure StandingHyp {n : ℕ} (D : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) : Prop where
  two_le : 2 ≤ n
  D_pos : ∀ i, 0 < D i
  P_nonneg : ∀ i j, i ≠ j → 0 ≤ P i j
  P_diag : ∀ i, P i i = 0
  ϕ_diag : ∀ i, ϕ i i = 0
  ϕ_nonneg : ∀ i j, i ≠ j → 0 ≤ ϕ i j
  ϕ_lt : ∀ i j, i ≠ j → ϕ i j < Real.pi / 2
  P_symm : ∀ i j, P i j = P j i
  ϕ_symm : ∀ i j, ϕ i j = ϕ j i
  connected : IsConnectedGraph P

end NonuniformKuramoto.CondII


