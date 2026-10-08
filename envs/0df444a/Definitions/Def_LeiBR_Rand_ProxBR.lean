-- Prove2me | Definitions.Def_LeiBR_Rand_ProxBR
-- name    : LeiBR_Rand_ProxBR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:34.627094+00:00
-- url     : https://prove2.me/theorems/837b00b7-f86f-4688-a8bb-a7f094ee8acc
-- title:
--   (2)–(4), (7), Assumption 2 — the proximal best-response map, the matrix $\Gamma$ and $a = \|\Gamma\|$
-- statement:
--   Fix a game with strategy sets $X_i$ and costs $f_i$, and a regularization parameter $\mu > 0$.
--
--   1. The **proximal best response** of player $i$ to a profile $y \in X$ is
--   $$\widehat x_i(y) = \operatorname*{argmin}_{x_i \in X_i}\Big[f_i(x_i, y_{-i}) + \frac{\mu}{2}\|x_i - y_i\|^2\Big].$$
--   2. With $\nabla^2_{x_i x_j} f_i(x)$ the $(i,j)$ block of the Hessian of $f_i$, set
--   $$\zeta_{i,\min} = \inf_{x \in X} \lambda_{\min}\big(\nabla^2_{x_i} f_i(x)\big), \qquad \zeta_{ij,\max} = \sup_{x \in X}\big\|\nabla^2_{x_i x_j} f_i(x)\big\| \quad (j \ne i),$$
--   where $\lambda_{\min}(A)$ is the smallest eigenvalue of $(A + A^{\top})/2$ and $\|\cdot\|$ is the spectral norm.
--   3. The $N \times N$ matrix $\Gamma = [\gamma_{ij}]$ has entries
--   $$\gamma_{ii} = \frac{\mu}{\mu + \zeta_{i,\min}}, \qquad \gamma_{ij} = \frac{\zeta_{ij,\max}}{\mu + \zeta_{i,\min}} \quad (j \ne i).$$
--   4. $a = \|\Gamma\|$ is the spectral norm of $\Gamma$, and **Assumption 2** is $\|\Gamma\| < 1$.
--
--   The matrix $\Gamma$ measures how strongly a change in the rivals' strategies moves each player's proximal best response; Assumption 2 makes the proximal BR map a contraction.
--
--   **Formalization Note** The best response is any map `xhat` such that, for every feasible $y$ and every $i$, `xhat y i` lies in $X_i$ and minimizes the proximal objective over $X_i$ (`IsProxBR`); under Assumption 1 the minimizer exists and is unique, so this pins `xhat` down on $X$. The Hessian blocks are read off the second Fréchet derivative of $f_i$ on the whole profile, restricted by the coordinate embeddings. $\lambda_{\min}$ of the symmetric part is written as the infimum of the Rayleigh quotient $v^\top \nabla^2_{x_i} f_i(x) v$ over unit $v$. $\|\Gamma\|$ is the operator norm of $\Gamma$ acting on Euclidean $\mathbb R^N$. The infimum and supremum are over a nonempty bounded set under Assumption 1 (compact $X$, $f_i$ of class $C^2$ on a neighbourhood).
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 4 (Notations, λmin), p. 5, (2)–(4); p. 6, (7); p. 7, Assumption 2

import Mathlib
import Definitions.Def_LeiBR_Rand_Game

namespace LeiBR.Rand

variable {N : ℕ} {n : Fin N → ℕ}

/-- The embedding `ι_i : ℝ^{n_i} → ∏_j ℝ^{n_j}`, `v ↦ (0, …, v, …, 0)`. -/
noncomputable def blockEmb (n : Fin N → ℕ) (i : Fin N) : LeiBR.Sync.Strat n i →L[ℝ] LeiBR.Sync.Profile n :=
  ContinuousLinearMap.single ℝ (fun j => LeiBR.Sync.Strat n j) i

/-- The `(i, j)` block `∇²_{x_i x_j} g(x)` of the second derivative of `g` at `x`, as the bilinear
map `(u, v) ↦ D²g(x)(ι_i u, ι_j v)` on `ℝ^{n_i} × ℝ^{n_j}`. Its operator norm is the spectral norm
of the `n_i × n_j` Hessian block. -/
noncomputable def hessBlock (g : LeiBR.Sync.Profile n → ℝ) (x : LeiBR.Sync.Profile n) (i j : Fin N) :
    LeiBR.Sync.Strat n i →L[ℝ] LeiBR.Sync.Strat n j →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (LeiBR.Sync.Strat n j) (LeiBR.Sync.Profile n) ℝ).flip (blockEmb n j)).comp
    ((fderiv ℝ (fderiv ℝ g) x).comp (blockEmb n i))

/-- `ζ_{i,min} = inf_{x ∈ X} λ_min(∇²_{x_i} f_i(x))`, (4). The smallest eigenvalue of the
symmetric part of `∇²_{x_i} f_i(x)` is its minimal Rayleigh quotient, so this is the infimum of
`vᵀ ∇²_{x_i} f_i(x) v` over `x ∈ X` and unit vectors `v ∈ ℝ^{n_i}`. -/
noncomputable def zetaMin (G : Game N n) (i : Fin N) : ℝ :=
  sInf {r : ℝ | ∃ x, G.Feasible x ∧ ∃ v : LeiBR.Sync.Strat n i, ‖v‖ = 1 ∧ r = hessBlock (G.f i) x i i v v}

/-- `ζ_{ij,max} = sup_{x ∈ X} ‖∇²_{x_i x_j} f_i(x)‖` (spectral norm), (4). -/
noncomputable def zetaMax (G : Game N n) (i j : Fin N) : ℝ :=
  sSup {r : ℝ | ∃ x, G.Feasible x ∧ r = ‖hessBlock (G.f i) x i j‖}

/-- The `N × N` matrix `Γ` of (3): `γ_ii = µ/(µ + ζ_{i,min})`,
`γ_ij = ζ_{ij,max}/(µ + ζ_{i,min})` for `j ≠ i`. -/
noncomputable def Gamma (G : Game N n) (mu : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i = j then mu / (mu + zetaMin G i) else zetaMax G i j / (mu + zetaMin G i)

/-- `a = ‖Γ‖`, the spectral norm (operator norm on Euclidean `ℝ^N`) of `Γ`. -/
noncomputable def contrFactor (G : Game N n) (mu : ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N) (Gamma G mu)‖

/-- Assumption 2: `‖Γ‖ < 1`. -/
def Assumption2 (G : Game N n) (mu : ℝ) : Prop := contrFactor G mu < 1

/-- `xhat` is the proximal best-response map (2)/(7): for every feasible `y` and every player `i`,
`xhat y i ∈ X_i` minimizes `z ↦ f_i(z, y_{-i}) + (µ/2)‖z − y_i‖²` over `X_i`. -/
def IsProxBR (G : Game N n) (mu : ℝ) (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) : Prop :=
  ∀ y, G.Feasible y → ∀ i, xhat y i ∈ G.X i ∧
    IsMinOn (fun z => G.f i (Function.update y i z) + mu / 2 * ‖z - y i‖ ^ 2) (G.X i) (xhat y i)

end LeiBR.Rand


