-- Prove2me | Definitions.Def_AdamDyn_ConstStep_adamMap
-- name    : AdamDyn_ConstStep_adamMap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:42.935186+00:00
-- url     : https://prove2.me/theorems/129c0c4b-66d1-44c6-a3da-2c753b6284a2
-- title:
--   The Adam map $T_{\gamma,\alpha,\beta}$ (2.1), the constant-step iterates (2.5), interpolation (2.3) and truncation $B_R$
-- statement:
--   Let $\nabla f(x,\xi)\in\mathbb R^d$ denote a stochastic gradient, $\gamma>0$ a step size, $\alpha,\beta\in[0,1)$ and $\varepsilon>0$. For $n\ge 1$ and $z=(x,m,v)\in\mathcal Z_+$ the **Adam map** is
--
--   $$
--   T_{\gamma,\alpha,\beta}(n,z,\xi) = \begin{pmatrix} x - \dfrac{\gamma(1-\alpha^n)^{-1}(\alpha m + (1-\alpha)\nabla f(x,\xi))}{\varepsilon + (1-\beta^n)^{-1/2}(\beta v + (1-\beta)\nabla f(x,\xi)^{\odot 2})^{1/2}} \\ \alpha m + (1-\alpha)\nabla f(x,\xi) \\ \beta v + (1-\beta)\nabla f(x,\xi)^{\odot 2}\end{pmatrix},
--   $$
--
--   with all operations coordinatewise. Given functions $\bar\alpha,\bar\beta$ of the step size, the paper sets:
--
--   1. $H_\gamma(n,z,\xi) := \gamma^{-1}\big(T_{\gamma,\bar\alpha(\gamma),\bar\beta(\gamma)}(n,z,\xi) - z\big)$;
--   2. $e_\gamma(n,z) := \big(x,\ (1-\bar\alpha(\gamma)^n)^{-1}m,\ (1-\bar\beta(\gamma)^n)^{-1}v\big)$ for $n\ge1$ and $e_\gamma(0,z) := z$;
--   3. the **constant-step Adam iterates** $z^\gamma_0 = (x_0,0,0)$ and $z^\gamma_n = T_{\gamma,\bar\alpha(\gamma),\bar\beta(\gamma)}(n,z^\gamma_{n-1},\xi_n)$ for $n\ge1$, along a sample sequence $(\xi_n)_{n\ge1}$;
--   4. the **interpolation map** $\mathsf X_\gamma(u)(t) := u_{\lfloor t/\gamma\rfloor} + (t/\gamma - \lfloor t/\gamma\rfloor)(u_{\lfloor t/\gamma\rfloor+1} - u_{\lfloor t/\gamma\rfloor})$ for $t\ge0$, so that $\mathsf z^\gamma = \mathsf X_\gamma(z^\gamma)$ is the piecewise linear process (2.3);
--   5. the exit time $\tau_R(u) := \inf\{n\in\mathbb N : \|e_\gamma(n,u_n)\| > R\}$, equal to $+\infty$ when the set is empty, and the stopped sequence $B_R(u)(n) := u_n\mathbb 1_{n<\tau_R(u)} + u_{\tau_R(u)}\mathbb 1_{n\ge\tau_R(u)}$;
--   6. the truncated iterates $z^{\gamma,R} := B_R(z^\gamma)$ and their normalised increments $\gamma^{-1}(z^{\gamma,R}_{n+1}-z^{\gamma,R}_n)$.
--
--   These are the discrete-time objects of the constant-step analysis of Adam.
--
--   **Formalization Note** The iterates are defined pathwise for a fixed realisation $(\xi_n)$; $\xi_0$ is unused. $(1-\beta^n)^{-1/2}$ is a real power and the square root is `Real.sqrt`; both are only evaluated at $n\ge1$ and on $\mathcal Z_+$ in the paper's use. $\tau_R$ takes values in $\mathbb N\cup\{+\infty\}$ (`ℕ∞`), and its norm is the Euclidean norm of $\mathbb R^{3d}$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 3, Algorithm 2.1 and Eq. (2.1); p. 4, Eqs. (2.3), (2.5); pp. 21–22, §8.1 (H_γ, e_γ, τ_R, B_R, z^{γ,R}, X_γ)

import Mathlib
import Definitions.Def_AdamDyn_ConstStep_adamField

open scoped ENNReal

namespace AdamDyn.ConstStep

/-- The Adam map `T_{γ,α,β}(n, z, ξ)` of (2.1), p. 3, for `z = (x, m, v) ∈ 𝒵₊`, `n ≥ 1`, where
`gf x ξ` is the stochastic gradient `∇f(x, ξ)`:
`x − γ(1−αⁿ)⁻¹(αm + (1−α)∇f) / (ε + (1−βⁿ)^{−1/2}(βv + (1−β)∇f^{⊙2})^{1/2})`,
`αm + (1−α)∇f`, `βv + (1−β)∇f^{⊙2}`, all operations coordinatewise. -/
noncomputable def adamMap {d : ℕ} {Ξ : Type*} (gf : E d → Ξ → E d) (γ α β ε : ℝ) (n : ℕ)
    (z : Z d) (ξ : Ξ) : Z d :=
  (WithLp.toLp 2 (fun i => z.1 i - γ * (1 - α ^ n)⁻¹ * (α * z.2.1 i + (1 - α) * gf z.1 ξ i) /
      (ε + (1 - β ^ n) ^ (-(1 / 2 : ℝ)) * Real.sqrt (β * z.2.2 i + (1 - β) * gf z.1 ξ i ^ 2))),
   WithLp.toLp 2 (fun i => α * z.2.1 i + (1 - α) * gf z.1 ξ i),
   WithLp.toLp 2 (fun i => β * z.2.2 i + (1 - β) * gf z.1 ξ i ^ 2))

/-- `H_γ(n, z, ξ) := γ⁻¹ (T_{γ,ᾱ(γ),β̄(γ)}(n, z, ξ) − z)`, §8.1, p. 21. -/
noncomputable def HGamma {d : ℕ} {Ξ : Type*} (gf : E d → Ξ → E d) (αbar βbar : ℝ → ℝ) (ε γ : ℝ)
    (n : ℕ) (z : Z d) (ξ : Ξ) : Z d :=
  γ⁻¹ • (adamMap gf γ (αbar γ) (βbar γ) ε n z ξ - z)

/-- `e_γ(n, z) := (x, (1 − ᾱ(γ)ⁿ)⁻¹ m, (1 − β̄(γ)ⁿ)⁻¹ v)` for `n ≥ 1` and `e_γ(0, z) := z`,
§8.1, p. 21. -/
noncomputable def eGamma {d : ℕ} (αbar βbar : ℝ → ℝ) (γ : ℝ) (n : ℕ) (z : Z d) : Z d :=
  if n = 0 then z else (z.1, (1 - αbar γ ^ n)⁻¹ • z.2.1, (1 - βbar γ ^ n)⁻¹ • z.2.2)

/-- The constant-step Adam iterates (2.5), p. 4, along a realisation `ξs : ℕ → Ξ` of the
sample sequence (`ξs n` is `ξ_n`; `ξs 0` is unused): `z^γ_0 = (x0, 0, 0)` and
`z^γ_n = T_{γ,ᾱ(γ),β̄(γ)}(n, z^γ_{n−1}, ξ_n)` for `n ≥ 1`. -/
noncomputable def adamIter {d : ℕ} {Ξ : Type*} (gf : E d → Ξ → E d) (αbar βbar : ℝ → ℝ)
    (ε γ : ℝ) (x0 : E d) (ξs : ℕ → Ξ) : ℕ → Z d
  | 0 => (x0, 0, 0)
  | n + 1 => adamMap gf γ (αbar γ) (βbar γ) ε (n + 1) (adamIter gf αbar βbar ε γ x0 ξs n)
      (ξs (n + 1))

/-- The interpolation map `X_γ` (p. 22) / interpolated process (2.3), p. 4:
`X_γ(u)(t) = u_{⌊t/γ⌋} + (t/γ − ⌊t/γ⌋)(u_{⌊t/γ⌋+1} − u_{⌊t/γ⌋})`, used for `t ≥ 0`. -/
noncomputable def interp {d : ℕ} (γ : ℝ) (u : ℕ → Z d) (t : ℝ) : Z d :=
  u ⌊t / γ⌋₊ + (t / γ - (⌊t / γ⌋₊ : ℝ)) • (u (⌊t / γ⌋₊ + 1) - u ⌊t / γ⌋₊)

/-- `τ_R(u) := inf {n ∈ ℕ : ‖e_γ(n, u_n)‖ > R}`, with `τ_R(u) = +∞` when the set is empty,
§8.1, p. 21 (the infimum in `ℕ∞`, whose empty infimum is `⊤`). -/
noncomputable def stopTime {d : ℕ} (αbar βbar : ℝ → ℝ) (γ R : ℝ) (u : ℕ → Z d) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : R < zNorm (eGamma αbar βbar γ n (u n))), (n : ℕ∞)

/-- The stopped sequence `B_R(u)(n) = u_n 1_{n < τ_R(u)} + u_{τ_R(u)} 1_{n ≥ τ_R(u)}`, p. 22. -/
noncomputable def stopSeq {d : ℕ} (αbar βbar : ℝ → ℝ) (γ R : ℝ) (u : ℕ → Z d) (n : ℕ) : Z d :=
  if (n : ℕ∞) < stopTime αbar βbar γ R u then u n else u (stopTime αbar βbar γ R u).toNat

/-- The truncated iterates `z^{γ,R} := B_R(z^γ)`, p. 22, along a realisation `ξs`. -/
noncomputable def truncIter {d : ℕ} {Ξ : Type*} (gf : E d → Ξ → E d) (αbar βbar : ℝ → ℝ)
    (ε γ R : ℝ) (x0 : E d) (ξs : ℕ → Ξ) : ℕ → Z d :=
  stopSeq αbar βbar γ R (adamIter gf αbar βbar ε γ x0 ξs)

/-- The normalised increment `γ⁻¹ (z^{γ,R}_{n+1} − z^{γ,R}_n)`, p. 22. -/
noncomputable def truncIncr {d : ℕ} {Ξ : Type*} (gf : E d → Ξ → E d) (αbar βbar : ℝ → ℝ)
    (ε γ R : ℝ) (x0 : E d) (ξs : ℕ → Ξ) (n : ℕ) : Z d :=
  γ⁻¹ • (truncIter gf αbar βbar ε γ R x0 ξs (n + 1) - truncIter gf αbar βbar ε γ R x0 ξs n)

end AdamDyn.ConstStep


