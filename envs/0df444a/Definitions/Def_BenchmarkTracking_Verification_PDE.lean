-- Prove2me | Definitions.Def_BenchmarkTracking_Verification_PDE
-- name    : BenchmarkTracking_Verification_PDE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:25:11.598402+00:00
-- url     : https://prove2.me/theorems/0ff0ed4d-14f8-4c0f-b2a1-c9e62efb24b6
-- title:
--   (2.8)–(2.11), (3.8), (3.15), (3.38), (4.2) — classical solutions of the Neumann problems and the HJB equation
-- statement:
--   A **classical solution** of a Neumann problem below is a function that is $C^2$ on the closed domain, satisfies the PDE pointwise on the open set indicated, and satisfies the Neumann conditions pointwise on the boundary faces. Subscripts denote partial derivatives.
--
--   1. **(3.8)**, on $(r,z)\in\mathbb R^2_+$: on $(0,\infty)^2$,
--   $$
--   \frac{\alpha^2}2l_{rr}+\Big(\frac{\alpha^2}2-\rho\Big)l_r+\frac12\sigma_Z^2z^2l_{zz}+\mu_Zzl_z+\kappa_2zl_{rz}+(\kappa_2-\mu_Z)\beta ze^{-r}+\frac{1-p}p\beta^{-\frac p{1-p}}e^{\frac p{1-p}r}=\rho l,
--   $$
--   and $l_r(0,z)=0$ for $z\ge0$.
--   2. **(3.15)**, on $(r,h)\in\mathbb R^2_+$: $\frac{\alpha^2}2\varphi_{rr}+(\frac{\alpha^2}2-\rho)\varphi_r+\frac{\sigma_B^2}2\varphi_{hh}-\mu_B\varphi_h=\rho\varphi$ on $(0,\infty)^2$, $\varphi_r(0,h)=0$, $\varphi_h(r,0)=\beta e^{-r}$.
--   3. **(3.38)**: as (3.15) with the extra term $-\kappa_1\psi_{rh}$ on the left-hand side.
--   4. **The dual problem (2.8), (2.10), (2.11)**, on $(y,h,z)\in(0,\beta]\times\mathbb R^2_+$: on $(0,\beta]\times(0,\infty)^2$,
--   $$
--   \frac{\alpha^2}2y^2\hat u_{yy}+\rho y\hat u_y+\frac{\sigma_B^2}2\hat u_{hh}-\mu_B\hat u_h+\frac12\sigma_Z^2z^2\hat u_{zz}+\mu_Zz\hat u_z+\kappa_1y\hat u_{yh}-\kappa_2zy\hat u_{yz}+\sigma_Z\sigma_B\gamma^\top\eta z\hat u_{zh}+(\kappa_2-\mu_Z)zy+\frac{1-p}py^{-\frac p{1-p}}=\rho\hat u,
--   $$
--   with $\hat u_y(\beta,h,z)=0$ for $(h,z)\in\mathbb R^2_+$ and $\hat u_h(y,0,z)=y$ for $(y,z)\in(0,\beta]\times\mathbb R_+$.
--   5. **The HJB equation (4.2)**, on $(x,h,z)\in\mathbb R^3_+$: on $(0,\infty)^3$,
--   $$
--   \sup_{\theta\in\mathbb R^d}\Big[\theta^\top\mu u_x+\tfrac12\theta^\top\sigma\sigma^\top\theta u_{xx}+\sigma_Z\theta^\top\sigma\eta z(u_{xx}-u_{xz})-\sigma_B\theta^\top\sigma\gamma u_{xh}\Big]+\sup_{c>0}\Big(\frac{c^p}p-cu_x\Big)+\frac12\sigma_B^2u_{hh}-\mu_Bu_h+\frac12\sigma_Z^2z^2(u_{zz}+u_{xx}-2u_{xz})+\mu_Zz(u_z-u_x)+\sigma_Z\sigma_Bz\eta^\top\gamma(u_{xh}-u_{hz})=\rho u,
--   $$
--   with $u_x(0,h,z)=\beta$ for $(h,z)\in\mathbb R^2_+$ and $u_h(x,0,z)=u_x(x,0,z)$ for $(x,z)\in\mathbb R^2_+$; both suprema are attained as least upper bounds in $\mathbb R$.
--
--   These are the equations that the probabilistic representation (Theorem 3.1) and its Legendre transform (Theorem 4.1) solve.
--
--   **Formalization Note** Partial derivatives are taken within the closed coordinate domains, $[0,\infty)$ or $(0,\beta]$. The suprema in (4.2) are expressed with `IsLUB`, so the equation also asserts that they are finite. The paper writes $\sup_{c\ge0}$; at $c=0$ the paper's $c^p/p$ is $0$ for $p>0$ and $-\infty$ for $p<0$, so the supremum over $c>0$ is the same, and it avoids Lean's convention $0^p=0$ for $p<0$. The paper prints (2.11) as $\hat u_z(y,0,z)=y$; the condition is $\hat u_h(y,0,z)=y$, the transform of $u_h=u_x$ at $h=0$ (the proof of Theorem 3.1 checks $v_h(r,0,z)=\beta e^{-r}$). The doubled "+ +" in (2.8) is dropped.
-- source:
--   Bo, Huang & Yu, Stochastic control problems with state-reflections arising from relaxed benchmark tracking, arXiv:2302.08302v4, p. 7 (2.8), (2.10), (2.11); p. 9 (3.8); p. 10 (3.15); p. 16 (3.38); p. 19 (4.2)

import Mathlib
import Definitions.Def_BenchmarkTracking_Verification_Model
import Definitions.Def_BenchmarkTracking_Verification_Analysis

open Set Matrix
open scoped Matrix

namespace BenchmarkTracking.Verification

/-!
Bo, Huang & Yu, arXiv:2302.08302v4: classical solutions of the Neumann problems (3.8), p. 9,
(3.15), p. 10, (3.38), p. 16, the dual problem (2.8), (2.10), (2.11), p. 7, and the primal HJB
equation (4.2), p. 19. A classical solution is `C²` on the closed domain, satisfies the PDE
pointwise on the open set the paper names, and satisfies the Neumann conditions pointwise on the
boundary faces. Partial derivatives are one-variable derivatives of coordinate sections, taken
within the closed coordinate domain (`[0, ∞)` or `(0, β]`), hence one-sided on the boundary;
for a `C²` function they are the true partial derivatives up to the boundary. A mixed
derivative `f_ab` is `∂_b(∂_a f)`.
-/

variable {d : ℕ}

/-- `l` is a classical solution of the Neumann problem (3.8) on `ℝ²₊ ∋ (r, z)`:
`(α²/2)l_rr + (α²/2 − ρ)l_r + ½σ_Z²z²l_zz + µ_Z z l_z + κ₂ z l_rz + (κ₂ − µ_Z)βze^{−r}
 + ((1−p)/p)β^{−p/(1−p)}e^{(p/(1−p))r} = ρl` on `(0, ∞)²`, and `l_r(0, z) = 0` for `z ≥ 0`. -/
def IsClassicalSol38 (M : Params d) (ρ : ℝ) (l : ℝ → ℝ → ℝ) : Prop :=
  let S : Set ℝ := Ici 0
  ContDiffOn ℝ 2 (fun q : ℝ × ℝ => l q.1 q.2) (S ×ˢ S) ∧
  (∀ r z : ℝ, 0 < r → 0 < z →
    M.alpha ^ 2 / 2 * pd2₁ (pd2₁ l S) S r z + (M.alpha ^ 2 / 2 - ρ) * pd2₁ l S r z +
      1 / 2 * M.sigmaZ ^ 2 * z ^ 2 * pd2₂ (pd2₂ l S) S r z + M.muZ * z * pd2₂ l S r z +
      M.kappa2 * z * pd2₂ (pd2₁ l S) S r z +
      (M.kappa2 - M.muZ) * M.beta * z * Real.exp (-r) +
      (1 - M.p) / M.p * M.beta ^ (-M.p / (1 - M.p)) * Real.exp (M.p / (1 - M.p) * r) =
      ρ * l r z) ∧
  ∀ z : ℝ, 0 ≤ z → pd2₁ l S 0 z = 0

/-- `φ` is a classical solution of the Neumann problem (3.15) on `ℝ²₊ ∋ (r, h)`:
`(α²/2)φ_rr + (α²/2 − ρ)φ_r + (σ_B²/2)φ_hh − µ_Bφ_h = ρφ` on `(0, ∞)²`, `φ_r(0, h) = 0` for
`h ≥ 0`, `φ_h(r, 0) = βe^{−r}` for `r ≥ 0`. -/
def IsClassicalSol315 (M : Params d) (ρ : ℝ) (φ : ℝ → ℝ → ℝ) : Prop :=
  let S : Set ℝ := Ici 0
  ContDiffOn ℝ 2 (fun q : ℝ × ℝ => φ q.1 q.2) (S ×ˢ S) ∧
  (∀ r h : ℝ, 0 < r → 0 < h →
    M.alpha ^ 2 / 2 * pd2₁ (pd2₁ φ S) S r h + (M.alpha ^ 2 / 2 - ρ) * pd2₁ φ S r h +
      M.sigmaB ^ 2 / 2 * pd2₂ (pd2₂ φ S) S r h - M.muB * pd2₂ φ S r h = ρ * φ r h) ∧
  (∀ h : ℝ, 0 ≤ h → pd2₁ φ S 0 h = 0) ∧
  ∀ r : ℝ, 0 ≤ r → pd2₂ φ S r 0 = M.beta * Real.exp (-r)

/-- `ψ` is a classical solution of the Neumann problem (3.38) on `ℝ²₊ ∋ (r, h)`:
`(α²/2)ψ_rr + (α²/2 − ρ)ψ_r + (σ_B²/2)ψ_hh − µ_Bψ_h − κ₁ψ_rh = ρψ` on `(0, ∞)²`,
`ψ_r(0, h) = 0` for `h ≥ 0`, `ψ_h(r, 0) = βe^{−r}` for `r ≥ 0`. -/
def IsClassicalSol338 (M : Params d) (ρ : ℝ) (ψ : ℝ → ℝ → ℝ) : Prop :=
  let S : Set ℝ := Ici 0
  ContDiffOn ℝ 2 (fun q : ℝ × ℝ => ψ q.1 q.2) (S ×ˢ S) ∧
  (∀ r h : ℝ, 0 < r → 0 < h →
    M.alpha ^ 2 / 2 * pd2₁ (pd2₁ ψ S) S r h + (M.alpha ^ 2 / 2 - ρ) * pd2₁ ψ S r h +
      M.sigmaB ^ 2 / 2 * pd2₂ (pd2₂ ψ S) S r h - M.muB * pd2₂ ψ S r h -
      M.kappa1 * pd2₂ (pd2₁ ψ S) S r h = ρ * ψ r h) ∧
  (∀ h : ℝ, 0 ≤ h → pd2₁ ψ S 0 h = 0) ∧
  ∀ r : ℝ, 0 ≤ r → pd2₂ ψ S r 0 = M.beta * Real.exp (-r)

/-- `û` is a classical solution of the dual PDE (2.8) on `(0, β] × ℝ²₊ ∋ (y, h, z)` with the
Neumann conditions (2.10) and (2.11):
`(α²/2)y²û_yy + ρyû_y + (σ_B²/2)û_hh − µ_Bû_h + ½σ_Z²z²û_zz + µ_Z zû_z + κ₁yû_yh − κ₂zyû_yz
 + σ_Zσ_Bγᵀη zû_zh + (κ₂ − µ_Z)zy + ((1−p)/p)y^{−p/(1−p)} = ρû` on `(0, β] × (0, ∞)²`;
`û_y(β, h, z) = 0` for `(h, z) ∈ ℝ²₊`; `û_h(y, 0, z) = y` for `(y, z) ∈ (0, β] × ℝ₊` (the paper
prints `û_z` in (2.11); the condition is the transform of `u_h = u_x` at `h = 0`). -/
def IsClassicalSolDual (M : Params d) (ρ : ℝ) (û : ℝ → ℝ → ℝ → ℝ) : Prop :=
  let Y : Set ℝ := Ioc 0 M.beta
  let S : Set ℝ := Ici 0
  ContDiffOn ℝ 2 (fun q : ℝ × ℝ × ℝ => û q.1 q.2.1 q.2.2) (Y ×ˢ S ×ˢ S) ∧
  (∀ y h z : ℝ, y ∈ Y → 0 < h → 0 < z →
    M.alpha ^ 2 / 2 * y ^ 2 * pd3₁ (pd3₁ û Y) Y y h z + ρ * y * pd3₁ û Y y h z +
      M.sigmaB ^ 2 / 2 * pd3₂ (pd3₂ û S) S y h z - M.muB * pd3₂ û S y h z +
      1 / 2 * M.sigmaZ ^ 2 * z ^ 2 * pd3₃ (pd3₃ û S) S y h z + M.muZ * z * pd3₃ û S y h z +
      M.kappa1 * y * pd3₂ (pd3₁ û Y) S y h z - M.kappa2 * z * y * pd3₃ (pd3₁ û Y) S y h z +
      M.sigmaZ * M.sigmaB * (M.gamma ⬝ᵥ M.eta) * z * pd3₂ (pd3₃ û S) S y h z +
      (M.kappa2 - M.muZ) * z * y + (1 - M.p) / M.p * y ^ (-M.p / (1 - M.p)) =
      ρ * û y h z) ∧
  (∀ h z : ℝ, 0 ≤ h → 0 ≤ z → pd3₁ û Y M.beta h z = 0) ∧
  ∀ y z : ℝ, y ∈ Y → 0 ≤ z → pd3₂ û S y 0 z = y

/-- `u` is a classical solution of the HJB equation (4.2) on `ℝ³₊ ∋ (x, h, z)` with its two
Neumann conditions: on `(0, ∞)³`,
`sup_{θ∈ℝ^d}[θᵀµu_x + ½θᵀσσᵀθu_xx + σ_Zθᵀσηz(u_xx − u_xz) − σ_Bθᵀσγu_xh] + sup_{c>0}(c^p/p − cu_x)
 + ½σ_B²u_hh − µ_Bu_h + ½σ_Z²z²(u_zz + u_xx − 2u_xz) + µ_Z z(u_z − u_x) + σ_Zσ_Bzηᵀγ(u_xh − u_hz) = ρu`,
where each supremum is a least upper bound in `ℝ` (so it exists and is finite);
`u_x(0, h, z) = β` for `(h, z) ∈ ℝ²₊`; `u_h(x, 0, z) = u_x(x, 0, z)` for `(x, z) ∈ ℝ²₊`.
The consumption supremum is over `c > 0`: the paper's `c ≥ 0` gives the same value, since at
`c = 0` the paper's `c^p/p` is `0` (`p > 0`) or `−∞` (`p < 0`), while Lean's `0 ^ p = 0`. -/
def IsClassicalSolHJB (M : Params d) (ρ : ℝ) (u : ℝ → ℝ → ℝ → ℝ) : Prop :=
  let S : Set ℝ := Ici 0
  ContDiffOn ℝ 2 (fun q : ℝ × ℝ × ℝ => u q.1 q.2.1 q.2.2) (S ×ˢ S ×ˢ S) ∧
  (∀ x h z : ℝ, 0 < x → 0 < h → 0 < z →
    let ux := pd3₁ u S x h z
    let uxx := pd3₁ (pd3₁ u S) S x h z
    let uxz := pd3₃ (pd3₁ u S) S x h z
    let uxh := pd3₂ (pd3₁ u S) S x h z
    let uh := pd3₂ u S x h z
    let uhh := pd3₂ (pd3₂ u S) S x h z
    let uhz := pd3₃ (pd3₂ u S) S x h z
    let uz := pd3₃ u S x h z
    let uzz := pd3₃ (pd3₃ u S) S x h z
    ∃ S₁ S₂ : ℝ,
      IsLUB (Set.range fun θ : Fin d → ℝ =>
        θ ⬝ᵥ M.mu * ux + 1 / 2 * (θ ⬝ᵥ ((M.sigma * M.sigmaᵀ) *ᵥ θ)) * uxx +
          M.sigmaZ * (θ ⬝ᵥ (M.sigma *ᵥ M.eta)) * z * (uxx - uxz) -
          M.sigmaB * (θ ⬝ᵥ (M.sigma *ᵥ M.gamma)) * uxh) S₁ ∧
      IsLUB ((fun c : ℝ => c ^ M.p / M.p - c * ux) '' Ioi 0) S₂ ∧
      S₁ + S₂ + 1 / 2 * M.sigmaB ^ 2 * uhh - M.muB * uh +
        1 / 2 * M.sigmaZ ^ 2 * z ^ 2 * (uzz + uxx - 2 * uxz) + M.muZ * z * (uz - ux) +
        M.sigmaZ * M.sigmaB * z * (M.eta ⬝ᵥ M.gamma) * (uxh - uhz) = ρ * u x h z) ∧
  (∀ h z : ℝ, 0 ≤ h → 0 ≤ z → pd3₁ u S 0 h z = M.beta) ∧
  ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → pd3₂ u S x 0 z = pd3₁ u S x 0 z

end BenchmarkTracking.Verification


