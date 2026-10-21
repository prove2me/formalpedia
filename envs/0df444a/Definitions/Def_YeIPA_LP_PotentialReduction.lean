-- Prove2me | Definitions.Def_YeIPA_LP_PotentialReduction
-- name    : YeIPA_LP_PotentialReduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:45.771835+00:00
-- url     : https://prove2.me/theorems/3680bc4a-1316-4d88-8053-528f9da1e661
-- title:
--   Standard-form LP, $\mathring{\mathcal F}$, the potentials $\psi_{n+\rho}$ and $\mathcal P_{n+\rho}$, the potential-reduction step (4.10)–(4.13), the direction (4.17) and the step size (4.18)
-- statement:
--   Fix a real $m\times n$ matrix $A$, $b\in\mathbb R^m$ and $c\in\mathbb R^n$, and consider the standard-form pair
--   $$(\mathrm{LP})\ \min\{c^Tx: Ax=b,\ x\ge0\},\qquad (\mathrm{LD})\ \max\{b^Ty: A^Ty+s=c,\ s\ge0\}.$$
--   Vector inequalities are componentwise, $e$ is the all-ones vector, $X=\operatorname{diag}(x)$, $S=\operatorname{diag}(s)$, $\|\cdot\|$ is the Euclidean norm, $\|v\|_\infty=\max_j|v_j|$ and $\min(v)=\min_jv_j$. This module defines the objects of Chapter 4 of Ye's *Interior Point Algorithms*:
--
--   1. The **interior** $\mathring{\mathcal F}$: triples $(x,y,s)$ with $Ax=b$, $x>0$, $A^Ty+s=c$, $s>0$. The **standing assumptions**: $A$ has rank $m$, (LP) and (LD) both have interior feasible points, and $b\ne0$ (Chapter 4 preamble, p. 109).
--   2. For $\rho\ge0$, the **primal-dual potential** and the **primal potential**
--   $$\psi_{n+\rho}(x,s)=(n+\rho)\log(x^Ts)-\sum_{j=1}^n\log(x_js_j),\qquad \mathcal P_{n+\rho}(x,z)=(n+\rho)\log(c^Tx-z)-\sum_{j=1}^n\log x_j,$$
--   and the gradient $\nabla\mathcal P_{n+\rho}(x,z)=\frac{n+\rho}{c^Tx-z}\,c-X^{-1}e$.
--   3. The **potential-reduction step** at $x$ and a lower bound $z$:
--   $$p(z)=(I-XA^T(AX^2A^T)^{-1}AX)\,X\nabla\mathcal P_{n+\rho}(x,z),\qquad x^+=x-\alpha\frac{Xp(z)}{\|p(z)\|}\quad(4.10),$$
--   and the dual update $y(z)=y_2-\frac{c^Tx-z}{n+\rho}\,y_1$, $y_1=(AX^2A^T)^{-1}b$, $y_2=(AX^2A^T)^{-1}AX^2c$ (4.13), $s(z)=c-A^Ty(z)$ (4.12).
--   4. The **primal-dual direction** $(d_x,d_y,d_s)$ at $(x,s)$ with parameter $\gamma$, $\mu=x^Ts/n$:
--   $$Sd_x+Xd_s=\gamma\mu e-Xs,\qquad Ad_x=0,\qquad -A^Td_y-d_s=0\quad(4.17).$$
--   5. The **step size**, for a constant $\alpha$,
--   $$\theta=\frac{\alpha\sqrt{\min(Xs)}}{\|(XS)^{-1/2}(\frac{x^Ts}{n+\rho}e-Xs)\|}\quad(4.18).$$
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, so indices $1,\dots,n$ become $0,\dots,n-1$; matrices are `Matrix (Fin m) (Fin n) ℝ`. The Euclidean norm is written out as `norm2` because Mathlib's norm on `Fin n → ℝ` is the sup norm; $\|\cdot\|_\infty$ is `normInf` and $\min(v)$ is `vmin`. $(XS)^{-1/2}w$ is written componentwise as $w_j/\sqrt{x_js_j}$. Matrix inverses are Mathlib's `⁻¹`, which is $0$ on a singular matrix; under the rank assumption $AX^2A^T$ is positive definite for $x>0$. The vector $p(z)$ is defined by its projection formula (p. 121), not by the equivalent form (4.11), and $x^+$ divides by $\|p(z)\|$ as printed (Lean's value is $x^+=x$ when $p(z)=0$). The standing assumptions are bundled as `StandingAssumptions A b c` and are a hypothesis of every theorem; no definition assumes them.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, pp. 18–19 ((LP), (LD)), p. 21 and p. 48 (rank m), p. 63 (F̊, standing assumption), p. 64 (P_{n+1}), p. 121 (ψ_{n+ρ}, ∇P, p^k), p. 122 ((4.10)–(4.13)), p. 126 ((4.17)), p. 127 ((4.18))

import Mathlib

open Matrix

namespace YeIPA.LP

/-!
# Standard-form LP, the primal-dual potential and the potential-reduction steps of Chapter 4

Ye, *Interior Point Algorithms: Theory and Analysis*, Wiley 1997: the standard-form pair
(LP) `min cᵀx s.t. Ax = b, x ≥ 0` and (LD) `max bᵀy s.t. Aᵀy + s = c, s ≥ 0` pp. 18–19; the
interior `F̊` and the standing assumption that both have interior feasible points p. 63; the
primal potential `P_{n+ρ}(x, z)` p. 64; the primal-dual potential `ψ_{n+ρ}(x, s)`, `ρ ≥ 0`,
p. 121; the gradient `∇P_{n+ρ}(xᵏ, zᵏ)`, the vector `pᵏ = p(zᵏ)` and the step (4.10)
pp. 121–122; `s(zᵏ)`, `y(zᵏ)` (4.12)–(4.13) p. 122; the primal-dual direction (4.17) p. 126;
the step size (4.18) p. 127.

`A : Matrix (Fin m) (Fin n) ℝ`, `b : Fin m → ℝ`, `c : Fin n → ℝ`. The book's indices
`1, …, n` are `0, …, n-1` here. Vector inequalities are componentwise; `e` is the all-ones
vector; `X = diag(x)`, `S = diag(s)`.
-/

variable {m n : ℕ}

/-- The all-ones vector `e ∈ ℝⁿ`. -/
def ones (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- The Euclidean norm `‖v‖ = (∑ⱼ vⱼ²)^{1/2}`. -/
noncomputable def norm2 (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ j, v j ^ 2)

/-- The max-norm `‖v‖_∞ = maxⱼ |vⱼ|` (equal to `0` when `n = 0`). -/
noncomputable def normInf (v : Fin n → ℝ) : ℝ := ⨆ j, |v j|

/-- `min(v) = minⱼ vⱼ` (p. 127; used with `n ≥ 1`). -/
noncomputable def vmin (v : Fin n → ℝ) : ℝ := ⨅ j, v j

/-- `(x, y, s) ∈ F̊` (pp. 18–19, 63): `Ax = b`, `x > 0`, `Aᵀy + s = c`, `s > 0`. -/
def IsInteriorFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ (∀ j, 0 < x j) ∧ Aᵀ *ᵥ y + s = c ∧ ∀ j, 0 < s j

/-- The standing assumptions of the LP chapters: `A ∈ ℝ^{m×n}` has full row rank `m`
(pp. 21, 48; needed for `(A X² Aᵀ)⁻¹` in (4.13)), both (LP) and (LD) have interior feasible
points (p. 63, §2.4; p. 109), and `b ≠ 0` (Chapter 4 preamble, p. 109). -/
def StandingAssumptions (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Prop :=
  A.rank = m ∧ (∃ x y s, IsInteriorFeasible A b c x y s) ∧ b ≠ 0

/-- The primal-dual potential function (p. 121, (2.17)):
`ψ_{n+ρ}(x, s) = (n + ρ) log(xᵀs) − ∑ⱼ log(xⱼ sⱼ)`. -/
noncomputable def pdPotential (ρ : ℝ) (x s : Fin n → ℝ) : ℝ :=
  ((n : ℝ) + ρ) * Real.log (x ⬝ᵥ s) - ∑ j, Real.log (x j * s j)

/-- The primal potential function (p. 64, p. 121):
`P_{n+ρ}(x, z) = (n + ρ) log(cᵀx − z) − ∑ⱼ log xⱼ`. -/
noncomputable def primalPotential (ρ : ℝ) (c : Fin n → ℝ) (x : Fin n → ℝ) (z : ℝ) : ℝ :=
  ((n : ℝ) + ρ) * Real.log (c ⬝ᵥ x - z) - ∑ j, Real.log (x j)

/-- The gradient of the primal potential (p. 121):
`∇P_{n+ρ}(x, z) = ((n + ρ)/(cᵀx − z)) c − X⁻¹e`. -/
noncomputable def gradPrimalPotential (ρ : ℝ) (c : Fin n → ℝ) (x : Fin n → ℝ) (z : ℝ) :
    Fin n → ℝ :=
  fun j => ((n : ℝ) + ρ) / (c ⬝ᵥ x - z) * c j - (x j)⁻¹

/-- `p(z) = (I − XAᵀ(AX²Aᵀ)⁻¹AX) X ∇P_{n+ρ}(x, z)` (p. 121, last display), the vector `pᵏ`
of the potential-reduction step at `x = xᵏ`, `z = zᵏ`. -/
noncomputable def pVec (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (ρ : ℝ)
    (x : Fin n → ℝ) (z : ℝ) : Fin n → ℝ :=
  (1 - diagonal x * Aᵀ * (A * diagonal x * diagonal x * Aᵀ)⁻¹ * A * diagonal x) *ᵥ
    (diagonal x *ᵥ gradPrimalPotential ρ c x z)

/-- The primal update (4.10): `xᵏ⁺¹ = xᵏ − α Xᵏpᵏ / ‖pᵏ‖` with `pᵏ = p(zᵏ)`. -/
noncomputable def primalStep (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (ρ α : ℝ)
    (x : Fin n → ℝ) (z : ℝ) : Fin n → ℝ :=
  fun j => x j - α * (x j * pVec A c ρ x z j) / norm2 (pVec A c ρ x z)

/-- `y₁ = (AX²Aᵀ)⁻¹ b` (4.13). -/
noncomputable def yOne (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    Fin m → ℝ :=
  (A * diagonal x * diagonal x * Aᵀ)⁻¹ *ᵥ b

/-- `y₂ = (AX²Aᵀ)⁻¹ A X² c` (4.13). -/
noncomputable def yTwo (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (x : Fin n → ℝ) :
    Fin m → ℝ :=
  (A * diagonal x * diagonal x * Aᵀ)⁻¹ *ᵥ (A *ᵥ (diagonal x *ᵥ (diagonal x *ᵥ c)))

/-- `y(z) = y₂ − ((cᵀx − z)/(n + ρ)) y₁` (4.13). -/
noncomputable def yOf (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (ρ : ℝ)
    (x : Fin n → ℝ) (z : ℝ) : Fin m → ℝ :=
  yTwo A c x - ((c ⬝ᵥ x - z) / ((n : ℝ) + ρ)) • yOne A b x

/-- `s(z) = c − Aᵀy(z)` (4.12). -/
noncomputable def sOf (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (ρ : ℝ)
    (x : Fin n → ℝ) (z : ℝ) : Fin n → ℝ :=
  c - Aᵀ *ᵥ yOf A b c ρ x z

/-- `(d_x, d_y, d_s)` solves the primal-dual system (4.17) at `(x, s)` with parameter `γ`:
`S d_x + X d_s = γμe − Xs`, `A d_x = 0`, `−Aᵀd_y − d_s = 0`, where `μ = xᵀs/n`. -/
def IsPDDirection (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ) (γ : ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) : Prop :=
  (∀ j, s j * dx j + x j * ds j = γ * ((x ⬝ᵥ s) / n) - x j * s j) ∧
    A *ᵥ dx = 0 ∧ -(Aᵀ *ᵥ dy) - ds = 0

/-- The step size (4.18):
`θ = α √min(Xs) / ‖(XS)^{-1/2}((xᵀs/(n + ρ)) e − Xs)‖`. -/
noncomputable def pdStepSize (ρ α : ℝ) (x s : Fin n → ℝ) : ℝ :=
  α * Real.sqrt (vmin (fun j => x j * s j)) /
    norm2 (fun j => (x ⬝ᵥ s / ((n : ℝ) + ρ) - x j * s j) / Real.sqrt (x j * s j))

end YeIPA.LP


