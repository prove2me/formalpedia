-- Prove2me | Definitions.Def_SepQPTardos_Main_Problem
-- name    : SepQPTardos_Main_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:26.09946+00:00
-- url     : https://prove2.me/theorems/6c770894-ff5f-48bf-9c3a-f8583315e349
-- title:
--   Problem (1): separable convex quadratic objective, feasibility, optimality and the three certificates
-- statement:
--   Let $A\in\mathbb R^{r\times m}$, $b\in\mathbb R^r$ and $q,c\in\mathbb R^m$ (the paper's instances have $A$ integer and $b,c,q$ rational, with $q\ge 0$; they are cast to reals). The objective of problem (1) is
--
--   $$\Phi(x)=\tfrac12\sum_{e=1}^m q_e x_e^2+\sum_{e=1}^m c_e x_e ,\qquad x\in\mathbb R^m .$$
--
--   1. A point $x\in\mathbb R^m$ is **feasible** if $Ax=b$ and $x\ge 0$; it is **optimal** if it is feasible and $\Phi(x)\le\Phi(y)$ for every feasible $y\in\mathbb R^m$. Optimality is defined by minimisation.
--   2. With $Q=\operatorname{diag}(q)$, the **dual slack** of $(x,\pi)$, $\pi\in\mathbb R^r$, is $\sigma=Qx+c-A^\top\pi$. The pair satisfies the **KKT system (8)** if $Ax=b$, $x\ge0$, $\sigma\ge0$ and $x^\top\sigma=0$; such a pair is an *optimal primal–dual pair*.
--   3. A **Farkas certificate of infeasibility** is $y\in\mathbb R^r$ with $A^\top y\ge0$ and $b^\top y<0$.
--   4. An **unboundedness certificate** is a feasible $x$ together with $d\in\mathbb R^m$ such that $Ad=0$, $d\ge0$, $d_e=0$ whenever $q_e>0$, and $c^\top d<0$. Along $x+\lambda d$, $\lambda\ge0$, the objective equals $\Phi(x)+\lambda c^\top d$ and tends to $-\infty$.
--   5. **System (5)** in the free variable $\pi_0\in\mathbb R^r$ is $A_Z^\top\pi_0\le c_Z$, i.e. $(A^\top\pi_0)_e\le c_e$ for every $e$ with $q_e=0$.
--
--   These are the objects in terms of which Theorem 1.1 and the structural lemmas of §2.2 are stated.
--
--   **Formalization Note.** Casts of integer matrices and rational vectors to real ones are provided as `castMat`, `castVec`, `castQMat`.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §1, eq. (1), p. 2; §2.2, systems (5) and (8) and the certificates, p. 5

import Mathlib

open Matrix

noncomputable section

namespace SepQPTardos.Main

/-!
# Problem (1): separable convex quadratic programming over `Ax = b, x ≥ 0`

Cui–Li–Miao, *Extending Tardos's Theorem to Separable Convex Quadratic Programming*,
STOC 2027 submission #829 (October 2026), §1, eq. (1), p. 2, and §2.2, pp. 5.

The data are real here (the paper's instances are `A ∈ ℤ^{r×m}`, `b ∈ ℚ^r`, `c ∈ ℚ^m`,
`q ∈ ℚ^m_{≥0}`, which are cast into these real objects). Feasible points, optimality and the
three certificates are defined on `ℝ^m`.
-/

variable {r m : ℕ}

/-- The objective `Φ(x) = ½ ∑ₑ qₑ xₑ² + ∑ₑ cₑ xₑ` of (1). -/
def Phi (q c : Fin m → ℝ) (x : Fin m → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ e, q e * x e ^ 2 + ∑ e, c e * x e

/-- `x` is feasible for (1): `Ax = b` and `x ≥ 0`. -/
def Feasible (A : Matrix (Fin r) (Fin m) ℝ) (b : Fin r → ℝ) (x : Fin m → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ e, 0 ≤ x e

/-- `x` is optimal for (1): feasible, and `Φ(x) ≤ Φ(y)` for every feasible `y ∈ ℝ^m`.
Optimality is defined by minimisation, not by the KKT system (8). -/
def IsOptimal (A : Matrix (Fin r) (Fin m) ℝ) (b : Fin r → ℝ) (q c : Fin m → ℝ)
    (x : Fin m → ℝ) : Prop :=
  Feasible A b x ∧ ∀ y, Feasible A b y → Phi q c x ≤ Phi q c y

/-- The dual slack `σ = Qx + c − Aᵀπ` with `Q = diag(q)`. -/
def slack (A : Matrix (Fin r) (Fin m) ℝ) (q c : Fin m → ℝ) (x : Fin m → ℝ)
    (π : Fin r → ℝ) : Fin m → ℝ :=
  fun e => q e * x e + c e - (Aᵀ *ᵥ π) e

/-- The KKT system (8): `Ax = b`, `x ≥ 0`, `σ = Qx + c − Aᵀπ ≥ 0`, `xᵀσ = 0`.
A pair `(x, π)` satisfying it is an *optimal primal–dual pair*. -/
def KKT (A : Matrix (Fin r) (Fin m) ℝ) (b : Fin r → ℝ) (q c : Fin m → ℝ) (x : Fin m → ℝ)
    (π : Fin r → ℝ) : Prop :=
  Feasible A b x ∧ (∀ e, 0 ≤ slack A q c x π e) ∧ x ⬝ᵥ slack A q c x π = 0

/-- Farkas certificate of infeasibility of `Ax = b, x ≥ 0` (§2.2, p. 5):
`Aᵀy ≥ 0` and `bᵀy < 0`. -/
def InfeasCert (A : Matrix (Fin r) (Fin m) ℝ) (b : Fin r → ℝ) (y : Fin r → ℝ) : Prop :=
  (∀ e, 0 ≤ (Aᵀ *ᵥ y) e) ∧ b ⬝ᵥ y < 0

/-- Certificate of unboundedness (§2.2, p. 5): a feasible point `x` and a direction `d` with
`Ad = 0`, `d ≥ 0`, `dₑ = 0` whenever `qₑ > 0`, and `cᵀd < 0`. Along `x + λd` the objective is
`Φ(x) + λ cᵀd`, so it tends to `−∞`. -/
def UnbddCert (A : Matrix (Fin r) (Fin m) ℝ) (b : Fin r → ℝ) (q c : Fin m → ℝ)
    (x d : Fin m → ℝ) : Prop :=
  Feasible A b x ∧ A *ᵥ d = 0 ∧ (∀ e, 0 ≤ d e) ∧ (∀ e, 0 < q e → d e = 0) ∧ c ⬝ᵥ d < 0

/-- System (5) of §2.2 (p. 5) in the free variable `π₀`: `A_Zᵀ π₀ ≤ c_Z`, i.e.
`(Aᵀπ₀)ₑ ≤ cₑ` for every `e` with `qₑ = 0`. -/
def Sys5 (A : Matrix (Fin r) (Fin m) ℝ) (q c : Fin m → ℝ) (π₀ : Fin r → ℝ) : Prop :=
  ∀ e, q e = 0 → (Aᵀ *ᵥ π₀) e ≤ c e

/-- An integer matrix viewed as a real matrix. -/
def castMat {p n : ℕ} (A : Matrix (Fin p) (Fin n) ℤ) : Matrix (Fin p) (Fin n) ℝ :=
  A.map (fun z : ℤ => (z : ℝ))

/-- A rational vector viewed as a real vector. -/
def castVec {n : ℕ} (v : Fin n → ℚ) : Fin n → ℝ := fun i => (v i : ℝ)

/-- A rational matrix viewed as a real matrix. -/
def castQMat {p n : ℕ} (M : Matrix (Fin p) (Fin n) ℚ) : Matrix (Fin p) (Fin n) ℝ :=
  M.map (fun z : ℚ => (z : ℝ))

end SepQPTardos.Main


