-- Prove2me | Definitions.Def_RobustPower_Hypercube_RhsProblems
-- name    : RobustPower_Hypercube_RhsProblems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:48:54.76366+00:00
-- url     : https://prove2.me/theorems/4a5b788d-234a-4d73-b496-8d1b7ec31349
-- title:
--   $\Pi_{\mathrm{Rob}}(b)$ (1.2) and the deterministic problem $\Pi$ of Theorem 2.4
-- statement:
--   Fix $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, costs $c\in\mathbb R^{n_1}$, $d\in\mathbb R^{n_2}$, integer-coordinate sets $I_1,I_2$, and an uncertain right-hand side $\omega\mapsto b(\omega)\in\mathbb R^m$ over a scenario set $\Omega$.
--
--   1. The **two-stage robust problem** $\Pi_{\mathrm{Rob}}(b)$ of (1.2) chooses one pair $(x,y)$ with $x\in D_{I_1}$, $y\in D_{I_2}$ and $Ax+By\ge b(\omega)$ for every $\omega\in\Omega$. Its value is
--   $$z_{\mathrm{Rob}}(b)=\inf\{c^Tx+d^Ty : (x,y)\ \text{feasible}\}.$$
--   2. The **coordinatewise worst right-hand side** is $b^h_j=\sup_{\omega\in\Omega}b_j(\omega)$, $j=1,\dots,m$.
--   3. For a vector $b^h$, the **deterministic problem** $\Pi$ chooses $(x,y)$ with $x\in D_{I_1}$, $y\in D_{I_2}$ and $Ax+By\ge b^h$; its value is
--   $$z(\Pi)=\inf\{c^Tx+d^Ty : (x,y)\ \text{feasible}\}.$$
--
--   These are the two problems compared in Theorem 2.4.
--
--   **Formalization Note** Both values are infima in the extended reals, equal to $+\infty$ when the problem is infeasible; no optimal solution is assumed to exist. Because $d$ does not depend on $\omega$, the worst-case cost $c^Tx+\max_\omega d^Ty$ of (1.2) is written $c^Tx+d^Ty$. The supremum defining $b^h$ is a real supremum; it is meaningful when the right-hand sides are bounded above (Theorem 2.4 assumes this), where it equals the paper's maximum whenever that maximum exists.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 4, (1.2); p. 17, Theorem 2.4

import Definitions.Def_RobustPower_StochGap_Problems

open Matrix

namespace RobustPower.Hypercube

/-- Feasibility in the two-stage robust problem `Π_Rob(b)` (1.2): one pair `(x, y)`
with `x ∈ ℝ₊^{n₁-p₁} × ℤ₊^{p₁}`, `y ∈ ℝ₊^{n₂-p₂} × ℤ₊^{p₂}` (integer coordinates
`I₁`, `I₂`) and `A x + B y ≥ b(ω)` for every scenario `ω`. -/
def robFeasibleRhs {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) : Prop :=
  x ∈ RobustPower.StochGap.mixedIntDomain I₁ ∧ y ∈ RobustPower.StochGap.mixedIntDomain I₂ ∧ ∀ ω, b ω ≤ A *ᵥ x + B *ᵥ y

/-- The optimal value `z_Rob(b)` of (1.2), an extended-real infimum (`⊤` when
infeasible). Since `d` does not depend on `ω`, the worst-case cost
`cᵀx + max_ω dᵀy` is `cᵀx + dᵀy`. -/
noncomputable def zRobRhs {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) : EReal :=
  ⨅ (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) (_ : robFeasibleRhs A B b I₁ I₂ x y),
    ((c ⬝ᵥ x + d ⬝ᵥ y : ℝ) : EReal)

/-- The coordinatewise worst right-hand side of Theorem 2.4:
`bʰⱼ = sup_{ω ∈ Ω} bⱼ(ω)` (the paper's `max`). -/
noncomputable def worstRhs {m : ℕ} {Ω : Type*} (b : Ω → Fin m → ℝ) : Fin m → ℝ :=
  fun j => ⨆ ω, b ω j

/-- Feasibility in the deterministic mixed integer problem `Π` of Theorem 2.4:
`A x + B y ≥ bʰ`, `x ∈ ℝ₊^{n₁-p₁} × ℤ₊^{p₁}`, `y ∈ ℝ₊^{n₂-p₂} × ℤ₊^{p₂}`. -/
def detFeasible {m n₁ n₂ : ℕ}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (bh : Fin m → ℝ) (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) : Prop :=
  x ∈ RobustPower.StochGap.mixedIntDomain I₁ ∧ y ∈ RobustPower.StochGap.mixedIntDomain I₂ ∧ bh ≤ A *ᵥ x + B *ᵥ y

/-- The optimal value `z(Π) = min cᵀx + dᵀy` of the deterministic problem, an
extended-real infimum (`⊤` when infeasible). -/
noncomputable def zDet {m n₁ n₂ : ℕ}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (bh : Fin m → ℝ) (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) : EReal :=
  ⨅ (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) (_ : detFeasible A B bh I₁ I₂ x y),
    ((c ⬝ᵥ x + d ⬝ᵥ y : ℝ) : EReal)

end RobustPower.Hypercube


