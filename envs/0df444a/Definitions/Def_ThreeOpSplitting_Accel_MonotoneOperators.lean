-- Prove2me | Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
-- name    : ThreeOpSplitting_Accel_MonotoneOperators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:57:14.181541+00:00
-- url     : https://prove2.me/theorems/a9a1ddc9-0977-4af0-90cf-10ed733e0c34
-- title:
--   Monotone, strongly monotone, cocoercive and Lipschitz operators, zeros and resolvents on a real Hilbert space
-- statement:
--   Let $H$ be a real inner product space. A **set-valued operator** is a map $A : H \to 2^H$; a single-valued operator is a map $C : H \to H$. This file fixes the vocabulary of problem (1.1) of Davis and Yin and of its accelerated variant in §3.3.
--
--   1. $A$ is **monotone** if $\langle x - y, u - v\rangle \ge 0$ whenever $u \in Ax$, $v \in Ay$; it is **maximal monotone** if moreover every monotone $A'$ with $Ax \subseteq A'x$ for all $x$ equals $A$.
--   2. $B$ is **$\mu$-strongly monotone** if $\langle x - y, u - v\rangle \ge \mu\|x - y\|^2$ whenever $u \in Bx$, $v \in By$.
--   3. A single-valued $C$ is **monotone** if $\langle x - y, Cx - Cy\rangle \ge 0$, and **$\mu$-strongly monotone** if $\langle x - y, Cx - Cy\rangle \ge \mu\|x-y\|^2$, for all $x, y$.
--   4. $C$ is **$\beta$-cocoercive** if $\beta\|Cx - Cy\|^2 \le \langle Cx - Cy, x - y\rangle$ for all $x, y$ (footnote 1, p. 830).
--   5. $C$ is **$L$-Lipschitz** if $\|Cx - Cy\| \le L\|x - y\|$ for all $x, y$.
--   6. $\operatorname{zer}(M) = \{x : 0 \in Mx\}$, and for set-valued $A, B$ and single-valued $C$
--   $$(A + B + C)x = \{a + b + Cx : a \in Ax,\ b \in Bx\}.$$
--   7. $J : H \to H$ is **the resolvent** $J_{\gamma A} = (I + \gamma A)^{-1}$ if $\gamma^{-1}(x - Jx) \in A(Jx)$ for every $x$; a map $J : \mathbb{R} \to (H \to H)$ is a **resolvent family** of $A$ if $J(\gamma)$ is the resolvent $J_{\gamma A}$ for every $\gamma > 0$.
--
--   These notions are shared by every statement of the mission: the accelerated scheme evaluates $J_{\gamma A}$ and $J_{\gamma B}$ at a different stepsize $\gamma$ in every iteration, which is why resolvents come as families indexed by $\gamma$.
--
--   **Formalization Note** The sign conditions ($\beta > 0$, $\mu_C > 0$, $\mu_B \ge 0$, $L_C > 0$) are not built into the predicates; they are hypotheses of each theorem that uses them. The resolvent is not constructed: a map is required to satisfy the resolvent inclusion. For $A$ maximal monotone and $\gamma > 0$ such a map exists (Minty's theorem) and is unique (by monotonicity), so nothing is lost. Values of a resolvent family at $\gamma \le 0$ are unconstrained and never used.
-- source:
--   Davis and Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017), https://doi.org/10.1007/s11228-017-0421-z, pp. 829-830 (Section 1, problem (1.1), footnote 1) and pp. 841-842 (Section 3.3, Theorem 3.3)

import Mathlib

open InnerProductSpace

namespace ThreeOpSplitting.Accel

/-- A set-valued operator `A : H → 2^H` is monotone if `⟪x - y, u - v⟫ ≥ 0`
whenever `u ∈ A x` and `v ∈ A y`. -/
def IsMonotoneOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) : Prop :=
  ∀ x y u v : H, u ∈ A x → v ∈ A y → 0 ≤ ⟪x - y, u - v⟫_ℝ

/-- A monotone operator is maximal monotone if its graph is not properly contained in the
graph of another monotone operator. -/
def IsMaximalMonotone {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) : Prop :=
  IsMonotoneOp A ∧ ∀ A' : H → Set H, IsMonotoneOp A' → (∀ x, A x ⊆ A' x) → A' = A

/-- A set-valued operator `B` is `μ`-strongly monotone if
`⟪x - y, u - v⟫ ≥ μ ‖x - y‖²` whenever `u ∈ B x` and `v ∈ B y`. The sign of `μ` is imposed
separately wherever it is used (the paper allows `μ = 0` for `B`). -/
def IsStronglyMonotoneOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : ℝ) (B : H → Set H) : Prop :=
  ∀ x y u v : H, u ∈ B x → v ∈ B y → μ * ‖x - y‖ ^ 2 ≤ ⟪x - y, u - v⟫_ℝ

/-- A single-valued operator `C : H → H` is monotone if `⟪x - y, C x - C y⟫ ≥ 0` for all
`x, y`. -/
def IsMonotoneFun {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : H → H) : Prop :=
  ∀ x y : H, 0 ≤ ⟪x - y, C x - C y⟫_ℝ

/-- A single-valued operator `C : H → H` is `μ`-strongly monotone if
`⟪x - y, C x - C y⟫ ≥ μ ‖x - y‖²` for all `x, y`. -/
def IsStronglyMonotoneFun {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : ℝ) (C : H → H) : Prop :=
  ∀ x y : H, μ * ‖x - y‖ ^ 2 ≤ ⟪x - y, C x - C y⟫_ℝ

/-- A single-valued operator `C` is `β`-cocoercive if
`β ‖C x - C y‖² ≤ ⟪C x - C y, x - y⟫` for all `x, y` (the positivity `β > 0` is a separate
hypothesis wherever it is needed). -/
def IsCocoercive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (β : ℝ) (C : H → H) : Prop :=
  ∀ x y : H, β * ‖C x - C y‖ ^ 2 ≤ ⟪C x - C y, x - y⟫_ℝ

/-- A single-valued operator `C` is `L`-Lipschitz if `‖C x - C y‖ ≤ L ‖x - y‖` for all
`x, y`. -/
def IsLipschitzOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (L : ℝ) (C : H → H) : Prop :=
  ∀ x y : H, ‖C x - C y‖ ≤ L * ‖x - y‖

/-- The set of zeros `zer(M) = {x | 0 ∈ M x}` of a set-valued operator. -/
def zer {H : Type*} [Zero H] (M : H → Set H) : Set H := {x | (0 : H) ∈ M x}

/-- The sum `A + B + C` of two set-valued operators and a single-valued operator:
`(A + B + C) x = {a + b + C x | a ∈ A x, b ∈ B x}`. -/
def opSum {H : Type*} [Add H] (A B : H → Set H) (C : H → H) : H → Set H :=
  fun x => {w | ∃ a ∈ A x, ∃ b ∈ B x, w = a + b + C x}

/-- `J` is (a choice of) the resolvent `J_{γA} = (I + γA)⁻¹`: for every `x`,
`γ⁻¹ (x - J x) ∈ A (J x)`, i.e. `x ∈ J x + γ A (J x)`. For maximal monotone `A` and `γ > 0`
such a map exists (Minty) and is unique. -/
def IsResolvent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (A : H → Set H) (J : H → H) : Prop :=
  ∀ x : H, γ⁻¹ • (x - J x) ∈ A (J x)

/-- `J : ℝ → H → H` is a family of resolvents of `A`: for every stepsize `γ > 0`, `J γ` is the
resolvent `J_{γA}`. Values of `J γ` for `γ ≤ 0` are unconstrained and never used. -/
def IsResolventFamily {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (J : ℝ → H → H) : Prop :=
  ∀ γ : ℝ, 0 < γ → IsResolvent γ A (J γ)

end ThreeOpSplitting.Accel


