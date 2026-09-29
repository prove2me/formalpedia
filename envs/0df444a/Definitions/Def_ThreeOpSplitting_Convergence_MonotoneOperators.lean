-- Prove2me | Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
-- name    : ThreeOpSplitting_Convergence_MonotoneOperators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:45:58.566844+00:00
-- url     : https://prove2.me/theorems/2b9a6b29-6c16-45b7-8af8-74e4ea0e865f
-- title:
--   Monotone and maximal monotone operators, zeros, cocoercivity and resolvents on a real Hilbert space
-- statement:
--   Let $H$ be a real inner product space. A **set-valued operator** is a map $A : H \to 2^H$. This file fixes the vocabulary of problem (1.1) of Davis and Yin.
--
--   1. $A$ is **monotone** if $\langle x - y, u - v\rangle \ge 0$ whenever $u \in Ax$ and $v \in Ay$.
--   2. $A$ is **maximal monotone** if it is monotone and every monotone operator $A'$ with $Ax \subseteq A'x$ for all $x$ equals $A$ (the graph of $A$ is not properly contained in the graph of a monotone operator).
--   3. The **domain** of $A$ is $\operatorname{dom}(A) = \{x \in H : Ax \neq \emptyset\}$ and the **zero set** of an operator $M$ is $\operatorname{zer}(M) = \{x : 0 \in Mx\}$.
--   4. For set-valued $A, B$ and single-valued $C : H \to H$, the sum is
--   $$(A + B + C)x = \{a + b + Cx : a \in Ax,\ b \in Bx\}.$$
--   5. $C : H \to H$ is **$\beta$-cocoercive** if $\beta\|Cx - Cy\|^2 \le \langle Cx - Cy, x - y\rangle$ for all $x, y \in H$ (footnote 1, p. 830; the requirement $\beta > 0$ is imposed separately wherever it is used).
--   6. $J : H \to H$ is **the resolvent** $J_{\gamma A} = (I + \gamma A)^{-1}$ if $\gamma^{-1}(x - Jx) \in A(Jx)$ for every $x \in H$, i.e. $x \in Jx + \gamma A(Jx)$.
--
--   These notions are shared by every statement of the mission: problem (1.1) asks for a point of $\operatorname{zer}(A + B + C)$, and the three-operator map is built from the resolvents of $A$ and $B$ and the forward step of $C$.
--
--   **Formalization Note** The paper uses $J_{\gamma A}$ without defining it. The resolvent is not constructed here; a map $J$ is instead required to satisfy the resolvent inclusion. For $A$ maximal monotone and $\gamma > 0$ such a map exists (Minty's theorem) and is unique (by monotonicity), so nothing is lost. The operator $C$ is single-valued and everywhere defined, as in the paper.
-- source:
--   Davis and Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017), https://doi.org/10.1007/s11228-017-0421-z, pp. 829-830, Section 1, problem (1.1) and footnote 1

import Mathlib

open InnerProductSpace

namespace ThreeOpSplitting.Convergence

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

/-- The domain `dom(A) = {x | A x ≠ ∅}` of a set-valued operator. -/
def dom {H : Type*} (A : H → Set H) : Set H := {x | (A x).Nonempty}

/-- The set of zeros `zer(M) = {x | 0 ∈ M x}` of a set-valued operator. -/
def zer {H : Type*} [Zero H] (M : H → Set H) : Set H := {x | (0 : H) ∈ M x}

/-- The sum `A + B + C` of two set-valued operators and a single-valued operator:
`(A + B + C) x = {a + b + C x | a ∈ A x, b ∈ B x}`. -/
def opSum {H : Type*} [Add H] (A B : H → Set H) (C : H → H) : H → Set H :=
  fun x => {w | ∃ a ∈ A x, ∃ b ∈ B x, w = a + b + C x}

/-- A single-valued operator `C` is `β`-cocoercive if
`β ‖C x - C y‖² ≤ ⟪C x - C y, x - y⟫` for all `x, y` (the positivity `β > 0` is a separate
hypothesis wherever it is needed). -/
def IsCocoercive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (β : ℝ) (C : H → H) : Prop :=
  ∀ x y : H, β * ‖C x - C y‖ ^ 2 ≤ ⟪C x - C y, x - y⟫_ℝ

/-- `J` is (a choice of) the resolvent `J_{γA} = (I + γA)⁻¹`: for every `x`,
`γ⁻¹ (x - J x) ∈ A (J x)`, i.e. `x ∈ J x + γ A (J x)`. For maximal monotone `A` and `γ > 0`
such a map exists (Minty) and is unique. -/
def IsResolvent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (A : H → Set H) (J : H → H) : Prop :=
  ∀ x : H, γ⁻¹ • (x - J x) ∈ A (J x)

end ThreeOpSplitting.Convergence


