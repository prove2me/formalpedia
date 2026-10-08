-- Prove2me | Definitions.Def_RobinsonSR_Reduction_Setting
-- name    : RobinsonSR_Reduction_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:59:15.073978+00:00
-- url     : https://prove2.me/theorems/87931bf3-88f9-429f-9106-1109a786a392
-- title:
--   Appendix, pp. 43–60 — normal cone ∂ψ_C, polyhedral sets, the face ∂ψ*_C(−y₀), tangent cone, parallel subspace, lineality space, strong regularity of 0 ∈ Ax + a + ∂ψ_C(x)
-- statement:
--   The objects of Robinson's appendix *Conversion of a linear generalized equation to reduced form*. Throughout, $E$ is a real inner product space (in the theorems $E=\mathbb R^n$ with the standard inner product, through which $\mathbb R^n$ is identified with its dual).
--
--   1. **Normal cone.** For $C\subseteq E$ and $x\in E$, the normal-cone operator (the subdifferential of the indicator function $\psi_C$) is
--   $$\partial\psi_C(x)=\begin{cases}\{y : \langle y, c-x\rangle\le 0 \text{ for all } c\in C\}, & x\in C,\\ \emptyset, & x\notin C.\end{cases}$$
--   2. **Polyhedral convex set.** $C$ is polyhedral if it is the intersection of finitely many closed half-spaces $\{x:\langle a_i,x\rangle\le b_i\}$, $i=1,\dots,m$ (with $m=0$ giving all of $E$).
--   3. **Polar and tangent cone.** The polar of $S\subseteq E$ is $S^\circ=\{h:\langle y,h\rangle\le 0 \text{ for all } y\in S\}$, and the tangent cone to $C$ at $x_0$ is $T_C(x_0):=\partial\psi_C(x_0)^\circ$, as on p. 58 of the paper.
--   4. **The face $F$.** For $y_0\in E$, $F:=\partial\psi_C^*(-y_0)$ is the subdifferential at $-y_0$ of the support function $\psi_C^*$ of $C$, that is, the set of maximisers of $\langle -y_0,\cdot\rangle$ over $C$:
--   $$\partial\psi_C^*(-y_0)=\{x\in C : \langle -y_0,c\rangle\le\langle -y_0,x\rangle \text{ for all } c\in C\}.$$
--   It is empty when the supremum is not attained.
--   5. **Parallel subspace.** The subspace parallel to a set $F$ is the direction $L$ of its affine hull.
--   6. **Lineality space.** The lineality space of a cone $T$ is the subspace spanned by $T\cap(-T)$; for a convex cone it equals $T\cap(-T)$.
--   7. **Strong regularity** (DEFINITION, p. 45, specialised to $f(x)=Ax+a$). Let $C\subseteq\mathbb R^n$, $A$ an $n\times n$ real matrix, $a,x_0\in\mathbb R^n$ and $\lambda\in\mathbb R$. The generalized equation $0\in Ax+a+\partial\psi_C(x)$ is *strongly regular at $x_0$ with associated Lipschitz constant $\lambda$* if $x_0$ solves the unperturbed equation and there are neighbourhoods $U$ of $0$ and $V$ of $x_0$ and a map $s$ such that for every $y\in U$ the point $s(y)\in V$ solves
--   $$y\in As(y)+a+\partial\psi_C(s(y)),$$
--   it is the only solution of this inclusion in $V$, and $\|s(y_1)-s(y_2)\|\le\lambda\|y_1-y_2\|$ for all $y_1,y_2\in U$. In the paper's words, the restriction to $U$ of $T^{-1}\cap V$, with $T(x)=Ax+a+\partial\psi_C(x)$, is a single-valued function from $U$ to $V$ which is Lipschitzian on $U$ with modulus $\lambda$.
--   These are the objects in which Theorem A.4 (the reduced-form criterion) and Corollary 3.2 are stated. The P-matrix predicate used by Corollary 3.2 is imported from the Schur setting.
--
--   **Formalization Note** The ∅ clause of the normal cone is part of the definition, so an inclusion $y\in Ax+a+\partial\psi_C(x)$ forces $x\in C$. Inclusions are written as memberships $y-(Ax+a)\in\partial\psi_C(x)$. The Lipschitz modulus $\lambda$ is a real number with no sign constraint, as on the page. A matrix acts on $\mathbb R^n$ through `Matrix.toEuclideanLin`. Neighbourhoods are filter neighbourhoods, not necessarily open.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 43 (∂ψ_C), p. 45 (DEFINITION), p. 58 (Appendix: (A.1), T_C(x₀) = ∂ψ_C(x₀)°, F := ∂ψ*_C(−y₀), subspace parallel to F), p. 59 (lineality space of T)

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting

namespace RobinsonSR.Reduction

open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The normal-cone operator `∂ψ_C` (Robinson 1980, §1, p. 43), with `ℝⁿ` identified with its dual
through the inner product: for `x ∈ C` it is `{y | ⟪y, c - x⟫ ≤ 0 for all c ∈ C}`; for `x ∉ C` it
is `∅`. -/
def normalCone (C : Set E) (x : E) : Set E :=
  {y | x ∈ C ∧ ∀ c ∈ C, ⟪y, c - x⟫ ≤ 0}

/-- A polyhedral convex set: the intersection of finitely many closed half-spaces
`{x | ⟪a i, x⟫ ≤ b i}` (`m = 0` gives the whole space). -/
def IsPolyhedral (C : Set E) : Prop :=
  ∃ (m : ℕ) (a : Fin m → E) (b : Fin m → ℝ), C = {x | ∀ i, ⟪a i, x⟫ ≤ b i}

/-- The polar `S° = {h | ⟪y, h⟫ ≤ 0 for all y ∈ S}`. -/
def polar (S : Set E) : Set E :=
  {h | ∀ y ∈ S, ⟪y, h⟫ ≤ 0}

/-- The tangent cone `T_C(x₀) := ∂ψ_C(x₀)°` (Appendix, p. 58), the polar of the normal cone. -/
def tangentCone (C : Set E) (x0 : E) : Set E :=
  polar (normalCone C x0)

/-- The face `F := ∂ψ*_C(-y₀)` (Proposition A.2, p. 58): the subdifferential at `-y₀` of the
support function `ψ*_C` of `C`, i.e. the set of maximisers of `⟪-y₀, ·⟫` over `C`. It is `∅` when
the supremum is not attained. -/
def exposedFace (C : Set E) (y0 : E) : Set E :=
  {x | x ∈ C ∧ ∀ c ∈ C, ⟪-y0, c⟫ ≤ ⟪-y0, x⟫}

/-- The subspace parallel to a set `F`: the direction of its affine hull (Proposition A.3, p. 58). -/
def parallelSubspace (F : Set E) : Submodule ℝ E :=
  (affineSpan ℝ F).direction

/-- The lineality space of a cone `T` (p. 59): the subspace spanned by `T ∩ (-T)` (for a convex
cone `T`, `T ∩ (-T)` is already this subspace). -/
def linealitySpace (T : Set E) : Submodule ℝ E :=
  Submodule.span ℝ (T ∩ -T)

/-- Strong regularity (DEFINITION, p. 45) of the linear generalized equation
`0 ∈ A x + a + ∂ψ_C(x)` (A.1) at `x₀`, with associated Lipschitz constant `lam`. Here
`f(x) = A x + a`, so `f(x₀) + f′(x₀)(x - x₀) = A x + a` and `T x = A x + a + ∂ψ_C(x)`. There are
the required condition that `x₀` solves the unperturbed equation, and neighbourhoods `U` of `0`
and `V` of `x₀` such that the restriction to `U` of `T⁻¹ ∩ V` is a
single-valued function `s : U → V`, Lipschitzian on `U` with modulus `lam`: for each `y ∈ U`,
`s y ∈ V` solves `y ∈ T (s y)` (the inclusion (A.2)), it is the only solution in `V`, and
`‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖` on `U`. -/
def StronglyRegularLin {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ) (a x0 : EuclideanSpace ℝ (Fin n)) (lam : ℝ) : Prop :=
  -(Matrix.toEuclideanLin A x0 + a) ∈ normalCone C x0 ∧
  ∃ U ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ∃ V ∈ 𝓝 x0,
    ∃ s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      (∀ y ∈ U, s y ∈ V ∧ y - (Matrix.toEuclideanLin A (s y) + a) ∈ normalCone C (s y) ∧
         ∀ x ∈ V, y - (Matrix.toEuclideanLin A x + a) ∈ normalCone C x → x = s y) ∧
      ∀ y₁ ∈ U, ∀ y₂ ∈ U, ‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖

end RobinsonSR.Reduction


