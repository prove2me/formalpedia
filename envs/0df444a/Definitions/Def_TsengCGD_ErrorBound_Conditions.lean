-- Prove2me | Definitions.Def_TsengCGD_ErrorBound_Conditions
-- name    : TsengCGD_ErrorBound_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T20:01:05.399868+00:00
-- url     : https://prove2.me/theorems/5d0dd2dc-f953-46b2-a892-fc3d8fbb2a67
-- title:
--   The subproblem (42), polyhedral functions and sets, and the conditions C1–C4 of Lemma 7 and Theorem 4
-- statement:
--   The notation is that of the shared definition files `TsengCGD.Global.Basic` and `TsengCGD.Linear.Basic`: $F_c = f + cP$ with $c > 0$, $P$ proper convex lsc with domain $\operatorname{dom}P$, and $f$ continuously differentiable near $\operatorname{dom}P$.
--
--   **The subproblem (42).** Write $\operatorname{epi}P = \{(x,\xi) \mid P(x) \le \xi\}$. For $(x,\xi) \in \operatorname{epi}P$, the **projection residual** at $(x,\xi)$ is the optimal solution $(\tilde d,\tilde\delta)$ of
--   $$\min_{(d,\delta)} \Big\{ \nabla f(x)^\top d + \tfrac12\|d\|^2 + \tfrac12\delta^2 + c\delta \;\Big|\; (x+d,\ \xi+\delta) \in \operatorname{epi}P \Big\}. \qquad (42)$$
--   Its size is measured by the Euclidean norm on $\mathbb R^n\times\mathbb R$, $\|(d,\delta)\| = \sqrt{\|d\|^2 + \delta^2}$.
--
--   **Lipschitz and polyhedral $P$.** $P$ is **Lipschitz continuous on $\operatorname{dom}P$** with constant $K \ge 0$ if $|P(y) - P(z)| \le K\|y - z\|$ for $y, z \in \operatorname{dom}P$. $P$ is **polyhedral** if $\operatorname{epi}P$ is a polyhedral set of $\mathbb R^n\times\mathbb R$, the solution set of finitely many inequalities $a_i^\top x + b_i\xi \le e_i$. A **polyhedral set** $Y \subseteq \mathbb R^m$ is the solution set of finitely many inequalities $a_i^\top y \le b_i$. A function $f$ is **quadratic** if $f(x) = \tfrac12 x^\top A x + b^\top x + c_0$ with $A$ symmetric (not necessarily positive semidefinite).
--
--   **The conditions.**
--   1. **C1**: $f$ is quadratic and $P$ is polyhedral.
--   2. **C2**: $f(x) = g(Ex) + q^\top x$ for all $x$, where $E \in \mathbb R^{m\times n}$, $q \in \mathbb R^n$, and $g$ is a strongly convex differentiable function on $\mathbb R^m$ with $\nabla g$ Lipschitz on $\mathbb R^m$; $P$ is polyhedral.
--   3. **C3**: $f(x) = \max_{y\in Y}\{(Ex)^\top y - g(y)\} + q^\top x$ for all $x$, where $Y \subseteq \mathbb R^m$ is polyhedral, $E$, $q$, $g$ are as in C2; $P$ is polyhedral.
--   4. **C4**: $f$ is strongly convex and satisfies (22) for some $L \ge 0$.
--
--   C1–C3 are the hypotheses of Lemma 7 and, with C4, of Theorem 4: each describes a problem class for which the local error bound of Assumption 2(a) holds.
--
--   **Formalization Note** The constraint $(x+d,\xi+\delta) \in \operatorname{epi}P$ is `x + d ∈ D ∧ P (x + d) ≤ ξ + δ`, and "$(\tilde d,\tilde\delta)$ is an optimal solution of (42)" is the predicate `IsEpiSubSol`, so no statement depends on a chosen minimizer. $E$ is a continuous linear map $\mathbb R^n \to \mathbb R^m$ (equivalently an $m\times n$ matrix). Strong convexity is Mathlib's `StrongConvexOn s μ g` with modulus $\mu > 0$ ($g(ax+by) \le ag(x)+bg(y) - ab\,\tfrac{\mu}{2}\|x-y\|^2$). In C3 the maximum is required to be attained at every $x$ (`IsGreatest`), which forces $Y \neq \emptyset$, as the paper's formula presumes. In C4 strong convexity and (22) are required on $\operatorname{dom}P$ only, since $f$ is only assumed smooth near $\operatorname{dom}P$; this is weaker than strong convexity on $\mathbb R^n$, so results assuming C4 are at least as strong as printed.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), p. 410 (42), p. 411 (Lemma 7, C1–C3), p. 412 (Theorem 4, C4); polyhedral P as defined on p. 388

import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic

namespace TsengCGD.ErrorBound

open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The objective of (42) at (d, δ): ∇f(x)ᵀd + ½‖d‖² + ½δ² + cδ. -/
noncomputable def epiObj (f : TsengCGD.Global.Vec n → ℝ) (c : ℝ) (x d : TsengCGD.Global.Vec n) (δ : ℝ) : ℝ :=
  ⟪gradient f x, d⟫ + ‖d‖ ^ 2 / 2 + δ ^ 2 / 2 + c * δ

/-- (d, δ) is an optimal solution of (42) at (x, ξ): (x + d, ξ + δ) ∈ epi P, i.e. x + d ∈ dom P and
P(x + d) ≤ ξ + δ, and no feasible (d′, δ′) has a smaller objective. -/
def IsEpiSubSol (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ) (x : TsengCGD.Global.Vec n) (ξ : ℝ)
    (d : TsengCGD.Global.Vec n) (δ : ℝ) : Prop :=
  x + d ∈ D ∧ P (x + d) ≤ ξ + δ ∧
    ∀ (d' : TsengCGD.Global.Vec n) (δ' : ℝ), x + d' ∈ D → P (x + d') ≤ ξ + δ' →
      epiObj f c x d δ ≤ epiObj f c x d' δ'

/-- ‖(d, δ)‖, the Euclidean norm on ℜⁿ × ℜ. -/
noncomputable def pairNorm (d : TsengCGD.Global.Vec n) (δ : ℝ) : ℝ := Real.sqrt (‖d‖ ^ 2 + δ ^ 2)

/-- P is Lipschitz continuous on dom P with constant K ≥ 0. -/
def PLipOn (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ y ∈ D, ∀ z ∈ D, |P y - P z| ≤ K * ‖y - z‖

/-- P is polyhedral (p. 388): its epigraph epi P = {(x, ξ) | x ∈ D, P x ≤ ξ} is a polyhedral set,
i.e. the solution set of finitely many weak linear inequalities in (x, ξ) ∈ ℜⁿ × ℜ. -/
def IsPolyhedral (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) : Prop :=
  ∃ (m : ℕ) (a : Fin m → TsengCGD.Global.Vec n) (b e : Fin m → ℝ),
    ∀ (x : TsengCGD.Global.Vec n) (ξ : ℝ), (x ∈ D ∧ P x ≤ ξ) ↔ ∀ i, ⟪a i, x⟫ + b i * ξ ≤ e i

/-- A polyhedral set in ℜᵐ: the solution set of finitely many weak linear inequalities. -/
def IsPolyhedralSet {m : ℕ} (Y : Set (EuclideanSpace ℝ (Fin m))) : Prop :=
  ∃ (r : ℕ) (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ),
    Y = {y | ∀ i, ⟪a i, y⟫ ≤ b i}

/-- f is quadratic: f(x) = ½xᵀAx + bᵀx + c₀ for all x, with A symmetric (not necessarily
positive semidefinite). -/
def IsQuadratic (f : TsengCGD.Global.Vec n → ℝ) : Prop :=
  ∃ (A : Matrix (Fin n) (Fin n) ℝ) (b : TsengCGD.Global.Vec n) (c₀ : ℝ),
    A.IsSymm ∧ ∀ x, f x = TsengCGD.Global.qf A x / 2 + ⟪b, x⟫ + c₀

/-- Condition C1 of Lemma 7 (p. 411): f is quadratic and P is polyhedral. -/
def C1 (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) : Prop :=
  IsQuadratic f ∧ IsPolyhedral D P

/-- Condition C2 of Lemma 7 (p. 411): f(x) = g(Ex) + qᵀx for all x, with E : ℜⁿ → ℜᵐ linear,
q ∈ ℜⁿ, g strongly convex and differentiable on ℜᵐ with ∇g Lipschitz on ℜᵐ; P is polyhedral. -/
def C2 (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) : Prop :=
  ∃ (m : ℕ) (E : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (q : TsengCGD.Global.Vec n)
    (g : EuclideanSpace ℝ (Fin m) → ℝ) (μ : ℝ) (Lg : NNReal),
    0 < μ ∧ StrongConvexOn Set.univ μ g ∧ Differentiable ℝ g ∧
      LipschitzWith Lg (gradient g) ∧ (∀ x, f x = g (E x) + ⟪q, x⟫) ∧ IsPolyhedral D P

/-- Condition C3 of Lemma 7 (p. 411): f(x) = max_{y∈Y} {(Ex)ᵀy − g(y)} + qᵀx for all x, the maximum
being attained, with Y ⊆ ℜᵐ polyhedral, E : ℜⁿ → ℜᵐ linear, q ∈ ℜⁿ, g strongly convex and
differentiable on ℜᵐ with ∇g Lipschitz on ℜᵐ; P is polyhedral. -/
def C3 (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) : Prop :=
  ∃ (m : ℕ) (Y : Set (EuclideanSpace ℝ (Fin m)))
    (E : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (q : TsengCGD.Global.Vec n)
    (g : EuclideanSpace ℝ (Fin m) → ℝ) (μ : ℝ) (Lg : NNReal),
    IsPolyhedralSet Y ∧ 0 < μ ∧ StrongConvexOn Set.univ μ g ∧ Differentiable ℝ g ∧
      LipschitzWith Lg (gradient g) ∧
      (∀ x, IsGreatest {v | ∃ y ∈ Y, v = ⟪E x, y⟫ - g y} (f x - ⟪q, x⟫)) ∧ IsPolyhedral D P

/-- Condition C4 of Theorem 4 (p. 412): f is strongly convex (on dom P) and satisfies (22) for some
L ≥ 0. -/
def C4 (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) : Prop :=
  (∃ μ > 0, StrongConvexOn D μ f) ∧ ∃ L, TsengCGD.Linear.GradLipOn f D L

end TsengCGD.ErrorBound


