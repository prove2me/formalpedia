-- Prove2me | Definitions.Def_MConvexL1_SD_Basic
-- name    : MConvexL1_SD_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:55.73417+00:00
-- url     : https://prove2.me/theorems/e302e9e4-dd5a-4080-abc5-c416db68a782
-- title:
--   §2.1 p. 4, §4 pp. 7–8, A.2 p. 17 — M-convex functions, bounded domains, the optimal sets M_k of (MML1(k)), runs of SteepestDescentMML1, monotone sequences
-- statement:
--   The objects of Shioura, *M-convex Function Minimization Under L1-Distance Constraint* (§2.1, p. 4; §4, pp. 7–8; Appendix A.2, p. 17). Let $V$ be a finite set, write $\chi_i \in \mathbb Z^V$ for the $i$-th unit vector, $\chi_0 = \mathbf 0$, $x(V) = \sum_v x(v)$, and $\|z\|_1 = \sum_v |z(v)|$.
--
--   1. **M-convex function** (p. 4). A function $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ is M$^\natural$-convex if
--   $$\forall x, y \in \operatorname{dom} f,\ \forall i \in \mathrm{supp}^+(x - y),\ \exists j \in \mathrm{supp}^-(x - y) \cup \{0\}:\ f(x) + f(y) \ge f(x - \chi_i + \chi_j) + f(y + \chi_i - \chi_j),$$
--   and **M-convex** if in addition $\operatorname{dom} f$ lies in a hyperplane $\{x \mid x(V) = \theta\}$ for some $\theta \in \mathbb Z$.
--
--   2. **Bounded domain** (p. 7). $\operatorname{dom} f$ is bounded: some $B$ satisfies $|x(v)| \le B$ for all $x \in \operatorname{dom} f$ and $v \in V$.
--
--   3. **The optimal sets $M_k$** (p. 8). For a center $x_c \in \mathbb Z^V$ and $k \in \mathbb Z_+$, $M_k$ is the set of optimal solutions of
--   $$(\mathrm{MML1}(k))\qquad \text{minimize } f(x) \text{ subject to } x \in \operatorname{dom} f,\ \|x - x_c\|_1 \le 2k.$$
--
--   4. **Runs of Algorithm SteepestDescentMML1** (p. 8). Given $\sigma \le \gamma$, a sequence $(x_k)$ is a run if $x_\sigma \in M_\sigma$ (Step 0) and, for every $k$ with $\sigma < k \le \gamma$, $x_k = x_{k-1} + \chi_{i_k} - \chi_{j_k}$ for a pair $(i_k, j_k) \in V \times V$ minimizing $f(x_{k-1} + \chi_i - \chi_j)$ over all pairs $(i, j)$, $i = j$ included (Steps 2–3). The output is $x_\gamma$ (Step 1).
--
--   5. **Monotone sequence** (p. 17). A sequence $y_0, \dots, y_h \in \operatorname{dom} f$ is monotone if $\|y_k - y_0\|_1 = 2k$ for $k = 0, \dots, h$ and, for $k = 0, \dots, h-1$, $y_{k+1} = y_k - \chi_i + \chi_j$ for some $i \in \mathrm{supp}^+(y_k - y_h)$ and $j \in \mathrm{supp}^-(y_k - y_h)$.
--
--   These objects carry every statement of the mission: Theorem 4.1 describes the sets $M_k$, Lemma A.3 produces monotone sequences, and Theorem 4.2 says every run stays in the sets $M_k$.
--
--   **Formalization Note** Vectors are `V → ℤ`, values are in `WithTop ℝ` ($+\infty = \top$), and $\|x - y\|_1$ is the published `L1Dist x y : ℕ`. (M$^\natural$-EXC) is the published `MNatExchangeAxiom`, written with a minimum over the finite set $\mathrm{supp}^-(x - y)$ and the term $j = 0$; a minimum over a finite set in a linear order is attained, so this is the existential above. $M_k$ omits the constraint $x(V) = \theta$ of (MML1), which every point of $\operatorname{dom} f$ satisfies when the hyperplane passes through $x_c$. In a run the indices $k < \sigma$ and $k > \gamma$ are unconstrained. The page states the monotonicity condition in two forms and says one "can be rewritten" as the other; the definition requires both (the step form implies the distance form when $y_0, \dots, y_h$ is read as a path towards $y_h$).
-- source:
--   Shioura, M-convex Function Minimization Under L1-Distance Constraint, arXiv:1809.03126v3, pp. 2, 4, 7–8, 17, (MML1), (M♮-EXC), (4.1), Algorithm SteepestDescentMML1, definition of a monotone sequence

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctions_MNatExchangeAxiom
import Definitions.Def_DiscreteConvex_Algorithms_L1Dist
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms

namespace MConvexL1.SD

/-- **M-convex function** (Shioura, §2.1, p. 4): `f : ℤ^V → ℝ ∪ {+∞}` satisfies the exchange
property (M♮-EXC) and its effective domain lies in a hyperplane `{x | x(V) = θ}` for some
`θ ∈ ℤ`. -/
def MConvex {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) : Prop :=
  MNatExchangeAxiom f ∧ ∃ θ : ℤ, ∀ x ∈ DomZ f, ∑ v, x v = θ

/-- The effective domain of `f` is bounded (§4, p. 7): some `B` bounds every coordinate of every
point of `dom f`. -/
def BddDom {V : Type*} (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ B : ℤ, ∀ x ∈ DomZ f, ∀ v, |x v| ≤ B

/-- `M_k` (p. 8): the set of optimal solutions of `(MML1(k))`, i.e. of minimizing `f(x)` over
`x ∈ dom f` with `‖x - x_c‖₁ ≤ 2k`. (The constraint `x(V) = θ` of (MML1) is implied by
`x ∈ dom f` whenever `dom f` lies in the hyperplane through `x_c`, and is omitted.) -/
def Mset {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (xc : V → ℤ) (k : ℕ) :
    Set (V → ℤ) :=
  {x | x ∈ DomZ f ∧ L1Dist x xc ≤ 2 * k ∧
    ∀ y ∈ DomZ f, L1Dist y xc ≤ 2 * k → f x ≤ f y}

/-- A run of Algorithm SteepestDescentMML1 (p. 8) with parameters `σ ≤ γ`: the vector `x σ` is
a point of `M_σ` (Step 0), and for every `k` with `σ < k ≤ γ` the vector `x k` equals
`x (k-1) + χ_i - χ_j` for a pair `(i, j) ∈ V × V` (with `i = j` allowed) minimizing
`f(x (k-1) + χ_i - χ_j)` over all pairs (Steps 2–3). The output is `x γ` (Step 1). -/
def IsSDRun {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) (xc : V → ℤ)
    (σ γ : ℕ) (x : ℕ → V → ℤ) : Prop :=
  x σ ∈ Mset f xc σ ∧
  ∀ k, σ < k → k ≤ γ → ∃ i j : V,
    (∀ i' j' : V, f (fun w => x (k - 1) w + CharVec i w - CharVec j w)
                  ≤ f (fun w => x (k - 1) w + CharVec i' w - CharVec j' w)) ∧
    x k = fun w => x (k - 1) w + CharVec i w - CharVec j w

/-- A **monotone sequence** `y_0, …, y_h ∈ dom f` (Appendix A.2, p. 17): `‖y_k - y_0‖₁ = 2k`
for `k = 0, …, h`, and for `k = 0, …, h - 1` one has `y_{k+1} = y_k - χ_i + χ_j` for some
`i ∈ supp⁺(y_k - y_h)` and `j ∈ supp⁻(y_k - y_h)`. -/
def IsMonotoneSeq {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (y : ℕ → V → ℤ) (h : ℕ) : Prop :=
  (∀ k ≤ h, y k ∈ DomZ f) ∧ (∀ k ≤ h, L1Dist (y k) (y 0) = 2 * k) ∧
  ∀ k < h, ∃ i ∈ SuppPos (y k) (y h), ∃ j ∈ SuppNeg (y k) (y h),
    y (k + 1) = fun w => y k w - CharVec i w + CharVec j w

end MConvexL1.SD


