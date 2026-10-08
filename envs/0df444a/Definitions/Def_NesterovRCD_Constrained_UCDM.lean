-- Prove2me | Definitions.Def_NesterovRCD_Constrained_UCDM
-- name    : NesterovRCD_Constrained_UCDM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T15:13:19.463966+00:00
-- url     : https://prove2.me/theorems/0f233063-c7a2-4fa7-90b8-9b60d5f9f712
-- title:
--   Problem (4.1) on $Q=\otimes Q_i$, the constrained block update $u^{(i)}(x)$, $V_i(x)$ (4.2), the method UCDM$(x_0)$ (4.5), and $R_1(x_0)$
-- statement:
--   These are the objects of §4 (constrained minimization) of Nesterov's paper. Let $Q_i\subseteq\mathbb R^{n_i}$, $i=1,\dots,n$, and let $f:\mathbb R^N\to\mathbb R$ with constants $L_i>0$.
--
--   1. **The feasible set.** $Q=Q_1\times\cdots\times Q_n$, and problem (4.1) is $\min_{x\in Q}f(x)$.
--   2. **The block subproblem (4.2).** A point $u\in\mathbb R^{n_i}$ *solves the $i$-th block subproblem at $x$* if $u\in Q_i$ and, for every $w\in Q_i$,
--   $$\langle f'_i(x),u-x^{(i)}\rangle+\tfrac{L_i}2\|u-x^{(i)}\|_{(i)}^2\le\langle f'_i(x),w-x^{(i)}\rangle+\tfrac{L_i}2\|w-x^{(i)}\|_{(i)}^2 .$$
--   3. **The constrained coordinate update (4.2).** $u^{(i)}(x)$ is a solution of that subproblem, and
--   $$V_i(x)=x+U_i\big(u^{(i)}(x)-x^{(i)}\big).$$
--   4. **UCDM$(x_0)$ (4.5).** Given draws $i_0,\dots,i_{k-1}\in\{1,\dots,n\}$, the iterates are $x_{s+1}=V_{i_s}(x_s)$, starting from $x_0$. The draws are uniform on $\{1,\dots,n\}$; this enters through the expectation, with all weights $1/n$.
--   5. **Optimal solutions.** $x_*$ is an optimal solution of (4.1) if $x_*\in Q$ and $f(x_*)\le f(y)$ for all $y\in Q$; then $f^*=f(x_*)$.
--   6. **The level-set radius.** "$R_1(x_0)\le R$" means: $\|x-x_*\|_1\le R$ for every $x\in Q$ with $f(x)\le f(x_0)$ and every optimal solution $x_*$ of (4.1). Here $R_1(x_0)=\max_x\{\max_{x_*\in X_*}\|x-x_*\|_1: f(x)\le f(x_0)\}$, the quantity of p. 7, read for problem (4.1).
--
--   These objects define the method whose rate is the goal of the mission.
--
--   **Formalization Note** The paper writes $V_i(x)=x+U_i^T(u^{(i)}(x)-x^{(i)})$; $U_i^T$ maps $\mathbb R^N$ to $\mathbb R^{n_i}$, so this is a typo for $U_i$, and Lean uses `Pi.single i`. $u^{(i)}(x)$ is chosen with `Classical.epsilon` among the solutions of the subproblem. When $Q_i$ is nonempty, closed and convex, $L_i>0$ and the block norm is Euclidean (the setting of §4), the subproblem has exactly one solution, so the choice is the paper's $u^{(i)}(x)$ and the junk value of `Classical.epsilon` is never reached; every theorem of the mission carries those hypotheses. The paper defines $R_\beta(x_0)$ for the unconstrained problem; for (4.1) the level set is taken inside $Q$ and $X_*$ is the set of optimal solutions of (4.1). $R_1(x_0)$ is not computed: `LevelRadiusOnLE f L Q x0 R` is the statement $R_1(x_0)\le R$, equivalent to the paper's bound when the max is finite, and it avoids the junk value of a supremum. Indices are `Fin n`, 0-based.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 13, §4, (4.1), (4.2), (4.5); R_β(x_0) defined in Theorem 1, p. 7

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic

namespace NesterovRCD.Constrained

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- The feasible set Q = Q_1 × ⋯ × Q_n of (4.1). -/
def Qset (Q : ∀ i, Set (E i)) : Set (NesterovRCD.Sublinear.Blocks E) := Set.univ.pi Q

/-- u solves the block subproblem of (4.2) at x:
u ∈ Q_i minimizes ⟨f′_i(x), w − x^{(i)}⟩ + (L_i/2)‖w − x^{(i)}‖²_{(i)} over w ∈ Q_i. -/
def IsBlockUpdate (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (Q : ∀ i, Set (E i)) (x : NesterovRCD.Sublinear.Blocks E)
    (i : Fin n) (u : E i) : Prop :=
  u ∈ Q i ∧ ∀ w ∈ Q i, NesterovRCD.Sublinear.partialGrad f x i (u - x i) + L i / 2 * ‖u - x i‖ ^ 2
                          ≤ NesterovRCD.Sublinear.partialGrad f x i (w - x i) + L i / 2 * ‖w - x i‖ ^ 2

/-- u^{(i)}(x) of (4.2), chosen by `Classical.epsilon`. When Q_i is nonempty, closed and convex,
L_i > 0 and the block norm is Euclidean, the minimizer exists and is unique (the objective is
strongly convex), so this is the paper's u^{(i)}(x). -/
noncomputable def blockUpdate (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (Q : ∀ i, Set (E i))
    (x : NesterovRCD.Sublinear.Blocks E) (i : Fin n) : E i :=
  Classical.epsilon (IsBlockUpdate f L Q x i)

/-- V_i(x) = x + U_i(u^{(i)}(x) − x^{(i)}) (4.2). -/
noncomputable def constrStep (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (Q : ∀ i, Set (E i))
    (i : Fin n) (x : NesterovRCD.Sublinear.Blocks E) : NesterovRCD.Sublinear.Blocks E :=
  x + Pi.single i (blockUpdate f L Q x i - x i)

/-- UCDM(x_0) (4.5) along given draws: `ucdm f L Q x0 k idx` is x_k when i_s = idx s
(s = 0, …, k − 1). The uniform distribution of the draws enters through `expect`. -/
noncomputable def ucdm (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (Q : ∀ i, Set (E i))
    (x0 : NesterovRCD.Sublinear.Blocks E) : (k : ℕ) → (Fin k → Fin n) → NesterovRCD.Sublinear.Blocks E
  | 0, _ => x0
  | k + 1, idx => constrStep f L Q (idx (Fin.last k)) (ucdm f L Q x0 k (Fin.init idx))

/-- x* ∈ X*: a minimizer of f on Q, i.e. an optimal solution of (4.1). -/
def IsMinimizerOn (f : NesterovRCD.Sublinear.Blocks E → ℝ) (Q : ∀ i, Set (E i)) (xs : NesterovRCD.Sublinear.Blocks E) : Prop :=
  xs ∈ Qset Q ∧ ∀ y ∈ Qset Q, f xs ≤ f y

/-- R_1(x_0) ≤ R for problem (4.1): every feasible x with f(x) ≤ f(x_0) is within
‖·‖_1-distance R of every optimal solution of (4.1). -/
def LevelRadiusOnLE (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (Q : ∀ i, Set (E i)) (x0 : NesterovRCD.Sublinear.Blocks E)
    (R : ℝ) : Prop :=
  ∀ x ∈ Qset Q, f x ≤ f x0 → ∀ xs, IsMinimizerOn f Q xs → NesterovRCD.Sublinear.wnorm L 1 (x - xs) ≤ R

end NesterovRCD.Constrained


