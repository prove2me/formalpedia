-- Prove2me | Definitions.Def_BellRegret_Representation_Model
-- name    : BellRegret_Representation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:12:28.50045+00:00
-- url     : https://prove2.me/theorems/be6ff410-99b4-4135-8278-7ac6894daac6
-- title:
--   Sec. 1, pp. 965–969 — simple comparisons, inequality (1), incremental-value shifts and Assumptions 1–3
-- statement:
--   This file sets up Bell's model of decision making with regret.
--
--   **Utility over final and foregone assets.** A decision maker's satisfaction at an endpoint is described by two attributes: the final assets $x$ and the **foregone assets** $y$, the asset level given up by the decision made. Utility is a function $u(x,y)$ of the two, increasing in $x$ and decreasing in $y$. A **value function** $v$ measures incremental value: the increment from $a$ to $b$ is worth $v(b)-v(a)$.
--
--   **Simple comparisons and inequality (1).** In a simple comparison all uncertainties are resolved according to a predetermined joint distribution. Model it by $n$ states with a probability vector $p=(p_1,\dots,p_n)$, $p_i\ge0$, $\sum_i p_i=1$, and two alternatives $A,B\in\mathbb R^n$, where $A_i$ is the final assets of $A$ in state $i$. If $A$ is selected, $B$ is foregone, so the expected utility of selecting $A$ against $B$ is
--   $$\mathrm{EU}_p(A\,|\,B)=\sum_{i=1}^n p_i\,u(A_i,B_i).$$
--   $A$ is **preferred** to $B$ when $\mathrm{EU}_p(B\,|\,A)<\mathrm{EU}_p(A\,|\,B)$; with two states and $p=(p,1-p)$ this is inequality (1) of the paper. The decision maker is **indifferent** when neither alternative is preferred.
--
--   **Shifts by incremental value.** $A'$ is obtained from $A$ by an increase (decrease) of incremental value $\delta\in\mathbb R$ if $v(A_i')=v(A_i)+\delta$ for every state $i$.
--
--   1. **Assumption 1.** If every outcome of both alternatives is shifted by the same incremental value $\delta$, a preferred alternative stays preferred.
--   2. **Assumption 2.** If $v(x_2)-v(x_1)=v(x_3)-v(x_2)$, the decision maker is indifferent between $x_2$ for sure and a 50-50 lottery between $x_1$ and $x_3$, i.e.
--   $$\tfrac12u(x_2,x_1)+\tfrac12u(x_2,x_3)=\tfrac12u(x_1,x_2)+\tfrac12u(x_3,x_2).$$
--   3. **Assumption 3.** If selecting $L_1$ over $L_2$ is preferred to selecting $L_3$ over $L_4$, that is $\mathrm{EU}_p(L_3\,|\,L_4)<\mathrm{EU}_p(L_1\,|\,L_2)$, the same holds after every outcome of all four alternatives is shifted by the same incremental value.
--
--   These are the objects every result of Bell's representation theorem (Lemmas 1–2, Theorem 1) is stated with.
--
--   **Formalization Note** Utilities, assets and probabilities are real numbers; $u$ is `u : ℝ → ℝ → ℝ` with `u x y` $=u(x,y)$. A simple comparison is a common finite state space `Fin n`; the four lotteries of Assumption 3 live on one common state space, which is the setting of the paper's own uses of the assumption. "Increased (decreased) by equal incremental value" is a shift by an arbitrary real $\delta$ of either sign. The 50-50 lottery is the two-state vector $(\tfrac12,\tfrac12)$ and "$x_2$ for sure" is the constant alternative $(x_2,x_2)$. The monotonicity of $u$ and $v$ is not part of these definitions; each theorem states it as a hypothesis.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, pp. 965–969 (PDF 6–10): Definition (p. 965), inequality (1) (p. 966), Assumption 1 (p. 966), Assumption 2 (p. 968), Assumption 3 (p. 969)

import Mathlib

namespace BellRegret.Representation

/-! Bell, *Regret in Decision Making under Uncertainty*, Operations Research 30(5) (1982) 961–981,
Definition (p. 965), inequality (1) and Assumptions 1–3 (pp. 965–969).

A utility `u : ℝ → ℝ → ℝ` is read as `u x y` = utility of final assets `x` when the foregone
assets are `y`. A value function `v : ℝ → ℝ` measures incremental value: the increment from `a`
to `b` is worth `v b - v a`. A simple comparison on `n` states of a common, predetermined joint
distribution is a probability vector `p : Fin n → ℝ` together with two alternatives
`A B : Fin n → ℝ`, `A i` being the final assets of the alternative in state `i`. -/

/-- `p` is a probability vector on `n` states: nonnegative entries summing to one. -/
def IsProbVec {n : ℕ} (p : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- Expected utility of selecting alternative `A` when alternative `B` is foregone, state by
state: `∑ᵢ pᵢ u(Aᵢ, Bᵢ)` (the sides of inequality (1), p. 966). -/
def selectEU (u : ℝ → ℝ → ℝ) {n : ℕ} (p : Fin n → ℝ) (A B : Fin n → ℝ) : ℝ :=
  ∑ i, p i * u (A i) (B i)

/-- Inequality (1), p. 966, on `n` states: in the simple comparison `(p, A, B)` alternative `A`
is (strictly) preferred to alternative `B`. -/
def Prefers (u : ℝ → ℝ → ℝ) {n : ℕ} (p : Fin n → ℝ) (A B : Fin n → ℝ) : Prop :=
  selectEU u p B A < selectEU u p A B

/-- The decision maker is indifferent between `A` and `B`: neither is preferred. -/
def Indifferent (u : ℝ → ℝ → ℝ) {n : ℕ} (p : Fin n → ℝ) (A B : Fin n → ℝ) : Prop :=
  ¬ Prefers u p A B ∧ ¬ Prefers u p B A

/-- `A'` is obtained from `A` by increasing (if `δ > 0`) or decreasing (if `δ < 0`) every
outcome by the incremental value `δ`: `v (A' i) - v (A i) = δ` for every state `i`. -/
def IsShift (v : ℝ → ℝ) (δ : ℝ) {n : ℕ} (A A' : Fin n → ℝ) : Prop :=
  ∀ i, v (A' i) = v (A i) + δ

/-- **Assumption 1** (p. 966). If all final asset positions of both alternatives are changed by
the same incremental value `δ`, the preferred alternative is unchanged. -/
def Assumption1 (u : ℝ → ℝ → ℝ) (v : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℝ) (A B A' B' : Fin n → ℝ) (δ : ℝ),
    IsProbVec p → IsShift v δ A A' → IsShift v δ B B' →
      Prefers u p A B → Prefers u p A' B'

/-- **Assumption 2** (p. 968). If the incremental value from `x₁` to `x₂` equals that from `x₂`
to `x₃`, the decision maker is indifferent between `x₂` for sure and a 50-50 lottery between
`x₁` and `x₃` (two equally likely states; sure `x₂` is `![x₂, x₂]`). -/
def Assumption2 (u : ℝ → ℝ → ℝ) (v : ℝ → ℝ) : Prop :=
  ∀ x₁ x₂ x₃ : ℝ, v x₂ - v x₁ = v x₃ - v x₂ →
    Indifferent u ![1 / 2, 1 / 2] ![x₂, x₂] ![x₁, x₃]

/-- **Assumption 3** (p. 969). If selecting `L₁ = A` over `L₂ = B` is preferred to selecting
`L₃ = C` over `L₄ = D`, this remains so after all outcomes of all four alternatives are changed
by the same incremental value `δ`. The four alternatives live on one common state space. -/
def Assumption3 (u : ℝ → ℝ → ℝ) (v : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℝ) (A B C D A' B' C' D' : Fin n → ℝ) (δ : ℝ),
    IsProbVec p → IsShift v δ A A' → IsShift v δ B B' → IsShift v δ C C' → IsShift v δ D D' →
      selectEU u p C D < selectEU u p A B → selectEU u p C' D' < selectEU u p A' B'

end BellRegret.Representation


