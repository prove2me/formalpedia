-- Prove2me | Definitions.Def_WiesemannRMDP_AffineSDP_Programs
-- name    : WiesemannRMDP_AffineSDP_Programs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:40:03.964166+00:00
-- url     : https://prove2.me/theorems/be0c1347-44cf-4633-9680-51ccc0090ef1
-- title:
--   The affine approximate policy evaluation problem (19)/(21), the semidefinite program (20) and the epigraph constraints (22b)–(22c)
-- statement:
--   Fix the robust MDP of the `Model` module and a policy $\pi\in\Pi$. Write $(r_{sa})_{s'} := r(s,a,s')$ and $\bar r := \max_{s,a,s'} r(s,a,s')$.
--
--   **Problem (19)/(21).** An affine reward to-go function $\vartheta(\xi) = w + W\xi$ with $w\in\mathbb R^S$, $W\in\mathbb R^{S\times q}$ is **feasible** if
--   $$w + W\xi \le \widehat r(\xi) + \lambda\widehat P(\xi)\,(w + W\xi)\qquad\forall\,\xi\in\Xi,$$
--   componentwise, and its **objective value** is $\inf_{\xi\in\Xi} p_0^\top(w + W\xi)$. Problem (19) maximizes the objective value over feasible affine functions; "the supremum of (19)" is the supremum of the set of objective values of feasible solutions.
--
--   **The semidefinite program (20).** Decision variables are $\tau\in\mathbb R$, $w\in\mathbb R^S$, $W\in\mathbb R^{S\times q}$, $\gamma\in\mathbb R^L_+$ and $\Gamma\in\mathbb R^{S\times L}_+$; the objective is to maximize $\tau$ (20a) subject to
--   $$\begin{bmatrix}p_0^\top w-\tau & \tfrac12 p_0^\top W\\ \tfrac12 W^\top p_0 & 0\end{bmatrix} - \sum_{l=1}^L\gamma_l Q_l\succeq 0, \tag{20b}$$
--   $$\sum_{a\in\mathcal A}\pi(a\mid s)\begin{bmatrix}k_{sa}^\top(r_{sa}+\lambda w) & \tfrac12\big(r_{sa}^\top K_{sa}+\lambda[k_{sa}^\top W + w^\top K_{sa}]\big)\\ \tfrac12\big(K_{sa}^\top r_{sa}+\lambda[W^\top k_{sa}+K_{sa}^\top w]\big) & \lambda K_{sa}^\top W\end{bmatrix} - \begin{bmatrix}w_s & \tfrac12 W_{s\cdot}^\top\\ \tfrac12 (W_{s\cdot}^\top)^\top & 0\end{bmatrix} - \sum_{l=1}^L\Gamma_{sl}Q_l \succeq 0\quad\forall\, s\in\mathcal S, \tag{20c}$$
--   where $Q_l = \begin{bmatrix}\omega_l & \tfrac12 o_l^\top\\ \tfrac12 o_l & O_l\end{bmatrix}$ and $W_{s\cdot}^\top$ is the $s$-th row of $W$. A point is **optimal** in (20) if it is feasible and no feasible point has a larger $\tau$.
--
--   **The epigraph constraints (22b)–(22c).** For $\tau$, $w$, $W$:
--   $$\tau\le p_0^\top(w+W\xi)\quad\forall\,\xi\in\Xi, \tag{22b}$$
--   $$w_s + W_{s\cdot}^\top\xi \le \sum_{a\in\mathcal A}\pi(a\mid s)\,(k_{sa}+K_{sa}\xi)^\top\big(r_{sa}+\lambda[w+W\xi]\big)\quad\forall\,\xi\in\Xi, \tag{22c}$$
--   the latter for a given state $s$.
--
--   These are the two optimization problems that Theorem 3.8 compares.
--
--   **Formalization Note.** The affine functions $\vartheta:\Xi\to\mathbb R^S$ of (19) are encoded by their coefficients $(w,W)$, which is the paper's own rewriting (21); because $\Xi$ has nonempty interior, every affine map on $\Xi$ has exactly one such representation. The objective value is an infimum over the subtype $\Xi$; under the standing assumptions $\Xi$ is nonempty and compact and the infimum is attained. $\bar r$ is a supremum over the finite type $\mathcal S\times\mathcal A\times\mathcal S$, equal to the maximum for nonempty $\mathcal S,\mathcal A$. $\succeq 0$ is the quadratic-form reading of the `ParamSet` module, since the lower-right block $\lambda K_{sa}^\top W$ of (20c) is not symmetric. Optimality in (20) is a predicate; no claim is made that (20) has an optimal solution.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), pp. 21–22: Theorem 3.8 ((19), (20a)–(20c), r_sa), proof of Theorem 3.8 ((21), r̄, (22a)–(22c))

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_WiesemannRMDP_AffineSDP_ParamSet
import Definitions.Def_WiesemannRMDP_AffineSDP_Model

namespace WiesemannRMDP.AffineSDP

open FoundationsML.ReinforcementLearning Matrix

namespace Model

variable {St Act : Type*} {q L : ℕ}

/-- The reward vector `r_sa ∈ ℝ^S` of Theorem 3.8, p. 21: `(r_sa)_{s'} := r(s, a, s')`. -/
def rvec (M : Model St Act q L) (s : St) (a : Act) : St → ℝ :=
  fun s' => M.r s a s'

/-- The largest reward `r̄ := max_{s,a,s'} {r(s, a, s')}` (proof of Theorem 3.8, p. 22).

**Formalization Note.** Written as the supremum over the finite type `S × A × S`; for nonempty
`S` and `A` it is attained and equals the paper's maximum. -/
noncomputable def rbar (M : Model St Act q L) : ℝ :=
  ⨆ x : St × Act × St, M.r x.1 x.2.1 x.2.2

/-- Feasibility of the affine reward to-go function `ϑ(ξ) = w + W ξ` in the affine approximate
policy evaluation problem (19) (equivalently (21)), p. 21, for the fixed policy `π`:
`w + W ξ ≤ r̂(π; ξ) + λ P̂(π; ξ) (w + W ξ)` for all `ξ ∈ Ξ`, componentwise.

**Formalization Note.** Problem (19) optimizes over affine maps `ϑ : Ξ ↦a ℝ^S`. The paper itself
rewrites (19) as (21), over `ϑ(ξ) = w + W ξ` with `w ∈ ℝ^S`, `W ∈ ℝ^{S×q}`; since `Ξ` has
nonempty interior (Slater point), every affine map on `Ξ` has exactly this form. -/
def Feas19 [Fintype St] [Fintype Act] (M : Model St Act q L) (π : St → Act → ℝ)
    (w : St → ℝ) (W : Matrix St (Fin q) ℝ) : Prop :=
  ∀ ξ ∈ M.Xi, w + W *ᵥ ξ ≤ M.rhat π ξ + M.lam • (M.Phat π ξ *ᵥ (w + W *ᵥ ξ))

/-- The objective of (19)/(21), p. 21: `inf_{ξ∈Ξ} {p₀ᵀ(w + W ξ)}`.

**Formalization Note.** The infimum is over the subtype `Ξ`. Under `Model.Standing`, `Ξ` is
nonempty (it contains the Slater point) and compact (closed and bounded), and `ξ ↦ p₀ᵀ(w + Wξ)` is
affine, so the infimum is finite and attained. -/
noncomputable def val19 [Fintype St] (M : Model St Act q L) (w : St → ℝ)
    (W : Matrix St (Fin q) ℝ) : ℝ :=
  ⨅ ξ : M.Xi, M.p0 ⬝ᵥ (w + W *ᵥ (ξ : Fin q → ℝ))

/-- The set of objective values of feasible solutions of (19)/(21); its supremum is "the
supremum of (19)" of Theorem 3.8. -/
def values19 [Fintype St] [Fintype Act] (M : Model St Act q L) (π : St → Act → ℝ) : Set ℝ :=
  {t | ∃ (w : St → ℝ) (W : Matrix St (Fin q) ℝ), M.Feas19 π w W ∧ M.val19 w W = t}

/-- The matrix on the left of (20b), p. 21, before the multiplier term:
`[p₀ᵀw − τ, ½ p₀ᵀW; ½ Wᵀp₀, 0]`. -/
noncomputable def lhs20b [Fintype St] (M : Model St Act q L) (τ : ℝ) (w : St → ℝ)
    (W : Matrix St (Fin q) ℝ) : Matrix (Unit ⊕ Fin q) (Unit ⊕ Fin q) ℝ :=
  quadBlock (M.p0 ⬝ᵥ w - τ) (M.p0 ᵥ* W) 0

/-- The `(s, a)` summand of (20c), p. 21:
`[k_saᵀ(r_sa + λw), ½(r_saᵀK_sa + λ[k_saᵀW + wᵀK_sa]); ½(K_saᵀr_sa + λ[Wᵀk_sa + K_saᵀw]), λK_saᵀW]`.
The two off-diagonal blocks are transposes of one another; the lower-right block `λ K_saᵀ W` is in
general not symmetric. -/
noncomputable def block20c [Fintype St] (M : Model St Act q L) (s : St) (a : Act) (w : St → ℝ)
    (W : Matrix St (Fin q) ℝ) : Matrix (Unit ⊕ Fin q) (Unit ⊕ Fin q) ℝ :=
  quadBlock (M.k s a ⬝ᵥ (M.rvec s a + M.lam • w))
    (M.rvec s a ᵥ* M.K s a + M.lam • (M.k s a ᵥ* W + w ᵥ* M.K s a))
    (M.lam • ((M.K s a)ᵀ * W))

/-- The full matrix of (20c), p. 21, at state `s`:
`∑_{a∈A} π(a|s) [block20c s a] − [w_s, ½ W_{s·}ᵀ; ½ (W_{s·}ᵀ)ᵀ, 0] − ∑_l Γ_sl Q_l`,
where `W_{s·}ᵀ` is the `s`-th row of `W` (Lean: `W s`). -/
noncomputable def lhs20c [Fintype St] [Fintype Act] (M : Model St Act q L) (π : St → Act → ℝ) (s : St)
    (w : St → ℝ) (W : Matrix St (Fin q) ℝ) (Γ : St → Fin L → ℝ) :
    Matrix (Unit ⊕ Fin q) (Unit ⊕ Fin q) ℝ :=
  (∑ a : Act, π s a • M.block20c s a w W) - quadBlock (w s) (W s) 0 -
    ∑ l : Fin L, Γ s l • Qblock M.O M.o M.ω l

/-- Feasibility in the semidefinite program (20), p. 21, for the fixed policy `π`: decision
variables `τ ∈ ℝ`, `w ∈ ℝ^S`, `W ∈ ℝ^{S×q}`, `γ ∈ ℝ^L_+`, `Γ ∈ ℝ^{S×L}_+`, subject to

* (20b): `[p₀ᵀw − τ, ½ p₀ᵀW; ½ Wᵀp₀, 0] − ∑_l γ_l Q_l ⪰ 0`;
* (20c): `lhs20c s ⪰ 0` for every `s ∈ S`.

**Formalization Note.** `⪰ 0` is `IsPSDForm` (nonnegative quadratic form), as the matrix of (20c)
is not symmetric. -/
def Feas20 [Fintype St] [Fintype Act] (M : Model St Act q L) (π : St → Act → ℝ)
    (τ : ℝ) (w : St → ℝ) (W : Matrix St (Fin q) ℝ) (γ : Fin L → ℝ) (Γ : St → Fin L → ℝ) :
    Prop :=
  (∀ l, 0 ≤ γ l) ∧ (∀ s l, 0 ≤ Γ s l) ∧
  IsPSDForm (M.lhs20b τ w W - ∑ l : Fin L, γ l • Qblock M.O M.o M.ω l) ∧
  ∀ s : St, IsPSDForm (M.lhs20c π s w W Γ)

/-- `(τ, w, W, γ, Γ)` is an optimal solution of the semidefinite program (20), p. 21: it is
feasible and maximizes `τ` (20a) among all feasible points. -/
def IsOpt20 [Fintype St] [Fintype Act] (M : Model St Act q L) (π : St → Act → ℝ)
    (τ : ℝ) (w : St → ℝ) (W : Matrix St (Fin q) ℝ) (γ : Fin L → ℝ) (Γ : St → Fin L → ℝ) :
    Prop :=
  M.Feas20 π τ w W γ Γ ∧
  ∀ (τ' : ℝ) (w' : St → ℝ) (W' : Matrix St (Fin q) ℝ) (γ' : Fin L → ℝ) (Γ' : St → Fin L → ℝ),
    M.Feas20 π τ' w' W' γ' Γ' → τ' ≤ τ

/-- Constraint (22b), p. 22: `τ ≤ p₀ᵀ(w + W ξ)` for all `ξ ∈ Ξ`. -/
def Con22b [Fintype St] (M : Model St Act q L) (τ : ℝ) (w : St → ℝ)
    (W : Matrix St (Fin q) ℝ) : Prop :=
  ∀ ξ ∈ M.Xi, τ ≤ M.p0 ⬝ᵥ (w + W *ᵥ ξ)

/-- Constraint (22c), p. 22, at state `s`:
`w_s + W_{s·}ᵀ ξ ≤ ∑_{a∈A} π(a|s) (k_sa + K_sa ξ)ᵀ (r_sa + λ[w + W ξ])` for all `ξ ∈ Ξ`. -/
def Con22c [Fintype St] [Fintype Act] (M : Model St Act q L) (π : St → Act → ℝ) (s : St)
    (w : St → ℝ) (W : Matrix St (Fin q) ℝ) : Prop :=
  ∀ ξ ∈ M.Xi, w s + W s ⬝ᵥ ξ ≤
    ∑ a : Act, π s a * ((M.k s a + M.K s a *ᵥ ξ) ⬝ᵥ (M.rvec s a + M.lam • (w + W *ᵥ ξ)))

end Model

end WiesemannRMDP.AffineSDP


