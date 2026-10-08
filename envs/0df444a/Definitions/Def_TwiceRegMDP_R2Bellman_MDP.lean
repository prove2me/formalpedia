-- Prove2me | Definitions.Def_TwiceRegMDP_R2Bellman_MDP
-- name    : TwiceRegMDP_R2Bellman_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:06:13.421296+00:00
-- url     : https://prove2.me/theorems/d1071e44-14d3-416e-a699-28063bcc4a7c
-- title:
--   Finite discounted MDP: the ℓ² norm, stochastic policies, the q-function and the evaluation Bellman operator $T^\pi_{(P,r)}$
-- statement:
--   Let $\mathcal S$ and $\mathcal A$ be finite sets of states and actions. A **transition array** is a function $P:\mathcal S\times\mathcal A\times\mathcal S\to\mathbb R$, where $P(s'\mid s,a)$ is the probability of moving to $s'$ after playing $a$ in $s$; it is a **transition kernel** when every $P(\cdot\mid s,a)$ is a probability distribution on $\mathcal S$. A reward is a function $r:\mathcal S\times\mathcal A\to\mathbb R$ and $\gamma$ is a discount factor.
--
--   This file defines the following objects.
--
--   1. The **$\ell_2$-norm** of a function $a\in\mathbb R^{\mathcal Z}$ on a finite set $\mathcal Z$, induced by the inner product $\langle a,b\rangle=\sum_{z}a(z)b(z)$:
--   $$\|a\| = \sqrt{\langle a,a\rangle}=\Big(\sum_{z\in\mathcal Z}a(z)^2\Big)^{1/2}.$$
--   2. A **policy** $\pi\in\Delta_{\mathcal A}^{\mathcal S}$: a map assigning to every state $s$ a probability distribution $\pi_s\in\Delta_{\mathcal A}$ on the actions (stationary and stochastic).
--   3. The **q-function** of a value function $v\in\mathbb R^{\mathcal S}$: $q(s,a)=r(s,a)+\gamma\langle P(\cdot\mid s,a),v\rangle$.
--   4. The **evaluation Bellman operator** $T^\pi_{(P,r)}v=r^\pi+\gamma P^\pi v$, that is,
--   $$[T^\pi_{(P,r)}v](s)=\sum_{a\in\mathcal A}\pi_s(a)\Big(r(s,a)+\gamma\sum_{s'\in\mathcal S}P(s'\mid s,a)\,v(s')\Big).$$
--
--   These are the standard objects of a finite discounted Markov decision process on which the twice regularized (R²) Bellman operators are built.
--
--   **Formalization Note.** Every norm written $\|\cdot\|$ in the paper except $\|\cdot\|_\infty$ is this $\ell_2$-norm, defined explicitly as `l2norm`, because Mathlib's default norm on `S → ℝ` is the sup norm. The kernel property is the separately published predicate `FoundationsML.ReinforcementLearning.IsTransitionKernel`; the operators are defined for arbitrary arrays.
-- source:
--   Derman, Geist and Mannor, Twice regularized MDPs and the equivalence between robustness and regularization, arXiv:2110.06267v1, p. 2 (Notations: inner product and ℓ2-norm) and p. 3, Section 2 (Discounted MDPs and LP formulation: policies, T^π_(P,r), q-function)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_TwiceRegMDP_RobustReg_MDP

namespace TwiceRegMDP.R2Bellman

open Finset

/-! Finite discounted MDP objects of Derman–Geist–Mannor (arXiv:2110.06267v1, pp. 2–3).
A transition array is `P : S → A → S → ℝ` with `P s a s'` = P(s'|s,a); being a kernel is the
separate hypothesis `FoundationsML.ReinforcementLearning.IsTransitionKernel P` (imported). -/

/-- The ℓ²-norm `‖a‖ = √⟨a, a⟩ = √(∑_z a(z)²)` of a real function on a finite set (p. 2).
Mathlib's own norm on `Z → ℝ` is the sup norm, which is *not* this one. -/
noncomputable def l2norm {Z : Type} [Fintype Z] (a : Z → ℝ) : ℝ :=
  Real.sqrt (∑ z, a z ^ 2)

/-- The q-function of `v`: `q(s,a) = r(s,a) + γ ⟨P(·|s,a), v⟩` (p. 3). -/
noncomputable def qfun {S A : Type} [Fintype S] (γ : ℝ) (P : S → A → S → ℝ)
    (r : S → A → ℝ) (v : S → ℝ) (s : S) (a : A) : ℝ :=
  r s a + γ * ∑ s', P s a s' * v s'

/-- The evaluation Bellman operator `T^π_{(P,r)} v = r^π + γ P^π v` (p. 3):
`[T^π_{(P,r)} v](s) = ∑_a π_s(a) (r(s,a) + γ ∑_{s'} P(s'|s,a) v(s'))`. -/
noncomputable def evalOp {S A : Type} [Fintype S] [Fintype A] (γ : ℝ) (P : S → A → S → ℝ)
    (r : S → A → ℝ) (π : S → A → ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => ∑ a, π s a * qfun γ P r v s a

end TwiceRegMDP.R2Bellman


