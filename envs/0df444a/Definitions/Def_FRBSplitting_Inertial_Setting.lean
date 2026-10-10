-- Prove2me | Definitions.Def_FRBSplitting_Inertial_Setting
-- name    : FRBSplitting_Inertial_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:42:56.266269+00:00
-- url     : https://prove2.me/theorems/30762e66-a884-4bb2-8a5f-77bfbe42e481
-- title:
--   (34)–(35), p. 11 — the shifted operator B − ρI and runs of the relaxed inertial scheme (34)
-- statement:
--   The objects of §4 of Malitsky and Tam. Throughout, $H$ is a real inner product space with inner product $\langle\cdot,\cdot\rangle$, $A:H\rightrightarrows H$ is set-valued and $B:H\to H$ is single-valued.
--
--   1. **Shifted operator.** For $c\in\mathbb R$, $B-cI$ is the map $y\mapsto B(y)-c\,y$. With $c=\alpha/\lambda$ this is the operator $B'$ of (35).
--   2. **Runs of the relaxed inertial scheme (34).** Given a family of maps $J_\gamma:H\to H$ ($J_\gamma$ plays the role of the resolvent $J_{\gamma A}=(I+\gamma A)^{-1}$), parameters $\alpha,\beta,\lambda\in\mathbb R$ and sequences $(x_k)_{k\ge-1}$, $(z_k)_{k\ge1}$, the pair is a run of (34) if for every $k\in\mathbb N$
--
--   $$z_{k+1}=J_{\lambda}\Big(x_k-\lambda B(x_k)-\frac{\lambda}{\beta}\big(B(x_k)-B(x_{k-1})\big)+\frac{\alpha}{\beta}(x_k-x_{k-1})\Big),\qquad x_{k+1}=(1-\beta)x_k+\beta z_{k+1}.$$
--
--   Together with the zero set $(A+B)^{-1}(0)=\{x : -B(x)\in A(x)\}$ and weak convergence (via inner products) of the shared module `FRBSplitting.Weak.Setting`, these are the objects every statement of the mission is phrased in; the operator vocabulary (monotone, maximally monotone, Lipschitz, cocoercive, resolvent) is the published module `ThreeOpSplitting.Accel.MonotoneOperators`. Rewriting the resolvent argument with $B'=B-(\alpha/\lambda)I$ gives the equivalent form (35).
--
--   **Formalization Note.** Indices are shifted by one: Lean's `x j` is $x_{j-1}$ and `z j` is $z_{j-1}$, so `x 0` $=x_{-1}$ and `x 1` $=x_0$; the values `z 0`, `z 1` are unconstrained and no statement mentions them. The run predicate places no condition on the initial points. The resolvent is supplied as a family `J` with a separate hypothesis that each `J γ`, $\gamma>0$, is the resolvent of $\gamma A$; for maximally monotone $A$ such a family exists and is unique (Minty).
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 11, §4, (34)–(35); p. 4, (12)

import Mathlib
import Definitions.Def_FRBSplitting_Weak_Setting

namespace FRBSplitting.Inertial

/-- The shifted operator `B′ := B − c I` of (35) and Lemma 4.1. -/
def shiftOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (B : H → H) (c : ℝ) : H → H :=
  fun y => B y - c • y

/-- A run of the relaxed inertial scheme (34) with parameters `α β lam`, index shift of the series:
`x j` is x_{j−1}, `z j` is z_{j−1} (`z 0`, `z 1` are unused). For every `k`,
`z_{k+1} = J_{λA}(x_k − λB(x_k) − (λ/β)(B(x_k) − B(x_{k−1})) + (α/β)(x_k − x_{k−1}))` and
`x_{k+1} = (1 − β)x_k + βz_{k+1}`. -/
def IsRelaxedInertialRun {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : ℝ → H → H) (B : H → H) (α β lam : ℝ) (x z : ℕ → H) : Prop :=
  ∀ k : ℕ, z (k + 2) = J lam (x (k + 1) - lam • B (x (k + 1))
      - (lam / β) • (B (x (k + 1)) - B (x k)) + (α / β) • (x (k + 1) - x k)) ∧
    x (k + 2) = (1 - β) • x (k + 1) + β • z (k + 2)

end FRBSplitting.Inertial


