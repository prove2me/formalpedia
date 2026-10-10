-- Prove2me | Definitions.Def_FRBSplitting_Linear_Setting
-- name    : FRBSplitting_Linear_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:03.506005+00:00
-- url     : https://prove2.me/theorems/2cb3a964-78e9-44ef-82e6-49751f479606
-- title:
--   Proof of Theorem 2.9, p. 9 — the energies a_k, b_k (the zero set and the run predicate (13) come from the shared FRBSplitting.Weak.Setting)
-- statement:
--   The objects of §2 and §2.1 of Malitsky and Tam. Throughout, $H$ is a real inner product space with inner product $\langle\cdot,\cdot\rangle$, $A:H\rightrightarrows H$ is set-valued and $B:H\to H$ is single-valued.
--
--   Items 1 and 2 below are declared in the shared module `FRBSplitting.Weak.Setting` (as `FRBSplitting.Weak.zeroSet` and `FRBSplitting.Weak.IsFRBRun`), which this file imports; item 3 is declared here.
--
--   1. **Zero set.** $(A+B)^{-1}(0)=\{x\in H: 0\in A(x)+B(x)\}=\{x : -B(x)\in A(x)\}$, the solution set of the inclusion (12).
--   2. **Runs of the forward-reflected-backward method.** Given a family of maps $J_\gamma:H\to H$ ($J_\gamma$ plays the role of the resolvent $J_{\gamma A}=(I+\gamma A)^{-1}$), step sizes $(\lambda_k)_{k\ge-1}$ and a sequence $(x_k)_{k\ge-1}$, the sequence is a run of (13) if
--   $$x_{k+1}=J_{\lambda_k}\big(x_k-\lambda_k B(x_k)-\lambda_{k-1}(B(x_k)-B(x_{k-1}))\big)\qquad\forall k\in\mathbb N.$$
--   With a constant step $\lambda_k=\lambda$ this is (15): $x_{k+1}=J_{\lambda}(x_k-2\lambda B(x_k)+\lambda B(x_{k-1}))$.
--   3. **Energies.** For a sequence $(x_k)_{k\ge-1}$, a point $x\in H$ and $\lambda\in\mathbb R$, for $k\ge0$,
--   $$a_k=\tfrac12\|x_k-x\|^2,\qquad b_k=\tfrac12\|x_k-x\|^2+2\lambda\langle B(x_k)-B(x_{k-1}),\,x-x_k\rangle+\tfrac12\|x_k-x_{k-1}\|^2 .$$
--
--   The run predicate is the method analysed in Theorem 2.9; $a_k$ and $b_k$ are the two sequences whose sum the proof of Theorem 2.9 shows to decrease geometrically. The operator vocabulary (monotone, strongly monotone, maximally monotone, Lipschitz, resolvent) is the published module `ThreeOpSplitting.Accel.MonotoneOperators`.
--
--   **Formalization Note.** Indices are shifted by one: Lean's `x j` is $x_{j-1}$ and `lam j` is $\lambda_{j-1}$, so `x 0` $=x_{-1}$, `x 1` $=x_0$, `lam 0` $=\lambda_{-1}$. The run predicate places no condition on the initial points. Accordingly `aSeq x xs k` and `bSeq B lam x xs k` are the paper's $a_k$, $b_k$, built from `x (k+1)` $=x_k$ and `x k` $=x_{k-1}$.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, pp. 4 and 9, §2 (12)–(15) and the definitions of a_k, b_k in the proof of Theorem 2.9

import Mathlib
import Definitions.Def_FRBSplitting_Weak_Setting

namespace FRBSplitting.Linear

/-- a_k := ½‖x_k − x‖² (p. 9), with `x (k+1)` the paper's `x_k`. -/
noncomputable def aSeq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : ℕ → H) (xs : H) (k : ℕ) : ℝ :=
  1 / 2 * ‖x (k + 1) - xs‖ ^ 2

/-- b_k := ½‖x_k − x‖² + 2λ⟨B(x_k) − B(x_{k−1}), x − x_k⟩ + ½‖x_k − x_{k−1}‖² (p. 9),
with `x (k+1)` the paper's `x_k` and `x k` the paper's `x_{k−1}`. -/
noncomputable def bSeq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H → H) (lam : ℝ) (x : ℕ → H) (xs : H) (k : ℕ) : ℝ :=
  1 / 2 * ‖x (k + 1) - xs‖ ^ 2 + 2 * lam * inner ℝ (B (x (k + 1)) - B (x k)) (xs - x (k + 1))
    + 1 / 2 * ‖x (k + 1) - x k‖ ^ 2

end FRBSplitting.Linear


