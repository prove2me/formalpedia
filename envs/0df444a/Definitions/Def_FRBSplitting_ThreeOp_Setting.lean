-- Prove2me | Definitions.Def_FRBSplitting_ThreeOp_Setting
-- name    : FRBSplitting_ThreeOp_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:05.737484+00:00
-- url     : https://prove2.me/theorems/da6c61db-93e3-4336-b4e1-57916eefadab
-- title:
--   (47), p. 15 — runs of the three-operator forward-reflected-backward scheme (47)
-- statement:
--   The objects of §5 of Malitsky and Tam. Throughout, $H$ is a real inner product space with inner product $\langle\cdot,\cdot\rangle$, $A:H\rightrightarrows H$ is set-valued and $B, C:H\to H$ are single-valued.
--
--   1. **Zero set.** For a set-valued $A$ and a single-valued $M$, $(A+M)^{-1}(0)=\{x\in H: 0\in A(x)+M(x)\}=\{x : -M(x)\in A(x)\}$. The solution set of the three-operator inclusion (46) is obtained with $M=B+C$:
--   $$(A+B+C)^{-1}(0)=\{x\in H : -(B+C)(x)\in A(x)\}.$$
--   2. **Weak convergence.** A sequence $(x_n)$ converges weakly to $\bar x$, written $x_n\rightharpoonup\bar x$, if $\langle x_n,v\rangle\to\langle\bar x,v\rangle$ for every $v\in H$.
--   3. **Sequential weak cluster point.** $p$ is a sequential weak cluster point of $(x_n)$ if some subsequence $(x_{\varphi(n)})$, $\varphi$ strictly increasing, converges weakly to $p$.
--   4. **Runs of the three-operator scheme (47).** Given a family of maps $J_\gamma:H\to H$ ($J_\gamma$ plays the role of the resolvent $J_{\gamma A}=(I+\gamma A)^{-1}$), a constant step size $\lambda$ and a sequence $(x_k)_{k\ge-1}$, the sequence is a run of (47) if
--
--   $$x_{k+1}=J_{\lambda}\big(x_k-2\lambda B(x_k)+\lambda B(x_{k-1})-\lambda C(x_k)\big)\qquad\forall k\in\mathbb N.$$
--
--   The operator $B$ enters through a reflected forward step, the operator $C$ through a plain forward step. These are the objects every statement of the mission is phrased in; the operator vocabulary (monotone, maximally monotone, Lipschitz, cocoercive, resolvent) is the published module `ThreeOpSplitting.Accel.MonotoneOperators`.
--
--   **Formalization Note.** Indices are shifted by one: Lean's `x j` is $x_{j-1}$, so `x 0` $=x_{-1}$ and `x 1` $=x_0$. The run predicate places no condition on the two initial points. Weak convergence is stated through inner products (equivalently, convergence in the weak topology, by the Riesz representation). The bodies of `zeroSet`, `IsWeakLimit` and `IsWeakClusterPt` are identical to those of the other missions of this series.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 15, §5, (46)–(47); zero set and weak convergence as on p. 4

import Mathlib
import Definitions.Def_FRBSplitting_Weak_Setting

namespace FRBSplitting.ThreeOp

/-- A run of the three-operator scheme (47) with constant step `lam`, index shift of the series
(`x j` is x_{j−1}): `x_{k+1} = J_{λA}(x_k − 2λB(x_k) + λB(x_{k−1}) − λC(x_k))` for every `k`. -/
def IsThreeOpRun {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : ℝ → H → H) (B C : H → H) (lam : ℝ) (x : ℕ → H) : Prop :=
  ∀ k : ℕ, x (k + 2) = J lam (x (k + 1) - (2 * lam) • B (x (k + 1)) + lam • B (x k) - lam • C (x (k + 1)))

end FRBSplitting.ThreeOp


