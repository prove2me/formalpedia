-- Prove2me | Definitions.Def_FRBSplitting_Weak_Setting
-- name    : FRBSplitting_Weak_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:00.29483+00:00
-- url     : https://prove2.me/theorems/bcef3c63-7342-4b25-8290-1f14d9034855
-- title:
--   (12)–(14), pp. 4–5 — the zero set (A+B)⁻¹(0), weak convergence and weak cluster points, runs of the forward-reflected-backward method (13)
-- statement:
--   The objects of §2 of Malitsky and Tam. Throughout, $H$ is a real inner product space with inner product $\langle\cdot,\cdot\rangle$, $A:H\rightrightarrows H$ is set-valued and $B:H\to H$ is single-valued.
--
--   1. **Zero set.** $(A+B)^{-1}(0)=\{x\in H: 0\in A(x)+B(x)\}=\{x : -B(x)\in A(x)\}$, the solution set of the inclusion (12).
--   2. **Weak convergence.** A sequence $(x_n)$ converges weakly to $\bar x$, written $x_n\rightharpoonup\bar x$, if $\langle x_n,v\rangle\to\langle\bar x,v\rangle$ for every $v\in H$.
--   3. **Sequential weak cluster point.** $p$ is a sequential weak cluster point of $(x_n)$ if some subsequence $(x_{\varphi(n)})$, $\varphi$ strictly increasing, converges weakly to $p$.
--   4. **Runs of the forward-reflected-backward method.** Given a family of maps $J_\gamma:H\to H$ ($J_\gamma$ plays the role of the resolvent $J_{\gamma A}=(I+\gamma A)^{-1}$), step sizes $(\lambda_k)_{k\ge-1}$ and a sequence $(x_k)_{k\ge-1}$, the sequence is a run of (13) if
--
--   $$x_{k+1}=J_{\lambda_k}\big(x_k-\lambda_k B(x_k)-\lambda_{k-1}(B(x_k)-B(x_{k-1}))\big)\qquad\forall k\in\mathbb N.$$
--
--   These are the objects every statement of the mission is phrased in; the operator vocabulary (monotone, maximally monotone, Lipschitz, resolvent) is the published module `ThreeOpSplitting.Accel.MonotoneOperators`.
--
--   **Formalization Note.** Indices are shifted by one: Lean's `x j` is $x_{j-1}$ and `lam j` is $\lambda_{j-1}$, so `x 0` $=x_{-1}$, `x 1` $=x_0$, `lam 0` $=\lambda_{-1}$. The run predicate places no condition on the initial points. Weak convergence is stated through inner products (equivalently, convergence in the weak topology, by the Riesz representation).
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, pp. 4–5, §2 definitions, (12)–(14)

import Mathlib

namespace FRBSplitting.Weak

/-- The zero set `(A + B)⁻¹(0) = {x | 0 ∈ A x + B x} = {x | -B x ∈ A x}` of a set-valued `A` plus a
single-valued `B`. -/
def zeroSet {H : Type*} [NormedAddCommGroup H] (A : H → Set H) (B : H → H) : Set H :=
  {x | -B x ∈ A x}

/-- Weak convergence `x n ⇀ xs` in a real inner product space: `⟪x n, v⟫ → ⟪xs, v⟫` for every `v`. -/
def IsWeakLimit {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (x : ℕ → H) (xs : H) : Prop :=
  ∀ v : H, Filter.Tendsto (fun n => inner ℝ (x n) v) Filter.atTop (nhds (inner ℝ xs v))

/-- `p` is a sequential weak cluster point of `x`: some subsequence converges weakly to `p`. -/
def IsWeakClusterPt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (x : ℕ → H) (p : H) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ IsWeakLimit (x ∘ φ) p

/-- A run of the forward-reflected-backward method (13), indices shifted by one:
`x j` is the paper's `x_{j-1}` and `lam j` is `λ_{j-1}` (so `x 0 = x_{-1}`, `x 1 = x_0`, `lam 0 = λ_{-1}`).
For every `k`, `x_{k+1} = J_{λ_k A}(x_k - λ_k B(x_k) - λ_{k-1}(B(x_k) - B(x_{k-1})))`. -/
def IsFRBRun {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : ℝ → H → H) (B : H → H) (lam : ℕ → ℝ) (x : ℕ → H) : Prop :=
  ∀ k : ℕ, x (k + 2) = J (lam (k + 1))
    (x (k + 1) - lam (k + 1) • B (x (k + 1)) - lam k • (B (x (k + 1)) - B (x k)))

end FRBSplitting.Weak


