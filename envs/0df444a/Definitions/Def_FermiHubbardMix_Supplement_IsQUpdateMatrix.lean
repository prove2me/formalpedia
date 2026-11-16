-- Prove2me | Definitions.Def_FermiHubbardMix_Supplement_IsQUpdateMatrix
-- name    : FermiHubbardMix_Supplement_IsQUpdateMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:03:58.160594+00:00
-- url     : https://prove2.me/theorems/e849e163-1524-4871-abd4-2f48738c34bc
-- title:
--   Qubit transport plans, cost vectors and update matrices
-- statement:
--   1. **Transport plan.** For a traceless Hermitian $n$-qubit operator $X$, a family $(X_i)_{i\in[n]}$ is a transport plan of $X$ if $X=\sum_iX_i$ and every $X_i$ is Hermitian, traceless and satisfies $\mathrm{tr}_i(X_i)=0$. Its **cost vector** is $x\in\mathbb R^n$ with $x_i=\tfrac12\|X_i\|_1$ (trace norm).
--   2. **Update matrix.** Let $\Phi$ be a trace-preserving linear map taking Hermitian operators to Hermitian operators. A matrix $Q\in\mathbb R^{n\times n}$ is an update matrix of $\Phi$ if for every traceless Hermitian $X$ and every transport plan of $X$ with cost vector $x$, the operator $\Phi(X)$ has a transport plan with cost vector $y$ satisfying $y\le Qx$ entrywise.
--
--   Update matrices turn one step of a quantum dynamics into a linear recursion on nonnegative cost vectors; they drive the qubit mixing proof.
--
--   **Formalization Note** The statement "$\Phi$ has update matrix $Q$" includes the standing hypothesis that $\Phi$ preserves Hermiticity and the trace. The cost is the published `FermiHubbardMix.planCost` (trace norm `WildeQIT.traceNorm`). There is no parity condition, unlike the base mission's fermionic transport plans.
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Definition 7.1, p.26; Definition 7.2, p.26; §4, p.15

import Mathlib
import Definitions.Def_FermiHubbardMix_Supplement_IsSuppOn
import Definitions.Def_FermiHubbardMix_w1
import Definitions.Def_WildeQIT_traceNorm
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix.Supplement

/-- **Definition 7.1 (Transport plan)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard
Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.26): for a traceless Hermitian `n`-qubit
operator `X`, `(X_i)_{i ∈ [n]}` is a transport plan of `X` if `X = ∑_i X_i` and every `X_i` is Hermitian,
traceless, and has `tr_i(X_i) = 0` (partial trace over qubit `i`). Its cost vector is
`x_i = ½‖X_i‖₁`, the published `FermiHubbardMix.planCost` (trace norm `WildeQIT.traceNorm`).

**Formalization Note** No parity condition: the base mission's `FermiHubbardMix.IsTransportPlan` is
the fermionic Definition 12.8 and is not used for qubits. -/
def IsQTransportPlan {n : ℕ} (X : Op n) (Xs : Fin n → Op n) : Prop :=
  ∑ i, Xs i = X ∧ ∀ i, (Xs i).IsHermitian ∧ (Xs i).trace = 0 ∧ ptrQ {i} (Xs i) = 0

/-- The standing hypothesis of Definition 7.2 (arXiv:2604.08408, held version sha256 055b8f8f…,
p.26, with the convention of §4, p.15, that a "linear map" takes Hermitian matrices to Hermitian
matrices): `Φ` preserves Hermiticity and the trace. -/
def PreservesHermTrace {n : ℕ} (Φ : Op n →ₗ[ℂ] Op n) : Prop :=
  ∀ X : Op n, (X.IsHermitian → (Φ X).IsHermitian) ∧ (Φ X).trace = X.trace

/-- **Definition 7.2 (Update matrix)** (arXiv:2604.08408, held version sha256 055b8f8f…, p.26): for
a trace-preserving linear map `Φ`, `Q ∈ ℝ^{n×n}` is an update matrix of `Φ` if for every traceless
Hermitian `X` and every transport plan `(X_i)_i` of `X`, `Φ(X)` has a transport plan with cost vector
`y ≤_v Qx`, `x` the cost vector of `(X_i)_i`.

**Formalization Note** "`Φ` has update matrix `Q`" asserts the standing hypothesis on `Φ`
(`PreservesHermTrace`) together with the cost condition; the quantifiers are ∀ plan of `X`, ∃ plan of
`Φ(X)`. -/
def IsQUpdateMatrix {n : ℕ} (Φ : Op n →ₗ[ℂ] Op n) (Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  PreservesHermTrace Φ ∧
  ∀ X : Op n, X.IsHermitian → X.trace = 0 →
    ∀ Xs : Fin n → Op n, IsQTransportPlan X Xs →
      ∃ Ys : Fin n → Op n, IsQTransportPlan (Φ X) Ys ∧
        ∀ i, planCost Ys i ≤ ∑ j, Q i j * planCost Xs j

end FermiHubbardMix.Supplement


