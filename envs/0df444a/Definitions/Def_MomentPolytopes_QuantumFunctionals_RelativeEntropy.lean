-- Prove2me | Definitions.Def_MomentPolytopes_QuantumFunctionals_RelativeEntropy
-- name    : MomentPolytopes_QuantumFunctionals_RelativeEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:01:48.58487+00:00
-- url     : https://prove2.me/theorems/15c5cc80-7dfd-44a3-bde0-ae87a598dd03
-- title:
--   Quantum relative entropy D(A‖B) of PSD matrices and completely positive trace-preserving maps
-- statement:
--   For positive-semidefinite matrices $A,B$ (of any trace),
--   $$D(A\|B)=\begin{cases}\operatorname{tr}[A\log A]-\operatorname{tr}[A\log B]&\text{if }A,B\succeq0\text{ and }\operatorname{im}A\subseteq\operatorname{im}B,\\ \infty&\text{otherwise,}\end{cases}$$
--   where the traces are taken on the images (the logarithm is only applied on the supports).
--
--   A linear map $\Lambda$ from $n\times n$ to $n'\times n'$ complex matrices is **completely positive and trace preserving (CPTP)** if $\operatorname{tr}\Lambda(X)=\operatorname{tr}X$ for all $X$ and $\Lambda\otimes\mathrm{id}_k$ maps positive-semidefinite matrices to positive-semidefinite matrices for every $k\in\mathbb N$. The partial trace is an example.
--
--   **Formalization Note** $D$ is `EReal`-valued, $\infty=\top$. The logarithm is `cfc Real.log`, which is $0$ on the kernel, so the traces equal the traces on the images. The index sets are arbitrary finite types.
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), p. 56, the definition before eq. (7.8), with fn. 43

import Mathlib

set_option autoImplicit false

open scoped ComplexOrder Matrix

namespace MomentPolytopes.QuantumFunctionals

/-- Quantum relative entropy (p. 56, with fn. 43), valued in `ℝ ∪ {∞}` (encoded in `EReal`):
`D(A‖B) = tr[A log A] − tr[A log B]` if `A, B ⪰ 0` and `im A ⊆ im B`, and `∞` otherwise.
`log` is the functional calculus of `Real.log`, which is `0` on the kernel, so both traces are
the traces on the image as in fn. 43. `A`, `B` need not have trace one. -/
noncomputable def relEntropy {m : Type} [Fintype m] [DecidableEq m] (A B : Matrix m m ℂ) :
    EReal :=
  haveI := Classical.propDecidable
  if A.PosSemidef ∧ B.PosSemidef ∧ LinearMap.range A.mulVecLin ≤ LinearMap.range B.mulVecLin then
    (((A * cfc Real.log A).trace - (A * cfc Real.log B).trace).re : EReal)
  else ⊤

/-- The ampliation `Λ ⊗ id_k` of a linear map on matrices, acting blockwise on
`Matrix (m × Fin k) (m × Fin k) ℂ`. -/
def ampliate {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (Λ : Matrix m m ℂ →ₗ[ℂ] Matrix m' m' ℂ) (k : ℕ) (M : Matrix (m × Fin k) (m × Fin k) ℂ) :
    Matrix (m' × Fin k) (m' × Fin k) ℂ :=
  fun x y => Λ (fun i j => M (i, x.2) (j, y.2)) x.1 y.1

/-- `Λ` is completely positive and trace preserving: `Λ ⊗ id_k` maps positive-semidefinite
matrices to positive-semidefinite matrices for every ancilla dimension `k`, and
`tr Λ(X) = tr X` for all `X`. -/
def IsCPTP {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (Λ : Matrix m m ℂ →ₗ[ℂ] Matrix m' m' ℂ) : Prop :=
  (∀ X, (Λ X).trace = X.trace) ∧
    ∀ (k : ℕ) (M : Matrix (m × Fin k) (m × Fin k) ℂ), M.PosSemidef → (ampliate Λ k M).PosSemidef

end MomentPolytopes.QuantumFunctionals


