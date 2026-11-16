-- Prove2me | Definitions.Def_ArbLindbladLearn_Supplement_indNorm
-- name    : ArbLindbladLearn_Supplement_indNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:16:53.799237+00:00
-- url     : https://prove2.me/theorems/7e78025a-18ed-4632-9cdc-49248e3b531d
-- title:
--   Induced norm $\|\Phi\|_{\infty\to\infty}$ of a superoperator
-- statement:
--   For a linear map $\Phi$ on the operators of $n$ qubits, the induced norm with respect to the operator (spectral) norm is
--   $$\|\Phi\|_{\infty\to\infty}=\sup_{A\ne0}\frac{\|\Phi(A)\|_\infty}{\|A\|_\infty},$$
--   equivalently the least $L\ge0$ with $\|\Phi(A)\|_\infty\le L\|A\|_\infty$ for every operator $A$.
--
--   It measures the strength of a generator in the Heisenberg picture, $\|\mathcal L^\dagger\|_{\infty\to\infty}$, and of its parts $\|\mathcal L_S^\dagger\|_{\infty\to\infty}$ in the local strength.
--
--   **Formalization Note** Defined as the infimum of the admissible constants $L\ge0$, with the published spectral norm `opNorm`. The set is nonempty (finite dimension) and bounded below, so the infimum is the norm itself.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), §2.1, pp.11–12

import Mathlib
import Definitions.Def_ArbLindbladLearn_opNorm

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn.Supplement

open LindbladTolerant.Testing
open ArbLindbladLearn

/-- The induced norm `‖Φ‖_{∞→∞} = sup_{A ≠ 0} ‖Φ(A)‖_∞ / ‖A‖_∞` of a superoperator on `n` qubits
(§2.1, pp.11–12, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…)), as the least
`L ≥ 0` with `‖Φ(A)‖_∞ ≤ L‖A‖_∞` for every operator `A`.

**Formalization Note** `‖·‖_∞` is the published spectral norm `opNorm`. The set of admissible `L` is
nonempty (a linear map on a finite-dimensional space is bounded) and bounded below by `0`, so the
real `sInf` is the induced norm itself and never a junk value. -/
def indNorm {n : ℕ} (Φ : Super (Qubits n) (Qubits n)) : ℝ :=
  sInf {L : ℝ | 0 ≤ L ∧ ∀ A : Op (Qubits n), opNorm (applySuper Φ A) ≤ L * opNorm A}

end ArbLindbladLearn.Supplement


