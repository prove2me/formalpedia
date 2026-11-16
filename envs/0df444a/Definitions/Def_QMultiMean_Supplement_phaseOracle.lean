-- Prove2me | Definitions.Def_QMultiMean_Supplement_phaseOracle
-- name    : QMultiMean_Supplement_phaseOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:13:30.056037+00:00
-- url     : https://prove2.me/theorems/7ac09d93-5f91-406e-955b-83ca3e035140
-- title:
--   Phase oracle $\mathcal P_X:|\omega\rangle|j\rangle\mapsto e^{iX(\omega)_j}|\omega\rangle|j\rangle$ (Definition 2.7)
-- statement:
--   Let $X:\Omega\to\mathbb R^d$ be a finite random variable and $\mathcal H_\Omega$ the Hilbert space with basis $\{|\omega\rangle\}_{\omega\in\Omega}$. The **phase oracle** of $X$ is the unitary $\mathcal P_X$ on $\mathcal H_\Omega\otimes\mathbb C^d$ with
--   $$\mathcal P_X:|\omega\rangle|j\rangle\mapsto e^{iX(\omega)_j}|\omega\rangle|j\rangle\qquad(\omega\in\Omega,\ j\in[d]).$$
--
--   It encodes the coordinates of $X(\omega)$ in phases rather than in a register, and is the input model of Section 4 of the paper, together with the quantum experiment $U_{\mathbb P}$.
--
--   **Formalization Note** $\Omega=\{0,\dots,N\}$ as in the published quantum experiment, and $[d]=\{0,\dots,d-1\}$. Since the definition prescribes the image of every basis state, $\mathcal P_X$ is the diagonal matrix with entries $e^{iX(\omega)_j}$.
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.7, Definition 2.7

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable

set_option autoImplicit false

namespace QMultiMean.Supplement

open QMultiMean

/-- The **phase oracle** `P_X` of a finite random variable `X : Ω → ℝ^d` (Cornelissen, Hamoudi,
Jerbi, *Near-Optimal Quantum Algorithms for Multivariate Mean Estimation*, arXiv:2111.09787v2,
Definition 2.7, p.7): the unitary on `H_Ω ⊗ ℂ^d` with `P_X : |ω⟩|j⟩ ↦ e^{i X(ω)_j} |ω⟩|j⟩` for all
`ω ∈ Ω` and `j ∈ [d]`.

**Formalization Note.** `Ω = Fin (N+1)` (as in the published `QMultiMean.IsQuantumExperiment`) and
`[d] = Fin d`. Definition 2.7 prescribes the image of every basis state, so the phase oracle is
unique: it is the diagonal matrix with entries `e^{i X(ω)_j}`. -/
noncomputable def phaseOracle {N d : ℕ} (X : Fin (N + 1) → Vec d) :
    Matrix (Fin (N + 1) × Fin d) (Fin (N + 1) × Fin d) ℂ :=
  Matrix.diagonal (fun q => Complex.exp (Complex.I * ((X q.1 q.2 : ℝ) : ℂ)))

end QMultiMean.Supplement


