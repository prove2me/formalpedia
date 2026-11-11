-- Prove2me | Definitions.Def_QVolTransducer_ampState
-- name    : QVolTransducer_ampState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:00.238066+00:00
-- url     : https://prove2.me/theorems/63b0dcc0-96df-4687-acdf-b8a8679a89f2
-- title:
--   Amplitude-amplification states $|\psi\rangle=|\psi_0\rangle|0\rangle+|\psi_1\rangle|1\rangle$ and $|\bar\psi\rangle$
-- statement:
--   For vectors $|\psi_0\rangle,|\psi_1\rangle\in\mathcal V$ the two states of $\mathcal V\otimes\mathbb C^2$ used in amplitude amplification are
--
--   $$
--   |\psi\rangle=|\psi_0\rangle|0\rangle+|\psi_1\rangle|1\rangle,
--   \qquad
--   |\bar\psi\rangle=\frac{\||\psi_1\rangle\|}{\||\psi_0\rangle\|}|\psi_0\rangle|0\rangle-\frac{\||\psi_0\rangle\|}{\||\psi_1\rangle\|}|\psi_1\rangle|1\rangle .
--   $$
--
--   When both components are nonzero, $|\bar\psi\rangle$ is orthogonal to $|\psi\rangle$. These are the states on which the reflection transducer of Corollary 3.4 is evaluated.
--
--   **Formalization Note** $\mathbb C^2$ is indexed by `Fin 2` and $|\psi_i\rangle|i\rangle$ is the tensor product with the basis vector $|i\rangle$.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Corollary 3.4, pp.20–21 (PDF pp.22–23)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

namespace QVolTransducer

open QAlgorithms

/-- The state `|ψ⟩ = |ψ_0⟩|0⟩ + |ψ_1⟩|1⟩ ∈ V ⊗ ℂ²` of amplitude amplification (Cornelissen, Apers,
Gribling, *Improved quantum volume estimation with transducers and amortized quantum walks*,
arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Corollary 3.4, pp.20–21), with
`ℂ²` indexed by `Fin 2`. -/
noncomputable def ampState {V : Type*} (ψ0 ψ1 : EuclideanSpace ℂ V) :
    EuclideanSpace ℂ (V × Fin 2) :=
  tensorVec ψ0 (ket 0) + tensorVec ψ1 (ket 1)

/-- The companion state
`|ψ̄⟩ = (‖|ψ_1⟩‖/‖|ψ_0⟩‖) |ψ_0⟩|0⟩ − (‖|ψ_0⟩‖/‖|ψ_1⟩‖) |ψ_1⟩|1⟩` of Corollary 3.4
(arXiv:2609.40217, p.20), orthogonal to `|ψ⟩` when both components are nonzero. -/
noncomputable def ampPerp {V : Type*} [Fintype V] (ψ0 ψ1 : EuclideanSpace ℂ V) :
    EuclideanSpace ℂ (V × Fin 2) :=
  ((‖ψ1‖ / ‖ψ0‖ : ℝ) : ℂ) • tensorVec ψ0 (ket 0) - ((‖ψ0‖ / ‖ψ1‖ : ℝ) : ℂ) • tensorVec ψ1 (ket 1)

end QVolTransducer


