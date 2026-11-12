-- Prove2me | Definitions.Def_QPVEntanglement_bb84TestProb
-- name    : QPVEntanglement_bb84TestProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:33:52.769682+00:00
-- url     : https://prove2.me/theorems/c670115f-8262-422c-b5fb-1b591dccf1d1
-- title:
--   Success probability of the random two-qubit BB84 test
-- statement:
--   For a two-qubit state $\rho$, the random BB84 test chooses the $ZZ$ or the $XX$ basis with probability $\tfrac12$ each, measures both qubits in it and passes iff the outcomes agree:
--
--   $$p(\rho)=\tfrac12\,\mathrm{tr}(\Pi_Z\rho)+\tfrac12\,\mathrm{tr}(\Pi_X\rho),\qquad \Pi_Z=|00\rangle\langle00|+|11\rangle\langle11|,\quad \Pi_X=(H\otimes H)\,\Pi_Z\,(H\otimes H).$$
--
--   It is the quantity Lemma 4 converts into a Bell fidelity.
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Lemma 4, p.32; proof of Lemma 4, eq. (59), p.64

import Mathlib
import Definitions.Def_QPVEntanglement_Draw

set_option autoImplicit false

open scoped Matrix

namespace QPVEntanglement

/-- Pass projector of the `ZZ` test: both qubits measured in the computational basis, outcomes
agree: `Π_Z = |00⟩⟨00| + |11⟩⟨11|` (proof of Lemma 4, p.64). -/
noncomputable def piZZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal fun p => if p.1 = p.2 then 1 else 0

/-- Pass projector of the `XX` test: both qubits measured in the Hadamard basis, outcomes
agree: `Π_X = |++⟩⟨++| + |−−⟩⟨−−| = (H⊗H) Π_Z (H⊗H)` (proof of Lemma 4, p.64). -/
noncomputable def piXX : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker hadamard hadamard * piZZ * Matrix.kronecker hadamard hadamard

/-- **Success probability of the random two-qubit BB84 test** (Lemma 4, p.32; proof p.64).
Behera–Goyal, arXiv:2609.39234 (sha256 bdf2928d…), Lemma 4, pp.32–33, and eq. (59), p.64:
a basis `ZZ` or `XX` is chosen with probability `½` each, both qubits are measured in it, and
the test passes iff the outcomes agree:
`p = ½ tr(Π_Z ρ) + ½ tr(Π_X ρ)`. -/
noncomputable def bb84TestProb (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  (1 / 2 : ℝ) * (piZZ * ρ).trace.re + (1 / 2 : ℝ) * (piXX * ρ).trace.re

end QPVEntanglement


