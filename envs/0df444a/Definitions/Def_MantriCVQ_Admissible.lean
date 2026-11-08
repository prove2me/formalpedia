-- Prove2me | Definitions.Def_MantriCVQ_Admissible
-- name    : MantriCVQ_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:19.248795+00:00
-- url     : https://prove2.me/theorems/c175cdb8-8653-4190-b25b-4dae0604a767
-- title:
--   Admissible gate sets
-- statement:
--   A finite list $G$ of gates is **admissible** if it contains $H$, $X$ and Toffoli, every gate in it is unitary, and it is closed under inverses, that is, under conjugate transpose. This is the paper's "finite gate set that contains the Hadamard, NOT, and Toffoli gates and is closed under inverses".
--
--   **Formalization Note** The order of the list names the gates in a circuit description.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_MantriCVQ_G0

open QAlgorithms.Complexity

namespace MantriCVQ

/-- A gate set in the sense of §3.1 (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1,
p. 14 (PDF p. 16): "We fix a finite gate set that contains the Hadamard, NOT, and Toffoli gates and
is closed under inverses").

**Formalization Note** A finite set is given as a list, whose order names the gates in a circuit
description. Every gate is unitary, and the inverse of a unitary is its conjugate transpose. -/
def Admissible (G : List Gate) : Prop :=
  hadamardGate ∈ G ∧ notGate ∈ G ∧ toffoliGate ∈ G ∧
    (∀ g ∈ G, g.U ∈ Matrix.unitaryGroup (Bits g.k) ℂ) ∧
    ∀ g ∈ G, (⟨g.k, g.U.conjTranspose⟩ : Gate) ∈ G

end MantriCVQ


