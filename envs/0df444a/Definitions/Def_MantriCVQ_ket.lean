-- Prove2me | Definitions.Def_MantriCVQ_ket
-- name    : MantriCVQ_ket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:28.66668+00:00
-- url     : https://prove2.me/theorems/4dd12ff5-b3d6-4343-966d-0250154fb571
-- title:
--   Basis states and the probability of measuring one
-- statement:
--   $|s\rangle$ is the computational basis state on $N$ wires read in order, and the probability that measuring a wire of $\psi$ gives $1$ is $\sum_{y:\,y_{\mathrm{out}}=1}|\psi(y)|^2$.
--
--   **Formalization Note** If $s$ does not have length $N$, the vector is zero. Every use in this mission passes a string of length $N$.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace MantriCVQ

/-- The computational basis state `|s⟩` on `N` wires, where the wires are read in order (Mantri,
arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)).

**Formalization Note** If `s` does not have length `N` this is the zero vector; every use in this
mission passes a string of length `N`. -/
noncomputable def ket (N : ℕ) (s : Str) : QState N :=
  fun y => if List.ofFn y = s then 1 else 0

/-- The probability that measuring the wire `out` of the state `ψ` gives `1`. -/
noncomputable def probOne {N : ℕ} (ψ : QState N) (out : Fin N) : ℝ :=
  ∑ y : Bits N, if y out = true then ‖ψ y‖ ^ 2 else 0

end MantriCVQ


