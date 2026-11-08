-- Prove2me | Definitions.Def_MantriCVQ_G0
-- name    : MantriCVQ_G0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:17.371233+00:00
-- url     : https://prove2.me/theorems/b549b9ce-58f9-48e0-8343-048c993049b1
-- title:
--   The gate set $\{H, X, \mathrm{Toffoli}\}$
-- statement:
--   The Hadamard gate $H$, the NOT gate $X$, and the Toffoli gate $|a,b,c\rangle\mapsto|a,b,c\oplus ab\rangle$ form the list $G_0$. Each of the three gates is its own inverse, so $G_0$ is the smallest finite gate set of the kind fixed in §3.1 of the paper. The goal theorem uses this set.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_MantriCVQ_Gate

open QAlgorithms.Complexity

namespace MantriCVQ

/-- The Hadamard gate as a one-qubit `MantriCVQ.Gate` (the matrix `hMat` of the shared layer). -/
noncomputable def hadamardGate : Gate := ⟨1, fun a b => hMat (a 0) (b 0)⟩

/-- The NOT gate as a one-qubit `MantriCVQ.Gate` (the matrix `xMat` of the shared layer). -/
noncomputable def notGate : Gate := ⟨1, fun a b => xMat (a 0) (b 0)⟩

/-- The Toffoli gate `|a, b, c⟩ ↦ |a, b, c ⊕ ab⟩` as a three-qubit `MantriCVQ.Gate`. -/
noncomputable def toffoliGate : Gate :=
  ⟨3, fun a b => if a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = xor (b 2) (b 0 && b 1) then 1 else 0⟩

/-- The smallest gate set of §3.1 (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1,
p. 14 (PDF p. 16): "a finite gate set that contains the Hadamard, NOT, and Toffoli gates and is
closed under inverses"): `{H, X, Toffoli}`. Each of the three is its own inverse. -/
noncomputable def G0 : List Gate := [hadamardGate, notGate, toffoliGate]

end MantriCVQ


