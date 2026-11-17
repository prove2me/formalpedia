-- Prove2me | Definitions.Def_PRUPermLayer_Supplement_IsCliffordGate
-- name    : PRUPermLayer_Supplement_IsCliffordGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:39:24.133253+00:00
-- url     : https://prove2.me/theorems/02ae68cb-eda9-4308-b5fd-3b273f941172
-- title:
--   Single-qubit Clifford gate: $CPC^\dagger\in\{\pm X,\pm Y,\pm Z\}$ for $P\in\{X,Y,Z\}$
-- statement:
--   A single-qubit unitary $C\in U(2)$ is a **Clifford gate** if conjugation by $C$ maps each Pauli matrix to a Pauli matrix up to sign: for every $P\in\{X,Y,Z\}$ there are $Q\in\{X,Y,Z\}$ and $s\in\{+1,-1\}$ with
--   $$C\,P\,C^\dagger=s\,Q.$$
--   Up to global phase there are $24$ such gates, for example the Hadamard gate $H$ and the phase gate $S=\mathrm{diag}(1,i)$. A layer $L=C_1\otimes\cdots\otimes C_n$ consists of Clifford gates if every $C_i$ is one.
--
--   **Formalization Note** Every global phase is allowed ($e^{i\theta}C$ is Clifford iff $C$ is), so this is the full Clifford group in $U(2)$ rather than the 24 phase-free representatives used by the mission's Clifford distribution.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa33ec861a7e9c10d88cfcefc2794b77ad1674c02661c9298c5ba565bcb), §1.1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates

namespace PRUPermLayer.Supplement

/-- A **single-qubit Clifford gate** (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §1.1, p.2 (PDF p.4): "Single-qubit Clifford gates are the
24 gates, up to global phase, that map the Pauli matrices X, Y, Z to Pauli matrices up to sign"):
a unitary `C` on one qubit such that for each `P ∈ {X, Y, Z}` the conjugate `C P C†` equals
`± Q` for some `Q ∈ {X, Y, Z}`.

**Formalization Note** Every global phase is allowed (`c C` is Clifford iff `C` is), so this is
the whole Clifford group of `U(2)`, not the 24 phase-free representatives of the published
`PRUPermLayer.clifford24`. `X, Y, Z` are the published `QAlgorithms.pauliX`, `pauliY`,
`pauliZ`. -/
def IsCliffordGate (C : Matrix.unitaryGroup Bool ℂ) : Prop :=
  ∀ P ∈ ({QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ} : Set (Matrix Bool Bool ℂ)),
    ∃ Q ∈ ({QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ} : Set (Matrix Bool Bool ℂ)),
      ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
        (C : Matrix Bool Bool ℂ) * P * star (C : Matrix Bool Bool ℂ) = s • Q

end PRUPermLayer.Supplement


