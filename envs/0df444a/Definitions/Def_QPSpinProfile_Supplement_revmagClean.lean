-- Prove2me | Definitions.Def_QPSpinProfile_Supplement_revmagClean
-- name    : QPSpinProfile_Supplement_revmagClean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:32:36.947451+00:00
-- url     : https://prove2.me/theorems/48db955c-c217-45c7-979a-09eb870bfe56
-- title:
--   Clean-ancilla reverse magic $\mathsf{revmag}^{[D],\mathrm{clean}}_n$ (Definition 4.11)
-- statement:
--   Fix $D \ge 1$. The class $\mathsf{revmag}^{[D],\mathrm{clean}}_n$ consists of the pure $n$-qubit states $|\psi\rangle$ for which there exist an integer $r \ge 0$, a Clifford $C \in \mathsf{cliff}_{n+r}$ and a circuit $Q \in \mathrm{Circ}[D]_{n+r}$ on $n+r$ qubits such that
--   $$
--   C Q\, |0^{n+r}\rangle = |\psi\rangle\, |0^r\rangle .
--   $$
--   The shallow circuit acts first and the Clifford after it (reverse magic). The $r$ ancillary qubits are the last $r$ qubits, and they must be returned **exactly** to $|0^r\rangle$ (clean ancillas): they are not traced out. The number $r$ of ancillas is arbitrary.
--
--   The class is the object of Theorem 4.16, which shows that a single round of reverse magic at fixed depth cannot reach the ground-state energy of the dense quantum $p$-spin model, however many clean ancillas it uses.
--
--   **Formalization Note** The class is a set of $2^n\times 2^n$ density matrices: a pure state $|\psi\rangle$ enters as $|\psi\rangle\langle\psi|$ with $\psi$ a unit vector. Qubits are labelled $0,\dots,n+r-1$ with the system first and the ancillas last, and $|0^M\rangle$ is the all-zeros basis vector. The class contains $|0^n\rangle\langle 0^n|$ ($r=0$, $C=Q=I$), so it is nonempty.
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), Definition 4.11, p.59 (PDF p.62); cliff_M p.45 (PDF p.48); Circ[D] Definition 3.7, p.39 (PDF p.42)

import Mathlib
import Definitions.Def_QPSpinProfile_Supplement_IsClifford
import Definitions.Def_QPSpinProfile_Supplement_Circ

namespace QPSpinProfile.Supplement

open Matrix

/-- The all-zeros computational basis vector `|0^M⟩` of `M` qubits. -/
def ket0 (M : ℕ) : Qubits M → ℂ :=
  fun x => if x = 0 then 1 else 0

open Classical in
/-- The vector `|ψ⟩|0^r⟩` on `n + r` qubits: the `n` system qubits come first (the
first `n` indices) and the `r` ancillas are the last `r` qubits, each in `|0⟩` (arXiv:2610.02166, held
version sha256 a0a1ec89…, Definition 4.11, p.59, PDF p.62). -/
noncomputable def withCleanAncillas {n : ℕ} (ψ : Qubits n → ℂ) (r : ℕ) : Qubits (n + r) → ℂ :=
  fun x => ψ (fun i => x (Fin.castAdd r i)) *
    (if ∀ j : Fin r, x (Fin.natAdd n j) = 0 then 1 else 0)

/-- **Clean-ancilla reverse magic** `revmag^{[D],clean}_n`, Definition 4.11 (Al-Ghattas, Gamarnik,
Kiani, *Beyond light cones*, arXiv:2610.02166, held version sha256 a0a1ec89…, p.59, PDF p.62):
"Fix `D ≥ 1`. Let `revmag^{[D],clean}_n` be the class of pure `n`-qubit states `|ψ⟩` for which
there exist `r ≥ 0`, a Clifford `C ∈ cliff_{n+r}`, and a depth-`D` matching circuit `Q` on `n + r`
qubits such that `CQ|0^{n+r}⟩ = |ψ⟩|0^r⟩`."

**Formalization Note** A class is a set of density matrices: the pure state `|ψ⟩` enters as
`|ψ⟩⟨ψ|` (`vecMulVec ψ (star ψ)`) with `ψ` a unit vector. The number `r` of ancillas is
existentially quantified with no bound; the ancillas must be returned exactly to `|0^r⟩` (vector
equality, no partial trace); the shallow circuit `Q ∈ Circ[D]_{n+r}` acts first and the Clifford
`C` after it. The class is defined for every `D`; Theorem 4.16 uses it for `D ≥ 1`. -/
def revmagClean (D n : ℕ) : Set (Matrix (Qubits n) (Qubits n) ℂ) :=
  {ρ | ∃ ψ : Qubits n → ℂ, ∑ x, ‖ψ x‖ ^ 2 = 1 ∧ ρ = vecMulVec ψ (star ψ) ∧
    ∃ (r : ℕ) (C Q : Matrix (Qubits (n + r)) (Qubits (n + r)) ℂ),
      IsClifford C ∧ Q ∈ Circ D (n + r) ∧ (C * Q) *ᵥ ket0 (n + r) = withCleanAncillas ψ r}

end QPSpinProfile.Supplement


