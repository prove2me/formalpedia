-- Prove2me | Definitions.Def_PelagicFF_Supplement_LevelMessage
-- name    : PelagicFF_Supplement_LevelMessage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:27:41.518331+00:00
-- url     : https://prove2.me/theorems/feaab9e1-9664-4336-b05d-124c3f64389c
-- title:
--   Level-$k$ messages of the Clifford hierarchy and Clifford measurements
-- statement:
--   Let $P_m$ be the $m$-qubit Pauli group. The **Clifford hierarchy** is
--
--   $$
--   C_1(m)=\{e^{i\theta}P: P\in P_m,\ \theta\in\mathbb R\},\qquad C_k(m)=\{U\text{ unitary}: UPU^\dagger\in C_{k-1}(m)\ \text{for all }P\in P_m\},
--   $$
--
--   and $C_2(m)$ is the Clifford group. A **level-$k$ message** on $n$ qubits is a state $U|0^n\rangle$ with $U\in C_k(n)$ (here as the density matrix $U|0^n\rangle\langle0^n|U^\dagger$).
--
--   A **Clifford measurement** with outcomes in $Z$ applies a Clifford unitary $U\in C_2(n)$, measures all qubits in the computational basis, and outputs $g(s)$ on outcome $s\in\{0,1\}^n$ for a fixed map $g$. Its POVM element for $z\in Z$ is $\sum_{s:\,g(s)=z}U^\dagger|s\rangle\langle s|U$.
--
--   These are the restrictions on the quantum protocol of Theorem 6.2.
--
--   **Formalization Note** $C_k(n)$ is the published `TeleportGates.Ck.cliffordLevel n (k − 1)` (its index is shifted by one). That definition's first level is the Pauli group with phases $\pm1,\pm i$ instead of every $e^{i\theta}$; for $k\ge2$ the two hierarchies coincide, because $UPU^\dagger$ squares to the identity for a Hermitian Pauli $P$, which forces any $e^{i\theta}P'$ equal to it into the $\pm1,\pm i$ Pauli group. The predicate is used only with $k=d\ge2$.
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §6.3, pp.51–52 (Clifford hierarchy, level-k message); Lemma 6.3 and proof, pp.43–44 (Clifford measurement)

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_POVM
import Definitions.Def_TeleportGates_Ck_cliffordLevel

namespace PelagicFF.Supplement

/-- The computational basis state `|0ⁿ⟩` on `n` qubits (basis `Fin n → Bool`). -/
def zeroKet (n : ℕ) : (Fin n → Bool) → ℂ := fun x => if x = (fun _ => false) then 1 else 0

/-- The density matrix `|φ⟩⟨φ|` of a vector `φ`. -/
def pureDensity {n : ℕ} (φ : (Fin n → Bool) → ℂ) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  Matrix.vecMulVec φ (star φ)

/-- **A level-`k` message** on `n` qubits: the state `U|0ⁿ⟩` (as the density matrix
`U|0ⁿ⟩⟨0ⁿ|U†`) for some `U ∈ C_k(n)`, the `k`th level of the Clifford hierarchy.

arXiv:2610.05585 (held version, sha256 4564aef3…), §6.3, pp.51–52: "C₁(m) = {e^{iθ}P | P ∈ P_m,
θ ∈ ℝ}, C_k(m) = {U | U P U† ∈ C_{k−1}(m) for all P ∈ P_m} where U ranges over all m-qubit
unitaries. … Call a level-k message a state U|0^m⟩ where U ∈ C_k(m)".

**Formalization Note.** `C_k(n)` is the published `TeleportGates.Ck.cliffordLevel n (k − 1)`
(index shifted by one). Its `C₁` is the Pauli group with phases `±1, ±i` rather than all `e^{iθ}`;
for `k ≥ 2` the two hierarchies coincide (if `UPU† = e^{iθ}P'` for a Pauli `P` then squaring forces
`e^{iθ}P'` into the `±1, ±i` Pauli group, and the higher levels are defined by the same recursion).
This predicate is used only for `k = d ≥ 2`; at `k = 0` the subtraction would be truncated. -/
def IsLevelMessage {n : ℕ} (k : ℕ) (ρ : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) : Prop :=
  ∃ U ∈ TeleportGates.Ck.cliffordLevel n (k - 1),
    ρ = pureDensity (Matrix.mulVec (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (zeroKet n))

open Classical in
/-- **A Clifford measurement** with outcomes in `Z`: apply a Clifford unitary `U ∈ C₂(n)`, measure
all qubits in the computational basis, and output `g(s)` on outcome `s`; the POVM element of `z`
is `∑_{s : g(s) = z} U† |s⟩⟨s| U`.

arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 6.3 and its proof, pp.43–44 ("measuring
in the basis B_a is equivalent to applying the Clifford circuit H_jC_a and then measuring in the
computational basis. Concretely, if the final computational-basis outcome is y ∈ F₂ⁿ, then Bob
sets b = y_j and x = y + y_je_j"); §6.3, p.51 (`C₂(m)` is the Clifford group).

**Formalization Note.** `C₂(n)` is `TeleportGates.Ck.cliffordLevel n 1`. -/
def IsCliffordMeasurement {n : ℕ} {Z : Type} [Fintype Z]
    (M : ShadowTomography.QuantumLB.POVM Z (Fin n → Bool)) : Prop :=
  ∃ U ∈ TeleportGates.Ck.cliffordLevel n 1, ∃ g : (Fin n → Bool) → Z, ∀ z,
    M.op z = ∑ s ∈ Finset.univ.filter (fun s => g s = z),
      Matrix.conjTranspose (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * Matrix.single s s (1 : ℂ) *
        (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)

end PelagicFF.Supplement


