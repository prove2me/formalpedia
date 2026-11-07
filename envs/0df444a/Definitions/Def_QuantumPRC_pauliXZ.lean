-- Prove2me | Definitions.Def_QuantumPRC_pauliXZ
-- name    : QuantumPRC_pauliXZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:41.220088+00:00
-- url     : https://prove2.me/theorems/7cbf39c1-99ad-4c6d-8bcc-73dac777da50
-- title:
--   Pauli operators $X^xZ^z$, the Pauli group $\mathcal P_n$, Hamming weight
-- statement:
--   On $n$ qubits with computational basis $\{|w\rangle : w\in\{0,1\}^n\}$:
--
--   1. $X^x|w\rangle=|w\oplus x\rangle$ and $Z^z|w\rangle=(-1)^{z\cdot w}|w\rangle$, for $x,z\in\{0,1\}^n$;
--   2. the **phase-free Pauli representative** is the product $X^xZ^z$;
--   3. the **Pauli group** is $\mathcal P_n=\{ i^k X^xZ^z : k\in\{0,1,2,3\},\ x,z\in\{0,1\}^n\}$, indexed by $(k,x,z)$, with $4^{n+1}$ elements;
--   4. the **weight** of $i^kX^xZ^z$ is the number of qubits on which it acts nontrivially, $|\{i : x_i=1 \text{ or } z_i=1\}|$;
--   5. $\mathrm{wt}(x)$ is the Hamming weight of a string, $x\oplus y$ the bitwise XOR and $u\cdot x=\bigoplus_i u_ix_i$ the inner product over $\mathbb F_2$;
--   6. for an operator $V$, $V(\cdot)V^\dagger$ is the superoperator $\rho\mapsto V\rho V^\dagger$.
--
--   These are the objects of §3.1 and §3.4 of the paper, used for the local-noise model, the Pauli twirl and the CWS encoding.
--
--   **Formalization Note** Qubits are indexed by `Fin n`; operators are complex matrices indexed by `Fin n → Bool`; a superoperator is any map from operators to operators (all those used are linear).
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), §3.1, pp.15–16 (wt, Pauli group, V(·)V†); §3.4, p.17 (phase-free representatives, weight)

import Mathlib
import Definitions.Def_QuantumPRC_IsPolyFamily

open Matrix

namespace QuantumPRC

/-- Bitwise XOR `x ⊕ y` of two strings of length `n`. -/
def xorB {n : ℕ} (x y : Bits n) : Bits n := fun i => Bool.xor (x i) (y i)

/-- Hamming weight `wt(x) = |{i : x_i = 1}|` (arXiv:2609.38986, §3.1, p.15). -/
def wt {n : ℕ} (x : Bits n) : ℕ := (Finset.univ.filter fun i => x i = true).card

/-- Inner product over `𝔽₂`: `u · x = ⊕_i u_i x_i`. -/
def dotB {n : ℕ} (u x : Bits n) : Bool :=
  decide (Odd (Finset.univ.filter fun i => u i = true ∧ x i = true).card)

/-- A superoperator: a map from operators on the space with basis `a` to operators on the space
with basis `b`. Every map used in this development is linear, and every one applied to a state is a
quantum channel. -/
abbrev Superop (a b : Type) : Type := Matrix a a ℂ → Matrix b b ℂ

/-- The superoperator `ρ ↦ V ρ V†` of an operator (isometry, unitary) `V`
(arXiv:2609.38986, §3.1, p.16: "`V_{A→B}(·)` denotes the CPTP map `ρ ↦ VρV†`"). -/
def conjMap {a b : Type} [Fintype a] (V : Matrix b a ℂ) : Superop a b :=
  fun ρ => V * ρ * Vᴴ

/-- The Pauli operator `X^x = ⊗_i X^{x_i}` on `n` qubits: `X^x |w⟩ = |w ⊕ x⟩` (p.16). -/
def pauliX {n : ℕ} (x : Bits n) : Matrix (Bits n) (Bits n) ℂ :=
  fun y w => if y = xorB w x then 1 else 0

/-- The Pauli operator `Z^z = ⊗_i Z^{z_i}` on `n` qubits: `Z^z |w⟩ = (−1)^{z·w} |w⟩` (p.16). -/
def pauliZ {n : ℕ} (z : Bits n) : Matrix (Bits n) (Bits n) ℂ :=
  Matrix.diagonal fun w => if dotB z w then -1 else 1

/-- **Phase-free Pauli representative `X^x Z^z`** (arXiv:2609.38986, sha256 6901b59d…, §3.1,
p.16 and §3.4, p.17: "we use the phase-free representatives `{X^x Z^z : x, z ∈ {0,1}^m}`").

**Formalization Note.** Qubits are indexed by `Fin n`, the computational basis is `Fin n → Bool`
(`true` = `|1⟩`), and `X^x Z^z` is the matrix product of `X^x` and `Z^z`. -/
def pauliXZ {n : ℕ} (x z : Bits n) : Matrix (Bits n) (Bits n) ℂ := pauliX x * pauliZ z

/-- Weight of the Pauli operator `v X^x Z^z`: the number of qubits on which it acts nontrivially
(§3.4, p.17), i.e. `|{i : x_i = 1 ∨ z_i = 1}|`. -/
def pauliWeight {n : ℕ} (x z : Bits n) : ℕ :=
  (Finset.univ.filter fun i => x i = true ∨ z i = true).card

/-- Index set of the `n`-qubit Pauli group `P_n = {v ⊗_i X^{x_i} Z^{z_i}}`, `v ∈ {±1, ±i}` (p.16):
a phase exponent `k ∈ Fin 4` (phase `i^k`) and the strings `x, z`. It has `4^{n+1}` elements. -/
abbrev PauliIdx (n : ℕ) : Type := Fin 4 × Bits n × Bits n

/-- The element `i^k X^x Z^z` of the Pauli group `P_n` named by an index. -/
noncomputable def pauliOp {n : ℕ} (P : PauliIdx n) : Matrix (Bits n) (Bits n) ℂ :=
  (Complex.I ^ (P.1 : ℕ)) • pauliXZ P.2.1 P.2.2

end QuantumPRC


