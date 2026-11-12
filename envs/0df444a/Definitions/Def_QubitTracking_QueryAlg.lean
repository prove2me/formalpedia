-- Prove2me | Definitions.Def_QubitTracking_QueryAlg
-- name    : QubitTracking_QueryAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:29:17.060345+00:00
-- url     : https://prove2.me/theorems/e120de74-c406-4465-9334-af2a3bfc2ae6
-- title:
--   Efficient isometries with superposition access to a classical oracle; subspace states
-- statement:
--   An **oracle algorithm** on a $d$-qubit input register is a circuit of one- and two-qubit unitaries and standard queries to an oracle $\mathcal O:\mathbb F_2^d\to\mathbb F_2^r\cup\{\bot\}$, acting on the input and on $k$ ancillas initialized to $|0\rangle$; $U^{\mathcal O}|\psi\rangle$ is its output. A family is **efficient** if its gate count is polynomially bounded. The **subspace state** of $S\le\mathbb F_2^d$ is $|S\rangle=|S|^{-1/2}\sum_{s\in S}|s\rangle$. For a subspace $W$ and dimensions $a\le b$, the pairs $(S,T)$ have $T\le W$ of dimension $b$ and $S\le T$ of dimension $a$. For unit vectors $\psi_S,\psi_T$ indexed by the pairs, the trace distance of $|\varphi_S\rangle=N^{-1/2}\sum|S,T\rangle|\psi_S\rangle$ and $|\varphi_T\rangle=N^{-1/2}\sum|S,T\rangle|\psi_T\rangle$ is $\sqrt{1-|N^{-1}\sum_{(S,T)}\langle\psi_S|\psi_T\rangle|^2}$, $N$ the number of pairs.
--
--   These are the objects of Lemma 5.1.
--
--   **Formalization Note** The trace distance of two pure unit states $\varphi,\varphi'$ is $\sqrt{1-|\langle\varphi|\varphi'\rangle|^2}$, and the registers $|S,T\rangle$ are orthonormal.
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), §5 and Lemma 5.1, p.29

import Definitions.Def_QubitTracking_Gate
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false

open Matrix

namespace QubitTracking

/-! Oracle algorithms with superposition access to a classical oracle, for §5 (Lemma 5.1).

Source: Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time*,
arXiv:2605.30732 (held version, sha256 bf98e5b5…), §5, p.29: "Let `U(·)` be any efficient isometry
with superposition access to a classical oracle." -/

/-- **An isometry with superposition access to a classical oracle**: a circuit of one- and
two-qubit unitaries and standard queries (`|z⟩|y⟩ ↦ |z⟩|y ⊕ 𝒪(z)⟩`) to an oracle
`𝒪 : 𝔽₂^d → 𝔽₂^r ∪ {⊥}` (answer encoded in `r + 1` qubits), on a `d`-qubit input register and `k`
ancilla qubits initialized to `|0⟩`. -/
structure QueryAlg (d k r : ℕ) where
  gates : List (Gate (Fin d ⊕ Fin k) Unit (fun _ => d) (fun _ => r + 1))

/-- **Efficient** oracle-algorithm families: well-formed gates, at most `p(λ)` of them for a
polynomially bounded `p`. -/
def QAEfficient {d k r : ℕ → ℕ} (U : (l : ℕ) → QueryAlg (d l) (k l) (r l)) : Prop :=
  ∃ p : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded p ∧
    ∀ l, (∀ g ∈ (U l).gates, g.WellFormed) ∧ (U l).gates.length ≤ p l

open Classical in
/-- `U^{𝒪} |ψ⟩`: the output of the oracle algorithm on input `|ψ⟩ ⊗ |0^k⟩` with oracle `𝒪`. -/
noncomputable def QueryAlg.run {d k r : ℕ} (U : QueryAlg d k r)
    (O : Bits (Fin d) → Option (Bits (Fin r))) (ψ : Bits (Fin d) → ℂ) : Bits (Fin d ⊕ Fin k) → ℂ :=
  circMat (fun _ q => encOpt (O q)) U.gates *ᵥ
    fun f => ψ (fun j => f (Sum.inl j)) * (if ∀ j, f (Sum.inr j) = 0 then 1 else 0)

open Classical in
/-- The subspace state `|S⟩ = |S|^{-1/2} ∑_{s ∈ S} |s⟩`. -/
noncomputable def subspaceState {d : ℕ} (S : Submodule (ZMod 2) (Bits (Fin d))) :
    Bits (Fin d) → ℂ :=
  fun z => if z ∈ S then ((Real.sqrt (Nat.card S : ℝ) : ℂ))⁻¹ else 0

/-- The pairs `(S, T)` of §5 (p.29): `T ≤ W` of dimension `b` and `S ≤ T` of dimension `a`. -/
def subspacePairs {d : ℕ} (W : Submodule (ZMod 2) (Bits (Fin d))) (a b : ℕ) :
    Set (Submodule (ZMod 2) (Bits (Fin d)) × Submodule (ZMod 2) (Bits (Fin d))) :=
  {p | p.1 ≤ p.2 ∧ p.2 ≤ W ∧ Module.finrank (ZMod 2) p.1 = a ∧ Module.finrank (ZMod 2) p.2 = b}

/-- The trace distance of the pure states `|φ_S⟩ = N^{-1/2} ∑_{(S,T)} |S, T⟩|ψ_S⟩` and
`|φ_T⟩ = N^{-1/2} ∑_{(S,T)} |S, T⟩|ψ_T⟩` (Lemma 5.1, p.29; `N = (c choose b)₂ (b choose a)₂` the
number of pairs), for unit vectors `ψ_S, ψ_T`: `√(1 − |⟨φ_S|φ_T⟩|²)` with
`⟨φ_S|φ_T⟩ = N^{-1} ∑_{(S,T)} ⟨ψ_S|ψ_T⟩` (the `|S, T⟩` are orthonormal).

**Formalization Note** For unit vectors the trace distance of `|φ⟩⟨φ|` and `|φ′⟩⟨φ′|` is
`√(1 − |⟨φ|φ′⟩|²)`. -/
noncomputable def tdPairs {d : ℕ} {β : Type} [Fintype β] (P : Set (Submodule (ZMod 2) (Bits (Fin d)) ×
    Submodule (ZMod 2) (Bits (Fin d)))) (ψS ψT : Submodule (ZMod 2) (Bits (Fin d)) →
      Submodule (ZMod 2) (Bits (Fin d)) → β → ℂ) : ℝ :=
  Real.sqrt (1 - Complex.normSq
    (((Nat.card P : ℂ))⁻¹ * ∑ᶠ p ∈ P, inner' (ψS p.1 p.2) (ψT p.1 p.2)))

end QubitTracking


