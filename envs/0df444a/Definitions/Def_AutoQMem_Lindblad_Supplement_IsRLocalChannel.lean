-- Prove2me | Definitions.Def_AutoQMem_Lindblad_Supplement_IsRLocalChannel
-- name    : AutoQMem_Lindblad_Supplement_IsRLocalChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:41:28.813894+00:00
-- url     : https://prove2.me/theorems/788318c8-b7f8-48f1-9602-94b0232bf0bb
-- title:
--   $R$-local quantum channel
-- statement:
--   For a set of qubits $A$, write $\operatorname{Tr}_{\bar A}\rho$ for the partial trace of an $n$-qubit operator over the qubits outside $A$. A channel $Q_*$ on $n$ qubits is **$R$-local** if for every set of qubits $A$ there is a CPTP map $Q_{A*}$ from operators on $N_R(A)$ to operators on $A$ such that, for every state $\rho$,
--   $$\operatorname{Tr}_{\bar A}Q_*(\rho)=Q_{A*}\big(\operatorname{Tr}_{N_R(A)^c}\rho\big).$$
--   Thus the state of $A$ after one round depends only on the input on $N_R(A)$; distances are those of the interaction graph of the CSS code.
--
--   This is the locality asserted of the 4D Toom channel in Theorem 3.
--
--   **Formalization Note** The partial trace is the platform's `WildeQIT.partialTraceRight` after splitting the basis label into its restrictions to $A$ and to its complement; CPTP is the platform's `AKNMixed.FQP.IsQuantumOperation`; a state is a positive semidefinite matrix of trace one.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.38, eq. (74), p. 27 (PDF p. 29)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_Supplement_interactionGraph
import Definitions.Def_AutoQMem_Lindblad_Op
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_AKNMixed_FQP_IsQuantumOperation
open Matrix
open scoped ComplexOrder

namespace AutoQMem.Lindblad.Supplement

open AutoQMem.Lindblad

/-- **Splitting a register of qubits into a subset `A` and its complement.** For a finite set of
qubits `V` and `A ⊆ V`, the computational basis label `x : V → 𝔽₂` is identified with the pair
`(x|_A, x|_{V∖A})`, i.e. `H_V = H_A ⊗ H_{V∖A}`. -/
def splitAt {V : Type} [DecidableEq V] (A : Finset V) :
    (V → ZMod 2) ≃ (({i // i ∈ A} → ZMod 2) × ({i // i ∉ A} → ZMod 2)) :=
  Equiv.piEquivPiSubtypeProd (fun i => i ∈ A) fun _ => ZMod 2

/-- **Reduced operator on a set of qubits** `Tr_{Ā} ρ`: the partial trace of an n-qubit operator
over the complement of `A` (Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical
Stochastic Processes*, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.38, eq. (74), p. 27,
PDF 29).

**Formalization Note.** `H = H_A ⊗ H_Ā` via `splitAt A`, and the partial trace is the platform's
`WildeQIT.partialTraceRight`. -/
noncomputable def keepTrace {n : ℕ} (A : Finset (Fin n)) (ρ : Op n) :
    Matrix ({i // i ∈ A} → ZMod 2) ({i // i ∈ A} → ZMod 2) ℂ :=
  WildeQIT.partialTraceRight (Matrix.reindex (splitAt A) (splitAt A) ρ)

/-- **R-local quantum channel.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from
Classical Stochastic Processes*, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.38, eq. (74),
p. 27 (PDF 29): "A CPTP map Q_* : T(H) → T(H) is R-local if for every set of qubits A there is a CPTP
map Q_{A*} : T(H_{N_R(A)}) → T(H_A) such that, for every state ρ,
Tr_Ā Q_*(ρ) = Q_{A*}(Tr_{N_R(A)^c} ρ)."

**Formalization Note.**
* Distances are those of the interaction graph of the CSS code (`cssGraph`, §2.1, p. 14).
* CPTP is the platform's `AKNMixed.FQP.IsQuantumOperation` (linear, trace preserving, completely
  positive).
* A state is a positive semidefinite matrix of trace one.
* Definition 2.38 itself, not the Heisenberg form of Claim 2.39. That `Q_*` is CPTP is not part of
  this predicate; in Theorem 3 it follows from `IsSyndromeBased`. -/
def IsRLocalChannel {n mX mZ : ℕ} (C : CSSCode n mX mZ) (R : ℕ) (Qm : Op n → Op n) : Prop :=
  ∀ A : Finset (Fin n),
    ∃ QA : Matrix ({i // i ∈ nbhd (cssGraph C) R A} → ZMod 2)
        ({i // i ∈ nbhd (cssGraph C) R A} → ZMod 2) ℂ →
        Matrix ({i // i ∈ A} → ZMod 2) ({i // i ∈ A} → ZMod 2) ℂ,
      AKNMixed.FQP.IsQuantumOperation QA ∧
      ∀ ρ : Op n, ρ.PosSemidef → ρ.trace = 1 →
        keepTrace A (Qm ρ) = QA (keepTrace (nbhd (cssGraph C) R A) ρ)

end AutoQMem.Lindblad.Supplement


