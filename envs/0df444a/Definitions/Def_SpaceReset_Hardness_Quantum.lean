-- Prove2me | Definitions.Def_SpaceReset_Hardness_Quantum
-- name    : SpaceReset_Hardness_Quantum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:09.118692+00:00
-- url     : https://prove2.me/theorems/3586f147-3212-41e5-aa40-28025881a2c4
-- title:
--   Online processes, adaptive testers and the two output contracts
-- statement:
--   Quantum systems are finite: an operator on a system $\alpha$ is a complex matrix indexed by $\alpha$, and a qubit has basis $\{|0\rangle,|1\rangle\}$. A **state** is a positive semidefinite matrix of trace one, a **channel** is a completely positive trace-preserving map given by Kraus operators $\Phi(\rho)=\sum_iK_i\rho K_i^\dagger$ with $\sum_iK_i^\dagger K_i=I$, and the **trace distance** is $d(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$.
--
--   An **online process** with $n$ slots has a private memory $M$, an initial memory state $\sigma$ independent of the user, and for each slot a map on carrier $\otimes M$: at slot $j$ the carrier arrives, the slot map acts, and the carrier is returned and never touched again. An **adaptive tester with a quantum reference** has a reference system $R$, an initial state on carrier$_1\otimes R$, and after slot $j$ a channel on out$_j\otimes R$ producing the next input and the new reference (after the last slot, a final channel). It may prepare entangled inputs, retain references, measure, and choose later inputs depending on earlier outputs. Running a process against a tester gives the tester's final state $\rho^P_T$ on carrier $\otimes R$.
--
--   For a specification $G\in\mathbb F_2^{k\times n}$ the two **output contracts** are:
--
--   1. **Code state.** Each slot receives a blank $|0\rangle$; the joint state of all $n$ returned carriers must be close to the diagonal code state
--   $$\rho_C=2^{-k}\sum_{x\in\mathbb F_2^k}|G^{\mathsf T}x\rangle\langle G^{\mathsf T}x|.$$
--   2. **Phase process** $\mathcal P_G$. One uniform $x\in\mathbb F_2^k$ is drawn once and slot $j$ applies $Z^{g_j\cdot x}$ to the arriving qubit; averaging over $x$ defines the process.
--
--   A process realizes a contract within error $\varepsilon$ if the code-state trace distance is at most $\varepsilon$, respectively if for **every** valid tester the trace distance between its final states under the process and under $\mathcal P_G$ is at most $\varepsilon$; this is $d_{\mathrm{op}}\le\varepsilon$ in (5).
--
--   **Formalization Note** One reference type serves at all steps: references of varying finite dimension embed isometrically into one, and trace distance is invariant under isometries. The code-state experiment is a fixed tester that feeds blanks and swaps each returned carrier into a fresh blank reference qubit. The trace norm is the platform definition `WildeQIT.traceNorm`.
-- source:
--   Rinka Miura, STOC 2027 submission #1715 (October 2026), §1.5.1, p. 6; §2.2 and eq. (5), p. 12; Definition 5 and the code-state generator, p. 13; §2.4, p. 16

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_SpaceReset_Hardness_Trellis

set_option autoImplicit false

noncomputable section

namespace SpaceReset.Hardness

/-!
Rinka Miura, STOC 2027 submission #1715 (October 2026): finite-dimensional quantum states and
channels, online processes, adaptive testers with a quantum reference, and the two output
contracts of a binary specification (§1.5.1, p. 6; §2.2, eq. (5), p. 12; Definition 5 and the
code-state generator, p. 13; §2.4, p. 16).

Conventions. An operator on a finite system `α` is a complex matrix indexed by `α`; a qubit's
basis is `Bool` (`false = |0⟩`). A state is a positive semidefinite matrix of trace one. A channel
is a map with a Kraus representation `Φ(ρ) = Σᵢ Kᵢ ρ Kᵢ†`, `Σᵢ Kᵢ† Kᵢ = I` (completely positive
and trace preserving). Trace distance is `d(ρ,σ) = ½‖ρ − σ‖₁` with the platform trace norm.

An online process with `n` slots has a private memory system `M`, an initial memory state `σ`
(independent of the user) and one slot map per slot acting on `carrier ⊗ M`; the carrier is
returned after its slot and never touched again. A tester has one reference system `R`, an
initial state on `carrier₁ ⊗ R`, and after slot `j` a channel on `out_j ⊗ R` that produces the
next input carrier and the new reference (for the last slot it is an arbitrary final channel);
it may prepare entangled inputs, retain quantum references, measure and choose future inputs
adaptively. A single reference type loses nothing: references of varying finite dimension embed
isometrically into one large enough system, and trace distance is invariant under isometries.
-/

open Matrix
open scoped ComplexOrder

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A density matrix: positive semidefinite with trace one. -/
def IsDensity (ρ : Matrix α α ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- A quantum channel (CPTP map) `Φ : L(α) → L(β)`, in Kraus form. -/
def IsChannel (Φ : Matrix α α ℂ → Matrix β β ℂ) : Prop :=
  ∃ (r : ℕ) (K : Fin r → Matrix β α ℂ),
    ∑ i, (K i)ᴴ * K i = 1 ∧ ∀ ρ, Φ ρ = ∑ i, K i * ρ * (K i)ᴴ

/-- A POVM indexed by a finite set `ι`: positive semidefinite effects summing to the identity. -/
def IsPOVM {ι : Type} [Fintype ι] (E : ι → Matrix α α ℂ) : Prop :=
  (∀ i, (E i).PosSemidef) ∧ ∑ i, E i = 1

/-- Trace distance `d(ρ,σ) = ½‖ρ − σ‖₁`. -/
def tdist (ρ σ : Matrix α α ℂ) : ℝ :=
  WildeQIT.traceNorm (ρ - σ) / 2

/-- Partial trace over the second factor: `Tr_β : L(α ⊗ β) → L(α)`. -/
def ptraceRight (ρ : Matrix (α × β) (α × β) ℂ) : Matrix α α ℂ :=
  fun a a' => ∑ b, ρ (a, b) (a', b)

/-- Partial trace over the first factor: `Tr_α : L(α ⊗ β) → L(β)`. -/
def ptraceLeft (ρ : Matrix (α × β) (α × β) ℂ) : Matrix β β ℂ :=
  fun b b' => ∑ a, ρ (a, b) (a, b')

/-- The computational-basis projector `|x⟩⟨x|`. -/
def ketbra (x : α) : Matrix α α ℂ :=
  fun y y' => if y = x ∧ y' = x then 1 else 0

/-! ### Online processes and adaptive testers -/

/-- An online process with `n` slots (the input-output behaviour of a device): memory `M`,
initial memory state `σ`, and the slot maps `Φ j` on `carrier ⊗ M` (carrier basis `Bool`). -/
structure Process (n : ℕ) where
  M : Type
  [fM : Fintype M]
  [dM : DecidableEq M]
  σ : Matrix M M ℂ
  Φ : Fin n → Matrix (Bool × M) (Bool × M) ℂ → Matrix (Bool × M) (Bool × M) ℂ

attribute [instance] Process.fM Process.dM

/-- An adaptive tester with a quantum reference for `n` slots: reference `R`, initial state `τ`
on `carrier₁ ⊗ R`, and channels `T j` on `out_j ⊗ R` (producing `in_{j+1} ⊗ R`, or the final
state after the last slot). -/
structure Tester (n : ℕ) where
  R : Type
  [fR : Fintype R]
  [dR : DecidableEq R]
  τ : Matrix (Bool × R) (Bool × R) ℂ
  T : Fin n → Matrix (Bool × R) (Bool × R) ℂ → Matrix (Bool × R) (Bool × R) ℂ

attribute [instance] Tester.fR Tester.dR

/-- A tester is valid when its initial state is a state and all its maps are channels. -/
def Tester.Valid {n : ℕ} (T : Tester n) : Prop :=
  IsDensity T.τ ∧ ∀ j, IsChannel (T.T j)

section Interaction

variable {M R : Type} [Fintype M] [DecidableEq M] [Fintype R] [DecidableEq R]

/-- `(Φ ⊗ id_R)` on `carrier ⊗ M ⊗ R` for a (linear) map `Φ` on `carrier ⊗ M`. -/
def applyDevice (Φ : Matrix (Bool × M) (Bool × M) ℂ → Matrix (Bool × M) (Bool × M) ℂ)
    (ρ : Matrix (Bool × M × R) (Bool × M × R) ℂ) : Matrix (Bool × M × R) (Bool × M × R) ℂ :=
  fun x x' => Φ (fun a a' => ρ (a.1, a.2, x.2.2) (a'.1, a'.2, x'.2.2)) (x.1, x.2.1) (x'.1, x'.2.1)

/-- `(id_M ⊗ T)` on `carrier ⊗ M ⊗ R` for a (linear) map `T` on `carrier ⊗ R`. -/
def applyTester (T : Matrix (Bool × R) (Bool × R) ℂ → Matrix (Bool × R) (Bool × R) ℂ)
    (ρ : Matrix (Bool × M × R) (Bool × M × R) ℂ) : Matrix (Bool × M × R) (Bool × M × R) ℂ :=
  fun x x' => T (fun a a' => ρ (a.1, x.2.1, a.2) (a'.1, x'.2.1, a'.2)) (x.1, x.2.2) (x'.1, x'.2.2)

end Interaction

/-- The joint state on `carrier ⊗ M ⊗ R` after the first `j` slots (each slot: the device's slot
map, then the tester's map). -/
def jointState {n : ℕ} (D : Process n) (T : Tester n) :
    ℕ → Matrix (Bool × D.M × T.R) (Bool × D.M × T.R) ℂ
  | 0 => fun x x' => T.τ (x.1, x.2.2) (x'.1, x'.2.2) * D.σ x.2.1 x'.2.1
  | j + 1 =>
    if h : j < n then applyTester (T.T ⟨j, h⟩) (applyDevice (D.Φ ⟨j, h⟩) (jointState D T j))
    else jointState D T j

/-- The tester's final state `ρ^P_T` on `carrier ⊗ R` (the device memory traced out). -/
def finalState {n : ℕ} (D : Process n) (T : Tester n) : Matrix (Bool × T.R) (Bool × T.R) ℂ :=
  fun a a' => ∑ m : D.M, jointState D T n (a.1, m, a.2) (a'.1, m, a'.2)

/-! ### The binary linear specification's two contracts (p. 6, p. 13) -/

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The parity `g_j · x ∈ 𝔽₂` of column `j` with the latent vector `x ∈ 𝔽₂^κ`, as a bit. -/
def parityBit {n : ℕ} (G : Matrix κ (Fin n) F2) (x : κ → F2) (j : Fin n) : Bool :=
  decide ((∑ i, G i j * x i) = 1)

/-- The codeword `Gᵀx` as a bit string (one bit per slot). -/
def codeword {n : ℕ} (G : Matrix κ (Fin n) F2) (x : κ → F2) : Fin n → Bool :=
  fun j => parityBit G x j

/-- The diagonal code state `ρ_C = 2^{−k} Σ_{x ∈ 𝔽₂^k} |Gᵀx⟩⟨Gᵀx|` on `n` qubits. -/
def codeState {n : ℕ} (G : Matrix κ (Fin n) F2) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  ∑ x : κ → F2, ((1 : ℂ) / (2 : ℂ) ^ Fintype.card κ) • ketbra (codeword G x)

/-- The Pauli `Z` on the carrier of `carrier ⊗ M`. -/
def carrierZ (M : Type) [Fintype M] [DecidableEq M] : Matrix (Bool × M) (Bool × M) ℂ :=
  Matrix.diagonal (fun a => if a.1 then -1 else 1)

/-- For a fixed latent vector `x`, the memoryless process applying `Z^{g_j · x}` at slot `j`
(Definition 5, p. 13). -/
def phaseProcessAt {n : ℕ} (G : Matrix κ (Fin n) F2) (x : κ → F2) : Process n where
  M := Unit
  σ := 1
  Φ := fun j ρ => if parityBit G x j then carrierZ Unit * ρ * carrierZ Unit else ρ

/-- The tester's final state under the phase process `P_G`: one uniform `x` drawn once and shared
by all slots, averaged over `x`. -/
def phaseFinal {n : ℕ} (G : Matrix κ (Fin n) F2) (T : Tester n) :
    Matrix (Bool × T.R) (Bool × T.R) ℂ :=
  ∑ x : κ → F2, ((1 : ℂ) / (2 : ℂ) ^ Fintype.card κ) • finalState (phaseProcessAt G x) T

/-- The swap of the carrier with reference bit `j` on `carrier ⊗ (Fin n → Bool)`, as a
permutation matrix. -/
def swapIn {n : ℕ} (j : Fin n) : Matrix (Bool × (Fin n → Bool)) (Bool × (Fin n → Bool)) ℂ :=
  fun y x => if y = (x.2 j, Function.update x.2 j x.1) then 1 else 0

/-- The code-state experiment as a tester (p. 13): every slot receives a blank `|0⟩`; after slot
`j` the returned carrier is swapped into a fresh blank reference qubit `j`, which also supplies
the next blank input. The reference ends holding all returned carriers. -/
def blankTester (n : ℕ) : Tester n where
  R := Fin n → Bool
  τ := ketbra (false, fun _ => false)
  T := fun j ρ => swapIn j * ρ * (swapIn j)ᴴ

/-- The joint state of all returned carriers when every slot receives a blank `|0⟩`. -/
def emittedState {n : ℕ} (D : Process n) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  ptraceLeft (finalState D (blankTester n))

/-- The two online output contracts (p. 6). -/
inductive Contract
  | codeState
  | phaseProcess
  deriving DecidableEq

/-- A process realizes contract `c` for the specification `G` within error `ε`:
for the code state, the trace distance of the joint emitted state from `ρ_C` is at most `ε`; for
the phase process, for every adaptive tester with quantum reference the trace distance between
its final states under the process and under `P_G` is at most `ε` (eq. (5), p. 12, stated
without a supremum). -/
def ErrorLE {n : ℕ} (G : Matrix κ (Fin n) F2) (c : Contract) (D : Process n) (ε : ℝ) : Prop :=
  match c with
  | .codeState => tdist (emittedState D) (codeState G) ≤ ε
  | .phaseProcess => ∀ T : Tester n, T.Valid → tdist (finalState D T) (phaseFinal G T) ≤ ε

end SpaceReset.Hardness


