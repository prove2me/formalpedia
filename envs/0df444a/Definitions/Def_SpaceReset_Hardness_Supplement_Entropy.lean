-- Prove2me | Definitions.Def_SpaceReset_Hardness_Supplement_Entropy
-- name    : SpaceReset_Hardness_Supplement_Entropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:43:50.213194+00:00
-- url     : https://prove2.me/theorems/f97cf174-64d3-4769-b709-eb2533544b2e
-- title:
--   Von Neumann and Shannon entropy in bits, the Fano term $F_D$, and the cumulative entropy exchange $\Gamma$
-- statement:
--   Logarithms are base two (§2.2, p. 12). The **von Neumann entropy** of a density matrix is $S(\rho)=-\sum_\lambda\lambda\log\lambda$ over its eigenvalues, with $0\log0=0$ (the published platform definition `ShadowTomography.QuantumLB.vnEntropy`, in bits). The **Shannon entropy** of a probability vector is $H(p)=-\sum_b p_b\log p_b$. The **Fano term** of Lemma 26 is
--   $$F_D(e)=h_2(e)+e\log(D-1),$$
--   with $h_2$ the binary entropy (platform `WildeQIT.binaryEntropy`). For $D=1$ it equals $h_2(e)$, which is $F_1(0)=0$ at the only error $e=0$ a one-outcome guess can have.
--
--   The **cumulative entropy exchange** (App. C, p. 39) is defined as follows. Fix the slot boundaries and dilate each slot map with fresh pure ancillas, and let $G_j$ be the joint system discarded in slot $j$. In the code-generation experiment every slot receives $|0\rangle$ (code-state contract) or $|+\rangle$ (phase-process contract), and the returned carriers are retained. Then
--   $$\Gamma=\sum_{j=1}^n S(G_j),$$
--   with $S(G_j)$ the entropy of the actual marginal state of $G_j$. It is not $S(G_1\cdots G_n)$. If slot $j$ acts by Kraus operators $(K_e)$ on the actual input $\rho_j$, that marginal is $(\operatorname{Tr}K_e\rho_jK_{e'}^\dagger)_{e,e'}$.
--
--   $\Gamma$ is defined for a Definition 4 device (Kraus operators from its Stinespring isometry) and for an explicit Clifford circuit. In a Clifford circuit each RESET is dilated by a swap with a fresh $|0\rangle$ environment qubit and each $D_Z$ by its two Kraus operators $Z^b/\sqrt2$, so each irreversible gate discards one qubit.
--
--   **Formalization Note.** The slot inputs do not depend on earlier outputs. The memory marginal therefore evolves on its own, and $\rho_j$ is the fixed carrier input tensored with it.
-- source:
--   Rinka Miura, STOC 2027 submission #1715 (October 2026), The Complexity of Space–Reset Tradeoffs in Online Quantum Computation (held submission, no arXiv version; SHA-256 c2a340e2195da0d130bf10d936d56d4f1d4da805e644efb7fe1c36d9c904f3e5), App. C, pp. 39–40 (definition of Γ, Lemma 26, Theorem 28); §2.2, p. 12 (base-two logarithms)

import Mathlib
import Definitions.Def_SpaceReset_Hardness_DiscardDevice
import Definitions.Def_SpaceReset_Hardness_Supplement_Sources
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy

set_option autoImplicit false

noncomputable section

namespace SpaceReset.Hardness.Supplement

/-!
Rinka Miura, STOC 2027 submission #1715 (October 2026), App. C, pp. 39–40: von Neumann and
Shannon entropy (logarithms base two, §2.2, p. 12; von Neumann entropy is the platform's
`ShadowTomography.QuantumLB.vnEntropy`, in bits) and the cumulative entropy exchange `Γ` of an
online implementation.

`Γ` (p. 39). Fix the slot boundaries and dilate each slot map with fresh pure ancillas; `G_j` is
the joint system discarded during slot `j`. In the code-generation experiment every slot receives
the same fixed input (`|0⟩` for the code-state contract, `|+⟩` for the phase-process contract)
and the returned carriers are kept; `S(G_j)` is the entropy of the actual marginal state of `G_j`,
and `Γ = Σ_j S(G_j)` (it is not `S(G_1 ⋯ G_n)`). If slot `j` acts by the Kraus operators
`(K_e)_{e ∈ E_j}` (from a Stinespring isometry `V_j = Σ_e K_e ⊗ |e⟩`), the marginal of `G_j` is
`(Tr K_e ρ_j K_{e'}†)_{e,e'}` with `ρ_j` the slot's actual input on `carrier ⊗ memory`. The inputs
do not depend on earlier outputs, so `ρ_j` is the fixed carrier input tensored with the memory
marginal, which evolves on its own.
-/

open Matrix
open scoped Kronecker
open SpaceReset.Hardness
open ShadowTomography.QuantumLB (vnEntropy)

/-- Shannon entropy in bits of a finite probability vector `p`. -/
def shannonEntropy {β : Type} [Fintype β] (p : β → ℝ) : ℝ :=
  ∑ b, Real.negMulLog (p b) / Real.log 2

/-- The Fano term of Lemma 26 (p. 39), `F_D(e) = h₂(e) + e log₂(D − 1)` with `h₂` the binary
entropy (platform `WildeQIT.binaryEntropy`, base two). For `D = 1` it is `h₂(e)`, which is
`F_1(0) = 0` at the only error `e = 0` that a one-outcome guess can have. -/
def fanoTerm (D : ℕ) (e : ℝ) : ℝ :=
  WildeQIT.binaryEntropy e + e * Real.logb 2 ((D : ℝ) - 1)

/-- The carrier input of the code-generation experiment: `|0⟩⟨0|` for the code-state contract
(blank inputs), `|+⟩⟨+|` for the phase-process contract. -/
def experimentInput : Contract → Matrix Bool Bool ℂ
  | .codeState => ketbra false
  | .phaseProcess => fun _ _ => (1 / 2 : ℂ)

section Gamma

variable {M : Type} [Fintype M] [DecidableEq M] {n : ℕ}
  {E : Fin n → Type} [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]

/-- The memory marginal before slot `t` when every slot receives the carrier input `ψ` and acts
by the Kraus operators `K j`. -/
def memMarg (ψ : Matrix Bool Bool ℂ) (σ : Matrix M M ℂ)
    (K : (j : Fin n) → E j → Matrix (Bool × M) (Bool × M) ℂ) : ℕ → Matrix M M ℂ
  | 0 => σ
  | t + 1 => if h : t < n then
      ptraceLeft (∑ e, K ⟨t, h⟩ e * (ψ ⊗ₖ memMarg ψ σ K t) * (K ⟨t, h⟩ e)ᴴ)
    else memMarg ψ σ K t

/-- The actual marginal state of the system `G_j` discarded in slot `j`. -/
def envState (ψ : Matrix Bool Bool ℂ) (σ : Matrix M M ℂ)
    (K : (j : Fin n) → E j → Matrix (Bool × M) (Bool × M) ℂ) (j : Fin n) :
    Matrix (E j) (E j) ℂ :=
  fun e e' => (K j e * (ψ ⊗ₖ memMarg ψ σ K j) * (K j e')ᴴ).trace

/-- `Γ = Σ_j S(G_j)` for the slot Kraus families `K`. -/
def gammaOf (ψ : Matrix Bool Bool ℂ) (σ : Matrix M M ℂ)
    (K : (j : Fin n) → E j → Matrix (Bool × M) (Bool × M) ℂ) : ℝ :=
  ∑ j, vnEntropy (envState ψ σ K j)

end Gamma

/-- `Γ` of a Definition 4 device in the code-generation experiment of contract `c`: the slot
isometry `V_j : carrier ⊗ M → carrier ⊗ M ⊗ E_j` has Kraus operators `K_e = (I ⊗ ⟨e|) V_j`, and
`E_j` is the system discarded in slot `j`. -/
def deviceGamma {n q g : ℕ} (D : DiscardDevice n q g) (c : Contract) : ℝ :=
  gammaOf (experimentInput c) D.σ (fun j e => fun x y => D.V j (x, e) y)

/-! ### `Γ` of an explicit Clifford circuit -/

/-- `RESET` and `D_Z` are the irreversible named gates. -/
def IsIrrev {P : ℕ} : CGate P → Bool
  | .reset _ => true
  | .dz _ => true
  | _ => false

/-- The number of irreversible gates in a gate list. -/
def irrevNum {P : ℕ} (gs : List (CGate P)) : ℕ := (gs.filter IsIrrev).length

/-- The Kraus operator of an irreversible gate for the discarded bit `b`: `|0⟩⟨b|` on the wire
for `RESET` (its dilation swaps the wire with a fresh `|0⟩` environment qubit, which is
discarded), and `Z^b/√2` for `D_Z`. -/
def irrevKraus {P : ℕ} : CGate P → Bool → Matrix (Fin P → Bool) (Fin P → Bool) ℂ
  | .reset w, b => resetKraus w b
  | .dz w, b => (1 / (Real.sqrt 2 : ℂ)) • (if b then pauliZMat w else 1)
  | _, _ => 1

/-- The Kraus operator of a gate list for the string `bits` of discarded bits (the `i`-th
irreversible gate discards `bits i`), first gate first. -/
def krausSeq {P : ℕ} : List (CGate P) → ℕ → (ℕ → Bool) → Matrix (Fin P → Bool) (Fin P → Bool) ℂ
  | [], _, _ => 1
  | gt :: gs, i, bits =>
      if IsIrrev gt then krausSeq gs (i + 1) bits * irrevKraus gt (bits i)
      else krausSeq gs i bits * cliffordGateMat gt

/-- `Γ` of a Clifford circuit (`q + 1` private wires, carrier wire `0`) in the code-generation
experiment of contract `c`: slot `j` is dilated canonically, each irreversible gate discarding
one qubit, so `G_j` consists of `irrevNum (gates j)` qubits. -/
def circuitGamma {q n : ℕ} (C : CliffordCircuit (q + 1) n) (c : Contract) : ℝ :=
  gammaOf (E := fun j => Fin (irrevNum (C.gates j)) → Bool) (experimentInput c)
    (cellState C.cells)
    (fun j e => (krausSeq (C.gates j) 0
      (fun i => if h : i < irrevNum (C.gates j) then e ⟨i, h⟩ else false)).submatrix
        (wireEquiv (q + 1)) (wireEquiv (q + 1)))

/-- The number of initially maximally mixed private cells of a Clifford circuit. -/
def circuitMixedCount {q n : ℕ} (C : CliffordCircuit q n) : ℕ :=
  (Finset.univ.filter (fun i => C.cells i = true)).card

end SpaceReset.Hardness.Supplement


