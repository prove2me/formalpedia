-- Prove2me | Definitions.Def_QIndInf_Supplement_instrOf
-- name    : QIndInf_Supplement_instrOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:21:28.816584+00:00
-- url     : https://prove2.me/theorems/679dec31-5509-4d64-9a34-c2c3ef267b06
-- title:
--   Instruments, POVMs and sources given by circuit descriptions
-- statement:
--   **Instruments.** A circuit with $n$ input wires and $n+k$ output wires implements an instrument $\{\mathcal E_x\}_{x\in\{0,1\}^k}$ on one $n$-qubit register: the first $n$ output wires are the post-measurement register $R$, the last $k$ the outcome register $X$, measured in the computational basis, and $\mathcal E_x(\rho)$ is the block of the circuit's output at outcome $x$. A description $d$ is valid if it describes such a circuit; the instrument it describes is the one the circuit implements.
--
--   **POVMs.** A circuit with $n$ input wires and $k$ output wires, all measured, implements a POVM $\{E_x\}$ with $\mathrm{Tr}[E_x\rho]=\langle x|C(\rho)|x\rangle$; it is used through the instrument $\mathcal E_x(\rho)=\mathrm{Tr}[E_x\rho]\,|0^n\rangle\langle 0^n|$.
--
--   **Sources.** For a program $T$, a register size $n$ and a time bound $t$, the source $\rho^T$ is defined as follows. If $T^t$ writes the description of a circuit, the circuit is run on the all-zero state, and its output state on $\ell$ qubits is adjusted to $jn$ qubits as in Eq. (40): the last $\ell-jn$ qubits are traced out if $\ell\ge jn$, and $|0^{jn-\ell}\rangle$ is appended if $\ell<jn$. This gives the state $\rho^T_{R_1\dots R_j}$ for every $j$. If $T^t$ writes no valid circuit, the state is $|0^{jn}\rangle\langle 0^{jn}|$.
--
--   These are the instances of Definitions 4.3 and 5.4: a program generating the source, and the circuit descriptions of the instruments or POVMs, which the learner reads.
--
--   **Formalization Note** The instrument is recorded as a Kraus family of the base type `QuantumInstrument` with $2^k$ outcomes; the branches are fixed by the circuit, the Kraus family is not, and no quantity depends on it.
-- source:
--   Hiroka, Hsieh, Shirakawa, Universal Inductive Inference of Quantum States, arXiv:2609.36912 (PDF of 2026-11-02, sha256 ac6387756651cc50c671f36acf1ef987db0df0c463581cd948250204441f6925), Definition 3.1, p.15; Definition 3.5, Eq. (40), p.16; §4.1, Eq. (50), p.18 (each instrument specified by a circuit description); §5.1, p.25 (POVM instruments); Definition 5.4, p.25

import Mathlib
import Definitions.Def_QIndInf_Supplement_IsQPT
import Definitions.Def_QIndInf_Supplement_regsEquiv
import Definitions.Def_QAlgorithms_Defs_QuantumInstruments

set_option autoImplicit false

namespace QIndInf.Supplement

open QAlgorithms QAlgorithms.CopyMeasurements QiOPoQ

variable {G : GateSet}

/-- A register-indexed operator on `n` qubits read on wires. -/
def toWires {n : ℕ} (ρ : Matrix (QIndInf.Reg n) (QIndInf.Reg n) ℂ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  Matrix.reindex (bitsEquiv n).symm (bitsEquiv n).symm ρ

/-- The outcome-`x` branch of the instrument implemented by a circuit `C` with `n` input wires and
`n + k` output wires: the first `n` output wires are the post-measurement register `R`, the last
`k` are the classical outcome register `X`, measured in the computational basis; the branch is the
block of `C(ρ)` at outcome `x`. -/
noncomputable def circBranch (C : Circ G) (n k : ℕ) (x : Fin k → Bool) :
    Superop (QIndInf.Reg n) (QIndInf.Reg n) :=
  fun ρ => Matrix.of fun r r' =>
    chanAs C n (n + k) (toWires ρ)
      ((splitEquiv n k).symm ((bitsEquiv n).symm r, x))
      ((splitEquiv n k).symm ((bitsEquiv n).symm r', x))

/-- `I` (with `2^k` outcomes) is the instrument implemented by the circuit `C`
(Definition 3.1, p.15, with an instrument "specified by a circuit description implementing it",
§4.1, p.18). -/
def ImplementsInstr (C : Circ G) (n k : ℕ)
    (I : QuantumInstrument (QIndInf.Reg n) (Fin (2 ^ k))) : Prop :=
  C.nin = n ∧ C.out.length = n + k ∧
    ∀ (x : Fin (2 ^ k)) (ρ : Matrix (QIndInf.Reg n) (QIndInf.Reg n) ℂ),
      instrumentBranch I x ρ = circBranch C n k ((bitsEquiv k).symm x) ρ

/-- The one-outcome identity instrument (a default value). -/
def trivInstr (n : ℕ) : QuantumInstrument (QIndInf.Reg n) (Fin (2 ^ 0)) where
  multiplicity := fun _ => 1
  kraus := fun _ _ => 1
  complete := by simp

/-- `d` is the description of a circuit implementing an instrument on one `n`-qubit register. -/
def ValidInstrDesc (G : GateSet) (n : ℕ) (d : List Bool) : Prop :=
  ∃ p : Σ k, QuantumInstrument (QIndInf.Reg n) (Fin (2 ^ k)), ∃ C : Circ G,
    decCirc G d = some C ∧ ImplementsInstr C n p.1 p.2

open Classical in
/-- **The instrument described by `d`**: `2^k` outcomes (`k` outcome bits) and the instrument the
described circuit implements; a default one-outcome instrument if `d` describes none.

**Formalization Note.** The branches `E_x` of the instrument are determined by the circuit; the
choice of Kraus family is immaterial (every quantity of the development depends on the branches
only). -/
noncomputable def instrOf (G : GateSet) (n : ℕ) (d : List Bool) :
    Σ k, QuantumInstrument (QIndInf.Reg n) (Fin (2 ^ k)) :=
  if h : ValidInstrDesc G n d then h.choose else ⟨0, trivInstr n⟩

/-- `|0^n⟩⟨0^n|` on a register. -/
def zeroProj (n : ℕ) : Matrix (QIndInf.Reg n) (QIndInf.Reg n) ℂ :=
  Matrix.single (bitsEquiv n fun _ => false) (bitsEquiv n fun _ => false) 1

/-- `I` (with `2^k` outcomes) is the instrument `E_x(ρ) = Tr[E_x ρ] |0^n⟩⟨0^n|` of the POVM
`{E_x}` implemented by the circuit `C` with `n` input wires and `k` output wires, all measured in
the computational basis (`Tr[E_x ρ] = ⟨x|C(ρ)|x⟩`).

arXiv:2609.36912 (PDF of 2026-11-02), §5.1, p.25 ("if we choose instruments … E^{(i)}_x(ρ) =
Tr[E^{(i)}_x ρ]|0^n⟩⟨0^n| for some POVM {E^{(i)}_x}_x, Definition 4.1 reduces to the POVM-based
definition") and Definition 5.4, p.25 ("described as a quantum circuit implementing it"). -/
def ImplementsPOVM (C : Circ G) (n k : ℕ)
    (I : QuantumInstrument (QIndInf.Reg n) (Fin (2 ^ k))) : Prop :=
  C.nin = n ∧ C.out.length = k ∧
    ∀ (x : Fin (2 ^ k)) (ρ : Matrix (QIndInf.Reg n) (QIndInf.Reg n) ℂ),
      instrumentBranch I x ρ =
        chanAs C n k (toWires ρ) ((bitsEquiv k).symm x) ((bitsEquiv k).symm x) • zeroProj n

/-- `d` is the description of a circuit implementing a POVM on one `n`-qubit register. -/
def ValidPOVMDesc (G : GateSet) (n : ℕ) (d : List Bool) : Prop :=
  ∃ p : Σ k, QuantumInstrument (QIndInf.Reg n) (Fin (2 ^ k)), ∃ C : Circ G,
    decCirc G d = some C ∧ ImplementsPOVM C n p.1 p.2

open Classical in
/-- **The POVM described by `d`**, as its instrument `E_x(ρ) = Tr[E_x ρ]|0^n⟩⟨0^n|`; a default
one-outcome instrument if `d` describes none. -/
noncomputable def povmOf (G : GateSet) (n : ℕ) (d : List Bool) :
    Σ k, QuantumInstrument (QIndInf.Reg n) (Fin (2 ^ k)) :=
  if h : ValidPOVMDesc G n d then h.choose else ⟨0, trivInstr n⟩

/-- **Eq. (40): adjusting an `ℓ`-qubit state to `N` qubits**: the partial trace over the last
`ℓ − N` qubits if `ℓ ≥ N`, and `σ ⊗ |0^{N−ℓ}⟩⟨0^{N−ℓ}|` if `ℓ < N`.

arXiv:2609.36912 (PDF of 2026-11-02), Definition 3.5, Eq. (40), p.16, and the convention after it
("whenever we say that a Turing machine generates a circuit description of an n-qubit state, if the
circuit does not output exactly n qubits, we implicitly apply partial tracing or padding"). -/
def adjustQubits (ℓ N : ℕ) (ρ : Matrix (Fin ℓ → Bool) (Fin ℓ → Bool) ℂ) :
    Matrix (Fin N → Bool) (Fin N → Bool) ℂ :=
  Matrix.of fun z z' =>
    if ∀ a : Fin N, ℓ ≤ a.val → z a = false ∧ z' a = false then
      ∑ y, ∑ y', if (∀ a : Fin ℓ, ∀ h : a.val < N, y a = z ⟨a.val, h⟩ ∧ y' a = z' ⟨a.val, h⟩) ∧
          (∀ a : Fin ℓ, N ≤ a.val → y a = y' a) then ρ y y' else 0
    else 0

/-- The circuit written by the machine `T` within `t` steps (on empty input), if any. -/
noncomputable def srcCirc (G : GateSet) (T : List Bool) (t : ℕ) : Option (Circ G) :=
  (tmRun T [] t).bind (decCirc G)

/-- **The source `ρ^T` generated by `T^t`** (Eq. (50), p.18): for every number `j` of registers,
the state on `R₁ … R_j` prepared by the circuit that `T` writes within `t` steps, run on the
all-zero state and adjusted to `j·n` qubits as in Eq. (40); `|0^{jn}⟩⟨0^{jn}|` if `T` writes no
valid circuit within `t` steps (Eq. (40), last sentence).

**Formalization Note.** Register `R_{i+1}` is the block of qubits `n·i, …, n·i+n−1`
(`regsEquiv`). Adjusting to fewer qubits is a partial trace over the last qubits, so `j ↦ ρ_{≤j}`
is the family of reduced states of one source. -/
noncomputable def srcFamily (G : GateSet) (n t : ℕ) (T : List Bool) :
    (j : ℕ) → Matrix (QIndInf.Regs n j) (QIndInf.Regs n j) ℂ :=
  fun j => Matrix.reindex (regsEquiv n j) (regsEquiv n j)
    (match srcCirc G T t with
      | some C => adjustQubits C.out.length (j * n)
          (chan C (Matrix.single (fun _ => false) (fun _ => false) 1))
      | none => Matrix.single (fun _ => false) (fun _ => false) 1)

end QIndInf.Supplement


