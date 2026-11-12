-- Prove2me | Definitions.Def_QSampVerif_tup
-- name    : QSampVerif_tup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:27:24.600213+00:00
-- url     : https://prove2.me/theorems/673b2fd4-955a-4478-bcea-e71cefe4074b
-- title:
--   Uniquely decodable tuples of bit strings and the string–qubit interface
-- statement:
--   Basic plumbing shared by every statement of the mission.
--
--   1. **Self-delimiting strings and tuples.** For a bit string $s$, the self-delimiting copy writes each bit $b$ as the pair $1\,b$ and closes with a single $0$. The tuple $\langle s_1,\dots,s_k\rangle$ is the concatenation of the self-delimiting copies; it is injective and of linear length, so a Turing machine can parse it.
--   2. **Wire lists** are tuples of wire indices written in unary; $\mathrm{numInstr}(c)$ is the number of instructions of a layered circuit $c$.
--   3. **Basis plumbing.** $|0\cdots0\rangle$ is the all-zero basis vector. A classical string $m$ is *loaded* into a list of wires $w$ by $X$ flips: wire $w_j$ is flipped when bit $j$ of $m$ is $1$. The string $\mathrm{padEnc}(m)$ writes each bit $b$ as $1\,b$, so a party that receives $\mathrm{padEnc}(m)$ in its wires can read the length of $m$. Measuring wires $w$ in the computational basis with outcome $a$ projects onto the basis states that agree with $a$ on $w$.
--   4. **Verifier outputs** are encoded as $\bot\mapsto 0$ and $s\mapsto 1s$.
--
--   **Formalization Note** The published `encStr` (a count followed by an unseparated concatenation) is not uniquely decodable, so inputs that machines must parse use the tuple encoding instead.
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), §3.11, p.23 (PDF 24), and paper.md decisions 4–8 of the mission plan

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Complexity

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms QAlgorithms.Complexity

/-!
Plumbing shared by the whole mission (Chung, Cojocaru, Lee, Lin, *Classical Verification of
Quantum Sampling with Negligible Error*, STOC 2027 submission, held version sha256 dbc19d8f…7ee7):
uniquely decodable string encodings and the interface between classical strings and the
computational basis of a register of qubits.
-/

/-- A self-delimiting copy of a string: every bit `b` is written as the pair `true, b`, and the
copy is closed by a single `false`.

**Formalization Note.** The published `encStr` (an element count followed by the unseparated
concatenation of the elements) is not uniquely decodable, so it is not used for inputs that a
machine has to parse. -/
def selfDelim (s : Str) : Str := s.flatMap (fun b => [true, b]) ++ [false]

/-- The tuple encoding `⟨s₁, …, s_k⟩`: the concatenation of the self-delimiting copies. It is
injective and its length is linear in the total length. -/
def tup (ls : List Str) : Str := ls.flatMap selfDelim

/-- A list of wire indices, each written in unary, as a tuple. -/
def wireList {n : ℕ} (w : List (Fin n)) : Str := tup (w.map fun i => unary i.val)

/-- The number of instructions of a layered Clifford+T circuit. -/
def numInstr {n : ℕ} (c : Layered n) : ℕ := (c.map List.length).sum

/-- The all-zero computational basis vector `|0…0⟩` as a raw amplitude vector. -/
def zeroState (n : ℕ) : QState n := fun y => if y = (fun _ => false) then 1 else 0

/-- The string `m` written so that its length can be read off: each bit `b` becomes `true, b`.
A party loading `padEnc m` into its wires can tell `m` apart from every prefix and extension. -/
def padEnc (m : Str) : Str := m.flatMap fun b => [true, b]

/-- The bit mask placed on the wires `w` by the string `m`: wire `w_j` is flipped when bit `j` of
`m` is `1` (bits beyond `|w|` are not read, missing bits count as `0`). -/
def xmask {n : ℕ} (w : List (Fin n)) (m : Str) : Qubits n := fun i =>
  (List.finRange w.length).any fun j => decide (w.get j = i) && m.getD j false

/-- Loading the classical string `m` into the wires `w` of a register by `X` flips: the
permutation `|y⟩ ↦ |y ⊕ mask⟩` of the computational basis. -/
def loadX {n : ℕ} (w : List (Fin n)) (m : Str) (ψ : QState n) : QState n :=
  fun y => ψ (fun i => xor (y i) (xmask w m i))

/-- The (unnormalized) post-measurement vector after the wires `w` are measured in the
computational basis with outcome `a`: the projection onto `{y : y_{w_j} = a_j for all j}`. -/
def project {n : ℕ} (w : List (Fin n)) (a : Qubits w.length) (ψ : QState n) : QState n :=
  fun y => if ∀ j : Fin w.length, y (w.get j) = a j then ψ y else 0

/-- The binary encoding of a verifier output: rejection `⊥` (`none`) is `0`, an accepted string
`s` is `1 s`. -/
def encOpt : Option Str → Str
  | none => [false]
  | some s => true :: s

end QSampVerif


