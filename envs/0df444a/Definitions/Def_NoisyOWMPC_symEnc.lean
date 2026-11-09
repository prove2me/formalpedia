-- Prove2me | Definitions.Def_NoisyOWMPC_symEnc
-- name    : NoisyOWMPC_symEnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:40:04.872257+00:00
-- url     : https://prove2.me/theorems/f9a7c062-be30-4d85-9a1d-94ccd9574c95
-- title:
--   Fixed-width encodings of symbols and words
-- statement:
--   A symbol $a$ of a finite alphabet $\alpha$ is encoded by the binary expansion, with a fixed number of digits, of its index in a fixed enumeration of $\alpha$; a word in $\alpha^n$ is encoded by the concatenation of its symbols' codes, and a receiver output in $\{0,1\}^m\cup\{\mathsf{fail}\}$ by $0$ for $\mathsf{fail}$ and $1v$ for an output $v$.
--
--   The paper requires that "Encodings have fixed public sizes"; these encodings are how channel words, observations, states and outputs are given to circuits, distinguishers and machines.
--
--   **Formalization Note** The alphabets have constant size, so any two fixed encodings differ by a constant-size table.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Sampling convention, p.24

import Mathlib
import Definitions.Def_KarpLiptonOM_binW
import Definitions.Def_LaconicBarrier_RunsWithin

namespace NoisyOWMPC

/-- The **fixed encoding of a symbol** of a finite alphabet `α` by `b` bits (Ishai, Lu, Zafar, STOC
2027 submission (manuscript sha256 3a9569fa…), Sampling convention, p.24: "Encodings have fixed
public sizes"): the index of `a` in a fixed enumeration of `α`, in binary with `b` digits.

**Formalization Note** The enumeration is `Fintype.equivFin α`, fixed once; since alphabets have
constant size (Definition 4.1, p.18: "The alphabets are fixed independently of `λ`"), any two fixed
encodings are translated by a constant-size table. With `b ≥ symWidth α` the encoding is
injective. -/
noncomputable def symEnc (α : Type) [Fintype α] (b : ℕ) (a : α) : List Bool :=
  KarpLiptonOM.binW b (Fintype.equivFin α a).val

/-- The number of bits `⌈log₂(|α| + 1)⌉` used for one symbol of `α`. -/
def symWidth (α : Type) [Fintype α] : ℕ := Nat.size (Fintype.card α)

/-- The encoding of a word `w ∈ αⁿ`: its symbols' codes, in order. -/
noncomputable def wordEnc (α : Type) [Fintype α] {n : ℕ} (w : Fin n → α) : List Bool :=
  (List.ofFn fun s => symEnc α (symWidth α) (w s)).flatten

/-- The encoding of a receiver output in `{0,1}^m ∪ {fail}`: `fail` is `0`, an output `v` is
`1v`. -/
def optEnc {m : ℕ} : Option (Fin m → Bool) → List Bool
  | none => [false]
  | some v => true :: LaconicBarrier.bits v

end NoisyOWMPC


