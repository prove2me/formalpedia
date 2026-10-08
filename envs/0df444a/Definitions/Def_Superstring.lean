-- Prove2me | Definitions.Def_Superstring
-- name    : Superstring
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:27.711511+00:00
-- url     : https://prove2.me/theorems/19271869-46bd-41cc-8c51-2ceb675754f3
-- statement:
--   A symbol is a finite list of bits, a word is a finite list of symbols, and an instance is a finite list of words. A generic list encoder to bits is defined with prefix markers: the empty list is encoded as the single bit true, and a list a :: as is encoded as false followed by the encoding of a followed by the encoding of as, so the spine and its final boundary are marked. Applying this once to bits (each bit b encoded as [b]) gives the encoding of symbols, applying it to symbols gives the encoding of words, and applying it to words gives the encoding of instances. For an instance S and a word T, IsCommonSuperstring(S,T) means that every word s in S occurs in T as a contiguous sublist (an infix), the empty word being allowed. opt(S) is the infimum, taken in the natural numbers, of the lengths n of such common superstrings T, so it is measured in number of symbols, not bits. HasPolynomialImplementation(f), for a function f from instances to words, means that f is computable in polynomial time by a deterministic multi-stack Turing machine (Mathlib's TM2ComputableInPolyTime), with the input given as the bit encoding of the instance and the output as the bit encoding of the word, the running time being polynomially bounded in the length of the encoded input, and in addition every stack of the machine has a finite alphabet. These are definitions only; no theorem about approximation or optimality is stated in this block.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Superstring.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Superstring.lean; bytes 16..1214
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace Superstring

abbrev Symbol := List Bool
abbrev Word := List Symbol
abbrev Instance := List Word

/-- Prefix markers encode the list spine, including its final boundary. -/
def encodeList {α : Type} (enc : α → List Bool) : List α → List Bool
  | [] => [true]
  | a :: as => false :: (enc a ++ encodeList enc as)

def encodeSymbol : Symbol → List Bool := encodeList (fun b => [b])
def encodeWord : Word → List Bool := encodeList encodeSymbol
def encodeInstance : Instance → List Bool := encodeList encodeWord

/-- Ordinary contiguous substring containment, including the empty word. -/
def IsCommonSuperstring (S : Instance) (T : Word) : Prop :=
  ∀ s ∈ S, s <:+: T

/-- The optimum in symbols, not in bits. -/
noncomputable def opt (S : Instance) : ℕ :=
  sInf {n : ℕ | ∃ T : Word, IsCommonSuperstring S T ∧ T.length = n}

/-- A deterministic finite-stack-machine implementation, with a polynomial bound
on bit-level running time in the explicitly encoded input length. -/
def HasPolynomialImplementation (f : Instance → Word) : Prop :=
  ∃ M : Turing.TM2ComputableInPolyTime encodeInstance encodeWord f,
    ∀ k : M.tm.K, Finite (M.tm.Γ k)



end Superstring
end OAI


