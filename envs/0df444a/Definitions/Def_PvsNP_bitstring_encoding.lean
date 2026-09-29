-- Prove2me | Definitions.Def_PvsNP_bitstring_encoding
-- name    : PvsNP_bitstring_encoding
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T00:51:23.5815+00:00
-- url     : https://prove2.me/theorems/bf419642-eed6-406a-897b-0bde5e07a883
-- title:
--   Bitstring encodings
-- statement:
--   A class-based version of Mathlib's `Computability.Encoding` specialised to the alphabet $\{0,1\}$: a *bitstring encoding* of a type $\alpha$ is an injective-by-construction pair of maps $\mathrm{enc} : \alpha \to \{0,1\}^*$ and $\mathrm{dec} : \{0,1\}^* \to \alpha \cup \{\bot\}$ with $\mathrm{dec}(\mathrm{enc}(a)) = a$ for all $a$.
--
--   Booleans are encoded as one-bit strings. Composite data is encoded with *self-delimiting blocks*: a bitstring $b_1 b_2 \cdots b_k$ is written as $1 b_1 1 b_2 \cdots 1 b_k 0$, which doubles its length plus one and lets a parser recover where it ends. A pair is then the self-delimiting block of the first component followed by the encoding of the second, and a list is the concatenation of the self-delimiting blocks of its entries. These instances give canonical encodings for the types used throughout the mission: bitstrings themselves, and pairs of bitstrings (instance–witness pairs).
--
--   Any other reasonable binary encoding of these types is interconvertible with this one in polynomial time, so the notion of polynomial-time computability built on top of it is the intended one.
-- source:
--   google-deepmind/formal-conjectures, FormalConjectures/Millennium/PvsNP.lean and FormalConjecturesForMathlib/Computability/Complexity.lean, https://github.com/google-deepmind/formal-conjectures

import Mathlib.Computability.Encoding

/-!
# Bitstring encodings

A `class` version of Mathlib's `Computability.Encoding`, specialised to the alphabet `Bool`,
together with the instances needed to talk about polynomial-time computable functions on
bitstrings, pairs of bitstrings and lists.

Adapted from the `FormalConjecturesForMathlib.Computability.BitstringEncoding` file of the
`google-deepmind/formal-conjectures` project (Apache License 2.0).
-/

namespace PvsNP

/-- A canonical encoding of a type as bitstrings (`List Bool`). -/
class BitstringEncoding (α : Type) extends Computability.Encoding α Bool

namespace BitstringEncoding

variable {α β : Type}

/-- The encoding function of the canonical bitstring encoding of `α`. -/
def bitEncode [BitstringEncoding α] (a : α) : List Bool := toEncoding.encode a

/-- The decoding function of the canonical bitstring encoding of `α`. -/
def bitDecode [BitstringEncoding α] (l : List Bool) : Option α := toEncoding.decode l

@[simp]
theorem bitDecode_bitEncode [BitstringEncoding α] (a : α) : bitDecode (bitEncode a) = some a :=
  toEncoding.decode_encode a

theorem bitEncode_injective [BitstringEncoding α] :
    Function.Injective (bitEncode : α → List Bool) :=
  (toEncoding (α := α)).encode_injective

/-- `Bool` is encoded as a singleton bitstring. -/
instance : BitstringEncoding Bool where
  encode b := [b]
  decode l := match l with
    | [b] => some b
    | _ => none
  decode_encode _ := rfl

/-! ### Self-delimiting blocks -/

/-- Make a bitstring self-delimiting: each payload bit `b` becomes the two bits `[true, b]`,
and the block is terminated by `false`. -/
def delimit : List Bool → List Bool
  | [] => [false]
  | b :: l => true :: b :: delimit l

/-- Parse one self-delimiting block from the front of the input, returning the payload and
the remaining input. -/
def undelimit : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: input => (undelimit input).map fun p => (b :: p.1, p.2)
  | _ => none

@[simp]
theorem undelimit_delimit (l rest : List Bool) :
    undelimit (delimit l ++ rest) = some (l, rest) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimit, undelimit, ih]

@[simp]
theorem length_delimit (l : List Bool) : (delimit l).length = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [delimit, List.length_cons, ih]; omega

/-- Parse a sequence of self-delimiting blocks, using `fuel` to bound the number of blocks. -/
def undelimitBlocksAux : ℕ → List Bool → Option (List (List Bool))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, input =>
    (undelimit input).bind fun p => (undelimitBlocksAux fuel p.2).map (p.1 :: ·)

/-- Parse a sequence of self-delimiting blocks off the front of the input. -/
def undelimitBlocks (input : List Bool) : Option (List (List Bool)) :=
  undelimitBlocksAux input.length input

theorem length_le_length_flatten_delimit (l : List (List Bool)) :
    l.length ≤ ((l.map delimit).flatten).length := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      length_delimit]
    omega

private theorem undelimitBlocksAux_flatten_delimit (l : List (List Bool)) (fuel : ℕ)
    (hfuel : l.length ≤ fuel) : undelimitBlocksAux fuel ((l.map delimit).flatten) = some l := by
  induction l generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons b t ih =>
    rw [List.length_cons] at hfuel
    cases fuel <;> cases b <;> grind [delimit, undelimitBlocksAux, undelimit_delimit]

theorem undelimitBlocks_flatten_delimit (l : List (List Bool)) :
    undelimitBlocks ((l.map delimit).flatten) = some l :=
  undelimitBlocksAux_flatten_delimit l _ (length_le_length_flatten_delimit l)

@[simp]
theorem mapM_bitDecode_map_bitEncode [BitstringEncoding α] (l : List α) :
    (l.map bitEncode).mapM bitDecode = some l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-! ### Derived instances -/

/-- A pair is encoded as a self-delimiting block for the first component followed by the
encoding of the second. -/
instance [BitstringEncoding α] [BitstringEncoding β] : BitstringEncoding (α × β) where
  encode p := delimit (bitEncode p.1) ++ bitEncode p.2
  decode input :=
    match undelimit input with
    | none => none
    | some (block, rest) =>
      match bitDecode block, bitDecode rest with
      | some a, some b => some (a, b)
      | _, _ => none
  decode_encode p := by simp

/-- A list is encoded as the concatenation of self-delimiting blocks for its elements. -/
instance [BitstringEncoding α] : BitstringEncoding (List α) where
  encode l := ((l.map bitEncode).map delimit).flatten
  decode input := (undelimitBlocks input).bind (·.mapM bitDecode)
  decode_encode l := by
    rw [undelimitBlocks_flatten_delimit (l.map bitEncode)]
    exact mapM_bitDecode_map_bitEncode l

end BitstringEncoding

end PvsNP


