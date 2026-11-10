-- Prove2me | Definitions.Def_GoldsteinMCSP_Hardness_Encoding
-- name    : GoldsteinMCSP_Hardness_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T17:11:33.130491+00:00
-- url     : https://prove2.me/theorems/8c015a8a-bd08-4b77-b50e-ee4aece679bd
-- title:
--   Self-delimiting binary words, natural numbers, lists and accuracies
-- statement:
--   Binary words are finite lists of bits. A framed word replaces each data bit b by 1b and terminates with 0. Natural numbers use framed canonical little-endian binary digits; a list prefixes each entry with 1 and terminates with 0. The parsers return an optional value and unconsumed suffix, rejecting truncated or noncanonical codes. List parsing uses input-length fuel. A pair frames its first word and appends its second.
--
--   Accuracy parameters are pairs of natural numbers (p,q) representing the positive rational (p+1)/(q+1); every positive rational is represented. Accuracy codes are two-element natural-number lists. The adapters for binary functions and accuracy-dependent functions parse the outer frame and return the empty word on malformed input. These are concrete encoding utilities, independent of the string problem.
-- source:
--   Goldstein, Kolman and Zheng (2005), Minimum Common String Partition Problem: Hardness and Approximations, EJC 12, R50, DOI 10.37236/1947, Section 2, pp. 6–9; explicit binary-machine encoding convention

import Mathlib

namespace GoldsteinMCSP.Hardness
abbrev Bits := List Bool

/-- Prefix-free escaping: a data bit b is 1b; 0 terminates a word. -/
def frame (w : Bits) : Bits := w.flatMap (fun b => [true,b]) ++ [false]

def unframe : Bits → Option (Bits × Bits)
  | false :: rest => some ([], rest)
  | true :: b :: rest => do
      let (w, tail) ← unframe rest
      pure (b :: w, tail)
  | _ => none

def bitsNat (w : Bits) : ℕ := w.foldr (fun b n => (if b then 1 else 0) + 2*n) 0

def encodeNat (n : ℕ) : Bits := frame n.bits

def parseNat (w : Bits) : Option (ℕ × Bits) := do
  let (ds, rest) ← unframe w
  let n := bitsNat ds
  if n.bits == ds then pure (n, rest) else none

def encodeList : List ℕ → Bits
  | [] => [false]
  | n :: ns => true :: (encodeNat n ++ encodeList ns)

/-- Fuel counts list constructors, bounded by the number of input bits. -/
def parseListAux : ℕ → Bits → Option (List ℕ × Bits)
  | 0, _ => none
  | _+1, false :: rest => some ([], rest)
  | k+1, true :: rest => do
      let (n, tail) ← parseNat rest
      let (ns, tail') ← parseListAux k tail
      pure (n :: ns, tail')
  | _+1, [] => none

def parseList (w : Bits) : Option (List ℕ × Bits) := parseListAux (w.length + 1) w

def pairBits (a b : Bits) : Bits := frame a ++ b

def onPair (f : Bits → Bits → Bits) (w : Bits) : Bits :=
  match unframe w with
  | some (a,b) => f a b
  | none => []

/-- Every positive rational is represented, possibly by more than one pair. -/
abbrev Accuracy := ℕ × ℕ

def accuracyValue (e : Accuracy) : ℚ := (e.1 + 1 : ℕ) / (e.2 + 1 : ℚ)

def encodeAccuracy (e : Accuracy) : Bits := encodeList [e.1,e.2]

def decodeAccuracy (w : Bits) : Option Accuracy := do
  let (xs, rest) ← parseList w
  match xs, rest with
  | [p,q], [] => some (p,q)
  | _, _ => none

def onAccuracy (f : Accuracy → Bits → Bits) (w : Bits) : Bits :=
  match unframe w with
  | some (a,x) => match decodeAccuracy a with
      | some e => f e x
      | none => []
  | none => []

end GoldsteinMCSP.Hardness


