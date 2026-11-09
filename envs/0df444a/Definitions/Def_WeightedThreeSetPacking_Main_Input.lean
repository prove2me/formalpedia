-- Prove2me | Definitions.Def_WeightedThreeSetPacking_Main_Input
-- name    : WeightedThreeSetPacking_Main_Input
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:37.751243+00:00
-- url     : https://prove2.me/theorems/b0b30973-c439-4bce-807a-72a137daf36f
-- title:
--   Finite rational input and binary encodings
-- statement:
--   An input is a duplicate-free list of nonempty sets of at most three natural-number labels, each with an arbitrary positive rational weight represented by positive numerator and denominator. Labels and integers are unbounded. A finite source universe can be relabeled without changing any intersection or weight. The family may be empty.
--
--   Matching, weight sums and ground unions use the published matching vocabulary. Feasibility and optimality refer to the original weights, not the squared potential. The binary encoder writes counts and self-delimiting natural-number payloads; its alphabet is Boolean, and its input contains no answer or optimum. Output lists represent finite subfamilies.
--
--   The computational goal can therefore quantify over one machine and one polynomial before every input.
-- source:
--   Tong and Xu, arXiv:2610.10036v1, §3, p. 6; Theorem 1.1, p. 3; §4.3, pp. 25–26; https://arxiv.org/abs/2610.10036v1

import Mathlib
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace WeightedThreeSetPacking.Main

/-- Tong and Xu, arXiv:2610.10036v1, §3, p. 6: an input edge with a
positive rational weight represented by binary numerator and denominator. -/
structure InputEdge where
  ground : List ℕ
  numerator : ℕ
  denominator : ℕ

/-- Ordered, duplicate-free input records; order has no mathematical significance.
No bound is imposed on ground labels, numerators or denominators. -/
structure Input where
  entries : List InputEdge
  distinct : (entries.map fun e => e.ground.toFinset).Nodup
  valid : ∀ e ∈ entries, e.ground.Nodup ∧ 1 ≤ e.ground.length ∧
    e.ground.length ≤ 3 ∧ 0 < e.numerator ∧ 0 < e.denominator

def Input.empty : Input := ⟨[], by simp, by simp⟩

def Input.family (I : Input) : Finset (Finset ℕ) :=
  (I.entries.map fun e => e.ground.toFinset).toFinset

/-- Weights away from the input family are zero. -/
def Input.rationalWeight (I : Input) (F : Finset ℕ) : ℚ :=
  I.entries.foldl (fun w e => if e.ground.toFinset = F then
    (e.numerator : ℚ) / e.denominator else w) 0

def Input.weight (I : Input) (F : Finset ℕ) : ℝ := I.rationalWeight F

def outputFamily (P : List (List ℕ)) : Finset (Finset ℕ) :=
  (P.map List.toFinset).toFinset

def Feasible (I : Input) (P : Finset (Finset ℕ)) : Prop :=
  HyperMatchDelay.Batching.IsMatching I.family P

def totalWeight (I : Input) (P : Finset (Finset ℕ)) : ℝ :=
  HyperMatchDelay.Batching.weight I.weight P

def Optimal (I : Input) (O : Finset (Finset ℕ)) : Prop :=
  Feasible I O ∧ ∀ P, Feasible I P → totalWeight I P ≤ totalWeight I O

/-- Self-delimiting binary natural: unary length of the binary payload, a zero,
then the little-endian payload. Size is 2*bitlength(n)+1, including n=0. -/
def encodeNatural (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def encodeNaturalList (xs : List ℕ) : List Bool :=
  encodeNatural xs.length ++ xs.flatMap encodeNatural

def encodeInput (I : Input) : List Bool :=
  encodeNatural I.entries.length ++ I.entries.flatMap (fun e =>
    encodeNaturalList e.ground ++ encodeNatural e.numerator ++ encodeNatural e.denominator)

def encodeOutput (P : List (List ℕ)) : List Bool :=
  encodeNatural P.length ++ P.flatMap encodeNaturalList

end WeightedThreeSetPacking.Main


