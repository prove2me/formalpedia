-- Prove2me | Definitions.Def_ForestPersuasion_Symmetric_Encoding
-- name    : ForestPersuasion_Symmetric_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:18:51.761546+00:00
-- url     : https://prove2.me/theorems/c703853c-6986-40a7-8e1c-385a6864cf07
-- title:
--   Binary rational inputs for exact weak polynomial computation
-- statement:
--   A raw input contains $n$, one optional parent per receiver, the prior, the four receiver payoffs per receiver, and $n+1$ sender utility values. All numerical data are rational. Validity requires the real persuasion model's standing assumptions, nonnegative sender utility values, and monotonicity of the utility table. An instance is the subtype of valid raw data; its encoding ignores the proof of validity.
--
--   Each natural number is written in little-endian binary, with a true marker before each bit and a final false delimiter. Its code length is twice the binary digit length plus one. A rational is its sign bit followed by the binary codes of its absolute numerator and positive denominator, in reduced form. Parent entries use zero for a root and $j+1$ for parent $j$. Arrays occur in increasing receiver order, with state and action ordered $0,1$.
--
--   The input contains only the source data. The same rational encoding represents the exact output; no threshold, optimal value, LP solution, or separation oracle is included in the input. This fixes the finite alphabet as Bool and the input size as binary bit length.
-- source:
--   Konstantin Zabarnyi, Designing Information in a Forest: Algorithmic Aspects, STOC 2027 submission #271 (October 2026; PDF dated November 2, 2026), §2 numerical model and utility representation; Theorem 9 weakly polynomial time, PDF pp. 6–8, 12 (printed pp. 5–7, 11). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/271.pdf

import Mathlib
import Definitions.Def_ForestPersuasion_Symmetric_Model

open scoped NNReal ENNReal
open Classical
noncomputable section

namespace ForestPersuasion.Symmetric

/-- All and only the finite numerical input data. No thresholds, LP solutions, or optimal values. -/
structure RawInstance where
  n : ℕ
  parent : Fin n → Option (Fin n)
  prior : ℚ
  receiverUtility : Fin n → Bool → Bool → ℚ
  senderUtility : Fin (n + 1) → ℚ

def RawInstance.model (I : RawInstance) : Model I.n where
  hierarchy := ⟨I.parent⟩
  prior := I.prior
  receiverUtility i w a := I.receiverUtility i w a

def RawInstance.Valid (I : RawInstance) : Prop :=
  I.model.Valid ∧ (∀ k, 0 ≤ I.senderUtility k) ∧ Monotone I.senderUtility

abbrev Instance := {I : RawInstance // I.Valid}

def Instance.utility (I : Instance) : SenderUtility I.val.n :=
  symmetricUtility (fun k => ⟨(I.val.senderUtility k : ℝ), by
    exact_mod_cast I.property.2.1 k⟩)

/-- Self-delimiting little-endian binary naturals: each data bit is prefixed by true,
then a lone false terminates the number. Zero has no data bits. Length is 2*bits(n)+1. -/
def encodeNat (n : ℕ) : List Bool :=
  (Nat.bits n).flatMap (fun b => [true, b]) ++ [false]

/-- Sign, absolute numerator, positive denominator in reduced form. -/
def encodeRat (q : ℚ) : List Bool :=
  [decide (q.num < 0)] ++ encodeNat q.num.natAbs ++ encodeNat q.den

/-- n, parent entries (0 for a root, j+1 for parent j), prior, four payoffs per
receiver, and n+1 sender payoffs, in that order. All numbers use the binary code above. -/
def encodeRaw (I : RawInstance) : List Bool :=
  encodeNat I.n ++
    (List.finRange I.n).flatMap (fun i => encodeNat (match I.parent i with
      | none => 0
      | some j => j.val + 1)) ++
    encodeRat I.prior ++
    (List.finRange I.n).flatMap (fun i =>
      [false, true].flatMap (fun w =>
        [false, true].flatMap (fun a => encodeRat (I.receiverUtility i w a)))) ++
    (List.finRange (I.n + 1)).flatMap (fun k => encodeRat (I.senderUtility k))

def encodeInstance (I : Instance) : List Bool := encodeRaw I.val

end ForestPersuasion.Symmetric


