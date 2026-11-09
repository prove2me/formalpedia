-- Prove2me | Definitions.Def_CommutativeRankNC_Approximation_ConstructionCodes
-- name    : CommutativeRankNC_Approximation_ConstructionCodes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:58.907588+00:00
-- url     : https://prove2.me/theorems/a6d27eed-2a2e-46e2-a4ef-0ecbf8fded5b
-- title:
--   Bit interfaces for the finite constructions
-- statement:
--   The construction interfaces encode the field parameter in unary and its two operands in $r_f$ fixed bits, with fixed-bit output for the chosen polynomial, sum, product and inverse. The sign-table code concatenates the signs for every seed in order; the direction-table code concatenates each rational direction using the published rational encoding.
--
--   $$\operatorname{bitSize}(a/b)=\max\{\operatorname{bits}(|a|),\operatorname{bits}(b)\}.$$
--
--   This is the numerator/denominator length parameter on p.24, with one additional sign bit absorbed in constants. These codes expose the actual functions whose uniform parallel construction is asserted by the milestones.
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), pp.9, 11, 24, 27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_Boosting

namespace CommutativeRankNC.Approximation

open QAlgorithms.LocalHamiltonian

def fixedBits (r a : ℕ) : List Bool := (List.range r).map a.testBit

/-- Unary field-size parameter followed by two r-bit operands. -/
def fieldInputCode (m a b : ℕ) : List Bool :=
  List.replicate m true ++ [false] ++ fixedBits (fieldDegree m) a ++ fixedBits (fieldDegree m) b

noncomputable def fieldOutputCode (m a b : ℕ) : List Bool :=
  fixedBits (fieldDegree m) (fieldPolynomialCode m) ++
  fixedBits (fieldDegree m) (fieldAdd m a b) ++ fixedBits (fieldDegree m) (fieldMul m a b) ++
  fixedBits (fieldDegree m) (fieldInv m a)

noncomputable def signTableCode (m t : ℕ) : List Bool :=
  (signList m t).flatMap (fun e => (List.finRange m).map e)

noncomputable def directionTableCode (k m : ℕ) : List Bool :=
  (directionList k m).flatMap (fun b => (List.finRange m).flatMap (fun i => encRat (b i)))

/-- The page-24 entry parameter: maximum of the numerator-magnitude and
positive-denominator binary lengths. A sign adds only one bit. -/
def rationalBitSize (q : ℚ) : ℕ := max q.num.natAbs.bits.length q.den.bits.length

end CommutativeRankNC.Approximation


