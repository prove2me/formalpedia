-- Prove2me | Definitions.Def_GaussianScalarCircuits
-- name    : GaussianScalarCircuits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.131245+00:00
-- url     : https://prove2.me/theorems/867cf428-8114-4811-976b-7a5612498800
-- title:
--   GaussianScalarCircuits definitions
-- statement:
--   Canonical Gaussian arithmetic, scalar circuit normalization and exact refinement lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
set_option autoImplicit true
namespace GaussianSynthesis
open GaussianParity
def normalizeCore : Nat → GInt → Fraction
  | 0, z => ⟨z, 0⟩
  | e+1, z =>
      if residue z = 0 then normalizeCore e (dividePi z) else ⟨z, e+1⟩
def normalize (x : Fraction) : Fraction := normalizeCore x.exponent x.numerator
def Canonical (x : Fraction) : Prop := x.exponent = 0 ∨ residue x.numerator ≠ 0
end GaussianSynthesis
namespace GaussianSynthesis
def mixedCenterN (sumB sumD : Int) : Int := sumB - 2*sumD
def scatterNumerator64 (sumSelectedB sumSelectedD N k : Int) : Int :=
  16*sumSelectedB - 32*sumSelectedD - (k-1)*N
def correctedBulkCoefficientNumerator (j : Int) : Int :=
  j-1 + (if j=0 then 1 else 0) - (if j=2 then 1 else 0)
end GaussianSynthesis
namespace GaussianSynthesis
structure CenterTotals where
  total : Int
  sumD : Int
  sumB : Int
  deriving DecidableEq, Repr
def centerPlus (u v : CenterTotals) : CenterTotals :=
  ⟨u.total+v.total, u.sumD+v.sumD, u.sumB+v.sumB⟩
def centerColumn (x k : Int) : CenterTotals :=
  ⟨x, (19-k)*x, 2*(3-k)*x⟩
def sumCenterColumns : List (Int × Int) → CenterTotals
  | [] => ⟨0,0,0⟩
  | (x,k)::xs => centerPlus (centerColumn x k) (sumCenterColumns xs)
def InCenterImage (c : CenterTotals) : Prop :=
  mixedCenterN c.sumB c.sumD = -32*c.total
end GaussianSynthesis
namespace GaussianSynthesis
def correctedScatterColumn64 (x j : Int) : Int :=
  32*(j-1)*x + 32*(if j=0 then x else 0) - 32*(if j=2 then x else 0)
def sumCorrectedScatter64 : List (Int × Int) → Int
  | [] => 0
  | (x,j)::xs => correctedScatterColumn64 x j + sumCorrectedScatter64 xs
def sumDiagonalSources : List (Int × Int) → Int
  | [] => 0
  | (x,j)::xs => (if j=3 then x else 0) + sumDiagonalSources xs
end GaussianSynthesis
namespace GaussianSynthesis
open GaussianParity
def rawC (u v : GInt) (e : Nat) : PackedPair :=
  ⟨numeratorLeft u v, numeratorRight u v, e+1⟩
def packedLeft (p : PackedPair) : Fraction := ⟨p.left,p.exponent⟩
def packedRight (p : PackedPair) : Fraction := ⟨p.right,p.exponent⟩
def rawCInverse (p : PackedPair) : PackedPair :=
  let q := rawC p.left p.right p.exponent
  ⟨q.right,q.left,q.exponent⟩
def rawAlignedC (x y : Fraction) : PackedPair :=
  let e := commonExponent x y
  rawC (raiseTo x e).numerator (raiseTo y e).numerator e
def phaseI (x : Fraction) : Fraction := ⟨mulI x.numerator,x.exponent⟩
def phaseNegI (x : Fraction) : Fraction := ⟨mulNegI x.numerator,x.exponent⟩
def exactHalf (x : Fraction) : Fraction := ⟨mulI x.numerator,x.exponent+2⟩
def exactDouble (x : Fraction) : Fraction := ⟨scaleTwo x.numerator,x.exponent⟩
end GaussianSynthesis
namespace GaussianSynthesis
open GaussianParity
def gaussianDifference (u v : GInt) : GInt := add u (neg v)
end GaussianSynthesis
namespace GaussianSynthesis
def recoverIfImage {A B : Type} [DecidableEq B]
    (P : A → B) (Q : B → A) (d : B) : Option A :=
  if P (Q d) = d then some (Q d) else none
end GaussianSynthesis
namespace GaussianSynthesis
end GaussianSynthesis
namespace GaussianSynthesis
open GaussianParity
end GaussianSynthesis
namespace GaussianSynthesis
open GaussianParity
end GaussianSynthesis


