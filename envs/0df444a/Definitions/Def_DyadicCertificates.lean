-- Prove2me | Definitions.Def_DyadicCertificates
-- name    : DyadicCertificates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.131245+00:00
-- url     : https://prove2.me/theorems/08ebd154-5611-428c-9292-e435d6ed70ee
-- title:
--   DyadicCertificates definitions
-- statement:
--   Exact Gaussian-integer parity and dyadic butterfly certificates.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
set_option autoImplicit true
namespace GaussianParity
structure GInt where
  re : Int
  im : Int
  deriving DecidableEq, Repr
def add (u v : GInt) : GInt := ⟨u.re + v.re, u.im + v.im⟩
def mulI (z : GInt) : GInt := ⟨-z.im, z.re⟩
def mulPi (z : GInt) : GInt := ⟨z.re - z.im, z.re + z.im⟩
def dividePi (z : GInt) : GInt := ⟨(z.re + z.im) / 2, (z.im - z.re) / 2⟩
def residue (z : GInt) : Int := (z.re + z.im) % 2
def PiDvd (z : GInt) : Prop := z.re % 2 = z.im % 2
def SameResidue (u v : GInt) : Prop := residue u = residue v
def numeratorLeft (u v : GInt) : GInt := add (mulI u) v
def numeratorRight (u v : GInt) : GInt := add u (mulI v)
def butterfly (u v : GInt) : GInt × GInt :=
  (dividePi (numeratorLeft u v), dividePi (numeratorRight u v))
def piIter : Nat → GInt → GInt
  | 0, z => z
  | n + 1, z => mulPi (piIter n z)
structure Fraction where
  numerator : GInt
  exponent : Nat
  deriving DecidableEq, Repr
def SameValue (x y : Fraction) : Prop :=
  piIter y.exponent x.numerator = piIter x.exponent y.numerator
structure PackedPair where
  left : GInt
  right : GInt
  exponent : Nat
  deriving DecidableEq, Repr
def certifiedButterfly (u v : GInt) (e : Nat) : PackedPair :=
  if residue u = residue v then
    ⟨(butterfly u v).1, (butterfly u v).2, e⟩
  else
    ⟨numeratorLeft u v, numeratorRight u v, e + 1⟩
def neg (z : GInt) : GInt := ⟨-z.re, -z.im⟩
def mulNegI (z : GInt) : GInt := ⟨z.im, -z.re⟩
def inverseButterfly (u v : GInt) : GInt × GInt :=
  (mulNegI (butterfly u (neg v)).1, mulI (butterfly u (neg v)).2)
def butterflyPair (p : GInt × GInt) : GInt × GInt := butterfly p.1 p.2
def doubleButterfly (u v : GInt) : GInt × GInt :=
  (⟨u.re - u.im + v.re + v.im, u.re + u.im - v.re + v.im⟩,
   ⟨u.re + u.im + v.re - v.im, -u.re + u.im + v.re + v.im⟩)
def sharedDefect (u v : GInt) : Int := (u.re + u.im + v.re + v.im) % 2
def scaleTwo (z : GInt) : GInt := ⟨2 * z.re, 2 * z.im⟩
def halfHadamard (u v : GInt) : GInt × GInt :=
  (⟨(u.re + v.re) / 2, (u.im + v.im) / 2⟩,
   ⟨(u.re - v.re) / 2, (u.im - v.im) / 2⟩)
def raiseTo (x : Fraction) (e : Nat) : Fraction :=
  ⟨piIter (e - x.exponent) x.numerator, e⟩
def commonExponent (x y : Fraction) : Nat := max x.exponent y.exponent
def alignedButterfly (x y : Fraction) : PackedPair :=
  let e := commonExponent x y
  certifiedButterfly (raiseTo x e).numerator (raiseTo y e).numerator e
end GaussianParity


