-- Prove2me | Definitions.Def_GaussianLattice
-- name    : GaussianLattice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.131245+00:00
-- url     : https://prove2.me/theorems/1377ffd6-d520-4708-819e-8ed5b229b47c
-- title:
--   GaussianLattice definitions
-- statement:
--   Gaussian divisibility, lattice and binary-grid conversion lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianLattice.lean). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianLattice.lean | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
set_option autoImplicit true
namespace GaussianParity
def scale (k : Int) (z : GInt) : GInt := ⟨k * z.re, k * z.im⟩
def repeatPi : Nat → GInt → GInt
  | 0, z => z
  | n+1, z => mulPi (repeatPi n z)
def repeatI : Nat → GInt → GInt
  | 0, z => z
  | n+1, z => mulI (repeatI n z)
end GaussianParity
namespace GaussianParity
def negI (z : GInt) : GInt := ⟨z.im, -z.re⟩
def repeatNegI : Nat → GInt → GInt
  | 0, z => z
  | n+1, z => negI (repeatNegI n z)
def BinaryDivisible (q : Nat) (z : GInt) : Prop :=
  ∃ w : GInt, scale ((2 : Int)^q) w = z
def PiPowerDivisible (n : Nat) (z : GInt) : Prop :=
  ∃ w : GInt, repeatPi n w = z
end GaussianParity
namespace GaussianParity
def BothOdd (z : GInt) : Prop := z.re % 2 = 1 ∧ z.im % 2 = 1
end GaussianParity
namespace GaussianParity
end GaussianParity
namespace GaussianParity
def gaussianMul (u v : GInt) : GInt :=
  ⟨u.re*v.re - u.im*v.im, u.re*v.im + u.im*v.re⟩
end GaussianParity


