-- Prove2me | Definitions.Def_AbelianCayleyHDX_encRat
-- name    : AbelianCayleyHDX_encRat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:26:26.764304+00:00
-- url     : https://prove2.me/theorems/1712f949-6385-4718-a763-4210f4775e92
-- title:
--   Binary encoding of a rational number
-- statement:
--   A rational number $r$ is written in binary as a sign bit followed by $|\mathrm{num}(r)|$ and $\mathrm{den}(r)$ (reduced form), each in self-delimiting binary (the published `encNat` encoding). The encoding is injective and has length $O(\log(|\mathrm{num}(r)| + \mathrm{den}(r)))$; the paper writes rational weights in binary.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9 ("rational weights are encoded in binary")

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding

namespace AbelianCayleyHDX

open RSListDecodingCapacity.AllRates in
/-- **A rational number in binary** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9: "rational weights are encoded in
binary"): its sign bit, then the absolute value of its numerator and its denominator (reduced
form), each in self-delimiting binary (`encNat` of the published encoding layer). -/
def encRat (r : ℚ) : List Bool :=
  decide (r < 0) :: (encNat r.num.natAbs ++ encNat r.den)

end AbelianCayleyHDX


