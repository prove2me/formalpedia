-- Prove2me | Definitions.Def_PosIndexNash_PPADS_NormalForm_enc
-- name    : PosIndexNash_PPADS_NormalForm_enc
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:47:11.408586+00:00
-- url     : https://prove2.me/theorems/67ca8ad0-959a-4f42-9597-5782dca3f638
-- title:
--   Binary encoding of an anchored max-affine normal form
-- statement:
--   The binary code of a normal form records its complete rational data: $d,m$, the vector $b$, the matrices $U,c$ in row-major order, and the distinguished gate indices $o_\ell,p_\ell$. All entries use the standard self-delimiting binary codes for natural and rational numbers. This supplies the concrete instance encoding needed for polynomial-time reductions between the fixed-point, LCP, and game stages of §§5–6.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879, pp. 35–36, §5.1, equations (31)–(36); encoding conventions as used throughout the mission

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_PosIndexNash_PPADS_NormalForm

namespace PosIndexNash.PPADS

open QAlgorithms.LocalHamiltonian

/-- Binary code of the complete rational data of a normal form: the dimensions `d,m`, then
`b`, `U`, `c`, and the output and predecessor gate indices `o,p`. Every numerical entry uses
the public self-delimiting binary encoding, and the row-major matrix entries have lengths fixed
by the dimensions. -/
def NormalForm.enc (F : NormalForm) : List Bool :=
  encBin F.d ++ encBin F.m ++
    (List.finRange F.m).flatMap (fun i => encRat (F.b i)) ++
    (List.finRange F.m).flatMap (fun i =>
      (List.finRange F.d).flatMap (fun k => encRat (F.U i k))) ++
    (List.finRange F.m).flatMap (fun i =>
      (List.finRange F.m).flatMap (fun j => encRat (F.c i j))) ++
    (List.finRange F.d).flatMap (fun l => encBin (F.o l).val) ++
    (List.finRange F.d).flatMap (fun l => encBin (F.p l).val)

end PosIndexNash.PPADS


