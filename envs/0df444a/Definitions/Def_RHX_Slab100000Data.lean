-- Prove2me | Definitions.Def_RHX_Slab100000Data
-- name    : RHX_Slab100000Data
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-18T19:50:02.495416+00:00
-- url     : https://prove2.me/theorems/907d8fe0-7762-46c2-ae43-02accdffbadf
-- title:
--   Slab certificate data at height 100000
-- statement:
--   Certificate data for the absence of zeros of $\zeta$ in the slab $\sigma\in[1/2,1]$, $t\in[100000,\,100000+3/1000]$.
--
--   One record of the framework structure `Arb4.SlabD`: Euler–Maclaurin cut $N=30001$, log bound, budget radius, the slab bounds, and 8 cells (`Arb4.CellD`: centre, radius, half-width, half-height) covering the slab. The data were produced by a program and are not trusted; each cell is checked by the kernel in `RHX100000.Slab.cell_0` … `cell_7`, the slab-level conditions in `RHX100000.Slab.clear`.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000) to height 100000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_Arb4_Slab
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q
namespace RHX100000.Slab
noncomputable def S : SlabD where
  tq := 14
  N := 30001
  L := (Q.frac 10309 1000)
  R := (Q.frac 417 10000)
  lo := (Q.ofNat 100000)
  hi := (Q.add (Q.ofNat 100000) (Q.frac 3 1000))
  U := (Q.frac 100001 1)
  Qr := 100000043095008432878366938256235708105086432450830519740993757073
  r0 := 173
  FN := 314126
  FD := 1000000
  m := 8
  xs := fun j => [(Q.frac 1 2),
    (Q.frac 25 48),
    (Q.frac 13 24),
    (Q.frac 7 12),
    (Q.frac 2 3),
    (Q.frac 3 4),
    (Q.frac 5 6),
    (Q.frac 11 12),
    (Q.frac 1 1)].getD j (Q.frac 1 1)
  cell := fun j => [{ a := 49, b := 0, q := 96, tn := 1638400025, rn := 106, rd := 10000, w := (Q.frac 1 96), hh := (Q.frac 25 16384) },
    { a := 34, b := 0, q := 64, tn := 1638400025, rn := 106, rd := 10000, w := (Q.frac 1 96), hh := (Q.frac 25 16384) },
    { a := 9, b := 0, q := 16, tn := 1638400025, rn := 209, rd := 10000, w := (Q.frac 1 48), hh := (Q.frac 25 16384) },
    { a := 5, b := 0, q := 8, tn := 1638400025, rn := 417, rd := 10000, w := (Q.frac 1 24), hh := (Q.frac 25 16384) },
    { a := 17, b := 0, q := 24, tn := 1638400025, rn := 417, rd := 10000, w := (Q.frac 1 24), hh := (Q.frac 25 16384) },
    { a := 19, b := 0, q := 24, tn := 1638400025, rn := 417, rd := 10000, w := (Q.frac 1 24), hh := (Q.frac 25 16384) },
    { a := 7, b := 0, q := 8, tn := 1638400025, rn := 417, rd := 10000, w := (Q.frac 1 24), hh := (Q.frac 25 16384) },
    { a := 23, b := 0, q := 24, tn := 1638400025, rn := 417, rd := 10000, w := (Q.frac 1 24), hh := (Q.frac 25 16384) }].getD j { a := 23, b := 0, q := 24, tn := 1638400025, rn := 417, rd := 10000, w := (Q.frac 1 24), hh := (Q.frac 25 16384) }
end RHX100000.Slab

def RHX_Slab100000Data : Nat := 0


