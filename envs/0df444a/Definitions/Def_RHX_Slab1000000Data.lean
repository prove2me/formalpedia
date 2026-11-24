-- Prove2me | Definitions.Def_RHX_Slab1000000Data
-- name    : RHX_Slab1000000Data
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:44:42.584947+00:00
-- url     : https://prove2.me/theorems/6982f9a1-6f56-46aa-89e0-1c6a8aea2557
-- title:
--   Slab certificate data at height 1000000
-- statement:
--   Certificate data for the absence of zeros of $\zeta$ in the slab $\sigma\in[1/2,1]$, $t\in[10^6,\,10^6+3/1000]$.
--
--   One record of the framework structure `Arb4.SlabD`: Euler–Maclaurin cut $N=300001$, log bound, budget radius, the slab bounds, and 10 cells (`Arb4.CellD`) covering the slab. The data were produced by a program and are not trusted; each cell is checked by the kernel in `RHX1000000.Slab.cell_00` … `cell_09`, the slab-level conditions in `RHX1000000.Slab.clear`.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_Arb4_Slab
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q
namespace RHX1000000.Slab
noncomputable def S : SlabD where
  tq := 14
  N := 300001
  L := (Q.frac 12612 1000)
  R := (Q.frac 251 10000)
  lo := (Q.ofNat 1000000)
  hi := (Q.add (Q.ofNat 1000000) (Q.frac 3 1000))
  U := (Q.frac 1000001 1)
  Qr := 1000000039409500715575035301368031751784218700384573634784580447291108796859557
  r0 := 547
  FN := 512342
  FD := 1000000
  m := 10
  xs := fun j => [(Q.frac 10 20),
    (Q.frac 11 20),
    (Q.frac 12 20),
    (Q.frac 13 20),
    (Q.frac 14 20),
    (Q.frac 15 20),
    (Q.frac 16 20),
    (Q.frac 17 20),
    (Q.frac 18 20),
    (Q.frac 19 20),
    (Q.frac 20 20)].getD j (Q.frac 20 20)
  cell := fun j => [{ a := 21, b := 0, q := 40, tn := 16384000025, rn := 251, rd := 10000, w := (Q.frac 1 40), hh := (Q.frac 25 16384) },
    { a := 23, b := 0, q := 40, tn := 16384000025, rn := 251, rd := 10000, w := (Q.frac 1 40), hh := (Q.frac 25 16384) },
    { a := 5, b := 0, q := 8, tn := 16384000025, rn := 251, rd := 10000, w := (Q.frac 1 40), hh := (Q.frac 25 16384) },
    { a := 27, b := 0, q := 40, tn := 16384000025, rn := 251, rd := 10000, w := (Q.frac 1 40), hh := (Q.frac 25 16384) },
    { a := 29, b := 0, q := 40, tn := 16384000025, rn := 251, rd := 10000, w := (Q.frac 1 40), hh := (Q.frac 25 16384) },
    { a := 31, b := 0, q := 40, tn := 16384000025, rn := 251, rd := 10000, w := (Q.frac 1 40), hh := (Q.frac 25 16384) },
    { a := 33, b := 0, q := 40, tn := 16384000025, rn := 251, rd := 10000, w := (Q.frac 1 40), hh := (Q.frac 25 16384) },
    { a := 7, b := 0, q := 8, tn := 16384000025, rn := 251, rd := 10000, w := (Q.frac 1 40), hh := (Q.frac 25 16384) },
    { a := 37, b := 0, q := 40, tn := 16384000025, rn := 251, rd := 10000, w := (Q.frac 1 40), hh := (Q.frac 25 16384) },
    { a := 39, b := 0, q := 40, tn := 16384000025, rn := 251, rd := 10000, w := (Q.frac 1 40), hh := (Q.frac 25 16384) }].getD j { a := 39, b := 0, q := 40, tn := 16384000025, rn := 251, rd := 10000, w := (Q.frac 1 40), hh := (Q.frac 25 16384) }
end RHX1000000.Slab

def RHX_Slab1000000Data : Nat := 0


