-- Prove2me | Definitions.Def_ArdaRH65K_Slab65000Data
-- name    : ArdaRH65K_Slab65000Data
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:17:21.167884+00:00
-- url     : https://prove2.me/theorems/fdf09fbe-117f-4762-b813-4fd316512776
-- title:
--   Certified zero-free upper slab data at height 65000
-- statement:
--   This bundle records rational interval data for eight cells in the narrow slab immediately above the horizontal boundary. For the slab data $S$ and cell checker $C_j$, the relevant interval and finite conditions are
--
--   $$65000\leq\operatorname{Im}s\leq 65000+\frac{3}{1000},\qquad C_j(S)=\mathrm{true}\quad(0\leq j<8).$$
--
--   These data are used by the separate proofs that the slab is zero-free.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Arb4_Slab.lean

import Definitions.Def_ArdaRH65K_Turing121_Arb4_Slab
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q
namespace H65K.Slab
noncomputable def S : SlabD where
  tq := 14
  N := 19501
  L := (Q.frac 9879 1000)
  R := (Q.frac 417 10000)
  lo := (Q.ofNat 65000)
  hi := (Q.add (Q.ofNat 65000) (Q.frac 3 1000))
  U := (Q.frac 65001 1)
  Qr := 369800000000000000000000000000000000000000000000000000000000000
  r0 := 139
  FN := 81
  FD := 500
  m := 8
  xs := fun j => [(Q.frac 1 2), (Q.frac 25 48), (Q.frac 13 24), (Q.frac 7 12), (Q.frac 2 3), (Q.frac 3 4), (Q.frac 5 6), (Q.frac 11 12), (Q.frac 1 1)].getD j (Q.frac 1 1)
  cell := fun j => [{ a := 49, b := 0, q := 96, tn := 1064960025, rn := 106, rd := 10000, w := (Q.frac 1 96), hh := (Q.frac 25 16384) },
    { a := 17, b := 0, q := 32, tn := 1064960025, rn := 106, rd := 10000, w := (Q.frac 1 96), hh := (Q.frac 25 16384) },
    { a := 9, b := 0, q := 16, tn := 1064960025, rn := 209, rd := 10000, w := (Q.frac 1 48), hh := (Q.frac 25 16384) },
    { a := 5, b := 0, q := 8, tn := 1064960025, rn := 417, rd := 10000, w := (Q.frac 1 24), hh := (Q.frac 25 16384) },
    { a := 17, b := 0, q := 24, tn := 1064960025, rn := 417, rd := 10000, w := (Q.frac 1 24), hh := (Q.frac 25 16384) },
    { a := 19, b := 0, q := 24, tn := 1064960025, rn := 417, rd := 10000, w := (Q.frac 1 24), hh := (Q.frac 25 16384) },
    { a := 7, b := 0, q := 8, tn := 1064960025, rn := 417, rd := 10000, w := (Q.frac 1 24), hh := (Q.frac 25 16384) },
    { a := 23, b := 0, q := 24, tn := 1064960025, rn := 417, rd := 10000, w := (Q.frac 1 24), hh := (Q.frac 25 16384) }].getD j { a := 23, b := 0, q := 24, tn := 1064960025, rn := 417, rd := 10000, w := (Q.frac 1 24), hh := (Q.frac 25 16384) }
end H65K.Slab

def ArdaRH65K_Slab65000Data : Nat := 0


