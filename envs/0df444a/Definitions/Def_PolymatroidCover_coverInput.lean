-- Prove2me | Definitions.Def_PolymatroidCover_coverInput
-- name    : PolymatroidCover_coverInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:39.201565+00:00
-- url     : https://prove2.me/theorems/61bedc8b-9912-4648-b305-ed80243d5614
-- title:
--   Input layout and output decoder for Theorem 1.1 on the oracle RAM
-- statement:
--   Theorem 1.1 is a statement about an algorithm that receives a **value oracle** for $f$. The mission fixes the published unit-cost value-oracle RAM `LSWNewArcAudit.NewArc` (real and integer registers, indirect integer memory, subset bitmaps written one bit at a time, a query instruction returning $f$ of a bitmap, and a halt instruction returning one integer pointer). The covering problem on the ground set $\{0, \dots, n-1\}$ is presented to it as follows:
--
--   1. **input**: integer memory cell $0$ holds $n$; all other cells are $0$; the polymatroid is available only through the oracle;
--   2. **output**: if the machine halts with pointer $p$, the color of element $e$ is the content of integer cell $p + e$.
--
--   **Formalization Note** The program is given neither $d$ nor $\chi^\circ(f)$ nor the target number of colors.
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, Theorem 1.1, p.3 (PDF p.5) (the paper fixes no machine)

import Mathlib
import Definitions.Def_LSWNewArcAudit_NewArc_OracleRAM

namespace PolymatroidCover

/-- The input layout for the covering problem of Theorem 1.1 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), printed p.3 = PDF p.5) on the
published oracle RAM `LSWNewArcAudit.NewArc`: integer cell `0` holds the size `n` of the
ground set `Fin n`; every other integer cell and every real cell is `0`. The polymatroid
itself is available only through the value oracle.

**Formalization Note** Nothing else is supplied: in particular not `d`, `χ°(f)` or the
target number of colors. -/
def coverInput (n : ℕ) : LSWNewArcAudit.NewArc.RAMInput :=
  ⟨fun z => if z = 0 then (n : ℤ) else 0, fun _ => 0⟩

/-- The output decoder for Theorem 1.1: a machine state `s` that halted with pointer `p`
outputs the coloring `e ↦ integerMemory (p + e)` of the ground set `Fin n` (color of the
element `e` stored in integer cell `p + e`). -/
def decodeColoring {n : ℕ} (s : LSWNewArcAudit.NewArc.OracleState n) (p : ℤ) : Fin n → ℤ :=
  fun e => s.integerMemory (p + (e : ℤ))

end PolymatroidCover


