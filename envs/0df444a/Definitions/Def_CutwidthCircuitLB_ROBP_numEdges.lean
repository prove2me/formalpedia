-- Prove2me | Definitions.Def_CutwidthCircuitLB_ROBP_numEdges
-- name    : CutwidthCircuitLB_ROBP_numEdges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:24.579502+00:00
-- url     : https://prove2.me/theorems/0c02bffa-8e59-4d14-9a93-b2d5198c60b1
-- title:
--   Number of edges of a read-once program
-- statement:
--   The **number of edges** $E$ of a read-once program is the total number of edges of its transition layers, counted with multiplicity.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.2 and Lemma 2.2, p.7

import Mathlib
import Definitions.Def_CutwidthCircuitLB_ROBP

namespace CutwidthCircuitLB

/-- The **number of edges** of a read-once program, counted with multiplicity (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3),
Definition 2.2 and Lemma 2.2, p.7). -/
def ROBP.numEdges {n : ℕ} (R : ROBP n) : ℕ :=
  ∑ t, (R.edges t).length

end CutwidthCircuitLB


