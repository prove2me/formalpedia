-- Prove2me | Definitions.Def_CutwidthCircuitLB_ROBP_Unambiguous
-- name    : CutwidthCircuitLB_ROBP_Unambiguous
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:28:38.527355+00:00
-- url     : https://prove2.me/theorems/b1a2ab88-b0e4-401a-9628-1841a359e713
-- title:
--   Unambiguous read-once program
-- statement:
--   A read-once program is **unambiguous** if every accepted input is consistent with exactly one start-to-accept path.
--
--   **Formalization Note** Paths are counted with multiplicity: two parallel edges give two different paths.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.2, p.7

import Mathlib
import Definitions.Def_CutwidthCircuitLB_ROBP
import Definitions.Def_CutwidthCircuitLB_ROBP_IsAcceptingPath
import Definitions.Def_CutwidthCircuitLB_ROBP_Accepts

namespace CutwidthCircuitLB

/-- A read-once program is **unambiguous** if every accepted input is consistent with exactly one
start-to-accept path (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Definition 2.2, p.7).

**Formalization Note** A path is its vertex sequence together with its choice of edge in every
transition layer, so two parallel edges give two different paths (multiplicity). -/
def ROBP.Unambiguous {n : ℕ} (R : ROBP n) : Prop :=
  ∀ x : Fin n → Bool, R.Accepts x →
    ∃! p : ((i : Fin (R.len + 1)) → Fin (R.layerSize i)) × ((t : Fin R.len) → Fin (R.edges t).length),
      R.IsAcceptingPath p.1 p.2 x

end CutwidthCircuitLB


