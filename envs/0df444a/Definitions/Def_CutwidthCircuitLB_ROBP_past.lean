-- Prove2me | Definitions.Def_CutwidthCircuitLB_ROBP_past
-- name    : CutwidthCircuitLB_ROBP_past
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:25.590806+00:00
-- url     : https://prove2.me/theorems/b7bc5414-c513-4043-8359-329ff8aa2e6a
-- title:
--   Past of a layer of a read-once program
-- statement:
--   The **past** of the layer $V_i$ of a read-once program is the set of variables queried in the transition layers $1, \dots, i$; its **future** consists of the remaining variables. Since every variable tags exactly one query layer, past and future partition $\{1, \dots, n\}$.
--
--   **Formalization Note** The future of $V_i$ is written as the complement of its past.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.2, p.7

import Mathlib
import Definitions.Def_CutwidthCircuitLB_ROBP

namespace CutwidthCircuitLB

/-- The **past** of the layer `V_i` of a read-once program: the variables queried in transition
layers `1, …, i` (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Definition 2.2, p.7). Its **future** is the complement `(past i)ᶜ`.

**Formalization Note** With 0-based transition layers, these are the variables tagging a layer
`t < i`. -/
def ROBP.past {n : ℕ} (R : ROBP n) (i : Fin (R.len + 1)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => ∃ t : Fin R.len, t.val < i.val ∧ R.tag t = some j)

end CutwidthCircuitLB


