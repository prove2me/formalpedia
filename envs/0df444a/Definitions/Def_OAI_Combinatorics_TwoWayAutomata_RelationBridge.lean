-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationBridge
-- name    : OAI_Combinatorics_TwoWayAutomata_RelationBridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:53:11.495988+00:00
-- url     : https://prove2.me/theorems/0a35c176-0f65-42da-9dca-6ce07610a5b7
-- title:
--   Currying equivalence between predicate relations and set relations on a type
-- statement:
--   Let $H$ be a set. Binary relations on $H$ appear in two encodings. In the first, a relation is a two-argument predicate $\rho$ on $H$: for all $x,y\in H$, $\rho(x,y)$ is a proposition. In the second, a relation is a subset $R\subseteq H\times H$.
--
--   **Relation equivalence.** The maps
--   $$\rho\ \longmapsto\ \{(x,y)\in H\times H:\ \rho(x,y)\},\qquad R\ \longmapsto\ \big((x,y)\mapsto [\,(x,y)\in R\,]\big)$$
--   are mutually inverse; they are uncurrying and currying, and both composites are the identity by definition.
--
--   This bijection identifies the alphabet of all predicate relations on $H$, which is the input alphabet of a companion model of deterministic two-way machines for one-way liveness, with the alphabet of all set relations on $H$, which is the input alphabet of the two-way automata studied here. Pulling an automaton back along it changes only how the letters are encoded, not the number of states.
--
--   **Formalization Note** `CompanionBridge.relationEquiv H : BRel H ≃ SetRel H H`, where `BRel H` is the structure with the single field `holds : H → H → Prop` from the companion one-way liveness development (namespace `OAI.OneWayLiveness`), and `SetRel H H` is Mathlib's type of set-valued relations. Both inverse laws hold by `rfl`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/RelationBridge.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/RelationBridge.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayDeterminization mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Network__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Chain__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Tape__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Main

namespace OAI

namespace TwoWayComplementation.CompanionBridge

open OneWayLiveness
open scoped SetRel

/-- Exact currying/uncurrying equivalence of the two full relation alphabets. -/
def relationEquiv (H : Type*) : BRel H ≃ SetRel H H where
  toFun R := {xy | R.holds xy.1 xy.2}
  invFun R := ⟨fun x y => (x, y) ∈ R⟩
  left_inv _R := rfl
  right_inv _R := rfl

end TwoWayComplementation.CompanionBridge

end OAI


