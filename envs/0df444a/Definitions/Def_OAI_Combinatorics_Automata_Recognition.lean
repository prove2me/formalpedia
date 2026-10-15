-- Prove2me | Definitions.Def_OAI_Combinatorics_Automata_Recognition
-- name    : OAI_Combinatorics_Automata_Recognition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:07:35.550656+00:00
-- url     : https://prove2.me/theorems/4c1aff16-bb94-445d-a42d-8b73d3123147
-- title:
--   The separation test on diagrams for a two-way automaton
-- statement:
--   Let $M$ be a deterministic two-way automaton with finite state set $Q$ and initial state $q_0$, and let $f\in Q$ be a distinguished finish state. Ports are pairs $(\sigma,\ell)$ of a slot $\sigma=(d,p,q)$ (a direction bit and two states) and a lane bit $\ell$. Diagrams are perfect matchings of (left ports) $\sqcup$ (right ports), multiplied by gluing. $D_\triangleright$ and $D_\triangleleft$ are the body diagrams of the two endmarker cells of $M$.
--
--   For a diagram $a$, the recognition test is the proposition
--   $$
--   \mathrm{Test}_{M,f}(a)\ :\iff\ \neg\,\exists\,l,r:\ \ D_\triangleright\,a\,D_\triangleleft\ \text{is compatible with }(l,r)\ \text{ and }\ (l,r)\ \text{is separated}.
--   $$
--   Here $l$ and $r$ are Boolean colorings of the left and right ports. Compatibility means that any two ports matched by the diagram receive equal colors. The pair $(l,r)$ is separated if both colorings are flat (the two lanes of every slot get the same color), $l(\sigma^\ast,0)=0$ and $r(\sigma^\ast,0)=1$, where $\sigma^\ast=(\mathrm{right},q_0,f)$ is the test slot.
--
--   The test inspects only the diagram, so it is a predicate on the diagram monoid. Later results apply it to the product $a=D_{w_1}\cdots D_{w_n}$ of the letter diagrams of a word $w$. Provided $f$ has no transition on the right endmarker, the test then holds exactly when $M$ can get from configuration $(0,q_0)$ to $(n+1,f)$. Thus any deterministic two-way automaton recognizing a language yields a recognition of that language by a monoid of matchings, which is the input to the algebraic lower bound.
--
--   **Formalization Note** The test is `CellNetwork.recognitionTest M finish a`, where `a : Pairing (Port Q ⊕ Port Q)`. The products are taken in the monoid structure on `Pairing (A ⊕ A)`, and the separation condition is `Separated M finish l r`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Recognition.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Recognition.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the OneWayLiveness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations
import Definitions.Def_OAI_Combinatorics_Automata_RankLoss

namespace OAI

namespace OneWayLiveness

namespace CellNetwork
variable {Alpha Q : Type} [Fintype Q] (M : Machine Alpha Q)

noncomputable def recognitionTest (finish : Q) (a : Pairing (Port Q ⊕ Port Q)) : Prop :=
  ¬ ∃ l r, (bodyDiagram M finish .left * a * bodyDiagram M finish .right).Compatible
    (Sum.elim l r) ∧ Separated M finish l r

end CellNetwork

namespace Machine
variable {H Q : Type} [Fintype H] [Fintype Q] (M : Machine (BRel H) Q)

end Machine

end OneWayLiveness

end OAI


