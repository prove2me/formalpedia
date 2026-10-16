-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
-- name    : OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:10:33.625987+00:00
-- url     : https://prove2.me/theorems/1de7ef7d-9d14-49cb-83ae-ab61a6d23a2d
-- title:
--   Selector-table coordinates read at a centre, indexed by bounded tree addresses
-- statement:
--   Fix $M, d \in \mathbb{N}$. Children are $0,1,\dots,M$, the letter $M$ being the default child. A *bounded address* is a pair $(P,i)$ where $P$ is a word over $\{0,\dots,M\}$ with $|P| < d$ (a node) and $i \in \{0,\dots,M-1\}$ (a selector at that node). Let $b$ assign a resolution $b(P,i) \in \mathbb{N}$ to every such pair, so that the selector table of $(P,i)$ has coordinates $((P,i),j)$ with $0 \le j < 2^{b(P,i)+2}$, and for $x \in \mathbb{R}$ let $\kappa_n(x) = \lfloor 2^{n+2}\{x\} \rfloor$ be the dyadic key, where $\{x\} = x - \lfloor x \rfloor$.
--
--   The *centre table address* at the centre $x$ sends a bounded address to the selector-table coordinate that the point $x$ reads:
--   $$
--   (P,i) \longmapsto \alpha_b(P,i,x) = \big((P,i),\ \kappa_{b(P,i)}(x)\big).
--   $$
--
--   This map transfers the abstract computation of the probability of avoiding the default child, which is stated for an independent family of fair bits indexed by bounded addresses, to the concrete selector table: for a random table $\omega$, the family $(P,i) \mapsto \omega(\alpha_b(P,i,x))$ consists of the bits read at the fixed centre $x$, and these are distinct coordinates of the table because the map is injective.
--
--   **Formalization Note** Bounded addresses are the subtype `FirstDefault.BoundedAddress M d` of `List (Fin (M + 1)) × Fin M`; the definition repackages such an address as a node of `FiniteTableModel.Node M d` and applies `selectorAddress`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/CenterFirstDefault.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/CenterFirstDefault.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DyadicAvoidance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_T

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem310.FiniteTableModel

/-- Center-table coordinate in the bounded-address convention used by the
first-default probability theorem. -/
def centerTableAddress {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ)
    (a : FirstDefault.BoundedAddress M d) : SelectorAddress b :=
  selectorAddress b ⟨a.1.1, a.2⟩ a.1.2 x

end Problem310.FiniteTableModel

end

end OAI


