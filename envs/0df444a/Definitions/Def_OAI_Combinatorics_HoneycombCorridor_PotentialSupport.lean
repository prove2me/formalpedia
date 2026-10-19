-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
-- name    : OAI_Combinatorics_HoneycombCorridor_PotentialSupport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:33:38.436165+00:00
-- url     : https://prove2.me/theorems/82c0c180-a7a0-41d5-9ce5-920b88d765a1
-- title:
--   Slot components of rational edge chains
-- statement:
--   Edges of the honeycomb lattice are indexed by pairs $(a,k)$ with a face index $a\in\mathbb Z^2$ and a slot $k\in\{0,1,2\}$.
--
--   For a finitely supported rational edge chain $q$ and a slot $k$, the rational flow component is the finitely supported face function
--   $$
--   q^{(k)}(a)=q(a,k),
--   $$
--   obtained by restricting $q$ to the edges of direction $k$. These components turn an edge chain into the triple $(q^{(0)},q^{(1)},q^{(2)})$ used to describe honeycomb flows and their face potentials over $\mathbb Q$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/PotentialSupport.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/PotentialSupport.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HoneycombBridgeFiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def rationalFlowComponent (q : EdgeIndex →₀ ℚ) (k : Fin 3) : FaceIndex →₀ ℚ :=
  Finsupp.comapDomain (fun a => (a,k)) q (by intro a _ b _ h; exact (Prod.mk.inj h).1)

end PolynomialVacuumBridge.Corridor

end

end OAI


