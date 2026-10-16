-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
-- name    : OAI_MathematicalPhysics_SheetFlows_ScheduledForce
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T00:57:45.886288+00:00
-- url     : https://prove2.me/theorems/23874e94-cf23-49a4-8d81-c155d140ad8c
-- title:
--   Reduction of points of $\mathbb{R}^3$ to the periodic cell $[0,10)^3$
-- statement:
--   For $x=(x_0,x_1,x_2)\in\mathbb{R}^3$ this file defines the wrapped point
--   $$
--   W(x)=\Bigl(10\,\Bigl\{\frac{x_0}{10}\Bigr\},\ 10\,\Bigl\{\frac{x_1}{10}\Bigr\},\ 10\,\Bigl\{\frac{x_2}{10}\Bigr\}\Bigr),
--   $$
--   where $\{y\}=y-\lfloor y\rfloor\in[0,1)$ denotes the fractional part. Each coordinate of $W(x)$ lies in $[0,10)$, and $x-W(x)=10\,\bigl(\lfloor x_0/10\rfloor,\lfloor x_1/10\rfloor,\lfloor x_2/10\rfloor\bigr)$ belongs to the lattice $10\mathbb{Z}^3$; thus $W(x)$ is the representative, in the fundamental cell $[0,10)^3$, of the class of $x$ in the torus $\mathbb{R}^3/(10\mathbb{Z})^3$.
--
--   A function $g$ on $\mathbb{R}^3$ that is invariant under translations by $10\mathbb{Z}^3$ satisfies $g(x)=g(W(x))$, so its global behaviour is determined by its values on the compact cube $[0,10]^3$. The map $W$ performs this reduction for spatially periodic fields: it turns continuity on the cube into uniform bounds for such fields and all their derivatives, shows that a periodic field vanishing on the cell vanishes everywhere, and allows periodic fields to be evaluated through formulas that are valid on one period cell only.
--
--   **Formalization Note** The definition is `wrapSpace x = fun j => 10 * Int.fract (x j / 10)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/ScheduledForce.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/ScheduledForce.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SolenoidalSheetPrograms mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential

namespace OAI

/-! SheetFlows scheduled force. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

def wrapSpace (x : Space) : Space := fun j => 10 * Int.fract (x j / 10)

end Solenoidal
end
end

end OAI


