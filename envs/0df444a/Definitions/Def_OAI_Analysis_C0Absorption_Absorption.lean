-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Absorption
-- name    : OAI_Analysis_C0Absorption_Absorption
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:50:55.494451+00:00
-- url     : https://prove2.me/theorems/f329bc28-239c-467c-bd68-07906ba29c61
-- title:
--   The concrete absorption map and the embedding of c0
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. Let $Z$ be the concrete space, $Q:Z\to C_0(\mathrm{Labels})$ the correction operator, and $c_0\cong c_0\times C_0(\mathrm{Labels})$ the coordinate splitting.
--
--   1. **Lift and shift on pairs.** $\mathrm{absorptionK}(x,y)$ is the radial lift of the joined point in $c_0$. $\mathrm{absorptionG}(x,y)$ is the recomputed shift of the joined point.
--   2. **Absorption map.** For $z\in Z$ and $x\in c_0$,
--   $$
--   F(z,x)=z+\mathrm{absorptionK}\bigl(x,Qz\bigr),
--   $$
--   the triangular absorption map $Z\times c_0\to Z$.
--   3. **Embedding.** $x\mapsto F(0,x)$ is the bi-Lipschitz embedding of $c_0$ into $Z$.
--
--   These are the maps realizing $Z\times c_0\simeq_{\mathrm{Lip}}Z$ and $c_0\hookrightarrow_{\mathrm{Lip}}Z$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Absorption.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Absorption.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Definitions.Def_OAI_Analysis_C0Absorption_Detection
import Definitions.Def_OAI_Analysis_C0Absorption_Grid
import Definitions.Def_OAI_Analysis_C0Absorption_Weights
import Definitions.Def_OAI_Analysis_C0Absorption_Angles
import Definitions.Def_OAI_Analysis_C0Absorption_Blocks
import Definitions.Def_OAI_Analysis_C0Absorption_Correction
import Definitions.Def_OAI_Analysis_C0Absorption_Frozen
import Definitions.Def_OAI_Analysis_C0Absorption_Tags
import Definitions.Def_OAI_Analysis_C0Absorption_Operators
import Definitions.Def_OAI_Analysis_C0Absorption_Shift
import Definitions.Def_OAI_Analysis_C0Absorption_Space
import Definitions.Def_OAI_Analysis_C0Absorption_Finite
import Definitions.Def_OAI_Analysis_C0Absorption_FiniteShift
import Definitions.Def_OAI_Analysis_C0Absorption_Onto

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

def absorptionK (x : C0 × BlockC0) : ConcreteSpace := concreteLift (inputCoordinates x)
def absorptionG (x : C0 × BlockC0) : BlockC0 := recomputedShift (inputCoordinates x)

def concreteAbsorption : ConcreteSpace × C0 → ConcreteSpace := absorptionMap correctionQ absorptionK

def concreteC0Embedding (x : C0) : ConcreteSpace := concreteAbsorption (0,x)

end
end C0Absorption

end OAI


