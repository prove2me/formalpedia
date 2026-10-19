-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Detection
-- name    : OAI_Analysis_C0Absorption_Detection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:13:37.612709+00:00
-- url     : https://prove2.me/theorems/726234a4-6f6c-4292-815d-59bc830ab628
-- title:
--   Relabelling generated representations
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. A generated representation for an index $\gamma$ of a family of cylinder bases is a list of cylinder operations with nonincreasing scales, within the budget of the band of $\gamma$. Applied to the base function of $\gamma$, it produces a test function on the unit ball of $c_0$.
--
--   If $\gamma=\gamma'$, a representation for $\gamma$ can be transported to one for $\gamma'$:
--   $$
--   \mathrm{relabel}(r,\gamma=\gamma'),
--   $$
--   with the same number of operations and the same value function. This bookkeeping lets detectors built for one index be compared with representations of an equal index.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Detection.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Detection.lean by skeleton subtraction
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

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
variable {Γ : Type*} {B : CylinderBases Γ}

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
variable {Γ : Type*} {B : CylinderBases Γ}

namespace GeneratedRepresentation

def relabel {γ γ' : Γ} (r : GeneratedRepresentation B γ) (he : γ=γ') : GeneratedRepresentation B γ' := he ▸ r

@[simp] theorem relabel_length {γ γ' : Γ} (r : GeneratedRepresentation B γ) (he : γ=γ') :
    (r.relabel he).operations.length=r.operations.length := by subst γ'; rfl

@[simp] theorem relabel_value {γ γ' : Γ} (r : GeneratedRepresentation B γ) (he : γ=γ') :
    (r.relabel he).value=r.value := by subst γ'; rfl
end GeneratedRepresentation

end
end C0Absorption

end OAI


