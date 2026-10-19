-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
-- name    : OAI_GroupTheory_Kervaire_StrongLimits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:06:55.206478+00:00
-- url     : https://prove2.me/theorems/37a0a3ee-3b24-464d-aa87-8e4e2a6eba83
-- title:
--   Strong convergence of operators
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Operators.** Bounded complex-linear operators on a normed space $H$.
--   2. **Strong convergence.** A family $T_i$ converges strongly to $S$ along a filter if
--   $$
--   T_i\xi\to S\xi\qquad\text{for every vector }\xi .
--   $$
--   Strong limits of power series in a unitary are used to build its spectral logarithm and phase operator.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/StrongLimits.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/StrongLimits.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Kervaire mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace KervaireStrong
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {ι : Type*} {l : Filter ι}
abbrev Operator (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] := H →L[ℂ] H

def StrongTendsto (T : ι → Operator H) (l : Filter ι) (S : Operator H) : Prop :=
  ∀ ξ, Tendsto (fun i => T i ξ) l (𝓝 (S ξ))

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
open scoped ComplexOrder

end KervaireStrong

end

end OAI


