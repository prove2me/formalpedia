-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
-- name    : OAI_GroupTheory_Kervaire_SpectralLogarithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:10:26.632051+00:00
-- url     : https://prove2.me/theorems/ea34ddd3-9340-458b-b564-8f854492694d
-- title:
--   Vector functionals on operators
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Vector functional.** For a vector $\xi$, the continuous linear functional on bounded operators
--   $$
--   T\mapsto\langle\xi,T\xi\rangle .
--   $$
--   Sums of such functionals over finitely many vectors give the traces used to measure phases. Applied to the Mercator series $-\log(1-aU)=\sum_n a^nU^n/n$, they compute regularized logarithms of unitaries.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/SpectralLogarithm.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/SpectralLogarithm.lean by skeleton subtraction
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
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology

namespace KervaireSpectral

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open KervaireStrong

end

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The continuous vector functional on all bounded operators. -/
def vectorCLM (ξ : H) : Operator H →L[ℂ] ℂ :=
  (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ H ξ)

omit [CompleteSpace H] in
@[simp] theorem vectorCLM_apply (ξ : H) (T : Operator H) :
    vectorCLM ξ T = inner ℂ ξ (T ξ) := rfl

end KervaireSpectral

end

end OAI


