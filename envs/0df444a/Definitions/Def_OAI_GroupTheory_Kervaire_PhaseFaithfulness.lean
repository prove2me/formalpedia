-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
-- name    : OAI_GroupTheory_Kervaire_PhaseFaithfulness
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:33:09.378163+00:00
-- url     : https://prove2.me/theorems/51e5e83d-b2a1-4ff6-87f6-ca7fd8ca5fb6
-- title:
--   Adjoints of left translations
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   This module adds the adjoint rule for left translations,
--   $$
--   L(a)^*=L(a^{-1}).
--   $$
--   It is used to show that the group phase is faithful. The phase $\mathrm{gph}_z(a)$ takes its extreme value only when $a=1$, which turns phase inequalities into the conclusion that a corner coefficient is trivial.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseFaithfulness.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PhaseFaithfulness.lean by skeleton subtraction
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
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireRegular
open KervaireSpectral
open scoped ComplexOrder
variable {A : Type*} [Group A]

@[simp] theorem star_leftOperator (a : A) : star (leftOperator a) = leftOperator a⁻¹ := by
  change ContinuousLinearMap.adjoint (left a).toContinuousLinearEquiv.toContinuousLinearMap = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  ext f x
  simp [leftOperator, left, reindex_symm, reindex_apply]

end KervaireRegular

namespace KervaireSpectral
open KervaireTraceCalculus
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end KervaireSpectral

end

end OAI


