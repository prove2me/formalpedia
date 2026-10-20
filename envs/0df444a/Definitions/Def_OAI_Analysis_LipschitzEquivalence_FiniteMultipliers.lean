-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
-- name    : OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:47:30.471992+00:00
-- url     : https://prove2.me/theorems/35379132-e80b-44e4-9df7-642a289ff02d
-- title:
--   Radial and finite-set multipliers on free spaces
-- statement:
--   Concrete multiplier operators on $\mathcal F(M)$ built from cutoffs, for a radius $R\ge0$, a finite set $A\subseteq M$ and a scale $\delta>0$.
--
--   1. **Radial multiplier.** With outer radius $R'=2R+2$, the radial multiplier multiplies by the cutoff $\psi_{0,R'}$ about the base point.
--   2. **Finite-set cutoff.** The finite cutoff is
--   $$
--   \chi(x)=\psi_{2\delta}\bigl(\mathrm{dist}(x,A)\bigr)\cdot\psi_{0,R'}(x),
--   $$
--   with Lipschitz bound $2/R'+2/(2\delta)$. The finite multiplier multiplies by $\chi$, with operator bound $1+(2/R'+1/\delta)R'$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/FiniteMultipliers.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/FiniteMultipliers.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LipschitzEquivalence mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction

namespace OAI

universe uM uE

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

def outerRadius (R : ℝ≥0) : ℝ≥0 := 2*R+2

def radialMultiplier (R : ℝ≥0) : Space M →L[ℝ] Space M :=
  multiplier (cutoff 0 (outerRadius R))

def finiteCutoff (R : ℝ≥0) (A : Finset M) (δ : ℝ≥0) (x : M) : ℝ :=
  setCutoff (A : Set M) (2*δ) x * cutoff 0 (outerRadius R) x

def finiteCutoffLip (R δ : ℝ≥0) : ℝ≥0 := 2/(outerRadius R)+2/(2*δ)

def finiteMultiplier (R : ℝ≥0) (A : Finset M) (δ : ℝ≥0) : Space M →L[ℝ] Space M :=
  multiplier (finiteCutoff R A δ)

def finiteMultiplierBound (R δ : ℝ≥0) : ℝ≥0 := 1+finiteCutoffLip R δ * outerRadius R

end LipschitzCounterexample.FreeSpace

end

end OAI


