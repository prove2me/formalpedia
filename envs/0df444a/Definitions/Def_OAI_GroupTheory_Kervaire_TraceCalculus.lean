-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
-- name    : OAI_GroupTheory_Kervaire_TraceCalculus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:13:35.585735+00:00
-- url     : https://prove2.me/theorems/83ebb4c8-e750-494d-92a9-99ed64c3d25d
-- title:
--   Trace logarithms and smooth traced phases
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   Let $\tau$ be a continuous linear functional on a Banach algebra, typically a trace.
--
--   1. **Trace logarithm.** For $|a|<1$,
--   $$
--   \mathrm{TL}_\tau(a,U)=\sum_{n\ge0}\frac{a^{n+1}}{n+1}\,\tau(U^{n+1})=\tau\bigl(-\log(1-aU)\bigr).
--   $$
--   2. **Phase velocity.** $2\pi i\,B$, the generator with $e^{2\pi iB}=U$ for a phase operator $B$.
--   3. **Smooth traced phase.** $\frac{\mathrm{Re}\,\tau(1)}2-\frac{\mathrm{Im}\,\mathrm{TL}_\tau(a,U)}\pi$, the trace of the smooth phase of $U$. It is the regularization used to prove phase subadditivity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/TraceCalculus.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/TraceCalculus.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireTraceCalculus
open scoped Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedRing E]
  [NormedAlgebra 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Complex
variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

end Complex

section PositiveTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
open scoped ComplexOrder

local instance instContinuousFunctionalCalculusRealIsSelfAdjoint_oAI : ContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

end PositiveTrace
section RealPath
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- A regularized logarithm evaluated by a trace. -/
def traceLog (τ : A →L[ℂ] ℂ) (a : ℂ) (U : A) : ℂ :=
  ∑' n : ℕ, (a ^ (n + 1) / (n + 1)) * τ (U ^ (n + 1))

end RealPath
section Cayley
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end Cayley
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A]

/-- The derivative generator has the normalization used for fractional phase. -/
def phaseVelocity (B : A) : A := ((2 * Real.pi : ℂ) * Complex.I) • B

/-- A smooth trace approximation to the fractional spectral phase. -/
def smoothTrace (τ : A →L[ℂ] ℂ) (a : ℂ) (U : A) : ℝ :=
  (τ 1).re / 2 - (traceLog τ a U).im / Real.pi

end KervaireTraceCalculus

end

end OAI


