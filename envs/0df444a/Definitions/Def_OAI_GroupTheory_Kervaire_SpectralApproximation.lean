-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
-- name    : OAI_GroupTheory_Kervaire_SpectralApproximation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:15:43.880249+00:00
-- url     : https://prove2.me/theorems/a5bde259-4109-4b08-91d6-edb771be46b4
-- title:
--   Spectral logarithm and smooth phase on the unitary spectrum
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   For a unitary $U$ and $|a|<1$:
--
--   1. **Spectral logarithm.** The continuous function $z\mapsto-\log(1-az)$ on $\operatorname{spec}U$, the Mercator logarithm. Its functional calculus is the strong sum of $\sum a^nU^n/n$.
--   2. **Spectral smooth phase.** The continuous function $z\mapsto\frac12+\arg(1-az)/\pi$ on $\operatorname{spec}U$.
--
--   As $a$ approaches $1$ along the cut times, the smooth phases converge to the fractional phase $\mathrm{ph}$ pointwise on the circle. Then
--   $$
--   \langle\xi,\mathrm{ph}_a(U)\xi\rangle\to\mathrm{ph}_\xi(U).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/SpectralApproximation.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/SpectralApproximation.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Mercator logarithm is continuous on the unitary spectrum. -/
def spectralLog (U : Operator H) (hU : U ∈ unitary (Operator H)) (a : ℂ)
    (ha : ‖a‖ < 1) : C(spectrum ℂ U, ℂ) :=
  ⟨fun z => -Complex.log (1 - a * z), by
    apply Continuous.neg
    apply Continuous.clog
    · fun_prop
    · intro z
      apply Complex.mem_slitPlane_iff.mpr
      exact Or.inl (re_one_sub_mul_pos ha
        (CStarRing.norm_of_mem_unitary
          (spectrum_subset_unitary_of_mem_unitary hU z.property)).le)⟩

/-- The regularized scalar phase is continuous on the unitary spectrum. -/
def spectralSmooth (U : Operator H) (hU : U ∈ unitary (Operator H))
    (a : ℂ) (ha : ‖a‖ < 1) : C(spectrum ℂ U, ℝ) :=
  ⟨fun z => smoothPhase a z, by
    have hc : Continuous (fun z : spectrum ℂ U =>
        1 / 2 - (spectralLog U hU a ha z).im / Real.pi) := by
      exact continuous_const.sub
        ((Complex.continuous_im.comp (spectralLog U hU a ha).continuous).div_const _)
    simpa [spectralLog, smoothPhase, Complex.log_im, sub_eq_add_neg, neg_div]
      using hc⟩

@[simp] theorem complexify_one {X : Type*} [TopologicalSpace X] :
    complexify (1 : C(X, ℝ)) = 1 := by ext; simp [complexify]

end KervaireSpectral

end

end OAI


