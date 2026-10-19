-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
-- name    : OAI_GroupTheory_Kervaire_ScalarPhase
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:11:34.491562+00:00
-- url     : https://prove2.me/theorems/40aaf5d9-2537-4ef1-8367-ab05fde9a037
-- title:
--   Scalar fractional phase and its regularization
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Fractional phase.** $\mathrm{ph}(z)=\{\arg z/2\pi\}\in[0,1)$.
--   2. **Cut approach.** $(1-\varepsilon^2)+\varepsilon i$, approaching $1$ from above the cut.
--   3. **Smooth phase.** For $|a|<1$,
--   $$
--   \mathrm{ph}_a(z)=\frac12+\frac{\arg(1-az)}\pi .
--   $$
--   For $|z|=1$ it tends to $\mathrm{ph}(z)$ as $a\to1$ from the correct side. Note that $\mathrm{Re}(1-az)>0$.
--   4. **Cut times.** $1/(n+2)$, a sequence used to approach the cut.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/ScalarPhase.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/ScalarPhase.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireScalarPhase

def phase (z : ℂ) : ℝ := Int.fract (z.arg / (2 * Real.pi))

@[simp] theorem phase_one : phase 1 = 0 := by simp [phase]

/-- Tangential approach to the phase cut, from the prescribed side. -/
def cutApproach (ε : ℝ) : ℂ := (1 - ε ^ 2 : ℝ) + ε * Complex.I

/-- The regularization used in the trace inequality. -/
def smoothPhase (a z : ℂ) : ℝ := 1 / 2 + (1 - a * z).arg / Real.pi

theorem re_one_sub_mul_pos {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    0 < (1 - a * z).re := by
  have h : (a*z).re < 1 := (Complex.re_le_norm _).trans_lt
    ((norm_mul_le a z).trans_lt <| by nlinarith [norm_nonneg a, norm_nonneg z])
  simpa using sub_pos.mpr h

/-- A concrete sequence in the open disk approaching the required side of the cut. -/
def cutTime (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

end KervaireScalarPhase

end

end OAI


