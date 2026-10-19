-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
-- name    : OAI_GroupTheory_Kervaire_PhaseNaturality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:18:23.19945+00:00
-- url     : https://prove2.me/theorems/f8a05cf3-1a67-4120-9118-012672596284
-- title:
--   Scalar rotations
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Scalar rotation.** For $x\in\mathbb R$,
--   $$
--   \mathrm{rot}(x)=e^{2\pi ix},
--   $$
--   a unit complex number with $\mathrm{rot}(0)=1$, $\mathrm{rot}(x+y)=\mathrm{rot}(x)\mathrm{rot}(y)$ and $\overline{\mathrm{rot}(x)}=\mathrm{rot}(-x)$.
--
--   Multiplying a unitary by $\mathrm{rot}(x)$ shifts its spectrum by angle $2\pi x$, which changes fractional phases in a controlled way.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseNaturality.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PhaseNaturality.lean by skeleton subtraction
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

namespace KervaireSpectral

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

def scalarRotation (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[simp] theorem scalarRotation_zero : scalarRotation 0 = 1 := by simp [scalarRotation]

@[simp] theorem norm_scalarRotation (x : ℝ) : ‖scalarRotation x‖ = 1 := by
  simp [scalarRotation, Complex.norm_exp]

@[simp] theorem scalarRotation_add (x y : ℝ) :
    scalarRotation (x+y) = scalarRotation x * scalarRotation y := by
  simp only [scalarRotation, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

@[simp] theorem star_scalarRotation (x : ℝ) : star (scalarRotation x) = scalarRotation (-x) := by
  unfold scalarRotation
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg,
    mul_neg, neg_mul]

theorem scalarRotation_unitary (x : ℝ) : scalarRotation x ∈ unitary ℂ := by
  rw [Unitary.mem_iff]
  simp only [star_scalarRotation, ← scalarRotation_add, neg_add_cancel, add_neg_cancel,
    scalarRotation_zero, and_self]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end KervaireSpectral

end

end OAI


