-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
-- name    : OAI_GroupTheory_Kervaire_PhaseDimension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:36:38.550983+00:00
-- url     : https://prove2.me/theorems/16e5c9bf-3c51-41dd-9255-cd4f1bfb37de
-- title:
--   Bases adapted to a subspace
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Adapted basis.** For a closed subspace $E$ of a Hilbert space, a basis obtained by joining orthonormal bases of $E$ and $E^\perp$, indexed by the disjoint union of the two index sets.
--   2. **Orthonormal version.** The same basis as an orthonormal basis.
--
--   With such bases, the summed phase of a unitary $U$ fixing $E$ satisfies
--   $$
--   \mathrm{Ph}(U)+\mathrm{Ph}(U^*)\le\operatorname{codim}E .
--   $$
--   Phases of unitary conjugates and involutions are bounded similarly in terms of fixed spaces.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseDimension.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PhaseDimension.lean by skeleton subtraction
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
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness

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
open scoped ComplexOrder

namespace KervaireSpectral

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- A basis adapted to a subspace and its orthogonal complement. -/
def orthogonalPairBasis (E : Submodule ℂ H) :
    Module.Basis (Fin (Module.finrank ℂ E) ⊕ Fin (Module.finrank ℂ Eᗮ)) ℂ H :=
  ((stdOrthonormalBasis ℂ E).toBasis.prod (stdOrthonormalBasis ℂ Eᗮ).toBasis).map
    (E.prodEquivOfIsCompl Eᗮ E.isCompl_orthogonal)

@[simp] theorem orthogonalPairBasis_inl (E : Submodule ℂ H) (i : Fin (Module.finrank ℂ E)) :
    orthogonalPairBasis E (.inl i) = (stdOrthonormalBasis ℂ E i : H) := by
  simp [orthogonalPairBasis, Module.Basis.map_apply, Module.Basis.prod_apply,
    Submodule.coe_prodEquivOfIsCompl']

@[simp] theorem orthogonalPairBasis_inr (E : Submodule ℂ H) (i : Fin (Module.finrank ℂ Eᗮ)) :
    orthogonalPairBasis E (.inr i) = (stdOrthonormalBasis ℂ Eᗮ i : H) := by
  simp [orthogonalPairBasis, Module.Basis.map_apply, Module.Basis.prod_apply,
    Submodule.coe_prodEquivOfIsCompl']

theorem orthogonalPairBasis_orthonormal (E : Submodule ℂ H) :
    Orthonormal ℂ (orthogonalPairBasis E) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simpa only [orthogonalPairBasis_inl, Submodule.coe_inner,
      Sum.inl.injEq] using (orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ E).orthonormal) i j
  · simp only [orthogonalPairBasis_inl, orthogonalPairBasis_inr, reduceCtorEq, ↓reduceIte]
    exact (stdOrthonormalBasis ℂ Eᗮ j).property _ (stdOrthonormalBasis ℂ E i).property
  · simp only [orthogonalPairBasis_inl, orthogonalPairBasis_inr, reduceCtorEq, ↓reduceIte]
    exact inner_eq_zero_symm.mp
      ((stdOrthonormalBasis ℂ Eᗮ i).property _ (stdOrthonormalBasis ℂ E j).property)
  · simpa only [orthogonalPairBasis_inr, Submodule.coe_inner,
      Sum.inr.injEq] using (orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ Eᗮ).orthonormal) i j

/-- The normalized basis is orthonormal. -/
def orthogonalPairONB (E : Submodule ℂ H) :
    OrthonormalBasis (Fin (Module.finrank ℂ E) ⊕ Fin (Module.finrank ℂ Eᗮ)) ℂ H :=
  (orthogonalPairBasis E).toOrthonormalBasis (orthogonalPairBasis_orthonormal E)

@[simp] theorem orthogonalPairONB_inl (E : Submodule ℂ H) (i : Fin (Module.finrank ℂ E)) :
    orthogonalPairONB E (.inl i) = (stdOrthonormalBasis ℂ E i : H) := by
  simp [orthogonalPairONB, Module.Basis.coe_toOrthonormalBasis]

@[simp] theorem orthogonalPairONB_inr (E : Submodule ℂ H) (i : Fin (Module.finrank ℂ Eᗮ)) :
    orthogonalPairONB E (.inr i) = (stdOrthonormalBasis ℂ Eᗮ i : H) := by
  simp [orthogonalPairONB, Module.Basis.coe_toOrthonormalBasis]

end

section
open KervaireTraceCalculus
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

end

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
variable {ι : Type*} [Fintype ι]

end KervaireSpectral

namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireTraceCalculus
open scoped Classical
variable {D A : Type*} [Fintype D] [Group A]

omit [Group A] in
@[simp] theorem scalarTensor_pow (M : Matrix D D ℂ) (n : ℕ) :
    scalarTensor (A := A) (M^n) = scalarTensor M ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, scalarTensor_mul, ih, pow_succ]

end KervaireMatrix

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

end KervaireSpectral

end

end OAI


