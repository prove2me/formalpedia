-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
-- name    : OAI_GroupTheory_Kervaire_MatrixTrace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:24:23.08464+00:00
-- url     : https://prove2.me/theorems/91da48a7-eb7e-424b-838a-aea4387e0ba9
-- title:
--   Matrices over the group von Neumann algebra
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   For a finite set $D$ and a group $A$:
--
--   1. **Space.** $\ell^2(D\times A)$, a direct sum of $|D|$ copies of $\ell^2(A)$, with diagonal right translations $R(a)$.
--   2. **Matrix algebra.** The operators commuting with all $R(a)$, a closed $*$-algebra identified with $D\times D$ matrices over the group von Neumann algebra.
--   3. **Trace.** $\mathrm{Tr}(T)=\sum_{i\in D}\langle\delta_{(i,1)},T\delta_{(i,1)}\rangle$, which is tracial on the matrix algebra.
--   4. **Phase.** For a unitary $U$, the summed fractional phase
--   $$
--   \mathrm{Ph}(U)=\sum_{i\in D}\mathrm{ph}_{\delta_{(i,1)}}(U).
--   $$
--   It is subadditive on unitaries of the matrix algebra.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/MatrixTrace.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/MatrixTrace.lean by skeleton subtraction
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

namespace KervaireMatrix

section
open KervaireRegular
variable {D A : Type*} [Group A]
abbrev Space (D A : Type*) := ℓ²(D × A, ℂ)
abbrev Operator (D A : Type*) := Space D A →L[ℂ] Space D A

/-- Diagonal right translations on the finite multiple of the regular Hilbert space. -/
def right (a : A) : Space D A ≃ₗᵢ[ℂ] Space D A :=
  reindex (Equiv.prodCongr (Equiv.refl D) (Equiv.mulRight a⁻¹))

@[simp] theorem right_apply (a : A) (f : Space D A) (j : D) (x : A) :
    right a f (j,x) = f (j,x*a) := by simp [right]

@[simp] theorem right_delta (a x : A) (j : D) :
    right a (delta (j,x)) = delta (j,x*a⁻¹) := by simp [right]

@[simp] theorem right_star (a : A) :
    star (right (D := D) a : Operator D A) = (right (D := D) a⁻¹ : Operator D A) := by
  rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.adjoint_eq_symm]
  ext f ⟨j,x⟩
  simp [right, reindex_symm, reindex_apply]

/-- The finite matrix group von Neumann algebra, before bundling. -/
def InCommutant (T : Operator D A) : Prop := ∀ a : A, Commute T (right (D := D) a : Operator D A)

variable [Fintype D]

def trace : Operator D A →L[ℂ] ℂ :=
  ∑ i : D, (innerSL ℂ (delta (i,(1 : A)))).comp
    (ContinuousLinearMap.apply ℂ (Space D A) (delta (i,1)))

@[simp] theorem trace_apply (T : Operator D A) :
    trace T = ∑ i : D, inner ℂ (delta (i,1)) (T (delta (i,1))) := by simp [trace]

@[simp] theorem trace_eq_coefficient (T : Operator D A) :
    trace T = ∑ i : D, T (delta (i,1)) (i,1) := by simp

@[simp] theorem trace_one : trace (1 : Operator D A) = Fintype.card D := by
  classical
  simp [delta]

end

section
open KervaireRegular
variable {D A : Type*} [Fintype D] [Group A]

end

section
open KervaireRegular KervaireSpectral
variable {D A : Type*} [Group A]

/-- The closed algebra `M_D(M_A)` represented on the arbitrary-group Hilbert space. -/
def algebra : StarSubalgebra ℂ (Operator D A) :=
  KervaireCentralizer.algebra (Set.range (fun a : A => (right (D := D) a : Operator D A)))

variable [Fintype D]

/-- The regular Hilbert space is nonzero whenever the finite index set is inhabited. -/
instance [Nonempty D] : Nontrivial (Space D A) := by
  classical
  let i : D := Classical.choice inferInstance
  refine ⟨⟨delta (i,(1 : A)), 0, ?_⟩⟩
  intro h
  have hh := congrArg (fun f : Space D A => f (i,1)) h
  simp [delta] at hh

def phase (U : Operator D A) [IsStarNormal U] : ℝ :=
  sumPhase U (fun i : D => delta (i,(1 : A)))

end

open KervaireRegular KervaireSpectral
variable {D A : Type*} [Fintype D] [Group A]

end KervaireMatrix

end

end OAI


