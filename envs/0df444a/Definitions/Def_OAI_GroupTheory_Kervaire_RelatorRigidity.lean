-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_RelatorRigidity
-- name    : OAI_GroupTheory_Kervaire_RelatorRigidity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:29:11.600823+00:00
-- url     : https://prove2.me/theorems/42993d05-4efb-4bc0-bc45-1604a0c4feec
-- title:
--   Corners and disk atlases of relator diagrams
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   Let the relator have positions $I$ in cyclic order $\rho$, coefficients $a:I\to A$ and signs $s$.
--
--   1. **Corner.** For permutations $\sigma,\theta$ of darts and potentials $u:D\to A$,
--   $$
--   \mathrm{corner}(d)=u(\theta d)\,u(\sigma d)^{-1}.
--   $$
--   2. **Vertex successor and corner.** On copies $(v,i)$ of the relator, the successor is $\rho$ on positively oriented copies and $\rho^{-1}$ on negative ones. The corner coefficient is $a_i$, respectively $a_{\rho^{-1}i}^{-1}$.
--   3. **Disk atlas.** An injection of $V\times I$ into the darts with polarities $\varepsilon_v=\pm1$. It intertwines the vertex successor with $\sigma$ and gives dart $(v,i)$ the sign $\varepsilon_vs_i$.
--
--   In a diagram, the corners at the relator disks equal the coefficients of the relator.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/RelatorRigidity.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/RelatorRigidity.lean by skeleton subtraction
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
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal
import Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]

/-- The coefficient on the corner immediately following a dart. -/
def corner (σ θ : Perm D) (u : D → A) (d : D) : A := u (θ d) * (u (σ d))⁻¹

end

section
open Equiv Equiv.Perm
open scoped Classical
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

omit [Fintype B] [DecidableEq B] in
lemma components_map (e : D → B) (σ θ : Perm D) (σ' θ' : Perm B)
    (hs : ∀ d, e (σ d) = σ' (e d)) (ht : ∀ d, e (θ d) = θ' (e d))
    {x y : D} (h : components σ θ x y) : components σ' θ' (e x) (e y) := by
  have hl : components σ θ ≤ (components σ' θ').comap e := by
    apply sup_le
    · apply cycle_le_of_step
      intro d
      change components σ' θ' (e (σ d)) (e d)
      rw [hs]
      exact (le_sup_left : SameCycle.setoid σ' ≤ components σ' θ') SameCycle.rfl.apply_left
    · apply cycle_le_of_step
      intro d
      change components σ' θ' (e (θ d)) (e d)
      rw [ht]
      exact (le_sup_right : SameCycle.setoid θ' ≤ components σ' θ') SameCycle.rfl.apply_left
  exact hl h

end

section
open Equiv Equiv.Perm
open scoped Classical
variable {V I D : Type*} [Fintype V] [Fintype I] [Fintype D]

end

open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

def vertexNext (ρ : Perm I) (ε : V → ℤ) (p : V × I) : V × I :=
  (p.1, if ε p.1 = 1 then ρ p.2 else ρ.symm p.2)
def vertexCorner (ρ : Perm I) (a : I → A) (ε : V → ℤ) (p : V × I) : A :=
  if ε p.1 = 1 then a p.2 else (a (ρ.symm p.2))⁻¹

/-- Disjoint relator disks in a larger ribbon diagram. The other darts may
belong to an outside word or be isolated markers from previous cancellations. -/
structure DiskAtlas (ρ : Perm I) (a : I → A) (s : I → ℤ)
    (σ : Perm D) (t : D → ℤ) where
  disk : V × I ↪ D
  ε : V → ℤ
  polarity : ∀ v, ε v = 1 ∨ ε v = -1
  next : ∀ v i, σ (disk (v,i)) = disk (vertexNext ρ ε (v,i))
  sign : ∀ v i, t (disk (v,i)) = ε v*s i

end KervaireRibbon

end

end OAI


