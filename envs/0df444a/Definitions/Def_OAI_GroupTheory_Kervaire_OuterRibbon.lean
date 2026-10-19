-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_OuterRibbon
-- name    : OAI_GroupTheory_Kervaire_OuterRibbon
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:59:55.878107+00:00
-- url     : https://prove2.me/theorems/0085742e-c173-4ae0-abb2-79138c309683
-- title:
--   Relator ribbons with an outer boundary
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   An outer ribbon for the relator data $(\rho,a,s)$, with a marker dart $o$ and a list $l$, consists of the following.
--
--   1. **Planar structure.** A vertex permutation $\sigma$ and an edge involution $\theta$ forming a planar pair, with signs $t(\theta d)=-t(d)$.
--   2. **Boundary.** The marker $o$, fixed by $\theta$ and of sign $0$. The list $o::l$ is a circle of $\sigma$ without repetitions, and the darts of $l$ have signs $\pm1$.
--   3. **Relator disks.** A disk atlas, disjoint from the boundary, covering all other non-isolated darts.
--   4. **Potentials.** $u:D\to A$ such that every corner at a relator disk equals the relator coefficient.
--
--   Its value is the boundary word
--   $$
--   \prod_{d\in o::l}t^{t(d)}\,u(\theta d)u(\sigma d)^{-1}\ \in A*\langle t\rangle .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/OuterRibbon.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/OuterRibbon.lean by skeleton subtraction
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
import Definitions.Def_OAI_GroupTheory_Kervaire_RelatorRigidity
import Definitions.Def_OAI_GroupTheory_Kervaire_VertexJoin
import Definitions.Def_OAI_GroupTheory_Kervaire_Circles
import Definitions.Def_OAI_GroupTheory_Kervaire_Splicing
import Definitions.Def_OAI_GroupTheory_Kervaire_Capping

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

/-- A finite genus-zero relator ribbon with a marked outside vertex. Isolated
zero-sign darts are retained, so cap surgery never changes the finite universe. -/
structure OuterRibbon (ρ : Perm I) (a : I → A) (s : I → ℤ) (o : D) (l : List D) where
  σ : Perm D
  θ : Perm D
  involutive : ∀ d, θ (θ d) = d
  planar' : planar σ θ
  t : D → ℤ
  opposite : ∀ d, t (θ d) = - t d
  marker : θ o = o
  marker_sign : t o = 0
  circle : Circle σ o l
  nodup : (o::l).Nodup
  unit : ∀ d ∈ l, t d = 1 ∨ t d = -1
  atlas : DiskAtlas (V := V) ρ a s σ t
  disjoint : ∀ vi, atlas.disk vi ∉ o::l
  cover : ∀ d, (∃ vi, atlas.disk vi = d) ∨ d ∈ o::l ∨ (σ d = d ∧ θ d = d)
  u : D → A
  corners : ∀ v i, vertexCorner ρ a atlas.ε (v,i) = corner σ θ u (atlas.disk (v,i))

def OuterRibbon.value {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) : FreeProd A :=
  dartEval r.t (corner r.σ r.θ r.u) (o::l)

end
section
open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

end
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

end KervaireRibbon

end

end OAI


