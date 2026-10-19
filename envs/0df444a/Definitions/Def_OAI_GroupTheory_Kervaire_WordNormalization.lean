-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_WordNormalization
-- name    : OAI_GroupTheory_Kervaire_WordNormalization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:23:22.079708+00:00
-- url     : https://prove2.me/theorems/2ddae84b-d6a2-4dac-9f0f-9296ebbbd50c
-- title:
--   Words with unit syllables
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Syllable evaluation.** For a list of pairs $(n_k,g_k)\in\mathbb Z\times A$,
--   $$
--   \prod_kt^{n_k}g_k\in A*\langle t\rangle .
--   $$
--   2. **Unit syllables.** Every exponent $n_k$ is $\pm1$.
--   3. **Normalized elements.** Elements of the form $g\cdot\prod_kt^{n_k}g_k$ with unit syllables.
--
--   Every element of the free product is normalized, by splitting powers $t^n$ into $|n|$ unit letters with trivial coefficients in between. The exponent sum is preserved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/WordNormalization.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/WordNormalization.lean by skeleton subtraction
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
import Definitions.Def_OAI_GroupTheory_Kervaire_OuterRibbon
import Definitions.Def_OAI_GroupTheory_Kervaire_RibbonProducts
import Definitions.Def_OAI_GroupTheory_Kervaire_Conjugation
import Definitions.Def_OAI_GroupTheory_Kervaire_Inversion
import Definitions.Def_OAI_GroupTheory_Kervaire_Realization
import Definitions.Def_OAI_GroupTheory_Kervaire_Annulus

namespace OAI

namespace KervaireRibbon

section
open Monoid Multiplicative
variable {A : Type*} [Group A]

def syllableEval (l : List (ℤ × A)) : FreeProd A :=
  (l.map (fun x ↦ Coprod.inr (ofAdd x.1)*Coprod.inl x.2)).prod

def UnitSyllables (l : List (ℤ × A)) : Prop := ∀ x ∈ l, x.1=1 ∨ x.1 = -1

def Normalized (w : FreeProd A) : Prop :=
  ∃ g : A, ∃ l : List (ℤ × A), UnitSyllables l ∧ w = Coprod.inl g*syllableEval l

end

open Equiv Equiv.Perm
open scoped Classical
variable {I : Type*} [DecidableEq I]

end KervaireRibbon

end OAI


