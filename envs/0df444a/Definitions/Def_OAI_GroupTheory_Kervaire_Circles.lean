-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_Circles
-- name    : OAI_GroupTheory_Kervaire_Circles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:34:01.609962+00:00
-- url     : https://prove2.me/theorems/34767572-1c92-4076-91e2-e392f8164c31
-- title:
--   Boundary circles and dart words
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Circle.** A list $l$ is a circle of $\sigma$ through $o$ if
--   $$
--   o\to l_1\to\cdots\to l_k\to o
--   $$
--   are consecutive steps of $\sigma$, so $o::l$ traverses the cycle of $o$.
--   2. **Free product.** $A*\langle t\rangle$ with $t$ of infinite order.
--   3. **Dart letters and words.** For signs $t:D\to\mathbb Z$ and corner coefficients $c:D\to A$, the letter $t^{t(d)}c(d)$ of a dart, and the product of letters along a list.
--
--   The value of a ribbon diagram is the dart word of its outer boundary circle.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/Circles.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Circles.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [DecidableEq D] [Finite D]

def Circle (σ : Perm D) (o : D) (l : List D) : Prop :=
  (o :: (l ++ [o])).IsChain (fun x y ↦ σ x = y)

end
open Monoid Multiplicative
open scoped Classical
variable {D A : Type*} [Group A]
abbrev FreeProd (A : Type*) [Group A] := Coprod A (Multiplicative ℤ)
def dartLetter (t : D → ℤ) (c : D → A) (d : D) : FreeProd A :=
  Coprod.inr (ofAdd (t d)) * Coprod.inl (c d)
def dartEval (t : D → ℤ) (c : D → A) (l : List D) : FreeProd A := (l.map (dartLetter t c)).prod

lemma dartEval_cons (t : D → ℤ) (c : D → A) (d : D) (l : List D) :
    dartEval t c (d::l) = dartLetter t c d * dartEval t c l := rfl

end KervaireRibbon

end

end OAI


