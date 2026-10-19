-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype
-- name    : OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:38:18.796522+00:00
-- url     : https://prove2.me/theorems/90c8e2ba-1970-4289-86e3-172e5d0e2d1c
-- title:
--   Supports split into free and exterior parts
-- statement:
--   Let $P$ be a decidable predicate on a coordinate set $\iota$. For $A\subseteq\{i:P(i)\}$ and $D\subseteq\{i:\neg P(i)\}$ let $A\sqcup D\subseteq\iota$ be their union viewed in $\iota$. Then
--   $$
--   (A,D)\mapsto A\sqcup D
--   $$
--   is a bijection between pairs and subsets of $\iota$, and restricting $A\sqcup D$ to the two parts recovers $A$ and $D$.
--
--   Fourier supports of a restricted function are indexed by such pairs. This bookkeeping identifies the Fourier mass of restrictions with that of the original function.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/RestrictionMassSubtype.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/RestrictionMassSubtype.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SharpThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence

namespace OAI

universe u

noncomputable section

open scoped BigOperators

namespace Problem313

variable {ι : Type u} [Fintype ι] (P : ι → Prop) [DecidablePred P]

namespace BiasedFourier

/-- The ambient support obtained by adjoining free and exterior supports. -/
def subtypeSupport (A : Finset {i // P i}) (D : Finset {i // ¬P i}) : Finset ι :=
  (A.disjSum D).map (Equiv.sumCompl P).toEmbedding

/-- Free and exterior support sets give each ambient support exactly once. -/
def subtypeSupportEquiv :
    (Finset {i // P i} × Finset {i // ¬P i}) ≃ Finset ι :=
  Finset.sumEquiv.toEquiv.symm.trans (Equiv.sumCompl P).finsetCongr

omit [Fintype ι] in
@[simp]
theorem subtypeSupportEquiv_apply
    (A : Finset {i // P i}) (D : Finset {i // ¬P i}) :
    subtypeSupportEquiv P (A,D) = subtypeSupport P A D := rfl

omit [Fintype ι] in
@[simp]
theorem subtype_subtypeSupport
    (A : Finset {i // P i}) (D : Finset {i // ¬P i}) :
    (subtypeSupport P A D).subtype P = A := by
  ext i
  simp [subtypeSupport]

omit [Fintype ι] in
@[simp]
theorem subtype_not_subtypeSupport
    (A : Finset {i // P i}) (D : Finset {i // ¬P i}) :
    (subtypeSupport P A D).subtype (fun i => ¬P i) = D := by
  ext i
  simp [subtypeSupport]

end BiasedFourier
end Problem313

end

end OAI


