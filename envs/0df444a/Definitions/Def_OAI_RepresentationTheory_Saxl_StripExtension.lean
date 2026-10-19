-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
-- name    : OAI_RepresentationTheory_Saxl_StripExtension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:32:47.903261+00:00
-- url     : https://prove2.me/theorems/f761e16d-c8cc-4b72-902c-f93c0ff27594
-- title:
--   Restricting permutations to an embedded position set and extending colorings
-- statement:
--   Two elementary constructions for an embedded set of positions, used when restriction maps are iterated along nested Young diagrams.
--
--   Write $[n]=\{0,1,\dots,n-1\}$ and $\mathfrak S_n$ for the group of permutations of $[n]$. Let $\iota:[a]\to[n]$ be an injective map, with image $\iota([a])$.
--
--   1. **Restriction of a permutation.** Let $g\in\mathfrak S_n$ map the image onto itself, in the sense that $g(x)\in\iota([a])$ holds if and only if $x\in\iota([a])$, for every $x\in[n]$. Then $g|_\iota\in\mathfrak S_a$ is the permutation determined by
--   $$
--   \iota\big(g|_\iota(k)\big)=g\big(\iota(k)\big)\qquad(k\in[a]),
--   $$
--   that is, the restriction of $g$ to $\iota([a])$ transported back to $[a]$ along $\iota$.
--
--   2. **Color extension.** For a coloring $c:[a]\to\mathbb{N}$ and a color $q\in\mathbb{N}$, the coloring $\tilde c:[n]\to\mathbb{N}$ with $\tilde c(x)=c(\iota^{-1}(x))$ if $x\in\iota([a])$ and $\tilde c(x)=q$ otherwise.
--
--   When horizontal-strip restrictions are iterated, the positions of the smaller diagram are embedded by $\iota$; the color extension keeps the old colors there and gives all newly added positions the fresh color $q$, while the restricted permutation converts a permutation preserving the embedded positions into one of the smaller position set, as needed to state equivariance.
--
--   **Formalization Note** The definitions are `restrictPerm i g hg`, where `hg : ∀ x, g x ∈ Set.range i ↔ x ∈ Set.range i`, built from `Equiv.ofInjective` and `Equiv.Perm.subtypePerm`, and `extendColor i c q`, where $\iota^{-1}$ is the inverse of `Equiv.ofInjective i`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/StripExtension.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/StripExtension.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Saxl mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

def restrictPerm {a n : ℕ} (i : Fin a ↪ Fin n) (g : Equiv.Perm (Fin n))
    (hg : ∀ x, g x ∈ Set.range i ↔ x ∈ Set.range i) : Equiv.Perm (Fin a) :=
  (Equiv.ofInjective i i.injective).trans ((g.subtypePerm hg).trans
    (Equiv.ofInjective i i.injective).symm)

def extendColor {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ) : Fin n → ℕ :=
  fun x => if h : x ∈ Set.range i then c ((Equiv.ofInjective i i.injective).symm ⟨x,h⟩) else q

end Saxl

end

end OAI


