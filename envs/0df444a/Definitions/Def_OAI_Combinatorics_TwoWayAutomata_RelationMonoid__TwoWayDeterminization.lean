-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid__TwoWayDeterminization
-- name    : OAI_Combinatorics_TwoWayAutomata_RelationMonoid__TwoWayDeterminization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:40:09.271143+00:00
-- url     : https://prove2.me/theorems/f369bc93-f66d-4c90-a78c-e5e5e33daed0
-- title:
--   Partial identities and the monoid of binary relations under path-order composition
-- statement:
--   Let $H$ be a set. For relations $R,S\subseteq H\times H$ write $RS$ for their composition in path order, $(x,z)\in RS$ iff there is $y$ with $(x,y)\in R$ and $(y,z)\in S$, and let $\mathrm{Id}_H=\{(x,x):x\in H\}$.
--
--   1. **Partial identity.** For $F\subseteq H$, $\mathrm{Id}_F=\{(x,x):\ x\in F\}$ is the identity restricted to the retained points of $F$. It is idempotent: $\mathrm{Id}_F\,\mathrm{Id}_F=\mathrm{Id}_F$.
--   2. **Relation monoid.** $\mathcal R(H)$ is the monoid whose elements are the binary relations on $H$, with product given by composition in path order and identity $\mathrm{Id}_H$. Writing $\mathrm{rel}(X)$ for the relation underlying an element $X$,
--   $$\mathrm{rel}(X\cdot Y)=\mathrm{rel}(X)\,\mathrm{rel}(Y),\qquad \mathrm{rel}(1)=\mathrm{Id}_H .$$
--   Every relation $R$ determines an element of $\mathcal R(H)$ whose underlying relation is $R$, and two elements with the same underlying relation are equal.
--
--   The relation monoid is where words over an alphabet of relations are evaluated: a word $R_1\cdots R_n$ evaluates to the product $R_1R_2\cdots R_n$, read from left to right along paths. Partial identities are idempotents of $\mathcal R(H)$; the elements $X$ with $\mathrm{Id}_F X=X=X\,\mathrm{Id}_F$ are exactly the relations contained in $F\times F$.
--
--   **Formalization Note** `RelationMonoid H` is the opposite `(CategoryTheory.End H)ᵐᵒᵖ` of the endomorphism monoid of $H$ in Mathlib's category `RelCat` of relations; passing to the opposite turns composition into path order. `RelationMonoid.ofRel` and `RelationMonoid.toRel` convert between `SetRel H H` and the monoid, with the simp lemmas `toRel_ofRel`, `toRel_mul`, `toRel_one` and the extensionality lemma `RelationMonoid.ext`. The partial identity is `restrictedIdentity F`, and its idempotence is `restrictedIdentity_comp_self`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/RelationMonoid.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/RelationMonoid.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayDeterminization mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners__TwoWayDeterminization

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Identity restricted to the retained points. -/
def restrictedIdentity {α : Type*} (F : Set α) : SetRel α α :=
  {(x, y) | x = y ∧ x ∈ F}

@[simp]
theorem restrictedIdentity_comp_self {α : Type*} (F : Set α) :
    restrictedIdentity F ○ restrictedIdentity F = restrictedIdentity F := by
  ext ⟨x, y⟩
  simp [SetRel.comp, restrictedIdentity]

/-- Relations in path order, using the opposite of Mathlib's endomorphism monoid. -/
abbrev RelationMonoid (H : Type*) :=
  (CategoryTheory.End (show CategoryTheory.RelCat from H))ᵐᵒᵖ

namespace RelationMonoid

/-- Regard a binary relation as a path-ordered endomorphism. -/
def ofRel {H : Type*} (R : SetRel H H) : RelationMonoid H :=
  MulOpposite.op (.ofRel R)

/-- The underlying binary relation. -/
def toRel {H : Type*} (R : RelationMonoid H) : SetRel H H := R.unop.rel

@[ext]
theorem ext {H : Type*} {R S : RelationMonoid H} (h : R.toRel = S.toRel) : R = S :=
  MulOpposite.unop_injective (CategoryTheory.RelCat.Hom.ext _ _ h)

@[simp]
theorem toRel_ofRel {H : Type*} (R : SetRel H H) : (ofRel R).toRel = R := rfl

@[simp]
theorem toRel_mul {H : Type*} (R S : RelationMonoid H) :
    (R * S).toRel = R.toRel ○ S.toRel := rfl

@[simp]
theorem toRel_one {H : Type*} : (1 : RelationMonoid H).toRel = SetRel.id := rfl

end RelationMonoid

end TwoWayComplementation

end OAI


