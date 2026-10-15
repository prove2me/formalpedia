-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
-- name    : OAI_Combinatorics_TwoWayAutomata_RelationMonoid
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T08:17:20.80962+00:00
-- url     : https://prove2.me/theorems/fa876eb2-042e-420a-93a7-e9ab1bbf868c
-- title:
--   Partial identities and the monoid of binary relations under composition in path order
-- statement:
--   Let $H$ be a set. For relations $R,S\subseteq H\times H$, $RS$ denotes composition in path order, $(x,z)\in RS\iff\exists y\in H:\ (x,y)\in R\ \text{and}\ (y,z)\in S$, and $\mathrm{Id}_H=\{(x,x):x\in H\}$ is the identity relation.
--
--   1. **Partial identities.** For a subset $F\subseteq H$, the partial identity is $\mathrm{Id}_F=\{(x,x):\ x\in F\}$. It is idempotent: $\mathrm{Id}_F\,\mathrm{Id}_F=\mathrm{Id}_F$.
--   2. **The relation monoid.** $\mathcal R(H)$ is the monoid whose elements are the relations on $H$, with
--   $$R\cdot S=RS,\qquad 1_{\mathcal R(H)}=\mathrm{Id}_H .$$
--   Every relation on $H$ is an element of $\mathcal R(H)$, every element has an underlying relation, and two elements are equal if and only if their underlying relations are equal.
--
--   The letters of the liveness language are relations on $H$, and a word belongs to it exactly when the product of its letters in $\mathcal R(H)$ is nonempty. The lower-bound argument maps a submonoid of the diagram monoid onto $\mathcal R(H)$ and then works in corners of $\mathcal R(H)$ cut out with the help of partial identities, which behave like relation monoids of smaller sets.
--
--   **Formalization Note** `RelationMonoid H` is the opposite monoid `(CategoryTheory.End H)ᵐᵒᵖ` of the endomorphisms of $H$ in the category `RelCat`; the opposite is taken so that multiplication is composition in path order. `RelationMonoid.ofRel` and `RelationMonoid.toRel` convert between `SetRel H H` and `RelationMonoid H`, `RelationMonoid.ext` is extensionality, and `toRel_ofRel`, `toRel_mul`, `toRel_one` are simp lemmas. The partial identity is `restrictedIdentity F`, with `restrictedIdentity_comp_self`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/RelationMonoid.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/RelationMonoid.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayComplementation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners

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


