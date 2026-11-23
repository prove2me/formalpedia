-- Prove2me | Definitions.Def_GlobalLanglandsSetup
-- name    : GlobalLanglandsSetup
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T14:18:53.216124+00:00
-- url     : https://prove2.me/theorems/9abf716e-db66-446e-b985-b5e8a9e511c4
-- title:
--   Global Langlands Functoriality Data Interface
-- statement:
--   This definition packages typed data for an abstract global functoriality problem: a base field, source and target groups, their representations, an L-group homomorphism, local parameter maps, and finite ramification sets. It also includes proposition-valued fields intended to record globality, reductivity, quasi-splitness, cuspidality, genericity, and standard-transfer conditions. The predicate `IsWeakTransfer` requires equality up to conjugacy between the target parameter and the image of the source parameter at every place outside the two finite ramification sets. **Formalization Note.** These certification fields are currently abstract propositions and are not defined in terms of concrete global fields, algebraic groups, Weil groups, or automorphic representations; this is a typed interface scaffold, not a complete mathematical foundation.
-- source:
--   J.-H. Yang, “Langlands Functoriality Conjecture,” 2008, §5, equations (5.1)–(5.2), https://arxiv.org/abs/0808.0917; nLab, “Langlands functoriality,” https://ncatlab.org/nlab/show/Langlands+functoriality

import Mathlib

/-!
# Interface for global Langlands functoriality beyond general linear groups

This initial interface records the data appearing in the global functoriality conjecture:
a global base field, connected reductive source and target groups (with quasi-split target),
their L-groups and an L-homomorphism, automorphic representations, unramified local
parameters, and finite ramification sets.

The proposition-valued fields about globality, reductivity, quasi-splitness, and L-homomorphism
conditions are certification slots for the mathematical predicates to be developed in the
foundational library. They are intentionally not axioms: a later formalization must define and
connect them to concrete field, algebraic-group, and L-group structures before the conjecture is
ready for launch. This file only provides the typed interface and the almost-everywhere transfer
predicate; it does not assert the conjecture.
-/

namespace LanglandsFunctorialityGeneral

/-- Typed data for one global functoriality problem. `Place` indexes local components;
`SourceLGroup` and `TargetLGroup` are the L-groups with their group structures. -/
structure GlobalLanglandsSetup (Place SourceLGroup TargetLGroup : Type)
    [Group SourceLGroup] [Group TargetLGroup] where
  /-- The global base field and the source and target groups over it. -/
  BaseField : Type
  SourceGroup : Type
  TargetGroup : Type
  /-- Semantic certificates to be connected to precise definitions in the foundational layer. -/
  baseFieldIsGlobal : Prop
  sourceIsConnectedReductive : Prop
  targetIsConnectedReductive : Prop
  targetIsQuasiSplit : Prop
  lHomSatisfiesLanglandsConditions : Prop
  /-- Source and target automorphic representations. -/
  SourceRep : Type
  TargetRep : Type
  sourceIsAutomorphic : SourceRep → Prop
  targetIsAutomorphic : TargetRep → Prop
  /-- The L-homomorphism between the two L-groups. -/
  lHom : SourceLGroup →* TargetLGroup
  /-- Unramified local parameters, represented by elements of the L-groups. -/
  sourceParameter : SourceRep → Place → SourceLGroup
  targetParameter : TargetRep → Place → TargetLGroup
  /-- Finite sets of ramified places attached to the two representations. -/
  sourceRamified : SourceRep → Finset Place
  targetRamified : TargetRep → Finset Place
  /-- Optional hypotheses used by the CKPSS classical-group milestone. -/
  baseFieldIsNumberField : Prop
  sourceIsSplitClassical : Prop
  sourceIsGloballyGeneric : SourceRep → Prop
  sourceIsCuspidal : SourceRep → Prop
  targetIsStandardGeneralLinearGroup : Prop
  standardDualEmbedding : Prop

/-- A target representation has the transfer parameters prescribed by the source representation
outside the union of their finite ramification sets. Equality is up to conjugacy in the target
L-group, matching the source's equality of semisimple Satake conjugacy classes. -/
def IsWeakTransfer {Place SourceLGroup TargetLGroup : Type}
    [Group SourceLGroup] [Group TargetLGroup]
    (D : GlobalLanglandsSetup Place SourceLGroup TargetLGroup)
    (π : D.SourceRep) (Pi : D.TargetRep) : Prop :=
  ∀ v : Place, v ∉ D.sourceRamified π → v ∉ D.targetRamified Pi →
    ∃ g : TargetLGroup,
      D.targetParameter Pi v = g * D.lHom (D.sourceParameter π v) * g⁻¹

end LanglandsFunctorialityGeneral


