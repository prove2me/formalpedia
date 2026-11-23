-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AbelianSchemeTorusCompare
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AbelianSchemeTorusCompare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:42.458396+00:00
-- url     : https://prove2.me/theorems/5bed4969-fc9b-42e2-929c-dbe54969bdea
-- title:
--   Abelian Scheme Torus Compare
-- statement:
--   Definitions and structural lemmas for Abelian Scheme Torus Compare, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AbelianSchemeTorusCompare.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableCompleteSplit
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianModels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.Compare.AbelianSchemeTorusCompare
open GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianModels
def torusExtOf {k : Type} [Field k] {T G B : Over (Spec (CommRingCat.of k))}
    [GrpObj T] [GrpObj G] [GrpObj B] {i : T ⟶ G} {q : G ⟶ B} (h : IsExtensionByTorus i q) :
    TorusExt G where
  B := B
  isAbelian := h.2.1
  q := q
  q_hom := h.2.2.2.1
  q_flat := h.2.2.2.2.1
  q_surjective := h.2.2.2.2.2.1
  q_quasiCompact := h.2.2.2.2.2.2.1
  T₀ := T
  isTorus := h.1
  i := i
  i_hom := h.2.2.1
  isKernel := h.2.2.2.2.2.2.2
end GlobalTheory.Compare.AbelianSchemeTorusCompare


