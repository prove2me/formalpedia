-- Prove2me | Definitions.Def_mme_dwz_canonical_component_row_cast_data
-- name    : mme_dwz_canonical_component_row_cast_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T08:41:37.738448+00:00
-- url     : https://prove2.me/theorems/406e18c4-a4e8-4788-aefb-c21ae9dc0361
-- title:
--   Canonical Table-2 row equality transports component modes and Z letters
-- statement:
--   Equal Table-2 row labels determine canonical transports of both the three component mode spaces and the dependent canonical $Z$-letter type. These transports are identity maps after eliminating the row equality. They provide the typed coordinate interface needed to reorder a heterogeneous Coppersmith--Winograd product without changing its literal basis data.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2--5.5 (Table-2 component words and regrouping), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_component_word_projection

open MME Module

universe u

set_option autoImplicit false

namespace MME.DWZSourceAligned

noncomputable def canonicalComponentModeCast
    {K : Type u} [Field K] {s t : Fin 15} (h : s = t) (i : Fin 3) :
    (DWZComponentRestriction.canonicalComponentBlock K s).V i ≃ₗ[K]
      (DWZComponentRestriction.canonicalComponentBlock K t).V i := by
  subst t
  exact LinearEquiv.refl K _

def canonicalComponentZLetterCast
    {s t : Fin 15} (h : s = t)
    (x : DWZComponentRestriction.LiftedCoarsePair.{u} 6
      (DWZSquare.shapeZ s)) :
    DWZComponentRestriction.LiftedCoarsePair.{u} 6
      (DWZSquare.shapeZ t) := by
  subst t
  exact x

end MME.DWZSourceAligned


