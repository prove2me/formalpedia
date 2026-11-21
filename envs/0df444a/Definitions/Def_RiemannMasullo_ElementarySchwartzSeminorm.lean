-- Prove2me | Definitions.Def_RiemannMasullo_ElementarySchwartzSeminorm
-- name    : RiemannMasullo_ElementarySchwartzSeminorm
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-21T02:07:22.482532+00:00
-- url     : https://prove2.me/theorems/17371a3b-ac1d-4350-81f3-fa2a6092b0f6
-- title:
--   The weighted seminorms of the elementary Schwartz space
-- statement:
--   Each fourfold multi-index defines a real-valued seminorm on the elementary Schwartz space by taking the supremum norm of its monomial-weighted mixed derivative.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L405-L416

import Theorems.Thm_RiemannMasullo_elementarySchwartzSeminorm_map_zero
import Theorems.Thm_RiemannMasullo_elementarySchwartzSeminorm_add_le
import Theorems.Thm_RiemannMasullo_elementarySchwartzSeminorm_smul
import Theorems.Thm_RiemannMasullo_elementarySchwartzSeminorm_neg
namespace RiemannMasullo
noncomputable section
variable {m n r : ℕ} {F : Type*}

def elementarySchwartzSeminorm (i : ElementarySchwartzIndex m n r) :
    Seminorm ℂ (elementarySchwartzSubmodule m n r F) where
  toFun f := (elementarySchwartzBound f.val i).toReal
  map_zero' := elementarySchwartzSeminorm_map_zero i
  add_le' := elementarySchwartzSeminorm_add_le i
  smul' := elementarySchwartzSeminorm_smul i
  neg' := elementarySchwartzSeminorm_neg i

end
end RiemannMasullo


