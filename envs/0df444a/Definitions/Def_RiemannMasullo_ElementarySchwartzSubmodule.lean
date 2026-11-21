-- Prove2me | Definitions.Def_RiemannMasullo_ElementarySchwartzSubmodule
-- name    : RiemannMasullo_ElementarySchwartzSubmodule
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-21T02:02:54.64619+00:00
-- url     : https://prove2.me/theorems/18c8e8f6-b4ae-4b38-9cfd-7c9ddafe481d
-- title:
--   The Schwartz submodule on elementary Lie groups
-- statement:
--   The complex vector space of functions on the elementary group that are smooth in the Euclidean and torus variables and have finite weighted derivative bounds of every order.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L357-L365

import Theorems.Thm_RiemannMasullo_elementarySchwartzSubmodule_zero_mem
import Theorems.Thm_RiemannMasullo_elementarySchwartzSubmodule_add_mem
import Theorems.Thm_RiemannMasullo_elementarySchwartzSubmodule_smul_mem
open scoped ContDiff ENNReal
namespace RiemannMasullo
noncomputable section

def elementarySchwartzSubmodule (m n r : ℕ) (F : Type*) :
    Submodule ℂ (ElementaryLieGroup m n r F → ℂ) where
  carrier := {f | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
    ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞)}
  zero_mem' := elementarySchwartzSubmodule_zero_mem
  add_mem' := elementarySchwartzSubmodule_add_mem
  smul_mem' := elementarySchwartzSubmodule_smul_mem

end
end RiemannMasullo


