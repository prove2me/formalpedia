-- Prove2me | Definitions.Def_Sensitivity_Subcube
-- name    : Sensitivity_Subcube
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T18:55:21.727861+00:00
-- url     : https://prove2.me/theorems/4a03cdba-b2e7-4508-8428-ad0e367419dc
-- title:
--   Subcube
-- statement:
--   Definitions and structural lemmas for Subcube, from Samuel Schlesinger's pinned Boolean function sensitivity development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Subcube.lean

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
set_option autoImplicit false
namespace Sensitivity
variable {n : ℕ}
def embed (free : Finset (Fin n)) (base : Fin n → Bool)
    (x : Fin n → Bool) : Fin n → Bool :=
  fun j => if j ∈ free then x j else base j
def BoolFun.restrictTo (f : BoolFun n) (free : Finset (Fin n))
    (base : Fin n → Bool) : BoolFun n :=
  fun x => f (embed free base x)
end Sensitivity


