-- Prove2me | Definitions.Def_TC433_LinearAlgebra_Submodule_Prod_6eeae7070a
-- name    : TC433_LinearAlgebra_Submodule_Prod_6eeae7070a
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:13:58.921199+00:00
-- url     : https://prove2.me/theorems/7e742e31-5f59-42ca-80f8-317b4ff7088a
-- title:
--   TauCeti: LinearAlgebra / Submodule / Prod
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.Submodule.Prod for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/Submodule/Prod.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Order.SupIndep

/-!
# Products of submodules

Products of submodules preserve indexed suprema and independence of families of submodules.

## Main declarations

* `TauCeti.iSup_prod_submodule`: products commute with indexed suprema.
* `TauCeti.iSupIndep.prod`: products of independent families are independent.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

/-- Taking products of submodules commutes with indexed suprema, including the empty one. -/
@[simp]
theorem iSup_prod_submodule {R M N : Type*} {ι : Sort*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (P : ι → Submodule R M) (Q : ι → Submodule R N) :
    (⨆ i, (P i).prod (Q i)) = (⨆ i, P i).prod (⨆ i, Q i) := by
  simp only [LinearMap.prod_eq_sup_map, _root_.Submodule.map_iSup, iSup_sup_eq]

/-- Componentwise products of independent families of submodules are independent.

Use `TauCeti.iSupIndep.prod hP hQ`, or `hP.prod hQ` after `open TauCeti`. -/
theorem iSupIndep.prod {R M N : Type*} {ι : Sort*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {P : ι → Submodule R M} {Q : ι → Submodule R N}
    (hP : iSupIndep P) (hQ : iSupIndep Q) : iSupIndep (fun i ↦ (P i).prod (Q i)) := by
  intro i
  simp only [iSup_prod_submodule, disjoint_iff, _root_.Submodule.prod_inf_prod,
    (hP i).eq_bot, (hQ i).eq_bot, _root_.Submodule.prod_bot]

end TauCeti


