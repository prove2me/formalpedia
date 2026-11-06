-- Prove2me | Definitions.Def_TC433_LinearAlgebra_RootSystem_SimplyConnectedRootDatum_LieAlgebra_Chevalley_ed62f3b598
-- name    : TC433_LinearAlgebra_RootSystem_SimplyConnectedRootDatum_LieAlgebra_Chevalley_ed62f3b598
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:29:49.209992+00:00
-- url     : https://prove2.me/theorems/cb84419e-7567-49ef-8f8a-00fb2b326cb5
-- title:
--   TauCeti: LinearAlgebra / RootSystem / SimplyConnectedRootDatum / LieAlgebra / Chevalley
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/LieAlgebra/Chevalley.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_Lie_Weights_Chevalley_BaseSquare_02cd0c53d2
public import Definitions.Def_TC433_LinearAlgebra_RootSystem_SimplyConnectedRootDatum_LieAlgebra_Killing_4db8fcb848

/-!
# Chevalley systems for the pinned rational Lie algebra

The signed Geck involution exchanges the simple raising and lowering generators of the pinned
Lie-algebra basis. The generic base-square propagation theorem therefore constructs a Chevalley
system over `ℚ` itself; no extension to an algebraic closure is needed for this choice. This does
not establish nondegeneracy of the rational Killing form, which is an independent input supplied
by the imported Killing-form module.

## Main results

* `TauCeti.DynkinType.instIsTriangularizableLieAlgebra`: the distinguished Cartan acts
  triangularizably on the pinned rational Lie algebra.
* `TauCeti.DynkinType.exists_isChevalleySystem`: the signed Geck involution admits a compatible
  Chevalley system over `ℚ`.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti.DynkinType

open _root_.LieAlgebra LieModule

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- The Cartan action on the pinned rational Lie algebra is triangularizable over `ℚ`. -/
instance instIsTriangularizableLieAlgebra :
    IsTriangularizable ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht) :=
  (t.lieBasis ht).isTriangularizable

/-- The pinned rational Lie algebra admits a root-vector system compatible with its signed Geck
involution. -/
theorem exists_isChevalleySystem :
    ∃ x : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht) → t.lieAlgebra ht,
      TauCeti.IsChevalleySystem (t.chevalleyInvolution ht) x := by
  obtain ⟨x, hx⟩ := TauCeti.exists_isSl2System ℚ (t.cartanSubalgebra ht)
  exact hx.exists_isChevalleySystem_of_lieBasis (t.chevalleyInvolution ht)
    (fun y hy => t.chevalleyInvolution_cartan ht ⟨y, hy⟩) (t.lieBasis ht)
    (t.chevalleyInvolution_lieBasis_e ht)

end

end TauCeti.DynkinType


