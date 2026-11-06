-- Prove2me | Definitions.Def_TC433_Algebra_Lie_F4_ShortRoot_Represented_Flag_PrimeField_d56bf350f3
-- name    : TC433_Algebra_Lie_F4_ShortRoot_Represented_Flag_PrimeField_d56bf350f3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:00:49.040642+00:00
-- url     : https://prove2.me/theorems/7ee5218e-e5f7-471e-a807-f060498a3225
-- title:
--   TauCeti: Algebra / Lie / F4 / ShortRoot / Represented / Flag / PrimeField
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Lie.F4.ShortRoot.Represented.Flag.PrimeField for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Lie/F4/ShortRoot/Represented/Flag/PrimeField.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_Lie_F4_ShortRoot_Represented_Flag_Root_09c19a5012
public import Definitions.Def_TC433_Algebra_Lie_F4_ShortRoot_PrimeField_PointsFunctor_064d991e27

/-!
# The prime-field F4 generators preserve the represented flag

This file applies the represented-flag criteria to the actual root and weight-torus coordinate
morphisms in the generated short-root carrier over `ZMod 2`.
-/

public section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti.DynkinType

open CategoryTheory
open TauCeti.F4ShortRoot

noncomputable section

local notation "𝔽₂" => ZMod 2
local notation "T₄" => MonoidAlgebra 𝔽₂ (SplitTorus.characterGroup (Fin 4))
local notation "Gₐ" => AdditiveGroup.coordinateHopfAlgebra 𝔽₂

/-- Local adjoint comodule used for the prime-field generator checks. -/
local instance : Comodule 𝔽₂ (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
    f4ShortRootCotangentDual :=
  Derivation.adjointComodule
    (R := 𝔽₂) (H := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)

/-- The weight-torus member of the prime-field generating family acts block triangularly on the
adapted represented flag. -/
theorem f4ShortRootPrimeField_weightTorus_blockTriangular :
    ((Comodule.coefficientMatrix
        (C := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
        f4ShortRootCotangentFlagBasis).map
      (F4ShortRoot.PrimeField.generator (.inr ())).hom).BlockTriangular
        (OrderDual.toDual ∘ f4ShortRootCotangentFlagWeight) := by
  let q : HopfAlgebra.points (R := 𝔽₂) (H := T₄) (CommAlgCat.of 𝔽₂ T₄) :=
    WithConv.toConv (AlgHom.id 𝔽₂ T₄)
  let g := (CommHopfAlgCat.mapPointsFunctor
    (GeneralLinear.weightTorusCoordinateMap (R := 𝔽₂) f4ShortRootWeight)).app
      (CommAlgCat.of 𝔽₂ T₄) q
  have hg : GeneralLinear.pointsMulEquiv 26 g =
      f4ShortRootWeightTorusGL (SplitTorus.pointsMulEquiv q) := by
    simpa only [f4ShortRootWeightTorusGL] using
      (GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap
        f4ShortRootWeight (CommAlgCat.of 𝔽₂ T₄) q)
  have h := f4ShortRootWeightTorus_adjoint_blockTriangular g
    (SplitTorus.pointsMulEquiv q) hg
  have hgen : g.ofConv =
      (F4ShortRoot.PrimeField.generator (.inr ())).hom.toAlgHom := by
    -- Evaluate the mapped torus point at the identity algebra homomorphism.
    change (AlgHom.id 𝔽₂ T₄).comp
      (GeneralLinear.weightTorusCoordinateMap (R := 𝔽₂) f4ShortRootWeight).hom.toAlgHom = _
    rw [AlgHom.id_comp, F4ShortRoot.PrimeField.generator_inr,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap,
      GeneralLinear.hom_weightTorusCoordinateMap]
  simpa only [hgen, BialgHom.coe_toAlgHom] using h

/-- Every root-subgroup member of the prime-field generating family acts block triangularly on
the adapted represented flag. -/
theorem f4ShortRootPrimeField_root_blockTriangular (k : Fin 4 ⊕ Fin 4) :
    ((Comodule.coefficientMatrix
        (C := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
        f4ShortRootCotangentFlagBasis).map
      (F4ShortRoot.PrimeField.generator (.inl k)).hom).BlockTriangular
        (OrderDual.toDual ∘ f4ShortRootCotangentFlagWeight) := by
  let q : HopfAlgebra.points (R := 𝔽₂) (H := Gₐ) (CommAlgCat.of 𝔽₂ Gₐ) :=
    WithConv.toConv (AlgHom.id 𝔽₂ Gₐ)
  let g := (CommHopfAlgCat.mapPointsFunctor
    (F4ShortRoot.PrimeField.generator (.inl k))).app (CommAlgCat.of 𝔽₂ Gₐ) q
  let u := AdditiveGroup.gaPointsMulEquiv (R := 𝔽₂) q
  have hg : GeneralLinear.pointsMulEquiv 26 g = rootSubgroupPoints k Gₐ u := by
    calc
      _ = (F4ShortRoot.PrimeField.rootSubgroupPoints k Gₐ u :
          GL (Fin 26) Gₐ) :=
        (F4ShortRoot.PrimeField.coe_rootSubgroupPoints_gaPointsMulEquiv k Gₐ q).symm
      _ = _ := F4ShortRoot.PrimeField.coe_rootSubgroupPoints k Gₐ u
  have h := f4ShortRootRootSubgroup_adjoint_blockTriangular g k u hg
  have hgen : g.ofConv =
      (F4ShortRoot.PrimeField.generator (.inl k)).hom.toAlgHom := by
    -- Evaluate the mapped root point at the identity algebra homomorphism.
    change (AlgHom.id 𝔽₂ Gₐ).comp
      (F4ShortRoot.PrimeField.generator (.inl k)).hom.toAlgHom = _
    rw [AlgHom.id_comp]
  simpa only [hgen, BialgHom.coe_toAlgHom] using h

end

end TauCeti.DynkinType


