-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.serrePairingInt_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/830fc08d-ad46-51ef-9a04-8c5d4bb9bde2

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_residue_kaehlerMap01
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_serrePairingInt_map

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u w

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePairingIntMap

theorem kaehlerMap01_smul {R : Type u} [CommRing R] {S : Type u} [CommRing S] {τ : R →+* S}
    {X : Scheme.{u}} {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)}
    {Y : Scheme.{u}} {𝒲 : Y.TwoAffineOpenCover} {c' : Y ⟶ Spec (.of S)}
    (f : Scheme.TwoAffineOpenCover.HomOver τ 𝒱 c 𝒲 c') (a : (𝒱.cover c).A01) (η : Ω[(𝒱.cover c).A01⁄R]) :
    f.kaehlerMap01 (a • η) = f.map01 a • f.kaehlerMap01 η :=
  KaehlerDifferential.mapOfRingHom_smul _ _ _ a η

end SerrePairingIntMap

theorem solution
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] {τ : R →+* S}
    {X : Scheme.{u}} {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)}
    {Y : Scheme.{u}} {𝒲 : Y.TwoAffineOpenCover} {c' : Y ⟶ Spec (.of S)} {ι : Type w} [Fintype ι]
    (f : Scheme.TwoAffineOpenCover.HomOver τ 𝒱 c 𝒲 c')
    (Λ : ι → (𝒱.cover c).LaurentChart) (Λ' : ι → (𝒲.cover c').LaurentChart)
    (hΛ : ∀ i y, (Λ' i).expand (f.map01 y) = ((Λ i).expand y).map τ)
    (hv : (𝒱.cover c).ResiduesVanishOnCoboundaries Λ) (hv' : (𝒲.cover c').ResiduesVanishOnCoboundaries Λ')
    (ω : (𝒱.kaehlerSections c).H0) (x : (𝒱.structureSheafSections c).H1) :
    (𝒲.cover c').serrePairingInt Λ' hv' (f.kaehlerH0map ω) (f.H1map x) =
      τ ((𝒱.cover c).serrePairingInt Λ hv ω x) := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    rw [Scheme.TwoAffineOpenCover.HomOver.H1map_mk, TwoChartCech.Cover.serrePairingInt_apply_mk,
      TwoChartCech.Cover.serrePairingInt_apply_mk, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← f.residue_kaehlerMap01 (Λ i) (Λ' i) (hΛ i), SerrePairingIntMap.kaehlerMap01_smul, f.kaehlerMap01_r0]
    rfl

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_serrePairingInt_map
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_serrePairingInt_map (solution)
