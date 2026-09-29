-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.serrePairingInt_bijective_and_flip_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/b1dcbe48-f1cb-5e0b-9276-2f48d6f46514

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Theorems.Thm_LinearMap_bijective_and_flip_bijective_of_baseChange_residueField
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_serrePairingInt_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_serrePairingInt_bijective_and_flip_bijective

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u w

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} {ι : Type w} [Fintype ι]
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    {k : Type u} [Field k] [Algebra R k] (hπ : Function.Surjective (algebraMap R k))
    (Λ : ι → (𝒱.cover c).LaurentChart)
    (Λk : ι → ((𝒱.pullback c k).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).LaurentChart)
    (hΛ : ∀ i y, (Λk i).expand ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c k).map01 y) =
      ((Λ i).expand y).map (algebraMap R k))
    (hv : (𝒱.cover c).ResiduesVanishOnCoboundaries Λ)
    (hvk : ((𝒱.pullback c k).cover
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).ResiduesVanishOnCoboundaries Λk)
    [Module.Free R (𝒱.kaehlerSections c).H0] [Module.Finite R (𝒱.kaehlerSections c).H0]
    [Module.Free R (𝒱.structureSheafSections c).H1] [Module.Finite R (𝒱.structureSheafSections c).H1]
    (eH0 : k ⊗[R] (𝒱.kaehlerSections c).H0 ≃ₗ[k]
      ((𝒱.pullback c k).kaehlerSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).H0)
    (heH0 : ∀ ω, eH0 (1 ⊗ₜ[R] ω) = Scheme.TwoAffineOpenCover.kaehlerH0baseChangeMap 𝒱 c k ω)
    (eH1 : k ⊗[R] (𝒱.structureSheafSections c).H1 ≃ₗ[k]
      ((𝒱.pullback c k).structureSheafSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).H1)
    (heH1 : ∀ x, eH1 (1 ⊗ₜ[R] x) = Scheme.TwoAffineOpenCover.H1baseChangeMap 𝒱 c k x)
    (hk : Function.Bijective (((𝒱.pullback c k).cover
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).serrePairingInt Λk hvk) ∧
      Function.Bijective (((𝒱.pullback c k).cover
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).serrePairingInt Λk hvk).flip) :
    Function.Bijective ((𝒱.cover c).serrePairingInt Λ hv) ∧
      Function.Bijective ((𝒱.cover c).serrePairingInt Λ hv).flip :=
  LinearMap.bijective_and_flip_bijective_of_baseChange_residueField hπ _ _ eH0 eH1
    (fun ω x => by
      rw [heH0, heH1]
      exact (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c k).serrePairingInt_map Λ Λk hΛ hv hvk ω x) hk

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_serrePairingInt_bijective_and_flip_bijective
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_serrePairingInt_bijective_and_flip_bijective (solution)
