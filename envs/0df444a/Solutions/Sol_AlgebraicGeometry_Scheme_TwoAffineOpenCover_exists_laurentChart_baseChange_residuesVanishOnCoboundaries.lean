-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_baseChange_residuesVanishOnCoboundaries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1325a0f9-8888-5ced-a154-7554e25c616b

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_kaehlerSections
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_residue_kaehlerMap01
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange_residuesVanishOnCoboundaries

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

open AlgebraicGeometry.Scheme.TwoAffineOpenCover in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A]
    {ιT : Type w} [Fintype ιT] (Λ : ιT → (𝒱.cover c).LaurentChart)
    (hv : (𝒱.cover c).ResiduesVanishOnCoboundaries Λ) :
    ∃ (ΛA : ιT → ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).LaurentChart)
      (_ : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ResiduesVanishOnCoboundaries ΛA),
      ∀ i y, (ΛA i).expand ((HomOver.baseChange 𝒱 c A).map01 y) = ((Λ i).expand y).map (algebraMap R A) := by
  classical
  choose ΛA hΛA _h2 _h3 _h4 _h5 _h6 using fun i => exists_laurentChart_baseChange 𝒱 c A (Λ i)
  refine ⟨ΛA, ?_, hΛA⟩
  set F := HomOver.baseChange 𝒱 c A with hF

  have key : ∀ η : Ω[(𝒱.cover c).A01⁄R],
      ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).residueSum ΛA (F.kaehlerMap01 η) =
        algebraMap R A ((𝒱.cover c).residueSum Λ η) := fun η => by
    rw [TwoChartCech.Cover.residueSum_apply, TwoChartCech.Cover.residueSum_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => HomOver.residue_kaehlerMap01 F (Λ i) (ΛA i) (hΛA i) η
  rw [TwoChartCech.Cover.residuesVanishOnCoboundaries_iff] at hv ⊢
  obtain ⟨e0, e1, -, -, -, he0, he1, -, -, -⟩ := exists_baseChangeIsos_kaehlerSections 𝒱 c A
  constructor
  · intro ωA
    obtain ⟨z, rfl⟩ := e0.surjective ωA
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, add_zero]
    | tmul a ω =>
      rw [he0, map_smul, map_smul, ← HomOver.kaehlerMap01_r0, key, hv.1 ω, map_zero, smul_zero]
  · intro ωA
    obtain ⟨z, rfl⟩ := e1.surjective ωA
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, add_zero]
    | tmul a ω =>
      rw [he1, map_smul, map_smul, ← HomOver.kaehlerMap01_r1, key, hv.2 ω, map_zero, smul_zero]

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange_residuesVanishOnCoboundaries
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange_residuesVanishOnCoboundaries (solution)
