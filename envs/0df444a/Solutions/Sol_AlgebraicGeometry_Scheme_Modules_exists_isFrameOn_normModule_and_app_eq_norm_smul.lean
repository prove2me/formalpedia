-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_normModule_and_app_eq_norm_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/cf045dcd-650d-5772-8faa-c666410d4b9d

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isFrameOn_normModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exteriorPower_map_app_unit_iotaMulti_eq_det_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_whiskerRight_app_tensorSections
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_and_app_eq_norm_smul

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite"

set_option maxHeartbeats 3200000 in
theorem solution
    {X X' : Scheme.{u}} (π : X' ⟶ X) (d : ℕ) [IsIso (Scheme.Modules.normModuleUnitEval π d)]
    {P : X'.Modules} (ι' : 𝟙_ X'.Modules ⟶ P) (U : X.Opens)
    (e : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules), U))
    (he : ∀ (W : X.Opens) (hW : W ≤ U),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).presheaf.map (homOfLE hW).op (e i))
    (s : Γ(P, π ⁻¹ᵁ U)) (hs : Scheme.Modules.IsFrameOn s (π ⁻¹ᵁ U))
    (g : Γ(X', π ⁻¹ᵁ U)) (hg : ι'.app (π ⁻¹ᵁ U) (Scheme.Modules.toUnitSection _ 1) = g • s) :
    letI : Algebra Γ(X, U) Γ(X', π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
    ∃ Ω : Γ(Scheme.Modules.normModule π d P, U), Scheme.Modules.IsFrameOn Ω U ∧
      (inv (Scheme.Modules.normModuleUnitEval π d) ≫ (Scheme.Modules.normModuleFunctor π d).map ι').app U
          (Scheme.Modules.toUnitSection U 1) = (Algebra.norm Γ(X, U) g) • Ω := by
  classical
  letI alg : Algebra Γ(X, U) Γ(X', π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra

  obtain ⟨q, hq, hq1, hΩ⟩ := Scheme.Modules.IsFrameOn.exists_isFrameOn_normModule π d e he hs
  refine ⟨_, hΩ, ?_⟩

  obtain ⟨b₀, hb₀⟩ := he U le_rfl
  have he' : ∀ i, b₀ i = e i := fun i => by
    rw [hb₀ i, show (homOfLE (le_refl U)).op = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]; rfl
  let b₁ : Module.Basis (Fin d) Γ(X, U) Γ(X', π ⁻¹ᵁ U) := Module.Basis.ofRepr
    { toFun := fun x => b₀.repr x
      invFun := fun c => b₀.repr.symm c
      map_add' := fun x y => b₀.repr.map_add x y
      map_smul' := fun r x => b₀.repr.map_smul r x
      left_inv := fun x => b₀.repr.symm_apply_apply x
      right_inv := fun c => b₀.repr.apply_symm_apply c }
  have hb₁ : ∀ i, b₁ i = (show Γ(X', π ⁻¹ᵁ U) from e i) := fun i => by
    change b₀.repr.symm (Finsupp.single i 1) = _
    rw [Module.Basis.repr_symm_single_one, he']

  set a : Matrix (Fin d) (Fin d) Γ(X, U) := Algebra.leftMulMatrix b₁ g with ha_def

  have hg' : ι'.app (π ⁻¹ᵁ U) (Scheme.Modules.unitSection (π ⁻¹ᵁ U)) = g • s := hg

  have h3 : ∀ j, (∑ i, (π.app U).hom (a i j) * (show Γ(X', π ⁻¹ᵁ U) from e i)) =
      g * (show Γ(X', π ⁻¹ᵁ U) from e j) := fun j => by
    have h := b₁.sum_repr (g * b₁ j)
    simp_rw [hb₁] at h
    refine (Finset.sum_congr rfl fun i _ => ?_).trans h
    rw [ha_def, Algebra.leftMulMatrix_eq_repr_mul, hb₁]
    rfl
  have ha : ∀ j, ((Scheme.Modules.pushforward π).map ι').app U (e j) = ∑ i, a i j • (fun i => (show Γ((Scheme.Modules.pushforward π).obj P, U) from (show Γ(X', π ⁻¹ᵁ U) from e i) • s)) i := by
    intro j
    rw [Scheme.Modules.pushforward_map_app]

    have happ := Scheme.Modules.Hom.app_smul ι' (show Γ(X', π ⁻¹ᵁ U) from e j)
      (Scheme.Modules.unitSection (π ⁻¹ᵁ U))
    rw [Scheme.Modules.smul_unitSection] at happ
    refine happ.trans ?_
    rw [hg', smul_smul]

    symm
    calc ∑ i, a i j • (fun i => (show Γ((Scheme.Modules.pushforward π).obj P, U) from (show Γ(X', π ⁻¹ᵁ U) from e i) • s)) i
        = ∑ i, (show Γ((Scheme.Modules.pushforward π).obj P, U) from
            ((π.app U).hom (a i j) * (show Γ(X', π ⁻¹ᵁ U) from e i)) • s) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          change (π.app U).hom (a i j) • ((show Γ(X', π ⁻¹ᵁ U) from e i) • s) = _
          rw [smul_smul]
      _ = (show Γ((Scheme.Modules.pushforward π).obj P, U) from
            (∑ i, (π.app U).hom (a i j) * (show Γ(X', π ⁻¹ᵁ U) from e i)) • s) := by
          change _ = (∑ i, (π.app U).hom (a i j) * (show Γ(X', π ⁻¹ᵁ U) from e i)) • s
          rw [Finset.sum_smul]
          rfl
      _ = (show Γ((Scheme.Modules.pushforward π).obj P, U) from
            ((show Γ(X', π ⁻¹ᵁ U) from e j) * g) • s) := by
          rw [h3 j, mul_comm]

  have key := Scheme.Modules.exteriorPower_map_app_unit_iotaMulti_eq_det_smul
    ((Scheme.Modules.pushforward π).map ι') (U := U) e (fun i => (show Γ((Scheme.Modules.pushforward π).obj P, U) from (show Γ(X', π ⁻¹ᵁ U) from e i) • s)) a ha
  have hdet : a.det = Algebra.norm Γ(X, U) g := (Algebra.norm_eq_matrix_det b₁ g).symm

  have hev : (Scheme.Modules.normModuleUnitEval π d).app U (Scheme.Modules.tensorSections (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            ((Scheme.Modules.presheafExteriorPower X d).obj ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).val)).app
          (op U)
          (show ((Scheme.Modules.presheafExteriorPower X d).obj
              ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).val).obj (op U) from exteriorPower.ιMulti Γ(X, U) d e)) q) =
      Scheme.Modules.toUnitSection U 1 := by
    change ((ihom.ev (Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)))).app
      (𝟙_ X.Modules)).app U (Scheme.Modules.tensorSections (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            ((Scheme.Modules.presheafExteriorPower X d).obj ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).val)).app
          (op U)
          (show ((Scheme.Modules.presheafExteriorPower X d).obj
              ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).val).obj (op U) from exteriorPower.ιMulti Γ(X, U) d e)) q) = _
    rw [Scheme.Modules.ihom_ev_app_tensorSections]
    exact hq1
  have hinv : (inv (Scheme.Modules.normModuleUnitEval π d)).app U (Scheme.Modules.toUnitSection U 1) =
      Scheme.Modules.tensorSections (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            ((Scheme.Modules.presheafExteriorPower X d).obj ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).val)).app
          (op U)
          (show ((Scheme.Modules.presheafExteriorPower X d).obj
              ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).val).obj (op U) from exteriorPower.ιMulti Γ(X, U) d e)) q := by
    rw [← hev, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, IsIso.hom_inv_id]
    rfl
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, hinv, Scheme.Modules.normModuleFunctor_map]
  erw [Scheme.Modules.whiskerRight_app_tensorSections, key, Scheme.Modules.tensorSections_smul_left, hdet]
  all_goals rfl

end S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_and_app_eq_norm_smul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_and_app_eq_norm_smul (solution)
