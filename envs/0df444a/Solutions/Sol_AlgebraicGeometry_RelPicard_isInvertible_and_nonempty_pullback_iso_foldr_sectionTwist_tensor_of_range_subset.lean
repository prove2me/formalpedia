-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isInvertible_and_nonempty_pullback_iso_foldr_sectionTwist_tensor_of_range_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e7d797f7-7317-5db7-aff5-0923ec1dd0d9

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionIdeal_pow_module_iso_of_smoothLocus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isInvertible_and_nonempty_pullback_iso_foldr_sectionTwist_tensor_of_range_subset
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver"
p2m_attr_erase "simp" "AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc"

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

set_option maxHeartbeats 3200000 in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {m : ℕ} (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hσ : ∀ j, Set.range (σ j).1 ⊆ (U : Set C)) (pos neg : Fin m → ℕ)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    Scheme.Modules.IsInvertible
        ((List.finRange m).foldr
          (fun j M => (sectionTwist c (σ j) t (pos j) ⊗ ((sectionIdeal c (σ j) t) ^ (neg j)).module) ⊗ M)
          (𝟙_ (pullback c t).Modules)) ∧
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj
          ((List.finRange m).foldr
            (fun j M => (sectionTwist c (σ j) t (pos j) ⊗ ((sectionIdeal c (σ j) t) ^ (neg j)).module) ⊗ M)
            (𝟙_ (pullback c t).Modules)) ≅
        (List.finRange m).foldr
          (fun j M => (sectionTwist c (σ j) t' (pos j) ⊗ ((sectionIdeal c (σ j) t') ^ (neg j)).module) ⊗ M)
          (𝟙_ (pullback c t').Modules)) := by

  have hI : ∀ {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R)) (j : Fin m),
      (sectionIdeal c (σ j) t₀).IsInvertible :=
    fun t₀ j => isInvertible_sectionIdeal_of_range_subset c (σ j) U (hσ j) t₀

  have hN : ∀ {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R)) (j : Fin m),
      Scheme.Modules.IsInvertible
        (sectionTwist c (σ j) t₀ (pos j) ⊗ ((sectionIdeal c (σ j) t₀) ^ (neg j)).module) :=
    fun t₀ j => Scheme.Modules.IsInvertible.tensor
      (Scheme.IdealSheafData.IsInvertible.isInvertible_invModule ((hI t₀ j).pow (pos j)))
      (Scheme.IdealSheafData.IsInvertible.isInvertible_module ((hI t₀ j).pow (neg j)))

  have eN : ∀ j : Fin m, Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj
        (sectionTwist c (σ j) t (pos j) ⊗ ((sectionIdeal c (σ j) t) ^ (neg j)).module) ≅
      sectionTwist c (σ j) t' (pos j) ⊗ ((sectionIdeal c (σ j) t') ^ (neg j)).module) := fun j =>
    ⟨Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _ ≪≫
      tensorIso (nonempty_pullback_sectionTwist_iso_of_range_subset R c (σ j) U (hσ j) ψ (pos j)).some
        (nonempty_pullback_sectionIdeal_pow_module_iso_of_smoothLocus R c U (σ j) (hσ j) ψ (neg j)).some⟩

  have key : ∀ l : List (Fin m),
      Scheme.Modules.IsInvertible
          (l.foldr (fun j M => (sectionTwist c (σ j) t (pos j) ⊗ ((sectionIdeal c (σ j) t) ^ (neg j)).module) ⊗ M)
            (𝟙_ (pullback c t).Modules)) ∧
        Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj
            (l.foldr (fun j M => (sectionTwist c (σ j) t (pos j) ⊗ ((sectionIdeal c (σ j) t) ^ (neg j)).module) ⊗ M)
              (𝟙_ (pullback c t).Modules)) ≅
          l.foldr (fun j M => (sectionTwist c (σ j) t' (pos j) ⊗ ((sectionIdeal c (σ j) t') ^ (neg j)).module) ⊗ M)
            (𝟙_ (pullback c t').Modules)) := by
    intro l
    induction l with
    | nil =>
        exact ⟨Scheme.Modules.isInvertible_unit _, ⟨Scheme.Modules.pullbackTensorUnitObjIso (baseChangeSnd c ψ)⟩⟩
    | cons j l ih =>
        simp only [List.foldr_cons]
        exact ⟨(hN t j).tensor ih.1,
          ⟨Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _ ≪≫ tensorIso (eN j).some ih.2.some⟩⟩
  exact key (List.finRange m)

end S_AlgebraicGeometry_RelPicard_isInvertible_and_nonempty_pullback_iso_foldr_sectionTwist_tensor_of_range_subset
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isInvertible_and_nonempty_pullback_iso_foldr_sectionTwist_tensor_of_range_subset (solution)
