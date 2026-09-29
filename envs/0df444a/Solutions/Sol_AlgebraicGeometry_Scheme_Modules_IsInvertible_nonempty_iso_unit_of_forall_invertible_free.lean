-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_forall_invertible_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a8ddf9cb-bc09-5d11-b283-3517ca4ceb0d

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finrank_baseChange_sections_eq_one_of_locallyTrivial
import Theorems.Thm_Module_Invertible_of_projective_of_forall_finrank_eq_one
import Theorems.Thm_Module_Invertible_of_ringEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_forall_invertible_free

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite TensorProduct"

namespace LFRAME

variable (R : Type u) [CommRing R]

noncomputable abbrev X : Scheme.{u} := Spec (CommRingCat.of R)

noncomputable abbrev N₀ (L : (X R).Modules) : ModuleCat.{u} R :=
  (modulesSpecToSheaf (R := CommRingCat.of R) |>.obj L).presheaf.obj (op ⊤)

noncomputable def Utop : (X R).affineOpens := ⟨⊤, isAffineOpen_top (X R)⟩

noncomputable def σ : R ≃+* Γ(X R, ⊤) :=
  (StructureSheaf.globalSectionsIso R).commRingCatIsoToRingEquiv

@[reducible] noncomputable def modR (L : (X R).Modules) : Module R Γ(L, ⊤) :=
  inferInstanceAs (Module R (N₀ R L))

theorem smul_eq (L : (X R).Modules) (r : R) (m : Γ(L, ⊤)) :
    (letI : Module R Γ(L, ⊤) := modR R L; r • m) = (σ R r) • m := rfl

variable (L : (X R).Modules)
  (htriv : ∀ x : X R, ∃ (V : (X R).Opens), x ∈ V ∧
    Nonempty ((Scheme.Modules.pullback V.ι).obj L ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))

include htriv in

theorem invertibleTop : Module.Invertible Γ(X R, ⊤) Γ(L, ⊤) := by
  haveI : Module.Finite Γ(X R, (Utop R).1) Γ(L, (Utop R).1) :=
    AlgebraicGeometry.Scheme.Modules.finite_sections_of_locallyTrivial L htriv (Utop R)
  haveI : Module.Projective Γ(X R, (Utop R).1) Γ(L, (Utop R).1) :=
    AlgebraicGeometry.Scheme.Modules.projective_sections_of_locallyTrivial L htriv (Utop R)
  exact Module.Invertible.of_projective_of_forall_finrank_eq_one (A := Γ(X R, (Utop R).1))
    Γ(L, (Utop R).1)
    (fun K _ _ =>
      AlgebraicGeometry.Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial
        L htriv (Utop R) K)

include htriv in

theorem invertibleR : @Module.Invertible R Γ(L, ⊤) _ _ (modR R L) := by
  haveI := invertibleTop R L htriv
  letI : Module R Γ(L, ⊤) := modR R L
  exact Module.Invertible.of_ringEquiv (σ R) Γ(L, ⊤) (fun r m => smul_eq R L r m)

set_option maxHeartbeats 3200000 in
include htriv in
theorem main
    (hPic : ∀ (N : Type u) [AddCommGroup N] [Module R N], Module.Invertible R N → Module.Free R N) :
    Nonempty (L ≅ SheafOfModules.unit (X R).ringCatSheaf) := by
  haveI hiso : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) L) :=
    AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial (R := CommRingCat.of R) L htriv
  letI : Module R Γ(L, ⊤) := modR R L
  haveI hinvR : Module.Invertible R Γ(L, ⊤) := invertibleR R L htriv
  haveI hfree : Module.Free R Γ(L, ⊤) := hPic Γ(L, ⊤) hinvR
  obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := R) (M := Γ(L, ⊤))).mp hfree
  let ι : N₀ R L ≅ ModuleCat.of R R := e.toModuleIso
  let i₁ : L ≅ tilde (N₀ R L) := (asIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) L)).symm
  let i₂ : tilde (N₀ R L) ≅ tilde (ModuleCat.of R R) := (tilde.functor (CommRingCat.of R)).mapIso ι
  let i₃ : tilde (ModuleCat.of R R) ≅ SheafOfModules.unit (X R).ringCatSheaf :=
    tildeSelf (R := CommRingCat.of R)
  exact ⟨i₁ ≪≫ i₂ ≪≫ i₃⟩

end LFRAME

set_option maxHeartbeats 1600000 in
theorem solution (R : Type u) [CommRing R]
    (hPic : ∀ (N : Type u) [AddCommGroup N] [Module R N], Module.Invertible R N → Module.Free R N)
    (L : (Spec (CommRingCat.of R)).Modules) (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (L ≅ 𝟙_ (Spec (CommRingCat.of R)).Modules) := by
  obtain ⟨i⟩ := LFRAME.main R L hL.1 hPic
  exact ⟨i ≪≫ eqToIso (Scheme.Modules.tensorUnit_eq (X := Spec (CommRingCat.of R))).symm⟩

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_forall_invertible_free
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_forall_invertible_free (solution)
