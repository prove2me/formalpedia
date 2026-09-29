-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_of_isIso_pullbackSection_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a66069b8-416d-5e97-a183-5b90a8cbebcb

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_isIso_pullbackSection_of_surjective

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

namespace P2Nak

theorem ne_zero_of_isIso {k : Type} [Field k] {N : (Spec (CommRingCat.of k)).Modules}
    (f : 𝟙_ (Spec (CommRingCat.of k)).Modules ⟶ N) [IsIso f] : f ≠ 0 := by
  intro hf
  subst hf
  have h1 : 𝟙 (𝟙_ (Spec (CommRingCat.of k)).Modules) = 0 := by
    rw [← IsIso.hom_inv_id (0 : 𝟙_ (Spec (CommRingCat.of k)).Modules ⟶ N), Limits.zero_comp]
  have h2 := congrArg (fun φ => Scheme.Modules.ofUnitSection ⊤ (Scheme.Modules.Hom.app φ ⊤ (Scheme.Modules.toUnitSection ⊤ 1))) h1
  simp only [Scheme.Modules.Hom.id_app, Scheme.Modules.Hom.zero_app] at h2
  have h3 : (1 : Γ(Spec (CommRingCat.of k), ⊤)) = 0 := h2
  have h4 : (1 : k) = 0 := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom h3
    simpa using this
  exact one_ne_zero h4

theorem isIso_pullbackSection_comp {X Y Z : Scheme.{0}} (a : Z ⟶ Y) (g : Y ⟶ X) {P : X.Modules}
    (s : 𝟙_ X.Modules ⟶ P) (hs : IsIso (Scheme.Modules.pullbackSection g s)) :
    IsIso (Scheme.Modules.pullbackSection (a ≫ g) s) := by
  haveI i0 : IsIso (Scheme.Modules.pullbackSection g s) := hs
  have h1 : (Scheme.Modules.pullback g).map s =
      (Scheme.Modules.pullbackUnitIso g).hom ≫ Scheme.Modules.pullbackSection g s := by
    simp [Scheme.Modules.pullbackSection_def]
  haveI i1 : IsIso ((Scheme.Modules.pullback g).map s) := by
    rw [h1]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance i0
  haveI i2 : IsIso ((Scheme.Modules.pullback a).map ((Scheme.Modules.pullback g).map s)) := Functor.map_isIso _ _
  haveI i2' : IsIso ((Scheme.Modules.pullbackComp a g).hom.app P) := Iso.isIso_hom ((Scheme.Modules.pullbackComp a g).app P)
  haveI i3 : IsIso ((Scheme.Modules.pullback a).map ((Scheme.Modules.pullback g).map s) ≫
      (Scheme.Modules.pullbackComp a g).hom.app P) := @IsIso.comp_isIso _ _ _ _ _ _ _ i2 i2'
  have h2 : (Scheme.Modules.pullbackComp a g).hom.app _ ≫ (Scheme.Modules.pullback (a ≫ g)).map s =
      (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback g).map s) ≫ (Scheme.Modules.pullbackComp a g).hom.app P :=
    ((Scheme.Modules.pullbackComp a g).hom.naturality s).symm
  rw [← h2] at i3
  haveI i2'' : IsIso ((Scheme.Modules.pullbackComp a g).hom.app (𝟙_ X.Modules)) :=
    Iso.isIso_hom ((Scheme.Modules.pullbackComp a g).app _)
  haveI i4 : IsIso ((Scheme.Modules.pullback (a ≫ g)).map s) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ ((Scheme.Modules.pullbackComp a g).hom.app _) _ i2'' i3
  rw [Scheme.Modules.pullbackSection_def]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance i4

end P2Nak

theorem solution
    {X Z : Scheme.{0}} (g : Z ⟶ X) (hg : Function.Surjective g.base)
    (P : X.Modules) (hP : Scheme.Modules.IsInvertible P) (s : 𝟙_ X.Modules ⟶ P)
    (hs : IsIso (Scheme.Modules.pullbackSection g s)) :
    IsIso s := by
  classical

  have hsupp : ∀ x : X, x ∉ (Scheme.Modules.zeroSchemeIdeal s).support := by
    intro x hx
    obtain ⟨z, rfl⟩ := hg x
    let pt : Spec (CommRingCat.of (IsLocalRing.ResidueField ↑(Z.presheaf.stalk z))) ⟶ X :=
      Z.fromSpecResidueField z ≫ g
    have hiso : IsIso (Scheme.Modules.pullbackSection pt s) := P2Nak.isIso_pullbackSection_comp _ g s hs
    have hne := P2Nak.ne_zero_of_isIso (Scheme.Modules.pullbackSection pt s)
    apply hne
    rw [AlgebraicGeometry.Scheme.Modules.IsInvertible.pullbackSection_eq_zero_iff_mem_support_monoidalV2 hP s pt]
    have hb : pt.base (IsLocalRing.closedPoint _) = g.base z := by
      show g.base ((Z.fromSpecResidueField z).base _) = g.base z
      rw [Scheme.fromSpecResidueField_apply]
    rw [hb]
    exact hx
  have hdis : Disjoint ((⊤ : X.Opens) : Set X) (Scheme.Modules.zeroSchemeIdeal s).support :=
    Set.disjoint_left.mpr fun x _ hx => hsupp x hx
  have hq := AlgebraicGeometry.Scheme.Modules.IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal_monoidalV2 hP s ⊤ hdis
  have hp : Scheme.Modules.IsFrameOn (Scheme.Modules.unitSection (⊤ : X.Opens)) ⊤ :=
    Scheme.Modules.isFrameOn_unitSection ⊤
  exact AlgebraicGeometry.Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top_monoidalV2 s
    (fun _ : Unit => (⊤ : X.Opens)) (by simp) (fun _ => Scheme.Modules.unitSection ⊤)
    (fun _ => s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) (fun _ => hp) (fun _ => hq) (fun _ => rfl)

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_isIso_pullbackSection_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_isIso_pullbackSection_of_surjective (solution)
