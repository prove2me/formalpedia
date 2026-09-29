-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/cc23efd8-9e68-5ebc-91f1-28aa83844dc1

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace FrameSpecSol

variable {X : Scheme.{u}}

noncomputable abbrev res (M : X.Modules) (m : Γ(M, ⊤)) (W : X.Opens) : Γ(M, W) :=
  M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op m

def IsFrame (M : X.Modules) (m : Γ(M, ⊤)) (U : X.Opens) : Prop :=
  ∀ W : X.Opens, W ≤ U → Function.Bijective fun g : Γ(X, W) => g • res M m W

theorem res_map (M : X.Modules) (m : Γ(M, ⊤)) {W W' : X.Opens} (i : W' ⟶ W) :
    M.presheaf.map i.op (res M m W) = res M m W' := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

theorem smul_res (M : X.Modules) (m : Γ(M, ⊤)) {W W' : X.Opens} (i : W' ⟶ W) (g : Γ(X, W)) :
    M.presheaf.map i.op (g • res M m W) = X.presheaf.map i.op g • res M m W' := by
  rw [Scheme.Modules.map_smul, res_map]

theorem res_smul (M : X.Modules) (H : Γ(X, ⊤)) (m : Γ(M, ⊤)) (W : X.Opens) :
    res M (H • m) W = X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op H • res M m W := by
  rw [res, Scheme.Modules.map_smul]

theorem app_res {M N : X.Modules} (φ : M ⟶ N) (m : Γ(M, ⊤)) (W : X.Opens) :
    φ.app W (res M m W) = res N (φ.app ⊤ m) W := by
  have := ((PresheafOfModules.toPresheaf _).map φ.val).naturality (homOfLE (le_top : W ≤ ⊤)).op
  exact (ConcreteCategory.congr_hom this m)

theorem IsFrame.of_iso {M N : X.Modules} (e : M ≅ N) {m : Γ(M, ⊤)} {U : X.Opens} (hm : IsFrame M m U) :
    IsFrame N (e.hom.app ⊤ m) U := by
  intro W hW
  have key : (fun g : Γ(X, W) => g • res N (e.hom.app ⊤ m) W) =
      (e.hom.app W) ∘ (fun g : Γ(X, W) => g • res M m W) := by
    funext g
    simp only [Function.comp_apply, Scheme.Modules.Hom.app_smul, app_res]
  rw [key]
  exact (ConcreteCategory.bijective_of_isIso (e.hom.app W)).comp (hm W hW)

theorem isFrame_of_iso_unit {M : X.Modules} (e : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsFrame M (e.inv.app ⊤ (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), ⊤) from (1 : Γ(X, ⊤)))) ⊤ := by
  have h1 : IsFrame (SheafOfModules.unit X.ringCatSheaf : X.Modules)
      (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), ⊤) from (1 : Γ(X, ⊤))) ⊤ := by
    intro W _
    have hres : res (SheafOfModules.unit X.ringCatSheaf : X.Modules)
        (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), ⊤) from (1 : Γ(X, ⊤))) W =
        (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), W) from (1 : Γ(X, W))) := by
      change ((X.ringCatSheaf.obj.map (homOfLE (le_top : W ≤ ⊤)).op).hom 1) = 1
      exact map_one _
    rw [hres]
    change Function.Bijective fun g : Γ(X, W) => g * 1
    simp only [mul_one]
    exact Function.bijective_id
  simpa using h1.of_iso e.symm

theorem isUnit_germ_of_isFrame_smul {M : X.Modules} {T : Γ(M, ⊤)} {U : X.Opens} (hT : IsFrame M T U)
    (H : Γ(X, ⊤)) {z : X} {V : X.Opens} (hzV : z ∈ V) (hVU : V ≤ U) (hHT : IsFrame M (H • T) V) :
    IsUnit (X.presheaf.germ V z hzV (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op H)) := by
  have hb := hHT V le_rfl
  have hbT := hT V hVU

  have key : (fun g : Γ(X, V) => g • res M (H • T) V) =
      (fun g : Γ(X, V) => g • res M T V) ∘ (fun g => g * X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op H) := by
    funext g
    simp only [Function.comp_apply, res_smul, mul_smul]
  rw [key] at hb
  have hmul : Function.Bijective (fun g : Γ(X, V) => g * X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op H) :=
    (Function.Bijective.of_comp_iff' hbT _).1 hb
  obtain ⟨g, hg⟩ := hmul.2 1
  have hu : IsUnit (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op H) := isUnit_iff_exists_inv'.2 ⟨g, hg⟩
  exact hu.map _

theorem exists_isFrame_smul_of_isUnit_germ {M : X.Modules} {T : Γ(M, ⊤)} {U : X.Opens} (hT : IsFrame M T U)
    (H : Γ(X, ⊤)) {z : X} (hzU : z ∈ U)
    (hu : IsUnit (X.presheaf.germ U z hzU (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op H))) :
    ∃ V : X.Opens, z ∈ V ∧ IsFrame M (H • T) V := by
  refine ⟨X.basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op H),
    (X.mem_basicOpen _ z hzU).2 hu, fun V hV => ?_⟩
  have hVU : V ≤ U := hV.trans (X.basicOpen_le _)
  have huV : IsUnit (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op H) := by
    have h0 := RingedSpace.isUnit_res_basicOpen (X := X.toLocallyRingedSpace.toSheafedSpace)
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op H)
    have hcomp : X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op H =
        X.presheaf.map (homOfLE hV).op (X.presheaf.map (homOfLE (X.basicOpen_le _)).op
          (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op H)) := by
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl
    rw [hcomp]
    exact h0.map (CommRingCat.Hom.hom (X.presheaf.map (homOfLE hV).op))
  have key : (fun g : Γ(X, V) => g • res M (H • T) V) =
      (fun g : Γ(X, V) => g • res M T V) ∘ (fun g => g * X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op H) := by
    funext g
    simp only [Function.comp_apply, res_smul, mul_smul]
  rw [key]
  obtain ⟨u', hu'⟩ := huV
  refine (hT V hVU).comp ?_
  rw [← hu']
  exact (Units.mulRight u').bijective

end FrameSpecSol

namespace FrameSpecSol

variable {X : Scheme.{u}}

theorem res_top (M : X.Modules) (m : Γ(M, ⊤)) : res M m ⊤ = m := by
  have : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ := rfl
  simp [res]

theorem IsFrame.of_openImmersion {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules) (m : Γ(M, ⊤))
    {U' : Y.Opens}
    (hfr : IsFrame ((Scheme.Modules.pullback j).obj M)
      (show Γ((Scheme.Modules.pullback j).obj M, ⊤) from
        (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app ⊤) m) U') :
    IsFrame M m (j ''ᵁ U') := by
  intro V hV
  have hVr : V ≤ j.opensRange := hV.trans (j.image_le_opensRange U')
  haveI : IsIso (j.app V) := j.isIso_app V hVr
  have ha : Function.Bijective (j.app V) := ConcreteCategory.bijective_of_isIso (j.app V)
  have hb : Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app V) :=
    Scheme.Modules.bijective_unit_app_of_le_opensRange j M V hVr
  have hW' : j ⁻¹ᵁ V ≤ U' :=
    (show j ⁻¹ᵁ V ≤ j ⁻¹ᵁ (j ''ᵁ U') from fun x hx => hV hx).trans_eq (j.preimage_image_eq U')
  have hψ := hfr (j ⁻¹ᵁ V) hW'

  have key : (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app V) ∘
      (fun g : Γ(X, V) => g • res M m V) =
      (fun g : Γ(Y, j ⁻¹ᵁ V) => g • res ((Scheme.Modules.pullback j).obj M)
        (show Γ((Scheme.Modules.pullback j).obj M, ⊤) from
          (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app ⊤) m) (j ⁻¹ᵁ V)) ∘ (j.app V) := by
    funext g
    simp only [Function.comp_apply]
    erw [Scheme.Modules.Hom.app_smul, app_res]
    rfl
  have hcomp : Function.Bijective ((((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app V) ∘
      (fun g : Γ(X, V) => g • res M m V)) := by
    rw [key]; exact hψ.comp ha
  exact (Function.Bijective.of_comp_iff' hb _).1 hcomp

end FrameSpecSol

namespace FrameSpecSol

variable {X : Scheme.{u}}

theorem exists_iso_forall_unit_eq {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X)
    (hh : g ≫ f = h) (M : X.Modules) :
    ∃ e : (Scheme.Modules.pullback h).obj M ≅ (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M),
      ∀ s : Γ(M, ⊤),
        (e.hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M).app ⊤) s) =
          (show Γ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M), ⊤) from
            (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app ((Scheme.Modules.pullback f).obj M)).app ⊤)
              (show Γ((Scheme.Modules.pullback f).obj M, ⊤) from
                (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤) s)) := by
  subst hh
  refine ⟨((Scheme.Modules.pullbackComp g f).app M).symm, fun s => ?_⟩
  exact CategoryTheory.ConcreteCategory.congr_hom (Scheme.Modules.unit_app_comp_pullbackComp_inv g f M ⊤) s

noncomputable abbrev pb {X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules) (m : Γ(M, ⊤)) :
    Γ((Scheme.Modules.pullback p).obj M, ⊤) :=
  show Γ((Scheme.Modules.pullback p).obj M, ⊤) from
    (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) m

theorem pb_smul {X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules) (r : Γ(X, ⊤)) (m : Γ(M, ⊤)) :
    pb p M (r • m) = p.appTop r • pb p M m := by
  dsimp only [pb]
  erw [Scheme.Modules.Hom.app_smul]
  rfl

theorem main {X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (m : Γ(M, ⊤)) (z : X') (h : ∃ U' : X'.Opens, z ∈ U' ∧ IsFrame ((Scheme.Modules.pullback p).obj M) (pb p M m) U') :
    ∃ U : X.Opens, p z ∈ U ∧ IsFrame M m U := by
  classical
  obtain ⟨U, hyU, ⟨eU⟩⟩ := hM.1 (p z)
  obtain ⟨U', hzU', hU'⟩ := h

  let j : (↑U : Scheme.{u}) ⟶ X := U.ι
  let j' : (↑(p ⁻¹ᵁ U) : Scheme.{u}) ⟶ X' := (p ⁻¹ᵁ U).ι
  let pU : (↑(p ⁻¹ᵁ U) : Scheme.{u}) ⟶ ↑U := p ∣_ U
  have hcomm : pU ≫ j = j' ≫ p := morphismRestrict_ι p U
  let z' : ↑(p ⁻¹ᵁ U) := ⟨z, hyU⟩
  have hjz' : j' z' = z := rfl

  let MU : (↑U : Scheme.{u}).Modules := (Scheme.Modules.pullback j).obj M
  let τ : Γ(MU, ⊤) := eU.inv.app ⊤ (show Γ((SheafOfModules.unit (↑U : Scheme.{u}).ringCatSheaf :
    (↑U : Scheme.{u}).Modules), ⊤) from (1 : Γ(↑U, ⊤)))
  have hτ : IsFrame MU τ ⊤ := isFrame_of_iso_unit eU
  obtain ⟨hf, hhf⟩ := (hτ ⊤ le_rfl).2 (pb j M m)
  have hmU : pb j M m = hf • τ := by rw [← hhf]; simp only [res_top]

  have h3a : IsFrame ((Scheme.Modules.pullback j').obj ((Scheme.Modules.pullback p).obj M))
      (pb j' _ (pb p M m)) (j' ⁻¹ᵁ U') := fun W hW =>
    Scheme.Modules.bijective_smul_unit_app_of_bijective_smul j' _ (pb p M m) hU' W hW
  obtain ⟨e₁, he₁⟩ := exists_iso_forall_unit_eq j' p (j' ≫ p) rfl M
  obtain ⟨e₂, he₂⟩ := exists_iso_forall_unit_eq pU j (j' ≫ p) hcomm M
  have he : ((e₁.symm ≪≫ e₂).hom.app ⊤) (pb j' _ (pb p M m)) = pb pU MU (pb j M m) := by
    have h1 : (e₁.inv.app ⊤) (pb j' _ (pb p M m)) = pb (j' ≫ p) M m := by
      have h2 := congrArg (e₁.inv.app ⊤) (he₁ m)
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
        Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] at h2
      exact h2.symm
    rw [Iso.trans_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, Iso.symm_hom, h1]
    exact he₂ m
  have h3 : IsFrame ((Scheme.Modules.pullback pU).obj MU) (pb pU MU (pb j M m)) (j' ⁻¹ᵁ U') := by
    rw [← he]; exact h3a.of_iso _

  have hT : IsFrame ((Scheme.Modules.pullback pU).obj MU) (pb pU MU τ) ⊤ := fun W hW =>
    Scheme.Modules.bijective_smul_unit_app_of_bijective_smul pU MU τ hτ W (by simp)
  rw [hmU, pb_smul] at h3
  have h5 := isUnit_germ_of_isFrame_smul hT (pU.appTop hf) (z := z') (V := j' ⁻¹ᵁ U') hzU' le_top h3

  have h6 : IsUnit ((↑U : Scheme.{u}).presheaf.germ ⊤ (pU z') trivial hf) := by
    rw [← isUnit_map_iff (CommRingCat.Hom.hom (pU.stalkMap z')), ← CommRingCat.comp_apply,
      Scheme.Hom.germ_stalkMap pU ⊤ z' trivial]
    rw [TopCat.Presheaf.germ_res_apply] at h5
    convert h5 using 1
    rfl

  obtain ⟨V, hzV, hV⟩ := exists_isFrame_smul_of_isUnit_germ hτ hf (z := pU z') (U := ⊤) trivial
    (by simp [res_top] at h6 ⊢; exact h6)
  rw [← hmU] at hV

  refine ⟨j ''ᵁ V, ?_, IsFrame.of_openImmersion j M m hV⟩
  refine ⟨pU z', hzV, ?_⟩
  show (pU ≫ j) z' = p z
  rw [hcomm]; rfl

end FrameSpecSol

theorem solution
    {X X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (m : Γ(M, ⊤)) (z : X')
    (h : ∃ U' : X'.Opens, z ∈ U' ∧ ∀ V' : X'.Opens, V' ≤ U' →
      Function.Bijective fun g : Γ(X', V') =>
        g • (((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) m) :
            Γ((Scheme.Modules.pullback p).obj M, V'))) :
    ∃ U : X.Opens, p z ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op m : Γ(M, V)) :=
  FrameSpecSol.main p M hM m z h

end S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback (solution)
