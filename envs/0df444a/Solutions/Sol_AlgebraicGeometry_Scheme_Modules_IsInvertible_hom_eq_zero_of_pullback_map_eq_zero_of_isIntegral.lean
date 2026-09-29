-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.hom_eq_zero_of_pullback_map_eq_zero_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/283efa7c-0732-5e1c-95e4-ec607ba3a683

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_hom_eq_zero_of_pullback_map_eq_zero_of_isIntegral

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlphaStub

open Opposite

theorem res_injective {Y : Scheme} [IsIntegral Y] {O₁ O₂ : Y.Opens} (i : O₂ ⟶ O₁) (hne : (O₂ : Set Y).Nonempty) :
    Function.Injective (Y.presheaf.map i.op) := by
  intro a b hab
  have hξ : genericPoint Y ∈ O₂ := ((genericPoint_spec Y).mem_open_set_iff O₂.isOpen).mpr (by simpa using hne)
  apply germ_injective_of_isIntegral Y (genericPoint Y) (i.le hξ)
  rw [← TopCat.Presheaf.germ_res_apply Y.presheaf i (genericPoint Y) hξ a,
    ← TopCat.Presheaf.germ_res_apply Y.presheaf i (genericPoint Y) hξ b, hab]

theorem restrictFunctor_map_eq_zero {X Y : Scheme} (f : Y ⟶ X) [IsOpenImmersion f] {𝓛 𝓜 : X.Modules} (φ : 𝓛 ⟶ 𝓜)
    (h : (Scheme.Modules.pullback f).map φ = 0) : (Scheme.Modules.restrictFunctor f).map φ = 0 := by
  let e := Scheme.Modules.restrictFunctorIsoPullback f
  have hn := e.hom.naturality φ
  rw [h, comp_zero] at hn
  rw [← cancel_mono (e.hom.app _), hn, zero_comp]

theorem app_eq_zero_of_le {X : Scheme} {𝓛 𝓜 : X.Modules} (φ : 𝓛 ⟶ 𝓜) (U : X.Opens)
    (h : (Scheme.Modules.pullback U.ι).map φ = 0) (O : X.Opens) (hO : O ≤ U) : φ.app O = 0 := by
  have h1 := restrictFunctor_map_eq_zero U.ι φ h
  have h2 : ((Scheme.Modules.restrictFunctor U.ι).map φ).app (U.ι ⁻¹ᵁ O) = 0 := by rw [h1]; rfl
  have h3 : φ.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ O)) = 0 := h2
  have hO' : U.ι ''ᵁ (U.ι ⁻¹ᵁ O) = O := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hO]
  rw [hO'] at h3
  exact h3

end AlphaStub

namespace AlphaStub

open Opposite

theorem hom_eq_zero_of_pullback_ι_map_eq_zero {X : Scheme} [IsIntegral X] {𝓛 𝓜 : X.Modules}
    (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (φ : 𝓛 ⟶ 𝓜)
    (U : X.Opens) (hU : (U : Set X).Nonempty) (h : (Scheme.Modules.pullback U.ι).map φ = 0) : φ = 0 := by
  apply Scheme.Modules.hom_ext
  intro V
  rw [Scheme.Modules.Hom.zero_app]
  ext x
  show (φ.app V) x = 0

  choose W hW eW using h𝓜.exists_trivialization

  let C : V → X.Opens := fun y => (W y.1).ι ''ᵁ ((W y.1).ι ⁻¹ᵁ V)
  have hC : ∀ y : V, C y = W y.1 ⊓ V := fun y => by
    show (W y.1).ι ''ᵁ ((W y.1).ι ⁻¹ᵁ V) = W y.1 ⊓ V
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hCV : ∀ y : V, C y ≤ V := fun y => by rw [hC]; exact inf_le_right
  have hcover : V ≤ ⨆ y : V, C y := by
    intro v hv
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨v, hv⟩, by rw [hC]; exact ⟨hW v, hv⟩⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨𝓜.presheaf, 𝓜.isSheaf⟩ : TopCat.Sheaf Ab X.carrier) C V
    (fun y => homOfLE (hCV y)) hcover ((φ.app V) x) 0 (fun y => ?_)
  rw [map_zero]

  obtain ⟨y, hyV⟩ := y
  obtain ⟨e⟩ := eW y
  let W₀ := W y
  let ιW := (W y).ι
  let W₁ : (W₀ : Scheme).Opens := ιW ⁻¹ᵁ V
  let W₂ : (W₀ : Scheme).Opens := ιW ⁻¹ᵁ (V ⊓ U)
  have h21 : W₂ ≤ W₁ := fun w hw => hw.1
  let T : (Scheme.Modules.restrictFunctor ιW).obj 𝓜 ≅ SheafOfModules.unit (W₀ : Scheme).ringCatSheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback ιW).app 𝓜 ≪≫ e

  let a : Γ(𝓜, ιW ''ᵁ W₁) := 𝓜.presheaf.map (homOfLE (hCV ⟨y, hyV⟩)).op ((φ.app V) x)
  show a = 0
  have hle₂ : ιW ''ᵁ W₂ ≤ U := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact hw.2
  have ha₂ : 𝓜.presheaf.map (ιW.opensFunctor.map (homOfLE h21)).op a = 0 := by
    show 𝓜.presheaf.map (ιW.opensFunctor.map (homOfLE h21)).op (𝓜.presheaf.map (homOfLE (hCV ⟨y, hyV⟩)).op ((φ.app V) x)) = 0
    rw [← CategoryTheory.comp_apply, ← 𝓜.presheaf.map_comp, ← op_comp]
    have hn := PresheafOfModules.naturality_apply φ.val ((ιW.opensFunctor.map (homOfLE h21)) ≫ homOfLE (hCV ⟨y, hyV⟩)).op x

    refine (hn.symm).trans ?_
    have hz := app_eq_zero_of_le φ U h (ιW ''ᵁ W₂) hle₂
    show (φ.app (ιW ''ᵁ W₂)) _ = 0
    rw [hz]
    rfl

  have hb : (W₀ : Scheme).presheaf.map (homOfLE h21).op (T.hom.app W₁ a) = 0 := by
    have hn := PresheafOfModules.naturality_apply T.hom.val (homOfLE h21).op a

    have h1 : ((Scheme.Modules.restrictFunctor ιW).obj 𝓜).val.map (homOfLE h21).op a =
        𝓜.presheaf.map (ιW.opensFunctor.map (homOfLE h21)).op a := rfl
    rw [h1, ha₂] at hn
    have h0 : (T.hom.val.app (op W₂)) (0 : Γ(𝓜, ιW ''ᵁ W₂)) = 0 := map_zero _
    exact hn.symm.trans h0

  haveI : Nonempty (W₀ : Scheme) := ⟨⟨y, hW y⟩⟩
  have hW₂ : ((W₂ : Set (W₀ : Scheme))).Nonempty := by
    obtain ⟨z, ⟨hzW, hzV⟩, hzU⟩ := nonempty_preirreducible_inter (W₀ ⊓ V).isOpen U.isOpen ⟨y, hW y, hyV⟩ hU
    exact ⟨⟨z, hzW⟩, ⟨hzV, hzU⟩⟩
  have hT : T.hom.app W₁ a = 0 := by
    apply res_injective (homOfLE h21) hW₂
    rw [hb]
    exact (map_zero _).symm
  have : a = T.inv.app W₁ (T.hom.app W₁ a) := by
    rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, T.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
  rw [this, hT, map_zero]
  rfl

end AlphaStub

theorem solution
    {X : Scheme} [IsIntegral X] {𝓛 𝓜 : X.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (φ : 𝓛 ⟶ 𝓜) (U : X.Opens) (hU : (U : Set X).Nonempty)
    (h : (Scheme.Modules.pullback U.ι).map φ = 0) : φ = 0 :=
  AlphaStub.hom_eq_zero_of_pullback_ι_map_eq_zero h𝓛 h𝓜 φ U hU h

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_hom_eq_zero_of_pullback_map_eq_zero_of_isIntegral
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_hom_eq_zero_of_pullback_map_eq_zero_of_isIntegral (solution)
