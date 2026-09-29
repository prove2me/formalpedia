-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/aec53eb3-fb83-5a3a-9c48-fe697353c376

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_isFinite

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_isFinite.AlgebraicGeometry TopologicalSpace Opposite"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.Modules.presheaf Scheme.Opens.ι_appIso IsFinite Scheme.Hom.image_preimage_eq_opensRange_inf isAffine_of_isAffineHom IsAffine Spec RingedSpace.isUnit_res_basicOpen Scheme Scheme.Hom.appIso Scheme.Hom.preimage_mono IsFinite.of_comp isAffineOpen_top IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.image_mono Scheme.Hom.opensFunctor Scheme.Opens.opensRange_ι RingedSpace Scheme.Modules.IsInvertible Scheme.Modules.FiniteBySections ProjSpace.π"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Hom.id_app Hom Modules.presheaf Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Hom.appIso Hom.preimage_mono Hom.comp_app basicOpen Modules Opens Hom.image_mono Hom.opensFunctor Opens.opensRange_ι restrict Modules.IsInvertible Modules.FiniteBySections"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul presheaf Hom.comp_app Hom mapPresheaf_app Hom.id_app restrictFunctorIsoPullback restrict_map isSheaf restrict map_smul IsInvertible FiniteBySections isLocalization_basicOpen_of_locallyTrivial exists_projPresentation_of_iSup_eq_top"
namespace FBSFinite
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace LocTriv

variable {X : Scheme.{u}} (M : X.Modules)

noncomputable abbrev rM {V W : X.Opens} (h : V ≤ W) : Γ(M, W) → Γ(M, V) := fun y => M.presheaf.map (homOfLE h).op y

noncomputable abbrev rO {V W : X.Opens} (h : V ≤ W) : Γ(X, W) → Γ(X, V) := fun g => X.presheaf.map (homOfLE h).op g

theorem rM_rM {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    rM M h₃₂ (rM M h₂₁ y) = rM M (h₃₂.trans h₂₁) y := by
  show (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

omit M in
theorem rO_rO {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (g : Γ(X, V₁)) :
    rO h₃₂ (rO h₂₁ g) = rO (h₃₂.trans h₂₁) g := by
  show (X.presheaf.map (homOfLE h₂₁).op ≫ X.presheaf.map (homOfLE h₃₂).op).hom g = _
  rw [← Functor.map_comp]; rfl

theorem rM_self {V : X.Opens} (h : V ≤ V) (y : Γ(M, V)) : rM M h y = y := by
  show (M.presheaf.map (homOfLE h).op) y = y
  rw [Subsingleton.elim (homOfLE h) (𝟙 V), op_id, M.presheaf.map_id]; rfl

omit M in
theorem rO_self {V : X.Opens} (h : V ≤ V) (g : Γ(X, V)) : rO h g = g := by
  show (X.presheaf.map (homOfLE h).op).hom g = g
  rw [Subsingleton.elim (homOfLE h) (𝟙 V), op_id, X.presheaf.map_id]; rfl

theorem rM_smul {V W : X.Opens} (h : V ≤ W) (g : Γ(X, W)) (y : Γ(M, W)) :
    rM M h (g • y) = rO h g • rM M h y := M.map_smul _ _ _

section Transport

variable (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)

theorem hat_eq {W : X.Opens} (hWV : W ≤ V) : V.ι ''ᵁ V.ι ⁻¹ᵁ W = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hWV]

theorem le_hat {W : X.Opens} (hWV : W ≤ V) : W ≤ V.ι ''ᵁ V.ι ⁻¹ᵁ W := (hat_eq V hWV).ge
theorem hat_le {W : X.Opens} (hWV : W ≤ V) : V.ι ''ᵁ V.ι ⁻¹ᵁ W ≤ W := (hat_eq V hWV).le

noncomputable def eApp (W : X.Opens) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W) :=
  (e.hom.app (V.ι ⁻¹ᵁ W)).hom m

noncomputable def eInv (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W) :=
  (e.inv.app (V.ι ⁻¹ᵁ W)).hom a

theorem eInv_eApp (W : X.Opens) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : eInv M V e W (eApp M V e W m) = m := by
  show (e.hom.app (V.ι ⁻¹ᵁ W) ≫ e.inv.app (V.ι ⁻¹ᵁ W)).hom m = m
  rw [← Hom.comp_app, e.hom_inv_id, Hom.id_app]; rfl

theorem eApp_eInv (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : eApp M V e W (eInv M V e W a) = a := by
  show (e.inv.app (V.ι ⁻¹ᵁ W) ≫ e.hom.app (V.ι ⁻¹ᵁ W)).hom a = a
  rw [← Hom.comp_app, e.inv_hom_id, Hom.id_app]; rfl

theorem eApp_zero (W : X.Opens) : eApp M V e W 0 = 0 := (e.hom.app (V.ι ⁻¹ᵁ W)).hom.map_zero

theorem eApp_injective (W : X.Opens) : Function.Injective (eApp M V e W) :=
  Function.LeftInverse.injective (eInv_eApp M V e W)

theorem restrict_smul_eq (W' : V.toScheme.Opens) (b : Γ(V.toScheme, W')) (m : Γ(M.restrict V.ι, W')) :
    (HSMul.hSMul (α := Γ(V.toScheme, W')) (β := Γ(M.restrict V.ι, W')) b m : Γ(M, V.ι ''ᵁ W'))
      = HSMul.hSMul (α := Γ(X, V.ι ''ᵁ W')) (β := Γ(M, V.ι ''ᵁ W')) ((Scheme.Hom.appIso V.ι W').inv b) m := rfl

theorem eApp_smul (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    eApp M V e W (a • m) = a * eApp M V e W m := by
  have hinv : (Scheme.Hom.appIso V.ι (V.ι ⁻¹ᵁ W)).inv a = a := by
    rw [Scheme.Opens.ι_appIso]; rfl
  have h := Hom.app_smul e.hom (U := V.ι ⁻¹ᵁ W) a m
  have hl := restrict_smul_eq M V (V.ι ⁻¹ᵁ W) a m
  rw [hinv] at hl
  unfold eApp
  rw [← hl]
  exact h.trans rfl

omit M e in

theorem unit_map_eq {W₁' W₂' : V.toScheme.Opens} (i : W₂' ⟶ W₁') (a : Γ(X, V.ι ''ᵁ W₁')) :
    ((Scheme.Modules.presheaf (SheafOfModules.unit V.toScheme.ringCatSheaf)).map i.op) a
      = (X.presheaf.map ((Scheme.Hom.opensFunctor V.ι).map i).op).hom a := rfl

theorem eApp_res {W₁ W₂ : X.Opens} (h : W₂ ≤ W₁) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W₁)) :
    eApp M V e W₂ (rM M (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) m)
      = rO (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) (eApp M V e W₁ m) := by
  have hnat := e.hom.mapPresheaf.naturality (homOfLE (Scheme.Hom.preimage_mono V.ι h)).op
  have hx := ConcreteCategory.congr_hom hnat m
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hx
  have e1 : (Scheme.Hom.opensFunctor V.ι).map (homOfLE (Scheme.Hom.preimage_mono V.ι h))
      = homOfLE (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) := Subsingleton.elim _ _
  rw [restrict_map, e1] at hx
  exact hx

end Transport

section StepA

variable (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)

noncomputable def ψ {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : Γ(X, W) :=
  rO (le_hat V hWV) (eApp M V e W (rM M (hat_le V hWV) m))

noncomputable def ψinv {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) : Γ(M, W) :=
  rM M (le_hat V hWV) (eInv M V e W (rO (hat_le V hWV) a))

theorem rM_roundtrip {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : rM M (le_hat V hWV) (rM M (hat_le V hWV) m) = m := by
  rw [rM_rM, rM_self]
theorem rM_roundtrip' {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    rM M (hat_le V hWV) (rM M (le_hat V hWV) m) = m := by
  rw [rM_rM, rM_self]
omit M e in
theorem rO_roundtrip {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) : rO (le_hat V hWV) (rO (hat_le V hWV) a) = a := by
  rw [rO_rO, rO_self]
omit M e in
theorem rO_roundtrip' {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    rO (hat_le V hWV) (rO (le_hat V hWV) a) = a := by
  rw [rO_rO, rO_self]

theorem ψ_ψinv {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) : ψ M V e hWV (ψinv M V e hWV a) = a := by
  simp only [ψ, ψinv]
  rw [rM_roundtrip' M V hWV, eApp_eInv, rO_roundtrip V hWV]

theorem ψinv_ψ {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : ψinv M V e hWV (ψ M V e hWV m) = m := by
  simp only [ψ, ψinv]
  rw [rO_roundtrip' V hWV, eInv_eApp, rM_roundtrip M V hWV]

theorem ψ_injective {W : X.Opens} (hWV : W ≤ V) : Function.Injective (ψ M V e hWV) :=
  Function.LeftInverse.injective (ψinv_ψ M V e hWV)

theorem ψ_zero {W : X.Opens} (hWV : W ≤ V) : ψ M V e hWV 0 = 0 := by
  simp only [ψ]
  show rO (le_hat V hWV) (eApp M V e W ((M.presheaf.map _) 0)) = 0
  rw [map_zero, eApp_zero]; exact map_zero _

theorem ψ_smul {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) (m : Γ(M, W)) :
    ψ M V e hWV (a • m) = a * ψ M V e hWV m := by
  simp only [ψ]
  rw [rM_smul, eApp_smul]
  show (X.presheaf.map _).hom (_ * _) = a * _
  rw [map_mul]
  congr 1
  exact rO_roundtrip V hWV a

theorem ψ_res {W₁ W₂ : X.Opens} (h₁ : W₁ ≤ V) (h : W₂ ≤ W₁) (m : Γ(M, W₁)) :
    ψ M V e (h.trans h₁) (rM M h m) = rO h (ψ M V e h₁ m) := by
  simp only [ψ]
  have lhs : rM M (hat_le V (h.trans h₁)) (rM M h m)
      = rM M (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) (rM M (hat_le V h₁) m) := by
    rw [rM_rM, rM_rM]
  rw [lhs, eApp_res M V e h, rO_rO, rO_rO]

end StepA

end LocTriv

section Frames

open LocTriv

variable {X : Scheme.{u}} (M : X.Modules) (V : X.Opens)
  (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)

theorem eq_of_le_bot {W : X.Opens} (hW : W ≤ ⊥) (s t : Γ(M, W)) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X.carrier)
    (fun _ : Empty => (⊥ : X.Opens)) W (fun i => i.elim) (hW.trans bot_le) s t (fun i => i.elim)

theorem frame_of_eq_unit_smul {W : X.Opens} (hWV : W ≤ V) (y : Γ(M, ⊤)) (c : Γ(X, W)) (hc : IsUnit c)
    (hy : rM M (le_top : W ≤ ⊤) y = c • ψinv M V e hWV 1) (V' : X.Opens) (hV' : V' ≤ W) :
    Function.Bijective fun a : Γ(X, V') => a • (M.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op y) := by
  have hcu : IsUnit (rO hV' c) := hc.map _
  have h1 : rM M hV' (ψinv M V e hWV 1) = ψinv M V e (hV'.trans hWV) 1 := by
    apply ψ_injective M V e (hV'.trans hWV)
    rw [ψ_res M V e hWV hV', ψ_ψinv, ψ_ψinv]
    exact map_one _
  have hres : M.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op y = rO hV' c • ψinv M V e (hV'.trans hWV) 1 := by
    show rM M le_top y = _
    rw [← rM_rM M (le_top : W ≤ ⊤) hV', hy, rM_smul, h1]
  have key : (fun a : Γ(X, V') => a • (M.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op y))
      = (ψinv M V e (hV'.trans hWV)) ∘ (fun a => a * rO hV' c) := by
    funext a
    simp only [Function.comp_apply]
    rw [hres, ← mul_smul]
    apply ψ_injective M V e (hV'.trans hWV)
    rw [ψ_smul, ψ_ψinv, ψ_ψinv, mul_one]
  rw [key]
  refine Function.Bijective.comp ?_ ?_
  · exact Function.bijective_iff_has_inverse.mpr ⟨ψ M V e _, ψ_ψinv M V e _, ψinv_ψ M V e _⟩
  · exact (Units.mulRight hcu.unit).bijective

end Frames

open LocTriv in
theorem main {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Scheme.Modules.FiniteBySections M f := by
  classical
  haveI : IsAffine X := isAffine_of_isAffineHom f
  have htop : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X

  have hpt : ∀ x : X, ∃ (g : Γ(X, ⊤)) (y : Γ(M, ⊤)), x ∈ X.basicOpen g ∧
      ∀ V' : X.Opens, V' ≤ X.basicOpen g →
        Function.Bijective fun a : Γ(X, V') => a • (M.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op y) := by
    intro x
    obtain ⟨V, hxV, ⟨e0⟩⟩ := hM.exists_trivialization x
    let e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf := (restrictFunctorIsoPullback V.ι).app M ≪≫ e0
    obtain ⟨g, hgV, hxg⟩ := htop.exists_basicOpen_le ⟨x, hxV⟩ (Set.mem_univ x)
    obtain ⟨n, y, hy⟩ := (isLocalization_basicOpen_of_locallyTrivial M hM.exists_trivialization ⟨⊤, htop⟩ g).1
      (ψinv M V e hgV 1)
    refine ⟨g, y, hxg, frame_of_eq_unit_smul M V e hgV y _ ?_ hy⟩
    rw [map_pow]
    exact (RingedSpace.isUnit_res_basicOpen _ g).pow n
  choose g y hxg hfr using hpt

  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (X.basicOpen (g x) : Set X))
    (fun x => (X.basicOpen (g x)).2) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxg x⟩)
  let l : List X := t.toList
  let N : ℕ := l.length
  let σ : Fin (N + 1) → Γ(M, ⊤) := fun i => Fin.cases (0 : Γ(M, ⊤)) (fun k => y (l.get k)) i
  let U : Fin (N + 1) → X.Opens := fun i => Fin.cases (⊥ : X.Opens) (fun k => X.basicOpen (g (l.get k))) i
  have hU : iSup U = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨x0, hx0t, hx0⟩ := hx
    have hx0l : x0 ∈ l := Finset.mem_toList.mpr hx0t
    obtain ⟨k, hk⟩ := List.get_of_mem hx0l
    refine Opens.mem_iSup.mpr ⟨k.succ, ?_⟩
    show x ∈ (Fin.cases (⊥ : X.Opens) (fun k => X.basicOpen (g (l.get k))) k.succ : X.Opens)
    rw [Fin.cases_succ, hk]
    exact hx0
  have hframe : ∀ (i : Fin (N + 1)) (V' : X.Opens), V' ≤ U i →
      Function.Bijective fun a : Γ(X, V') => a • (M.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op (σ i)) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · intro V' hV'
      have hV'b : V' ≤ ⊥ := hV'
      haveI : Subsingleton Γ(X, V') :=
        CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty (le_bot_iff.mp hV'b))
      exact ⟨fun a b _ => Subsingleton.elim a b, fun m => ⟨0, eq_of_le_bot M hV'b _ _⟩⟩
    · intro V' hV'
      exact hfr (l.get k) V' hV'
  obtain ⟨𝔓, -, -⟩ := exists_projPresentation_of_iSup_eq_top f M N σ U hU hframe
  refine ⟨N, 𝔓, ?_⟩
  haveI : IsFinite (𝔓.toProj ≫ ProjSpace.π R N) := by rw [𝔓.toProj_π]; infer_instance
  exact IsFinite.of_comp 𝔓.toProj (ProjSpace.π R N)

end AlgebraicGeometry.Scheme.Modules.FBSFinite

theorem solution {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Scheme.Modules.FiniteBySections M f :=
  AlgebraicGeometry.Scheme.Modules.FBSFinite.main f M hM

end S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_isFinite
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_isFinite (solution)
