-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.rankAtStalk_sections_eq_one_of_locallyTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0ba864ea-91be-58dc-b36f-4766acca16a9

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_rankAtStalk_sections_eq_one_of_locallyTrivial

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_rankAtStalk_sections_eq_one_of_locallyTrivial.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom Scheme.Modules.presheaf Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Hom.appIso Flat Scheme.Hom.preimage_mono Scheme.Modules Scheme.Opens Scheme.Hom.image_mono Scheme.Hom.opensFunctor Scheme.Opens.opensRange_ι"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pullback Hom.id_app Hom Modules.presheaf Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Hom.appIso Hom.preimage_mono affineOpens Hom.comp_app basicOpen Modules Opens Hom.image_mono Hom.opensFunctor Opens.opensRange_ι basicOpen_le restrict"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pullback presheaf Hom.comp_app Hom mapPresheaf_app Hom.id_app restrictFunctorIsoPullback restrict_map restrict map_smul isLocalization_basicOpen_of_locallyTrivial finite_sections_of_locallyTrivial"
namespace SectRank
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

section Loc

open LocTriv

variable {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens) (f : Γ(X, U.1))
  (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
  (hfV : X.basicOpen f ≤ V)

theorem ψ_add {W : X.Opens} (hWV : W ≤ V) (m m' : Γ(M, W)) :
    ψ M V e hWV (m + m') = ψ M V e hWV m + ψ M V e hWV m' := by
  simp only [ψ, rM, rO, eApp, map_add]
  first
    | rfl
    | (erw [AddMonoidHom.map_add, RingHom.map_add])
    | (erw [map_add, map_add])
    | (rw [AddMonoidHom.map_add]; erw [map_add])

noncomputable def gψ : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(X, X.basicOpen f) where
  toFun m := ψ M V e hfV (rM M (X.basicOpen_le f) m)
  map_add' m m' := by
    simp only [rM, map_add]
    exact ψ_add M V e hfV _ _
  map_smul' a m := by
    simp only [RingHom.id_apply]
    rw [rM_smul, ψ_smul, Algebra.smul_def]
    rfl

theorem gψ_apply (m : Γ(M, U.1)) : gψ M U f V e hfV m = ψ M V e hfV (rM M (X.basicOpen_le f) m) := rfl

include hfV in
theorem isLocalizedModule_gψ
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    IsLocalizedModule (Submonoid.powers f) (gψ M U f V e hfV) where
  map_units s := by
    haveI := U.2.isLocalization_basicOpen f
    exact IsLocalizedModule.map_units (Algebra.linearMap Γ(X, U.1) Γ(X, X.basicOpen f)) s
  surj b := by
    obtain ⟨n, y, hy⟩ := (isLocalization_basicOpen_of_locallyTrivial M htriv U f).1 (ψinv M V e hfV b)
    refine ⟨(y, ⟨f ^ n, n, rfl⟩), ?_⟩
    show (f ^ n : Γ(X, U.1)) • b = ψ M V e hfV (rM M (X.basicOpen_le f) y)
    change (f ^ n : Γ(X, U.1)) • b = ψ M V e hfV (M.presheaf.map (homOfLE (X.basicOpen_le f)).op y)
    rw [hy, ψ_smul, ψ_ψinv, Algebra.smul_def]
    rfl
  exists_of_eq {m m'} h := by
    have h' : rM M (X.basicOpen_le f) m = rM M (X.basicOpen_le f) m' := ψ_injective M V e hfV h
    have h0 : M.presheaf.map (homOfLE (X.basicOpen_le f)).op (m - m') = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr h'
    obtain ⟨n, hn⟩ := (isLocalization_basicOpen_of_locallyTrivial M htriv U f).2 _ h0
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    rw [smul_sub, sub_eq_zero] at hn
    exact hn

end Loc

open LocTriv in
theorem rankAtStalk_sections
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) (𝔭 : PrimeSpectrum Γ(X, U.1)) :
    Module.rankAtStalk (R := Γ(X, U.1)) Γ(M, U.1) 𝔭 = 1 := by
  classical
  haveI hfin : Module.Finite Γ(X, U.1) Γ(M, U.1) := finite_sections_of_locallyTrivial M htriv U

  let s : Set Γ(X, U.1) := {f | ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf),
    X.basicOpen f ≤ V}
  have hspan : Ideal.span s = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro p hp
    obtain ⟨V, hxV, ⟨e⟩⟩ := htriv p
    obtain ⟨h, hhV, hph⟩ := U.2.exists_basicOpen_le ⟨p, hxV⟩ hp
    exact Opens.mem_iSup.mpr ⟨⟨h, V, (restrictFunctorIsoPullback V.ι).app M ≪≫ e, hhV⟩, hph⟩
  have hdata : ∀ r : s, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf),
      X.basicOpen r.1 ≤ V := fun r => r.2
  choose V e hle using hdata
  haveI hloc : ∀ r : s, IsLocalizedModule (Submonoid.powers r.1) (gψ M U r.1 (V r) (e r) (hle r)) :=
    fun r => isLocalizedModule_gψ M U r.1 (V r) (e r) (hle r) htriv

  haveI hflat : Module.Flat Γ(X, U.1) Γ(M, U.1) :=
    Module.flat_of_isLocalized_span (R := Γ(X, U.1)) Γ(X, U.1) Γ(M, U.1) s hspan
      (fun r => Γ(X, X.basicOpen r.1)) (fun r => gψ M U r.1 (V r) (e r) (hle r)) fun r => by
        haveI := U.2.isLocalization_basicOpen r.1
        exact IsLocalization.flat Γ(X, X.basicOpen r.1) (Submonoid.powers r.1)

  have hns : ¬ (s ⊆ 𝔭.asIdeal) := fun hsub =>
    𝔭.isPrime.ne_top (top_le_iff.mp (hspan ▸ Ideal.span_le.mpr hsub))
  obtain ⟨f, hfs, hfp⟩ := Set.not_subset.mp hns
  haveI := U.2.isLocalization_basicOpen f
  haveI := hloc ⟨f, hfs⟩
  have hmem : 𝔭 ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f))) := by
    rw [PrimeSpectrum.localization_away_comap_range Γ(X, X.basicOpen f) f]
    exact hfp
  obtain ⟨q, rfl⟩ := hmem
  haveI : Nontrivial Γ(X, X.basicOpen f) := PrimeSpectrum.nontrivial q
  rw [← Module.rankAtStalk_baseChange,
    Module.rankAtStalk_eq_of_equiv
      (IsLocalizedModule.isBaseChange (Submonoid.powers f) Γ(X, X.basicOpen f)
        (gψ M U f (V ⟨f, hfs⟩) (e ⟨f, hfs⟩) (hle ⟨f, hfs⟩))).equiv,
    Module.rankAtStalk_self]
  rfl

end AlgebraicGeometry.Scheme.Modules.SectRank

theorem solution
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) (𝔭 : PrimeSpectrum Γ(X, U.1)) :
    Module.rankAtStalk (R := Γ(X, U.1)) Γ(M, U.1) 𝔭 = 1 :=
  AlgebraicGeometry.Scheme.Modules.SectRank.rankAtStalk_sections M htriv U 𝔭

end S_AlgebraicGeometry_Scheme_Modules_rankAtStalk_sections_eq_one_of_locallyTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_rankAtStalk_sections_eq_one_of_locallyTrivial (solution)
