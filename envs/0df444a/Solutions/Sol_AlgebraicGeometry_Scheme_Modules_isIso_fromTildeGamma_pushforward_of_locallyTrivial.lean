-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_pushforward_of_locallyTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/211acec0-62b7-510e-a92b-e22aa1c3286f

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_pushforward_of_locallyTrivial

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_pushforward_of_locallyTrivial.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.basicOpen_res Scheme.Modules.pushforward Scheme.Modules.pullback Spec RingedSpace.isUnit_res_basicOpen Scheme Scheme.Modules.fromTildeΓ modulesSpecToSheaf Scheme.preimage_basicOpen_top IsAffineOpen Scheme.Modules tilde Scheme.Modules.map_smul RingedSpace basicOpen_eq_of_affine Scheme.ΓSpecIso"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "basicOpen_res ringCatSheaf Modules.pushforward Modules.pullback Hom Γ toLocallyRingedSpace Modules.fromTildeΓ basicOpen preimage_basicOpen_top Modules Opens rec Modules.map_smul basicOpen_le ΓSpecIso TwoAffineOpenCover"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforward pullback presheaf Hom fromTildeΓ isSheaf map_smul isIso_fromTildeGamma_iff_isLocalizedModule isLocalization_basicOpen_of_locallyTrivial"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}} (M : X.Modules)

noncomputable abbrev res {W W' : X.Opens} (h : W' ≤ W) : Γ(M, W) → Γ(M, W') :=
  fun s => M.presheaf.map (homOfLE h).op s

noncomputable abbrev rres (X : Scheme.{u}) {W W' : X.Opens} (h : W' ≤ W) : Γ(X, W) → Γ(X, W') :=
  fun t => X.presheaf.map (homOfLE h).op t

variable {M}

lemma map_eq_res {W W' : X.Opens} (i : W' ⟶ W) (s : Γ(M, W)) : M.presheaf.map i.op s = res M i.le s := by
  rw [Subsingleton.elim i (homOfLE i.le)]

lemma res_res {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W') (s : Γ(M, W)) :
    res M h' (res M h s) = res M (h'.trans h) s := by
  change (M.presheaf.map (homOfLE h).op ≫ M.presheaf.map (homOfLE h').op) s = _
  rw [← Functor.map_comp, ← op_comp]
  rfl

lemma rres_rres {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W') (t : Γ(X, W)) :
    rres X h' (rres X h t) = rres X (h'.trans h) t := by
  change (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op) t = _
  rw [← Functor.map_comp, ← op_comp]
  rfl

lemma res_smul {W W' : X.Opens} (h : W' ≤ W) (t : Γ(X, W)) (s : Γ(M, W)) :
    res M h (t • s) = rres X h t • res M h s :=
  Scheme.Modules.map_smul M (homOfLE h) t s

lemma res_add {W W' : X.Opens} (h : W' ≤ W) (s s' : Γ(M, W)) : res M h (s + s') = res M h s + res M h s' :=
  map_add _ _ _

lemma res_sub {W W' : X.Opens} (h : W' ≤ W) (s s' : Γ(M, W)) : res M h (s - s') = res M h s - res M h s' :=
  map_sub _ _ _

lemma res_zero {W W' : X.Opens} (h : W' ≤ W) : res M h (0 : Γ(M, W)) = 0 := map_zero _

lemma rres_pow {W W' : X.Opens} (h : W' ≤ W) (t : Γ(X, W)) (n : ℕ) : rres X h (t ^ n) = rres X h t ^ n :=
  map_pow _ _ _

lemma rres_refl {W : X.Opens} (h : W ≤ W) (t : Γ(X, W)) : rres X h t = t := by
  change X.presheaf.map (homOfLE h).op t = t
  rw [Subsingleton.elim (homOfLE h) (𝟙 W), op_id, CategoryTheory.Functor.map_id]
  rfl

theorem exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero
    (U0 U1 : X.Opens) (hU0 : IsAffineOpen U0) (hU1 : IsAffineOpen U1) (hsup : U0 ⊔ U1 = ⊤)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (t : Γ(X, ⊤)) (V : X.Opens) (hV : V = X.basicOpen t) (s : Γ(M, ⊤))
    (hs : res M (le_top (a := V)) s = 0) :
    ∃ n : ℕ, t ^ n • s = 0 := by
  subst hV

  have key : ∀ (U : X.Opens), IsAffineOpen U → ∃ n : ℕ, res M (le_top (a := U)) (t ^ n • s) = 0 := by
    intro U hU
    have hle : X.basicOpen (rres X (le_top (a := U)) t) ≤ X.basicOpen t := by
      rw [Scheme.basicOpen_res]; exact inf_le_right
    obtain ⟨n, hn⟩ := (isLocalization_basicOpen_of_locallyTrivial M htriv ⟨U, hU⟩ (rres X le_top t)).2
      (res M le_top s) (by
        rw [map_eq_res, res_res]
        have : res M (hle.trans (X.basicOpen_le t)) s =
            res M hle (res M (X.basicOpen_le t) s) := (res_res _ _ _).symm
        rw [show res M ((X.basicOpen_le (rres X (le_top (a := U)) t)).trans le_top) s =
            res M (hle.trans (X.basicOpen_le t)) s from rfl, this, hs, res_zero])
    exact ⟨n, by rw [res_smul, rres_pow]; exact hn⟩
  obtain ⟨n0, h0⟩ := key U0 hU0
  obtain ⟨n1, h1⟩ := key U1 hU1
  refine ⟨n0 + n1, ?_⟩

  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  apply F.eq_of_locally_eq₂ (homOfLE (le_top (a := U0))) (homOfLE (le_top (a := U1))) (hsup.symm.le)
  · rw [map_zero]
    change res M le_top (t ^ (n0 + n1) • s) = 0
    rw [pow_add, mul_comm, mul_smul, res_smul, h0, smul_zero]
  · rw [map_zero]
    change res M le_top (t ^ (n0 + n1) • s) = 0
    rw [pow_add, mul_smul, res_smul, h1, smul_zero]

theorem exists_glue₂ (U0 U1 : X.Opens) (hsup : U0 ⊔ U1 = ⊤) (z0 : Γ(M, U0)) (z1 : Γ(M, U1))
    (h : res M (inf_le_left : U0 ⊓ U1 ≤ U0) z0 = res M (inf_le_right : U0 ⊓ U1 ≤ U1) z1) :
    ∃ s : Γ(M, ⊤), res M le_top s = z0 ∧ res M le_top s = z1 := by

  have hagree : ∀ (W : X.Opens) (h0 : W ≤ U0) (h1 : W ≤ U1), res M h0 z0 = res M h1 z1 := by
    intro W h0 h1
    rw [← res_res inf_le_left (le_inf h0 h1), ← res_res inf_le_right (le_inf h0 h1), h]
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  let U : Bool → X.Opens := fun b => Bool.rec U0 U1 b
  let sf : ∀ b : Bool, Γ(M, U b) := fun b => Bool.rec z0 z1 b
  have hcov : (⊤ : X.Opens) ≤ iSup U := by
    rw [← hsup]
    exact sup_le (le_iSup U false) (le_iSup U true)
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' U ⊤ (fun b => homOfLE le_top) hcov sf (by
    intro i j
    cases i <;> cases j
    · exact congrArg (fun φ => M.presheaf.map (Quiver.Hom.op φ) z0) (Subsingleton.elim _ _)
    · exact (map_eq_res _ _).trans (((hagree _ inf_le_left inf_le_right)).trans (map_eq_res _ _).symm)
    · exact (map_eq_res _ _).trans (((hagree _ inf_le_right inf_le_left)).symm.trans (map_eq_res _ _).symm)
    · exact congrArg (fun φ => M.presheaf.map (Quiver.Hom.op φ) z1) (Subsingleton.elim _ _))
  exact ⟨s, hs false, hs true⟩

theorem exists_res_eq_pow_smul
    (U0 U1 : X.Opens) (hU0 : IsAffineOpen U0) (hU1 : IsAffineOpen U1) (hsup : U0 ⊔ U1 = ⊤)
    (hinf : IsAffineOpen (U0 ⊓ U1))
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (t : Γ(X, ⊤)) (V : X.Opens) (hV : V = X.basicOpen t) (y : Γ(M, V)) :
    ∃ (n : ℕ) (s : Γ(M, ⊤)), res M (le_top (a := V)) s = rres X (le_top (a := V)) t ^ n • y := by
  subst hV

  have hD : ∀ U : X.Opens, X.basicOpen (rres X (le_top (a := U)) t) = U ⊓ X.basicOpen t :=
    fun U => X.basicOpen_res t (homOfLE le_top).op
  have hDV : ∀ U : X.Opens, X.basicOpen (rres X (le_top (a := U)) t) ≤ X.basicOpen t :=
    fun U => (hD U).le.trans inf_le_right
  have hDU : ∀ U : X.Opens, X.basicOpen (rres X (le_top (a := U)) t) ≤ U :=
    fun U => X.basicOpen_le _
  have hDmono : ∀ {U U' : X.Opens}, U' ≤ U →
      X.basicOpen (rres X (le_top (a := U')) t) ≤ X.basicOpen (rres X (le_top (a := U)) t) :=
    fun {U U'} hle => by rw [hD, hD]; exact inf_le_inf_right _ hle

  have ht : ∀ U : X.Opens, rres X (hDU U) (rres X (le_top (a := U)) t) = rres X (hDV U) (rres X (X.basicOpen_le t) t) :=
    fun U => by rw [rres_rres, rres_rres]

  have chart : ∀ (U : X.Opens), IsAffineOpen U → ∃ (n : ℕ) (x : Γ(M, U)),
      res M (hDU U) x = rres X (hDV U) (rres X (X.basicOpen_le t) t) ^ n • res M (hDV U) y := by
    intro U hU
    obtain ⟨n, x, hx⟩ := (isLocalization_basicOpen_of_locallyTrivial M htriv ⟨U, hU⟩
      (rres X le_top t)).1 (res M (hDV U) y)
    refine ⟨n, x, ?_⟩
    rw [map_eq_res] at hx
    rw [hx, map_pow, ← ht U]
  obtain ⟨n0, x0, hx0⟩ := chart U0 hU0
  obtain ⟨n1, x1, hx1⟩ := chart U1 hU1

  set N := n0 + n1 with hN
  set x0' : Γ(M, U0) := rres X (le_top (a := U0)) t ^ n1 • x0 with hx0'
  set x1' : Γ(M, U1) := rres X (le_top (a := U1)) t ^ n0 • x1 with hx1'
  have key : ∀ (U : X.Opens) (n m : ℕ) (x : Γ(M, U)),
      res M (hDU U) x = rres X (hDV U) (rres X (X.basicOpen_le t) t) ^ n • res M (hDV U) y →
      res M (hDU U) (rres X (le_top (a := U)) t ^ m • x) =
        rres X (hDV U) (rres X (X.basicOpen_le t) t) ^ (n + m) • res M (hDV U) y := by
    intro U n m x hx
    rw [res_smul, rres_pow, hx, ht U, smul_smul, ← pow_add, add_comm]
  have h0 : res M (hDU U0) x0' = rres X (hDV U0) (rres X (X.basicOpen_le t) t) ^ N • res M (hDV U0) y :=
    key U0 n0 n1 x0 hx0
  have h1 : res M (hDU U1) x1' = rres X (hDV U1) (rres X (X.basicOpen_le t) t) ^ N • res M (hDV U1) y := by
    rw [hN, add_comm]; exact key U1 n1 n0 x1 hx1
  clear_value x0' x1'

  have hdiff : res M (hDU (U0 ⊓ U1)) (res M inf_le_left x0' - res M inf_le_right x1') = 0 := by
    rw [res_sub, res_res, res_res,
      ← res_res (hDU U0) (hDmono inf_le_left), ← res_res (hDU U1) (hDmono inf_le_right), h0, h1,
      res_smul, res_smul, rres_pow, rres_pow]
    simp only [rres_rres, res_res, sub_self]
  obtain ⟨k, hk⟩ := (isLocalization_basicOpen_of_locallyTrivial M htriv ⟨U0 ⊓ U1, hinf⟩
    (rres X le_top t)).2 _ (by rw [map_eq_res]; exact hdiff)

  obtain ⟨s, hs0, hs1⟩ := exists_glue₂ (M := M) U0 U1 hsup (rres X (le_top (a := U0)) t ^ k • x0')
    (rres X (le_top (a := U1)) t ^ k • x1') (by
    rw [res_smul, res_smul, rres_pow, rres_pow, rres_rres, rres_rres, ← sub_eq_zero, ← smul_sub]
    exact hk)
  refine ⟨N + k, s, ?_⟩

  have hcov : X.basicOpen t ≤ X.basicOpen (rres X (le_top (a := U0)) t) ⊔ X.basicOpen (rres X (le_top (a := U1)) t) := by
    rw [hD, hD, ← inf_sup_right, hsup, top_inf_eq]
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  apply F.eq_of_locally_eq₂ (homOfLE (hDV U0)) (homOfLE (hDV U1)) hcov
  · change res M (hDV U0) (res M _ s) = res M (hDV U0) _
    rw [res_res, ← res_res (le_top (a := U0)) (hDU U0), hs0, key U0 N k x0' h0, res_smul, rres_pow]
  · change res M (hDV U1) (res M _ s) = res M (hDV U1) _
    rw [res_res, ← res_res (le_top (a := U1)) (hDU U1), hs1, key U1 N k x1' h1, res_smul, rres_pow]

section pushforward

variable {A : Type u} [CommRing A] (π : X ⟶ Spec (.of A))

noncomputable def toSecRingHom (U : (Spec (CommRingCat.of A)).Opens) : A →+* Γ(X, π ⁻¹ᵁ U) :=
  (π.app U).hom.comp ((((Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top (a := U))).op).hom).comp
    (Scheme.ΓSpecIso (.of A)).inv.hom)

lemma smul_pushforward_eq (U : (Spec (CommRingCat.of A)).Opens) (a : A)
    (s : ((modulesSpecToSheaf (R := .of A)).obj ((Scheme.Modules.pushforward π).obj M)).1.obj (op U)) :
    a • s = (toSecRingHom π U a) • (show Γ(M, π ⁻¹ᵁ U) from s) := rfl

noncomputable def secTop (a : A) : Γ(X, ⊤) := π.appTop ((Scheme.ΓSpecIso (.of A)).inv a)

lemma toSecRingHom_eq (U : (Spec (CommRingCat.of A)).Opens) (a : A) :
    toSecRingHom π U a = rres X (le_top (a := π ⁻¹ᵁ U)) (secTop π a) := by
  have h := π.naturality (homOfLE (le_top (a := U))).op
  have h' := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of A)).inv a)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h'
  exact h'.trans (map_eq_res' _ _)
where

  map_eq_res' {W W' : X.Opens} (i : W' ⟶ W) (t : Γ(X, W)) : X.presheaf.map i.op t = rres X i.le t := by
    rw [Subsingleton.elim i (homOfLE i.le)]

lemma preimage_basicOpen_eq (f : A) : π ⁻¹ᵁ PrimeSpectrum.basicOpen f = X.basicOpen (secTop π f) := by
  rw [show PrimeSpectrum.basicOpen f =
      (Spec (CommRingCat.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv f) from (basicOpen_eq_of_affine (R := CommRingCat.of A) f).symm]
  exact Scheme.preimage_basicOpen_top π _

theorem isIso_fromTildeGamma_pushforward
    (U0 U1 : X.Opens) (hU0 : IsAffineOpen U0) (hU1 : IsAffineOpen U1) (hsup : U0 ⊔ U1 = ⊤)
    (hinf : IsAffineOpen (U0 ⊓ U1))
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    IsIso (Scheme.Modules.fromTildeΓ (R := .of A) ((Scheme.Modules.pushforward π).obj M)) := by
  refine (isIso_fromTildeGamma_iff_isLocalizedModule (R := CommRingCat.of A)
    ((Scheme.Modules.pushforward π).obj M)).mpr fun f => ?_
  have hVt := preimage_basicOpen_eq π f

  have hact : ∀ (U : (Spec (CommRingCat.of A)).Opens) (n : ℕ)
      (s : ((modulesSpecToSheaf (R := .of A)).obj ((Scheme.Modules.pushforward π).obj M)).1.obj (op U)),
      (⟨f ^ n, n, rfl⟩ : Submonoid.powers f) • s =
        rres X (le_top (a := π ⁻¹ᵁ U)) (secTop π f) ^ n • (show Γ(M, π ⁻¹ᵁ U) from s) := by
    intro U n s
    rw [Submonoid.smul_def, smul_pushforward_eq, map_pow, toSecRingHom_eq]

  let N' := ((modulesSpecToSheaf (R := .of A)).obj ((Scheme.Modules.pushforward π).obj M)).1.obj
    (op (PrimeSpectrum.basicOpen f))
  refine ⟨?_, ?_, ?_⟩
  ·
    rintro ⟨_, n, rfl⟩
    dsimp only
    have hu : IsUnit (rres X (le_top (a := π ⁻¹ᵁ PrimeSpectrum.basicOpen f)) (secTop π f) ^ n) := by
      refine IsUnit.pow n ?_
      rw [← rres_rres (X.basicOpen_le (secTop π f)) hVt.le]
      exact (RingedSpace.isUnit_res_basicOpen X.toLocallyRingedSpace.toRingedSpace (secTop π f)).map _
    rw [Module.End.isUnit_iff]
    show @Function.Bijective Γ(M, π ⁻¹ᵁ PrimeSpectrum.basicOpen f) Γ(M, π ⁻¹ᵁ PrimeSpectrum.basicOpen f)
      (fun s => (algebraMap (CommRingCat.of A) (Module.End (CommRingCat.of A) N')
        ((⟨f ^ n, n, rfl⟩ : Submonoid.powers f) : (CommRingCat.of A))) s)
    convert hu.smul_bijective (β := Γ(M, π ⁻¹ᵁ PrimeSpectrum.basicOpen f)) using 1
    funext s
    exact (Module.algebraMap_end_apply _ _ _ _ _).trans (hact _ n s)
  ·
    intro y
    obtain ⟨n, s, hs⟩ := exists_res_eq_pow_smul (M := M) U0 U1 hU0 hU1 hsup hinf htriv (secTop π f)
      (π ⁻¹ᵁ PrimeSpectrum.basicOpen f) hVt y
    exact ⟨⟨s, ⟨f ^ n, n, rfl⟩⟩, (hact _ n y).trans hs.symm⟩
  ·
    intro x₁ x₂ h
    have h' : res M (le_top (a := π ⁻¹ᵁ PrimeSpectrum.basicOpen f)) (show Γ(M, ⊤) from x₁) =
        res M (le_top (a := π ⁻¹ᵁ PrimeSpectrum.basicOpen f)) (show Γ(M, ⊤) from x₂) := h
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero (M := M) U0 U1 hU0 hU1 hsup htriv
      (secTop π f) (π ⁻¹ᵁ PrimeSpectrum.basicOpen f) hVt
      ((show Γ(M, ⊤) from x₁) - (show Γ(M, ⊤) from x₂))
      ((res_sub _ _ _).trans (sub_eq_zero.mpr h'))
    refine ⟨⟨f ^ n, n, rfl⟩, (hact _ n x₁).trans (Eq.trans ?_ (hact _ n x₂).symm)⟩
    have hrefl : rres X (le_top (a := π ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens))) (secTop π f) =
        secTop π f := rres_refl _ _
    rw [smul_sub, sub_eq_zero] at hn
    have hpow : rres X (le_top (a := π ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens))) (secTop π f) ^ n =
        secTop π f ^ n := congrArg (· ^ n) hrefl
    exact (congrArg (fun r : Γ(X, ⊤) => r • (show Γ(M, ⊤) from x₁)) hpow).trans
      (hn.trans (congrArg (fun r : Γ(X, ⊤) => r • (show Γ(M, ⊤) from x₂)) hpow).symm)

end pushforward

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_pushforward_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {A : Type u} [CommRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A)) (𝒱 : X.TwoAffineOpenCover)
    (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    IsIso (Scheme.Modules.fromTildeΓ (R := .of A) ((Scheme.Modules.pushforward π).obj M)) :=
  isIso_fromTildeGamma_pushforward π 𝒱.U0 𝒱.U1 𝒱.isAffineOpen_U0 𝒱.isAffineOpen_U1 𝒱.sup_eq_top
    𝒱.isAffineOpen_inf htriv

#print axioms solution

end S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_pushforward_of_locallyTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_pushforward_of_locallyTrivial (solution)
