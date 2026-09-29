-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f1f706b7-588d-57ad-9f5e-440a8e8a2659

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization

namespace P2mWs6E1Aux

theorem map_appTop_π_eq_awayToSection_algebraMap (k : Type u) [CommRing k] (n : ℕ) (i : Fin (n + 1)) (r : k) :
    (Proj (homogeneousSubmodule (Fin (n + 1)) k)).presheaf.map
        (homOfLE (le_top : Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) k) (X i) ≤ ⊤)).op
        ((ProjSpace.π k n).appTop ((Scheme.ΓSpecIso (.of k)).inv r))
      = Proj.awayToSection (homogeneousSubmodule (Fin (n + 1)) k) (X i)
          (algebraMap k (Away (homogeneousSubmodule (Fin (n + 1)) k) (X i)) r) := by

  let 𝒜 := homogeneousSubmodule (Fin (n + 1)) k
  let P := Proj 𝒜
  let D : P.Opens := Proj.basicOpen 𝒜 (X i)
  let e := Proj.basicOpenIsoSpec 𝒜 (X i) (ProjSpace.X_mem_one k n i) one_pos
  let x : Γ(Spec (.of k), ⊤) := (Scheme.ΓSpecIso (.of k)).inv r
  let am := algebraMap k (Away 𝒜 (X i))

  have h1 : (Proj.awayι 𝒜 (X i) (ProjSpace.X_mem_one k n i) one_pos).appTop ((ProjSpace.π k n).appTop x)
      = (Scheme.ΓSpecIso (.of (Away 𝒜 (X i)))).inv (am r) := by
    have h := ProjSpace.awayι_comp_π k n i
    have h' : ((ProjSpace.π k n).appTop ≫ (Proj.awayι 𝒜 (X i) (ProjSpace.X_mem_one k n i) one_pos).appTop) x
        = (Spec.map (CommRingCat.ofHom am)).appTop x := by
      rw [← Scheme.Hom.comp_appTop, h]
    rw [CommRingCat.comp_apply] at h'
    rw [h']
    have nat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom am)
    have nat' : ((CommRingCat.ofHom am) ≫ (Scheme.ΓSpecIso (.of (Away 𝒜 (X i)))).inv) r
        = ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec.map (CommRingCat.ofHom am)).appTop) r := by rw [nat]
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at nat'
    exact nat'.symm

  have h2 : ∀ y : Γ(P, ⊤), (Proj.awayι 𝒜 (X i) (ProjSpace.X_mem_one k n i) one_pos).appTop y
      = e.inv.appTop (D.topIso.inv (P.presheaf.map (homOfLE (le_top : D ≤ ⊤)).op y)) := by
    intro y
    rw [← Proj.basicOpenIsoSpec_inv_ι, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Opens.ι_appTop,
      Scheme.Opens.topIso_inv]
    congr 1

  have h3 : ∀ z : Γ(Spec (.of (Away 𝒜 (X i))), ⊤),
      e.hom.appTop z = D.topIso.inv (Proj.awayToSection 𝒜 (X i) ((Scheme.ΓSpecIso (.of (Away 𝒜 (X i)))).hom z)) := by
    intro z
    have := Proj.basicOpenToSpec_app_top 𝒜 (X i)
    rw [Proj.basicOpenIsoSpec_hom]
    change (Proj.basicOpenToSpec 𝒜 (X i)).app ⊤ z = _
    rw [this]
    rfl

  have h4 : ∀ w : Γ(↑D, ⊤), e.hom.appTop (e.inv.appTop w) = w := by
    intro w
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
    rfl

  have key : D.topIso.inv ((Proj (homogeneousSubmodule (Fin (n + 1)) k)).presheaf.map
        (homOfLE (le_top : Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) k) (X i) ≤ ⊤)).op
        ((ProjSpace.π k n).appTop ((Scheme.ΓSpecIso (.of k)).inv r)))
      = D.topIso.inv (Proj.awayToSection 𝒜 (X i) (am r)) := by
    have hx := h2 ((ProjSpace.π k n).appTop x)
    rw [h1] at hx

    have := congrArg (fun w => e.hom.appTop w) hx
    simp only [h4] at this
    rw [← this, h3]
    congr 2
    exact CategoryTheory.Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of (Away 𝒜 (X i)))) (am r)
  have hinj : Function.Injective (fun w => D.topIso.inv w) := fun a b hab => by
    have := congrArg (fun w => D.topIso.hom w) hab
    simpa only [CategoryTheory.Iso.inv_hom_id_apply] using this
  exact hinj key

section Frac

variable {k : Type u} [CommRing k] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

noncomputable def frac (d : ℕ) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i : Fin (n + 1)) : Away 𝒜 (X i) :=
  HomogeneousLocalization.mk
    { deg := d
      num := ⟨p.1, p.2⟩
      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
      den_mem := ⟨d, rfl⟩ }

theorem val_frac (d : ℕ) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i : Fin (n + 1)) :
    (frac d p i).val = Localization.mk p.1 (⟨MvPolynomial.X i ^ d, ⟨d, rfl⟩⟩ : Submonoid.powers (MvPolynomial.X i)) := rfl

theorem frac_add (d : ℕ) (p q : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i : Fin (n + 1)) :
    frac d (p + q) i = frac d p i + frac d q i := by
  apply HomogeneousLocalization.val_injective
  rw [val_add, val_frac, val_frac, val_frac, Localization.add_mk_self]
  rfl

theorem frac_smul (d : ℕ) (c : k) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i : Fin (n + 1)) :
    frac d (c • p) i = algebraMap k (Away 𝒜 (X i)) c * frac d p i := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, val_frac, val_frac, ProjSpace.val_algebraMap, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, one_mul]
  congr 1
  rw [Submodule.coe_smul, MvPolynomial.smul_eq_C_mul]

theorem awayMap_frac_eq (d : ℕ) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i j : Fin (n + 1)) :
    awayMap 𝒜 (ProjSpace.X_mem_one k n j) rfl (frac d p i)
      = awayMap 𝒜 (ProjSpace.X_mem_one k n j) rfl (ProjSpace.ratio k n i j) ^ d
          * awayMap 𝒜 (ProjSpace.X_mem_one k n i)
              (mul_comm (X i) (X j) : (X i * X j : MvPolynomial (Fin (n + 1)) k) = X j * X i) (frac d p j) := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, val_pow]
  rw [frac, val_awayMap_mk, frac, val_awayMap_mk,
    ProjSpace.val_awayMap_ratio k n i j j (ProjSpace.X_mem_one k n j) rfl _ (X j) (by rw [ProjSpace.ratio, Away.val_mk]),
    Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow]
  ring

end Frac

section Comp

variable {k : Type u} [CommRing k] {n : ℕ} {Z : Scheme.{u}}
  (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

noncomputable def pullAway (i : Fin (n + 1)) (a : Away 𝒜 (X i)) : Γ(Z, ProjSpace.pullbackChart φ i) :=
  (φ.app (Proj.basicOpen 𝒜 (X i))).hom ((Proj.awayToSection 𝒜 (X i)).hom a)

theorem pullAway_eq (i : Fin (n + 1)) (a : Away 𝒜 (X i)) :
    pullAway φ i a = (φ.app (Proj.basicOpen 𝒜 (X i))) (Proj.awayToSection 𝒜 (X i) a) := rfl

theorem pullAway_add (i : Fin (n + 1)) (a b : Away 𝒜 (X i)) :
    pullAway φ i (a + b) = pullAway φ i a + pullAway φ i b :=
  map_add ((φ.app (Proj.basicOpen 𝒜 (X i))).hom.comp (Proj.awayToSection 𝒜 (X i)).hom) a b

theorem pullAway_mul (i : Fin (n + 1)) (a b : Away 𝒜 (X i)) :
    pullAway φ i (a * b) = pullAway φ i a * pullAway φ i b :=
  map_mul ((φ.app (Proj.basicOpen 𝒜 (X i))).hom.comp (Proj.awayToSection 𝒜 (X i)).hom) a b

theorem pullAway_zero (i : Fin (n + 1)) : pullAway φ i 0 = 0 :=
  map_zero ((φ.app (Proj.basicOpen 𝒜 (X i))).hom.comp (Proj.awayToSection 𝒜 (X i)).hom)

theorem restrictFun_pullAway_left (i j : Fin (n + 1)) (a : Away 𝒜 (X i)) :
    ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (pullAway φ i a)
      = (φ.app (Proj.basicOpen 𝒜 (X i * X j))).hom
          ((Proj.awayToSection 𝒜 (X i * X j)).hom (awayMap 𝒜 (ProjSpace.X_mem_one k n j) rfl a)) := by
  have h1 := congrArg (fun (ψ : CommRingCat.of (Away 𝒜 (X i)) ⟶ _) => ψ.hom a)
    (Proj.awayMap_awayToSection 𝒜 (ProjSpace.X_mem_one k n j)
      (rfl : (X i * X j : MvPolynomial (Fin (n + 1)) k) = X i * X j))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
  rw [h1]
  have h2 := congrArg (fun ψ => ψ.hom ((Proj.awayToSection 𝒜 (X i)).hom a))
    (φ.naturality (homOfLE (show Proj.basicOpen 𝒜 (X i * X j) ≤ Proj.basicOpen 𝒜 (X i) from by
      rw [Proj.basicOpen_mul]; exact inf_le_left)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [h2]
  rfl

theorem restrictFun_pullAway_right (i j : Fin (n + 1)) (a : Away 𝒜 (X j)) :
    ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_right φ i j) (pullAway φ j a)
      = (φ.app (Proj.basicOpen 𝒜 (X i * X j))).hom
          ((Proj.awayToSection 𝒜 (X i * X j)).hom (awayMap 𝒜 (ProjSpace.X_mem_one k n i)
            (mul_comm (X i) (X j) : (X i * X j : MvPolynomial (Fin (n + 1)) k) = X j * X i) a)) := by
  have h1 := congrArg (fun (ψ : CommRingCat.of (Away 𝒜 (X j)) ⟶ _) => ψ.hom a)
    (Proj.awayMap_awayToSection 𝒜 (ProjSpace.X_mem_one k n i)
      (mul_comm (X i) (X j) : (X i * X j : MvPolynomial (Fin (n + 1)) k) = X j * X i))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
  rw [h1]
  have h2 := congrArg (fun ψ => ψ.hom ((Proj.awayToSection 𝒜 (X j)).hom a))
    (φ.naturality (homOfLE (show Proj.basicOpen 𝒜 (X i * X j) ≤ Proj.basicOpen 𝒜 (X j) from by
      rw [Proj.basicOpen_mul]; exact inf_le_right)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [h2]
  rfl

theorem restrictFun_pullAway_frac (d : ℕ) (p : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) (i j : Fin (n + 1)) :
    ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (pullAway φ i (frac d p i))
      = ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (ProjSpace.frameUnit φ i j) ^ d
          * ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_right φ i j) (pullAway φ j (frac d p j)) := by
  rw [restrictFun_pullAway_left, restrictFun_pullAway_right, ProjSpace.restrictFun_frameUnit_left]
  let f := (φ.app (Proj.basicOpen 𝒜 (X i * X j))).hom.comp (Proj.awayToSection 𝒜 (X i * X j)).hom
  have hf : ∀ a, f a = (φ.app (Proj.basicOpen 𝒜 (X i * X j))).hom ((Proj.awayToSection 𝒜 (X i * X j)).hom a) :=
    fun _ => rfl
  rw [← hf, ← hf, ← hf, awayMap_frac_eq, map_mul, map_pow]
  rfl

theorem pullAway_algebraMap (i : Fin (n + 1)) (c : k) {W : Z.Opens} (hW : W ≤ ProjSpace.pullbackChart φ i) :
    ProjSpace.restrictFun hW (pullAway φ i (algebraMap k (Away 𝒜 (X i)) c))
      = (Scheme.TwoAffineOpenCover.algebraOfHom (φ ≫ ProjSpace.π k n) W).algebraMap c := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  change _ = (φ.appLE ⊤ W _) ((ProjSpace.π k n).appTop ((Scheme.ΓSpecIso (.of k)).inv c))
  rw [pullAway, ← P2mWs6E1Aux.map_appTop_π_eq_awayToSection_algebraMap k n i c]

  have : φ.appLE ⊤ W (hW.trans (by simp)) =
      (Proj 𝒜).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 (X i) ≤ ⊤)).op ≫
        φ.appLE (Proj.basicOpen 𝒜 (X i)) W hW := by
    rw [Scheme.Hom.map_appLE]
  rw [this, CommRingCat.comp_apply]
  rfl

end Comp

end P2mWs6E1Aux

open P2mWs6E1Aux in
theorem solution
    {k : Type u} [CommRing k] {n : ℕ} {Z : Scheme.{u}}
    (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) (d : ℕ) :
    ∃ θ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k]
        ProjSpace.twistObj (φ ≫ ProjSpace.π k n) φ d ⊤,
      (∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) (i : Fin (n + 1)),
        (θ ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩).val i =
          ProjSpace.restrictFun (inf_le_right : ⊤ ⊓ ProjSpace.pullbackChart φ i ≤ ProjSpace.pullbackChart φ i)
            ((φ.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })))) ∧
      (∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        θ ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ = 0 ↔
          ∀ i : Fin (n + 1),
            (φ.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })) = 0) := by
  classical

  let comp : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) → ∀ i : Fin (n + 1),
      Γ(Z, (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) :=
    fun p i => ProjSpace.restrictFun inf_le_right (pullAway φ i (frac d p i))
  have hcompat : ∀ p, ProjSpace.TwistCompat φ d ⊤ (comp p) := by
    intro p i j
    have hV : ((⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) ⊓ ProjSpace.pullbackChart φ j ≤ ProjSpace.pullbackOverlap φ i j := by
      rw [ProjSpace.pullbackOverlap_eq_inf]; exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    show ProjSpace.restrictFun _ (ProjSpace.restrictFun _ (pullAway φ i (frac d p i)))
      = ProjSpace.restrictFun _ (ProjSpace.frameUnit φ i j) ^ d *
          ProjSpace.restrictFun _ (ProjSpace.restrictFun _ (pullAway φ j (frac d p j)))
    rw [ProjSpace.restrictFun_restrictFun, ProjSpace.restrictFun_restrictFun]
    have e1 : ProjSpace.restrictFun (inf_le_left.trans inf_le_right :
          ((⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) ⊓ ProjSpace.pullbackChart φ j ≤ ProjSpace.pullbackChart φ i)
          (pullAway φ i (frac d p i))
        = ProjSpace.restrictFun hV (ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (pullAway φ i (frac d p i))) := by
      rw [ProjSpace.restrictFun_restrictFun]
    have e2 : ProjSpace.restrictFun (inf_le_right :
          ((⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) ⊓ ProjSpace.pullbackChart φ j ≤ ProjSpace.pullbackChart φ j)
          (pullAway φ j (frac d p j))
        = ProjSpace.restrictFun hV (ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_right φ i j) (pullAway φ j (frac d p j))) := by
      rw [ProjSpace.restrictFun_restrictFun]
    have e3 : ProjSpace.restrictFun (inf_le_left.trans inf_le_right :
          ((⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) ⊓ ProjSpace.pullbackChart φ j ≤ ProjSpace.pullbackChart φ i)
          (ProjSpace.frameUnit φ i j)
        = ProjSpace.restrictFun hV (ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (ProjSpace.frameUnit φ i j)) := by
      rw [ProjSpace.restrictFun_restrictFun]
    rw [e1, e2, e3, restrictFun_pullAway_frac, map_mul, map_pow]
  let θfun : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) → ProjSpace.twistObj (φ ≫ ProjSpace.π k n) φ d ⊤ :=
    fun p => ⟨comp p, hcompat p⟩
  have hval : ∀ p i, (θfun p).val i = ProjSpace.restrictFun inf_le_right (pullAway φ i (frac d p i)) := fun _ _ => rfl
  refine ⟨{ toFun := θfun, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro p q
    refine ProjSpace.twistObj.ext (funext fun i => ?_)
    rw [ProjSpace.twistObj.add_val, Pi.add_apply, hval, hval, hval, frac_add, pullAway_add, map_add]
  · intro c p
    refine ProjSpace.twistObj.ext (funext fun i => ?_)
    rw [hval, RingHom.id_apply, ProjSpace.twistObj.algebraMap_smul, ProjSpace.twistObj.smul_val, hval, frac_smul,
      pullAway_mul, map_mul]
    congr 1
    rw [pullAway_algebraMap φ i c, ProjSpace.restrictFun_algebraMap']
  · intro F hF i
    rfl
  · intro F hF
    constructor
    · intro h i
      have hi := congrArg (fun g => g.val i) h
      simp only [ProjSpace.twistObj.zero_val, Pi.zero_apply] at hi
      change ProjSpace.restrictFun inf_le_right (pullAway φ i (frac d ⟨F, _⟩ i)) = 0 at hi

      have hback : ∀ x : Γ(Z, ProjSpace.pullbackChart φ i),
          ProjSpace.restrictFun (le_inf le_top le_rfl : ProjSpace.pullbackChart φ i ≤ (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i)
            (ProjSpace.restrictFun inf_le_right x) = x := fun x => by
        rw [ProjSpace.restrictFun_restrictFun, ProjSpace.restrictFun_refl]
      have := hback (pullAway φ i (frac d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ i))
      rw [hi, map_zero] at this
      exact this.symm
    · intro h
      refine ProjSpace.twistObj.ext (funext fun i => ?_)
      rw [ProjSpace.twistObj.zero_val, Pi.zero_apply]
      change ProjSpace.restrictFun inf_le_right (pullAway φ i (frac d ⟨F, _⟩ i)) = 0
      rw [pullAway_eq]
      exact (congrArg _ (h i)).trans (map_zero _)

end S_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq (solution)
