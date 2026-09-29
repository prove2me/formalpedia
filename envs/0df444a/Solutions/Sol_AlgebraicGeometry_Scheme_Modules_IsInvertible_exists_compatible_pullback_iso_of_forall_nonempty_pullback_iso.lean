-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_compatible_pullback_iso_of_forall_nonempty_pullback_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/f1abb975-b05e-5605-9280-c6706879bc66

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_map_app_eq_smul_of_forall_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_one_of_forall_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_compatible_pullback_iso_of_forall_nonempty_pullback_iso
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CIaux

variable {A : Scheme.{u}} (L : A.Modules) (w : Γ(A, ⊤))

noncomputable abbrev res (U : A.Opens) : Γ(A, U) := A.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op w

omit L in
theorem map_res {U V : A.Opens} (i : V ⟶ U) : A.presheaf.map i.op (res w U) = res w V := by
  change (A.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ A.presheaf.map i.op) w = _
  rw [← Functor.map_comp]
  rfl

noncomputable def smulPresheafHom : L.presheaf ⟶ L.presheaf where
  app U := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom Γ(L, U.unop) (res w U.unop))
  naturality {U V} i := by
    obtain ⟨U⟩ := U; obtain ⟨V⟩ := V
    ext x
    change res w V • L.presheaf.map i x = L.presheaf.map i (res w U • x)
    rw [show i = i.unop.op from rfl, Scheme.Modules.map_smul L i.unop (res w U) x, map_res]

noncomputable def smulHom : L ⟶ L :=
  ⟨PresheafOfModules.homMk (smulPresheafHom L w) (fun U r m => by
    obtain ⟨U⟩ := U
    exact @smul_comm Γ(A, U) Γ(A, U) Γ(L, U) _ _ (smulCommClass_self _ _) (res w U) r m)⟩

theorem smulHom_app (U : A.Opens) (x : Γ(L, U)) : (smulHom L w).app U x = res w U • x := rfl

noncomputable def smulIso (w' : Γ(A, ⊤)) (h1 : w' * w = 1) (h2 : w * w' = 1) : L ≅ L where
  hom := smulHom L w
  inv := smulHom L w'
  hom_inv_id := by
    apply Scheme.Modules.hom_ext; intro U; ext x
    change res w' U • (res w U • x) = x
    rw [smul_smul, ← map_mul, h1, map_one, one_smul]
  inv_hom_id := by
    apply Scheme.Modules.hom_ext; intro U; ext x
    change res w U • (res w' U • x) = x
    rw [smul_smul, ← map_mul, h2, map_one, one_smul]

theorem exists_isUnit_mk_eq {R : Type u} [CommRing R] [IsLocalRing R] (n : ℕ)
    (a : R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)) (ha : IsUnit a) :
    ∃ x : R, IsUnit x ∧ Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)) x = a := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨x, ?_, rfl⟩
  by_contra hx
  have hxm : x ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal x).mpr hx
  have h0 : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)) x) ^ (n + 1) = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hxm (n + 1)
  have hu := ha.pow (n + 1)
  rw [h0, isUnit_zero_iff] at hu
  have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R ^ (n + 1) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]
    exact hu.symm
  exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (Ideal.pow_le_self (Nat.succ_ne_zero n) h1)

end CIaux

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (Xk : ℕ → Scheme.{u})
    (q : ∀ k : ℕ, Xk k ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))
    (j : ∀ k : ℕ, Xk k ⟶ X) (t : ∀ k : ℕ, Xk k ⟶ Xk (k + 1))
    (ht : ∀ k, t k ≫ j (k + 1) = j k)
    (htq : ∀ k, t k ≫ q (k + 1) = q k ≫ Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (k + 1)) :
        IsLocalRing.maximalIdeal R ^ (k + 1 + 1) ≤ IsLocalRing.maximalIdeal R ^ (k + 1)))))
    (hH0 : ∀ k : ℕ,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom (q k) ⊤
      Function.Bijective (algebraMap (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) Γ(Xk k, ⊤)))
    (𝓜 𝓜' : X.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (h𝓜' : Scheme.Modules.IsInvertible 𝓜')
    (hk : ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (j k)).obj 𝓜 ≅ (Scheme.Modules.pullback (j k)).obj 𝓜')) :
    ∃ φ : ∀ k : ℕ, (Scheme.Modules.pullback (j k)).obj 𝓜 ≅ (Scheme.Modules.pullback (j k)).obj 𝓜',
      ∀ k, φ k = ((Scheme.Modules.pullbackComp (t k) (j (k + 1))).app 𝓜 ≪≫ (Scheme.Modules.pullbackCongr (ht k)).app 𝓜).symm
          ≪≫ (Scheme.Modules.pullback (t k)).mapIso (φ (k + 1))
          ≪≫ ((Scheme.Modules.pullbackComp (t k) (j (k + 1))).app 𝓜' ≪≫ (Scheme.Modules.pullbackCongr (ht k)).app 𝓜') := by
  classical

  have hN : ∀ k, Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (j k)).obj 𝓜) := fun k => h𝓜.pullback (j k)

  have P4 : ∀ k, (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1 + 1)))).inv ≫
        (q (k + 1)).appLE ⊤ ⊤ le_top ≫ (t k).appTop =
      CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (k + 1)) :
        IsLocalRing.maximalIdeal R ^ (k + 1 + 1) ≤ IsLocalRing.maximalIdeal R ^ (k + 1))) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))).inv ≫ (q k).appLE ⊤ ⊤ le_top := by
    intro k
    rw [show (q (k + 1)).appLE ⊤ ⊤ le_top = (q (k + 1)).appTop from Scheme.Hom.appLE_eq_app _,
      show (q k).appLE ⊤ ⊤ le_top = (q k).appTop from Scheme.Hom.appLE_eq_app _,
      ← Scheme.Hom.comp_appTop, htq k, Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality_assoc]

  have lift : ∀ (k : ℕ) (φk : (Scheme.Modules.pullback (j k)).obj 𝓜 ≅ (Scheme.Modules.pullback (j k)).obj 𝓜'),
      ∃ ψ : (Scheme.Modules.pullback (j (k + 1))).obj 𝓜 ≅ (Scheme.Modules.pullback (j (k + 1))).obj 𝓜',
        ((Scheme.Modules.pullbackComp (t k) (j (k + 1))).app 𝓜 ≪≫ (Scheme.Modules.pullbackCongr (ht k)).app 𝓜).symm
          ≪≫ (Scheme.Modules.pullback (t k)).mapIso ψ
          ≪≫ ((Scheme.Modules.pullbackComp (t k) (j (k + 1))).app 𝓜' ≪≫ (Scheme.Modules.pullbackCongr (ht k)).app 𝓜')
        = φk := by
    intro k φk

    let c : (Scheme.Modules.pullback (t k)).obj ((Scheme.Modules.pullback (j (k + 1))).obj 𝓜) ≅
        (Scheme.Modules.pullback (j k)).obj 𝓜 :=
      (Scheme.Modules.pullbackComp (t k) (j (k + 1))).app 𝓜 ≪≫ (Scheme.Modules.pullbackCongr (ht k)).app 𝓜
    let c' : (Scheme.Modules.pullback (t k)).obj ((Scheme.Modules.pullback (j (k + 1))).obj 𝓜') ≅
        (Scheme.Modules.pullback (j k)).obj 𝓜' :=
      (Scheme.Modules.pullbackComp (t k) (j (k + 1))).app 𝓜' ≪≫ (Scheme.Modules.pullbackCongr (ht k)).app 𝓜'
    obtain ⟨ψ₀⟩ := hk (k + 1)
    let δ : (Scheme.Modules.pullback (j k)).obj 𝓜 ≅ (Scheme.Modules.pullback (j k)).obj 𝓜' :=
      c.symm ≪≫ (Scheme.Modules.pullback (t k)).mapIso ψ₀ ≪≫ c'
    let α : (Scheme.Modules.pullback (j k)).obj 𝓜 ≅ (Scheme.Modules.pullback (j k)).obj 𝓜 := φk ≪≫ δ.symm

    obtain ⟨s, hs⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_app_eq_smul (hN k) α.hom
    obtain ⟨s', hs'⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_app_eq_smul (hN k) α.inv
    have hss : s * s' = 1 := by
      refine AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_one_of_forall_smul_eq (hN k) (s * s') (fun V x => ?_)
      rw [map_mul, mul_smul, ← hs', ← hs]
      change (α.inv ≫ α.hom).app V x = x
      rw [α.inv_hom_id, Scheme.Modules.Hom.id_app]
      rfl

    letI algk := Scheme.TwoAffineOpenCover.algebraOfHom (q k) ⊤
    letI algk1 := Scheme.TwoAffineOpenCover.algebraOfHom (q (k + 1)) ⊤
    obtain ⟨a, ha⟩ := (hH0 k).2 s
    obtain ⟨a', ha'⟩ := (hH0 k).2 s'
    have haa : a * a' = 1 := (hH0 k).1 (by rw [map_mul, ha, ha', hss, map_one])
    obtain ⟨x, hxU, hx⟩ := CIaux.exists_isUnit_mk_eq (R := R) k a ⟨⟨a, a', haa, (mul_comm a' a).trans haa⟩, rfl⟩
    obtain ⟨xu, rfl⟩ := hxU

    let w : Γ(Xk (k + 1), ⊤) :=
      algebraMap (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1 + 1)) Γ(Xk (k + 1), ⊤)
        (Ideal.Quotient.mk _ (↑xu : R))
    let w' : Γ(Xk (k + 1), ⊤) :=
      algebraMap (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1 + 1)) Γ(Xk (k + 1), ⊤)
        (Ideal.Quotient.mk _ (↑xu⁻¹ : R))
    have hww' : w * w' = 1 := by
      change algebraMap _ _ _ * algebraMap _ _ _ = (1 : Γ(Xk (k + 1), ⊤))
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have hw'w : w' * w = 1 := by rw [mul_comm, hww']
    let μ : (Scheme.Modules.pullback (j (k + 1))).obj 𝓜 ≅ (Scheme.Modules.pullback (j (k + 1))).obj 𝓜 :=
      CIaux.smulIso _ w w' hw'w hww'

    have htw : (t k).appTop w = s := by
      have e1 := congrArg (fun φ => φ.hom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1 + 1)) (↑xu : R))) (P4 k)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Ideal.Quotient.factor_mk] at e1
      rw [← ha, ← hx]
      exact e1

    have key : (Scheme.Modules.pullback (t k)).mapIso μ = c ≪≫ α ≪≫ c.symm := by
      apply Iso.ext
      apply Scheme.Modules.hom_ext; intro V; ext y
      rw [Functor.mapIso_hom,
        AlgebraicGeometry.Scheme.Modules.pullback_map_app_eq_smul_of_forall_app_eq_smul (t k) _ w μ.hom
          (fun U z => rfl) V y, htw]
      change _ = (c.inv.app V) ((α.hom.app V) ((c.hom.app V) y))
      rw [hs V ((c.hom.app V) y), Scheme.Modules.Hom.app_smul]
      change _ = _ • ((c.hom ≫ c.inv).app V y)
      rw [c.hom_inv_id, Scheme.Modules.Hom.id_app]
      rfl
    refine ⟨μ ≪≫ ψ₀, ?_⟩
    change c.symm ≪≫ (Scheme.Modules.pullback (t k)).mapIso (μ ≪≫ ψ₀) ≪≫ c' = φk
    rw [Functor.mapIso_trans, key]
    ext : 1
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, α, δ]
    rw [Iso.map_inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

  let φ : ∀ k : ℕ, (Scheme.Modules.pullback (j k)).obj 𝓜 ≅ (Scheme.Modules.pullback (j k)).obj 𝓜' :=
    fun k => Nat.rec (motive := fun k => (Scheme.Modules.pullback (j k)).obj 𝓜 ≅ (Scheme.Modules.pullback (j k)).obj 𝓜')
      (hk 0).some (fun k φk => (lift k φk).choose) k
  refine ⟨φ, fun k => ?_⟩
  exact ((lift k (φ k)).choose_spec).symm

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_compatible_pullback_iso_of_forall_nonempty_pullback_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_compatible_pullback_iso_of_forall_nonempty_pullback_iso (solution)
