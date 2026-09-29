-- Prove2me | solution 1 for AlgebraicGeometry.maximalIdeal_stalk_pullback_le_of_sections_of_isAffine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ad92c395-f59a-5014-b4ca-f2f69dbb178b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_maximalIdeal_stalk_pullback_le_of_sections_of_isAffine

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped TensorProduct

universe u

namespace ProdStalkAffb6

lemma ker_eq_maximalIdeal {R K : Type*} [CommRing R] [IsLocalRing R] [Field K] (φ : R →+* K)
    [IsLocalHom φ] : RingHom.ker φ = maximalIdeal R := by
  ext x
  rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h hu
    exact (hu.map φ).ne_zero h
  · intro h
    by_contra h0
    exact h (IsLocalHom.map_nonunit x (isUnit_iff_ne_zero.mpr h0))

noncomputable def ev {k : Type u} [Field k] {X : Scheme.{u}} (s : Spec (.of k) ⟶ X) :
    Γ(X, ⊤) →+* k :=
  (X.presheaf.germ ⊤ (s (closedPoint k)) trivial ≫ Scheme.stalkClosedPointTo s).hom

lemma ev_apply {k : Type u} [Field k] {X : Scheme.{u}} (s : Spec (.of k) ⟶ X) (a : Γ(X, ⊤)) :
    ev s a = (Scheme.stalkClosedPointTo s).hom ((X.presheaf.germ ⊤ (s (closedPoint k)) trivial).hom a) :=
  rfl

lemma germ_stalkClosedPointTo_of_eq_id {k : Type u} [Field k] (g : Spec (.of k) ⟶ Spec (.of k))
    (hg : g = 𝟙 _) :
    (Spec (CommRingCat.of k)).presheaf.germ ⊤ (g (closedPoint k)) trivial ≫ Scheme.stalkClosedPointTo g =
      (Scheme.ΓSpecIso (.of k)).hom := by
  subst hg
  rw [show (𝟙 (Spec (CommRingCat.of k))) = Spec.map (𝟙 _) from (Spec.map_id _).symm,
    Scheme.germ_stalkClosedPointTo_Spec, Category.comp_id]

lemma ev_comp_appTop {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (s : Spec (.of k) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    (ev s).comp ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom = RingHom.id k := by
  have h1 : p.appTop ≫ X.presheaf.germ ⊤ (s (closedPoint k)) trivial ≫ Scheme.stalkClosedPointTo s =
      ((Spec (CommRingCat.of k)).presheaf.germ ⊤ (p (s (closedPoint k))) trivial ≫
        p.stalkMap (s (closedPoint k))) ≫ Scheme.stalkClosedPointTo s := by
    rw [Scheme.Hom.germ_stalkMap]; rfl
  have h2 : ((Spec (CommRingCat.of k)).presheaf.germ ⊤ (p (s (closedPoint k))) trivial ≫
        p.stalkMap (s (closedPoint k))) ≫ Scheme.stalkClosedPointTo s = (Scheme.ΓSpecIso (.of k)).hom := by
    rw [Category.assoc, ← Scheme.stalkClosedPointTo_comp]
    exact germ_stalkClosedPointTo_of_eq_id (s ≫ p) hs
  apply RingHom.ext
  intro r
  change (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop) ≫ X.presheaf.germ ⊤ (s (closedPoint k)) trivial ≫
    Scheme.stalkClosedPointTo s).hom r = r
  rw [Category.assoc, h1, h2, Iso.inv_hom_id]
  rfl

lemma ev_comp {k : Type u} [Field k] {X Y : Scheme.{u}} (s : Spec (.of k) ⟶ X) (g : X ⟶ Y) :
    (ev s).comp g.appTop.hom = ev (s ≫ g) := by
  have h1 : g.appTop ≫ X.presheaf.germ ⊤ (s (closedPoint k)) trivial ≫ Scheme.stalkClosedPointTo s =
      (Y.presheaf.germ ⊤ (g (s (closedPoint k))) trivial ≫ g.stalkMap (s (closedPoint k))) ≫
        Scheme.stalkClosedPointTo s := by
    rw [Scheme.Hom.germ_stalkMap]; rfl
  apply RingHom.ext
  intro b
  change (g.appTop ≫ X.presheaf.germ ⊤ (s (closedPoint k)) trivial ≫ Scheme.stalkClosedPointTo s).hom b = _
  rw [h1, Category.assoc, ← Scheme.stalkClosedPointTo_comp]
  rfl

lemma mem_ker_ev_iff {k : Type u} [Field k] {X : Scheme.{u}} (s : Spec (.of k) ⟶ X) (a : Γ(X, ⊤)) :
    a ∈ RingHom.ker (ev s) ↔
      (X.presheaf.germ ⊤ (s (closedPoint k)) trivial).hom a ∈ maximalIdeal _ := by
  rw [← ker_eq_maximalIdeal (Scheme.stalkClosedPointTo s).hom, RingHom.mem_ker, RingHom.mem_ker, ev_apply]

end ProdStalkAffb6

open ProdStalkAffb6 in
theorem solution
    {k : Type u} [Field k] {Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z]
    (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ pY = 𝟙 _) (z : Spec (.of k) ⟶ Z) (hz : z ≫ pZ = 𝟙 _)
    (w : ↑(pullback pY pZ)) (hw : w = (pullback.lift y z (hy.trans hz.symm)) (closedPoint k)) :
    maximalIdeal ((pullback pY pZ).presheaf.stalk w) ≤
      (maximalIdeal _).map ((pullback.fst pY pZ).stalkMap w).hom ⊔
        (maximalIdeal _).map ((pullback.snd pY pZ).stalkMap w).hom := by
  classical
  subst hw
  have hs1 : (pullback.lift y z (hy.trans hz.symm) ≫ pullback.fst pY pZ) ≫ pY = 𝟙 _ := by
    rw [pullback.lift_fst, hy]
  have hs2 : (pullback.lift y z (hy.trans hz.symm) ≫ pullback.snd pY pZ) ≫ pZ = 𝟙 _ := by
    rw [pullback.lift_snd, hz]
  generalize pullback.lift y z (hy.trans hz.symm) = s at *
  clear y z hy hz
  have hX : IsAffineOpen (⊤ : (pullback pY pZ).Opens) := isAffineOpen_top _

  letI algB : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop).hom.toAlgebra
  letI algC : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ pZ.appTop).hom.toAlgebra

  let εB : Γ(Y, ⊤) →ₐ[k] k := ⟨ev (s ≫ pullback.fst pY pZ), fun r =>
    congrArg (fun φ : k →+* k => φ r) (ev_comp_appTop pY _ hs1)⟩
  let εC : Γ(Z, ⊤) →ₐ[k] k := ⟨ev (s ≫ pullback.snd pY pZ), fun r =>
    congrArg (fun φ : k →+* k => φ r) (ev_comp_appTop pZ _ hs2)⟩
  have hεB : Function.Surjective εB := fun r => ⟨algebraMap k _ r, εB.commutes r⟩
  have hεC : Function.Surjective εC := fun r => ⟨algebraMap k _ r, εC.commutes r⟩

  have sq : IsPullback (pullback.fst pY pZ ≫ Y.isoSpec.hom) (pullback.snd pY pZ ≫ Z.isoSpec.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap k Γ(Y, ⊤))))
      (Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, ⊤)))) := by
    refine (IsPullback.of_hasPullback pY pZ).of_iso (Iso.refl _) Y.isoSpec Z.isoSpec (Iso.refl _)
      (by simp) (by simp) ?_ ?_
    · change pY ≫ 𝟙 _ = Y.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop)
      rw [Category.comp_id, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
        Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
        Category.comp_id]
    · change pZ ≫ 𝟙 _ = Z.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ pZ.appTop)
      rw [Category.comp_id, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
        Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
        Category.comp_id]
  let e : pullback pY pZ ≅ Spec (.of (Γ(Y, ⊤) ⊗[k] Γ(Z, ⊤))) :=
    sq.isoPullback ≪≫ pullbackSpecIso k Γ(Y, ⊤) Γ(Z, ⊤)
  have he1 := pullbackSpecIso_inv_fst k Γ(Y, ⊤) Γ(Z, ⊤)
  have he2 := pullbackSpecIso_inv_snd k Γ(Y, ⊤) Γ(Z, ⊤)
  rw [Iso.inv_comp_eq] at he1 he2

  have he1' : e.hom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
      pullback.fst pY pZ ≫ Y.isoSpec.hom := by
    rw [← sq.isoPullback_hom_fst, he1]; rfl

  let Φ : Γ(Y, ⊤) ⊗[k] Γ(Z, ⊤) →+* Γ(pullback pY pZ, ⊤) :=
    ((Scheme.ΓSpecIso (.of (Γ(Y, ⊤) ⊗[k] Γ(Z, ⊤)))).inv ≫ e.hom.appTop).hom
  have hΦsurj : Function.Surjective Φ :=
    (ConcreteCategory.bijective_of_isIso
      ((Scheme.ΓSpecIso (.of (Γ(Y, ⊤) ⊗[k] Γ(Z, ⊤)))).inv ≫ e.hom.appTop)).2
  have hΦl : ∀ b, Φ (b ⊗ₜ[k] 1) = (pullback.fst pY pZ).appTop.hom b := by
    intro b
    change ((CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
      (Scheme.ΓSpecIso _).inv ≫ e.hom.appTop).hom b = _
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop, he1', Scheme.Hom.comp_appTop,
      Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
    erw [Iso.inv_hom_id_assoc]
  have hΦr : ∀ c, Φ (1 ⊗ₜ[k] c) = (pullback.snd pY pZ).appTop.hom c := by
    intro c
    have he2' : e.hom ≫ Spec.map (CommRingCat.ofHom
        (↑(Algebra.TensorProduct.includeRight (R := k) (A := (Y.presheaf.obj (Opposite.op ⊤) : Type u))
            (B := (Z.presheaf.obj (Opposite.op ⊤) : Type u))) : _ →+* _)) =
        pullback.snd pY pZ ≫ Z.isoSpec.hom := by
      rw [← sq.isoPullback_hom_snd, he2]; rfl
    change ((CommRingCat.ofHom
        (↑(Algebra.TensorProduct.includeRight (R := k) (A := (Y.presheaf.obj (Opposite.op ⊤) : Type u))
            (B := (Z.presheaf.obj (Opposite.op ⊤) : Type u))) : _ →+* _)) ≫
      (Scheme.ΓSpecIso _).inv ≫ e.hom.appTop).hom c = _
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop, he2', Scheme.Hom.comp_appTop,
      Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
    erw [Iso.inv_hom_id_assoc]

  have hevl : ∀ b, ev s ((pullback.fst pY pZ).appTop.hom b) = εB b := fun b =>
    congrArg (fun φ : _ →+* k => φ b) (ev_comp s (pullback.fst pY pZ))
  have hevr : ∀ c, ev s ((pullback.snd pY pZ).appTop.hom c) = εC c := fun c =>
    congrArg (fun φ : _ →+* k => φ c) (ev_comp s (pullback.snd pY pZ))
  have hevΦ : ∀ t, ev s (Φ t) = Algebra.TensorProduct.lid k k (Algebra.TensorProduct.map εB εC t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      have : b ⊗ₜ[k] c = (b ⊗ₜ[k] 1) * (1 ⊗ₜ[k] c) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this, map_mul, map_mul, hΦl, hΦr, hevl, hevr]
      simp [Algebra.TensorProduct.map_tmul]
    | add x x' hx hx' => simp only [map_add, hx, hx']

  letI algSt : Algebra Γ(pullback pY pZ, ⊤) ((pullback pY pZ).presheaf.stalk (s (closedPoint k))) :=
    TopCat.Presheaf.algebra_section_stalk (pullback pY pZ).presheaf
      (⟨s (closedPoint k), trivial⟩ : (⊤ : (pullback pY pZ).Opens))
  haveI hloc : IsLocalization.AtPrime ((pullback pY pZ).presheaf.stalk (s (closedPoint k)))
      (hX.primeIdealOf ⟨s (closedPoint k), trivial⟩).asIdeal :=
    hX.isLocalization_stalk ⟨s (closedPoint k), trivial⟩
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (hX.primeIdealOf ⟨s (closedPoint k), trivial⟩).asIdeal
    ((pullback pY pZ).presheaf.stalk (s (closedPoint k))), Ideal.map_le_iff_le_comap]
  intro a ha
  have ha' : a ∈ RingHom.ker (ev s) := by
    rw [mem_ker_ev_iff]
    have hu := IsLocalization.AtPrime.under_maximalIdeal ((pullback pY pZ).presheaf.stalk (s (closedPoint k)))
      (hX.primeIdealOf ⟨s (closedPoint k), trivial⟩).asIdeal
    rw [← hu] at ha
    exact ha
  obtain ⟨t, rfl⟩ := hΦsurj a
  have ht : t ∈ RingHom.ker (Algebra.TensorProduct.map εB εC) := by
    rw [RingHom.mem_ker] at ha' ⊢
    rw [hevΦ] at ha'
    exact (Algebra.TensorProduct.lid k k).injective (by rw [ha', map_zero])
  rw [Algebra.TensorProduct.map_ker εB εC hεB hεC] at ht
  obtain ⟨t1, ht1, t2, ht2, rfl⟩ := Submodule.mem_sup.mp ht
  rw [Ideal.mem_comap, map_add, map_add]
  refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
  · have key : ∀ b : Γ(Y, ⊤), ev (s ≫ pullback.fst pY pZ) b = 0 →
        algebraMap Γ(pullback pY pZ, ⊤) ((pullback pY pZ).presheaf.stalk (s (closedPoint k))) (Φ (b ⊗ₜ[k] 1)) ∈
          (maximalIdeal (Y.presheaf.stalk ((pullback.fst pY pZ) (s (closedPoint k))))).map
            ((pullback.fst pY pZ).stalkMap (s (closedPoint k))).hom := by
      intro b hb
      have : algebraMap Γ(pullback pY pZ, ⊤) ((pullback pY pZ).presheaf.stalk (s (closedPoint k))) (Φ (b ⊗ₜ[k] 1)) =
          ((pullback.fst pY pZ).stalkMap (s (closedPoint k))).hom
            ((Y.presheaf.germ ⊤ ((s ≫ pullback.fst pY pZ) (closedPoint k)) trivial).hom b) := by
        change ((pullback pY pZ).presheaf.germ ⊤ (s (closedPoint k)) trivial).hom (Φ (b ⊗ₜ[k] 1)) =
          (Y.presheaf.germ ⊤ ((pullback.fst pY pZ) (s (closedPoint k))) trivial ≫
            (pullback.fst pY pZ).stalkMap (s (closedPoint k))).hom b
        rw [hΦl, Scheme.Hom.germ_stalkMap]
        rfl
      rw [this]
      exact Ideal.mem_map_of_mem _ ((mem_ker_ev_iff (s ≫ pullback.fst pY pZ) b).mp hb)
    have hle : Ideal.map (Algebra.TensorProduct.includeLeft (R := k) (S := k)) (RingHom.ker εB) ≤
        Ideal.comap ((algebraMap _ ((pullback pY pZ).presheaf.stalk (s (closedPoint k)))).comp Φ)
          ((maximalIdeal (Y.presheaf.stalk ((pullback.fst pY pZ) (s (closedPoint k))))).map
            ((pullback.fst pY pZ).stalkMap (s (closedPoint k))).hom) :=
      Ideal.map_le_iff_le_comap.mpr fun b hb => Ideal.mem_comap.mpr (key b hb)
    exact hle ht1
  · have key : ∀ c : Γ(Z, ⊤), ev (s ≫ pullback.snd pY pZ) c = 0 →
        algebraMap Γ(pullback pY pZ, ⊤) ((pullback pY pZ).presheaf.stalk (s (closedPoint k))) (Φ (1 ⊗ₜ[k] c)) ∈
          (maximalIdeal (Z.presheaf.stalk ((pullback.snd pY pZ) (s (closedPoint k))))).map
            ((pullback.snd pY pZ).stalkMap (s (closedPoint k))).hom := by
      intro c hc
      have : algebraMap Γ(pullback pY pZ, ⊤) ((pullback pY pZ).presheaf.stalk (s (closedPoint k))) (Φ (1 ⊗ₜ[k] c)) =
          ((pullback.snd pY pZ).stalkMap (s (closedPoint k))).hom
            ((Z.presheaf.germ ⊤ ((s ≫ pullback.snd pY pZ) (closedPoint k)) trivial).hom c) := by
        change ((pullback pY pZ).presheaf.germ ⊤ (s (closedPoint k)) trivial).hom (Φ (1 ⊗ₜ[k] c)) =
          (Z.presheaf.germ ⊤ ((pullback.snd pY pZ) (s (closedPoint k))) trivial ≫
            (pullback.snd pY pZ).stalkMap (s (closedPoint k))).hom c
        rw [hΦr, Scheme.Hom.germ_stalkMap]
        rfl
      rw [this]
      exact Ideal.mem_map_of_mem _ ((mem_ker_ev_iff (s ≫ pullback.snd pY pZ) c).mp hc)
    have hle : Ideal.map (Algebra.TensorProduct.includeRight (R := k)) (RingHom.ker εC) ≤
        Ideal.comap ((algebraMap _ ((pullback pY pZ).presheaf.stalk (s (closedPoint k)))).comp Φ)
          ((maximalIdeal (Z.presheaf.stalk ((pullback.snd pY pZ) (s (closedPoint k))))).map
            ((pullback.snd pY pZ).stalkMap (s (closedPoint k))).hom) :=
      Ideal.map_le_iff_le_comap.mpr fun c hc => Ideal.mem_comap.mpr (key c hc)
    exact hle ht2

end S_AlgebraicGeometry_maximalIdeal_stalk_pullback_le_of_sections_of_isAffine
end P2MW
export P2MW.S_AlgebraicGeometry_maximalIdeal_stalk_pullback_le_of_sections_of_isAffine (solution)
