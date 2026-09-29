-- Prove2me | solution 1 for AlgebraicGeometry.exists_pow_eq_of_section_fromNormalization_kummer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1ff1d53e-beef-5c75-a87e-6671e5f97cc1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_pow_eq_of_section_fromNormalization_kummer

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace SecRoot

section thin

variable {Z : Scheme.{u}}

lemma map_op_congr {A B : Z.Opens} (i j : B ⟶ A) (s : Γ(Z, A)) :
    Z.presheaf.map i.op s = Z.presheaf.map j.op s := by
  rw [Subsingleton.elim i j]

lemma app_map_top {Z' : Scheme.{u}} (q : Z' ⟶ Z) (W : Z.Opens) (x : Γ(Z, ⊤)) :
    q.app W (Z.presheaf.map (homOfLE le_top).op x) =
      Z'.presheaf.map (homOfLE le_top).op (q.appTop x) := by
  have := congrArg (fun φ => φ.hom x) (q.naturality (homOfLE (le_top : W ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
  rw [this]
  exact map_op_congr _ _ _

lemma comp_app_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (x : Γ(Z, U)) :
    (f ≫ g).app U x = f.app (g ⁻¹ᵁ U) (g.app U x) := rfl

end thin

lemma root_pow {K : Type*} [CommRing K] (k : ℕ) (g : K) :
    AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C g) ^ k =
      algebraMap K (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g)) g := by
  have h := AdjoinRoot.mk_self (f := (Polynomial.X ^ k - Polynomial.C g))
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
  rw [h, AdjoinRoot.algebraMap_eq]

theorem exists_pow_eq {X : Scheme.{u}} [IsIntegral X] (k : ℕ) (g : X.functionField)
    {X' : Scheme.{u}} (φ : X' ⟶ X) [QuasiCompact φ] [QuasiSeparated φ]
    (s : X ⟶ φ.normalization) (hs : s ≫ φ.fromNormalization = 𝟙 X)
    (V : X.Opens) (hV : IsAffineOpen V) (hηV : genericPoint X ∈ V)
    (θ : AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField) →+* Γ(X', φ ⁻¹ᵁ V))
    (hθ : ∀ c : Γ(X, V), φ.app V c =
      θ (algebraMap X.functionField _ (X.presheaf.germ V (genericPoint X) hηV c))) :
    ∃ f : X.functionField, f ^ k = g := by
  haveI : Nonempty V := ⟨⟨_, hηV⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X V hV

  letI alg : Algebra Γ(X, V) Γ(X', φ ⁻¹ᵁ V) := (φ.app V).hom.toAlgebra
  have halg : ∀ c : Γ(X, V), algebraMap Γ(X, V) Γ(X', φ ⁻¹ᵁ V) c = φ.app V c := fun c => rfl

  have hgerm : ∀ c : Γ(X, V),
      X.presheaf.germ V (genericPoint X) hηV c = algebraMap Γ(X, V) X.functionField c := fun c => rfl

  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, V)) g
  have hb' : algebraMap Γ(X, V) X.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb

  let e := φ.normalizationObjIso hV
  have hπ := φ.fromNormalization_app hV

  have hW : genericPoint X ∈ s ⁻¹ᵁ (φ.fromNormalization ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, hs]; exact hηV

  let χ : integralClosure Γ(X, V) Γ(X', φ ⁻¹ᵁ V) →+* X.functionField :=
    (X.presheaf.germ _ (genericPoint X) hW).hom.comp ((s.app (φ.fromNormalization ⁻¹ᵁ V)).hom.comp e.inv.hom)
  have hχ : ∀ c : Γ(X, V),
      χ (algebraMap Γ(X, V) (integralClosure Γ(X, V) Γ(X', φ ⁻¹ᵁ V)) c) =
        algebraMap Γ(X, V) X.functionField c := by
    intro c
    have h1 : e.inv (algebraMap Γ(X, V) (integralClosure Γ(X, V) Γ(X', φ ⁻¹ᵁ V)) c) =
        φ.fromNormalization.app V c := by
      rw [hπ]; rfl
    have h2 : s.app (φ.fromNormalization ⁻¹ᵁ V) (φ.fromNormalization.app V c) =
        X.presheaf.map (eqToHom (by rw [← Scheme.Hom.comp_preimage, hs]; rfl)).op c := by
      rw [← comp_app_apply, Scheme.Hom.congr_app hs V, CommRingCat.comp_apply, Scheme.Hom.id_app]
      exact map_op_congr _ _ _
    simp only [χ, RingHom.coe_comp, Function.comp_apply]
    rw [h1, h2, TopCat.Presheaf.germ_res_apply]
    rfl

  rcases Nat.eq_zero_or_pos k with hk | hk
  ·
    subst hk
    refine ⟨1, ?_⟩
    have hL : (1 : AdjoinRoot (Polynomial.X ^ 0 - Polynomial.C g : Polynomial X.functionField)) =
        algebraMap _ _ g := (pow_zero _).symm.trans (root_pow 0 g)
    have hga : X.presheaf.germ V (genericPoint X) hηV a =
        g * X.presheaf.germ V (genericPoint X) hηV b := by
      rw [hgerm, hgerm, ← hab, div_mul_cancel₀ _ hb']
    have hφab : φ.app V a = φ.app V b := by
      rw [hθ, hθ, hga, map_mul, map_mul, ← hL, map_one, one_mul]
    have hIC : algebraMap Γ(X, V) (integralClosure Γ(X, V) Γ(X', φ ⁻¹ᵁ V)) a =
        algebraMap Γ(X, V) (integralClosure Γ(X, V) Γ(X', φ ⁻¹ᵁ V)) b := by
      apply Subtype.ext
      change algebraMap Γ(X, V) Γ(X', φ ⁻¹ᵁ V) a = algebraMap Γ(X, V) Γ(X', φ ⁻¹ᵁ V) b
      rw [halg, halg, hφab]
    have := congrArg χ hIC
    rw [hχ, hχ] at this
    rw [pow_zero, ← hab, this, div_self hb']
  ·
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hK : algebraMap Γ(X, V) X.functionField b ^ (m + 1) * g =
        algebraMap Γ(X, V) X.functionField (b ^ m * a) := by
      rw [← hab, map_mul, map_pow]
      field_simp
      ring
    let tb : AdjoinRoot (Polynomial.X ^ (m + 1) - Polynomial.C g : Polynomial X.functionField) :=
      algebraMap X.functionField _ (algebraMap Γ(X, V) X.functionField b) *
        AdjoinRoot.root (Polynomial.X ^ (m + 1) - Polynomial.C g)
    have htb : tb ^ (m + 1) =
        algebraMap X.functionField _ (algebraMap Γ(X, V) X.functionField (b ^ m * a)) := by
      simp only [tb]
      rw [mul_pow, ← map_pow, root_pow, ← map_mul, hK]
    have he₀ : θ tb ^ (m + 1) = φ.app V (b ^ m * a) := by
      rw [← map_pow, htb, ← hgerm, ← hθ]
    have hint : IsIntegral Γ(X, V) (θ tb) := by
      refine ⟨Polynomial.X ^ (m + 1) - Polynomial.C (b ^ m * a), Polynomial.monic_X_pow_sub_C _ (by omega), ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, he₀, halg, sub_self]
    let y : integralClosure Γ(X, V) Γ(X', φ ⁻¹ᵁ V) := ⟨θ tb, hint⟩
    have hy : y ^ (m + 1) = algebraMap Γ(X, V) (integralClosure Γ(X, V) Γ(X', φ ⁻¹ᵁ V)) (b ^ m * a) := by
      apply Subtype.ext
      change θ tb ^ (m + 1) = algebraMap Γ(X, V) Γ(X', φ ⁻¹ᵁ V) (b ^ m * a)
      rw [he₀, halg]
    have hF : χ y ^ (m + 1) = algebraMap Γ(X, V) X.functionField (b ^ m * a) := by
      rw [← map_pow, hy, hχ]
    refine ⟨χ y / algebraMap Γ(X, V) X.functionField b, ?_⟩
    rw [div_pow, hF, ← hab, map_mul, map_pow]
    field_simp
    ring

end SecRoot

open SecRoot in
theorem solution
    {X : Scheme.{u}} [IsIntegral X] (k : ℕ) (g : X.functionField) (hg : g ≠ 0)
    (s : X ⟶ (Spec.map (CommRingCat.ofHom (algebraMap X.functionField
        (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).normalization)
    (hs : s ≫ (Spec.map (CommRingCat.ofHom (algebraMap X.functionField
        (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).fromNormalization = 𝟙 X) :
    ∃ f : X.functionField, f ^ k = g := by

  let V : X.Opens := (X.affineCover.f (X.affineCover.idx (genericPoint X))).opensRange
  have hV : IsAffineOpen V := isAffineOpen_opensRange _
  have hηV : genericPoint X ∈ V := X.affineCover.covers _

  refine exists_pow_eq k g _ s hs V hV hηV
    (((Spec (CommRingCat.of (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))).presheaf.map
        (homOfLE le_top).op).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of
        (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))).inv.hom) ?_
  intro c
  rw [comp_app_apply, Scheme.fromSpecStalk_app hηV, CommRingCat.comp_apply, CommRingCat.comp_apply]
  erw [app_map_top]
  have hnat := congrArg (fun ψ => ψ.hom (X.presheaf.germ V (genericPoint X) hηV c))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap X.functionField
      (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at hnat
  simp only [RingHom.coe_comp, Function.comp_apply]
  erw [← hnat]
  exact map_op_congr _ _ _

end S_AlgebraicGeometry_exists_pow_eq_of_section_fromNormalization_kummer
end P2MW
export P2MW.S_AlgebraicGeometry_exists_pow_eq_of_section_fromNormalization_kummer (solution)
