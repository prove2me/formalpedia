-- Prove2me | solution 1 for AlgebraicGeometry.exists_hom_glued_comp_toBase_eq_and_isPushout_of_affHom_pushforwardUnit_of_coequifibered
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0a85c6cd-9731-5baf-a3f4-016b2fb1150d

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Theorems.Thm_AlgebraicGeometry_exists_hom_glued_comp_toBase_eq_of_affHom_pushforwardUnit_of_coequifibered
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isPushout_app_of_affHom_pushforwardUnit_of_ker_eq_pow_smul_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_hom_glued_comp_toBase_eq_and_isPushout_of_affHom_pushforwardUnit_of_coequifibered

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1))))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)

    (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)

    (Y : ℕ → Scheme.{u}) (g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n)) [∀ n : ℕ, IsFinite (g n)]
    (yn : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n))

    (F : OModulePresheaf f) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent)
    (ψ : ∀ n : ℕ, OModulePresheaf.AffHom F (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))))
    (hψs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ψ n).app U))
    (hψk : ∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((ψ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (F.obj U.1)))
    (hψc : ∀ (n : ℕ) (U : X.affineOpens) (x : F.obj U.1),
      (ψ n).app U x =
        ((yn n).appLE ((g (n + 1) ≫ pullback.fst f (sR (n + 1))) ⁻¹ᵁ U.1) ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1)
          (by rw [← Scheme.Hom.comp_preimage, ← Category.assoc, (hY n).w, Category.assoc, hxn₁])).hom
          ((ψ (n + 1)).app U x))

    (A : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u})
    (α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ A) (Hco : α.Coequifibered)
    (e : ∀ U : X.AffineZariskiSite, A.obj (op U) ≃+ F.obj U.1)
    (hlin : ∀ (U : X.AffineZariskiSite) (a : Γ(X, U.1)) (x : A.obj (op U)),
      e U ((α.app (op U)).hom a * x) = a • e U x)
    (hnat : ∀ (U V : X.AffineZariskiSite) (i : V ⟶ U) (x : A.obj (op U)),
      e V ((A.map i.op).hom x) = F.res (Scheme.AffineZariskiSite.toOpens_mono i.le) (e U x))
    (r : ∀ (n : ℕ) (U : X.AffineZariskiSite), A.obj (op U) →+* Γ(Y n, (g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1))
    (hr : ∀ (n : ℕ) (U : X.AffineZariskiSite) (x : A.obj (op U)), r n U x = (ψ n).app ⟨U.1, U.2⟩ (e U x)) :
    ∃ φ : ∀ n : ℕ, Y n ⟶ (Scheme.AffineZariskiSite.relativeGluingData Hco).glued,
      (∀ n : ℕ, φ n ≫ (Scheme.AffineZariskiSite.relativeGluingData Hco).toBase = g n ≫ pullback.fst f (sR n)) ∧
      (∀ n : ℕ, yn n ≫ φ (n + 1) = φ n) ∧
      (∀ (n : ℕ) (U : X.AffineZariskiSite),
        ((g n) ⁻¹ᵁ ((pullback.fst f (sR n)) ⁻¹ᵁ U.1)).ι ≫ φ n =
          ((g n) ⁻¹ᵁ ((pullback.fst f (sR n)) ⁻¹ᵁ U.1)).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (r n U)) ≫
            (Scheme.AffineZariskiSite.relativeGluingData Hco).cover.f U) ∧
      (∀ (n : ℕ) (U : X.AffineZariskiSite),
        IsPushout (α.app (op U)) ((pullback.fst f (sR n)).app U.1) (CommRingCat.ofHom (r n U))
          ((g n).app ((pullback.fst f (sR n)) ⁻¹ᵁ U.1))) := by
  obtain ⟨φ, h1, h2, h3⟩ :=
    AlgebraicGeometry.exists_hom_glued_comp_toBase_eq_of_affHom_pushforwardUnit_of_coequifibered
      R I X f sR hsR tR htR xn hxn₁ hxn₂ Y g yn hY F ψ hψc A α Hco e hlin hnat r hr
  exact ⟨φ, h1, h2, h3, fun n U =>
    AlgebraicGeometry.OModulePresheaf.isPushout_app_of_affHom_pushforwardUnit_of_ker_eq_pow_smul_top
      R I X f sR hsR Y g F ψ hψs hψk A α e hlin r hr n U⟩

end S_AlgebraicGeometry_exists_hom_glued_comp_toBase_eq_and_isPushout_of_affHom_pushforwardUnit_of_coequifibered
end P2MW
export P2MW.S_AlgebraicGeometry_exists_hom_glued_comp_toBase_eq_and_isPushout_of_affHom_pushforwardUnit_of_coequifibered (solution)
