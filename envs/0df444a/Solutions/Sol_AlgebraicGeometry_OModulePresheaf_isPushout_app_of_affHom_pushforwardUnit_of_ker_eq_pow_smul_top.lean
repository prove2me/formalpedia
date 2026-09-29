-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.isPushout_app_of_affHom_pushforwardUnit_of_ker_eq_pow_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4196e99c-d592-5970-8799-d1abedba26f5

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Theorems.Thm_AlgebraicGeometry_surjective_app_and_ker_eq_map_of_isPullback_specMap_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isPushout_app_of_affHom_pushforwardUnit_of_ker_eq_pow_smul_top

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem solution
    (R : Type u) [CommRing R] (I : Ideal R)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (Y : ℕ → Scheme.{u}) (g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n))
    (F : OModulePresheaf f)
    (ψ : ∀ n : ℕ, OModulePresheaf.AffHom F (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))))
    (hψs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ψ n).app U))
    (hψk : ∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((ψ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (F.obj U.1)))
    (A : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u})
    (α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ A)
    (e : ∀ U : X.AffineZariskiSite, A.obj (op U) ≃+ F.obj U.1)
    (hlin : ∀ (U : X.AffineZariskiSite) (a : Γ(X, U.1)) (x : A.obj (op U)),
      e U ((α.app (op U)).hom a * x) = a • e U x)
    (r : ∀ (n : ℕ) (U : X.AffineZariskiSite), A.obj (op U) →+* Γ(Y n, (g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1))
    (hr : ∀ (n : ℕ) (U : X.AffineZariskiSite) (x : A.obj (op U)), r n U x = (ψ n).app ⟨U.1, U.2⟩ (e U x))
    (n : ℕ) (U : X.AffineZariskiSite) :
    IsPushout (α.app (op U)) ((pullback.fst f (sR n)).app U.1) (CommRingCat.ofHom (r n U))
      ((g n).app ((pullback.fst f (sR n)) ⁻¹ᵁ U.1)) := by
  classical

  letI instRU : Algebra R Γ(X, U.1) := Scheme.TwoAffineOpenCover.algebraOfHom f U.1
  have hU : IsAffineOpen U.1 := U.2

  have Hpb : IsPullback (pullback.fst f (sR n)) (pullback.snd f (sR n)) f
      (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1))))) := by
    rw [← hsR n]; exact IsPullback.of_hasPullback f (sR n)
  obtain ⟨ht_surj, ht_ker⟩ :=
    AlgebraicGeometry.surjective_app_and_ker_eq_map_of_isPullback_specMap_of_surjective
      (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))) Ideal.Quotient.mk_surjective Hpb U.1 hU
  have ht_zero : ∀ i ∈ I ^ (n + 1), ((pullback.fst f (sR n)).app U.1).hom (algebraMap R Γ(X, U.1) i) = 0 := by
    intro i hi
    rw [← RingHom.mem_ker, ht_ker]
    apply Ideal.mem_map_of_mem
    simpa [RingHom.mem_ker] using hi

  have hr_surj : Function.Surjective (r n U) := by
    intro b
    obtain ⟨y, hy⟩ := hψs n ⟨U.1, U.2⟩ b
    exact ⟨(e U).symm y, by rw [hr, AddEquiv.apply_symm_apply, hy]⟩

  have hr1 : (ψ n).app ⟨U.1, U.2⟩ ((e U) 1) = (1 : Γ(Y n, (g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1)) := by
    rw [← hr]; exact map_one (r n U)
  have hrα : ∀ a : Γ(X, U.1), r n U ((α.app (op U)).hom a) =
      ((g n).app ((pullback.fst f (sR n)) ⁻¹ᵁ U.1)).hom (((pullback.fst f (sR n)).app U.1).hom a) := by
    intro a
    have h1 : (e U) ((α.app (op U)).hom a) = a • (e U) 1 := by
      simpa using hlin U a 1
    rw [hr, h1, (ψ n).app_smul, hr1]
    change ((g n ≫ pullback.fst f (sR n)).appLE U.1 ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1) le_rfl).hom a * 1 = _
    rw [mul_one, ← Scheme.Hom.app_eq_appLE, Scheme.Hom.comp_app]
    first
      | rfl
      | simp
  have hcomm : α.app (op U) ≫ CommRingCat.ofHom (r n U) =
      (pullback.fst f (sR n)).app U.1 ≫ (g n).app ((pullback.fst f (sR n)) ⁻¹ᵁ U.1) := by
    ext a; exact hrα a

  have hker : ∀ (W : CommRingCat.{u}) (a : A.obj (op U) ⟶ W) (b : Γ(pullback f (sR n), (pullback.fst f (sR n)) ⁻¹ᵁ U.1) ⟶ W),
      α.app (op U) ≫ a = (pullback.fst f (sR n)).app U.1 ≫ b →
      ∀ x : A.obj (op U), r n U x = 0 → a.hom x = 0 := by
    intro W a b hab x hx
    have hx' : (e U) x ∈ I ^ (n + 1) • (⊤ : Submodule R (F.obj U.1)) := by
      rw [← hψk n ⟨U.1, U.2⟩, LinearMap.mem_ker, ← hr]
      exact hx
    suffices h : ∀ y ∈ I ^ (n + 1) • (⊤ : Submodule R (F.obj U.1)), a.hom ((e U).symm y) = 0 by
      simpa using h _ hx'
    intro y hy
    induction hy using Submodule.smul_induction_on' with
    | smul i hi y _ =>
      have h2 : (e U).symm (i • y) = (α.app (op U)).hom (algebraMap R Γ(X, U.1) i) * (e U).symm y := by
        apply (e U).injective
        rw [AddEquiv.apply_symm_apply, hlin, AddEquiv.apply_symm_apply, algebraMap_smul]
      have h3 : a.hom ((α.app (op U)).hom (algebraMap R Γ(X, U.1) i)) =
          b.hom (((pullback.fst f (sR n)).app U.1).hom (algebraMap R Γ(X, U.1) i)) :=
        congrArg (fun φ => φ.hom (algebraMap R Γ(X, U.1) i)) hab
      rw [h2, map_mul, h3, ht_zero i hi, map_zero, zero_mul]
    | add y₁ y₂ _ _ h₁ h₂ => simp [map_add, h₁, h₂]

  let qe : (A.obj (op U) ⧸ RingHom.ker (r n U)) ≃+* Γ(Y n, (g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1) :=
    RingHom.quotientKerEquivOfSurjective hr_surj
  have hqe : ∀ x : A.obj (op U), qe.symm (r n U x) = Ideal.Quotient.mk (RingHom.ker (r n U)) x := by
    intro x
    apply qe.injective
    rw [RingEquiv.apply_symm_apply]
    first
      | rfl
      | exact (RingHom.kerLift_mk (r n U) x).symm
      | simp [qe, RingHom.quotientKerEquivOfSurjective, RingHom.quotientKerEquivOfRightInverse]
  refine IsPushout.of_isColimit' ⟨hcomm⟩ (PushoutCocone.IsColimit.mk hcomm
    (fun s => CommRingCat.ofHom ((Ideal.Quotient.lift (RingHom.ker (r n U)) s.inl.hom
      (fun x hx => hker s.pt s.inl s.inr s.condition x (RingHom.mem_ker.mp hx))).comp qe.symm.toRingHom)) ?_ ?_ ?_)
  · intro s
    have hK : ∀ a ∈ RingHom.ker (r n U), s.inl.hom a = 0 :=
      fun x hx => hker s.pt s.inl s.inr s.condition x (RingHom.mem_ker.mp hx)
    ext x
    change (Ideal.Quotient.lift (RingHom.ker (r n U)) s.inl.hom hK) (qe.symm (r n U x)) = s.inl.hom x
    rw [hqe, Ideal.Quotient.lift_mk]
  · intro s
    have hK : ∀ a ∈ RingHom.ker (r n U), s.inl.hom a = 0 :=
      fun x hx => hker s.pt s.inl s.inr s.condition x (RingHom.mem_ker.mp hx)
    ext y
    obtain ⟨a, rfl⟩ := ht_surj y
    change (Ideal.Quotient.lift (RingHom.ker (r n U)) s.inl.hom hK)
        (qe.symm (((g n).app ((pullback.fst f (sR n)) ⁻¹ᵁ U.1)).hom (((pullback.fst f (sR n)).app U.1).hom a))) =
      s.inr.hom (((pullback.fst f (sR n)).app U.1).hom a)
    rw [← hrα a, hqe, Ideal.Quotient.lift_mk]
    exact congrArg (fun φ => φ.hom a) s.condition
  · intro s m h1 h2
    have hK : ∀ a ∈ RingHom.ker (r n U), s.inl.hom a = 0 :=
      fun x hx => hker s.pt s.inl s.inr s.condition x (RingHom.mem_ker.mp hx)
    ext b
    obtain ⟨x, rfl⟩ := hr_surj b
    change m.hom (r n U x) = (Ideal.Quotient.lift (RingHom.ker (r n U)) s.inl.hom hK) (qe.symm (r n U x))
    rw [hqe, Ideal.Quotient.lift_mk]
    change (CommRingCat.ofHom (r n U) ≫ m).hom x = s.inl.hom x
    rw [h1]

end S_AlgebraicGeometry_OModulePresheaf_isPushout_app_of_affHom_pushforwardUnit_of_ker_eq_pow_smul_top
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_isPushout_app_of_affHom_pushforwardUnit_of_ker_eq_pow_smul_top (solution)
