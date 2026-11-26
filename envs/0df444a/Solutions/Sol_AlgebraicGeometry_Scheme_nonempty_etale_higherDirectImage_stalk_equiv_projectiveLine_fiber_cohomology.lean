-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_etale_higherDirectImage_stalk_equiv_projectiveLine_fiber_cohomology
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-26T06:24:26.104699+00:00
-- url     : https://prove2.me/submissions/73daf80f-0ae3-4335-8e74-e59a3de1fd33

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_223

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

open AlgebraicGeometry CategoryTheory Limits

theorem solution_aux
    (K : Type) [Field K] [IsAlgClosed K] (Λ : Type) [CommRing Λ] (hΛfin : Finite Λ)
    (l : ℕ) (hl : l.Prime) (hlK : (l : K) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)
    (S : Scheme.{0}) [IsNoetherian S] (g : S ⟶ Spec (.of K)) [LocallyOfFiniteType g]
    (π : Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K) ⟶ Spec (.of K))
    (hπ : π = Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) K) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0))))
    (s : Spec (.of K) ⟶ S) (hs : s ≫ g = 𝟙 _)
    (E : S.Etale ⥤ (pullback π g).Etale)
    (hE : E = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (pullback.snd π g))
    [E.IsContinuous S.smallEtaleTopology (pullback π g).smallEtaleTopology]
    [(E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology (pullback π g).smallEtaleTopology).Additive]
    (E' : (pullback π g).Etale ⥤ (pullback (pullback.snd π g) s).Etale)
    (hE' : E' = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (pullback.fst (pullback.snd π g) s))
    [E'.IsContinuous (pullback π g).smallEtaleTopology (pullback (pullback.snd π g) s).smallEtaleTopology]
    [(E'.sheafPushforwardContinuous (ModuleCat.{0} Λ) (pullback π g).smallEtaleTopology
      (pullback (pullback.snd π g) s).smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf (pullback π g).smallEtaleTopology (ModuleCat.{0} Λ)) (q : ℕ) :
    Nonempty (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} Λ)).obj
        (((E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
          (pullback π g).smallEtaleTopology).rightDerived q).obj F) ≃+
      (Abelian.Ext
        ((constantSheaf (pullback (pullback.snd π g) s).smallEtaleTopology (ModuleCat.{0} Λ)).obj
          (ModuleCat.of Λ Λ))
        ((E'.sheafPullback (ModuleCat.{0} Λ) (pullback π g).smallEtaleTopology
          (pullback (pullback.snd π g) s).smallEtaleTopology).obj F) q : Type)) := by
  obtain ⟨p, hp⟩ := ExpChar.exists K
  have := hΛfin
  have : Fact l.Prime := ⟨hl⟩
  subst hπ hE hE'
  let s' : RamanujanPetersson.EtSheaves.GeomPt S := ⟨K, s⟩
  have : IsIso (s'.pt ≫ g) := by
    show IsIso (s ≫ g)
    rw [hs]; infer_instance
  have hΛ' : ∀ x : Λ, (l ^ m) • x = 0 := fun x => by
    rw [nsmul_eq_mul, hΛ, zero_mul]
  exact RamanujanPetersson.EtPBC.pbc_P1 K p l hlK m hΛ' g s' F q

-- The Definitions chain declares the global instances EtMV.etsh_enoughInjectives and GalTrE.hasExtEt; erase them so the
-- statement below elaborates exactly as the Mathlib-only formal statement does (Mathlib's own instances).
attribute [-instance] RamanujanPetersson.EtPBC.EtMV.etsh_enoughInjectives
attribute [-instance] RamanujanPetersson.EtCompact.GalTrE.hasExtEt

theorem solution
    (K : Type) [Field K] [IsAlgClosed K] (Λ : Type) [CommRing Λ] (hΛfin : Finite Λ)
    (l : ℕ) (hl : l.Prime) (hlK : (l : K) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)
    (S : Scheme.{0}) [IsNoetherian S] (g : S ⟶ Spec (.of K)) [LocallyOfFiniteType g]
    (π : Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K) ⟶ Spec (.of K))
    (hπ : π = Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) K) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0))))
    (s : Spec (.of K) ⟶ S) (hs : s ≫ g = 𝟙 _)
    (E : S.Etale ⥤ (pullback π g).Etale)
    (hE : E = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (pullback.snd π g))
    [E.IsContinuous S.smallEtaleTopology (pullback π g).smallEtaleTopology]
    [(E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology (pullback π g).smallEtaleTopology).Additive]
    (E' : (pullback π g).Etale ⥤ (pullback (pullback.snd π g) s).Etale)
    (hE' : E' = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (pullback.fst (pullback.snd π g) s))
    [E'.IsContinuous (pullback π g).smallEtaleTopology (pullback (pullback.snd π g) s).smallEtaleTopology]
    [(E'.sheafPushforwardContinuous (ModuleCat.{0} Λ) (pullback π g).smallEtaleTopology
      (pullback (pullback.snd π g) s).smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf (pullback π g).smallEtaleTopology (ModuleCat.{0} Λ)) (q : ℕ) :
    Nonempty (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} Λ)).obj
        (((E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
          (pullback π g).smallEtaleTopology).rightDerived q).obj F) ≃+
      (Abelian.Ext
        ((constantSheaf (pullback (pullback.snd π g) s).smallEtaleTopology (ModuleCat.{0} Λ)).obj
          (ModuleCat.of Λ Λ))
        ((E'.sheafPullback (ModuleCat.{0} Λ) (pullback π g).smallEtaleTopology
          (pullback (pullback.snd π g) s).smallEtaleTopology).obj F) q : Type)) := by
  exact solution_aux K Λ hΛfin l hl hlK m hΛ S g π hπ s hs E hE E' hE' F q
