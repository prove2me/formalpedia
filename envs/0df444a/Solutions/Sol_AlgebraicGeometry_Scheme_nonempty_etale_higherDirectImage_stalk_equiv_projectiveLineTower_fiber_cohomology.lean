-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_etale_higherDirectImage_stalk_equiv_projectiveLineTower_fiber_cohomology
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-26T08:37:59.613156+00:00
-- url     : https://prove2.me/submissions/f1e2e2fa-b706-4864-b233-b37db082de70

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCB_007

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
    (T : ℕ → Σ Y : Scheme.{0}, Y ⟶ S)
    (hT0 : T 0 = ⟨pullback π g, pullback.snd π g⟩)
    (hTs : ∀ k, T (k + 1) =
      ⟨pullback π ((T k).2 ≫ g), pullback.snd π ((T k).2 ≫ g) ≫ (T k).2⟩)
    (n : ℕ) (s : Spec (.of K) ⟶ S) (hs : s ≫ g = 𝟙 _)
    (E : S.Etale ⥤ (T n).1.Etale)
    (hE : E = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (T n).2)
    [E.IsContinuous S.smallEtaleTopology (T n).1.smallEtaleTopology]
    [(E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
      (T n).1.smallEtaleTopology).Additive]
    (E' : (T n).1.Etale ⥤ (pullback (T n).2 s).Etale)
    (hE' : E' = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (pullback.fst (T n).2 s))
    [E'.IsContinuous (T n).1.smallEtaleTopology (pullback (T n).2 s).smallEtaleTopology]
    [(E'.sheafPushforwardContinuous (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology
      (pullback (T n).2 s).smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf (T n).1.smallEtaleTopology (ModuleCat.{0} Λ)) (q : ℕ) :
    Nonempty (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} Λ)).obj
        (((E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
          (T n).1.smallEtaleTopology).rightDerived q).obj F) ≃+
      (Abelian.Ext
        ((constantSheaf (pullback (T n).2 s).smallEtaleTopology (ModuleCat.{0} Λ)).obj
          (ModuleCat.of Λ Λ))
        ((E'.sheafPullback (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology
          (pullback (T n).2 s).smallEtaleTopology).obj F) q : Type)) := by
  obtain ⟨p, hp⟩ := ExpChar.exists K
  have := hΛfin
  have : Fact l.Prime := ⟨hl⟩
  subst hπ
  have hT : T = fun k => RamanujanPetersson.EtPBC.towerP K g k := by
    funext k
    induction k with
    | zero => exact hT0
    | succ k ih => rw [hTs k, ih]; rfl
  subst hT hE hE'
  let s' : RamanujanPetersson.EtSheaves.GeomPt S := ⟨K, s⟩
  have : IsIso (s'.pt ≫ g) := by
    show IsIso (s ≫ g)
    rw [hs]; infer_instance
  have hΛ' : ∀ x : Λ, (l ^ m) • x = 0 := fun x => by
    rw [nsmul_eq_mul, hΛ, zero_mul]
  exact RamanujanPetersson.EtPBC.pbc_towerP K Λ p l hlK m hΛ' g s' n F q

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
    (T : ℕ → Σ Y : Scheme.{0}, Y ⟶ S)
    (hT0 : T 0 = ⟨pullback π g, pullback.snd π g⟩)
    (hTs : ∀ k, T (k + 1) =
      ⟨pullback π ((T k).2 ≫ g), pullback.snd π ((T k).2 ≫ g) ≫ (T k).2⟩)
    (n : ℕ) (s : Spec (.of K) ⟶ S) (hs : s ≫ g = 𝟙 _)
    (E : S.Etale ⥤ (T n).1.Etale)
    (hE : E = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (T n).2)
    [E.IsContinuous S.smallEtaleTopology (T n).1.smallEtaleTopology]
    [(E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
      (T n).1.smallEtaleTopology).Additive]
    (E' : (T n).1.Etale ⥤ (pullback (T n).2 s).Etale)
    (hE' : E' = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (pullback.fst (T n).2 s))
    [E'.IsContinuous (T n).1.smallEtaleTopology (pullback (T n).2 s).smallEtaleTopology]
    [(E'.sheafPushforwardContinuous (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology
      (pullback (T n).2 s).smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf (T n).1.smallEtaleTopology (ModuleCat.{0} Λ)) (q : ℕ) :
    Nonempty (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} Λ)).obj
        (((E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
          (T n).1.smallEtaleTopology).rightDerived q).obj F) ≃+
      (Abelian.Ext
        ((constantSheaf (pullback (T n).2 s).smallEtaleTopology (ModuleCat.{0} Λ)).obj
          (ModuleCat.of Λ Λ))
        ((E'.sheafPullback (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology
          (pullback (T n).2 s).smallEtaleTopology).obj F) q : Type)) := by
  exact solution_aux K Λ hΛfin l hl hlK m hΛ S g π hπ T hT0 hTs n s hs E hE E' hE' F q
