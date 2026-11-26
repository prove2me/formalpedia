-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_natural_etale_compactSupport_stalk_equiv_projectiveLineTower_fiber_cohomology
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-26T19:56:59.861594+00:00
-- url     : https://prove2.me/submissions/54270625-c42c-4bc9-97db-765aa5e2d086

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCB_007
import Definitions.Def_RPLib_FX_EtPBCC1_012

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
    {X Z : Scheme.{0}} (j : X ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ (T n).1) [IsClosedImmersion i]
    (E : S.Etale ⥤ (T n).1.Etale)
    (hE : E = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (T n).2)
    [E.IsContinuous S.smallEtaleTopology (T n).1.smallEtaleTopology]
    [(E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
      (T n).1.smallEtaleTopology).Additive]
    (Ei : (T n).1.Etale ⥤ Z.Etale)
    (hEi : Ei = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) i)
    [Ei.IsContinuous (T n).1.smallEtaleTopology Z.smallEtaleTopology]
    (Ej : X.Etale ⥤ Z.Etale)
    (hEj : Ej = MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : Etale j))
    [Ej.IsContinuous X.smallEtaleTopology Z.smallEtaleTopology]
    [(Ej.sheafPushforwardContinuous (ModuleCat.{0} Λ) X.smallEtaleTopology
      Z.smallEtaleTopology).IsRightAdjoint]
    (Eis : (pullback (T n).2 s).Etale ⥤ (pullback i (pullback.fst (T n).2 s)).Etale)
    (hEis : Eis = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤)
      (pullback.snd i (pullback.fst (T n).2 s)))
    [Eis.IsContinuous (pullback (T n).2 s).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology]
    (Ejs : (pullback j (pullback.fst i (pullback.fst (T n).2 s))).Etale ⥤
      (pullback i (pullback.fst (T n).2 s)).Etale)
    (hEjs : Ejs = MorphismProperty.Over.map (P := @Etale) ⊤
      (inferInstance : Etale (pullback.snd j (pullback.fst i (pullback.fst (T n).2 s)))))
    [Ejs.IsContinuous (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology]
    [(Ejs.sheafPushforwardContinuous (ModuleCat.{0} Λ)
      (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology).IsRightAdjoint]
    (EX : X.Etale ⥤ (pullback j (pullback.fst i (pullback.fst (T n).2 s))).Etale)
    (hEX : EX = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤)
      (pullback.fst j (pullback.fst i (pullback.fst (T n).2 s))))
    [EX.IsContinuous X.smallEtaleTopology
      (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology]
    [(EX.sheafPushforwardContinuous (ModuleCat.{0} Λ) X.smallEtaleTopology
      (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology).IsRightAdjoint]
    (q : ℕ) :
    ∃ e : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{0} Λ),
        (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} Λ)).obj
          (((E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
            (T n).1.smallEtaleTopology).rightDerived q).obj
            ((Ei.sheafPushforwardContinuous (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology
              Z.smallEtaleTopology).obj
              ((Ej.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology Z.smallEtaleTopology).obj F))) ≃+
        (Abelian.Ext
          ((constantSheaf (pullback (T n).2 s).smallEtaleTopology (ModuleCat.{0} Λ)).obj
            (ModuleCat.of Λ Λ))
          ((Eis.sheafPushforwardContinuous (ModuleCat.{0} Λ) (pullback (T n).2 s).smallEtaleTopology
            (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology).obj
            ((Ejs.sheafPullback (ModuleCat.{0} Λ)
              (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology
              (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology).obj
              ((EX.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology
                (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology).obj F))) q :
          Type)),
      ∀ (F F' : Sheaf X.smallEtaleTopology (ModuleCat.{0} Λ)) (φ : F ⟶ F')
        (y : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} Λ)).obj
          (((E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
            (T n).1.smallEtaleTopology).rightDerived q).obj
            ((Ei.sheafPushforwardContinuous (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology
              Z.smallEtaleTopology).obj
              ((Ej.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology Z.smallEtaleTopology).obj F)))),
        e F' ((((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} Λ)).map
          (((E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
            (T n).1.smallEtaleTopology).rightDerived q).map
            ((Ei.sheafPushforwardContinuous (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology
              Z.smallEtaleTopology).map
              ((Ej.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology Z.smallEtaleTopology).map φ)))).hom y) =
        (e F y).comp (Abelian.Ext.mk₀
          ((Eis.sheafPushforwardContinuous (ModuleCat.{0} Λ) (pullback (T n).2 s).smallEtaleTopology
            (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology).map
            ((Ejs.sheafPullback (ModuleCat.{0} Λ)
              (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology
              (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology).map
              ((EX.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology
                (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology).map φ))))
          (add_zero q) := by
  obtain ⟨p, hp⟩ := ExpChar.exists K
  have := hΛfin
  have : Fact l.Prime := ⟨hl⟩
  subst hπ
  have hT : T = fun k => RamanujanPetersson.EtPBC.towerP K g k := by
    funext k
    induction k with
    | zero => exact hT0
    | succ k ih => rw [hTs k, ih]; rfl
  subst hT hE hEi hEj hEis hEjs hEX
  let s' : RamanujanPetersson.EtSheaves.GeomPt S := ⟨K, s⟩
  have : IsIso (s'.pt ≫ g) := by
    show IsIso (s ≫ g)
    rw [hs]; infer_instance
  have hΛ' : ∀ x : Λ, (l ^ m) • x = 0 := fun x => by
    rw [nsmul_eq_mul, hΛ, zero_mul]
  let c : RamanujanPetersson.EtCompact.Cpt (j ≫ i ≫ (RamanujanPetersson.EtPBC.towerP K g n).2) :=
    { P := (RamanujanPetersson.EtPBC.towerP K g n).1, Z := Z, j := j, i := i,
      fbar := (RamanujanPetersson.EtPBC.towerP K g n).2,
      isOpenImmersion_j := inferInstance, isClosedImmersion_i := inferInstance,
      isProper_fbar := inferInstance, comm := rfl }
  have hg : RamanujanPetersson.EtPBC.PBCGood Λ c.fbar s' :=
    RamanujanPetersson.EtPBC.good_towerP K Λ p l hlK m hΛ' g s' n
  exact ⟨fun F => RamanujanPetersson.EtPBC.C1.pbcEquivC c s' hg F q,
    fun F F' φ y => (RamanujanPetersson.EtPBC.C1.pbcEquivC_natural c s' hg φ q y).trans
      (RamanujanPetersson.EtCompact.Hmap_apply _ _ _ _)⟩

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
    {X Z : Scheme.{0}} (j : X ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ (T n).1) [IsClosedImmersion i]
    (E : S.Etale ⥤ (T n).1.Etale)
    (hE : E = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (T n).2)
    [E.IsContinuous S.smallEtaleTopology (T n).1.smallEtaleTopology]
    [(E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
      (T n).1.smallEtaleTopology).Additive]
    (Ei : (T n).1.Etale ⥤ Z.Etale)
    (hEi : Ei = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) i)
    [Ei.IsContinuous (T n).1.smallEtaleTopology Z.smallEtaleTopology]
    (Ej : X.Etale ⥤ Z.Etale)
    (hEj : Ej = MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : Etale j))
    [Ej.IsContinuous X.smallEtaleTopology Z.smallEtaleTopology]
    [(Ej.sheafPushforwardContinuous (ModuleCat.{0} Λ) X.smallEtaleTopology
      Z.smallEtaleTopology).IsRightAdjoint]
    (Eis : (pullback (T n).2 s).Etale ⥤ (pullback i (pullback.fst (T n).2 s)).Etale)
    (hEis : Eis = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤)
      (pullback.snd i (pullback.fst (T n).2 s)))
    [Eis.IsContinuous (pullback (T n).2 s).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology]
    (Ejs : (pullback j (pullback.fst i (pullback.fst (T n).2 s))).Etale ⥤
      (pullback i (pullback.fst (T n).2 s)).Etale)
    (hEjs : Ejs = MorphismProperty.Over.map (P := @Etale) ⊤
      (inferInstance : Etale (pullback.snd j (pullback.fst i (pullback.fst (T n).2 s)))))
    [Ejs.IsContinuous (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology]
    [(Ejs.sheafPushforwardContinuous (ModuleCat.{0} Λ)
      (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology).IsRightAdjoint]
    (EX : X.Etale ⥤ (pullback j (pullback.fst i (pullback.fst (T n).2 s))).Etale)
    (hEX : EX = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤)
      (pullback.fst j (pullback.fst i (pullback.fst (T n).2 s))))
    [EX.IsContinuous X.smallEtaleTopology
      (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology]
    [(EX.sheafPushforwardContinuous (ModuleCat.{0} Λ) X.smallEtaleTopology
      (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology).IsRightAdjoint]
    (q : ℕ) :
    ∃ e : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{0} Λ),
        (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} Λ)).obj
          (((E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
            (T n).1.smallEtaleTopology).rightDerived q).obj
            ((Ei.sheafPushforwardContinuous (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology
              Z.smallEtaleTopology).obj
              ((Ej.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology Z.smallEtaleTopology).obj F))) ≃+
        (Abelian.Ext
          ((constantSheaf (pullback (T n).2 s).smallEtaleTopology (ModuleCat.{0} Λ)).obj
            (ModuleCat.of Λ Λ))
          ((Eis.sheafPushforwardContinuous (ModuleCat.{0} Λ) (pullback (T n).2 s).smallEtaleTopology
            (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology).obj
            ((Ejs.sheafPullback (ModuleCat.{0} Λ)
              (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology
              (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology).obj
              ((EX.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology
                (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology).obj F))) q :
          Type)),
      ∀ (F F' : Sheaf X.smallEtaleTopology (ModuleCat.{0} Λ)) (φ : F ⟶ F')
        (y : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} Λ)).obj
          (((E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
            (T n).1.smallEtaleTopology).rightDerived q).obj
            ((Ei.sheafPushforwardContinuous (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology
              Z.smallEtaleTopology).obj
              ((Ej.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology Z.smallEtaleTopology).obj F)))),
        e F' ((((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} Λ)).map
          (((E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
            (T n).1.smallEtaleTopology).rightDerived q).map
            ((Ei.sheafPushforwardContinuous (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology
              Z.smallEtaleTopology).map
              ((Ej.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology Z.smallEtaleTopology).map φ)))).hom y) =
        (e F y).comp (Abelian.Ext.mk₀
          ((Eis.sheafPushforwardContinuous (ModuleCat.{0} Λ) (pullback (T n).2 s).smallEtaleTopology
            (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology).map
            ((Ejs.sheafPullback (ModuleCat.{0} Λ)
              (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology
              (pullback i (pullback.fst (T n).2 s)).smallEtaleTopology).map
              ((EX.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology
                (pullback j (pullback.fst i (pullback.fst (T n).2 s))).smallEtaleTopology).map φ))))
          (add_zero q) := by
  exact solution_aux K Λ hΛfin l hl hlK m hΛ S g π hπ T hT0 hTs n s hs j i E hE Ei hEi Ej hEj Eis hEis Ejs hEjs EX hEX q
