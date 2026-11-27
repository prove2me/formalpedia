-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_etale_compactSupport_baseChange_natIso_projectiveLineTower
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-27T02:18:38.712829+00:00
-- url     : https://prove2.me/submissions/841510d8-0b85-49c7-b012-5ccc40436f7d

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC2_004

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

open AlgebraicGeometry CategoryTheory Limits

theorem solution_aux
    (K : Type) [Field K] [IsAlgClosed K] (Λ : Type) [CommRing Λ] (hΛfin : Finite Λ)
    (l : ℕ) (hl : l.Prime) (hlK : (l : K) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)
    (S : Scheme.{0}) [IsNoetherian S] (gS : S ⟶ Spec (.of K)) [LocallyOfFiniteType gS]
    (S' : Scheme.{0}) [IsNoetherian S'] (g : S' ⟶ S) [LocallyOfFiniteType (g ≫ gS)]
    (π : Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K) ⟶ Spec (.of K))
    (hπ : π = Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) K) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0))))
    (T : ℕ → Σ Y : Scheme.{0}, Y ⟶ S)
    (hT0 : T 0 = ⟨pullback π gS, pullback.snd π gS⟩)
    (hTs : ∀ k, T (k + 1) =
      ⟨pullback π ((T k).2 ≫ gS), pullback.snd π ((T k).2 ≫ gS) ≫ (T k).2⟩)
    (n : ℕ) {X Z : Scheme.{0}} (j : X ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ (T n).1) [IsClosedImmersion i]
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
    (Eg : S.Etale ⥤ S'.Etale)
    (hEg : Eg = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) g)
    [Eg.IsContinuous S.smallEtaleTopology S'.smallEtaleTopology]
    [(Eg.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
      S'.smallEtaleTopology).IsRightAdjoint]
    (E' : S'.Etale ⥤ (pullback (T n).2 g).Etale)
    (hE' : E' = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (pullback.snd (T n).2 g))
    [E'.IsContinuous S'.smallEtaleTopology (pullback (T n).2 g).smallEtaleTopology]
    [(E'.sheafPushforwardContinuous (ModuleCat.{0} Λ) S'.smallEtaleTopology
      (pullback (T n).2 g).smallEtaleTopology).Additive]
    (Ei' : (pullback (T n).2 g).Etale ⥤ (pullback i (pullback.fst (T n).2 g)).Etale)
    (hEi' : Ei' = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤)
      (pullback.snd i (pullback.fst (T n).2 g)))
    [Ei'.IsContinuous (pullback (T n).2 g).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 g)).smallEtaleTopology]
    (Ej' : (pullback j (pullback.fst i (pullback.fst (T n).2 g))).Etale ⥤
      (pullback i (pullback.fst (T n).2 g)).Etale)
    (hEj' : Ej' = MorphismProperty.Over.map (P := @Etale) ⊤
      (inferInstance : Etale (pullback.snd j (pullback.fst i (pullback.fst (T n).2 g)))))
    [Ej'.IsContinuous (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 g)).smallEtaleTopology]
    [(Ej'.sheafPushforwardContinuous (ModuleCat.{0} Λ)
      (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 g)).smallEtaleTopology).IsRightAdjoint]
    (EX : X.Etale ⥤ (pullback j (pullback.fst i (pullback.fst (T n).2 g))).Etale)
    (hEX : EX = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤)
      (pullback.fst j (pullback.fst i (pullback.fst (T n).2 g))))
    [EX.IsContinuous X.smallEtaleTopology
      (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology]
    [(EX.sheafPushforwardContinuous (ModuleCat.{0} Λ) X.smallEtaleTopology
      (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology).IsRightAdjoint]
    (q : ℕ) :
    Nonempty
      (Ej.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology Z.smallEtaleTopology ⋙
        Ei.sheafPushforwardContinuous (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology Z.smallEtaleTopology ⋙
        (E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
          (T n).1.smallEtaleTopology).rightDerived q ⋙
        Eg.sheafPullback (ModuleCat.{0} Λ) S.smallEtaleTopology S'.smallEtaleTopology ≅
      EX.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology
          (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology ⋙
        Ej'.sheafPullback (ModuleCat.{0} Λ)
          (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology
          (pullback i (pullback.fst (T n).2 g)).smallEtaleTopology ⋙
        Ei'.sheafPushforwardContinuous (ModuleCat.{0} Λ) (pullback (T n).2 g).smallEtaleTopology
          (pullback i (pullback.fst (T n).2 g)).smallEtaleTopology ⋙
        (E'.sheafPushforwardContinuous (ModuleCat.{0} Λ) S'.smallEtaleTopology
          (pullback (T n).2 g).smallEtaleTopology).rightDerived q) := by
  obtain ⟨p, hp⟩ := ExpChar.exists K
  have := hΛfin
  have : Fact l.Prime := ⟨hl⟩
  subst hπ
  have hT : T = fun k => RamanujanPetersson.EtPBC.towerP K gS k := by
    funext k
    induction k with
    | zero => exact hT0
    | succ k ih => rw [hTs k, ih]; rfl
  subst hT hE hEi hEj hEg hE' hEi' hEj' hEX
  have hΛ' : ∀ x : Λ, (l ^ m) • x = 0 := fun x => by
    rw [nsmul_eq_mul, hΛ, zero_mul]
  have key : ∀ k, RamanujanPetersson.EtPBC.C2.IsTower K gS (RamanujanPetersson.EtPBC.towerP K gS k).2 := by
    intro k
    induction k with
    | zero => exact RamanujanPetersson.EtPBC.C2.IsTower.base
    | succ k ih => exact RamanujanPetersson.EtPBC.C2.IsTower.step (RamanujanPetersson.EtPBC.towerP K gS k).2 ih
  let c : RamanujanPetersson.EtCompact.Cpt (j ≫ i ≫ (RamanujanPetersson.EtPBC.towerP K gS n).2) :=
    { P := (RamanujanPetersson.EtPBC.towerP K gS n).1, Z := Z, j := j, i := i,
      fbar := (RamanujanPetersson.EtPBC.towerP K gS n).2,
      isOpenImmersion_j := inferInstance, isClosedImmersion_i := inferInstance,
      isProper_fbar := inferInstance, comm := rfl }
  exact ⟨NatIso.ofComponents
    (fun F => RamanujanPetersson.EtPBC.C2.bcMorIso K Λ p l hlK m hΛ' gS g c (key n) q F)
    (fun φ => RamanujanPetersson.EtPBC.C1.bcMor_natural Λ c g q φ)⟩

-- The Definitions chain declares the global instance EtMV.etsh_enoughInjectives; erase it so the statement below
-- elaborates exactly as the Mathlib-only formal statement does (Mathlib's own instances).
attribute [-instance] RamanujanPetersson.EtPBC.EtMV.etsh_enoughInjectives

theorem solution
    (K : Type) [Field K] [IsAlgClosed K] (Λ : Type) [CommRing Λ] (hΛfin : Finite Λ)
    (l : ℕ) (hl : l.Prime) (hlK : (l : K) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)
    (S : Scheme.{0}) [IsNoetherian S] (gS : S ⟶ Spec (.of K)) [LocallyOfFiniteType gS]
    (S' : Scheme.{0}) [IsNoetherian S'] (g : S' ⟶ S) [LocallyOfFiniteType (g ≫ gS)]
    (π : Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K) ⟶ Spec (.of K))
    (hπ : π = Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) K) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0))))
    (T : ℕ → Σ Y : Scheme.{0}, Y ⟶ S)
    (hT0 : T 0 = ⟨pullback π gS, pullback.snd π gS⟩)
    (hTs : ∀ k, T (k + 1) =
      ⟨pullback π ((T k).2 ≫ gS), pullback.snd π ((T k).2 ≫ gS) ≫ (T k).2⟩)
    (n : ℕ) {X Z : Scheme.{0}} (j : X ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ (T n).1) [IsClosedImmersion i]
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
    (Eg : S.Etale ⥤ S'.Etale)
    (hEg : Eg = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) g)
    [Eg.IsContinuous S.smallEtaleTopology S'.smallEtaleTopology]
    [(Eg.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
      S'.smallEtaleTopology).IsRightAdjoint]
    (E' : S'.Etale ⥤ (pullback (T n).2 g).Etale)
    (hE' : E' = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) (pullback.snd (T n).2 g))
    [E'.IsContinuous S'.smallEtaleTopology (pullback (T n).2 g).smallEtaleTopology]
    [(E'.sheafPushforwardContinuous (ModuleCat.{0} Λ) S'.smallEtaleTopology
      (pullback (T n).2 g).smallEtaleTopology).Additive]
    (Ei' : (pullback (T n).2 g).Etale ⥤ (pullback i (pullback.fst (T n).2 g)).Etale)
    (hEi' : Ei' = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤)
      (pullback.snd i (pullback.fst (T n).2 g)))
    [Ei'.IsContinuous (pullback (T n).2 g).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 g)).smallEtaleTopology]
    (Ej' : (pullback j (pullback.fst i (pullback.fst (T n).2 g))).Etale ⥤
      (pullback i (pullback.fst (T n).2 g)).Etale)
    (hEj' : Ej' = MorphismProperty.Over.map (P := @Etale) ⊤
      (inferInstance : Etale (pullback.snd j (pullback.fst i (pullback.fst (T n).2 g)))))
    [Ej'.IsContinuous (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 g)).smallEtaleTopology]
    [(Ej'.sheafPushforwardContinuous (ModuleCat.{0} Λ)
      (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology
      (pullback i (pullback.fst (T n).2 g)).smallEtaleTopology).IsRightAdjoint]
    (EX : X.Etale ⥤ (pullback j (pullback.fst i (pullback.fst (T n).2 g))).Etale)
    (hEX : EX = MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤)
      (pullback.fst j (pullback.fst i (pullback.fst (T n).2 g))))
    [EX.IsContinuous X.smallEtaleTopology
      (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology]
    [(EX.sheafPushforwardContinuous (ModuleCat.{0} Λ) X.smallEtaleTopology
      (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology).IsRightAdjoint]
    (q : ℕ) :
    Nonempty
      (Ej.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology Z.smallEtaleTopology ⋙
        Ei.sheafPushforwardContinuous (ModuleCat.{0} Λ) (T n).1.smallEtaleTopology Z.smallEtaleTopology ⋙
        (E.sheafPushforwardContinuous (ModuleCat.{0} Λ) S.smallEtaleTopology
          (T n).1.smallEtaleTopology).rightDerived q ⋙
        Eg.sheafPullback (ModuleCat.{0} Λ) S.smallEtaleTopology S'.smallEtaleTopology ≅
      EX.sheafPullback (ModuleCat.{0} Λ) X.smallEtaleTopology
          (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology ⋙
        Ej'.sheafPullback (ModuleCat.{0} Λ)
          (pullback j (pullback.fst i (pullback.fst (T n).2 g))).smallEtaleTopology
          (pullback i (pullback.fst (T n).2 g)).smallEtaleTopology ⋙
        Ei'.sheafPushforwardContinuous (ModuleCat.{0} Λ) (pullback (T n).2 g).smallEtaleTopology
          (pullback i (pullback.fst (T n).2 g)).smallEtaleTopology ⋙
        (E'.sheafPushforwardContinuous (ModuleCat.{0} Λ) S'.smallEtaleTopology
          (pullback (T n).2 g).smallEtaleTopology).rightDerived q) := by
  exact solution_aux K Λ hΛfin l hl hlK m hΛ S gS S' g π hπ T hT0 hTs n j i E hE Ei hEi Ej hEj Eg hEg E' hE'
    Ei' hEi' Ej' hEj' EX hEX q
