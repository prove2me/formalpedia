-- Prove2me | solution 1 for AlgebraicGeometry.ker_fiberIota_stalkMap_eq_maximalIdeal_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a5ec4edc-798b-5028-9c4d-b7ccd738e08e

import Mathlib
import Definitions.Def_Mathlib_RingTheory_KmfloorsGlueFiberLocalizationQuotientEngine
import Definitions.Def_AlgebraicGeometry_Kmf2FiberSpecTensorStalkLeg1AffineDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ker_fiberIota_stalkMap_eq_maximalIdeal_map

set_option autoImplicit false
set_option maxHeartbeats 6400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

noncomputable section

namespace KERPort

abbrev KwFF14FiberιStalkMapKer : Prop :=
  ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (s : Spec (CommRingCat.of R)) (q : f.fiber s),
    RingHom.ker ((f.fiberι s).stalkMap q).hom =
      (IsLocalRing.maximalIdeal
        ((Spec (CommRingCat.of R)).presheaf.stalk (f.base ((f.fiberι s).base q)))).map
        (f.stalkMap ((f.fiberι s).base q)).hom

theorem kwFF14_map_stalkMap_congr_point {S X : Scheme.{0}} (f : X ⟶ S) (y y' : X)
    (hyy' : y = y') :
    ((IsLocalRing.maximalIdeal (S.presheaf.stalk (f.base y))).map (f.stalkMap y).hom).map
        (X.presheaf.stalkCongr (.of_eq hyy')).hom.hom =
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f.base y'))).map (f.stalkMap y').hom := by
  subst hyy'
  simp [TopCat.Presheaf.stalkCongr, TopCat.Presheaf.stalkSpecializes_refl, Ideal.map_id]

abbrev KwFF15FiberιStalkMapKerAffine : Prop :=
  ∀ (R : Type) (S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (s : Spec (CommRingCat.of R))
    (q : (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber s),
    RingHom.ker (((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι s).stalkMap q).hom =
      (IsLocalRing.maximalIdeal
        ((Spec (CommRingCat.of R)).presheaf.stalk
          ((Spec.map (CommRingCat.ofHom (algebraMap R S))).base
            (((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι s).base q)))).map
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap
          (((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι s).base q)).hom

theorem kwFF15_kerEq_of_congr_hom {S X : Scheme.{0}} (f f' : X ⟶ S) (hff' : f = f')
    (s : S) (q : f.fiber s)
    (hall : ∀ q' : f'.fiber s, RingHom.ker ((f'.fiberι s).stalkMap q').hom =
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f'.base ((f'.fiberι s).base q')))).map
        (f'.stalkMap ((f'.fiberι s).base q')).hom) :
    RingHom.ker ((f.fiberι s).stalkMap q).hom =
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f.base ((f.fiberι s).base q)))).map
        (f.stalkMap ((f.fiberι s).base q)).hom := by
  subst hff'; exact hall q

theorem kwFF15_kerEq_congr_point {S X : Scheme.{0}} (f : X ⟶ S) (s : S)
    (q q' : f.fiber s) (hqq' : q = q')
    (h : RingHom.ker ((f.fiberι s).stalkMap q).hom =
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f.base ((f.fiberι s).base q)))).map
        (f.stalkMap ((f.fiberι s).base q)).hom) :
    RingHom.ker ((f.fiberι s).stalkMap q').hom =
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f.base ((f.fiberι s).base q')))).map
        (f.stalkMap ((f.fiberι s).base q')).hom := by
  subst hqq'; exact h

theorem kwFF15_ker_hom_comp_of_isIso {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C)
    [IsIso g] : RingHom.ker (f ≫ g).hom = RingHom.ker f.hom := by
  rw [CommRingCat.hom_comp]
  exact RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso g).1

theorem kwFF15_ker_hom_comp_comap {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) :
    RingHom.ker (f ≫ g).hom = (RingHom.ker g.hom).comap f.hom := by
  rw [CommRingCat.hom_comp, ← RingHom.comap_ker]

theorem kwFF15_comap_map_of_isIso {A B : CommRingCat.{0}} (f : A ⟶ B) [IsIso f]
    (I : Ideal A) : (I.map f.hom).comap f.hom = I :=
  Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso f)

theorem kwFF15_ker_stalkMap_comp_strip {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) [IsIso (f.stalkMap x)] :
    RingHom.ker ((f ≫ g).stalkMap x).hom = RingHom.ker (g.stalkMap (f x)).hom := by
  rw [Scheme.Hom.stalkMap_comp]
  exact RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso (f.stalkMap x)).1

theorem kwFF15_ker_stalkMap_comp_peel {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) :
    RingHom.ker ((f ≫ g).stalkMap x).hom =
      (RingHom.ker (f.stalkMap x).hom).comap (g.stalkMap (f x)).hom := by
  rw [Scheme.Hom.stalkMap_comp]
  exact (RingHom.comap_ker (f.stalkMap x).hom (g.stalkMap (f x)).hom).symm

theorem kwFF15_kerEq_of_openImmersion {S X Z : Scheme.{0}} (f : X ⟶ S) (m : Z ⟶ X)
    [IsOpenImmersion m] (s : S) (q : f.fiber s)
    (hq : (f.fiberι s) q ∈ Set.range m)
    (hall : ∀ w : (m ≫ f).fiber s,
      RingHom.ker (((m ≫ f).fiberι s).stalkMap w).hom =
        (IsLocalRing.maximalIdeal
          (S.presheaf.stalk ((m ≫ f) (((m ≫ f).fiberι s) w)))).map
          ((m ≫ f).stalkMap (((m ≫ f).fiberι s) w)).hom) :
    RingHom.ker ((f.fiberι s).stalkMap q).hom =
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f ((f.fiberι s) q)))).map
        (f.stalkMap ((f.fiberι s) q)).hom := by
  haveI : IsOpenImmersion (pullback.snd m (f.fiberι s)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  haveI : IsOpenImmersion
      (pullbackRightPullbackFstIso f (S.fromSpecResidueField s) m).hom :=
    inferInstance

  obtain ⟨w', hw'⟩ : q ∈ Set.range (pullback.snd m (f.fiberι s)) := by
    rw [Scheme.Pullback.range_snd]; exact hq
  subst hw'
  haveI : IsIso ((pullbackRightPullbackFstIso f (S.fromSpecResidueField s)
      m).hom.stalkMap w') :=
    inferInstance

  have hcomm : pullback.snd m (f.fiberι s) ≫ f.fiberι s =
      (pullbackRightPullbackFstIso f (S.fromSpecResidueField s) m).hom ≫
        ((m ≫ f).fiberι s ≫ m) :=
    (Iso.inv_comp_eq _).mp
      (pullbackRightPullbackFstIso_inv_snd_fst f (S.fromSpecResidueField s) m)

  have hpt : (f.fiberι s) ((pullback.snd m (f.fiberι s)) w') =
      m (((m ≫ f).fiberι s)
        ((pullbackRightPullbackFstIso f (S.fromSpecResidueField s) m).hom w')) := by
    have h1 := congrArg (· w') hcomm
    simp only [Scheme.Hom.comp_apply] at h1; exact h1

  have hker := congrArg (fun φ => RingHom.ker (CommRingCat.Hom.hom φ))
    (Scheme.Hom.stalkMap_congr_hom _ _ hcomm w')
  dsimp only at hker

  rw [kwFF15_ker_stalkMap_comp_strip (pullback.snd m (f.fiberι s)) (f.fiberι s) w',
    kwFF15_ker_hom_comp_comap] at hker

  have hinner : RingHom.ker (((pullbackRightPullbackFstIso f (S.fromSpecResidueField s)
        m).hom ≫ ((m ≫ f).fiberι s ≫ m)).stalkMap w').hom =
      ((IsLocalRing.maximalIdeal
          (S.presheaf.stalk (f ((f.fiberι s) ((pullback.snd m (f.fiberι s)) w'))))).map
        (f.stalkMap ((f.fiberι s) ((pullback.snd m (f.fiberι s)) w'))).hom).map
        (X.presheaf.stalkCongr (.of_eq hpt)).hom.hom := by
    rw [kwFF15_ker_stalkMap_comp_strip
        (pullbackRightPullbackFstIso f (S.fromSpecResidueField s) m).hom
        ((m ≫ f).fiberι s ≫ m) w']
    rw [kwFF15_ker_stalkMap_comp_peel]

    erw [hall ((pullbackRightPullbackFstIso f (S.fromSpecResidueField s) m).hom w')]
    rw [Scheme.Hom.stalkMap_comp]
    erw [← Ideal.map_map, kwFF15_comap_map_of_isIso (m.stalkMap _),
      ← kwFF14_map_stalkMap_congr_point f _ _ hpt]

  exact hker.trans ((congrArg _ hinner).trans
    (kwFF15_comap_map_of_isIso (X.presheaf.stalkCongr (.of_eq hpt)).hom _))

theorem kwFF15_ker_of_affine (hAff : KwFF15FiberιStalkMapKerAffine) :
    KwFF14FiberιStalkMapKer := by
  intro R _ X f s q

  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := (f.fiberι s).base q) (U := ⊤) trivial
  have eVU : V ≤ f ⁻¹ᵁ ⊤ := by simp
  letI : Algebra R ↑Γ(X, V) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ V eVU).hom.toAlgebra
  have halg : algebraMap R ↑Γ(X, V) =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ V eVU).hom := rfl

  have hm : Spec.map (CommRingCat.ofHom (algebraMap R ↑Γ(X, V))) = hV.fromSpec ≫ f := by
    rw [halg, CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.isoSpec_Spec_inv,
      ← IsAffineOpen.fromSpec_top,
      IsAffineOpen.SpecMap_appLE_fromSpec f
        (isAffineOpen_top (Spec (CommRingCat.of R))) hV eVU]

  have hq : (f.fiberι s) q ∈ Set.range hV.fromSpec :=
    ⟨hV.primeIdealOf ⟨(f.fiberι s) q, hxV⟩,
      hV.fromSpec_primeIdealOf ⟨(f.fiberι s) q, hxV⟩⟩

  refine kwFF15_kerEq_of_openImmersion f hV.fromSpec s q hq ?_

  intro w
  exact kwFF15_kerEq_of_congr_hom (hV.fromSpec ≫ f)
    (Spec.map (CommRingCat.ofHom (algebraMap R ↑Γ(X, V)))) hm.symm s w
    (fun w' => hAff R ↑Γ(X, V) s w')

theorem kwFF16_specStalkMap_toStalk {R S : Type} [CommRing R] [CommRing S]
    (φ : R →+* S) (p : Spec (CommRingCat.of S)) :
    StructureSheaf.toStalk R ((Spec.map (CommRingCat.ofHom φ)).base p) ≫
        (Spec.map (CommRingCat.ofHom φ)).stalkMap p =
      CommRingCat.ofHom φ ≫ StructureSheaf.toStalk S p :=
  stalkMap_toStalk (CommRingCat.ofHom φ) p

theorem kwFF16_wireIdeal_eq_pBq {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (x : Spec (CommRingCat.of S)) :
    (IsLocalRing.maximalIdeal (↑((Spec (CommRingCat.of R)).presheaf.stalk
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))).base x)))).map
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap x).hom =
    (((Spec.map (CommRingCat.ofHom (algebraMap R S))).base x).asIdeal.map (algebraMap R S)).map
      (StructureSheaf.toStalk S x).hom := by
  letI : Algebra R
      (↑((Spec (CommRingCat.of R)).presheaf.stalk
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))).base x))) :=
    (StructureSheaf.toStalk R ((Spec.map (CommRingCat.ofHom (algebraMap R S))).base x)).hom.toAlgebra
  letI : Algebra S (↑((Spec (CommRingCat.of S)).presheaf.stalk x)) :=
    (StructureSheaf.toStalk S x).hom.toAlgebra
  haveI : IsLocalization.AtPrime
      (↑((Spec (CommRingCat.of R)).presheaf.stalk
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))).base x)))
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).base x).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).base x)
  exact kmfloorsGlue_maximalIdeal_map_eq (B := S)
    ((Spec.map (CommRingCat.ofHom (algebraMap R S))).base x).asIdeal
    (↑((Spec (CommRingCat.of S)).presheaf.stalk x))
    (↑((Spec (CommRingCat.of R)).presheaf.stalk
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).base x)))
    ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap x).hom
    (congrArg CommRingCat.Hom.hom (kwFF16_specStalkMap_toStalk (algebraMap R S) x))

theorem kwFF16_ker_specIncludeRight_stalkMap {R S : Type} [CommRing R] [CommRing S]
    [Algebra R S] (s : PrimeSpectrum R) (Q : Spec (CommRingCat.of (s.asIdeal.Fiber S)))
    [hLO : ((Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight
        (R := R) (A := s.asIdeal.ResidueField) (B := S))))).base Q).asIdeal.LiesOver
      s.asIdeal] :
    RingHom.ker ((Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight
          (R := R) (A := s.asIdeal.ResidueField) (B := S))))).stalkMap Q).hom =
      (s.asIdeal.map (algebraMap R S)).map
        (StructureSheaf.toStalk S ((Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight
            (R := R) (A := s.asIdeal.ResidueField) (B := S))))).base Q)).hom := by

  let g := Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
    (Algebra.TensorProduct.includeRight
      (R := R) (A := s.asIdeal.ResidueField) (B := S))))
  let q : Ideal S := (g.base Q).asIdeal
  haveI : q.IsPrime := (g.base Q).isPrime
  let Bq := ↑((Spec (CommRingCat.of S)).presheaf.stalk (g.base Q))
  let Fq := ↑((Spec (CommRingCat.of (s.asIdeal.Fiber S))).presheaf.stalk Q)

  letI : Algebra S Bq := (StructureSheaf.toStalk S (g.base Q)).hom.toAlgebra
  letI : Algebra (s.asIdeal.Fiber S) Fq :=
    (StructureSheaf.toStalk (s.asIdeal.Fiber S) Q).hom.toAlgebra
  haveI : IsLocalization.AtPrime Bq q := StructureSheaf.IsLocalization.to_stalk S (g.base Q)
  haveI : IsLocalization.AtPrime Fq Q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (s.asIdeal.Fiber S) Q

  let pBq : Ideal Bq := (s.asIdeal.map (algebraMap R S)).map (algebraMap S Bq)
  letI : Algebra (s.asIdeal.Fiber S) (Bq ⧸ pBq) :=
    (kmfloorsGlue_fiberEval s.asIdeal q Bq).toAlgebra

  have hQq : Q.asIdeal.comap (Algebra.TensorProduct.includeRight
      (R := R) (A := s.asIdeal.ResidueField) (B := S)).toRingHom = q := by
    rw [← PrimeSpectrum.comap_asIdeal]; rfl
  haveI : IsLocalization Q.asIdeal.primeCompl (Bq ⧸ pBq) :=
    kmfloorsGlue_isLocalization_fiberEval s.asIdeal q Q.asIdeal Bq hQq

  let e : Fq ≃ₐ[s.asIdeal.Fiber S] Bq ⧸ pBq :=
    IsLocalization.algEquiv Q.asIdeal.primeCompl Fq (Bq ⧸ pBq)

  have hkey : e.toAlgHom.toRingHom.comp (g.stalkMap Q).hom = Ideal.Quotient.mk pBq := by
    refine IsLocalization.ringHom_ext (M := q.primeCompl) (R := S) (S := Bq) ?_

    rw [RingHom.comp_assoc]
    have hCC30 : (g.stalkMap Q).hom.comp (algebraMap S Bq) =
        (algebraMap (s.asIdeal.Fiber S) Fq).comp
          (Algebra.TensorProduct.includeRight
            (R := R) (A := s.asIdeal.ResidueField) (B := S)).toRingHom :=
      congrArg CommRingCat.Hom.hom (kwFF16_specStalkMap_toStalk
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight
          (R := R) (A := s.asIdeal.ResidueField) (B := S))) Q)
    rw [hCC30, ← RingHom.comp_assoc]

    have hecomm : e.toAlgHom.toRingHom.comp (algebraMap (s.asIdeal.Fiber S) Fq) =
        kmfloorsGlue_fiberEval s.asIdeal q Bq :=
      RingHom.ext fun y => e.commutes y
    rw [hecomm]
    ext b
    exact kmfloorsGlue_fiberEval_one_tmul s.asIdeal q Bq b

  show RingHom.ker (g.stalkMap Q).hom = pBq
  calc RingHom.ker (g.stalkMap Q).hom
      = RingHom.ker (e.toAlgHom.toRingHom.comp (g.stalkMap Q).hom) :=
        (RingHom.ker_comp_of_injective _
          (EquivLike.injective e.toRingEquiv)).symm
    _ = RingHom.ker (Ideal.Quotient.mk pBq) := by rw [hkey]
    _ = pBq := Ideal.mk_ker

theorem kwFF16_kerEq_congr_ι {S X W : Scheme.{0}} (f : X ⟶ S) (ι ι' : W ⟶ X)
    (hι : ι = ι') (q : W)
    (h : RingHom.ker (ι'.stalkMap q).hom =
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f.base (ι'.base q)))).map
        (f.stalkMap (ι'.base q)).hom) :
    RingHom.ker (ι.stalkMap q).hom =
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f.base (ι.base q)))).map
        (f.stalkMap (ι.base q)).hom := by
  subst hι; exact h

theorem kwFF16_affineKer_discharge : KwFF15FiberιStalkMapKerAffine := by
  intro R S _ _ _ s q

  refine kwFF16_kerEq_congr_ι (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι s)
    ((kmf2_fiberSpecTensorIso R S s).hom ≫
      Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight
          (R := R) (A := s.asIdeal.ResidueField) (B := S)))))
    (kmf2_fiberSpecTensorIso_hom_includeRight R S s).symm q ?_

  rw [kwFF15_ker_stalkMap_comp_strip (kmf2_fiberSpecTensorIso R S s).hom
    (Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight
        (R := R) (A := s.asIdeal.ResidueField) (B := S))))) q]

  have hfx : (Spec.map (CommRingCat.ofHom (algebraMap R S))).base
      (((kmf2_fiberSpecTensorIso R S s).hom ≫
        Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight
            (R := R) (A := s.asIdeal.ResidueField) (B := S))))).base q) = s := by
    have hmem : ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι s) q ∈
        Set.range ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι s) := ⟨q, rfl⟩
    rw [Scheme.Hom.range_fiberι] at hmem
    exact kmf2_fiberSpecTensorIso_hom_includeRight R S s ▸ hmem

  erw [kwFF16_wireIdeal_eq_pBq (R := R) (S := S)
    (((kmf2_fiberSpecTensorIso R S s).hom ≫
      Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight
          (R := R) (A := s.asIdeal.ResidueField) (B := S))))).base q)]
  rw [congrArg PrimeSpectrum.asIdeal hfx]

  haveI : ((Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight
        (R := R) (A := s.asIdeal.ResidueField) (B := S))))).base
      ((kmf2_fiberSpecTensorIso R S s).hom q)).asIdeal.LiesOver s.asIdeal :=
    ⟨(congrArg PrimeSpectrum.asIdeal hfx).symm⟩
  exact kwFF16_ker_specIncludeRight_stalkMap (R := R) (S := S) s
    ((kmf2_fiberSpecTensorIso R S s).hom q)

end KERPort

end

open CategoryTheory AlgebraicGeometry KERPort in

theorem solution
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (s : Spec (CommRingCat.of R)) (q : f.fiber s) :
    RingHom.ker ((f.fiberι s).stalkMap q).hom =
      (IsLocalRing.maximalIdeal
        ((Spec (CommRingCat.of R)).presheaf.stalk (f.base ((f.fiberι s).base q)))).map
        (f.stalkMap ((f.fiberι s).base q)).hom := by
  exact (KERPort.kwFF15_ker_of_affine KERPort.kwFF16_affineKer_discharge) R f s q

end S_AlgebraicGeometry_ker_fiberIota_stalkMap_eq_maximalIdeal_map
end P2MW
export P2MW.S_AlgebraicGeometry_ker_fiberIota_stalkMap_eq_maximalIdeal_map (solution)
