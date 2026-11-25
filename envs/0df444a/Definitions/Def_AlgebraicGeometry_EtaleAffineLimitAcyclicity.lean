-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAffineLimitAcyclicity
-- name    : AlgebraicGeometry_EtaleAffineLimitAcyclicity
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T05:04:33.815787+00:00
-- url     : https://prove2.me/theorems/555afc0e-74e6-43f9-bcd8-b0ef4f8cb7d5
-- title:
--   Čech acyclicity of the affine limit of injective étale sheaves
-- statement:
--   A compatible system of stagewise injective sheaves gives an acyclic sheaf on the affine inverse limit. The proof descends affine étale covers to stages where injectivity makes the Čech cochains exact.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitSheaf
import Definitions.Def_AlgebraicGeometry_EtaleModeledCech
import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.VanKampen

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleModeledSections


namespace PhilipponEtaleModeledCoverArrow

universe u

private def baseChangeCofanIsColimit {X Z : Scheme.{u}} (r : Z ⟶ X) {β : Type u} [Finite β]
    (W : β → X.Etale) (A : X.Etale) (κ : ∀ l, W l ⟶ A)
    (h : IsColimit (Cofan.mk A.left (fun l => (κ l).left))) :
    IsColimit (Cofan.mk ((reversedBaseChange r).obj A).left
      (fun l => ((reversedBaseChange r).map (κ l)).left)) := by
  let K := reversedBaseChange r
  let d : Cofan (fun l => (K.obj (W l)).left) :=
    Cofan.mk (K.obj A).left (fun l => (K.map (κ l)).left)
  let hU := FinitaryPreExtensive.isUniversal_finiteCoproducts h
  refine (hU.nonempty_isColimit_of_isPullback_left (fun l => (W l).hom) A.hom r
    (fun l => pullback.fst r (W l).hom) (fun l => pullback.snd r (W l).hom)
    (fun l => IsPullback.of_hasPullback r (W l).hom) (IsPullback.of_hasPullback r A.hom)
    d (Iso.refl _) (fun l => MorphismProperty.Over.w (κ l)) ?_ ?_).some
  · intro l
    change (K.map (κ l)).left ≫ 𝟙 _ ≫ pullback.fst r A.hom = pullback.fst r (W l).hom
    rw [Category.id_comp]
    exact pullback.lift_fst ..
  · intro l
    change (K.map (κ l)).left ≫ 𝟙 _ ≫ pullback.snd r A.hom =
      pullback.snd r (W l).hom ≫ (κ l).left
    rw [Category.id_comp]
    exact pullback.lift_snd ..

/-- Combine a finite affine covering family refining one arrow into a
single affine cover, by taking its finite disjoint union. -/
theorem exists_covering_arrow_of_family {X Z : Scheme.{u}} (r : Z ⟶ X)
    {U B : Z.Etale} (a : B ⟶ U) (T : X.Etale)
    (e : U ≅ (reversedBaseChange r).obj T)
    {β : Type u} [Fintype β] (W : β → X.Etale) (q : ∀ l, W l ⟶ T)
    (hW : ∀ l, IsAffine (W l).left) (hstage : Sieve.ofArrows W q ∈ X.smallEtaleTopology T)
    (hmem : ∀ l, Sieve.generate (Presieve.singleton a) ((reversedBaseChange r).map (q l) ≫ e.inv))
    (hcover : Sieve.ofArrows _ (fun l => (reversedBaseChange r).map (q l) ≫ e.inv) ∈
      Z.smallEtaleTopology U) :
    ∃ (V : X.Etale) (b : V ⟶ T) (g : (reversedBaseChange r).obj V ⟶ B),
      IsAffine V.left ∧ Function.Surjective b.left ∧
      Sieve.generate (Presieve.singleton ((reversedBaseChange r).map b)) ∈
        Z.smallEtaleTopology ((reversedBaseChange r).obj T) ∧
      g ≫ a = (reversedBaseChange r).map b ≫ e.inv := by
  classical
  let K := reversedBaseChange r
  let W₀ := fun l => (W l).left
  let (l : β) : IsAffine (W₀ l) := hW l
  let t : (∐ W₀) ⟶ X := Sigma.desc fun l => (W l).hom
  let : Etale t := by
    apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (sigmaOpenCover W₀)).mpr
    intro l
    change Etale (Sigma.ι W₀ l ≫ t)
    rw [Sigma.ι_desc]
    exact (W l).prop
  let V : X.Etale := Scheme.Etale.mk t
  let v : (∐ W₀) ⟶ T.left := Sigma.desc fun l => (q l).left
  let κ (l : β) : W l ⟶ V := MorphismProperty.Over.homMk (Sigma.ι W₀ l) (Sigma.ι_desc _ _) trivial
  let b : V ⟶ T := MorphismProperty.Over.homMk v (by
    apply Sigma.hom_ext
    intro l
    change Sigma.ι W₀ l ≫ v ≫ T.hom = Sigma.ι W₀ l ≫ t
    rw [← Category.assoc, Sigma.ι_desc, Sigma.ι_desc]
    exact MorphismProperty.Over.w (q l)) trivial
  have hb (l : β) : κ l ≫ b = q l := MorphismProperty.Over.Hom.ext (Sigma.ι_desc _ _)
  have hKb (l : β) : K.map (κ l) ≫ K.map b = K.map (q l) := by rw [← K.map_comp, hb]
  have hfact (l : β) : ∃ k : K.obj (W l) ⟶ B, k ≫ a = K.map (q l) ≫ e.inv := by
    obtain ⟨Z, d, z, hzs, hz⟩ := hmem l
    cases hzs
    exact ⟨d, hz⟩
  choose k hk using hfact
  let hC := baseChangeCofanIsColimit r W V κ (coproductIsCoproduct W₀)
  let d : Cofan (fun l => (K.obj (W l)).left) := Cofan.mk B.left (fun l => (k l).left)
  let g₀ := hC.desc d
  have hg (l : β) : (K.map (κ l)).left ≫ g₀ = (k l).left := hC.fac d ⟨l⟩
  let g : K.obj V ⟶ B := MorphismProperty.Over.homMk g₀ (by
    apply Cofan.IsColimit.hom_ext hC
    intro l
    change (K.map (κ l)).left ≫ g₀ ≫ B.hom = (K.map (κ l)).left ≫ (K.obj V).hom
    rw [← Category.assoc, hg, MorphismProperty.Over.w, MorphismProperty.Over.w]) trivial
  refine ⟨V, b, g, inferInstanceAs (IsAffine (∐ W₀)), ?_, ?_, ?_⟩
  · intro x
    have hx := (Scheme.ofArrows_mem_smallEtaleTopology_iff q).mp hstage
    obtain ⟨l, y, hy⟩ := Set.mem_iUnion.mp (hx.symm ▸ Set.mem_univ x)
    exact ⟨Sigma.ι W₀ l y, (congrArg (fun m : W₀ l ⟶ T.left => m y) (Sigma.ι_desc _ _)).trans hy⟩
  · apply singleton_cover_of_surjective
    intro x
    have hx := (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mp hcover
    obtain ⟨l, y, hy⟩ := Set.mem_iUnion.mp (hx.symm ▸ Set.mem_univ (e.inv.left x))
    have h' : (K.map (q l)).left y = x := by
      let A := Scheme.Etale.forget Z ⋙ Over.forget Z
      let e' := A.mapIso e
      exact e'.inv.homeomorph.injective hy
    exact ⟨(K.map (κ l)).left y,
      (congrArg (fun m : K.obj (W l) ⟶ K.obj T => m.left y) (hKb l)).trans h'⟩
  · apply MorphismProperty.Over.Hom.ext
    apply Cofan.IsColimit.hom_ext hC
    intro l
    change (K.map (κ l)).left ≫ g₀ ≫ a.left =
      (K.map (κ l)).left ≫ (K.map b).left ≫ e.inv.left
    rw [← Category.assoc, hg, ← Category.assoc]
    exact (congrArg (fun m => m.left) (hk l)).trans
      (congrArg (fun m : K.obj (W l) ⟶ K.obj T => m.left ≫ e.inv.left) (hKb l).symm)

end PhilipponEtaleModeledCoverArrow

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCech
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleBaseChangeComparison (map_isPullback)
open PhilipponEtaleDirectImageSystem (chart directImages)
open PhilipponEtaleLimitAffinePresheaf (affineCharts)
open PhilipponEtaleAffineSectionColimit (stageSections)
open PhilipponEtaleStageSectionSheaf (evalIso)
open PhilipponEtaleModeledCoverArrow (singleton_cover_of_surjective)
open PhilipponEtaleModeledSections (reversedBaseChange reversedBaseChangeIso)
open PhilipponEtaleLimitSheaf (limitSheaf affineOverlap sectionsIso chartComparison)


namespace PhilipponEtaleLimitCech

universe u

instance (X : Scheme.{u}) : (affineCharts X).IsClosedUnderIsomorphisms where
  of_iso e h := by
    let K := Scheme.Etale.forget X ⋙ Over.forget X
    let e' := K.mapIso e
    let : IsAffine (K.obj _) := h
    exact IsAffine.of_isIso e'.inv

/-- The Čech nerve of a map between two affine charts stays affine. -/
theorem affineCechNerve {X : Scheme.{u}} {U V : X.Etale} (a : V ⟶ U)
    (hU : IsAffine U.left) (hV : IsAffine V.left) (m : SimplexCategoryᵒᵖ) :
    IsAffine ((Arrow.mk a).cechNerve.obj m).left := by
  apply PhilipponCech.widePullback_prop_of_pullbacks (affineCharts X) a _ hU hV (m.unop.len + 1)
  intro A B T f g hA hB hT
  let : IsAffine A.left := hA
  let : IsAffine B.left := hB
  let : IsAffine T.left := hT
  exact affineOverlap f g

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} (F : System (directImages D))
  {i : I} {U V : (D.obj i).Etale} (a : V ⟶ U)

private theorem stageCech_exact [Surjective a.left]
    (j : (Over i)ᵒᵖ) [Injective (F.obj j.unop.left)] (n : ℕ) :
    (cofaceShortComplex (cechSections a (stageSections F i) ⋙ (evaluation _ _).obj j) n).Exact := by
  let X := D.obj j.unop.left
  let r := D.map j.unop.hom
  let B := chart D j.unop.hom
  let F' := F.obj j.unop.left
  let : PreservesFiniteLimits B := inferInstanceAs
    (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ r))
  let e := cechNerveMapIso B a
  let e₂ : (Arrow.mk a).cechNerve.rightOp ⋙ B.op ≅ (Arrow.mk (B.map a)).cechNerve.rightOp :=
    (Functor.leftOpRightOpEquiv SimplexCategory X.Etale).functor.mapIso (Iso.op e.symm)
  let eqSections : cechSections a (stageSections F i) ⋙ (evaluation _ _).obj j ≅
      cechSections (B.map a) F'.obj :=
    Functor.isoWhiskerLeft (Arrow.mk a).cechNerve.rightOp (evalIso F j.unop) ≪≫
      Functor.isoWhiskerRight e₂ F'.obj
  let hsurj : Surjective (B.map a).left :=
    MorphismProperty.of_isPullback (P := @Surjective) (map_isPullback r a) inferInstance
  have hcover := singleton_cover_of_surjective (B.map a) hsurj.surj
  have h := (cofaceShortComplex_cech_exact_iff (B.map a) X.smallEtaleTopology F' n).mpr
    (sectionCechD_exact_of_injective (B.map a) X.smallEtaleTopology hcover F' n)
  exact ShortComplex.exact_of_iso (cofaceShortComplexIso eqSections n).symm h

variable [IsCofiltered I] [∀ j, IsAffine (D.obj j)] (c : Cone D) (hc : IsLimit c)

/-- A compatible system of injective sheaves gives exact positive-degree
Čech cochains for every affine singleton cover pulled back from a stage. -/
theorem cech_exact [∀ j, Injective (F.obj j)] [Surjective a.left]
    (hU : IsAffine U.left) (hV : IsAffine V.left) (n : ℕ) :
    Function.Exact
      (sectionCechD ((reversedBaseChange (c.π.app i)).map a) c.pt.smallEtaleTopology
        (limitSheaf c hc F) n)
      (sectionCechD ((reversedBaseChange (c.π.app i)).map a) c.pt.smallEtaleTopology
        (limitSheaf c hc F) (n + 1)) := by
  let N := (Arrow.mk a).cechNerve
  let M := affineCharts (D.obj i)
  let N' := M.lift N (affineCechNerve a hU hV)
  let r := c.π.app i
  let K := reversedBaseChange r
  let P := (limitSheaf c hc F).obj
  let : PreservesFiniteLimits K :=
    preservesFiniteLimits_of_natIso (reversedBaseChangeIso r).symm
  let e₁ : M.ι.op ⋙ (stageSections F i ⋙ colim) ≅ (M.ι ⋙ K).op ⋙ P :=
    sectionsIso c hc F i ≪≫
      Functor.isoWhiskerLeft M.ι.op
        (Functor.isoWhiskerRight (NatIso.op (chartComparison c i)) P)
  let e := cechNerveMapIso K a
  let e₂ : N.rightOp ⋙ K.op ≅ (Arrow.mk (K.map a)).cechNerve.rightOp :=
    (Functor.leftOpRightOpEquiv SimplexCategory c.pt.Etale).functor.mapIso (Iso.op e.symm)
  let isoSections : cechSections a (stageSections F i) ⋙ colim ≅ cechSections (K.map a) P :=
    Functor.isoWhiskerLeft N'.rightOp e₁ ≪≫ Functor.isoWhiskerRight e₂ P
  have hx := cofaceShortComplex_exact_colim (cechSections a (stageSections F i)) n
    (fun j => stageCech_exact F a j n)
  apply (cofaceShortComplex_cech_exact_iff (K.map a) c.pt.smallEtaleTopology (limitSheaf c hc F) n).mp
  exact ShortComplex.exact_of_iso (cofaceShortComplexIso isoSections n) hx

end PhilipponEtaleLimitCech

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open PhilipponCech
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleLimitAffinePresheaf (exists_affineModel)
open PhilipponEtaleLimitSheaf (limitSheaf chartComparison)
open PhilipponEtaleLimitCech (cech_exact affineCechNerve)
open PhilipponEtaleModeledSections (reversedBaseChange reversedBaseChangeIso)
open PhilipponEtaleModeledCoverArrow (singleton_cover_of_surjective exists_covering_arrow_of_family)


namespace PhilipponEtaleLimitAcyclicity

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ j, IsAffine (D.obj j)] (c : Cone D) (hc : IsLimit c) (F : System (directImages D))
  [∀ j, Injective (F.obj j)]

include hc in
/-- The limit of stagewise injective étale sheaves is acyclic on all
affine étale charts pulled back from stages. -/
theorem acyclic_on_modeled (q : ℕ) :
    ∀ (i : I) (U : (D.obj i).Etale), IsAffine U.left →
      Subsingleton ((limitSheaf c hc F).H' (q + 1) ((reversedBaseChange (c.π.app i)).obj U)) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro i U hU
      let X := c.pt
      let J := X.smallEtaleTopology
      let P := limitSheaf c hc F
      let A := (reversedBaseChange (c.π.app i)).obj U
      let Cq := P.cohomologyPresheaf (q + 1)
      let : IsAffine U.left := hU
      let : IsAffine X := Scheme.isAffine_of_isLimit c hc
      let : IsAffine A.left :=
        @Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine X U.left (D.obj i)
          (c.π.app i) U.hom ‹_› ‹_› inferInstance
      let : CompactSpace A.left := inferInstance
      refine subsingleton_of_forall_eq 0 (fun x => ?_)
      obtain ⟨B, a, hB, ha, hx⟩ := Scheme.exists_surjective_affine_arrow_killing_class A P q x
      obtain ⟨j, T, e, β, hβ, W, s, hT, hW, hstage, hmem, hcover⟩ :=
        PhilipponEtaleAffineCoverModel.exists_cover_model c ⟨i, U⟩ hc
          (Sieve.generate (Presieve.singleton a)) (singleton_cover_of_surjective a ha)
      let : Fintype β := hβ
      obtain ⟨V, b, g, hV, hb, hcov, hfac⟩ :=
        exists_covering_arrow_of_family (c.π.app j) a T e W s hW hstage hmem hcover
      let : Surjective b.left := ⟨hb⟩
      let K := reversedBaseChange (c.π.app j)
      let x' := Cq.map e.inv.op x
      have hx' : Cq.map (K.map b).op x' = 0 := by
        change Cq.map (K.map b).op (Cq.map e.inv.op x) = 0
        rw [← ConcreteCategory.comp_apply, ← Cq.map_comp, ← op_comp, ← hfac,
          op_comp, Cq.map_comp, ConcreteCategory.comp_apply, hx, map_zero]
      have hz : x' = 0 := by
        apply class_eq_zero_of_cech_exact (K.map b) J hcov P q ?_
          (cech_exact F b c hc hT hV) x' hx'
        intro m k hk hle
        cases k with
        | zero => exact (Nat.not_lt_zero _ hk).elim
        | succ k =>
          let Z := (Arrow.mk b).cechNerve.obj (op ⦋m⦌)
          let L := P.cohomologyPresheaf (k + 1)
          let : Subsingleton ↥(L.obj (op (K.obj Z))) :=
            ih k (Nat.lt_of_succ_le hle) j Z (affineCechNerve b hT hV (op ⦋m⦌))
          let : PreservesFiniteLimits K :=
            preservesFiniteLimits_of_natIso (reversedBaseChangeIso (c.π.app j)).symm
          let e' : K.obj Z ≅ (Arrow.mk (K.map b)).cechNerve.obj (op ⦋m⦌) :=
            (cechNerveMapIso K b).app (op ⦋m⦌)
          exact (L.mapIso e'.op).addCommGroupIsoToAddEquiv.injective.subsingleton
      let d : Cq.obj (op A) ≅ Cq.obj (op (K.obj T)) := Cq.mapIso e.symm.op
      have he : x' = Cq.map e.inv.op 0 := hz.trans (map_zero _).symm
      exact d.addCommGroupIsoToAddEquiv.injective he

include hc in
/-- Stagewise injective sheaves give a limit sheaf acyclic on every
affine étale chart of the limit scheme. -/
theorem acyclic_on_affine (q : ℕ) (U : c.pt.Etale) [IsAffine U.left] :
    Subsingleton ((limitSheaf c hc F).H' (q + 1) U) := by
  let M := (exists_affineModel c hc U).some
  let z := M.comparison ≪≫ ((chartComparison c M.chart.index).app M.chart.etale).symm
  let P := limitSheaf c hc F
  let : Subsingleton (P.H' (q + 1) ((reversedBaseChange (c.π.app M.chart.index)).obj M.chart.etale)) :=
    acyclic_on_modeled c hc F q M.chart.index M.chart.etale M.affine
  exact ((P.cohomologyPresheaf (q + 1)).mapIso z.symm.op).addCommGroupIsoToAddEquiv.injective.subsingleton

include hc in
/-- The limit of stagewise injective étale sheaves on affine schemes is
acyclic for global sections. -/
theorem acyclic (q : ℕ) : Subsingleton ((limitSheaf c hc F).H (q + 1)) := by
  let T := Scheme.Etale.mk (𝟙 c.pt)
  let : IsAffine T.left := Scheme.isAffine_of_isLimit c hc
  let P := limitSheaf c hc F
  let : Subsingleton (P.H' (q + 1) T) := acyclic_on_affine c hc F q T
  let hTerminal : IsTerminal T := IsTerminal.isTerminalOfObj (Scheme.Etale.forget c.pt) _ Over.mkIdTerminal
  exact (PhilipponSheafCohomology.terminalComparison c.pt.smallEtaleTopology hTerminal P (q + 1)).injective.subsingleton

end PhilipponEtaleLimitAcyclicity

end

end


