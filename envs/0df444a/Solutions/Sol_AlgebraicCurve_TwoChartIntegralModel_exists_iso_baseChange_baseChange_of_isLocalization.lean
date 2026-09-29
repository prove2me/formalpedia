-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_iso_baseChange_baseChange_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d239581b-f0f1-5b5a-a1e9-8548c0007172

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isLocalization_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isPullback_chartFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isPullback_chartInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_chartIncl_comp_chartBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_baseChange_baseChange_of_isLocalization

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel TwoChartIntegralModel.ιFin TwoChartIntegralModel.ιInf TwoChartIntegralModel.baseChange TwoChartIntegralModel.baseChangeι TwoChartIntegralModel.baseChangeToBase TwoChartIntegralModel.chartBaseChange"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlg sFin_subset sInf_subset chartAlgFin chartAlgInf chartAlgMid jChartFin jInvChartInf coe_jChartFin coe_jInvChartInf inclFin inclInf isLocalization_away_inclFin isLocalization_away_inclInf XFin XInf XMid fFin fInf ιFin ιInf glue_condition toBase ιFin_toBase ιInf_toBase mem_range_ιFin_or_mem_range_ιInf baseChange baseChangeι baseChangeToBase chartBaseChange coe_chartBaseChange chartBaseChange_algebraMap ιFin_toBase_assoc ιInf_toBase_assoc isLocalization_chartAlg isPullback_chartFin isPullback_chartInf chartIncl_comp_chartBaseChange"
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

section Glue

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
variable (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]

theorem fFin_comp_Spec_chartBaseChange :
    fFin R' F j ≫ Spec.map (CommRingCat.ofHom (chartBaseChange R F R' {j})) =
      Spec.map (CommRingCat.ofHom (chartBaseChange R F R' {j, j⁻¹})) ≫ fFin R F j := by
  simp only [fFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [chartIncl_comp_chartBaseChange R F R' (sFin_subset F j)]

theorem fInf_comp_Spec_chartBaseChange :
    fInf R' F j ≫ Spec.map (CommRingCat.ofHom (chartBaseChange R F R' {j⁻¹})) =
      Spec.map (CommRingCat.ofHom (chartBaseChange R F R' {j, j⁻¹})) ≫ fInf R F j := by
  simp only [fInf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [chartIncl_comp_chartBaseChange R F R' (sInf_subset F j)]

noncomputable def overBase :
    AlgebraicCurve.TwoChartIntegralModel R' F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j :=
  pushout.desc (Spec.map (CommRingCat.ofHom (chartBaseChange R F R' {j})) ≫ ιFin R F j)
    (Spec.map (CommRingCat.ofHom (chartBaseChange R F R' {j⁻¹})) ≫ ιInf R F j) (by
      rw [← Category.assoc, fFin_comp_Spec_chartBaseChange, Category.assoc, glue_condition,
        ← Category.assoc, ← fInf_comp_Spec_chartBaseChange, Category.assoc])

@[reassoc (attr := simp)]
theorem ιFin_overBase : ιFin R' F j ≫ overBase R F j R' =
    Spec.map (CommRingCat.ofHom (chartBaseChange R F R' {j})) ≫ ιFin R F j :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem ιInf_overBase : ιInf R' F j ≫ overBase R F j R' =
    Spec.map (CommRingCat.ofHom (chartBaseChange R F R' {j⁻¹})) ≫ ιInf R F j :=
  pushout.inr_desc _ _ _

theorem Spec_chartBaseChange_comp_Spec_algebraMap (S : Set F) :
    Spec.map (CommRingCat.ofHom (chartBaseChange R F R' S)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (chartAlg R F S))) =
      Spec.map (CommRingCat.ofHom (algebraMap R' (chartAlg R' F S))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun r => chartBaseChange_algebraMap R F R' S r

@[reassoc]
theorem overBase_toBase : overBase R F j R' ≫ toBase R F j =
    toBase R' F j ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
  apply pushout.hom_ext
  · show ιFin R' F j ≫ _ = ιFin R' F j ≫ _
    rw [ιFin_overBase_assoc, ιFin_toBase, ιFin_toBase_assoc,
      Spec_chartBaseChange_comp_Spec_algebraMap]
  · show ιInf R' F j ≫ _ = ιInf R' F j ≫ _
    rw [ιInf_overBase_assoc, ιInf_toBase, ιInf_toBase_assoc,
      Spec_chartBaseChange_comp_Spec_algebraMap]

noncomputable def toPullback : AlgebraicCurve.TwoChartIntegralModel R' F j ⟶
    pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
  pullback.lift (overBase R F j R') (toBase R' F j) (overBase_toBase R F j R')

@[reassoc (attr := simp)]
theorem toPullback_fst : toPullback R F j R' ≫ pullback.fst _ _ = overBase R F j R' :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem toPullback_snd : toPullback R F j R' ≫ pullback.snd _ _ = toBase R' F j :=
  pullback.lift_snd _ _ _

variable (M : Submonoid R) [IsLocalization M R']

include M in

theorem isPullback_ιFin_toPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (chartBaseChange R F R' {j})))
      (ιFin R' F j ≫ toPullback R F j R') (ιFin R F j)
      (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback _ _)
  rw [Category.assoc, toPullback_snd, ιFin_toBase, ιFin_toBase]
  exact isPullback_chartFin R F j R' M

include M in
theorem isPullback_ιInf_toPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (chartBaseChange R F R' {j⁻¹})))
      (ιInf R' F j ≫ toPullback R F j R') (ιInf R F j)
      (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback _ _)
  rw [Category.assoc, toPullback_snd, ιInf_toBase, ιInf_toBase]
  exact isPullback_chartInf R F j R' M

include M in
theorem ιFin_toPullback_eq : ιFin R' F j ≫ toPullback R F j R' =
    (isPullback_ιFin_toPullback R F j R' M).isoPullback.hom ≫ pullback.snd _ _ :=
  ((isPullback_ιFin_toPullback R F j R' M).isoPullback_hom_snd).symm

include M in
theorem ιInf_toPullback_eq : ιInf R' F j ≫ toPullback R F j R' =
    (isPullback_ιInf_toPullback R F j R' M).isoPullback.hom ≫ pullback.snd _ _ :=
  ((isPullback_ιInf_toPullback R F j R' M).isoPullback_hom_snd).symm

include M in
theorem isOpenImmersion_ιFin_toPullback : IsOpenImmersion (ιFin R' F j ≫ toPullback R F j R') := by
  rw [ιFin_toPullback_eq R F j R' M]; infer_instance

include M in
theorem isOpenImmersion_ιInf_toPullback : IsOpenImmersion (ιInf R' F j ≫ toPullback R F j R') := by
  rw [ιInf_toPullback_eq R F j R' M]; infer_instance

theorem range_comp_of_surjective {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Function.Surjective f) : Set.range (f ≫ g) = Set.range g := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨f x, by rw [← Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨x, by rw [Scheme.Hom.comp_apply]⟩

include M in
theorem range_ιFin_toPullback : Set.range (ιFin R' F j ≫ toPullback R F j R') =
    (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ⁻¹'
      Set.range (ιFin R F j) := by
  rw [ιFin_toPullback_eq R F j R' M, range_comp_of_surjective _ _ (Scheme.Hom.surjective _),
    IsOpenImmersion.range_pullbackSnd]
  rfl

include M in
theorem range_ιInf_toPullback : Set.range (ιInf R' F j ≫ toPullback R F j R') =
    (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ⁻¹'
      Set.range (ιInf R F j) := by
  rw [ιInf_toPullback_eq R F j R' M, range_comp_of_surjective _ _ (Scheme.Hom.surjective _),
    IsOpenImmersion.range_pullbackSnd]
  rfl

include M in
theorem surjective_toPullback : Function.Surjective (toPullback R F j R') := by
  intro p
  rcases mem_range_ιFin_or_mem_range_ιInf R F j
      (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) p) with h | h
  · have hp : p ∈ Set.range (ιFin R' F j ≫ toPullback R F j R') := by
      rw [range_ιFin_toPullback R F j R' M]; exact h
    obtain ⟨a, rfl⟩ := hp
    exact ⟨ιFin R' F j a, by rw [← Scheme.Hom.comp_apply]⟩
  · have hp : p ∈ Set.range (ιInf R' F j ≫ toPullback R F j R') := by
      rw [range_ιInf_toPullback R F j R' M]; exact h
    obtain ⟨a, rfl⟩ := hp
    exact ⟨ιInf R' F j a, by rw [← Scheme.Hom.comp_apply]⟩

include M in
theorem injective_Spec_chartBaseChange (S : Set F) :
    Function.Injective (Spec.map (CommRingCat.ofHom (chartBaseChange R F R' S))) := by
  letI : Algebra (chartAlg R F S) (chartAlg R' F S) := (chartBaseChange R F R' S).toAlgebra
  haveI := isLocalization_chartAlg R F R' M S
  intro x y h
  simp only [Spec.map_apply, CommRingCat.hom_ofHom] at h
  exact PrimeSpectrum.localization_comap_injective (chartAlg R' F S)
    (M.map (algebraMap R (chartAlg R F S))) h

theorem range_fFin : Set.range (fFin R F j) =
    (PrimeSpectrum.basicOpen (jChartFin R F j) : Set (PrimeSpectrum (chartAlgFin R F j))) := by
  letI := (inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  have := PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jChartFin R F j)
  rw [RingHom.algebraMap_toAlgebra] at this
  rw [← this]
  rfl

theorem range_fInf : Set.range (fInf R F j) =
    (PrimeSpectrum.basicOpen (jInvChartInf R F j) : Set (PrimeSpectrum (chartAlgInf R F j))) := by
  letI := (inclInf R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R F j
  have := PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jInvChartInf R F j)
  rw [RingHom.algebraMap_toAlgebra] at this
  rw [← this]
  rfl

omit [Fact (j ≠ 0)] in
theorem chartBaseChange_jChartFin :
    chartBaseChange R F R' {j} (jChartFin R F j) = jChartFin R' F j :=
  Subtype.ext (by rw [coe_chartBaseChange, coe_jChartFin, coe_jChartFin])

omit [Fact (j ≠ 0)] in
theorem chartBaseChange_jInvChartInf :
    chartBaseChange R F R' {j⁻¹} (jInvChartInf R F j) = jInvChartInf R' F j :=
  Subtype.ext (by rw [coe_chartBaseChange, coe_jInvChartInf, coe_jInvChartInf])

theorem exists_fFin_eq_of_mem_range {a : XFin R' F j}
    (ha : Spec.map (CommRingCat.ofHom (chartBaseChange R F R' {j})) a ∈ Set.range (fFin R F j)) :
    ∃ z : XMid R' F j, fFin R' F j z = a := by
  rw [range_fFin, Spec.map_apply, CommRingCat.hom_ofHom] at ha
  have ha1 : PrimeSpectrum.comap (chartBaseChange R F R' {j}) a ∈
      (PrimeSpectrum.basicOpen (jChartFin R F j) : Set (PrimeSpectrum (chartAlgFin R F j))) := ha

  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    chartBaseChange_jChartFin] at ha1
  show a ∈ Set.range (fFin R' F j)
  rw [range_fFin]
  exact ha1

theorem exists_fInf_eq_of_mem_range {a : XInf R' F j}
    (ha : Spec.map (CommRingCat.ofHom (chartBaseChange R F R' {j⁻¹})) a ∈ Set.range (fInf R F j)) :
    ∃ z : XMid R' F j, fInf R' F j z = a := by
  rw [range_fInf, Spec.map_apply, CommRingCat.hom_ofHom] at ha
  have ha1 : PrimeSpectrum.comap (chartBaseChange R F R' {j⁻¹}) a ∈
      (PrimeSpectrum.basicOpen (jInvChartInf R F j) :
        Set (PrimeSpectrum (chartAlgInf R F j))) := ha
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    chartBaseChange_jInvChartInf] at ha1
  show a ∈ Set.range (fInf R' F j)
  rw [range_fInf]
  exact ha1

theorem exists_of_ιFin_eq_ιInf {a : XFin R F j} {b : XInf R F j}
    (h : ιFin R F j a = ιInf R F j b) : ∃ z : XMid R F j, fFin R F j z = a ∧ fInf R F j z = b := by
  have h' : colimit.ι (span (fFin R F j) (fInf R F j)) WalkingSpan.left a =
      colimit.ι (span (fFin R F j) (fInf R F j)) WalkingSpan.right b := h
  obtain ⟨k, fi, fj, z, hz1, hz2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff _).mp h'
  rcases k with (_ | _ | _)
  · obtain rfl : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
    obtain rfl : fj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
    rw [span_map_fst] at hz1
    rw [span_map_snd] at hz2
    exact ⟨z, hz1, hz2⟩
  · rcases fj with (_ | _)
  · rcases fi with (_ | _)

include M in
theorem injective_overBase : Function.Injective (overBase R F j R') := by
  have hFin : Function.Injective (ιFin R' F j ≫ overBase R F j R') := by
    rw [ιFin_overBase, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (ιFin R F j).isOpenEmbedding.injective.comp (injective_Spec_chartBaseChange R F R' M {j})
  have hInf : Function.Injective (ιInf R' F j ≫ overBase R F j R') := by
    rw [ιInf_overBase, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (ιInf R F j).isOpenEmbedding.injective.comp
      (injective_Spec_chartBaseChange R F R' M {j⁻¹})

  have hmix : ∀ (a : XFin R' F j) (b : XInf R' F j),
      overBase R F j R' (ιFin R' F j a) = overBase R F j R' (ιInf R' F j b) →
      ιFin R' F j a = ιInf R' F j b := by
    intro a b hab
    have hab' := hab
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ιFin_overBase, ιInf_overBase,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hab'
    obtain ⟨w, hw1, -⟩ := exists_of_ιFin_eq_ιInf R F j hab'
    obtain ⟨z, rfl⟩ := exists_fFin_eq_of_mem_range R F j R' ⟨w, hw1⟩
    have hz : ιFin R' F j (fFin R' F j z) = ιInf R' F j (fInf R' F j z) := by
      rw [← Scheme.Hom.comp_apply, glue_condition, Scheme.Hom.comp_apply]
    rw [hz] at hab ⊢
    exact congrArg _ (hInf (by simpa only [Scheme.Hom.comp_apply] using hab))
  intro x y hxy
  rcases mem_range_ιFin_or_mem_range_ιInf R' F j x with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases mem_range_ιFin_or_mem_range_ιInf R' F j y with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · exact congrArg _ (hFin (by simpa only [Scheme.Hom.comp_apply] using hxy))
  · exact hmix a b hxy
  · exact (hmix b a hxy.symm).symm
  · exact congrArg _ (hInf (by simpa only [Scheme.Hom.comp_apply] using hxy))

include M in
theorem injective_toPullback : Function.Injective (toPullback R F j R') := by
  intro x y h
  apply injective_overBase R F j R' M
  rw [← toPullback_fst R F j R', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h]

include M in
theorem isOpenImmersion_toPullback : IsOpenImmersion (toPullback R F j R') := by
  refine IsOpenImmersion.of_forall_source_exists _ (injective_toPullback R F j R' M) fun x => ?_
  rcases mem_range_ιFin_or_mem_range_ιInf R' F j x with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact ⟨_, ιFin R' F j, inferInstance, ⟨a, rfl⟩, isOpenImmersion_ιFin_toPullback R F j R' M⟩
  · exact ⟨_, ιInf R' F j, inferInstance, ⟨a, rfl⟩, isOpenImmersion_ιInf_toPullback R F j R' M⟩

include M in
theorem isIso_toPullback : IsIso (toPullback R F j R') :=
  (isIso_iff_isOpenImmersion_and_surjective _).mpr
    ⟨isOpenImmersion_toPullback R F j R' M, ⟨surjective_toPullback R F j R' M⟩⟩

end Glue

end AlgebraicCurve.TwoChartIntegralModel

open _root_.AlgebraicCurve.TwoChartIntegralModel _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_baseChange_baseChange_of_isLocalization.AlgebraicCurve.TwoChartIntegralModel in

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]
    (M : Submonoid R) [IsLocalization M R']
    (S : Type u) [CommRing S] [Algebra R S] [Algebra R' S] [IsScalarTower R R' S] :
    ∃ (u : AlgebraicCurve.TwoChartIntegralModel R' F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
      (e : AlgebraicCurve.TwoChartIntegralModel.baseChange R' F j S ≅
        AlgebraicCurve.TwoChartIntegralModel.baseChange R F j S),
      AlgebraicCurve.TwoChartIntegralModel.ιFin R' F j ≫ u =
        Spec.map (CommRingCat.ofHom (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' {j})) ≫
          AlgebraicCurve.TwoChartIntegralModel.ιFin R F j ∧
      AlgebraicCurve.TwoChartIntegralModel.ιInf R' F j ≫ u =
        Spec.map (CommRingCat.ofHom (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' {j⁻¹})) ≫
          AlgebraicCurve.TwoChartIntegralModel.ιInf R F j ∧
      e.hom ≫ AlgebraicCurve.TwoChartIntegralModel.baseChangeToBase R F j S =
        AlgebraicCurve.TwoChartIntegralModel.baseChangeToBase R' F j S ∧
      e.hom ≫ AlgebraicCurve.TwoChartIntegralModel.baseChangeι R F j S =
        AlgebraicCurve.TwoChartIntegralModel.baseChangeι R' F j S ≫ u := by
  haveI := isIso_toPullback R F j R' M
  have sq2 : IsPullback (overBase R F j R') (toBase R' F j) (toBase R F j)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    IsPullback.of_iso_pullback ⟨overBase_toBase R F j R'⟩ (asIso (toPullback R F j R'))
      (toPullback_fst R F j R') (toPullback_snd R F j R')
  have sq1 : IsPullback (baseChangeι R' F j S) (baseChangeToBase R' F j S) (toBase R' F j)
      (Spec.map (CommRingCat.ofHom (algebraMap R' S))) :=
    IsPullback.of_hasPullback _ _
  have sq := sq1.paste_horiz sq2
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R R' S] at sq
  refine ⟨overBase R F j R', sq.isoPullback, ιFin_overBase R F j R', ιInf_overBase R F j R',
    sq.isoPullback_hom_snd, sq.isoPullback_hom_fst⟩

end S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_baseChange_baseChange_of_isLocalization
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_baseChange_baseChange_of_isLocalization (solution)
