-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_hom_isFinite_surjective_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/0a8590a6-8153-57ac-9146-59cd02a07e8b

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_of_algHom

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_of_algHom.AlgebraicCurve.TwoChartIntegralModel"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlg mem_chartAlg_iff adjoin_le_chartAlg subset_chartAlg coe_chartIncl chartAlgFin chartAlgInf chartAlgMid jChartFin jInvChartInf coe_jChartFin coe_jInvChartInf inclFin inclInf XFin XInf fFin fInf ιFin ιInf glue_condition toBase ιFin_toBase ιInf_toBase mem_range_ιFin_or_mem_range_ιInf TwoChartsAux.ιFin_eq_ιInf_iff TwoChartsAux.range_fFin TwoChartsAux.range_fInf"
namespace ModelMap
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

variable (R : Type u) [CommRing R] {F F' : Type u} [Field F] [Field F'] [Algebra R F] [Algebra R F'] (φ : F →ₐ[R] F')

theorem map_mem_chartAlg {S : Set F} {T : Set F'} (hST : φ '' S ⊆ T) {x : F} (hx : x ∈ chartAlg R F S) :
    φ x ∈ chartAlg R F' T := by
  rw [mem_chartAlg_iff] at hx ⊢
  have hle : (Algebra.adjoin R S).map φ ≤ Algebra.adjoin R T := by
    rw [AlgHom.map_adjoin]
    exact Algebra.adjoin_mono hST
  let ψ : Algebra.adjoin R S →ₐ[R] Algebra.adjoin R T :=
    (φ.comp (Algebra.adjoin R S).val).codRestrict (Algebra.adjoin R T) (fun y => hle ⟨y, y.2, rfl⟩)
  exact IsIntegral.map_of_comp_eq ψ.toRingHom φ.toRingHom (by ext y; rfl) hx

def chartMap (S : Set F) (T : Set F') (hST : φ '' S ⊆ T) : chartAlg R F S →ₐ[R] chartAlg R F' T :=
  (φ.comp (chartAlg R F S).val).codRestrict (chartAlg R F' T) (fun x => map_mem_chartAlg R φ hST x.2)

@[scoped simp] theorem coe_chartMap (S : Set F) (T : Set F') (hST : φ '' S ⊆ T) (x : chartAlg R F S) :
    (chartMap R φ S T hST x : F') = φ x := rfl

variable (j : F) [Fact (j ≠ 0)] [Fact (φ j ≠ 0)]

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in
theorem image_sFin : φ '' ({j} : Set F) ⊆ ({φ j} : Set F') := by
  rw [Set.image_singleton]
omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in
theorem image_sInf : φ '' ({j⁻¹} : Set F) ⊆ ({(φ j)⁻¹} : Set F') := by
  rw [Set.image_singleton, map_inv₀]
omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in
theorem image_sMid : φ '' ({j, j⁻¹} : Set F) ⊆ ({φ j, (φ j)⁻¹} : Set F') := by
  rw [Set.image_pair, map_inv₀]

def ιF : chartAlgFin R F j →ₐ[R] chartAlgFin R F' (φ j) := chartMap R φ {j} {φ j} (image_sFin R φ j)
def ιI : chartAlgInf R F j →ₐ[R] chartAlgInf R F' (φ j) := chartMap R φ {j⁻¹} {(φ j)⁻¹} (image_sInf R φ j)
def ιM : chartAlgMid R F j →ₐ[R] chartAlgMid R F' (φ j) := chartMap R φ {j, j⁻¹} {φ j, (φ j)⁻¹} (image_sMid R φ j)

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in
theorem coe_ιF (x : chartAlgFin R F j) : (ιF R φ j x : F') = φ x := coe_chartMap R φ _ _ _ x
omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in
theorem coe_ιI (x : chartAlgInf R F j) : (ιI R φ j x : F') = φ x := coe_chartMap R φ _ _ _ x
omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in
theorem coe_ιM (x : chartAlgMid R F j) : (ιM R φ j x : F') = φ x := coe_chartMap R φ _ _ _ x

theorem inclFin_ιF_apply (x : chartAlgFin R F j) :
    ((inclFin R F' (φ j)) (ιF R φ j x) : F') = ((ιM R φ j) (inclFin R F j x) : F') := by
  rw [coe_chartIncl, coe_ιF, coe_ιM, coe_chartIncl]

theorem inclInf_ιI_apply (x : chartAlgInf R F j) :
    ((inclInf R F' (φ j)) (ιI R φ j x) : F') = ((ιM R φ j) (inclInf R F j x) : F') := by
  rw [coe_chartIncl, coe_ιI, coe_ιM, coe_chartIncl]

theorem inclFin_comp_ιF : (inclFin R F' (φ j)).comp (ιF R φ j) = (ιM R φ j).comp (inclFin R F j) :=
  AlgHom.ext fun x => Subtype.ext (by rw [AlgHom.comp_apply, AlgHom.comp_apply]; exact inclFin_ιF_apply R φ j x)

theorem inclInf_comp_ιI : (inclInf R F' (φ j)).comp (ιI R φ j) = (ιM R φ j).comp (inclInf R F j) :=
  AlgHom.ext fun x => Subtype.ext (by rw [AlgHom.comp_apply, AlgHom.comp_apply]; exact inclInf_ιI_apply R φ j x)

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in

theorem chartAlg_isIntegral_adjoin (S : Set F) :
    letI := (Subalgebra.inclusion (adjoin_le_chartAlg R F S)).toRingHom.toAlgebra
    Algebra.IsIntegral (Algebra.adjoin R S) (chartAlg R F S) := by
  letI := (Subalgebra.inclusion (adjoin_le_chartAlg R F S)).toRingHom.toAlgebra
  haveI : IsScalarTower (Algebra.adjoin R S) (chartAlg R F S) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨fun a => ?_⟩
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (Algebra.adjoin R S) (chartAlg R F S) F)
    Subtype.val_injective).mp a.2

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in

theorem mem_chartAlg_of_isIntegral (S : Set F) {x : F} (hx : IsIntegral (chartAlg R F S) x) :
    x ∈ chartAlg R F S := by
  letI := (Subalgebra.inclusion (adjoin_le_chartAlg R F S)).toRingHom.toAlgebra
  haveI : IsScalarTower (Algebra.adjoin R S) (chartAlg R F S) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := chartAlg_isIntegral_adjoin R (F := F) S
  exact (mem_chartAlg_iff R F).mpr (isIntegral_trans x hx)

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in

theorem isIntegrallyClosed_chartAlg (S : Set F) [IsFractionRing (chartAlg R F S) F] :
    IsIntegrallyClosed (chartAlg R F S) :=
  (isIntegrallyClosed_iff F).mpr fun {x} hx => ⟨⟨x, mem_chartAlg_of_isIntegral R (F := F) S hx⟩, rfl⟩

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in

theorem isIntegralElem_coe_of_mem_chartAlg (S : Set F) (T : Set F') (hTS : T ⊆ φ '' S) (x : F')
    (hx : x ∈ chartAlg R F' T) :
    (φ.toRingHom.comp (algebraMap (chartAlg R F S) F)).IsIntegralElem x := by
  letI := (φ.toRingHom.comp (algebraMap (chartAlg R F S) F)).toAlgebra
  haveI : IsScalarTower R (chartAlg R F S) F' := IsScalarTower.of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    show algebraMap R F' r = φ ((algebraMap R (chartAlg R F S) r : chartAlg R F S) : F)
    rw [Subalgebra.coe_algebraMap, AlgHom.commutes]
  set C := integralClosure (chartAlg R F S) F' with hC
  have hle : Algebra.adjoin R T ≤ C.restrictScalars R := by
    rw [Algebra.adjoin_le_iff]
    intro t ht
    obtain ⟨s, hs, rfl⟩ := hTS ht
    show IsIntegral (chartAlg R F S) (φ s)
    have : φ s = algebraMap (chartAlg R F S) F' ⟨s, subset_chartAlg R F S hs⟩ := rfl
    rw [this]
    exact isIntegral_algebraMap
  rw [mem_chartAlg_iff] at hx
  obtain ⟨P, hPm, hP⟩ := hx
  let ι : Algebra.adjoin R T →+* C :=
    { toFun := fun a => ⟨a, hle a.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have h2 : IsIntegral C x := by
    refine ⟨P.map ι, hPm.map ι, ?_⟩
    rw [Polynomial.eval₂_map]
    convert hP using 1
    rfl
  exact isIntegral_trans (R := chartAlg R F S) (A := C) x h2

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in

theorem ringHom_finite_of_isIntegralElem {A B : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Algebra A F] [IsFractionRing A F] [CommRing B] [CharZero F']
    (ψ : F →+* F') (hψ : ψ.Finite) (g : A →+* B) (v : B →+* F') (hv : Function.Injective v)
    (hcomm : v.comp g = ψ.comp (algebraMap A F))
    (hint : ∀ b : B, (ψ.comp (algebraMap A F)).IsIntegralElem (v b)) : g.Finite := by
  classical
  letI algFF' : Algebra F F' := ψ.toAlgebra
  letI algAF' : Algebra A F' := (ψ.comp (algebraMap A F)).toAlgebra
  haveI : IsScalarTower A F F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite F F' := hψ
  haveI : CharZero F := ψ.charZero
  haveI : Algebra.IsAlgebraic F F' := Algebra.IsAlgebraic.of_finite F F'
  haveI : Module.Finite A (integralClosure A F') := IsIntegralClosure.finite A F F' (integralClosure A F')
  letI algAB : Algebra A B := g.toAlgebra
  let f : B →ₗ[A] integralClosure A F' :=
    { toFun := fun b => ⟨v b, hint b⟩
      map_add' := fun _ _ => Subtype.ext (map_add v _ _)
      map_smul' := fun a b => Subtype.ext (by
        show v (g a * b) = (ψ.comp (algebraMap A F)) a * v b
        rw [map_mul, ← RingHom.comp_apply, hcomm]) }
  have hf : Function.Injective f := fun x y h =>
    hv (congrArg (fun z : integralClosure A F' => (z : F')) h)
  exact Module.Finite.of_injective f hf

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in

theorem finite_chartMap [CharZero F'] (hφ : φ.toRingHom.Finite) (S : Set F) (T : Set F')
    (hST : φ '' S ⊆ T) (hTS : T ⊆ φ '' S)
    (hA : IsNoetherianRing ↥(chartAlg R F S) ∧ IsFractionRing ↥(chartAlg R F S) F) :
    (chartMap R φ S T hST).toRingHom.Finite := by
  haveI : IsNoetherianRing (chartAlg R F S) := hA.1
  haveI : IsFractionRing (chartAlg R F S) F := hA.2
  haveI : IsIntegrallyClosed (chartAlg R F S) := isIntegrallyClosed_chartAlg R (F := F) S
  refine ringHom_finite_of_isIntegralElem (F := F) (F' := F') φ.toRingHom hφ (chartMap R φ S T hST).toRingHom
    (chartAlg R F' T).val.toRingHom Subtype.val_injective (RingHom.ext fun a => ?_) fun b => ?_
  · show ((chartMap R φ S T hST a : chartAlg R F' T) : F') = φ (a : F)
    rw [coe_chartMap]
  · exact isIntegralElem_coe_of_mem_chartAlg R φ S T hTS (b : F') b.2

theorem ringHom_inclFin_comp_ιF :
    (inclFin R F' (φ j)).toRingHom.comp (ιF R φ j).toRingHom = (ιM R φ j).toRingHom.comp (inclFin R F j).toRingHom :=
  RingHom.ext fun x => by
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    exact Subtype.ext (inclFin_ιF_apply R φ j x)

theorem ringHom_inclInf_comp_ιI :
    (inclInf R F' (φ j)).toRingHom.comp (ιI R φ j).toRingHom = (ιM R φ j).toRingHom.comp (inclInf R F j).toRingHom :=
  RingHom.ext fun x => by
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    exact Subtype.ext (inclInf_ιI_apply R φ j x)

theorem fFin_comp_spec_ιF :
    fFin R F' (φ j) ≫ Spec.map (CommRingCat.ofHom (ιF R φ j).toRingHom) =
      Spec.map (CommRingCat.ofHom (ιM R φ j).toRingHom) ≫ fFin R F j := by
  show Spec.map (CommRingCat.ofHom (inclFin R F' (φ j)).toRingHom) ≫ Spec.map (CommRingCat.ofHom (ιF R φ j).toRingHom) =
    Spec.map (CommRingCat.ofHom (ιM R φ j).toRingHom) ≫ Spec.map (CommRingCat.ofHom (inclFin R F j).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ringHom_inclFin_comp_ιF]

theorem fInf_comp_spec_ιI :
    fInf R F' (φ j) ≫ Spec.map (CommRingCat.ofHom (ιI R φ j).toRingHom) =
      Spec.map (CommRingCat.ofHom (ιM R φ j).toRingHom) ≫ fInf R F j := by
  show Spec.map (CommRingCat.ofHom (inclInf R F' (φ j)).toRingHom) ≫ Spec.map (CommRingCat.ofHom (ιI R φ j).toRingHom) =
    Spec.map (CommRingCat.ofHom (ιM R φ j).toRingHom) ≫ Spec.map (CommRingCat.ofHom (inclInf R F j).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ringHom_inclInf_comp_ιI]

noncomputable def m : AlgebraicCurve.TwoChartIntegralModel R F' (φ j) ⟶ AlgebraicCurve.TwoChartIntegralModel R F j :=
  pushout.desc (Spec.map (CommRingCat.ofHom (ιF R φ j).toRingHom) ≫ ιFin R F j)
    (Spec.map (CommRingCat.ofHom (ιI R φ j).toRingHom) ≫ ιInf R F j)
    (by rw [← Category.assoc, fFin_comp_spec_ιF, Category.assoc, glue_condition, ← Category.assoc,
          ← fInf_comp_spec_ιI, Category.assoc])

theorem ιFin_m : ιFin R F' (φ j) ≫ m R φ j = Spec.map (CommRingCat.ofHom (ιF R φ j).toRingHom) ≫ ιFin R F j := by
  rw [ιFin, m]
  exact pushout.inl_desc _ _ _

theorem ιInf_m : ιInf R F' (φ j) ≫ m R φ j = Spec.map (CommRingCat.ofHom (ιI R φ j).toRingHom) ≫ ιInf R F j := by
  rw [ιInf, m]
  exact pushout.inr_desc _ _ _

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in
theorem ιF_comp_algebraMap : (ιF R φ j).toRingHom.comp (algebraMap R (chartAlgFin R F j)) = algebraMap R (chartAlgFin R F' (φ j)) :=
  RingHom.ext fun r => by
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in
theorem ιI_comp_algebraMap : (ιI R φ j).toRingHom.comp (algebraMap R (chartAlgInf R F j)) = algebraMap R (chartAlgInf R F' (φ j)) :=
  RingHom.ext fun r => by
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]

theorem m_toBase : m R φ j ≫ toBase R F j = toBase R F' (φ j) := by

  have h1 : ιFin R F' (φ j) ≫ m R φ j ≫ toBase R F j = ιFin R F' (φ j) ≫ toBase R F' (φ j) := by
    rw [← Category.assoc, ιFin_m, Category.assoc, ιFin_toBase, ιFin_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ιF_comp_algebraMap]
  have h2 : ιInf R F' (φ j) ≫ m R φ j ≫ toBase R F j = ιInf R F' (φ j) ≫ toBase R F' (φ j) := by
    rw [← Category.assoc, ιInf_m, Category.assoc, ιInf_toBase, ιInf_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ιI_comp_algebraMap]
  rw [ιFin] at h1
  rw [ιInf] at h2
  exact pushout.hom_ext h1 h2

omit [Fact (φ j ≠ 0)] in

theorem ιInf_mem_range_ιFin_iff (𝔮 : PrimeSpectrum (chartAlgInf R F j)) :
    (ιInf R F j).base 𝔮 ∈ Set.range (ιFin R F j).base ↔ jInvChartInf R F j ∉ 𝔮.asIdeal := by
  have key : 𝔮 ∈ Set.range (fInf R F j).base ↔ jInvChartInf R F j ∉ 𝔮.asIdeal := by
    rw [TwoChartsAux.range_fInf]; exact Iff.rfl
  rw [← key]
  constructor
  · rintro ⟨x₀, hx⟩
    obtain ⟨u, -, hu⟩ := (TwoChartsAux.ιFin_eq_ιInf_iff R F j x₀ 𝔮).mp hx
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨(fFin R F j).base u, (TwoChartsAux.ιFin_eq_ιInf_iff R F j _ 𝔮).mpr ⟨u, rfl, hu⟩⟩

omit [Fact (φ j ≠ 0)] in

theorem ιFin_mem_range_ιInf_iff (𝔭 : PrimeSpectrum (chartAlgFin R F j)) :
    (ιFin R F j).base 𝔭 ∈ Set.range (ιInf R F j).base ↔ jChartFin R F j ∉ 𝔭.asIdeal := by
  have key : 𝔭 ∈ Set.range (fFin R F j).base ↔ jChartFin R F j ∉ 𝔭.asIdeal := by
    rw [TwoChartsAux.range_fFin]; exact Iff.rfl
  rw [← key]
  constructor
  · rintro ⟨xi, hx⟩
    obtain ⟨u, hu, -⟩ := (TwoChartsAux.ιFin_eq_ιInf_iff R F j 𝔭 xi).mp hx.symm
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨(fInf R F j).base u, ((TwoChartsAux.ιFin_eq_ιInf_iff R F j 𝔭 _).mpr ⟨u, hu, rfl⟩).symm⟩

theorem ιF_jChartFin : ιF R φ j (jChartFin R F j) = jChartFin R F' (φ j) :=
  Subtype.ext (by rw [coe_ιF, coe_jChartFin, coe_jChartFin])

theorem ιI_jInvChartInf : ιI R φ j (jInvChartInf R F j) = jInvChartInf R F' (φ j) :=
  Subtype.ext (by rw [coe_ιI, coe_jInvChartInf, coe_jInvChartInf, map_inv₀])

theorem m_base_ιFin (y : XFin R F' (φ j)) :
    (m R φ j).base ((ιFin R F' (φ j)).base y) =
      (ιFin R F j).base ((Spec.map (CommRingCat.ofHom (ιF R φ j).toRingHom)).base y) := by
  show ((ιFin R F' (φ j)) ≫ m R φ j).base y = (Spec.map (CommRingCat.ofHom (ιF R φ j).toRingHom) ≫ ιFin R F j).base y
  rw [ιFin_m]

theorem m_base_ιInf (y : XInf R F' (φ j)) :
    (m R φ j).base ((ιInf R F' (φ j)).base y) =
      (ιInf R F j).base ((Spec.map (CommRingCat.ofHom (ιI R φ j).toRingHom)).base y) := by
  show ((ιInf R F' (φ j)) ≫ m R φ j).base y = (Spec.map (CommRingCat.ofHom (ιI R φ j).toRingHom) ≫ ιInf R F j).base y
  rw [ιInf_m]

theorem jChartFin_mem_specMap_ιF_iff (y : PrimeSpectrum (chartAlgFin R F' (φ j))) :
    jChartFin R F j ∈ ((Spec.map (CommRingCat.ofHom (ιF R φ j).toRingHom)).base y).asIdeal ↔
      jChartFin R F' (φ j) ∈ y.asIdeal := by
  show jChartFin R F j ∈ (PrimeSpectrum.comap (ιF R φ j).toRingHom y).asIdeal ↔ _
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ιF_jChartFin]

theorem jInvChartInf_mem_specMap_ιI_iff (y : PrimeSpectrum (chartAlgInf R F' (φ j))) :
    jInvChartInf R F j ∈ ((Spec.map (CommRingCat.ofHom (ιI R φ j).toRingHom)).base y).asIdeal ↔
      jInvChartInf R F' (φ j) ∈ y.asIdeal := by
  show jInvChartInf R F j ∈ (PrimeSpectrum.comap (ιI R φ j).toRingHom y).asIdeal ↔ _
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ιI_jInvChartInf]

theorem preimage_clauses :
    m R φ j ⁻¹ᵁ (ιFin R F j).opensRange = (ιFin R F' (φ j)).opensRange ∧
      m R φ j ⁻¹ᵁ (ιInf R F j).opensRange = (ιInf R F' (φ j)).opensRange := by
  constructor
  · ext x
    show (m R φ j).base x ∈ Set.range (ιFin R F j).base ↔ x ∈ Set.range (ιFin R F' (φ j)).base
    constructor
    · intro hx
      rcases mem_range_ιFin_or_mem_range_ιInf R F' (φ j) x with h | ⟨y, rfl⟩
      · exact h
      · rw [m_base_ιInf, ιInf_mem_range_ιFin_iff, jInvChartInf_mem_specMap_ιI_iff] at hx
        exact (ιInf_mem_range_ιFin_iff R (φ j) y).mpr hx
    · rintro ⟨y, rfl⟩
      rw [m_base_ιFin]
      exact ⟨_, rfl⟩
  · ext x
    show (m R φ j).base x ∈ Set.range (ιInf R F j).base ↔ x ∈ Set.range (ιInf R F' (φ j)).base
    constructor
    · intro hx
      rcases mem_range_ιFin_or_mem_range_ιInf R F' (φ j) x with ⟨y, rfl⟩ | h
      · rw [m_base_ιFin, ιFin_mem_range_ιInf_iff, jChartFin_mem_specMap_ιF_iff] at hx
        exact (ιFin_mem_range_ιInf_iff R (φ j) y).mpr hx
      · exact h
    · rintro ⟨y, rfl⟩
      rw [m_base_ιInf]
      exact ⟨_, rfl⟩

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in
theorem finite_ιF [CharZero F'] (hφ : φ.toRingHom.Finite)
    (hFfin : IsNoetherianRing ↥(chartAlgFin R F j) ∧ IsFractionRing ↥(chartAlgFin R F j) F) :
    (ιF R φ j).toRingHom.Finite :=
  finite_chartMap R φ hφ {j} {φ j} (image_sFin R φ j) (by rw [Set.image_singleton]) hFfin

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in
theorem finite_ιI [CharZero F'] (hφ : φ.toRingHom.Finite)
    (hFinf : IsNoetherianRing ↥(chartAlgInf R F j) ∧ IsFractionRing ↥(chartAlgInf R F j) F) :
    (ιI R φ j).toRingHom.Finite :=
  finite_chartMap R φ hφ {j⁻¹} {(φ j)⁻¹} (image_sInf R φ j) (by rw [Set.image_singleton, map_inv₀]) hFinf

theorem isPullback_ιFin :
    IsPullback (Spec.map (CommRingCat.ofHom (ιF R φ j).toRingHom)) (ιFin R F' (φ j)) (ιFin R F j) (m R φ j) :=
  IsOpenImmersion.isPullback _ _ _ _ (ιFin_m R φ j) (preimage_clauses R φ j).1

theorem isPullback_ιInf :
    IsPullback (Spec.map (CommRingCat.ofHom (ιI R φ j).toRingHom)) (ιInf R F' (φ j)) (ιInf R F j) (m R φ j) :=
  IsOpenImmersion.isPullback _ _ _ _ (ιInf_m R φ j) (preimage_clauses R φ j).2

noncomputable def twoChartOpenCover : (AlgebraicCurve.TwoChartIntegralModel R F j).OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b => bif b then XFin R F j else XInf R F j)
    (fun b => match b with
      | true => ιFin R F j
      | false => ιInf R F j)
    (fun x => by
      rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨true, y, hy⟩
      · exact ⟨false, y, hy⟩)
    (fun b => match b with
      | true => (inferInstance : IsOpenImmersion (ιFin R F j))
      | false => (inferInstance : IsOpenImmersion (ιInf R F j)))

theorem isFinite_m [CharZero F'] (hφ : φ.toRingHom.Finite)
    (hFfin : IsNoetherianRing ↥(chartAlgFin R F j) ∧ IsFractionRing ↥(chartAlgFin R F j) F)
    (hFinf : IsNoetherianRing ↥(chartAlgInf R F j) ∧ IsFractionRing ↥(chartAlgInf R F j) F) :
    IsFinite (m R φ j) := by
  haveI hF : IsFinite (Spec.map (CommRingCat.ofHom (ιF R φ j).toRingHom)) := by
    rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]; exact finite_ιF R φ j hφ hFfin
  haveI hI : IsFinite (Spec.map (CommRingCat.ofHom (ιI R φ j).toRingHom)) := by
    rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]; exact finite_ιI R φ j hφ hFinf
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) (twoChartOpenCover R j) ?_
  rintro (_ | _)
  · show IsFinite (pullback.snd (m R φ j) (ιInf R F j))
    rw [← (isPullback_ιInf R φ j).flip.isoPullback_inv_snd]
    infer_instance
  · show IsFinite (pullback.snd (m R φ j) (ιFin R F j))
    rw [← (isPullback_ιFin R φ j).flip.isoPullback_inv_snd]
    infer_instance

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in

theorem isIntegralElem_of_comp_injective {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* B) (v : B →+* C) (hv : Function.Injective v) (b : B)
    (h : (v.comp g).IsIntegralElem (v b)) : g.IsIntegralElem b := by
  obtain ⟨p, hp, h0⟩ := h
  refine ⟨p, hp, hv ?_⟩
  rw [map_zero, Polynomial.hom_eval₂, h0]

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in
theorem val_comp_chartMap (S : Set F) (T : Set F') (hST : φ '' S ⊆ T) :
    (chartAlg R F' T).val.toRingHom.comp (chartMap R φ S T hST).toRingHom =
      φ.toRingHom.comp (algebraMap (chartAlg R F S) F) :=
  RingHom.ext fun a => by
    show ((chartMap R φ S T hST a : chartAlg R F' T) : F') = φ (a : F)
    rw [coe_chartMap]

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in

theorem isIntegral_chartMap (S : Set F) (T : Set F') (hST : φ '' S ⊆ T) (hTS : T ⊆ φ '' S) :
    (chartMap R φ S T hST).toRingHom.IsIntegral := fun b =>
  isIntegralElem_of_comp_injective _ (chartAlg R F' T).val.toRingHom Subtype.val_injective b (by
    rw [val_comp_chartMap]
    exact isIntegralElem_coe_of_mem_chartAlg R φ S T hTS (b : F') b.2)

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in

theorem injective_chartMap (S : Set F) (T : Set F') (hST : φ '' S ⊆ T) :
    Function.Injective (chartMap R φ S T hST) := fun x y h =>
  Subtype.ext (φ.toRingHom.injective (by
    have h' := congrArg (fun z : chartAlg R F' T => (z : F')) h
    simp only [coe_chartMap] at h'
    exact h'))

omit [Fact (j ≠ 0)] [Fact (φ j ≠ 0)] in

theorem surjective_specMap_chartMap (S : Set F) (T : Set F') (hST : φ '' S ⊆ T) (hTS : T ⊆ φ '' S) :
    Function.Surjective (Spec.map (CommRingCat.ofHom (chartMap R φ S T hST).toRingHom)).base := by
  intro w
  obtain ⟨w', hw'⟩ := (isIntegral_chartMap R φ S T hST hTS).comap_surjective (injective_chartMap R φ S T hST) w
  exact ⟨w', hw'⟩

theorem surjective_m : Function.Surjective (m R φ j).base := by
  intro z
  rcases mem_range_ιFin_or_mem_range_ιInf R F j z with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · obtain ⟨w', hw'⟩ :=
      surjective_specMap_chartMap R φ {j} {φ j} (image_sFin R φ j) (by rw [Set.image_singleton]) w
    exact ⟨(ιFin R F' (φ j)).base w', by rw [m_base_ιFin]; exact congrArg _ hw'⟩
  · obtain ⟨w', hw'⟩ :=
      surjective_specMap_chartMap R φ {j⁻¹} {(φ j)⁻¹} (image_sInf R φ j) (by rw [Set.image_singleton, map_inv₀]) w
    exact ⟨(ιInf R F' (φ j)).base w', by rw [m_base_ιInf]; exact congrArg _ hw'⟩

end AlgebraicCurve.TwoChartIntegralModel.ModelMap
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_of_algHom.AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_of_algHom.AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_of_algHom.AlgebraicCurve.TwoChartIntegralModel.ModelMap"
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_of_algHom.AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_of_algHom.AlgebraicCurve.TwoChartIntegralModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_of_algHom.AlgebraicCurve"

open AlgebraicCurve.TwoChartIntegralModel.ModelMap in
theorem solution
    (R : Type u) [CommRing R] (F F' : Type u) [Field F] [Field F'] [CharZero F'] [Algebra R F] [Algebra R F']
    (φ : F →ₐ[R] F') (hφ : φ.toRingHom.Finite)
    (j : F) (j' : F') [Fact (j ≠ 0)] [Fact (j' ≠ 0)] (hj : φ j = j')
    (hFfin : IsNoetherianRing ↥(chartAlgFin R F j) ∧ IsFractionRing ↥(chartAlgFin R F j) F)
    (hFinf : IsNoetherianRing ↥(chartAlgInf R F j) ∧ IsFractionRing ↥(chartAlgInf R F j) F) :
    ∃ (m : AlgebraicCurve.TwoChartIntegralModel R F' j' ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
      (ιF : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F' j'))
      (ιI : ↥(chartAlgInf R F j) →ₐ[R] ↥(chartAlgInf R F' j')),
      (∀ x, (ιF x : F') = φ x) ∧ (∀ x, (ιI x : F') = φ x) ∧
      m ≫ toBase R F j = toBase R F' j' ∧
      Spec.map (CommRingCat.ofHom ιF.toRingHom) ≫ ιFin R F j = ιFin R F' j' ≫ m ∧
      Spec.map (CommRingCat.ofHom ιI.toRingHom) ≫ ιInf R F j = ιInf R F' j' ≫ m ∧
      m ⁻¹ᵁ (ιFin R F j).opensRange = (ιFin R F' j').opensRange ∧
      m ⁻¹ᵁ (ιInf R F j).opensRange = (ιInf R F' j').opensRange ∧
      IsFinite m ∧ Function.Surjective m.base := by
  subst hj
  exact ⟨m R φ j, ιF R φ j, ιI R φ j, fun x => coe_ιF R φ j x, fun x => coe_ιI R φ j x, m_toBase R φ j,
    (ιFin_m R φ j).symm, (ιInf_m R φ j).symm, (preimage_clauses R φ j).1, (preimage_clauses R φ j).2,
    isFinite_m R φ j hφ hFfin hFinf, surjective_m R φ j⟩

end S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_of_algHom
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_of_algHom (solution)
