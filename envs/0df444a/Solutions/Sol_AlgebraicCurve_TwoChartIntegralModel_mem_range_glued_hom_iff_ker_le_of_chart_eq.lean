-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.mem_range_glued_hom_iff_ker_le_of_chart_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/6a897e90-db41-5767-b6ec-99bb7006f9fc

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Theorems.Thm_PrimeSpectrum_range_comap_eq_zeroLocus_ker_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_glued_hom_iff_ker_le_of_chart_eq

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.CurveModel
open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

namespace RangeChartK12

open AlgebraicCurve.TwoChartIntegralModel

abbrev baseMap (R : Type u) [CommRing R] (κ : Type u) [Field κ] [Algebra R κ] :
    Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R κ))

section Model

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem tc_ιFin_eq_ιInf_iff (x₀ : XFin R F j) (xi : TwoChartIntegralModel.XInf R F j) :
    (ιFin R F j).base x₀ = (TwoChartIntegralModel.ιInf R F j).base xi ↔
      ∃ w : XMid R F j, (fFin R F j).base w = x₀ ∧ (TwoChartIntegralModel.fInf R F j).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (F := span (fFin R F j) (TwoChartIntegralModel.fInf R F j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · exact match fi, fj, h₁, h₂ with
        | .init _, .init _, h₁, h₂ => ⟨w, h₁, h₂⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨w, rfl, rfl⟩
    change (fFin R F j ≫ ιFin R F j).base w =
      (TwoChartIntegralModel.fInf R F j ≫ TwoChartIntegralModel.ιInf R F j).base w
    rw [TwoChartIntegralModel.glue_condition]

theorem tc_range_fInf : Set.range (TwoChartIntegralModel.fInf R F j).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf R F j) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(chartAlgInf R F j))) : Set (PrimeSpectrum ↥(chartAlgInf R F j))) := by
  letI := (TwoChartIntegralModel.inclInf R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R F j
  exact PrimeSpectrum.localization_away_comap_range ↥(chartAlgMid R F j) (jInvChartInf R F j)

theorem tc_ιInf_mem_range_ιFin_iff (xi : TwoChartIntegralModel.XInf R F j) :
    (TwoChartIntegralModel.ιInf R F j).base xi ∈ Set.range (ιFin R F j).base ↔
      jInvChartInf R F j ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← tc_range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (tc_ιFin_eq_ιInf_iff R F j x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(fFin R F j).base w, (tc_ιFin_eq_ιInf_iff R F j _ _).mpr ⟨w, rfl, rfl⟩⟩

theorem tc_range_fFin : Set.range (fFin R F j).base =
    ((PrimeSpectrum.basicOpen (jChartFin R F j) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(chartAlgFin R F j))) : Set (PrimeSpectrum ↥(chartAlgFin R F j))) := by
  letI := (TwoChartIntegralModel.inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  exact PrimeSpectrum.localization_away_comap_range ↥(chartAlgMid R F j) (jChartFin R F j)

theorem tc_ιFin_mem_range_ιInf_iff (x₀ : XFin R F j) :
    (ιFin R F j).base x₀ ∈ Set.range (TwoChartIntegralModel.ιInf R F j).base ↔
      jChartFin R F j ∉ x₀.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← tc_range_fFin, Set.mem_range]
  constructor
  · rintro ⟨xi, h⟩
    obtain ⟨w, hw, -⟩ := (tc_ιFin_eq_ιInf_iff R F j x₀ xi).mp h.symm
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(TwoChartIntegralModel.fInf R F j).base w, ((tc_ιFin_eq_ιInf_iff R F j _ _).mpr ⟨w, rfl, rfl⟩).symm⟩

end Model

section Fin

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]
  (θFin : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t} : Set L)))
  (c : CurveModel.glued κ t ⟶ pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))

abbrev θF : ↥(chartAlgFin R F j) ⊗[R] κ →+* ↥(CurveModel.chartRing κ ({t} : Set L)) :=
  θFin.toRingHom.comp (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ).toRingHom

theorem θF_tmul (b : ↥(chartAlgFin R F j)) (x : κ) : θF θFin (b ⊗ₜ[R] x) = θFin (x ⊗ₜ[R] b) := by
  change θFin (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ (b ⊗ₜ[R] x)) = _
  rw [Algebra.TensorProduct.comm_tmul]

theorem θF_includeLeft :
    (θF θFin).comp Algebra.TensorProduct.includeLeftRingHom =
      θFin.toRingHom.comp (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom :=
  RingHom.ext fun b => θF_tmul θFin b 1

theorem θF_includeRight :
    (θF θFin).comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      κ →ₐ[R] ↥(chartAlgFin R F j) ⊗[R] κ)) = algebraMap κ ↥(CurveModel.chartRing κ ({t} : Set L)) := by
  refine RingHom.ext fun x => ?_
  change θF θFin ((1 : ↥(chartAlgFin R F j)) ⊗ₜ[R] x) = _
  rw [θF_tmul, ← mul_one x, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, smul_eq_mul, mul_one,
    ← Algebra.TensorProduct.one_def, map_one, Algebra.smul_def, mul_one]

abbrev PFin (_c : CurveModel.glued κ t ⟶ pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) :=
  pullback (ιFin R F j) (pullback.fst (toBase R F j) (baseMap R κ))

abbrev uFin : X₀ κ t ⟶ XFin R F j :=
  Spec.map (CommRingCat.ofHom (θFin.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom))

variable (hcFin : CurveModel.ι₀ κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
    Spec.map (CommRingCat.ofHom (θFin.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom)) ≫ ιFin R F j)

def φFin : X₀ κ t ⟶ PFin c :=
  pullback.lift (uFin θFin) (ι₀ κ t ≫ c) (by rw [Category.assoc]; exact hcFin.symm)

@[reassoc (attr := simp)]
theorem φFin_fst : φFin θFin c hcFin ≫ pullback.fst _ _ = uFin θFin := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem φFin_snd : φFin θFin c hcFin ≫ pullback.snd _ _ = ι₀ κ t ≫ c := pullback.lift_snd _ _ _

def isoFin : PFin c ≅ Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] κ)) :=
  pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (ιFin R F j) ≪≫
    pullback.congrHom (ιFin_toBase R F j) rfl ≪≫ pullbackSpecIso R ↥(chartAlgFin R F j) κ

variable (hc_over : c ≫ pullback.snd (toBase R F j) _ = CurveModel.gluedToBase κ t)

include hcFin hc_over

theorem SpecMap_θF_eq :
    Spec.map (CommRingCat.ofHom (θF θFin)) ≫ (pullbackSpecIso R ↥(chartAlgFin R F j) κ).inv =
      φFin θFin c hcFin ≫ (pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (ιFin R F j)).hom ≫
        (pullback.congrHom (ιFin_toBase R F j) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp, θF_includeLeft]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φFin_fst]
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [θF_includeRight]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φFin_snd_assoc]
    rw [hc_over, ι₀_gluedToBase]

theorem φFin_isoFin : φFin θFin c hcFin ≫ (isoFin c).hom = Spec.map (CommRingCat.ofHom (θF θFin)) := by
  calc φFin θFin c hcFin ≫ (isoFin c).hom
      = (φFin θFin c hcFin ≫ (pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (ιFin R F j)).hom ≫
          (pullback.congrHom (ιFin_toBase R F j) rfl).hom) ≫ (pullbackSpecIso R ↥(chartAlgFin R F j) κ).hom := by
        simp only [isoFin, Iso.trans_hom, Category.assoc]
    _ = (Spec.map (CommRingCat.ofHom (θF θFin)) ≫ (pullbackSpecIso R ↥(chartAlgFin R F j) κ).inv) ≫
          (pullbackSpecIso R ↥(chartAlgFin R F j) κ).hom := by rw [SpecMap_θF_eq θFin c hcFin hc_over]
    _ = Spec.map (CommRingCat.ofHom (θF θFin)) := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Fin

section Integral

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]
  (θFin : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t} : Set L)))
  (m : ℕ) (hm : 0 < m) (hj : ((θFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m)

include hm hj

theorem θF_jChartFin_tmul_one : θF θFin (jChartFin R F j ⊗ₜ[R] 1) = tChart κ t ^ m := by
  apply Subtype.ext
  rw [θF_tmul, hj, SubmonoidClass.coe_pow]
  rfl

theorem isIntegral_θF : (θF θFin).IsIntegral := by
  let i : κ →+* ↥(chartAlgFin R F j) ⊗[R] κ :=
    (Algebra.TensorProduct.includeRight (R := R) (A := ↥(chartAlgFin R F j)) (B := κ)).toRingHom
  let f : Polynomial κ →+* ↥(chartAlgFin R F j) ⊗[R] κ := Polynomial.eval₂RingHom i (jChartFin R F j ⊗ₜ[R] 1)
  let B : Type u := ↥(Algebra.adjoin κ ({t} : Set L))
  let tB : B := ⟨t, Algebra.subset_adjoin rfl⟩
  let g₁ : Polynomial κ →+* B := Polynomial.eval₂RingHom (algebraMap κ B) (tB ^ m)
  let g₂ : B →+* ↥(CurveModel.chartRing κ ({t} : Set L)) := algebraMap B _
  have hg₂ : g₂.IsIntegral := fun x => IsIntegralClosure.isIntegral (Algebra.adjoin κ ({t} : Set L)) L x
  have hg₁ : g₁.IsIntegral := by
    rintro ⟨y, hy⟩
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst hx
        refine ⟨Polynomial.X ^ m - Polynomial.C Polynomial.X, Polynomial.monic_X_pow_sub_C _ (Nat.pos_iff_ne_zero.mp hm), ?_⟩
        rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
        change tB ^ m - Polynomial.eval₂ (algebraMap κ B) (tB ^ m) Polynomial.X = 0
        rw [Polynomial.eval₂_X, sub_self]
    | algebraMap r =>
        have : (⟨algebraMap κ L r, Subalgebra.algebraMap_mem _ r⟩ : B) = g₁ (Polynomial.C r) := by
          apply Subtype.ext
          change algebraMap κ L r = ((Polynomial.eval₂ (algebraMap κ B) (tB ^ m) (Polynomial.C r) : B) : L)
          rw [Polynomial.eval₂_C]
          rfl
        rw [this]
        exact g₁.isIntegralElem_map
    | add x y hx hy ihx ihy => exact RingHom.IsIntegralElem.add g₁ ihx ihy
    | mul x y hx hy ihx ihy => exact RingHom.IsIntegralElem.mul (hx := ihx) (hy := ihy)
  have h12 : (g₂.comp g₁).IsIntegral := RingHom.IsIntegral.trans g₁ g₂ hg₁ hg₂
  have hcomp : (θF θFin).comp f = g₂.comp g₁ := by
    apply Polynomial.ringHom_ext
    · intro r
      change θF θFin (Polynomial.eval₂ i (jChartFin R F j ⊗ₜ[R] 1) (Polynomial.C r)) =
        g₂ (Polynomial.eval₂ (algebraMap κ B) (tB ^ m) (Polynomial.C r))
      rw [Polynomial.eval₂_C, Polynomial.eval₂_C]
      change θF θFin ((1 : ↥(chartAlgFin R F j)) ⊗ₜ[R] r) = algebraMap B ↥(CurveModel.chartRing κ ({t} : Set L)) (algebraMap κ B r)
      rw [show θF θFin ((1 : ↥(chartAlgFin R F j)) ⊗ₜ[R] r) = algebraMap κ _ r from
        RingHom.congr_fun (θF_includeRight θFin) r, ← IsScalarTower.algebraMap_apply]
    · change θF θFin (Polynomial.eval₂ i (jChartFin R F j ⊗ₜ[R] 1) Polynomial.X) =
        g₂ (Polynomial.eval₂ (algebraMap κ B) (tB ^ m) Polynomial.X)
      rw [Polynomial.eval₂_X, Polynomial.eval₂_X, θF_jChartFin_tmul_one θFin m hm hj, map_pow]
      rfl
  have hF : ((θF θFin).comp f).IsIntegral := hcomp ▸ h12
  exact RingHom.IsIntegral.tower_top (f := f) (g := θF θFin) hF

end Integral

section RangeFin

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]
  (θFin : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t} : Set L)))
  (m : ℕ) (hm : 0 < m) (hj : ((θFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m)
  (c : CurveModel.glued κ t ⟶ pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
  (hc_over : c ≫ pullback.snd (toBase R F j) _ = CurveModel.gluedToBase κ t)
  (hcFin : CurveModel.ι₀ κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
    Spec.map (CommRingCat.ofHom (θFin.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom)) ≫ ιFin R F j)
  (hmatch : ∀ y : ↥(CurveModel.glued κ t),
    (c ≫ pullback.fst (toBase R F j) _).base y ∈ Set.range (ιFin R F j).base ↔ y ∈ Set.range (CurveModel.ι₀ κ t).base)

include hmatch in

theorem snd_mem_range_iff_mem_range_φFin (z : ↥(PFin c)) :
    (pullback.snd (ιFin R F j) (pullback.fst (toBase R F j) (baseMap R κ))).base z ∈ Set.range c.base ↔
      z ∈ Set.range (φFin θFin c hcFin).base := by
  constructor
  · rintro ⟨y, hy⟩
    have hy' : (c ≫ pullback.fst (toBase R F j) (baseMap R κ)).base y ∈ Set.range (ιFin R F j).base := by
      refine ⟨(pullback.fst (ιFin R F j) _).base z, ?_⟩
      change _ = (c.base ≫ (pullback.fst (toBase R F j) (baseMap R κ)).base) y
      rw [TopCat.comp_app, hy]
      change (pullback.fst (ιFin R F j) _ ≫ ιFin R F j).base z =
        (pullback.snd (ιFin R F j) _ ≫ pullback.fst (toBase R F j) (baseMap R κ)).base z
      rw [pullback.condition]
    obtain ⟨x₀, rfl⟩ := (hmatch y).mp hy'
    refine ⟨x₀, (pullback.snd (ιFin R F j) (pullback.fst (toBase R F j) (baseMap R κ))).isOpenEmbedding.injective ?_⟩
    change (φFin θFin c hcFin ≫ pullback.snd _ _).base x₀ = _
    rw [φFin_snd]
    exact hy
  · rintro ⟨x₀, rfl⟩
    refine ⟨(ι₀ κ t).base x₀, ?_⟩
    change (ι₀ κ t ≫ c).base x₀ = (φFin θFin c hcFin ≫ pullback.snd _ _).base x₀
    rw [φFin_snd]

include hm hj hc_over in

theorem mem_range_φFin_iff (z : ↥(PFin c)) :
    z ∈ Set.range (φFin θFin c hcFin).base ↔ RingHom.ker (θF θFin) ≤ ((isoFin c).hom.base z).asIdeal := by
  have hbij := (isoFin c).hom.homeomorph.injective
  constructor
  · rintro ⟨x₀, rfl⟩
    have : (isoFin c).hom.base ((φFin θFin c hcFin).base x₀) = (Spec.map (CommRingCat.ofHom (θF θFin))).base x₀ := by
      change (φFin θFin c hcFin ≫ (isoFin c).hom).base x₀ = _
      rw [φFin_isoFin θFin c hcFin hc_over]
    rw [this]
    change RingHom.ker (θF θFin) ≤ (x₀.asIdeal.comap (θF θFin))
    exact fun a ha => by simp [Ideal.mem_comap, RingHom.mem_ker.mp ha]
  · intro h
    have hz : (isoFin c).hom.base z ∈ Set.range (Spec.map (CommRingCat.ofHom (θF θFin))).base := by
      change (isoFin c).hom.base z ∈ Set.range (PrimeSpectrum.comap (θF θFin))
      rw [PrimeSpectrum.range_comap_eq_zeroLocus_ker_of_isIntegral _ (isIntegral_θF θFin m hm hj)]
      exact h
    obtain ⟨x₀, hx₀⟩ := hz
    refine ⟨x₀, hbij ?_⟩
    change (φFin θFin c hcFin ≫ (isoFin c).hom).base x₀ = _
    rw [φFin_isoFin θFin c hcFin hc_over]
    exact hx₀

end RangeFin

section Inf

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]
  (θInf : κ ⊗[R] ↥(chartAlgInf R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t⁻¹} : Set L)))
  (c : CurveModel.glued κ t ⟶ pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))

abbrev θI : ↥(chartAlgInf R F j) ⊗[R] κ →+* ↥(CurveModel.chartRing κ ({t⁻¹} : Set L)) :=
  θInf.toRingHom.comp (Algebra.TensorProduct.comm R ↥(chartAlgInf R F j) κ).toRingHom

theorem θI_tmul (b : ↥(chartAlgInf R F j)) (x : κ) : θI θInf (b ⊗ₜ[R] x) = θInf (x ⊗ₜ[R] b) := by
  change θInf (Algebra.TensorProduct.comm R ↥(chartAlgInf R F j) κ (b ⊗ₜ[R] x)) = _
  rw [Algebra.TensorProduct.comm_tmul]

theorem θI_includeLeft :
    (θI θInf).comp Algebra.TensorProduct.includeLeftRingHom =
      θInf.toRingHom.comp (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom :=
  RingHom.ext fun b => θI_tmul θInf b 1

theorem θI_includeRight :
    (θI θInf).comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      κ →ₐ[R] ↥(chartAlgInf R F j) ⊗[R] κ)) = algebraMap κ ↥(CurveModel.chartRing κ ({t⁻¹} : Set L)) := by
  refine RingHom.ext fun x => ?_
  change θI θInf ((1 : ↥(chartAlgInf R F j)) ⊗ₜ[R] x) = _
  rw [θI_tmul, ← mul_one x, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, smul_eq_mul, mul_one,
    ← Algebra.TensorProduct.one_def, map_one, Algebra.smul_def, mul_one]

abbrev PInf (_c : CurveModel.glued κ t ⟶ pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) :=
  pullback (TwoChartIntegralModel.ιInf R F j) (pullback.fst (toBase R F j) (baseMap R κ))

abbrev uInf : CurveModel.XInf κ t ⟶ TwoChartIntegralModel.XInf R F j :=
  Spec.map (CommRingCat.ofHom (θInf.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom))

variable (hcInf : CurveModel.ιInf κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
    Spec.map (CommRingCat.ofHom (θInf.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom)) ≫ TwoChartIntegralModel.ιInf R F j)

def φInf : CurveModel.XInf κ t ⟶ PInf c :=
  pullback.lift (uInf θInf) (CurveModel.ιInf κ t ≫ c) (by rw [Category.assoc]; exact hcInf.symm)

@[reassoc (attr := simp)]
theorem φInf_fst : φInf θInf c hcInf ≫ pullback.fst _ _ = uInf θInf := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem φInf_snd : φInf θInf c hcInf ≫ pullback.snd _ _ = CurveModel.ιInf κ t ≫ c := pullback.lift_snd _ _ _

def isoInf : PInf c ≅ Spec (CommRingCat.of (↥(chartAlgInf R F j) ⊗[R] κ)) :=
  pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (TwoChartIntegralModel.ιInf R F j) ≪≫
    pullback.congrHom (ιInf_toBase R F j) rfl ≪≫ pullbackSpecIso R ↥(chartAlgInf R F j) κ

variable (hc_over : c ≫ pullback.snd (toBase R F j) _ = CurveModel.gluedToBase κ t)

include hcInf hc_over

theorem SpecMap_θI_eq :
    Spec.map (CommRingCat.ofHom (θI θInf)) ≫ (pullbackSpecIso R ↥(chartAlgInf R F j) κ).inv =
      φInf θInf c hcInf ≫ (pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (TwoChartIntegralModel.ιInf R F j)).hom ≫
        (pullback.congrHom (ιInf_toBase R F j) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp, θI_includeLeft]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φInf_fst]
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [θI_includeRight]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φInf_snd_assoc]
    rw [hc_over, ιInf_gluedToBase]

theorem φInf_isoInf : φInf θInf c hcInf ≫ (isoInf c).hom = Spec.map (CommRingCat.ofHom (θI θInf)) := by
  calc φInf θInf c hcInf ≫ (isoInf c).hom
      = (φInf θInf c hcInf ≫ (pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (TwoChartIntegralModel.ιInf R F j)).hom ≫
          (pullback.congrHom (ιInf_toBase R F j) rfl).hom) ≫ (pullbackSpecIso R ↥(chartAlgInf R F j) κ).hom := by
        simp only [isoInf, Iso.trans_hom, Category.assoc]
    _ = (Spec.map (CommRingCat.ofHom (θI θInf)) ≫ (pullbackSpecIso R ↥(chartAlgInf R F j) κ).inv) ≫
          (pullbackSpecIso R ↥(chartAlgInf R F j) κ).hom := by rw [SpecMap_θI_eq θInf c hcInf hc_over]
    _ = Spec.map (CommRingCat.ofHom (θI θInf)) := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Inf

section IntegralInf

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]
  (θInf : κ ⊗[R] ↥(chartAlgInf R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t⁻¹} : Set L)))
  (m : ℕ) (hm : 0 < m) (hjInv : ((θInf ((1 : κ) ⊗ₜ[R] jInvChartInf R F j)) : L) = t⁻¹ ^ m)

include hm hjInv

theorem θI_jInvChartInf_tmul_one : θI θInf (jInvChartInf R F j ⊗ₜ[R] 1) = tInvChart κ t ^ m := by
  apply Subtype.ext
  rw [θI_tmul, hjInv, SubmonoidClass.coe_pow]
  rfl

theorem isIntegral_θI : (θI θInf).IsIntegral := by
  let i : κ →+* ↥(chartAlgInf R F j) ⊗[R] κ :=
    (Algebra.TensorProduct.includeRight (R := R) (A := ↥(chartAlgInf R F j)) (B := κ)).toRingHom
  let f : Polynomial κ →+* ↥(chartAlgInf R F j) ⊗[R] κ := Polynomial.eval₂RingHom i (jInvChartInf R F j ⊗ₜ[R] 1)
  let B : Type u := ↥(Algebra.adjoin κ ({t⁻¹} : Set L))
  let tB : B := ⟨t⁻¹, Algebra.subset_adjoin rfl⟩
  let g₁ : Polynomial κ →+* B := Polynomial.eval₂RingHom (algebraMap κ B) (tB ^ m)
  let g₂ : B →+* ↥(CurveModel.chartRing κ ({t⁻¹} : Set L)) := algebraMap B _
  have hg₂ : g₂.IsIntegral := fun x => IsIntegralClosure.isIntegral (Algebra.adjoin κ ({t⁻¹} : Set L)) L x
  have hg₁ : g₁.IsIntegral := by
    rintro ⟨y, hy⟩
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst hx
        refine ⟨Polynomial.X ^ m - Polynomial.C Polynomial.X, Polynomial.monic_X_pow_sub_C _ (Nat.pos_iff_ne_zero.mp hm), ?_⟩
        rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
        change tB ^ m - Polynomial.eval₂ (algebraMap κ B) (tB ^ m) Polynomial.X = 0
        rw [Polynomial.eval₂_X, sub_self]
    | algebraMap r =>
        have : (⟨algebraMap κ L r, Subalgebra.algebraMap_mem _ r⟩ : B) = g₁ (Polynomial.C r) := by
          apply Subtype.ext
          change algebraMap κ L r = ((Polynomial.eval₂ (algebraMap κ B) (tB ^ m) (Polynomial.C r) : B) : L)
          rw [Polynomial.eval₂_C]
          rfl
        rw [this]
        exact g₁.isIntegralElem_map
    | add x y hx hy ihx ihy => exact RingHom.IsIntegralElem.add g₁ ihx ihy
    | mul x y hx hy ihx ihy => exact RingHom.IsIntegralElem.mul (hx := ihx) (hy := ihy)
  have h12 : (g₂.comp g₁).IsIntegral := RingHom.IsIntegral.trans g₁ g₂ hg₁ hg₂
  have hcomp : (θI θInf).comp f = g₂.comp g₁ := by
    apply Polynomial.ringHom_ext
    · intro r
      change θI θInf (Polynomial.eval₂ i (jInvChartInf R F j ⊗ₜ[R] 1) (Polynomial.C r)) =
        g₂ (Polynomial.eval₂ (algebraMap κ B) (tB ^ m) (Polynomial.C r))
      rw [Polynomial.eval₂_C, Polynomial.eval₂_C]
      change θI θInf ((1 : ↥(chartAlgInf R F j)) ⊗ₜ[R] r) = algebraMap B ↥(CurveModel.chartRing κ ({t⁻¹} : Set L)) (algebraMap κ B r)
      rw [show θI θInf ((1 : ↥(chartAlgInf R F j)) ⊗ₜ[R] r) = algebraMap κ _ r from
        RingHom.congr_fun (θI_includeRight θInf) r, ← IsScalarTower.algebraMap_apply]
    · change θI θInf (Polynomial.eval₂ i (jInvChartInf R F j ⊗ₜ[R] 1) Polynomial.X) =
        g₂ (Polynomial.eval₂ (algebraMap κ B) (tB ^ m) Polynomial.X)
      rw [Polynomial.eval₂_X, Polynomial.eval₂_X, θI_jInvChartInf_tmul_one θInf m hm hjInv, map_pow]
      rfl
  have hF : ((θI θInf).comp f).IsIntegral := hcomp ▸ h12
  exact RingHom.IsIntegral.tower_top (f := f) (g := θI θInf) hF

end IntegralInf

section RangeInf

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]
  (θInf : κ ⊗[R] ↥(chartAlgInf R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t⁻¹} : Set L)))
  (m : ℕ) (hm : 0 < m) (hjInv : ((θInf ((1 : κ) ⊗ₜ[R] jInvChartInf R F j)) : L) = t⁻¹ ^ m)
  (c : CurveModel.glued κ t ⟶ pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
  (hc_over : c ≫ pullback.snd (toBase R F j) _ = CurveModel.gluedToBase κ t)
  (hcInf : CurveModel.ιInf κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
    Spec.map (CommRingCat.ofHom (θInf.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom)) ≫ TwoChartIntegralModel.ιInf R F j)
  (hmatchInf : ∀ y : ↥(CurveModel.glued κ t),
    (c ≫ pullback.fst (toBase R F j) _).base y ∈ Set.range (TwoChartIntegralModel.ιInf R F j).base ↔ y ∈ Set.range (CurveModel.ιInf κ t).base)

include hmatchInf in

theorem snd_mem_range_iff_mem_range_φInf (z : ↥(PInf c)) :
    (pullback.snd (TwoChartIntegralModel.ιInf R F j) (pullback.fst (toBase R F j) (baseMap R κ))).base z ∈ Set.range c.base ↔
      z ∈ Set.range (φInf θInf c hcInf).base := by
  constructor
  · rintro ⟨y, hy⟩
    have hy' : (c ≫ pullback.fst (toBase R F j) (baseMap R κ)).base y ∈ Set.range (TwoChartIntegralModel.ιInf R F j).base := by
      refine ⟨(pullback.fst (TwoChartIntegralModel.ιInf R F j) _).base z, ?_⟩
      change _ = (c.base ≫ (pullback.fst (toBase R F j) (baseMap R κ)).base) y
      rw [TopCat.comp_app, hy]
      change (pullback.fst (TwoChartIntegralModel.ιInf R F j) _ ≫ TwoChartIntegralModel.ιInf R F j).base z =
        (pullback.snd (TwoChartIntegralModel.ιInf R F j) _ ≫ pullback.fst (toBase R F j) (baseMap R κ)).base z
      rw [pullback.condition]
    obtain ⟨x₀, rfl⟩ := (hmatchInf y).mp hy'
    refine ⟨x₀, (pullback.snd (TwoChartIntegralModel.ιInf R F j) (pullback.fst (toBase R F j) (baseMap R κ))).isOpenEmbedding.injective ?_⟩
    change (φInf θInf c hcInf ≫ pullback.snd _ _).base x₀ = _
    rw [φInf_snd]
    exact hy
  · rintro ⟨x₀, rfl⟩
    refine ⟨(CurveModel.ιInf κ t).base x₀, ?_⟩
    change (CurveModel.ιInf κ t ≫ c).base x₀ = (φInf θInf c hcInf ≫ pullback.snd _ _).base x₀
    rw [φInf_snd]

include hm hjInv hc_over in

theorem mem_range_φInf_iff (z : ↥(PInf c)) :
    z ∈ Set.range (φInf θInf c hcInf).base ↔ RingHom.ker (θI θInf) ≤ ((isoInf c).hom.base z).asIdeal := by
  have hbij := (isoInf c).hom.homeomorph.injective
  constructor
  · rintro ⟨x₀, rfl⟩
    have : (isoInf c).hom.base ((φInf θInf c hcInf).base x₀) = (Spec.map (CommRingCat.ofHom (θI θInf))).base x₀ := by
      change (φInf θInf c hcInf ≫ (isoInf c).hom).base x₀ = _
      rw [φInf_isoInf θInf c hcInf hc_over]
    rw [this]
    change RingHom.ker (θI θInf) ≤ (x₀.asIdeal.comap (θI θInf))
    exact fun a ha => by simp [Ideal.mem_comap, RingHom.mem_ker.mp ha]
  · intro h
    have hz : (isoInf c).hom.base z ∈ Set.range (Spec.map (CommRingCat.ofHom (θI θInf))).base := by
      change (isoInf c).hom.base z ∈ Set.range (PrimeSpectrum.comap (θI θInf))
      rw [PrimeSpectrum.range_comap_eq_zeroLocus_ker_of_isIntegral _ (isIntegral_θI θInf m hm hjInv)]
      exact h
    obtain ⟨x₀, hx₀⟩ := hz
    refine ⟨x₀, hbij ?_⟩
    change (φInf θInf c hcInf ≫ (isoInf c).hom).base x₀ = _
    rw [φInf_isoInf θInf c hcInf hc_over]
    exact hx₀

end RangeInf

section Match

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]
  (θFin : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t} : Set L)))
  (θInf : κ ⊗[R] ↥(chartAlgInf R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t⁻¹} : Set L)))
  (m : ℕ) (hm : 0 < m) (hj : ((θFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m)
  (c : CurveModel.glued κ t ⟶ pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
  (hcFin : CurveModel.ι₀ κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
    Spec.map (CommRingCat.ofHom (θFin.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom)) ≫ ιFin R F j)
  (hcInf : CurveModel.ιInf κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
    Spec.map (CommRingCat.ofHom (θInf.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom)) ≫
      TwoChartIntegralModel.ιInf R F j)
  (hmatch : ∀ y : ↥(CurveModel.glued κ t),
    (c ≫ pullback.fst (toBase R F j) _).base y ∈ Set.range (ιFin R F j).base ↔ y ∈ Set.range (CurveModel.ι₀ κ t).base)

include hm hj hcFin hcInf in
theorem fst_mem_range_ιInf_iff (y : ↥(CurveModel.glued κ t)) :
    (c ≫ pullback.fst (toBase R F j) _).base y ∈ Set.range (TwoChartIntegralModel.ιInf R F j).base ↔
      y ∈ Set.range (CurveModel.ιInf κ t).base := by
  constructor
  · intro hy
    rcases CurveModel.mem_range_ι₀_or_mem_range_ιInf κ t y with ⟨x₀, rfl⟩ | h'
    · by_contra hne
      have ht : tChart κ t ∈ x₀.asIdeal := by
        by_contra ht
        exact hne ((CurveModel.ι₀_mem_range_ιInf_iff κ t x₀).mpr ht)
      have h1 : (c ≫ pullback.fst (toBase R F j) _).base ((CurveModel.ι₀ κ t).base x₀) =
          (ιFin R F j).base ((uFin θFin).base x₀) := by
        change (CurveModel.ι₀ κ t ≫ c ≫ pullback.fst (toBase R F j) _).base x₀ = (uFin θFin ≫ ιFin R F j).base x₀
        rw [hcFin]
      rw [h1] at hy
      refine (tc_ιFin_mem_range_ιInf_iff R F j _).mp hy ?_
      change (θFin.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom)
          (jChartFin R F j) ∈ x₀.asIdeal
      have : (θFin.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom)
            (jChartFin R F j) = tChart κ t ^ m := by
        apply Subtype.ext
        change ((θFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = _
        rw [hj, SubmonoidClass.coe_pow]
        rfl
      rw [this]
      exact Ideal.pow_mem_of_mem _ ht m hm
    · exact h'
  · rintro ⟨xi, rfl⟩
    refine ⟨(uInf θInf).base xi, ?_⟩
    change (uInf θInf ≫ TwoChartIntegralModel.ιInf R F j).base xi =
      (CurveModel.ιInf κ t ≫ c ≫ pullback.fst (toBase R F j) _).base xi
    rw [hcInf]

end Match

end RangeChartK12

open RangeChartK12 AlgebraicCurve.TwoChartIntegralModel in
theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (κ : Type u) [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] (t : L) [Fact (t ≠ 0)]
    (m : ℕ) (hm : 0 < m)
    (θFin : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t} : Set L)))
    (θInf : κ ⊗[R] ↥(chartAlgInf R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t⁻¹} : Set L)))
    (hj : ((θFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m)
    (hjInv : ((θInf ((1 : κ) ⊗ₜ[R] jInvChartInf R F j)) : L) = t⁻¹ ^ m)
    (c : CurveModel.glued κ t ⟶ pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hc_over : c ≫ pullback.snd (toBase R F j) _ = CurveModel.gluedToBase κ t)
    (hcFin : CurveModel.ι₀ κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (θFin.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom)) ≫
          ιFin R F j)
    (hcInf : CurveModel.ιInf κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (θInf.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom)) ≫
          ιInf R F j)
    (hmatch : ∀ y : ↥(CurveModel.glued κ t),
        (c ≫ pullback.fst (toBase R F j) _).base y ∈ Set.range (ιFin R F j).base ↔
          y ∈ Set.range (CurveModel.ι₀ κ t).base) :
    (∀ z : ↥(pullback (ιFin R F j) (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))),
        (pullback.snd (ιFin R F j) _).base z ∈ Set.range c.base ↔
          RingHom.ker (θFin.toRingHom.comp
              (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ).toRingHom) ≤
            ((pullbackRightPullbackFstIso (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ιFin R F j) ≪≫
                pullback.congrHom (ιFin_toBase R F j) rfl ≪≫
                pullbackSpecIso R ↥(chartAlgFin R F j) κ).hom.base z).asIdeal) ∧
    (∀ z : ↥(pullback (ιInf R F j) (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))),
        (pullback.snd (ιInf R F j) _).base z ∈ Set.range c.base ↔
          RingHom.ker (θInf.toRingHom.comp
              (Algebra.TensorProduct.comm R ↥(chartAlgInf R F j) κ).toRingHom) ≤
            ((pullbackRightPullbackFstIso (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ιInf R F j) ≪≫
                pullback.congrHom (ιInf_toBase R F j) rfl ≪≫
                pullbackSpecIso R ↥(chartAlgInf R F j) κ).hom.base z).asIdeal) := by
  refine ⟨fun z => ?_, fun z => ?_⟩
  · exact (snd_mem_range_iff_mem_range_φFin θFin c hcFin hmatch z).trans
      (mem_range_φFin_iff θFin m hm hj c hc_over hcFin z)
  · exact (snd_mem_range_iff_mem_range_φInf θInf c hcInf
        (fst_mem_range_ιInf_iff θFin θInf m hm hj c hcFin hcInf) z).trans
      (mem_range_φInf_iff θInf m hm hjInv c hc_over hcInf z)

end

#print axioms solution

end S_AlgebraicCurve_TwoChartIntegralModel_mem_range_glued_hom_iff_ker_le_of_chart_eq
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_glued_hom_iff_ker_le_of_chart_eq (solution)
