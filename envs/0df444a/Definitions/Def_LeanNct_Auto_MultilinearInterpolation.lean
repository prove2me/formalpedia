-- Prove2me | Definitions.Def_LeanNct_Auto_MultilinearInterpolation
-- name    : LeanNct_Auto_MultilinearInterpolation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:42:51.30489+00:00
-- url     : https://prove2.me/theorems/48215aaa-a513-4184-86d1-447e55a7ae0c
-- title:
--   Multilinear Interpolation
-- statement:
--   Definitions and structural lemmas for Multilinear Interpolation, from Floris van Doorn, Polona Durcik, Joris Roos, Lenka Slavíková, Christoph Thiele (roos-j/lean-nct; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Norm-variation of multiple ergodic averages for commuting transformations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean

module
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
namespace Auto
noncomputable def aux_multilinear_input_deformation
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (p₀ p₁ p : Fin (m + 1) → ENNReal) (g : Fin m → SimpleFunc X ℂ)
    (z : ℂ) (i : Fin m) : SimpleFunc X ℂ :=
  (g i).map (fun c ↦ if c = 0 then 0 else
    c / (‖c‖ : ℂ) * Complex.exp
      (((((p i.succ).toReal * ((p₁ i.succ)⁻¹).toReal -
            (p i.succ).toReal * ((p₀ i.succ)⁻¹).toReal : ℝ) : ℂ) * z +
          ((p i.succ).toReal * ((p₀ i.succ)⁻¹).toReal : ℝ) : ℂ) *
        ((Real.log ‖c‖ : ℝ) : ℂ)))
noncomputable def multilinearExponentOfReciprocal
    {m : ℕ} (u : Fin (m + 1) → ℝ) : Fin (m + 1) → ENNReal :=
  fun i ↦ ENNReal.ofReal ((u i)⁻¹)
def aux_stronglyMeasurableSubmodule {Y : Type*} [MeasurableSpace Y] :
    Submodule ℂ (Y → ℂ) where
  carrier := {f | StronglyMeasurable f}
  zero_mem' := stronglyMeasurable_zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _f hf := hf.const_smul c
noncomputable def aux_aeeqFunMkLinear {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} :
    aux_stronglyMeasurableSubmodule (Y := Y) →ₗ[ℂ] (Y →ₘ[ν] ℂ) where
  toFun f := AEEqFun.mk f f.property.aestronglyMeasurable
  map_add' f g := by
    have hf : StronglyMeasurable (f : Y → ℂ) := by
      simpa [aux_stronglyMeasurableSubmodule] using f.property
    have hg : StronglyMeasurable (g : Y → ℂ) := by
      simpa [aux_stronglyMeasurableSubmodule] using g.property
    have hfg : StronglyMeasurable
        ((f + g : aux_stronglyMeasurableSubmodule (Y := Y)) : Y → ℂ) := by
      change StronglyMeasurable ((f : Y → ℂ) + (g : Y → ℂ))
      exact hf.add hg
    change AEEqFun.mk ((f + g : aux_stronglyMeasurableSubmodule (Y := Y)) : Y → ℂ)
      hfg.aestronglyMeasurable =
        AEEqFun.mk (f : Y → ℂ) hf.aestronglyMeasurable +
          AEEqFun.mk (g : Y → ℂ) hg.aestronglyMeasurable
    simpa only [Submodule.coe_add] using
      (AEEqFun.mk_add_mk (f : Y → ℂ) (g : Y → ℂ) hf.aestronglyMeasurable
        hg.aestronglyMeasurable).symm
  map_smul' c f := by
    have hf : StronglyMeasurable (f : Y → ℂ) := by
      simpa [aux_stronglyMeasurableSubmodule] using f.property
    have hcf : StronglyMeasurable
        ((c • f : aux_stronglyMeasurableSubmodule (Y := Y)) : Y → ℂ) := by
      change StronglyMeasurable (c • (f : Y → ℂ))
      exact hf.const_smul c
    change AEEqFun.mk ((c • f : aux_stronglyMeasurableSubmodule (Y := Y)) : Y → ℂ)
      hcf.aestronglyMeasurable = c • AEEqFun.mk (f : Y → ℂ) hf.aestronglyMeasurable
    simpa only [Submodule.coe_smul] using
      (AEEqFun.smul_mk c (f : Y → ℂ) hf.aestronglyMeasurable).symm
theorem aux_aeeqFunMkLinear_surjective {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} : Function.Surjective
    (aux_aeeqFunMkLinear (Y := Y) (ν := ν)) := by
  intro h
  refine ⟨⟨(h : Y → ℂ), h.stronglyMeasurable⟩, ?_⟩
  exact AEEqFun.mk_coeFn h
noncomputable def aux_aeeqFunLinearRepresentative {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} : (Y →ₘ[ν] ℂ) →ₗ[ℂ]
    aux_stronglyMeasurableSubmodule (Y := Y) :=
  Classical.choose <|
    (aux_aeeqFunMkLinear (Y := Y) (ν := ν)).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top_of_surjective _
        (aux_aeeqFunMkLinear_surjective (Y := Y) (ν := ν)))
noncomputable def aux_lpAEEqFunRepresentative {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} : Lp ℂ 2 ν →ₗ[ℂ]
    aux_stronglyMeasurableSubmodule (Y := Y) :=
  (aux_aeeqFunLinearRepresentative (Y := Y) (ν := ν)).comp
    (Lp.LpSubmodule ℂ ℂ 2 ν).subtype
noncomputable def aux_lpLinearRepresentative {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} : Lp ℂ 2 ν →ₗ[ℂ] (Y → ℂ) :=
  ((aux_stronglyMeasurableSubmodule (Y := Y)).subtype).comp
    (aux_lpAEEqFunRepresentative (Y := Y) (ν := ν))
theorem aux_lpLinearRepresentative_stronglyMeasurable {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} (f : Lp ℂ 2 ν) :
    StronglyMeasurable (aux_lpLinearRepresentative (Y := Y) (ν := ν) f) := by
  exact (aux_lpAEEqFunRepresentative (Y := Y) (ν := ν) f).property
noncomputable def aux_multilinearLpRepresentative {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommMonoid (E i)] [∀ i, Module ℂ (E i)] {Y : Type*}
    [MeasurableSpace Y] {ν : Measure Y}
    (B : MultilinearMap ℂ E (Lp ℂ 2 ν)) : MultilinearMap ℂ E (Y → ℂ) :=
  (aux_lpLinearRepresentative (Y := Y) (ν := ν)).compMultilinearMap B
section
noncomputable def aux_simpleFuncMemLpSubmodule {X : Type*} [MeasurableSpace X]
    (p : ℝ≥0∞) (μ : Measure X) : Submodule ℂ (SimpleFunc X ℂ) where
  carrier := {f | MemLp (f : X → ℂ) p μ}
  zero_mem' := by
    change MemLp (0 : X → ℂ) p μ
    exact MemLp.zero
  add_mem' hf hg := by
    change MemLp (((↑) : SimpleFunc X ℂ → X → ℂ) (_ + _)) p μ
    simpa only [SimpleFunc.coe_add] using hf.add hg
  smul_mem' c f hf := by
    change MemLp (((↑) : SimpleFunc X ℂ → X → ℂ) (c • _)) p μ
    simpa only [SimpleFunc.coe_smul] using hf.const_smul c
noncomputable def aux_simpleFuncMemLpRetract {X : Type*} [MeasurableSpace X]
    (p : ℝ≥0∞) (μ : Measure X) :
    SimpleFunc X ℂ →ₗ[ℂ] aux_simpleFuncMemLpSubmodule p μ :=
  (aux_simpleFuncMemLpSubmodule p μ).subtype.leftInverse
noncomputable def aux_simpleFuncMemLpToLp {X : Type*} [MeasurableSpace X]
    (p : ℝ≥0∞) (μ : Measure X) :
    aux_simpleFuncMemLpSubmodule p μ →ₗ[ℂ] Lp ℂ p μ where
  toFun f := f.property.toLp (f : X → ℂ)
  map_add' f g := by
    change (f + g).property.toLp ((f + g :
      aux_simpleFuncMemLpSubmodule p μ) : X → ℂ) =
      f.property.toLp (f : X → ℂ) + g.property.toLp (g : X → ℂ)
    exact MemLp.toLp_add f.property g.property
  map_smul' c f := by
    change (c • f).property.toLp ((c • f :
      aux_simpleFuncMemLpSubmodule p μ) : X → ℂ) =
      c • f.property.toLp (f : X → ℂ)
    exact MemLp.toLp_const_smul c f.property
noncomputable def aux_extendLpCMLMToSimpleFunc {ι X F : Type*}
    [Fintype ι] [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (p : ι → ℝ≥0∞) (μ : Measure X) [∀ i, Fact (1 ≤ p i)]
    (B : ContinuousMultilinearMap ℂ (fun i ↦ Lp ℂ (p i) μ) F) :
    MultilinearMap ℂ (fun _ : ι ↦ SimpleFunc X ℂ) F :=
  B.toMultilinearMap.compLinearMap fun i ↦
    (aux_simpleFuncMemLpToLp (p i) μ).comp
      (aux_simpleFuncMemLpRetract (p i) μ)
noncomputable abbrev aux_integrableSimpleFuncSubmodule {X : Type*} [MeasurableSpace X]
    (μ : Measure X) : Submodule ℂ (SimpleFunc X ℂ) :=
  aux_simpleFuncMemLpSubmodule 1 μ
noncomputable def aux_integrableSimpleFuncRetract {X : Type*} [MeasurableSpace X]
    (μ : Measure X) :
    SimpleFunc X ℂ →ₗ[ℂ] aux_integrableSimpleFuncSubmodule μ :=
  aux_simpleFuncMemLpRetract 1 μ
theorem aux_simpleFuncExponent_ne_zero {p : ENNReal} [Fact (1 ≤ p)] : p ≠ 0 := by
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
noncomputable def aux_integrableSimpleFuncToMemLp {X : Type*} [MeasurableSpace X]
    (p : ENNReal) (μ : Measure X) [Fact (1 ≤ p)] (hp_top : p ≠ ∞) :
    aux_integrableSimpleFuncSubmodule μ →ₗ[ℂ] aux_simpleFuncMemLpSubmodule p μ where
  toFun f := ⟨f, (SimpleFunc.memLp_iff_integrable
    (aux_simpleFuncExponent_ne_zero (p := p)) hp_top).mpr
    (memLp_one_iff_integrable.mp f.property)⟩
  map_add' f g := by
    apply Subtype.ext
    rfl
  map_smul' c f := by
    apply Subtype.ext
    rfl
noncomputable def aux_integrableSimpleFuncToLp {X : Type*} [MeasurableSpace X]
    (p : ENNReal) (μ : Measure X) [Fact (1 ≤ p)] (hp_top : p ≠ ∞) :
    aux_integrableSimpleFuncSubmodule μ →ₗ[ℂ] Lp ℂ p μ :=
  (aux_simpleFuncMemLpToLp p μ).comp (aux_integrableSimpleFuncToMemLp p μ hp_top)
noncomputable def aux_extendLpCMLMToSimpleFuncIntegrable {ι X F : Type*}
    [Fintype ι] [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (p : ι → ENNReal) (μ : Measure X) [∀ i, Fact (1 ≤ p i)]
    (hp_top : ∀ i, p i ≠ ∞)
    (B : ContinuousMultilinearMap ℂ (fun i ↦ Lp ℂ (p i) μ) F) :
    MultilinearMap ℂ (fun _ : ι ↦ SimpleFunc X ℂ) F :=
  B.toMultilinearMap.compLinearMap fun i ↦
    (aux_integrableSimpleFuncToLp (p i) μ (hp_top i)).comp
      (aux_integrableSimpleFuncRetract μ)
noncomputable def aux_lpStrongRepresentative
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : Lp ℂ 2 μ) : X → ℂ :=
  (Lp.memLp f).aestronglyMeasurable.mk (f : X → ℂ)
theorem aux_lpStrongRepresentative_stronglyMeasurable
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : Lp ℂ 2 μ) : StronglyMeasurable (aux_lpStrongRepresentative f) := by
  exact (Lp.memLp f).aestronglyMeasurable.stronglyMeasurable_mk
theorem aux_lpStrongRepresentative_ae_eq
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : Lp ℂ 2 μ) : (f : X → ℂ) =ᵐ[μ] aux_lpStrongRepresentative f := by
  exact (Lp.memLp f).aestronglyMeasurable.ae_eq_mk
noncomputable def aux_packLpFun
    {J : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : Fin J → Lp ℂ 2 μ) : Fin J × X → ℂ :=
  fun z ↦ aux_lpStrongRepresentative (u z.1) z.2
theorem aux_packLpFun_stronglyMeasurable
    {J : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : Fin J → Lp ℂ 2 μ) : StronglyMeasurable (aux_packLpFun u) := by
  unfold aux_packLpFun
  change StronglyMeasurable (Function.uncurry fun j x ↦ aux_lpStrongRepresentative (u j) x)
  apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
  · intro x
    exact continuous_of_discreteTopology
  · intro j
    exact aux_lpStrongRepresentative_stronglyMeasurable (u j)
theorem aux_eLpNorm_two_sq_eq_lintegral {X E : Type*} [MeasurableSpace X] [ENorm E]
    {μ : Measure X} (F : X → E) :
    eLpNorm F 2 μ ^ 2 = ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
theorem aux_eLpNorm_sq_pack {J : ℕ} {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure X} [SFinite μ]
    (F : Fin J → X → E)
    (hF : AEMeasurable (fun z : Fin J × X ↦ F z.1 z.2)
      ((Measure.count : Measure (Fin J)).prod μ)) :
    eLpNorm (fun z : Fin J × X ↦ F z.1 z.2) 2
        ((Measure.count : Measure (Fin J)).prod μ) ^ 2 =
      ∑ j : Fin J, eLpNorm (F j) 2 μ ^ 2 := by
  rw [aux_eLpNorm_two_sq_eq_lintegral]
  have hpow : AEMeasurable (fun z : Fin J × X ↦ ‖F z.1 z.2‖ₑ ^ (2 : ℝ))
      ((Measure.count : Measure (Fin J)).prod μ) := by
    simpa only [ENNReal.rpow_two] using
      (hF.enorm.pow (measurable_const.aemeasurable :
        AEMeasurable (fun _ : Fin J × X ↦ (2 : ℝ))
          ((Measure.count : Measure (Fin J)).prod μ)))
  rw [lintegral_prod _ hpow]
  rw [lintegral_count, tsum_fintype]
  simp_rw [← aux_eLpNorm_two_sq_eq_lintegral]
theorem aux_eLpNorm_sq_packLpFun {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ] (u : Fin J → Lp ℂ 2 μ) :
    eLpNorm (aux_packLpFun u) 2 ((Measure.count : Measure (Fin J)).prod μ) ^ 2 =
      ∑ j : Fin J, eLpNorm (u j : X → ℂ) 2 μ ^ 2 := by
  calc
    eLpNorm (aux_packLpFun u) 2 ((Measure.count : Measure (Fin J)).prod μ) ^ 2 =
        ∑ j : Fin J, eLpNorm (aux_lpStrongRepresentative (u j)) 2 μ ^ 2 :=
      aux_eLpNorm_sq_pack (fun j ↦ aux_lpStrongRepresentative (u j))
        (aux_packLpFun_stronglyMeasurable u).aemeasurable
    _ = ∑ j : Fin J, eLpNorm (u j : X → ℂ) 2 μ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [eLpNorm_congr_ae (aux_lpStrongRepresentative_ae_eq (u j)).symm]
theorem aux_packLpFun_memLp {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ] (u : Fin J → Lp ℂ 2 μ) :
    MemLp (aux_packLpFun u) 2 ((Measure.count : Measure (Fin J)).prod μ) := by
  refine ⟨(aux_packLpFun_stronglyMeasurable u).aestronglyMeasurable, ?_⟩
  apply lt_top_iff_ne_top.mpr
  intro htop
  have hsumtop : ∑ j : Fin J, eLpNorm (u j : X → ℂ) 2 μ ^ 2 = ∞ := by
    rw [← aux_eLpNorm_sq_packLpFun u, htop]
    norm_num
  have hsumne : ∑ j : Fin J, eLpNorm (u j : X → ℂ) 2 μ ^ 2 ≠ ∞ := by
    apply ENNReal.sum_ne_top.mpr
    intro j _
    exact ENNReal.pow_ne_top (Lp.memLp (u j)).eLpNorm_ne_top
  exact hsumne hsumtop
theorem aux_packed_ae_eq_of_forall {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ] {f g : Fin J → X → ℂ}
    (hf : StronglyMeasurable (fun z : Fin J × X ↦ f z.1 z.2))
    (hg : StronglyMeasurable (fun z : Fin J × X ↦ g z.1 z.2))
    (hfg : ∀ j, f j =ᵐ[μ] g j) :
    (fun z : Fin J × X ↦ f z.1 z.2) =ᵐ[(Measure.count : Measure (Fin J)).prod μ]
      fun z ↦ g z.1 z.2 := by
  apply (MeasureTheory.Measure.ae_prod_iff_ae_ae (hf.measurableSet_eq_fun hg)).mpr
  filter_upwards [] with j
  exact hfg j
theorem aux_lpStrongRepresentative_add_ae {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (u v : Lp ℂ 2 μ) :
    aux_lpStrongRepresentative (u + v) =ᵐ[μ]
      aux_lpStrongRepresentative u + aux_lpStrongRepresentative v := by
  filter_upwards [aux_lpStrongRepresentative_ae_eq (u + v), Lp.coeFn_add u v,
    aux_lpStrongRepresentative_ae_eq u, aux_lpStrongRepresentative_ae_eq v] with x hsum hadd hu hv
  rw [← hsum, hadd]
  simpa only [Pi.add_apply] using congrArg₂ (· + ·) hu hv
theorem aux_lpStrongRepresentative_smul_ae {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (c : ℂ) (u : Lp ℂ 2 μ) :
    aux_lpStrongRepresentative (c • u) =ᵐ[μ]
      c • aux_lpStrongRepresentative u := by
  filter_upwards [aux_lpStrongRepresentative_ae_eq (c • u), Lp.coeFn_smul c u,
    aux_lpStrongRepresentative_ae_eq u] with x hcu hsmul hu
  rw [← hcu, hsmul]
  simpa only [Pi.smul_apply] using congrArg (c • ·) hu
theorem aux_packLpFun_add_ae {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ] (u v : Fin J → Lp ℂ 2 μ) :
    aux_packLpFun (u + v) =ᵐ[(Measure.count : Measure (Fin J)).prod μ]
      aux_packLpFun u + aux_packLpFun v := by
  exact aux_packed_ae_eq_of_forall
    (aux_packLpFun_stronglyMeasurable (u + v))
    ((aux_packLpFun_stronglyMeasurable u).add (aux_packLpFun_stronglyMeasurable v))
    (fun j ↦ by simpa [aux_packLpFun] using aux_lpStrongRepresentative_add_ae (u j) (v j))
theorem aux_packLpFun_smul_ae {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ] (c : ℂ) (u : Fin J → Lp ℂ 2 μ) :
    aux_packLpFun (c • u) =ᵐ[(Measure.count : Measure (Fin J)).prod μ]
      c • aux_packLpFun u := by
  exact aux_packed_ae_eq_of_forall
    (aux_packLpFun_stronglyMeasurable (c • u))
    ((aux_packLpFun_stronglyMeasurable u).const_smul c)
    (fun j ↦ by simpa [aux_packLpFun] using aux_lpStrongRepresentative_smul_ae c (u j))
noncomputable def aux_packLpLinearMap {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ] :
    (Fin J → Lp ℂ 2 μ) →ₗ[ℂ] Lp ℂ 2 ((Measure.count : Measure (Fin J)).prod μ) where
  toFun u := (aux_packLpFun_memLp u).toLp (aux_packLpFun u)
  map_add' u v := by
    calc
      (aux_packLpFun_memLp (u + v)).toLp (aux_packLpFun (u + v)) =
          ((aux_packLpFun_memLp u).add (aux_packLpFun_memLp v)).toLp
            (aux_packLpFun u + aux_packLpFun v) :=
        MemLp.toLp_congr _ _ (aux_packLpFun_add_ae u v)
      _ = (aux_packLpFun_memLp u).toLp (aux_packLpFun u) +
          (aux_packLpFun_memLp v).toLp (aux_packLpFun v) :=
        MemLp.toLp_add _ _
  map_smul' c u := by
    calc
      (aux_packLpFun_memLp (c • u)).toLp (aux_packLpFun (c • u)) =
          ((aux_packLpFun_memLp u).const_smul c).toLp (c • aux_packLpFun u) :=
        MemLp.toLp_congr _ _ (aux_packLpFun_smul_ae c u)
      _ = c • (aux_packLpFun_memLp u).toLp (aux_packLpFun u) :=
        MemLp.toLp_const_smul c _
theorem aux_eLpNorm_sq_packLpLinearMap {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ] (u : Fin J → Lp ℂ 2 μ) :
    eLpNorm ((aux_packLpLinearMap (μ := μ)) u : Fin J × X → ℂ) 2
        ((Measure.count : Measure (Fin J)).prod μ) ^ 2 =
      ∑ j : Fin J, eLpNorm (u j : X → ℂ) 2 μ ^ 2 := by
  change eLpNorm ((aux_packLpFun_memLp u).toLp (aux_packLpFun u) : Fin J × X → ℂ) 2
      ((Measure.count : Measure (Fin J)).prod μ) ^ 2 = _
  calc
    eLpNorm ((aux_packLpFun_memLp u).toLp (aux_packLpFun u) : Fin J × X → ℂ) 2
        ((Measure.count : Measure (Fin J)).prod μ) ^ 2 =
        eLpNorm (aux_packLpFun u) 2 ((Measure.count : Measure (Fin J)).prod μ) ^ 2 := by
      rw [eLpNorm_congr_ae (MemLp.coeFn_toLp (aux_packLpFun_memLp u))]
    _ = _ := aux_eLpNorm_sq_packLpFun u
theorem aux_norm_sq_packLpLinearMap {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ] (u : Fin J → Lp ℂ 2 μ) :
    ‖(aux_packLpLinearMap (μ := μ)) u‖ ^ 2 = ∑ j : Fin J, ‖u j‖ ^ 2 := by
  have h := congrArg ENNReal.toReal (aux_eLpNorm_sq_packLpLinearMap u)
  rw [ENNReal.toReal_pow,
    ENNReal.toReal_sum (fun j _ ↦ ENNReal.pow_ne_top (Lp.memLp (u j)).eLpNorm_ne_top)] at h
  simp_rw [ENNReal.toReal_pow] at h
  simpa only [Lp.norm_def] using h
noncomputable def aux_packLpPiLinearMap {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ] :
    PiLp 2 (fun _ : Fin J ↦ Lp ℂ 2 μ) →ₗ[ℂ]
      Lp ℂ 2 ((Measure.count : Measure (Fin J)).prod μ) :=
  (aux_packLpLinearMap (μ := μ)).comp
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin J ↦ Lp ℂ 2 μ)).toLinearMap
theorem aux_norm_sq_packLpPiLinearMap {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ] (u : PiLp 2 (fun _ : Fin J ↦ Lp ℂ 2 μ)) :
    ‖aux_packLpPiLinearMap (μ := μ) u‖ ^ 2 = ‖u‖ ^ 2 := by
  change ‖aux_packLpLinearMap (μ := μ) (fun j ↦ u j)‖ ^ 2 = ‖u‖ ^ 2
  rw [aux_norm_sq_packLpLinearMap]
  exact (PiLp.norm_sq_eq_of_L2 (fun _ : Fin J ↦ Lp ℂ 2 μ) u).symm
noncomputable def aux_packLpLinearIsometry {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ] :
    PiLp 2 (fun _ : Fin J ↦ Lp ℂ 2 μ) →ₗᵢ[ℂ]
      Lp ℂ 2 ((Measure.count : Measure (Fin J)).prod μ) where
  toLinearMap := aux_packLpPiLinearMap (μ := μ)
  norm_map' u := by
    nlinarith [aux_norm_sq_packLpPiLinearMap (μ := μ) u,
      norm_nonneg (aux_packLpPiLinearMap (μ := μ) u), norm_nonneg u]
noncomputable def aux_packLpContinuousLinearMap {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ] :
    PiLp 2 (fun _ : Fin J ↦ Lp ℂ 2 μ) →L[ℂ]
      Lp ℂ 2 ((Measure.count : Measure (Fin J)).prod μ) :=
  (aux_packLpLinearIsometry (μ := μ)).toContinuousLinearMap
noncomputable def aux_packLpCMLM {J : ℕ} {ι Y : Type*} {X : ι → Type*} [Fintype ι]
    [MeasurableSpace Y] {μ : Measure Y} [SFinite μ]
    [∀ i, SeminormedAddCommGroup (X i)] [∀ i, NormedSpace ℂ (X i)]
    (B : Fin J → ContinuousMultilinearMap ℂ X (Lp ℂ 2 μ)) :
    ContinuousMultilinearMap ℂ X
      (Lp ℂ 2 ((Measure.count : Measure (Fin J)).prod μ)) :=
  (aux_packLpContinuousLinearMap (μ := μ)).compContinuousMultilinearMap
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin J ↦ Lp ℂ 2 μ)).symm.toContinuousLinearMap
      |>.compContinuousMultilinearMap
        ((ContinuousMultilinearMap.piₗᵢ ℂ X) B))
end
end Auto


