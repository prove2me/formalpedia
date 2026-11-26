-- Prove2me | Definitions.Def_Malliavin_ClarkOcone
-- name    : Malliavin_ClarkOcone
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:10:59.476372+00:00
-- url     : https://prove2.me/theorems/391c6817-6460-5b86-8721-26bd0e29281d
-- title:
--   Clark Ocone
-- statement:
--   Definitions and structural lemmas for Clark Ocone, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_IsWienerGenerated_measurable
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
noncomputable section
namespace Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
abbrev TimeProcessL2 (P : Measure W) :=
  Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P)
abbrev PredictableProcessL2 (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (P : Measure W) :=
  lpMeas ℝ ℝ 𝓕.predictable 2 (nonnegativeLebesgueMeasure.prod P)
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] in
/-- The predictable sigma-algebra is contained in the ambient product sigma-algebra. -/
theorem predictable_le_prod (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    𝓕.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × W)) := by
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    exact (measurableSet_singleton (0 : ℝ≥0)).prod (𝓕.le 0 A hA)
  · intro t A hA
    exact measurableSet_Ioi.prod (𝓕.le t A hA)
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The time coordinate is measurable from the predictable sigma-algebra. -/
theorem measurable_fst_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    @Measurable (ℝ≥0 × W) ℝ≥0 𝓕.predictable inferInstance Prod.fst := by
  apply measurable_of_Iic
  intro t
  have hset : Prod.fst ⁻¹' Set.Iic t =
      ({0} ×ˢ (Set.univ : Set W)) ∪ (Set.Ioc 0 t ×ˢ Set.univ) := by
    ext ⟨s, w⟩
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_prod,
      Set.mem_singleton_iff, Set.mem_univ, and_true]
    constructor
    · intro hst
      rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ s) with hs | hs
      · exact Or.inl hs.symm
      · exact Or.inr ⟨hs, hst⟩
    · rintro (hs | hs)
      · subst s
        exact (zero_le : (0 : ℝ≥0) ≤ t)
      · exact hs.2
  rw [hset]
  exact (measurableSet_predictable_singleton_bot_prod MeasurableSet.univ).union
    (measurableSet_predictable_Ioc_prod 0 t MeasurableSet.univ)
noncomputable def deterministicTimeEmbedding :
    Lp ℝ 2 nonnegativeLebesgueMeasure →ₗᵢ[ℝ] TimeProcessL2 P :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst
omit [CompleteSpace W] [BorelSpace W] in
/-- A deterministic time integrand is measurably predictable. -/
theorem deterministicTimeEmbedding_aestronglyMeasurable
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    AEStronglyMeasurable[𝓕.predictable]
      (deterministicTimeEmbedding (P := P) f : (ℝ≥0 × W) → ℝ)
      (nonnegativeLebesgueMeasure.prod P) := by
  have hcomp : StronglyMeasurable[𝓕.predictable]
      ((f : ℝ≥0 → ℝ) ∘ Prod.fst) :=
    (Lp.stronglyMeasurable f).comp_measurable (measurable_fst_predictable 𝓕)
  exact hcomp.aestronglyMeasurable.congr
    (Lp.coeFn_compMeasurePreserving f measurePreserving_fst).symm
noncomputable def deterministicPredictableEmbedding
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    Lp ℝ 2 nonnegativeLebesgueMeasure →ₗᵢ[ℝ] PredictableProcessL2 𝓕 P where
  toFun f := ⟨deterministicTimeEmbedding (P := P) f,
    deterministicTimeEmbedding_aestronglyMeasurable 𝓕 f⟩
  map_add' f g := Subtype.ext (map_add (deterministicTimeEmbedding (P := P)) f g)
  map_smul' c f := Subtype.ext (map_smul (deterministicTimeEmbedding (P := P)) c f)
  norm_map' f := (deterministicTimeEmbedding (P := P)).norm_map f
noncomputable def elementaryRepresentative (_𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (a b : ℝ≥0) (Z : W → ℝ) (p : ℝ≥0 × W) : ℝ :=
  if p.1 ∈ Set.Ioc a b then Z p.2 else 0
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] in
/-- If `Z` is `𝓕_a`-measurable, then `(t, ω) ↦ 1_(a,b](t) Z(ω)` is predictable. -/
theorem stronglyMeasurable_elementaryRepresentative
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    {Z : W → ℝ} (hZ : StronglyMeasurable[𝓕 a] Z) :
    StronglyMeasurable[𝓕.predictable] (elementaryRepresentative 𝓕 a b Z) := by
  apply Measurable.stronglyMeasurable
  apply measurable_of_Iic
  intro c
  by_cases hc : 0 ≤ c
  · have hset : elementaryRepresentative 𝓕 a b Z ⁻¹' Set.Iic c =
        (Set.Ioc a b ×ˢ (Z ⁻¹' Set.Ioi c))ᶜ := by
      ext p
      by_cases hp : p.1 ∈ Set.Ioc a b
      · simp only [Set.mem_preimage, elementaryRepresentative, hp, ↓reduceIte, Set.mem_Iic, Set.mem_compl_iff,
          Set.mem_prod, Set.mem_Ioi, true_and, not_lt]
      · simp only [Set.mem_preimage, elementaryRepresentative, hp, ↓reduceIte, Set.mem_Iic, hc, Set.mem_compl_iff,
          Set.mem_prod, Set.mem_Ioi, false_and, not_false_eq_true]
    rw [hset]
    exact (measurableSet_predictable_Ioc_prod a b
      (hZ.measurable measurableSet_Ioi)).compl
  · have hc' : c < 0 := lt_of_not_ge hc
    have hset : elementaryRepresentative 𝓕 a b Z ⁻¹' Set.Iic c =
        Set.Ioc a b ×ˢ (Z ⁻¹' Set.Iic c) := by
      ext p
      by_cases hp : p.1 ∈ Set.Ioc a b
      · simp only [Set.mem_preimage, elementaryRepresentative, hp, ↓reduceIte, Set.mem_Iic, Set.mem_prod, true_and]
      · simp only [Set.mem_preimage, elementaryRepresentative, hp, ↓reduceIte, Set.mem_Iic, Set.mem_prod, false_and,
          iff_false, not_le, hc']
    rw [hset]
    exact measurableSet_predictable_Ioc_prod a b (hZ.measurable measurableSet_Iic)
noncomputable def iocIndicator (a b : ℝ≥0) :
    Lp ℝ 2 nonnegativeLebesgueMeasure :=
  indicatorConstLp 2 measurableSet_Ioc
    (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (1 : ℝ)
noncomputable def elementaryPredictable
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) : PredictableProcessL2 𝓕 P := by
  let hZ : AEStronglyMeasurable[𝓕 a] (Z : W → ℝ) P :=
    lpMeas.aestronglyMeasurable Z
  let Zm : W → ℝ := hZ.mk (Z : W → ℝ)
  let H : ℝ≥0 × W → ℝ := elementaryRepresentative 𝓕 a b Zm
  let V : Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P) :=
    tensor (iocIndicator a b) (Z : Lp ℝ 2 P)
  have hV : (V : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] H := by
    have hg : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
        (iocIndicator a b : ℝ≥0 → ℝ) p.1 =
          (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) p.1 :=
      Measure.quasiMeasurePreserving_fst.ae_eq_comp
        (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
          (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top a b) (c := (1 : ℝ)))
    have hZm : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
        (Z : W → ℝ) p.2 = Zm p.2 :=
      Measure.quasiMeasurePreserving_snd.ae_eq_comp hZ.ae_eq_mk
    filter_upwards [coeFn_tensor (iocIndicator a b) (Z : Lp ℝ 2 P), hg, hZm]
      with p hp hg' hZm'
    rw [hp, hg', hZm']
    by_cases ht : p.1 ∈ Set.Ioc a b <;>
      simp [H, elementaryRepresentative, ht]
  exact ⟨V,
    (stronglyMeasurable_elementaryRepresentative 𝓕 a b hZ.stronglyMeasurable_mk)
      |>.aestronglyMeasurable.congr hV.symm⟩
noncomputable def adaptedOne
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a : ℝ≥0) :
    lpMeas ℝ ℝ (𝓕 a) 2 P :=
  ⟨Lp.const 2 P (1 : ℝ),
    aestronglyMeasurable_const.congr (Lp.coeFn_const 2 P (1 : ℝ)).symm⟩
def predictableProjection (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    TimeProcessL2 P →L[ℝ] PredictableProcessL2 𝓕 P :=
  condExpL2 ℝ ℝ (predictable_le_prod 𝓕)
def filtrationCondExpL2 (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) :
    RandomL2 P →L[ℝ] RandomL2 P :=
  (lpMeas ℝ ℝ (𝓕 t) 2 P).subtypeL.comp (condExpL2 ℝ ℝ (𝓕.le t))
def expectationL2 (F : RandomL2 P) : RandomL2 P :=
  Lp.const 2 P (∫ ω, F ω ∂P)
structure ClarkOconeFamily (B : ℝ≥0 → W → ℝ) (P : Measure W) [IsGaussian P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) where
  /-- The designated process has Brownian finite-dimensional laws. -/
  isPreBrownian : IsPreBrownianReal B P
  /-- The Brownian coordinates are compatible with the linear Gaussian structure on `W`. -/
  coordinate : ℝ≥0 → StrongDual ℝ W
  /-- Identification of the process with the linear coordinates. -/
  coordinate_apply : ∀ t w, B t w = coordinate t w
  /-- The coordinates generate the ambient probability space. -/
  generated : IsWienerGenerated B
  /-- Measurability used to form the natural filtration. -/
  stronglyMeasurable : ∀ t, StronglyMeasurable (B t)
  /-- The filtration is the natural Brownian filtration. -/
  naturalFiltration : 𝓕 = Filtration.natural B stronglyMeasurable
  /-- Designated integration isometry on predictable square-integrable processes. -/
  itoIntegral : PredictableProcessL2 𝓕 P →L[ℝ] RandomL2 P
  /-- Norm isometry of the designated integration operator. -/
  norm_itoIntegral : ∀ u, ‖itoIntegral u‖ = ‖u‖
  /-- Outputs of the designated integration operator are centered. -/
  integral_itoIntegral : ∀ u, ∫ ω, itoIntegral u ω ∂P = 0
  /-- Terminal `L²` representation by the designated integration operator. -/
  martingaleRepresentation : ∀ G : RandomL2 P, ∃ u,
    G = expectationL2 G + itoIntegral u
  /-- Duality identifies the predictable Malliavin derivative as the MRT integrand.  Here the
  time derivative `Dₜ` is the one constructed in `TimeDerivative.lean` from the Brownian
  coordinates (`Malliavin.timeDerivative`): `J₁⁻¹` pointwise, then the Fubini lift. -/
  malliavinItoDuality : ∀ (F : D12 P) u,
    inner ℝ (F.1 - expectationL2 F.1) (itoIntegral u) =
      inner ℝ (predictableProjection 𝓕
        (Malliavin.timeDerivative isPreBrownian coordinate coordinate_apply generated
          (mderivD12 P F))) u
def ClarkOconeFamily.itoIntegralₗᵢ {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) :
    PredictableProcessL2 𝓕 P →ₗᵢ[ℝ] RandomL2 P :=
  ⟨C.itoIntegral.toLinearMap, C.norm_itoIntegral⟩
@[simp]
theorem ClarkOconeFamily.itoIntegralₗᵢ_apply {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (u : PredictableProcessL2 𝓕 P) :
    C.itoIntegralₗᵢ u = C.itoIntegral u :=
  rfl
noncomputable def ClarkOconeFamily.centeredItoIntegralₗᵢ
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) :
    PredictableProcessL2 𝓕 P →ₗᵢ[ℝ] (CameronMartin.expectationMap P).ker where
  toLinearMap := C.itoIntegralₗᵢ.toLinearMap.codRestrict
    (CameronMartin.expectationMap P).ker fun u => by
      rw [LinearMap.mem_ker]
      change CameronMartin.expectationMap P (C.itoIntegral u) = 0
      rw [CameronMartin.expectationMap_apply]
      exact C.integral_itoIntegral u
  norm_map' u := C.norm_itoIntegral u
@[simp]
theorem ClarkOconeFamily.centeredItoIntegralₗᵢ_apply
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (u : PredictableProcessL2 𝓕 P) :
    (C.centeredItoIntegralₗᵢ u : RandomL2 P) = C.itoIntegral u :=
  rfl
theorem ClarkOconeFamily.centeredItoIntegralₗᵢ_surjective
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) :
    Function.Surjective C.centeredItoIntegralₗᵢ := by
  intro G
  obtain ⟨u, hu⟩ := C.martingaleRepresentation (G : RandomL2 P)
  have hmean : ∫ w, (G : RandomL2 P) w ∂P = 0 := by
    rw [← CameronMartin.expectationMap_apply]
    exact G.property
  have hexpect : expectationL2 (G : RandomL2 P) = 0 := by
    rw [expectationL2, hmean]
    simp only [map_zero]
  refine ⟨u, Subtype.ext ?_⟩
  change C.itoIntegral u = (G : RandomL2 P)
  rw [hexpect, zero_add] at hu
  exact hu.symm
noncomputable def ClarkOconeFamily.centeredItoEquiv
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) :
    PredictableProcessL2 𝓕 P ≃ₗᵢ[ℝ] (CameronMartin.expectationMap P).ker :=
  LinearIsometryEquiv.ofSurjective C.centeredItoIntegralₗᵢ
    C.centeredItoIntegralₗᵢ_surjective
@[simp]
theorem ClarkOconeFamily.centeredItoEquiv_apply
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (u : PredictableProcessL2 𝓕 P) :
    (C.centeredItoEquiv u : RandomL2 P) = C.itoIntegral u :=
  rfl
noncomputable def ClarkOconeFamily.timeDerivative {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) : Lp (CameronMartin.Space P) 2 P →L[ℝ] TimeProcessL2 P :=
  (Malliavin.timeDerivative C.isPreBrownian C.coordinate C.coordinate_apply
    C.generated).toContinuousLinearMap
theorem ClarkOconeFamily.indep_increment_of_adapted
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {a b : ℝ≥0} (hab : a ≤ b)
    {Z : W → ℝ} (hZ : AEStronglyMeasurable[𝓕 a] Z P) :
    IndepFun (fun w ↦ B b w - B a w) Z P := by
  let Zm : W → ℝ := hZ.mk Z
  have hshift := C.isPreBrownian.indepFun_shift a
  have heval : Measurable (fun x : ℝ≥0 → ℝ ↦ x (b - a)) := measurable_pi_apply _
  have hfuturePast := hshift.comp heval measurable_id
  have hfuturePast' : IndepFun (fun w ↦ B b w - B a w)
      (fun w (t : Set.Iic a) ↦ B t w) P := by
    convert hfuturePast using 1
    · funext w
      change B b w - B a w = B (a + (b - a)) w - B a w
      rw [add_comm, tsub_add_cancel_of_le hab]
    · rfl
  have hind := (IndepFun_iff_Indep _ _ _).mp hfuturePast'
  have hnat : 𝓕 a =
      MeasurableSpace.comap (fun w (t : Set.Iic a) ↦ B t w) inferInstance := by
    rw [C.naturalFiltration, Filtration.natural_eq_comap]
  rw [← hnat] at hind
  have hZm : @Measurable W ℝ (𝓕 a) inferInstance Zm :=
    hZ.stronglyMeasurable_mk.measurable
  have hindZm := indep_of_indep_of_le_right hind hZm.comap_le
  have hfunZm : IndepFun (fun w ↦ B b w - B a w) Zm P :=
    (IndepFun_iff_Indep _ _ _).mpr hindZm
  exact hfunZm.congr Filter.EventuallyEq.rfl hZ.ae_eq_mk.symm
theorem ClarkOconeFamily.indep_increment_adapted
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {a b : ℝ≥0} (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    IndepFun (fun w ↦ B b w - B a w) (Z : W → ℝ) P :=
  C.indep_increment_of_adapted hab (lpMeas.aestronglyMeasurable Z)
theorem ClarkOconeFamily.memLp_adapted_mul_increment
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {a b : ℝ≥0} (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    MemLp (fun w ↦ (Z : W → ℝ) w * (B b w - B a w)) 2 P := by
  have hΔ : MemLp (fun w ↦ B b w - B a w) 2 P :=
    C.isPreBrownian.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  have hind := C.indep_increment_adapted hab Z
  have hindSq : IndepFun (fun w ↦ (B b w - B a w) ^ 2)
      (fun w ↦ (Z : W → ℝ) w ^ 2) P :=
    hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hint : Integrable ((fun w ↦ (B b w - B a w) ^ 2) *
      fun w ↦ (Z : W → ℝ) w ^ 2) P :=
    hindSq.integrable_mul hΔ.integrable_sq
      (Lp.memLp (Z : Lp ℝ 2 P)).integrable_sq
  have hZamb : AEStronglyMeasurable (Z : W → ℝ) P :=
    AEStronglyMeasurable.mono (𝓕.le a) (lpMeas.aestronglyMeasurable Z)
  have hmeas : AEStronglyMeasurable
      (fun w ↦ (Z : W → ℝ) w * (B b w - B a w)) P :=
    hZamb.mul hΔ.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).2
  refine hint.congr (Filter.Eventually.of_forall fun w ↦ ?_)
  simp only [Pi.mul_apply]
  ring
noncomputable def ClarkOconeFamily.elementaryIntegralValue
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {a b : ℝ≥0} (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) : RandomL2 P :=
  (C.memLp_adapted_mul_increment hab Z).toLp
    (fun w ↦ (Z : W → ℝ) w * (B b w - B a w))
def ClarkOconeFamily.IsBrownianOnElementary
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) : Prop :=
  ∀ {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P),
    C.itoIntegral (elementaryPredictable 𝓕 a b Z) =
      C.elementaryIntegralValue hab Z
def ClarkOconeFamily.IsBrownianOnDeterministic
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕) : Prop :=
  ∀ t, C.itoIntegral
    (deterministicPredictableEmbedding 𝓕 (intervalIndicator t)) = brownianLp C.isPreBrownian t
noncomputable def ClarkOconeFamily.deterministicIntegral
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕) :
    Lp ℝ 2 nonnegativeLebesgueMeasure →L[ℝ] RandomL2 P :=
  C.itoIntegral.comp (deterministicPredictableEmbedding 𝓕).toContinuousLinearMap
def predictableDerivative {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) : PredictableProcessL2 𝓕 P :=
  predictableProjection 𝓕
    (C.timeDerivative (mderivD12 P F))
def clarkOconeIntegral {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) : RandomL2 P :=
  C.itoIntegral (predictableDerivative C F)
end Malliavin
end


