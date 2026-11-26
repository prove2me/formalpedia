-- Prove2me | Definitions.Def_Malliavin_ElementaryIto
-- name    : Malliavin_ElementaryIto
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:13:44.485601+00:00
-- url     : https://prove2.me/theorems/cd86e117-5b8e-4e57-91e2-73d4a7e307e6
-- title:
--   Elementary Ito
-- statement:
--   Definitions and structural lemmas for Elementary Ito, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean

import Definitions.Def_Malliavin_ClarkOcone
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
noncomputable section
namespace Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
noncomputable def partitionElementaryPredictable
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    PredictableProcessL2 𝓕 P :=
  Finset.univ.sum fun i ↦
    elementaryPredictable 𝓕 (Q.t i.castSucc) (Q.t i.succ) (Z i)
noncomputable def ClarkOconeFamily.partitionElementaryIntegralValue
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) : RandomL2 P :=
  Finset.univ.sum fun i ↦
    C.elementaryIntegralValue
      (Q.mono.monotone (Fin.castSucc_le_succ i)) (Z i)
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Future Brownian increments are independent of every random variable measurable for a
filtration identified with the natural Brownian filtration. -/
theorem indep_increment_of_natural_adapted
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) {Z : W → ℝ}
    (hZ : AEStronglyMeasurable[𝓕 a] Z P) :
    IndepFun (fun w ↦ B b w - B a w) Z P := by
  let Zm : W → ℝ := hZ.mk Z
  have hshift := hB.indepFun_shift a
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
  have hnat_a : 𝓕 a =
      MeasurableSpace.comap (fun w (t : Set.Iic a) ↦ B t w) inferInstance := by
    rw [hnat, Filtration.natural_eq_comap]
  rw [← hnat_a] at hind
  have hZm : @Measurable W ℝ (𝓕 a) inferInstance Zm :=
    hZ.stronglyMeasurable_mk.measurable
  have hindZm := indep_of_indep_of_le_right hind hZm.comap_le
  have hfunZm : IndepFun (fun w ↦ B b w - B a w) Zm P :=
    (IndepFun_iff_Indep _ _ _).mpr hindZm
  exact hfunZm.congr Filter.EventuallyEq.rfl hZ.ae_eq_mk.symm
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- An adapted `L²` coefficient times a future Brownian increment is again in `L²`. -/
theorem memLp_natural_adapted_mul_increment
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    MemLp (fun w ↦ (Z : W → ℝ) w * (B b w - B a w)) 2 P := by
  have hΔ : MemLp (fun w ↦ B b w - B a w) 2 P :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  have hind := indep_increment_of_natural_adapted hB hsm hnat hab
    (lpMeas.aestronglyMeasurable Z)
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
noncomputable def elementaryBrownianValue
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) : RandomL2 P :=
  (memLp_natural_adapted_mul_increment hB hsm hnat hab Z).toLp
    (fun w ↦ (Z : W → ℝ) w * (B b w - B a w))
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- A representative of the constructed elementary Brownian terminal value. -/
theorem coeFn_elementaryBrownianValue
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    (elementaryBrownianValue hB hsm hnat hab Z : W → ℝ) =ᵐ[P]
      fun w ↦ (Z : W → ℝ) w * (B b w - B a w) :=
  MemLp.coeFn_toLp _
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The elementary Brownian terminal value is additive in its adapted coefficient. -/
theorem elementaryBrownianValue_add
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z Y : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryBrownianValue hB hsm hnat hab (Z + Y) =
      elementaryBrownianValue hB hsm hnat hab Z +
        elementaryBrownianValue hB hsm hnat hab Y := by
  apply Lp.ext
  filter_upwards [coeFn_elementaryBrownianValue hB hsm hnat hab (Z + Y),
    coeFn_elementaryBrownianValue hB hsm hnat hab Z,
    coeFn_elementaryBrownianValue hB hsm hnat hab Y,
    Lp.coeFn_add (Z : RandomL2 P) (Y : RandomL2 P),
    Lp.coeFn_add (elementaryBrownianValue hB hsm hnat hab Z)
      (elementaryBrownianValue hB hsm hnat hab Y)]
    with w hsum hZ hY hZY hvalue
  rw [hsum, hvalue, Pi.add_apply, hZ, hY]
  change (Z.1 + Y.1 : RandomL2 P) w * (B b w - B a w) =
    (Z : W → ℝ) w * (B b w - B a w) +
      (Y : W → ℝ) w * (B b w - B a w)
  rw [hZY, Pi.add_apply]
  ring
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The elementary Brownian terminal value commutes with real scalar multiplication. -/
theorem elementaryBrownianValue_smul
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (c : ℝ) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryBrownianValue hB hsm hnat hab (c • Z) =
      c • elementaryBrownianValue hB hsm hnat hab Z := by
  apply Lp.ext
  filter_upwards [coeFn_elementaryBrownianValue hB hsm hnat hab (c • Z),
    coeFn_elementaryBrownianValue hB hsm hnat hab Z,
    Lp.coeFn_smul c (Z : RandomL2 P),
    Lp.coeFn_smul c (elementaryBrownianValue hB hsm hnat hab Z)]
    with w hsmul hZ hcZ hvalue
  rw [hsmul, hvalue, Pi.smul_apply, hZ]
  change (c • Z.1 : RandomL2 P) w * (B b w - B a w) =
    c • ((Z : W → ℝ) w * (B b w - B a w))
  rw [hcZ, Pi.smul_apply]
  simp only [smul_eq_mul]
  ring
noncomputable def elementaryBrownianValueLinear
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) : lpMeas ℝ ℝ (𝓕 a) 2 P →ₗ[ℝ] RandomL2 P where
  toFun := elementaryBrownianValue hB hsm hnat hab
  map_add' := elementaryBrownianValue_add hB hsm hnat hab
  map_smul' := elementaryBrownianValue_smul hB hsm hnat hab
noncomputable def partitionElementaryBrownianValue
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) : RandomL2 P :=
  Finset.univ.sum fun i ↦ elementaryBrownianValue hB hsm hnat
    (Q.mono.monotone (Fin.castSucc_le_succ i)) (Z i)
end Malliavin


