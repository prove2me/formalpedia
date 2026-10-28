-- Prove2me | Definitions.Def_OAIQ071C002
-- name    : OAIQ071C002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T04:58:28.311365+00:00
-- url     : https://prove2.me/theorems/46a953e1-bfc0-4294-97ab-bf27ecddd69b
-- title:
--   Definitions bundle OAIQ071C002 of the split of OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 360 declarations of OpenAI's Lean: 135 definitions, 2 inductive types or structures, 5 instances and 218 theorems. The definitions and types are `OAI.CoulombAtom.DeficitSecants`, `OAI.CoulombAtom.HasWeakDirectionalDerivative`, `OAI.CoulombAtom.Occupied`, `OAI.CoulombAtom.Pauli.Many`, `OAI.CoulombAtom.Pauli.OneParticle`, `OAI.CoulombAtom.Pauli.coordinateSplit`, `OAI.CoulombAtom.Pauli.globalDensityConstant`, `OAI.CoulombAtom.Pauli.gradientMany`, `OAI.CoulombAtom.Pauli.gradientVector`, `OAI.CoulombAtom.Pauli.insertTest`, `OAI.CoulombAtom.Pauli.manyTest`, `OAI.CoulombAtom.Pauli.oneMeasure`, `OAI.CoulombAtom.Pauli.splitSpin`, `OAI.CoulombAtom.Pauli.toMany`, `OAI.CoulombAtom.SlaterPairRest`, `OAI.CoulombAtom.SlaterParticle`, `OAI.CoulombAtom.allSectorEnergy`, `OAI.CoulombAtom.annularCellCostConstant`, `OAI.CoulombAtom.annularCellScaleConstant`, `OAI.CoulombAtom.annularOffsetMass`, `OAI.CoulombAtom.antisymmetrize`, `OAI.CoulombAtom.blockPerm`, `OAI.CoulombAtom.blockPermHom`, `OAI.CoulombAtom.blockSubgroup`, `OAI.CoulombAtom.cappedWidthProfile`, `OAI.CoulombAtom.coherentSpatialSupport`, `OAI.CoulombAtom.finiteCorePatchBound`, `OAI.CoulombAtom.finiteOrbitalDensity`, `OAI.CoulombAtom.firstPartial`, `OAI.CoulombAtom.fixedSectorScale`, `OAI.CoulombAtom.gridPacketRadius`, `OAI.CoulombAtom.initialDensityConstant`, `OAI.CoulombAtom.innerScale`, `OAI.CoulombAtom.limitDeficit`, `OAI.CoulombAtom.limitPriceEnergy`, `OAI.CoulombAtom.limitSectorEnergy`, `OAI.CoulombAtom.localFieldScale`, `OAI.CoulombAtom.localTFResponse`, `OAI.CoulombAtom.occupationIndex`, `OAI.CoulombAtom.occupationOrbitals` and 97 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombIonization_Fermionic_Basis`, `CoulombIonization_Fermionic_DyadicPowerSq`, `CoulombIonization_Fermionic_FreqCut`, `CoulombIonization_Fermionic_GlobalDensityConstant`, `CoulombIonization_Fermionic_InfiniteDensity`, `CoulombIonization_Fermionic_InsertTest`, `CoulombIonization_Fermionic_ManyTest`, `CoulombIonization_Fermionic_OccupationPairDensity`, `CoulombIonization_Fermionic_Pull`, `CoulombIonization_Fermionic_Slater`, `CoulombIonization_Fermionic_SlaterBody`, `CoulombIonization_Fermionic_SlaterMeasure`, `CoulombIonization_Fermionic_SlaterOccupation`, `CoulombIonization_Fermionic_SlaterPairAlgebra`, `CoulombIonization_Fermionic_SlaterPairTrace`, `CoulombIonization_Fermionic_SlaterRepulsion`, `CoulombIonization_Fermionic_SlaterSymmetry`, `CoulombIonization_Fermionic_SlaterTwoBody`, `CoulombIonization_Fermionic_Spin`, `CoulombIonization_Fermionic_WeightedPairDensity`, `CoulombIonization_FieldAnalysis_CellFieldNormalizationBarrier`, `CoulombIonization_FieldAnalysis_CoreFieldRegularity`, `CoulombIonization_FieldAnalysis_LocalFieldBootstrapBarrier`, `CoulombIonization_FieldAnalysis_LocalFieldScalarBoundBarrier`, `CoulombIonization_FieldAnalysis_ObservedFieldScale`, `CoulombIonization_FormDomain_BlockEnergetics`, `CoulombIonization_FormDomain_CoherentHilbert`, `CoulombIonization_FormDomain_CoherentSchwartz`, `CoulombIonization_FormDomain_CompCL`, `CoulombIonization_FormDomain_CompactEigenbasis`, `CoulombIonization_FormDomain_CosetWedge`, `CoulombIonization_FormDomain_FiniteFermionEnsemble`, `CoulombIonization_FormDomain_FormBody`, `CoulombIonization_FormDomain_FourierMomentGradient`, `CoulombIonization_FormDomain_GradientVector`, `CoulombIonization_FormDomain_L2`, `CoulombIonization_FormDomain_SumForm`, `CoulombIonization_FormDomain_TrialSmoothTest`, `CoulombIonization_FormDomain_WeakDerivativeSmulL2`, `CoulombIonization_FormDomain_WeakDirectionalDerivative`, `CoulombIonization_Ionization_IntegratedStability`, `CoulombIonization_Ionization_PricedSubsequence`, `CoulombIonization_Localization_BarrierConditionalBarrier`, `CoulombIonization_Localization_ConditionalRetainedGap`, `CoulombIonization_Localization_DyadicObservation`, `CoulombIonization_Localization_FermionGradient`, `CoulombIonization_Localization_FermionL2`, `CoulombIonization_Localization_GridPacketRadius`, `CoulombIonization_Localization_ObservationIntegral`, `CoulombIonization_Localization_ObservedInnerCap`, `CoulombIonization_Localization_PacketCloud`, `CoulombIonization_Localization_PacketFourier`, `CoulombIonization_Localization_PacketScale`, `CoulombIonization_Localization_SqrtMultiplier`, `CoulombIonization_Localization_TailObservationEventBarrier`, `CoulombIonization_Localization_Trace`, `CoulombIonization_RadialBounds_AnnularCellGeometryBarrier`, `CoulombIonization_RadialBounds_AnnularCutExcess`, `CoulombIonization_RadialBounds_ArbitraryCutExcess`, `CoulombIonization_RadialBounds_BarrierNuclearScaleBarrier`, `CoulombIonization_RadialBounds_BarrierRetainedComparisonBarrier`, `CoulombIonization_RadialBounds_BarrierRetainedFiniteBarrier`, `CoulombIonization_RadialBounds_BarrierSmoothMaxBarrier`, `CoulombIonization_RadialBounds_BarrierStepGeometryBarrier`, `CoulombIonization_RadialBounds_BarrierStepWeakBarrier`, `CoulombIonization_RadialBounds_CellCountAbsorptionBarrier`, `CoulombIonization_RadialBounds_CellScaleBarrier`, `CoulombIonization_RadialBounds_CoulombTailNumerics`, `CoulombIonization_RadialBounds_GlobalDensityBarrier`, `CoulombIonization_RadialBounds_LocalDensityTraceBarrier`, `CoulombIonization_RadialBounds_RadialPatchGeometry`, `CoulombIonization_RadialBounds_RadialSelectedCounts`, `CoulombIonization_RadialBounds_RootMomentCauchyBarrier`, `CoulombIonization_RadialBounds_SelectionNumerics`, `CoulombIonization_RadialBounds_StripAveraging`, `CoulombIonization_RadialBounds_TailInitialEventuallyBarrier`, `CoulombIonization_RadialBounds_TinyProbabilityFloorBarrier`, `CoulombIonization_RadialBounds_TruncationRadius`, `CoulombIonization_ThomasFermi_CellDensityBoundBarrier`, `CoulombIonization_ThomasFermi_ContractFunction`, `CoulombIonization_ThomasFermi_InverseThresholdLimitBarrier`, `CoulombIonization_ThomasFermi_PacketFieldConstant`, `CoulombIonization_ThomasFermi_PatchRandomVariables`, `CoulombIonization_Variational_AllSectorEnergy`, `CoulombIonization_Variational_BlockEnergy`, `CoulombIonization_Variational_BlockPermutations`, `CoulombIonization_Variational_CoherentBessel`, `CoulombIonization_Variational_CoherentDensityTrace`, `CoulombIonization_Variational_ComplexOccupation`, `CoulombIonization_Variational_CorrelatedFiniteInsertion`, `CoulombIonization_Variational_Electrostatic`, `CoulombIonization_Variational_InsertionSwap`, `CoulombIonization_Variational_MasterWidth`, `CoulombIonization_Variational_OccupationTraces`, `CoulombIonization_Variational_OrbitalPole`, `CoulombIonization_Variational_Pointwise`, `CoulombIonization_Variational_SmoothCompactIntegral`, `CoulombIonization_Variational_Space`, `CoulombIonization_Variational_SpinSpaceIntegrable`, `CoulombIonization_Variational_SumPairsHalf`, `CoulombIonization_Variational_TensorLp`, `CoulombIonization_Variational_WeightedCauchy`.
--
--   **Imports.** It imports the published bundle `Def_CoulombIonization`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ071C004` and `OAIQ071C005`; the statement `OAI_CoulombAtom_actual_priced_deficit_limit`.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombIonization

section
-- module Solutions.OAIQ071_CI.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_GlobalDensityBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal

namespace CoulombPauli

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]

omit [SFinite μ] in
lemma memLp_tensor {u : A → ℂ} {v : B → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 ν) :
    MemLp (fun z : A × B => u z.1 * v z.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm
    (hu.aestronglyMeasurable.comp_fst.mul hv.aestronglyMeasurable.comp_snd)).2
  simpa only [Pi.mul_apply, norm_mul, mul_pow] using
    ((memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu).mul_prod
      ((memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).1 hv)

omit [SFinite μ] in
lemma l2_norm_sq (u : Lp ℂ 2 μ) : ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def]
  simp only [inner_self_eq_norm_sq_to_K]
  change (∫ a, ((‖u a‖ : ℝ) : ℂ)^2 ∂μ).re = _
  simp_rw [← Complex.ofReal_pow]
  rw [integral_complex_ofReal]
  rfl

def tensor (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) :=
  (memLp_tensor (Lp.memLp u) (Lp.memLp v)).toLp _

omit [SFinite μ] in
lemma tensor_ae (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    tensor u v =ᵐ[μ.prod ν] (fun z => u z.1 * v z.2) := MemLp.coeFn_toLp _

lemma tensor_norm_sq (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    ‖tensor u v‖^2 = ‖u‖^2 * ‖v‖^2 := by
  rw [l2_norm_sq, l2_norm_sq u, l2_norm_sq v]
  calc
    _ = ∫ z : A × B, ‖u z.1 * v z.2‖^2 ∂μ.prod ν :=
      integral_congr_ae ((tensor_ae u v).fun_comp (fun c : ℂ => ‖c‖^2))
    _ = _ := by
      simp only [norm_mul, mul_pow]
      exact integral_prod_mul (fun x => ‖u x‖^2) (fun y => ‖v y‖^2)

lemma tensor_norm (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) : ‖tensor u v‖ = ‖u‖*‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1
  simpa only [mul_pow] using tensor_norm_sq u v

omit [SFinite μ] in
lemma tensor_add_right (u : Lp ℂ 2 μ) (v w : Lp ℂ 2 ν) :
    tensor u (v+w) = tensor u v + tensor u w := by
  apply Lp.ext
  filter_upwards [tensor_ae u (v+w), tensor_ae u v, tensor_ae u w,
    Lp.coeFn_add (tensor u v) (tensor u w),
    Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_add v w)] with z h1 h2 h3 h4 h5
  simp only [h1,h2,h3,h4,h5, Pi.add_apply, mul_add]

omit [SFinite μ] in
lemma tensor_smul_right (u : Lp ℂ 2 μ) (c : ℂ) (v : Lp ℂ 2 ν) :
    tensor u (c • v) = c • tensor u v := by
  apply Lp.ext
  filter_upwards [tensor_ae u (c • v), tensor_ae u v,
    Lp.coeFn_smul c (tensor u v),
    Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_smul c v)] with z h1 h2 h3 h4
  simp only [h1,h2,h3,h4, Pi.smul_apply, smul_eq_mul]
  ring

def tensorLeft (u : Lp ℂ 2 μ) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearMap.mkContinuous
    ({ toFun := fun v => tensor u v
       map_add' := tensor_add_right u
       map_smul' := tensor_smul_right u } : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 (μ.prod ν))
    ‖u‖ (fun v => (tensor_norm u v).le)

lemma tensorLeft_apply (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) : tensorLeft u v = tensor u v := rfl

lemma tensor_inner (u u' : Lp ℂ 2 μ) (v v' : Lp ℂ 2 ν) :
    ⟪tensor u v, tensor u' v'⟫_ℂ = ⟪u,u'⟫_ℂ * ⟪v,v'⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def]
  calc
    _ = ∫ z : A × B, ⟪u z.1,u' z.1⟫_ℂ * ⟪v z.2,v' z.2⟫_ℂ ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [tensor_ae u v, tensor_ae u' v'] with z h1 h2
      simp only [h1,h2,inner,star_mul]
      ring
    _ = _ := integral_prod_mul (L := ℂ) (fun x => ⟪u x,u' x⟫_ℂ) (fun y => ⟪v y,v' y⟫_ℂ)

omit [SFinite μ] [SFinite ν] in
lemma integrable_eq_zero_of_rectangles {f : A × B → ℂ} (hf : Integrable f (μ.prod ν))
    (h : ∀ (s : Set A) (t : Set B), MeasurableSet s → MeasurableSet t →
      ∫ z in s ×ˢ t, f z ∂μ.prod ν = 0) : f =ᵐ[μ.prod ν] 0 := by
  apply hf.ae_eq_of_withDensityᵥ_eq (integrable_zero _ _ _)
  rw [withDensityᵥ_zero]
  apply VectorMeasure.ext_of_generateFrom _ _ generateFrom_prod.symm isPiSystem_prod
  · rw [withDensityᵥ_apply hf MeasurableSet.univ]
    simpa only [Set.univ_prod_univ, zero_apply] using h Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
  · rintro _ ⟨s, hs, t, ht, rfl⟩
    rw [withDensityᵥ_apply hf (hs.prod ht)]
    exact h s t hs ht

omit [SFinite μ] in
lemma tensor_indicator (s : Set A) (t : Set B) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ⊤) (hνt : ν t ≠ ⊤) :
    tensor (indicatorConstLp 2 hs hμs (1 : ℂ)) (indicatorConstLp 2 ht hνt (1 : ℂ)) =
      indicatorConstLp 2 (hs.prod ht) (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμs hνt) (1 : ℂ) := by
  classical
  apply Lp.ext
  filter_upwards [tensor_ae (indicatorConstLp 2 hs hμs (1 : ℂ))
    (indicatorConstLp 2 ht hνt (1 : ℂ)),
    Measure.quasiMeasurePreserving_fst.ae (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℂ))),
    Measure.quasiMeasurePreserving_snd.ae (indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := hνt) (c := (1 : ℂ))),
    indicatorConstLp_coeFn (p := 2) (hs := hs.prod ht)
      (hμs := by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμs hνt) (c := (1 : ℂ))] with z h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  by_cases hz : z.1 ∈ s <;> by_cases hz' : z.2 ∈ t <;> simp [hz, hz']

omit [SFinite μ] in
lemma rectangle_integral_eq_zero_of_tensor_orthogonal (ψ : Lp ℂ 2 (μ.prod ν))
    (hψ : ∀ (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν), ⟪tensor u v, ψ⟫_ℂ = 0)
    (s : Set A) (t : Set B) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ⊤) (hνt : ν t ≠ ⊤) : ∫ z in s ×ˢ t, ψ z ∂μ.prod ν = 0 := by
  have h := hψ (indicatorConstLp 2 hs hμs (1 : ℂ)) (indicatorConstLp 2 ht hνt (1 : ℂ))
  rw [tensor_indicator, L2.inner_indicatorConstLp_one] at h
  exact h

omit [SFinite μ] in
lemma rectangle_indicator_eq_zero_of_tensor_orthogonal (ψ : Lp ℂ 2 (μ.prod ν))
    (hψ : ∀ (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν), ⟪tensor u v, ψ⟫_ℂ = 0)
    (s : Set A) (t : Set B) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ⊤) (hνt : ν t ≠ ⊤) :
    (s ×ˢ t).indicator (fun z => ψ z) =ᵐ[μ.prod ν] 0 := by
  classical
  have hR : (μ.prod ν) (s ×ˢ t) ≠ ⊤ := by
    rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμs hνt
  apply integrable_eq_zero_of_rectangles
    ((integrableOn_Lp_of_measure_ne_top ψ (by norm_num) hR).integrable_indicator (hs.prod ht))
  intro s' t' hs' ht'
  rw [setIntegral_indicator (hs.prod ht), Set.prod_inter_prod]
  exact rectangle_integral_eq_zero_of_tensor_orthogonal ψ hψ (s' ∩ s) (t' ∩ t)
    (hs'.inter hs) (ht'.inter ht)
    ((measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.2 hμs)).ne
    ((measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.2 hνt)).ne

omit [SFinite μ] in
lemma eq_zero_of_tensor_orthogonal [SigmaFinite μ] [SigmaFinite ν]
    (ψ : Lp ℂ 2 (μ.prod ν))
    (hψ : ∀ (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν), ⟪tensor u v, ψ⟫_ℂ = 0) : ψ = 0 := by
  have hzero : ∀ᵐ z ∂μ.prod ν, ∀ n m : ℕ,
      (spanningSets μ n ×ˢ spanningSets ν m).indicator (fun z => ψ z) z = 0 := by
    apply ae_all_iff.2
    intro n
    apply ae_all_iff.2
    intro m
    exact rectangle_indicator_eq_zero_of_tensor_orthogonal ψ hψ _ _
      (measurableSet_spanningSets μ n) (measurableSet_spanningSets ν m)
      (measure_spanningSets_lt_top μ n).ne (measure_spanningSets_lt_top ν m).ne
  apply Lp.ext
  filter_upwards [hzero, Lp.coeFn_zero ℂ 2 (μ.prod ν)] with z hz h0
  have ha : z.1 ∈ ⋃ n, spanningSets μ n := by rw [iUnion_spanningSets]; trivial
  have hb : z.2 ∈ ⋃ m, spanningSets ν m := by rw [iUnion_spanningSets]; trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 ha
  obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hb
  have hz' := hz n m
  rw [Set.indicator_of_mem (show z ∈ spanningSets μ n ×ˢ spanningSets ν m from ⟨hn, hm⟩)] at hz'
  simpa only [h0, Pi.zero_apply] using hz'

end CoulombPauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Basis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
namespace CoulombPauli
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]

omit [SigmaFinite μ] in
lemma tensor_add_left (u w : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    tensor (u+w) v = tensor u v + tensor w v := by
  apply Lp.ext
  filter_upwards [tensor_ae (u+w) v, tensor_ae u v, tensor_ae w v,
    Lp.coeFn_add (tensor u v) (tensor w v),
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_add u w)] with z h1 h2 h3 h4 h5
  simp only [h1,h2,h3,h4,h5,Pi.add_apply,add_mul]

omit [SigmaFinite μ] in
lemma tensor_smul_left (c : ℂ) (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    tensor (c • u) v = c • tensor u v := by
  apply Lp.ext
  filter_upwards [tensor_ae (c • u) v, tensor_ae u v,
    Lp.coeFn_smul c (tensor u v),
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_smul c u)] with z h1 h2 h3 h4
  simp only [h1,h2,h3,h4,Pi.smul_apply,smul_eq_mul,mul_assoc]

def tensorRight (v : Lp ℂ 2 ν) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearMap.mkContinuous
    ({ toFun := fun u => tensor u v
       map_add' := fun u w => tensor_add_left u w v
       map_smul' := fun c u => tensor_smul_left c u v } :
        Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 (μ.prod ν))
    ‖v‖ (fun u => by
      change ‖tensor u v‖ ≤ ‖v‖ * ‖u‖
      rw [tensor_norm, mul_comm])

lemma tensorRight_apply (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) : tensorRight v u = tensor u v := rfl

lemma tensor_adjoint_exchange (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν)
    (ψ : Lp ℂ 2 (μ.prod ν)) :
    inner ℂ v ((tensorLeft u).adjoint ψ) = inner ℂ u ((tensorRight v).adjoint ψ) := by
  rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]
  rfl

omit [SigmaFinite μ] [SigmaFinite ν] in
lemma hilbertBasis_inner_eq_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ι : Type*} (b : HilbertBasis ι ℂ H) (u : H)
    (h : ∀ i, inner ℂ (b i) u = 0) : u = 0 := by
  apply b.repr.injective
  ext i
  simp [b.repr_apply_apply, h]

variable {ι κ : Type*}

lemma tensor_orthonormal (a : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν)) :
    Orthonormal ℂ (fun p : ι × κ => tensor (a p.1) (b p.2)) := by
  classical
  rw [orthonormal_iff_ite]
  intro p q
  rw [tensor_inner, orthonormal_iff_ite.mp a.orthonormal,
    orthonormal_iff_ite.mp b.orthonormal]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
    simp [h1,h2,Prod.ext_iff]

lemma tensor_basis_total (a : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν)) :
    (Submodule.span ℂ (Set.range (fun p : ι × κ => tensor (a p.1) (b p.2))))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro ψ hψ
  change ψ = 0
  have hij (i : ι) (j : κ) : inner ℂ (tensor (a i) (b j)) ψ = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self (i,j))) hψ
  have hleft (i : ι) : (tensorLeft (a i)).adjoint ψ = 0 := by
    apply hilbertBasis_inner_eq_zero b
    intro j
    rw [ContinuousLinearMap.adjoint_inner_right,tensorLeft_apply]
    exact hij i j
  apply eq_zero_of_tensor_orthogonal
  intro u v
  have hr : (tensorRight v).adjoint ψ = 0 := by
    apply hilbertBasis_inner_eq_zero a
    intro i
    rw [← tensor_adjoint_exchange, hleft, inner_zero_right]
  rw [← tensorRight_apply, ← ContinuousLinearMap.adjoint_inner_right, hr, inner_zero_right]

def tensorBasis (a : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν)) : HilbertBasis (ι × κ) ℂ (Lp ℂ 2 (μ.prod ν)) :=
  HilbertBasis.mkOfOrthogonalEqBot (tensor_orthonormal a b) (tensor_basis_total a b)

end CoulombPauli

open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_WeakDirectionalDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
namespace CoulombAtom
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def HasWeakDirectionalDerivative (f g : V → ℂ) (v : V) : Prop :=
  ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, f x * Complex.ofReal (lineDeriv ℝ φ x v)) =
      -(∫ x, g x * (φ x : ℂ))

def testBump : ContDiffBump (0 : V) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def testScale (n : ℕ) : ℝ := ((n:ℝ)+1)⁻¹

def testCutoff (n : ℕ) (x : V) : ℝ := (testBump (V := V)) (testScale n • x)

open scoped LineDeriv

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_FreqCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace CoulombLT

section
open CoulombAtom Metric
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def freqCut (R : ℝ) (f : Lp ℂ 2 (volume : Measure V)) : Lp ℂ 2 (volume : Measure V) :=
  ((Lp.memLp f).indicator (measurableSet_ball (x := (0:V)) (ε := R))).toLp ((ball 0 R).indicator (fun ξ => f ξ))

def lowPart (R : ℝ) (f : Lp ℂ 2 (volume : Measure V)) (x : V) : ℂ :=
  𝓕⁻ ((ball 0 R).indicator (fun ξ => (𝓕 f : Lp ℂ 2 volume) ξ)) x

end

open CoulombAtom Metric ComplexConjugate
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def kernelFunction (R : ℝ) (x : V) (ξ : V) : ℂ :=
  (ball 0 R).indicator (fun ξ => conj ((Real.fourierChar (inner ℝ ξ x) : Circle) : ℂ)) ξ

lemma kernelFunction_memLp (R : ℝ) (x : V) : MemLp (kernelFunction R x) 2 := by
  have : IsFiniteMeasure ((volume : Measure V).restrict (ball 0 R)) :=
    ⟨by simpa using measure_ball_lt_top (x := (0:V)) (r := R)⟩
  apply (memLp_indicator_iff_restrict measurableSet_ball).2
  have hc : Continuous (fun ξ : V => conj ((Real.fourierChar (inner ℝ ξ x) : Circle) : ℂ)) := by
    fun_prop
  exact (memLp_const (μ := (volume : Measure V).restrict (ball 0 R)) (1:ℝ)).congr_norm
    hc.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => by simp [Circle.norm_coe])

def lowKernel (R : ℝ) (x : V) : Lp ℂ 2 (volume : Measure V) :=
  (kernelFunction_memLp R x).toLp _

variable {ι : Type*} [Fintype ι]

def BesselFamily (f : ι → Lp ℂ 2 (volume : Measure V)) : Prop :=
  ∀ u, (∑ j, ‖inner ℂ u (f j)‖^2) ≤ ‖u‖^2

end CoulombLT

open MeasureTheory Filter
open scoped ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_DyadicPowerSq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombLT

open CoulombAtom Metric
abbrev Space := EuclideanSpace ℝ (Fin 3)

variable {ι : Type*} [Fintype ι]
def familyDensity (f : ι → Lp ℂ 2 (volume : Measure Space)) (x : Space) : ℝ :=
  ∑ j, ‖f j x‖^2

def highDensity (f : ι → Lp ℂ 2 (volume : Measure Space)) (n : ℕ) (x : Space) : ℝ :=
  ∑ j, ‖f j x - lowPart ((2:ℝ)^n) (f j) x‖^2

end CoulombLT

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Pull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
namespace CoulombPauli

section
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B}

def pull (f : A → B) (hf : MeasurePreserving f μ ν) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ f hf).toContinuousLinearMap

end

section

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]

abbrev configMeasure (N : ℕ) (μ : Measure A) := Measure.pi (fun _ : Fin N => μ)
abbrev sectorL2 (N : ℕ) (μ : Measure A) := Lp ℂ 2 (configMeasure N μ)

lemma memLp_pure {N : ℕ} (u : Fin N → Lp ℂ 2 μ) :
    MemLp (fun x : Fin N → A => ∏ i, u i (x i)) 2 (configMeasure N μ) := by
  have hm : AEStronglyMeasurable (fun x : Fin N → A => ∏ i, u i (x i)) (configMeasure N μ) :=
    Finset.aestronglyMeasurable_fun_prod _ fun i _ =>
      (Lp.aestronglyMeasurable (u i)).comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun _ : Fin N => μ) i)
  apply (memLp_two_iff_integrable_sq_norm hm).2
  simpa only [norm_prod, ← Finset.prod_pow] using
    Integrable.fintype_prod (fun i =>
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (u i))).1 (Lp.memLp (u i)))

def pureTensor {N : ℕ} (u : Fin N → Lp ℂ 2 μ) : sectorL2 N μ :=
  (memLp_pure u).toLp _

def splitAt {N : ℕ} (i : Fin (N+1)) : (Fin (N+1) → A) ≃ᵐ A × (Fin N → A) :=
  MeasurableEquiv.piFinSuccAbove (fun _ => A) i

lemma splitAt_preserving {N : ℕ} (i : Fin (N+1)) :
    MeasurePreserving (splitAt (A := A) i) (configMeasure (N+1) μ) (μ.prod (configMeasure N μ)) :=
  measurePreserving_piFinSuccAbove (fun _ => μ) i

end

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]

def insertOrbital {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ) :
    sectorL2 N μ →L[ℂ] sectorL2 (N+1) μ :=
  (pull (splitAt i) (splitAt_preserving i)).comp (tensorLeft u)

def projectOrbital {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ) :
    sectorL2 (N+1) μ →L[ℂ] sectorL2 (N+1) μ :=
  (insertOrbital i u).comp (insertOrbital i u).adjoint

def permCoords {N : ℕ} (π : Equiv.Perm (Fin N)) : (Fin N → A) ≃ᵐ (Fin N → A) :=
  MeasurableEquiv.piCongrLeft (fun _ => A) π.symm

lemma permCoords_preserving {N : ℕ} (π : Equiv.Perm (Fin N)) :
    MeasurePreserving (permCoords (A := A) π) (configMeasure N μ) (configMeasure N μ) :=
  measurePreserving_piCongrLeft (fun _ : Fin N => μ) π.symm

def permute {N : ℕ} (π : Equiv.Perm (Fin N)) : sectorL2 N μ →L[ℂ] sectorL2 N μ :=
  pull (permCoords π) (permCoords_preserving π)

end CoulombPauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_L2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace CoulombSobolev

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

abbrev L2 (E : Type*) [MeasureSpace E] : Type _ := Lp ℂ 2 (volume : Measure E)

structure Test (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  fn : E → ℝ
  smooth : ContDiff ℝ ∞ fn
  compact : HasCompactSupport fn

namespace Test

def deriv (φ : Test E) (v : E) : Test E where
  fn x := fderiv ℝ φ.fn x v
  smooth := (φ.smooth.fderiv_right (by simp)).clm_apply contDiff_const
  compact := φ.compact.fderiv_apply ℝ v

omit [FiniteDimensional ℝ E] in
lemma memLp (φ : Test E) : MemLp (fun x => (φ.fn x : ℂ)) 2 :=
  (Complex.continuous_ofReal.comp φ.smooth.continuous).memLp_of_hasCompactSupport
    (φ.compact.comp_left (by simp))

def toL2 (φ : Test E) : L2 E := φ.memLp.toLp (fun x => (φ.fn x : ℂ))

end Test

end

section
open CoulombPauli
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [(volume : Measure V).IsAddHaarMeasure]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasureSpace W] [BorelSpace W]
  [(volume : Measure W).IsAddHaarMeasure]

namespace Test
omit [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [(volume : Measure V).IsAddHaarMeasure]
  [FiniteDimensional ℝ W] [MeasureSpace W] [BorelSpace W]
  [(volume : Measure W).IsAddHaarMeasure] in
 def tensor (φ : Test V) (η : Test W) : Test (V × W) where
  fn z := φ.fn z.1 * η.fn z.2
  smooth := (φ.smooth.comp contDiff_fst).mul (η.smooth.comp contDiff_snd)
  compact := HasCompactSupport.of_support_subset_isCompact
    (φ.compact.prod η.compact) (by
      intro z hz
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hz
      exact ⟨subset_tsupport φ.fn hz.1, subset_tsupport η.fn hz.2⟩)

end Test

end

open CoulombPauli
end CoulombSobolev

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Spin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombPauli
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
  [Fintype S] [MeasurableSingletonClass S] {μ : Measure A} [SigmaFinite μ]

omit [SigmaFinite μ] in
lemma memLp_spin (v : S → A → ℂ) (hv : ∀ s, MemLp (v s) 2 μ) :
    MemLp (fun p : A × S => v p.2 p.1) 2 (μ.prod Measure.count) := by
  classical
  have ht (s : S) : MemLp (({p : A × S | p.2 = s} : Set (A × S)).indicator
      (fun p => v s p.1)) 2 (μ.prod Measure.count) :=
    ((hv s).comp_fst Measure.count).indicator (measurable_snd (measurableSet_singleton s))
  have hf : (fun p : A × S => v p.2 p.1) =
      ∑ s : S, ({p : A × S | p.2 = s} : Set (A × S)).indicator (fun p => v s p.1) := by
    funext p
    simp only [Finset.sum_apply, Set.indicator_apply, Set.mem_ofPred_eq]
    simp
  rw [hf]
  exact memLp_finsetSum' _ (fun s _ => ht s)

lemma pi_count_eq {I S : Type*} [Fintype I] [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] :
    Measure.pi (fun _ : I => (Measure.count : Measure S)) = Measure.count := by
  apply Measure.ext_of_singleton
  intro f
  simp
end CoulombPauli

namespace CoulombAtom
namespace Pauli
open CoulombPauli
abbrev OneParticle := Space × Fin 2
abbrev oneMeasure : Measure OneParticle := volume.prod Measure.count
abbrev Many (N : ℕ) := CoulombPauli.sectorL2 N oneMeasure

def splitSpin (N : ℕ) : (Fin N → OneParticle) ≃ᵐ (Configuration N × Spins N) :=
  MeasurableEquiv.arrowProdEquivProdArrow Space (Fin 2) (Fin N)

lemma splitSpin_preserving (N : ℕ) :
    MeasurePreserving (splitSpin N) (configMeasure N oneMeasure)
      ((volume : Measure (Configuration N)).prod (Measure.count : Measure (Spins N))) := by
  have he := measurePreserving_arrowProdEquivProdArrow Space (Fin 2) (Fin N)
    (fun _ => (volume : Measure Space)) (fun _ => (Measure.count : Measure (Fin 2)))
  simpa only [splitSpin, pi_count_eq, ← volume_pi] using he

lemma memLp_value {N : ℕ} (ψ : FormVector N) (hψ : ∀ s, MemLp (ψ.value s) 2) :
    MemLp (fun x : Fin N → OneParticle =>
      ψ.value (fun i => (x i).2) (fun i => (x i).1)) 2 (configMeasure N oneMeasure) := by
  exact (memLp_spin ψ.value hψ).comp_measurePreserving (splitSpin_preserving N)

def toMany {N : ℕ} (ψ : FormVector N) (hψ : ∀ s, MemLp (ψ.value s) 2) : Many N :=
  (memLp_value ψ hψ).toLp _

end Pauli
end CoulombAtom

namespace CoulombPauli
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
local instance instDecidableEq_solutions : DecidableEq S := Classical.decEq S

def countVector (s : S) : Lp ℂ 2 (Measure.count : Measure S) :=
  indicatorConstLp 2 (measurableSet_singleton s) (by simp) 1

open CoulombSobolev

end CoulombPauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_ManyTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombAtom.Pauli
open CoulombPauli CoulombSobolev

def manyTest {N : ℕ} (φ : Test (Configuration N)) (s : Spins N) : Many N :=
  pull (splitSpin N) (splitSpin_preserving N) (tensor φ.toL2 (countVector s))

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
def coordinateSplit {N : ℕ} (i : Fin (N+1)) : (Fin (N+1) → X) ≃L[ℝ] X × (Fin N → X) :=
  ({ toEquiv := (Fin.insertNthEquiv (fun _ : Fin (N+1) => X) i).symm
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : (Fin (N+1) → X) ≃ₗ[ℝ] X × (Fin N → X)).toContinuousLinearEquiv

end CoulombAtom.Pauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CompCL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombSobolev.Test
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def compCL (φ : Test F) (e : E ≃L[ℝ] F) : Test E where
  fn x := φ.fn (e x)
  smooth := φ.smooth.comp e.contDiff
  compact := φ.compact.comp_homeomorph e.toHomeomorph

end CoulombSobolev.Test

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_InsertTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombAtom.Pauli
open CoulombPauli CoulombSobolev

def insertTest {N : ℕ} (i : Fin (N+1)) (φ : Test Space) (η : Test (Configuration N)) :
    Test (Configuration (N+1)) := (φ.tensor η).compCL (coordinateSplit i)

end CoulombAtom.Pauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_Trace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
namespace CoulombPackets

open CoulombPauli

def spinVector (s : Fin 2) : Lp ℂ 2 (Measure.count : Measure (Fin 2)) :=
  indicatorConstLp 2 (measurableSet_singleton s) (by simp) 1

lemma spinVector_inner (s : Fin 2) (u : Lp ℂ 2 (Measure.count : Measure (Fin 2))) :
    inner ℂ (spinVector s) u = u s := by
  rw [spinVector, L2.inner_indicatorConstLp_one]
  simp

lemma spinVector_orthonormal : Orthonormal ℂ spinVector := by
  classical
  rw [orthonormal_iff_ite]
  intro s t
  rw [spinVector, spinVector, L2.inner_indicatorConstLp_one_indicatorConstLp_one]
  by_cases h : s = t
  · subst t; simp
  · have hd : ({s} : Set (Fin 2)) ∩ {t} = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl,rfl⟩; exact h rfl
    simp [hd,h]

def spinBasis : HilbertBasis (Fin 2) ℂ (Lp ℂ 2 (Measure.count : Measure (Fin 2))) :=
  HilbertBasis.mkOfOrthogonalEqBot spinVector_orthonormal (by
    apply le_antisymm _ bot_le
    intro u hu
    change u = 0
    have hv (s : Fin 2) : u s = 0 := by
      rw [← spinVector_inner]
      exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self s)) hu
    apply Lp.ext
    filter_upwards [Lp.coeFn_zero ℂ 2 (Measure.count : Measure (Fin 2))] with s hs
    rw [hv, hs, Pi.zero_apply])

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

abbrev spinSpaceMeasure : Measure (V × Fin 2) := (volume : Measure V).prod Measure.count

end CoulombPackets

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FermionL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
namespace CoulombPackets
open CoulombPauli
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

abbrev fermionL2 (N : ℕ) := sectorL2 N (spinSpaceMeasure (V := V))

def splitFermion {N : ℕ} (i : Fin (N+1)) (ψ : fermionL2 (V := V) (N+1)) :
    Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod (configMeasure N (spinSpaceMeasure (V := V)))) :=
  pull (splitAt i).symm ((splitAt_preserving (μ := spinSpaceMeasure (V := V)) i).symm (splitAt i)) ψ

end CoulombPackets

open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology

namespace CoulombPackets
open CoulombPauli CoulombSobolev
open scoped LineDeriv
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {B : Type*} [MeasurableSpace B] {ν : Measure B} [SigmaFinite ν]

def spinMarginal (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν))
    (s : Fin 2) (w : Lp ℂ 2 ν) : Lp ℂ 2 (volume : Measure V) :=
  (tensorRight (spinVector s)).adjoint ((tensorRight w).adjoint ψ)

def HasWeakSpinPartialDerivative
    (ψ u : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν)) (v : V) : Prop :=
  ∀ (φ : CoulombSobolev.Test V) (s : Fin 2),
    (tensorLeft (tensor (φ.deriv v).toL2 (spinVector s))).adjoint ψ +
      (tensorLeft (tensor φ.toL2 (spinVector s))).adjoint u = 0

end CoulombPackets

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FermionGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombPackets
open CoulombPauli
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
def HasFermionGradient {N : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (ψ : fermionL2 (V := V) (N+1))
    (u : Fin (N+1) → ι → fermionL2 (V := V) (N+1)) : Prop :=
  ∀ i a, HasWeakSpinPartialDerivative (splitFermion i ψ) (splitFermion i (u i a)) (b a)

end CoulombPackets

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_GradientVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombAtom.Pauli
open CoulombPauli CoulombSobolev CoulombPackets

def gradientVector {N : ℕ} (ψ : FormVector N) (i : Fin N) (a : Fin 3) : FormVector N where
  value s := ψ.gradient s i a
  gradient _ _ _ _ := 0

def gradientMany {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ)
    (i : Fin N) (a : Fin 3) : Many N :=
  toMany (gradientVector ψ i a) (fun s => hψ.2.1 s i a)

end CoulombAtom.Pauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_InfiniteDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombLT
open CoulombAtom Metric
variable {ι : Type*}

def infiniteDensity (f : ι → Lp ℂ 2 (volume : Measure Space)) (x : Space) : ℝ≥0∞ :=
  ∑' j, ENNReal.ofReal (‖f j x‖^2)

def fourierMoment (f : Lp ℂ 2 (volume : Measure Space)) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (‖ξ‖^2 * ‖(𝓕 f : Lp ℂ 2 volume) ξ‖^2)

end CoulombLT

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_SumForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

lemma norm_sum_sq_disjoint {ι : Type*} [Fintype ι] (v : ι → ℂ)
    (h : ∀ i j, i ≠ j → v i = 0 ∨ v j = 0) :
    ‖∑ i, v i‖^2 = ∑ i, ‖v i‖^2 := by
  classical
  by_cases hz : ∀ i, v i = 0
  · simp [hz]
  · push Not at hz
    obtain ⟨i,hi⟩ := hz
    have hh (j : ι) (hji : j ≠ i) : v j = 0 := (h j i hji).resolve_right hi
    rw [Finset.sum_eq_single i (fun j _ hj => hh j hj) (by simp),
      Finset.sum_eq_single i (fun j _ hj => by simp [hh j hj]) (by simp)]

end CoulombAtom

open MeasureTheory Filter
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Pointwise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

variable {J E : Type*} [Fintype J] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma square_partition_derivative (p : J → E → ℝ)
    (hp : ∀ j, Differentiable ℝ (p j)) (h : ∀ x, ∑ j, p j x ^ 2 = 1)
    (x v : E) : ∑ j, p j x * lineDeriv ℝ (p j) x v = 0 := by
  have he : (fun x => ∑ j, p j x ^ 2) = fun _ => (1 : ℝ) := funext h
  have hd := congrArg (fun f : E → ℝ => fderiv ℝ f x v) he
  change fderiv ℝ (fun y => ∑ j, p j y ^ 2) x v = fderiv ℝ (fun _ : E => (1 : ℝ)) x v at hd
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun j y => p j y ^ 2) (fun j _ => (hp j x).pow 2), fderiv_const_apply] at hd
  simp only [sum_apply, fderiv_fun_pow 2 (hp _ x), smul_apply,
    smul_eq_mul, Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat, zero_apply] at hd
  have hs : (∑ j, 2 * p j x * fderiv ℝ (p j) x v) =
      2 * ∑ j, p j x * lineDeriv ℝ (p j) x v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [(hp j x).lineDeriv_eq_fderiv]
    ring
  rw [hs] at hd
  linarith

lemma complex_norm_square_expansion (p d : ℝ) (a b : ℂ) :
    ‖(p : ℂ) * a + (d : ℂ) * b‖ ^ 2 = p ^ 2 * ‖a‖ ^ 2 +
      d ^ 2 * ‖b‖ ^ 2 + 2 * (p * d) * (a.re * b.re + a.im * b.im) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma finite_complex_ims (p d : J → ℝ) (hp : ∑ j, p j ^ 2 = 1)
    (hd : ∑ j, p j * d j = 0) (a b : ℂ) :
    (∑ j, ‖(p j : ℂ) * a + (d j : ℂ) * b‖ ^ 2) =
      ‖a‖ ^ 2 + (∑ j, d j ^ 2) * ‖b‖ ^ 2 := by
  simp_rw [complex_norm_square_expansion]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hp, hd]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_TrialSmoothTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

def antisymmetrize {N : ℕ} (g : Configuration N → ℂ) (x : Configuration N) : ℂ :=
  ∑ π : Equiv.Perm (Fin N), (((Equiv.Perm.sign π : ℤ) : ℂ) * g (x ∘ π))

lemma complex_sign_sq {N : ℕ} (π : Equiv.Perm (Fin N)) :
    (((Equiv.Perm.sign π : ℤ) : ℂ)) ^ 2 = 1 := by
  have h : (Equiv.Perm.sign π : ℤ) * (Equiv.Perm.sign π : ℤ) = 1 :=
    congrArg (fun u : ℤˣ => (u : ℤ)) (Int.units_mul_self (Equiv.Perm.sign π))
  have hc : (((Equiv.Perm.sign π : ℤ) : ℂ)) * (((Equiv.Perm.sign π : ℤ) : ℂ)) = 1 := by
    exact_mod_cast h
  simpa only [pow_two] using hc

lemma antisymmetrize_perm {N : ℕ} (g : Configuration N → ℂ)
    (σ : Equiv.Perm (Fin N)) (x : Configuration N) :
    antisymmetrize g (x ∘ σ) =
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * antisymmetrize g x) := by
  classical
  unfold antisymmetrize
  calc
    _ = (((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ π : Equiv.Perm (Fin N),
          (((Equiv.Perm.sign (σ * π) : ℤ) : ℂ) * g (x ∘ (σ * π : Equiv.Perm (Fin N))))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro π _
      have heq : (x ∘ σ) ∘ π = x ∘ (σ * π : Equiv.Perm (Fin N)) := rfl
      rw [heq, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
      have hs := complex_sign_sq σ
      linear_combination -(Equiv.Perm.sign π : ℤ) * g (x ∘ (σ * π : Equiv.Perm (Fin N))) * hs
    _ = _ := by
      congr 1
      simpa only [Equiv.coe_mulLeft] using
        Equiv.sum_comp (Equiv.mulLeft σ)
          (fun π : Equiv.Perm (Fin N) => (((Equiv.Perm.sign π : ℤ) : ℂ) * g (x ∘ π)))

lemma antisymmetrize_smooth {N : ℕ} {g : Configuration N → ℂ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (antisymmetrize g) := by
  classical
  apply ContDiff.sum
  intro π _
  apply contDiff_const.mul
  exact hg.comp (contDiff_pi.mpr (fun i => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Space) (π i)).contDiff))

def permuteConfig {N : ℕ} (π : Equiv.Perm (Fin N)) :
    Configuration N ≃ₜ Configuration N where
  toFun x := x ∘ π
  invFun x := x ∘ π.symm
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  continuous_toFun := continuous_pi (fun i => continuous_apply (π i))
  continuous_invFun := continuous_pi (fun i => continuous_apply (π.symm i))

lemma antisymmetrize_compact {N : ℕ} {g : Configuration N → ℂ}
    (hg : HasCompactSupport g) : HasCompactSupport (antisymmetrize g) := by
  classical
  have h (π : Equiv.Perm (Fin N)) : HasCompactSupport
      (fun x => (((Equiv.Perm.sign π : ℤ) : ℂ) * g (x ∘ π))) :=
    (hg.comp_homeomorph (permuteConfig π)).mul_left
  have hs := HasCompactSupport.finset_sum (s := Finset.univ) (fun π _ => h π)
  have heq : (∑ π : Equiv.Perm (Fin N),
      fun x => (((Equiv.Perm.sign π : ℤ) : ℂ) * g (x ∘ π))) = antisymmetrize g := by
    ext x
    simp only [Finset.sum_apply, antisymmetrize]
  exact heq ▸ hs

def trialCenter (N : ℕ) : Configuration N :=
  fun i => EuclideanSpace.single 0 (4 * ((i.val : ℝ) + 1))

lemma trialCenter_norm {N : ℕ} (i : Fin N) : 4 ≤ ‖trialCenter N i‖ := by
  rw [trialCenter, PiLp.norm_single 2 (fun _ : Fin 3 => ℝ), Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  linarith

lemma trialCenter_separated {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    4 ≤ ‖trialCenter N i - trialCenter N j‖ := by
  change 4 ≤ ‖PiLp.single (β := fun _ : Fin 3 => ℝ) 2 (0 : Fin 3) (4 * ((i.val : ℝ) + 1)) -
    PiLp.single (β := fun _ : Fin 3 => ℝ) 2 (0 : Fin 3) (4 * ((j.val : ℝ) + 1))‖
  rw [← PiLp.single_sub, PiLp.norm_single 2 (fun _ : Fin 3 => ℝ), Real.norm_eq_abs]
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · have hd : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hd : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith

def trialBump (N : ℕ) : ContDiffBump (trialCenter N) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def trialSeed (N : ℕ) (x : Configuration N) : ℂ := ((trialBump N x : ℝ) : ℂ)

lemma trialSeed_smooth (N : ℕ) : ContDiff ℝ ∞ (trialSeed N) :=
  Complex.ofRealCLM.contDiff.comp (trialBump N).contDiff

lemma trialSeed_compact (N : ℕ) : HasCompactSupport (trialSeed N) :=
  (trialBump N).hasCompactSupport.comp_left (g := Complex.ofReal) (by rfl)

lemma trialSeed_support {N : ℕ} {x : Configuration N} (hx : trialSeed N x ≠ 0) :
    ‖x - trialCenter N‖ < 1 := by
  have hn : trialBump N x ≠ 0 := by simpa only [trialSeed, ne_eq, Complex.ofReal_eq_zero] using hx
  have hm : x ∈ Function.support (trialBump N) := hn
  rw [(trialBump N).support_eq] at hm
  exact hm

lemma trialSeed_dist {N : ℕ} {x : Configuration N} (hx : trialSeed N x ≠ 0) (i : Fin N) :
    ‖x i - trialCenter N i‖ < 1 :=
  (norm_le_pi_norm (x - trialCenter N) i).trans_lt (trialSeed_support hx)

lemma trialSeed_nucleus {N : ℕ} {x : Configuration N} (hx : trialSeed N x ≠ 0) (i : Fin N) :
    1 ≤ ‖x i‖ := by
  have hd := trialSeed_dist hx i
  have hc := trialCenter_norm i
  have ht := norm_sub_norm_le (trialCenter N i) (x i)
  rw [norm_sub_rev] at ht
  linarith

lemma trialSeed_pair {N : ℕ} {x : Configuration N} (hx : trialSeed N x ≠ 0)
    (i j : Fin N) (hij : i ≠ j) : 1 ≤ ‖x i - x j‖ := by
  have hd := trialSeed_dist hx i
  have he := trialSeed_dist hx j
  have hc := trialCenter_separated i j hij
  have ht : ‖trialCenter N i - trialCenter N j‖ ≤
      ‖x i - trialCenter N i‖ + ‖x i - x j‖ + ‖x j - trialCenter N j‖ := by
    calc
      _ = ‖(trialCenter N i - x i) + (x i - x j) + (x j - trialCenter N j)‖ := by
        congr 1; abel
      _ ≤ ‖trialCenter N i - x i‖ + ‖x i - x j‖ + ‖x j - trialCenter N j‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by rw [norm_sub_rev (trialCenter N i)]
  linarith

lemma trialSeed_center (N : ℕ) : trialSeed N (trialCenter N) = 1 := by
  have h : trialBump N (trialCenter N) = 1 :=
    (trialBump N).one_of_mem_closedBall (by simp [trialBump])
  simp only [trialSeed, h, Complex.ofReal_one]

lemma trialSeed_center_permuted {N : ℕ} {π : Equiv.Perm (Fin N)} (hπ : π ≠ 1) :
    trialSeed N (trialCenter N ∘ π) = 0 := by
  by_contra hn
  have hi : ∃ i, π i ≠ i := by
    by_contra hh
    push Not at hh
    exact hπ (Equiv.ext hh)
  obtain ⟨i, hi⟩ := hi
  have hd := trialSeed_dist hn i
  have hc := trialCenter_separated (π i) i hi
  change ‖trialCenter N (π i) - trialCenter N i‖ < 1 at hd
  linarith

lemma antisymmetrize_trialSeed_nonzero (N : ℕ) :
    antisymmetrize (trialSeed N) (trialCenter N) = 1 := by
  classical
  unfold antisymmetrize
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin N))]
  · simpa using trialSeed_center N
  · intro π _ hπ
    rw [trialSeed_center_permuted hπ, mul_zero]
  · simp

lemma antisymmetrize_has_nonzero_term {N : ℕ} {g : Configuration N → ℂ}
    {x : Configuration N} (hx : antisymmetrize g x ≠ 0) :
    ∃ π : Equiv.Perm (Fin N), g (x ∘ π) ≠ 0 := by
  classical
  obtain ⟨π, _, hπ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  exact ⟨π, (mul_ne_zero_iff.mp hπ).2⟩

lemma antisymmetrize_trialSeed_nucleus {N : ℕ} {x : Configuration N}
    (hx : antisymmetrize (trialSeed N) x ≠ 0) (i : Fin N) : 1 ≤ ‖x i‖ := by
  obtain ⟨π, hπ⟩ := antisymmetrize_has_nonzero_term hx
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using trialSeed_nucleus hπ (π.symm i)

lemma antisymmetrize_trialSeed_pair {N : ℕ} {x : Configuration N}
    (hx : antisymmetrize (trialSeed N) x ≠ 0) (i j : Fin N) (hij : i ≠ j) : 1 ≤ ‖x i - x j‖ := by
  obtain ⟨π, hπ⟩ := antisymmetrize_has_nonzero_term hx
  have hn : π.symm i ≠ π.symm j := fun h => hij (π.symm.injective h)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
    trialSeed_pair hπ (π.symm i) (π.symm j) hn

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Electrostatic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

lemma triangular_sum_eq_half {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) (hs : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, if j < i then f i j else 0) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, if i ≠ j then f i j else 0 := by
  classical
  have he : (∑ i, ∑ j, if i < j then f i j else 0) =
      ∑ i, ∑ j, if j < i then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  have ht (i j : ι) : (if j < i then f i j else 0) +
      (if i < j then f i j else 0) = if i ≠ j then f i j else 0 := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst j; simp
    · simp [h, h.ne', not_lt.mpr h.le]
  have hh : (∑ i, ∑ j, if j < i then f i j else 0) +
      (∑ i, ∑ j, if i < j then f i j else 0) =
      ∑ i, ∑ j, if i ≠ j then f i j else 0 := by
    simp only [← Finset.sum_add_distrib, ht]
  rw [he] at hh
  linarith

lemma card_small_fin_le (N M : ℕ) : (Finset.univ.filter (fun i : Fin N => i.val < M)).card ≤ M := by
  classical
  have hsubset : (Finset.univ.filter (fun i : Fin N => i.val < M)).image Fin.val ⊆
      Finset.range M := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  have hh := Finset.card_le_card hsubset
  rwa [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_range] at hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_IntegratedStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom


def DeficitSecants (G d : ℝ → ℝ) : Prop :=
  ∀ v t : ℝ, 0 < v → v < t →
    -(t - v) * d t ≤ G t - G v ∧ G t - G v ≤ -(t - v) * d v

def limitPriceEnergy (q t : ℝ) : ℝ := -(4 / 7 : ℝ) * q * t ^ (7 / 4 : ℝ)

def limitDeficit (q t : ℝ) : ℝ := q * t ^ (3 / 4 : ℝ)

def limitSectorEnergy (q t : ℝ) : ℝ := (3 / 7 : ℝ) * q * t ^ (7 / 4 : ℝ)

def scaledDeficit (Z n : ℕ) (m : ℝ) : ℝ := ((Z : ℝ) - n) / m

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SumPairsHalf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
lemma sum_pairs_half {N : ℕ} (f : Fin N → Fin N → ℝ) (hs : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, if i < j then f i j else 0) =
      (1/2:ℝ) * ∑ i, ∑ j, if i ≠ j then f i j else 0 := by
  classical
  have he : (∑ i, ∑ j, if i ≠ j then f i j else 0) =
      (∑ i, ∑ j, if i < j then f i j else 0) +
      (∑ i, ∑ j, if j < i then f i j else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge (le_of_lt h)]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge (le_of_lt h)]
  have hr : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hs j i]
  rw [he, hr]
  ring


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_TensorLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff

section TensorLp
variable {E F : Type*} [MeasureSpace E] [MeasureSpace F]
  [SFinite (volume : Measure E)] [SFinite (volume : Measure F)]

omit [SFinite (volume : Measure E)] [SFinite (volume : Measure F)] in
lemma memLp_tensor_of_aemeasurable
    (hkernel : AEMeasurable
      (fun point : E => Measure.map (Prod.mk point) (volume : Measure F))
      (volume : Measure E))
    {f : E → ℂ} {g : F → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    MemLp (fun point : E × F => f point.1 * g point.2) 2 := by
  have hfst : Measure.QuasiMeasurePreserving (Prod.fst : E × F → E) volume volume := by
    refine ⟨measurable_fst, Measure.AbsolutelyContinuous.mk fun subset hsubset hzero => ?_⟩
    rw [Measure.map_apply measurable_fst hsubset, Measure.volume_eq_prod, Measure.prod,
      Measure.bind_apply (measurable_fst hsubset) hkernel]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with point hpoint
    rw [Measure.map_apply measurable_prodMk_left (measurable_fst hsubset)]
    have hempty : Prod.mk point ⁻¹' (Prod.fst ⁻¹' subset) = (∅ : Set F) := by
      ext other
      simp [hpoint]
    rw [hempty, measure_empty]
    rfl
  have hsnd : Measure.QuasiMeasurePreserving (Prod.snd : E × F → F) volume volume := by
    refine ⟨measurable_snd, Measure.AbsolutelyContinuous.mk fun subset hsubset hzero => ?_⟩
    rw [Measure.map_apply measurable_snd hsubset, Measure.volume_eq_prod, Measure.prod,
      Measure.bind_apply (measurable_snd hsubset) hkernel]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact Filter.Eventually.of_forall fun point => by
      change (Measure.map (Prod.mk point) volume) (Prod.snd ⁻¹' subset) = 0
      rw [Measure.map_apply measurable_prodMk_left (measurable_snd hsubset)]
      exact hzero
  have hm : AEStronglyMeasurable (fun point : E × F => f point.1 * g point.2) :=
    (hf.aestronglyMeasurable.comp_quasiMeasurePreserving hfst).mul
      (hg.aestronglyMeasurable.comp_quasiMeasurePreserving hsnd)
  refine ⟨hm, (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (p := 2) (by norm_num) (by simp)).mpr ?_⟩
  have hfinite_f : (∫⁻ point, ‖f point‖ₑ ^ (2 : ℕ)) < (∞ : ℝ≥0∞) := by
    simpa using lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := 2) (by norm_num) (by simp) hf.2
  have hfinite_g : (∫⁻ point, ‖g point‖ₑ ^ (2 : ℕ)) < (∞ : ℝ≥0∞) := by
    simpa using lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := 2) (by norm_num) (by simp) hg.2
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc
    (∫⁻ point : E × F, ‖f point.1 * g point.2‖ₑ ^ (2 : ℕ))
        ≤ ∫⁻ point : E, ∫⁻ other : F, ‖f point‖ₑ ^ (2 : ℕ) * ‖g other‖ₑ ^ (2 : ℕ) := by
      rw [Measure.volume_eq_prod, Measure.prod]
      refine (Measure.lintegral_bind_le _ _ _).trans ?_
      apply lintegral_mono
      intro point
      simpa only [enorm_mul, mul_pow] using
        lintegral_map_le (fun pair : E × F => ‖f pair.1 * g pair.2‖ₑ ^ (2 : ℕ))
          (Prod.mk point)
    _ = (∫⁻ point, ‖f point‖ₑ ^ (2 : ℕ)) * ∫⁻ other, ‖g other‖ₑ ^ (2 : ℕ) :=
      lintegral_lintegral_mul (hf.aemeasurable.enorm.pow_const 2)
        (hg.aemeasurable.enorm.pow_const 2)
    _ < (∞ : ℝ≥0∞) := ENNReal.mul_lt_top hfinite_f hfinite_g

omit [SFinite (volume : Measure E)] in
lemma memLp_tensor_of_sfinite_right {f : E → ℂ} {g : F → ℂ}
    (hf : MemLp f 2) (hg : MemLp g 2) :
    MemLp (fun point : E × F => f point.1 * g point.2) 2 :=
  memLp_tensor_of_aemeasurable Measurable.map_prodMk_left.aemeasurable hf hg

omit [SFinite (volume : Measure E)] in
/-- Right s-finiteness makes the product kernel measurable, so L² factors have an L² tensor.
Without an a.e. measurable kernel, Mathlib's product uses an arbitrary chosen measure, whose
integrability is not guaranteed by the factors.
The finite-dimensional Haar hypotheses in the applications imply right s-finiteness. -/
lemma memLp_tensor {f : E → ℂ} {g : F → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    MemLp (fun point : E × F => f point.1 * g point.2) 2 :=
  memLp_tensor_of_sfinite_right hf hg

lemma integral_tensor_sq (f : E → ℂ) (g : F → ℂ) :
    (∫ p : E × F, ‖f p.1*g p.2‖^2) = (∫ x, ‖f x‖^2)*(∫ y, ‖g y‖^2) := by
  simp only [norm_mul, mul_pow]
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul (fun x => ‖f x‖^2) (fun y => ‖g y‖^2)

end TensorLp
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [(volume : Measure F).IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure] in
lemma lineDeriv_slice_left {φ : E × F → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (x : E) (y : F) (v : E) :
    lineDeriv ℝ (fun z => φ (z,y)) x v = lineDeriv ℝ φ (x,y) (v,0) := by
  have hh := (hφ.differentiable (by simp) (x,y)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (𝕜 := ℝ) y x))
  have hd := (hh.hasLineDerivAt v).lineDeriv
  rw [(hφ.differentiable (by simp) (x,y)).lineDeriv_eq_fderiv]
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply] using hd

end

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_InsertionSwap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators

lemma real_sign_sq {N : ℕ} (π : Equiv.Perm (Fin N)) :
    (((Equiv.Perm.sign π : ℤ) : ℝ))^2 = 1 := by
  have hh : (Equiv.Perm.sign π : ℤ) * (Equiv.Perm.sign π : ℤ) = 1 :=
    congrArg (fun u : ℤˣ => (u : ℤ)) (Int.units_mul_self (Equiv.Perm.sign π))
  have hh' : (((Equiv.Perm.sign π : ℤ) : ℝ))*(((Equiv.Perm.sign π : ℤ) : ℝ)) = 1 := by
    exact_mod_cast hh
  simpa only [pow_two] using hh'


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TruncationRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

def truncationRadius (k : ℕ) : ℝ := (k : ℝ)+1
lemma truncationRadius_pos (k : ℕ) : 0 < truncationRadius k := by
  unfold truncationRadius; positivity

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FormBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators

lemma insertion_normalizer (N : ℕ) : (Real.sqrt (N+1 : ℝ))⁻¹^2 * (N+1 : ℝ) = 1 := by
  rw [inv_pow,Real.sq_sqrt (by positivity)]
  exact inv_mul_cancel₀ (by positivity)


open MeasureTheory Filter
open scoped Topology BigOperators


open MeasureTheory Filter
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FourierMomentGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombLT

open CoulombPauli CoulombPackets
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

variable {N : ℕ} {κ : Type*}
def fermionFamily (b : HilbertBasis κ ℂ
    (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := V)))))
    (ψ : fermionL2 (V := V) (N+1))
    (p : Fin (N+1) × Fin 2 × κ) : Lp ℂ 2 (volume : Measure V) :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • spinMarginal (splitFermion p.1 ψ) p.2.1 (b p.2.2)

end CoulombLT

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_ContractFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace CoulombPauli
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]

lemma memLp_slice_ae (ψ : Lp ℂ 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => ψ (x,y)) 2 ν := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp ψ).aestronglyMeasurable).mp (Lp.memLp ψ)
  filter_upwards [(Lp.memLp ψ).aestronglyMeasurable.prodMk_left, hi.prod_right_ae] with x hx hy
  exact (memLp_two_iff_integrable_sq_norm hx).mpr hy

def contractFunction (b : Lp ℂ 2 ν) (ψ : Lp ℂ 2 (μ.prod ν)) (x : A) : ℂ :=
  ∫ y, star (b y) * ψ (x,y) ∂ν

omit [SigmaFinite μ] [SigmaFinite ν] in
lemma contractFunction_slice (b : Lp ℂ 2 ν) (ψ : Lp ℂ 2 (μ.prod ν)) (x : A)
    (hx : MemLp (fun y => ψ (x,y)) 2 ν) :
    contractFunction b ψ x = inner ℂ b (hx.toLp (fun y => ψ (x,y))) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hx.coeFn_toLp] with y hy
  simp only [hy, inner]
  ring

lemma contractFunction_sq_le (b : Lp ℂ 2 ν) (ψ : Lp ℂ 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, ‖contractFunction b ψ x‖^2 ≤ ‖b‖^2*(∫ y, ‖ψ (x,y)‖^2 ∂ν) := by
  filter_upwards [memLp_slice_ae ψ] with x hx
  rw [contractFunction_slice b ψ x hx]
  have hc := norm_inner_le_norm (𝕜 := ℂ) b (hx.toLp (fun y => ψ (x,y)))
  have hn : ‖hx.toLp (fun y => ψ (x,y))‖^2 = ∫ y, ‖ψ (x,y)‖^2 ∂ν := by
    rw [l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [hx.coeFn_toLp] with y hy
    rw [hy]
  have hc2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
  simpa only [mul_pow, hn] using hc2

lemma contractFunction_memLp (b : Lp ℂ 2 ν) (ψ : Lp ℂ 2 (μ.prod ν)) :
    MemLp (contractFunction b ψ) 2 μ := by
  have hm : AEStronglyMeasurable (contractFunction b ψ) μ :=
    ((Lp.memLp b).aestronglyMeasurable.comp_snd.star.mul
      (Lp.memLp ψ).aestronglyMeasurable).integral_prod_right'
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp ψ).aestronglyMeasurable).mp (Lp.memLp ψ)
  refine (hi.integral_prod_left.const_mul (‖b‖^2)).mono' (hm.norm.pow 2) ?_
  filter_upwards [contractFunction_sq_le b ψ] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖contractFunction b ψ x‖))] using hx

def contractL2 (b : Lp ℂ 2 ν) (ψ : Lp ℂ 2 (μ.prod ν)) : Lp ℂ 2 μ :=
  (contractFunction_memLp b ψ).toLp _

end CoulombPauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_WeakDerivativeSmulL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal

namespace CoulombLT

section
open CoulombPauli CoulombPackets
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def fermionDensity {N : ℕ} (ψ : fermionL2 (V := V) (N+1)) (x : V) : ℝ≥0∞ :=
  ∑ i : Fin (N+1), ∑ s : Fin 2, ∫⁻ y,
    ENNReal.ofReal (‖splitFermion i ψ ((x,s),y)‖^2)
      ∂(configMeasure N (spinSpaceMeasure (V := V)))

end

open CoulombPauli CoulombPackets CoulombAtom
end CoulombLT

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
open MeasureTheory Set Metric
open scoped ENNReal
namespace CoulombDensity
abbrev Space := EuclideanSpace ℝ (Fin 3)

end CoulombDensity

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_GlobalDensityConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
open MeasureTheory Set Metric
open scoped ENNReal
namespace CoulombAtom

namespace Pauli
open CoulombDensity

def globalDensityConstant : ℝ :=
  192 + (8192/3:ℝ)*(8*Real.pi*(3/8192:ℝ)^(-3/2:ℝ)+3) + 8192/3

end Pauli
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CosetWedge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators

namespace CoulombAtom

instance cosetWedgeFintype {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) :
    Fintype (Equiv.Perm (Fin n) ⧸ H) := Fintype.ofFinite _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BlockPermutations
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

namespace CoulombAtom

def blockPermHom (N M : ℕ) :
    Equiv.Perm (Fin N) × Equiv.Perm (Fin M) →* Equiv.Perm (Fin (N+M)) :=
  finSumFinEquiv.permCongrHom.toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin N) (Fin M))

def blockPerm {N M : ℕ} (π : Equiv.Perm (Fin N)) (ρ : Equiv.Perm (Fin M)) :
    Equiv.Perm (Fin (N+M)) := blockPermHom N M (π,ρ)

def blockSubgroup (N M : ℕ) : Subgroup (Equiv.Perm (Fin (N+M))) :=
  (blockPermHom N M).range

lemma blockSubgroup_mem {N M : ℕ} {κ : Equiv.Perm (Fin (N+M))} :
    κ ∈ blockSubgroup N M ↔ ∃ π ρ, blockPerm π ρ = κ := by
  simp only [blockSubgroup, MonoidHom.mem_range, Prod.exists, blockPerm]

lemma blockPerm_apply_left {N M : ℕ} (π : Equiv.Perm (Fin N)) (ρ : Equiv.Perm (Fin M))
    (i : Fin N) : blockPerm π ρ (finSumFinEquiv (Sum.inl i)) = finSumFinEquiv (Sum.inl (π i)) := by
  simp [blockPerm,blockPermHom,Equiv.permCongr,Equiv.Perm.sumCongrHom_apply]

lemma blockPerm_apply_right {N M : ℕ} (π : Equiv.Perm (Fin N)) (ρ : Equiv.Perm (Fin M))
    (i : Fin M) : blockPerm π ρ (finSumFinEquiv (Sum.inr i)) = finSumFinEquiv (Sum.inr (ρ i)) := by
  simp [blockPerm,blockPermHom,Equiv.permCongr,Equiv.Perm.sumCongrHom_apply]

lemma blockPerm_sign {N M : ℕ} (π : Equiv.Perm (Fin N)) (ρ : Equiv.Perm (Fin M)) :
    Equiv.Perm.sign (blockPerm π ρ) = Equiv.Perm.sign π * Equiv.Perm.sign ρ := by
  simp [blockPerm,blockPermHom,Equiv.Perm.sign_sumCongr]

lemma blockSubgroup_mem_of_maps_left {N M : ℕ} (κ : Equiv.Perm (Fin (N+M)))
    (h : ∀ i : Fin N, ∃ j : Fin N,
      κ (finSumFinEquiv (Sum.inl i)) = finSumFinEquiv (Sum.inl j)) :
    κ ∈ blockSubgroup N M := by
  let σ : Equiv.Perm (Fin N ⊕ Fin M) := finSumFinEquiv.symm.permCongr κ
  have hs : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := h i
    refine ⟨j,?_⟩
    change Sum.inl j = finSumFinEquiv.symm (κ (finSumFinEquiv (Sum.inl i)))
    rw [hj,Equiv.symm_apply_apply]
  obtain ⟨⟨π,ρ⟩,he⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hs
  apply blockSubgroup_mem.mpr
  refine ⟨π,ρ,?_⟩
  apply finSumFinEquiv.symm.permCongr.injective
  calc
    _ = Equiv.Perm.sumCongrHom (Fin N) (Fin M) (π,ρ) := by
      ext i
      simp [blockPerm,blockPermHom,Equiv.permCongr]
    _ = _ := he

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BlockEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators

lemma sum_pair_blocks {N M : ℕ} (f : Fin (N+M) → Fin (N+M) → ℝ) :
    (∑ i, ∑ j, if i < j then f i j else 0) =
      (∑ i : Fin N, ∑ j : Fin N, if i < j then
        f (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) else 0) +
      (∑ i : Fin M, ∑ j : Fin M, if i < j then
        f (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) else 0) +
      ∑ i : Fin N, ∑ j : Fin M,
        f (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) := by
  have he (g : Fin (N+M) → ℝ) : (∑ i, g i) =
      (∑ i : Fin N, g (finSumFinEquiv (Sum.inl i))) +
      ∑ i : Fin M, g (finSumFinEquiv (Sum.inr i)) := by
    rw [← Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]
  rw [he]
  simp_rw [he,Finset.sum_add_distrib]
  have hlr (i : Fin N) (j : Fin M) : finSumFinEquiv (Sum.inl i) < finSumFinEquiv (Sum.inr j) := by
    simp only [finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,Fin.lt_def,
      Fin.val_castAdd,Fin.val_natAdd]
    omega
  have hrl (i : Fin M) (j : Fin N) : ¬finSumFinEquiv (Sum.inr i) < finSumFinEquiv (Sum.inl j) :=
    not_lt_of_ge (hlr j i).le
  have hll (i j : Fin N) : (finSumFinEquiv : Fin N ⊕ Fin M ≃ Fin (N+M)) (Sum.inl i) < finSumFinEquiv (Sum.inl j) ↔ i < j := by
    simp only [finSumFinEquiv_apply_left,Fin.lt_def,Fin.val_castAdd]
  have hrr (i j : Fin M) : (finSumFinEquiv : Fin N ⊕ Fin M ≃ Fin (N+M)) (Sum.inr i) < finSumFinEquiv (Sum.inr j) ↔ i < j := by
    simp
  simp_rw [hlr,hrl,hll,hrr,ite_true,ite_false,Finset.sum_const_zero,zero_add]
  ring

open MeasureTheory
open scoped BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Slater
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

namespace CoulombAtom

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

def slaterTensor (φ : Fin n → α → ℂ) (σ : Equiv.Perm (Fin n)) (x : Fin n → α) : ℂ :=
  ∏ i, φ (σ i) (x i)

def slaterRaw (φ : Fin n → α → ℂ) (x : Fin n → α) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), (((σ.sign : ℤ) : ℂ)) * slaterTensor φ σ x

omit [MeasurableSpace α] in
lemma slaterRaw_eq_det (φ : Fin n → α → ℂ) (x : Fin n → α) :
    slaterRaw φ x = Matrix.det (Matrix.of (fun i j => φ i (x j))) := by
  rw [Matrix.det_apply']
  rfl

lemma memLp_slaterTensor {φ : Fin n → α → ℂ} (hφ : ∀ i, MemLp (φ i) 2 μ)
    (σ : Equiv.Perm (Fin n)) :
    MemLp (slaterTensor φ σ) 2 (Measure.pi fun _ : Fin n => μ) := by
  have hm : AEStronglyMeasurable (slaterTensor φ σ) (Measure.pi fun _ : Fin n => μ) := by
    unfold slaterTensor
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (hφ (σ i)).aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => μ) i)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [slaterTensor, norm_prod, Finset.prod_pow] using
    Integrable.fintype_prod (fun i : Fin n => (hφ (σ i)).norm.integrable_sq)

lemma memLp_slaterRaw {φ : Fin n → α → ℂ} (hφ : ∀ i, MemLp (φ i) 2 μ) :
    MemLp (slaterRaw φ) 2 (Measure.pi fun _ : Fin n => μ) :=
  memLp_finsetSum _ (fun σ _ => (memLp_slaterTensor hφ σ).const_mul _)

lemma slaterTensor_inner (φ ψ : Fin n → α → ℂ) (σ τ : Equiv.Perm (Fin n)) :
    (∫ x, conj (slaterTensor φ σ x) * slaterTensor ψ τ x
      ∂Measure.pi (fun _ : Fin n => μ)) =
      ∏ i, ∫ t, conj (φ (σ i) t) * ψ (τ i) t ∂μ := by
  simp only [slaterTensor, map_prod, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (μ := fun _ : Fin n => μ)
    (fun i t => conj (φ (σ i) t) * ψ (τ i) t)

lemma permutations_eq_of_agree_except (σ τ : Equiv.Perm (Fin n)) (j : Fin n)
    (h : ∀ i, i ≠ j → σ i = τ i) : σ = τ := by
  apply Equiv.ext
  intro i
  by_cases hij : i = j
  · subst i
    obtain ⟨k,hk⟩ := τ.surjective (σ j)
    by_cases hkj : k = j
    · simpa only [hkj] using hk.symm
    · have hh := h k hkj
      have he : σ k = σ j := hh.trans hk
      exact False.elim (hkj (σ.injective he))
  · exact h i hij

def slater (φ : Fin n → α → ℂ) (x : Fin n → α) : ℂ :=
  (Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹ * slaterRaw φ x

lemma memLp_slater {φ : Fin n → α → ℂ} (hφ : ∀ i, MemLp (φ i) 2 μ) :
    MemLp (slater φ) 2 (Measure.pi fun _ : Fin n => μ) :=
  (memLp_slaterRaw hφ).const_mul _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterBody
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

namespace CoulombAtom

lemma complex_integral_norm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : α → ℂ) :
    (∫ x, conj (f x) * f x ∂μ) = (∫ x, ‖f x‖^2 ∂μ : ℝ) := by
  calc
    _ = ∫ x, (Complex.ofReal (‖f x‖^2)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simpa only [Complex.sq_norm] using
          (Complex.normSq_eq_conj_mul_self (z := f x)).symm)
    _ = _ := integral_ofReal (𝕜 := ℂ)

lemma integral_norm_sq_weighted_sum {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} [Fintype ι] (a : ι → ℂ) (f : ι → α → ℂ)
    (hf : ∀ i, MemLp (f i) 2 μ) :
    (Complex.ofReal (∫ x, ‖∑ i, a i * f i x‖^2 ∂μ)) =
      ∑ i, ∑ j, conj (a i) * a j * (∫ x, conj (f i x) * f j x ∂μ) := by
  rw [← complex_integral_norm_sq]
  have hi (i j : ι) : Integrable (fun x => conj (a i) * a j *
      (conj (f i x) * f j x)) μ :=
    ((hf i).star.integrable_mul (hf j)).const_mul _
  have he (x : α) : conj (∑ i, a i * f i x) * (∑ i, a i * f i x) =
      ∑ i, ∑ j, conj (a i) * a j * (conj (f i x) * f j x) := by
    simp only [map_sum, map_mul]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_const_mul]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

def slaterCoordinateTensor (φ ψ : Fin n → α → ℂ) (j : Fin n)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → α) : ℂ :=
  ∏ i, (if i=j then ψ else φ) (σ i) (x i)

def slaterCoordinateRaw (φ ψ : Fin n → α → ℂ) (j : Fin n) (x : Fin n → α) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((σ.sign : ℤ) : ℂ) * slaterCoordinateTensor φ ψ j σ x

lemma memLp_slaterCoordinateTensor {φ ψ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (j : Fin n) (σ : Equiv.Perm (Fin n)) :
    MemLp (slaterCoordinateTensor φ ψ j σ) 2 (Measure.pi fun _ : Fin n => μ) := by
  have h (i : Fin n) : MemLp ((if i=j then ψ else φ) (σ i)) 2 μ := by
    split_ifs <;> first | exact hψ _ | exact hφ _
  have hm : AEStronglyMeasurable (slaterCoordinateTensor φ ψ j σ)
      (Measure.pi fun _ : Fin n => μ) := by
    unfold slaterCoordinateTensor
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (h i).aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => μ) i)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [slaterCoordinateTensor, norm_prod, Finset.prod_pow] using
    Integrable.fintype_prod (fun i : Fin n => (h i).norm.integrable_sq)

lemma memLp_slaterCoordinateRaw {φ ψ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hψ : ∀ i, MemLp (ψ i) 2 μ) (j : Fin n) :
    MemLp (slaterCoordinateRaw φ ψ j) 2 (Measure.pi fun _ : Fin n => μ) :=
  memLp_finsetSum _ (fun σ _ => (memLp_slaterCoordinateTensor hφ hψ j σ).const_mul _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterPairAlgebra
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SlaterPairAlgebra_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

lemma permutations_eq_or_swap_of_agree_except_two {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) (j k : Fin n)
    (h : ∀ i, i ≠ j → i ≠ k → σ i = τ i) :
    τ = σ ∨ τ = σ * Equiv.swap j k := by
  classical
  by_cases hj : σ j = τ j
  · left
    exact (permutations_eq_of_agree_except σ τ k (fun i hik => by
      by_cases hij : i=j
      · simpa only [hij] using hj
      · exact h i hij hik)).symm
  · right
    have hk : σ k = τ j := by
      obtain ⟨i,hi⟩ := σ.surjective (τ j)
      by_cases hij : i=j
      · exact (hj (hij ▸ hi)).elim
      by_cases hik : i=k
      · exact hik ▸ hi
      have hit : τ i = τ j := (h i hij hik).symm.trans hi
      exact (hij (τ.injective hit)).elim
    apply (permutations_eq_of_agree_except (σ * Equiv.swap j k) τ k ?_).symm
    intro i hik
    by_cases hij : i=j
    · subst i
      simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using hk
    · simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hij hik] using h i hij hik

abbrev SlaterPairRest {n : ℕ} (j k : Fin n) := {i : Fin n // i ≠ j ∧ i ≠ k}

def slaterRestTensor {α : Type*} {n : ℕ} (φ : Fin n → α → ℂ)
    (j k : Fin n) (σ : Equiv.Perm (Fin n)) (x : SlaterPairRest j k → α) : ℂ :=
  ∏ i : SlaterPairRest j k, φ (σ i) (x i)

def slaterPairAmplitude {α : Type*} {n : ℕ} (φ : Fin n → α → ℂ)
    (j k : Fin n) (σ : Equiv.Perm (Fin n)) (u v : α) : ℂ :=
  φ (σ j) u * φ (σ k) v

def slaterPairSliceRaw {α : Type*} {n : ℕ} (φ : Fin n → α → ℂ)
    (j k : Fin n) (u v : α) (x : SlaterPairRest j k → α) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((σ.sign : ℤ) : ℂ) *
    slaterPairAmplitude φ j k σ u v * slaterRestTensor φ j k σ x

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

lemma memLp_slaterRestTensor {φ : Fin n → α → ℂ} (hφ : ∀ i, MemLp (φ i) 2 μ)
    (j k : Fin n) (σ : Equiv.Perm (Fin n)) :
    MemLp (slaterRestTensor φ j k σ) 2 (Measure.pi fun _ : SlaterPairRest j k => μ) := by
  have hm : AEStronglyMeasurable (slaterRestTensor φ j k σ)
      (Measure.pi fun _ : SlaterPairRest j k => μ) := by
    unfold slaterRestTensor
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (hφ (σ i)).aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : SlaterPairRest j k => μ) i)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [slaterRestTensor, norm_prod, Finset.prod_pow] using
    Integrable.fintype_prod (fun i : SlaterPairRest j k => (hφ (σ i)).norm.integrable_sq)

lemma perm_mul_swap_ne_self {n : ℕ} (σ : Equiv.Perm (Fin n)) {j k : Fin n} (hjk : j ≠ k) :
    σ * Equiv.swap j k ≠ σ := by
  intro h
  have he := congrArg (fun τ : Equiv.Perm (Fin n) => τ j) h
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at he
  exact hjk (σ.injective he).symm

lemma complex_sign_mul_swap {n : ℕ} (σ : Equiv.Perm (Fin n)) {j k : Fin n} (hjk : j ≠ k) :
    ((((σ * Equiv.swap j k).sign : ℤ) : ℂ)) = -((σ.sign : ℤ) : ℂ) := by
  simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hjk]

end Work_SlaterPairAlgebra_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

def slaterPairIndex {n : ℕ} {j k : Fin n} (hjk : j ≠ k) :
    Fin 2 ≃ {i : Fin n // i=j ∨ i=k} where
  toFun a := if a=0 then ⟨j,Or.inl rfl⟩ else ⟨k,Or.inr rfl⟩
  invFun i := if i.1=j then 0 else 1
  left_inv a := by
    fin_cases a <;> simp [Ne.symm hjk]
  right_inv i := by
    rcases i with ⟨i,hi|hi⟩
    · subst i; simp
    · subst i; simp [Ne.symm hjk]

def slaterRestIndex {n : ℕ} (j k : Fin n) :
    SlaterPairRest j k ≃ {i : Fin n // ¬ (i=j ∨ i=k)} where
  toFun i := ⟨i,not_or.mpr i.2⟩
  invFun i := ⟨i,(not_or.mp i.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

def slaterPairSplit {j k : Fin n} (hjk : j ≠ k) :
    (Fin n → α) ≃ᵐ (α × α) × (SlaterPairRest j k → α) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => α) (fun i => i=j ∨ i=k)).trans
    ((MeasurableEquiv.prodCongr
      ((MeasurableEquiv.piCongrLeft (fun _ : {i : Fin n // i=j ∨ i=k} => α)
        (slaterPairIndex hjk)).symm.trans (MeasurableEquiv.piFinTwo (fun _ => α)))
      (MeasurableEquiv.piCongrLeft (fun _ : {i : Fin n // ¬(i=j ∨ i=k)} => α)
        (slaterRestIndex j k)).symm))

lemma slaterPairSplit_preserving {j k : Fin n} (hjk : j ≠ k) :
    MeasurePreserving (slaterPairSplit (α := α) hjk)
      (Measure.pi fun _ : Fin n => μ)
      ((μ.prod μ).prod (Measure.pi fun _ : SlaterPairRest j k => μ)) := by
  apply (measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => μ)
    (fun i => i=j ∨ i=k)).trans
  exact ((measurePreserving_piCongrLeft (fun _ : {i : Fin n // i=j ∨ i=k} => μ)
    (slaterPairIndex hjk)).symm.trans (measurePreserving_piFinTwo (fun _ => μ))).prod
    (measurePreserving_piCongrLeft (fun _ : {i : Fin n // ¬(i=j ∨ i=k)} => μ)
      (slaterRestIndex j k)).symm

lemma slaterPairSplit_apply {j k : Fin n} (hjk : j ≠ k) (x : Fin n → α) :
    slaterPairSplit hjk x = ((x j,x k),fun i : SlaterPairRest j k => x i) := by
  rfl

lemma slaterPairSplit_symm_apply_left {j k : Fin n} (hjk : j ≠ k)
    (u v : α) (y : SlaterPairRest j k → α) :
    (slaterPairSplit hjk).symm ((u,v),y) j = u := by
  have h := congrArg (fun z : (α×α) × (SlaterPairRest j k → α) => z.1.1)
    ((slaterPairSplit hjk).apply_symm_apply ((u,v),y))
  simpa only [slaterPairSplit_apply] using h

lemma slaterPairSplit_symm_apply_right {j k : Fin n} (hjk : j ≠ k)
    (u v : α) (y : SlaterPairRest j k → α) :
    (slaterPairSplit hjk).symm ((u,v),y) k = v := by
  have h := congrArg (fun z : (α×α) × (SlaterPairRest j k → α) => z.1.2)
    ((slaterPairSplit hjk).apply_symm_apply ((u,v),y))
  simpa only [slaterPairSplit_apply] using h

lemma slaterPairSplit_symm_apply_rest {j k : Fin n} (hjk : j ≠ k)
    (u v : α) (y : SlaterPairRest j k → α) (i : SlaterPairRest j k) :
    (slaterPairSplit hjk).symm ((u,v),y) i = y i := by
  have h := congrArg (fun z : (α×α) × (SlaterPairRest j k → α) => z.2 i)
    ((slaterPairSplit hjk).apply_symm_apply ((u,v),y))
  simpa only [slaterPairSplit_apply] using h

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterPairTrace
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SlaterPairTrace_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

def slaterPairContraction (φ : Fin n → α → ℂ) (i l : Fin n) (u v : α) : ℂ :=
  conj (φ i u * φ l v) * (φ i u * φ l v) -
    conj (φ i u * φ l v) * (φ l u * φ i v)

omit [MeasurableSpace α] in
lemma slaterPairContraction_self (φ : Fin n → α → ℂ) (i : Fin n) (u v : α) :
    slaterPairContraction φ i i u v = 0 := by
  simp only [slaterPairContraction, sub_self]

omit [MeasurableSpace α] in
lemma slaterPairAmplitude_contraction (φ : Fin n → α → ℂ) (j k : Fin n)
    (σ : Equiv.Perm (Fin n)) (u v : α) :
    conj (slaterPairAmplitude φ j k σ u v) * slaterPairAmplitude φ j k σ u v -
      conj (slaterPairAmplitude φ j k σ u v) *
        slaterPairAmplitude φ j k (σ * Equiv.swap j k) u v =
      slaterPairContraction φ (σ j) (σ k) u v := by
  simp only [slaterPairAmplitude, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right, slaterPairContraction]

omit [MeasurableSpace α] in
lemma slaterPairContraction_sum (φ : Fin n → α → ℂ) (u v : α) :
    (∑ i : Fin n, ∑ l : Fin n, slaterPairContraction φ i l u v) =
      (Complex.ofReal ((∑ i : Fin n, ‖φ i u‖^2) * (∑ i : Fin n, ‖φ i v‖^2) -
        ‖∑ i : Fin n, φ i u * conj (φ i v)‖^2)) := by
  have hnorm (z : ℂ) : Complex.ofReal (‖z‖^2) = conj z * z := by
    simpa only [Complex.sq_norm] using Complex.normSq_eq_conj_mul_self (z := z)
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sum, hnorm]
  simp only [slaterPairContraction, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    simp only [map_mul]
    ring
  · simp only [map_sum, map_mul, starRingEnd_self_apply]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring

end Work_SlaterPairTrace_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

omit [MeasurableSpace α] in
lemma slaterTensor_pair (φ : Fin n → α → ℂ) (σ : Equiv.Perm (Fin n))
    {j k : Fin n} (hjk : j ≠ k) (x : Fin n → α) :
    slaterTensor φ σ x = slaterPairAmplitude φ j k σ (x j) (x k) *
      slaterRestTensor φ j k σ (fun i => x i) := by
  classical
  unfold slaterTensor slaterPairAmplitude slaterRestTensor
  have hk : k ∈ (Finset.univ : Finset (Fin n)).erase j :=
    Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ _ hk, ← mul_assoc]
  congr 1
  exact Finset.prod_subtype _ (fun i => by simp [and_comm]) _

lemma slaterRaw_pair_split (φ : Fin n → α → ℂ) {j k : Fin n} (hjk : j ≠ k)
    (u v : α) (y : SlaterPairRest j k → α) :
    slaterRaw φ ((slaterPairSplit hjk).symm ((u,v),y)) =
      slaterPairSliceRaw φ j k u v y := by
  unfold slaterRaw slaterPairSliceRaw
  apply Finset.sum_congr rfl
  intro σ _
  rw [slaterTensor_pair φ σ hjk, slaterPairSplit_symm_apply_left,
    slaterPairSplit_symm_apply_right]
  simp only [slaterRestTensor, slaterPairSplit_symm_apply_rest]
  ring

lemma slater_pair_split_norm_sq (φ : Fin n → α → ℂ) {j k : Fin n} (hjk : j ≠ k)
    (u v : α) (y : SlaterPairRest j k → α) :
    ‖slater φ ((slaterPairSplit hjk).symm ((u,v),y))‖^2 =
      (n.factorial : ℝ)⁻¹ * ‖slaterPairSliceRaw φ j k u v y‖^2 := by
  simp only [slater, slaterRaw_pair_split, norm_mul, mul_pow, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (show (0:ℝ) ≤ n.factorial by positivity)]

lemma slater_pair_observable {φ : Fin n → α → ℂ} {j k : Fin n} (hjk : j ≠ k)
    (w : α × α → ℝ)
    (hi : Integrable (fun x => w (x j,x k) * ‖slater φ x‖^2)
      (Measure.pi fun _ : Fin n => μ)) :
    (∫ x, w (x j,x k) * ‖slater φ x‖^2 ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ z, w z * ((n.factorial : ℝ)⁻¹ *
        ∫ y, ‖slaterPairSliceRaw φ j k z.1 z.2 y‖^2
          ∂Measure.pi (fun _ : SlaterPairRest j k => μ)) ∂μ.prod μ := by
  have mp := (slaterPairSplit_preserving (μ := μ) hjk).symm
  have he : (fun z : (α×α) × (SlaterPairRest j k → α) =>
      w ((slaterPairSplit hjk).symm z j,(slaterPairSplit hjk).symm z k) *
        ‖slater φ ((slaterPairSplit hjk).symm z)‖^2) =
      (fun z => w z.1 * ((n.factorial : ℝ)⁻¹ *
        ‖slaterPairSliceRaw φ j k z.1.1 z.1.2 z.2‖^2)) := by
    funext ⟨⟨u,v⟩,y⟩
    simp only [slaterPairSplit_symm_apply_left,
      slaterPairSplit_symm_apply_right, slater_pair_split_norm_sq]
  have hs : Integrable (fun z : (α×α) × (SlaterPairRest j k → α) =>
      w z.1 * ((n.factorial : ℝ)⁻¹ * ‖slaterPairSliceRaw φ j k z.1.1 z.1.2 z.2‖^2))
      ((μ.prod μ).prod (Measure.pi fun _ : SlaterPairRest j k => μ)) := by
    simpa only [Function.comp_def, he] using mp.integrable_comp_of_integrable hi
  calc
    _ = ∫ z : (α×α) × (SlaterPairRest j k → α),
        w z.1 * ((n.factorial : ℝ)⁻¹ * ‖slaterPairSliceRaw φ j k z.1.1 z.1.2 z.2‖^2)
        ∂(μ.prod μ).prod (Measure.pi fun _ : SlaterPairRest j k => μ) := by
      rw [← he]
      exact (mp.integral_comp' (fun x => w (x j,x k) * ‖slater φ x‖^2)).symm
    _ = _ := by
      rw [integral_prod _ hs]
      simp only [integral_const_mul]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterTwoBody
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SlaterTwoBody_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

def slaterPairMarginal (φ : Fin n → α → ℂ) (j k : Fin n) (z : α × α) : ℝ :=
  if j ≠ k then (n.factorial : ℝ)⁻¹ *
    ∫ y, ‖slaterPairSliceRaw φ j k z.1 z.2 y‖^2
      ∂Measure.pi (fun _ : SlaterPairRest j k => μ) else 0

end Work_SlaterTwoBody_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

def slaterCoordinate (φ ψ : Fin n → α → ℂ) (j : Fin n) (x : Fin n → α) : ℂ :=
  (Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹ * slaterCoordinateRaw φ ψ j x

lemma memLp_slaterCoordinate {φ ψ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hψ : ∀ i, MemLp (ψ i) 2 μ) (j : Fin n) :
    MemLp (slaterCoordinate φ ψ j) 2 (Measure.pi fun _ : Fin n => μ) :=
  (memLp_slaterCoordinateRaw hφ hψ j).const_mul _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterSymmetry
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SlaterSymmetry_scope

open MeasureTheory
open scoped BigOperators ComplexConjugate

variable {α : Type*} {n : ℕ}

lemma slaterRaw_perm (φ : Fin n → α → ℂ) (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    slaterRaw φ (x ∘ σ) = ((σ.sign : ℤ) : ℂ) * slaterRaw φ x := by
  rw [slaterRaw_eq_det, slaterRaw_eq_det]
  exact Matrix.det_permute' σ (Matrix.of (fun i j => φ i (x j)))

lemma slater_perm (φ : Fin n → α → ℂ) (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    slater φ (x ∘ σ) = ((σ.sign : ℤ) : ℂ) * slater φ x := by
  rw [slater, slaterRaw_perm, slater]
  ring

end Work_SlaterSymmetry_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

abbrev SlaterParticle := Fin 2 × Space

def slaterParticles {n : ℕ} (s : Spins n) (x : Configuration n) : Fin n → SlaterParticle :=
  fun i => (s i, x i)

def spatialOrbitalDerivative {n : ℕ} (φ : Fin n → SlaterParticle → ℂ)
    (a : Fin 3) (i : Fin n) (z : SlaterParticle) : ℂ :=
  fderiv ℝ (fun x : Space => φ i (z.1,x)) z.2 (EuclideanSpace.single a 1)

lemma slater_spatial_tensor_smooth {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (s : Spins n) (σ : Equiv.Perm (Fin n)) :
    ContDiff ℝ ∞ (fun x : Configuration n => slaterTensor φ σ (slaterParticles s x)) := by
  unfold slaterTensor slaterParticles
  apply contDiff_prod
  intro i _
  exact (hφ (σ i) (s i)).comp (f := fun y : Configuration n => y i)
    (ContinuousLinearMap.proj i : Configuration n →L[ℝ] Space).contDiff

lemma slater_spatial_tensor_compact {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (s : Spins n) (σ : Equiv.Perm (Fin n)) :
    HasCompactSupport (fun x : Configuration n => slaterTensor φ σ (slaterParticles s x)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_univ_pi (fun i => hφ (σ i) (s i)))
  intro x hx i _
  apply subset_tsupport (fun t : Space => φ (σ i) (s i,t))
  exact (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)

lemma slater_spatial_raw_smooth {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x))) (s : Spins n) :
    ContDiff ℝ ∞ (fun x : Configuration n => slaterRaw φ (slaterParticles s x)) := by
  apply ContDiff.sum
  intro σ _
  exact contDiff_const.mul (slater_spatial_tensor_smooth hφ s σ)

lemma slater_spatial_smooth {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x))) (s : Spins n) :
    ContDiff ℝ ∞ (fun x : Configuration n => slater φ (slaterParticles s x)) :=
  contDiff_const.mul (slater_spatial_raw_smooth hφ s)

lemma slater_spatial_compact {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x))) (s : Spins n) :
    HasCompactSupport (fun x : Configuration n => slater φ (slaterParticles s x)) := by
  have h (σ : Equiv.Perm (Fin n)) : HasCompactSupport (fun x : Configuration n =>
      ((σ.sign : ℤ) : ℂ) * slaterTensor φ σ (slaterParticles s x)) :=
    (slater_spatial_tensor_compact hφ s σ).mul_left
  have hs := HasCompactSupport.finset_sum (s := Finset.univ) (fun σ _ => h σ)
  have he : (∑ σ : Equiv.Perm (Fin n), fun x : Configuration n =>
      ((σ.sign : ℤ) : ℂ) * slaterTensor φ σ (slaterParticles s x)) =
      (fun x : Configuration n => slaterRaw φ (slaterParticles s x)) := by
    ext x
    simp only [Finset.sum_apply, slaterRaw]
  have hh : HasCompactSupport (fun x : Configuration n => slaterRaw φ (slaterParticles s x)) :=
    he ▸ hs
  exact hh.mul_left

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterMeasure
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

lemma pi_count_eq_count {ι β : Type*} [Fintype ι] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β] :
    (Measure.pi fun _ : ι => (Measure.count : Measure β)) = Measure.count := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.pi_singleton, Measure.count_singleton]
  simp only [Measure.count_singleton, Finset.prod_const_one]

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpinSpaceIntegrable
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SpinSpaceIntegrable_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

lemma continuous_slater {α : Type*} [TopologicalSpace α] {n : ℕ}
    {φ : Fin n → α → ℂ} (hφ : ∀ i, Continuous (φ i)) : Continuous (slater φ) := by
  unfold slater slaterRaw slaterTensor
  apply continuous_const.mul
  apply continuous_finsetSum
  intro σ _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro i _
  exact (hφ (σ i)).comp (continuous_apply i)

end Work_SpinSpaceIntegrable_scope

open MeasureTheory
open scoped BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterRepulsion
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

abbrev slaterDirectDensity {n : ℕ} (φ : Fin n → SlaterParticle → ℂ)
    (z : SlaterParticle) : ℝ := ∑ i : Fin n, ‖φ i z‖^2

abbrev slaterExchangeDensity {n : ℕ} (φ : Fin n → SlaterParticle → ℂ)
    (z : SlaterParticle × SlaterParticle) : ℝ :=
  ‖∑ i : Fin n, φ i z.1 * conj (φ i z.2)‖^2

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

lemma memLp_potential_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} {V : α → ℝ} (hf : Measurable f) (hV : Measurable V)
    (hVn : ∀ x, 0 ≤ V x) (hi : Integrable (fun x => V x * ‖f x‖^2) μ) :
    MemLp (fun x => (Real.sqrt (V x) : ℂ)*f x) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm
    ((Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp hV)).mul hf).aestronglyMeasurable).mpr
  change Integrable (fun x => ‖(Real.sqrt (V x) : ℂ)*f x‖^2) μ
  simpa only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hVn _)] using hi

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_OrbitalPole
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def occupationWeight (p : ι → ℝ) (m : ι → Bool) : ℝ :=
  ∏ i, if m i then p i else 1-p i

omit [DecidableEq ι] in
lemma occupationWeight_nonneg {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (m : ι → Bool) : 0 ≤ occupationWeight p m := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact (hp i).1
  · exact sub_nonneg.mpr (hp i).2

lemma occupation_product (p : ι → ℝ) (f : ι → Bool → ℝ) :
    (∑ m : ι → Bool, occupationWeight p m * ∏ i, f i (m i)) =
      ∏ i, ((1-p i) * f i false + p i * f i true) := by
  simp only [occupationWeight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => (if b then p i else 1-p i)*f i b)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  ring

lemma occupationWeight_sum (p : ι → ℝ) : (∑ m : ι → Bool, occupationWeight p m) = 1 := by
  simpa only [Finset.prod_const_one,mul_one,sub_add_cancel,Finset.prod_const_one] using
    occupation_product p (fun _ _ => 1)

lemma occupation_first (p : ι → ℝ) (j : ι) :
    (∑ m : ι → Bool, occupationWeight p m * (if m j then 1 else 0)) = p j := by
  have hp := occupation_product p (fun i b => if i=j then (if b then 1 else 0) else 1)
  have he (m : ι → Bool) :
      (∏ i : ι, if i=j then (if m i then (1:ℝ) else 0) else 1) = if m j then 1 else 0 := by
    simp
  simp_rw [he] at hp
  rw [hp]
  trans ∏ i : ι, if i=j then p i else 1
  · apply Finset.prod_congr rfl
    intro i _
    by_cases hij : i=j <;> simp [hij]
  · simp

lemma occupation_second {p : ι → ℝ} {j k : ι} (hjk : j ≠ k) :
    (∑ m : ι → Bool, occupationWeight p m *
      ((if m j then 1 else 0) * (if m k then 1 else 0))) = p j*p k := by
  have hp := occupation_product p (fun i b =>
    (if i=j then (if b then (1:ℝ) else 0) else 1) *
    (if i=k then (if b then (1:ℝ) else 0) else 1))
  simp only [Finset.prod_mul_distrib] at hp
  have he (m : ι → Bool) (r : ι) :
      (∏ i : ι, if i=r then (if m i then (1:ℝ) else 0) else 1) = if m r then 1 else 0 := by
    simp
  simp_rw [he] at hp
  rw [hp]
  trans ∏ i : ι, (if i=j then p i else 1) * (if i=k then p i else 1)
  · apply Finset.prod_congr rfl
    intro i _
    by_cases hij : i=j
    · subst i; simp [hjk]
    · by_cases hik : i=k
      · subst i; simp [hij]
      · simp [hij,hik]
  · rw [Finset.prod_mul_distrib]
    simp

lemma occupation_sum (p : ι → ℝ) (f : ι → ℝ) :
    (∑ m : ι → Bool, occupationWeight p m * ∑ i, if m i then f i else 0) =
      ∑ i, p i*f i := by
  have he (m : ι → Bool) (i : ι) : (if m i then f i else 0) =
      (if m i then 1 else 0) * f i := by cases m i <;> simp
  simp_rw [he,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc,← Finset.sum_mul,occupation_first]

lemma occupation_pair_sum (p : ι → ℝ) (f : ι → ι → ℝ) (hf : ∀ i, f i i = 0) :
    (∑ m : ι → Bool, occupationWeight p m *
      ∑ i, ∑ j, if m i && m j then f i j else 0) =
      ∑ i, ∑ j, p i*p j*f i j := by
  have he (m : ι → Bool) (i j : ι) : (if m i && m j then f i j else 0) =
      ((if m i then 1 else 0)*(if m j then 1 else 0)) * f i j := by
    cases m i <;> cases m j <;> simp
  simp_rw [he,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i=j
  · subst j; simp [hf]
  · calc
      _ = (∑ m : ι → Bool, occupationWeight p m *
          ((if m i then 1 else 0)*(if m j then 1 else 0))) * f i j := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m _
        ring
      _ = _ := by rw [occupation_second hij]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

abbrev Occupied {n : ℕ} (m : Fin n → Bool) := {i : Fin n // m i = true}

def occupationIndex {n : ℕ} (m : Fin n → Bool) : Fin (Fintype.card (Occupied m)) ↪ Fin n :=
  (Fintype.equivFin (Occupied m)).symm.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩

def occupationOrbitals {n : ℕ} {α : Type*} (φ : Fin n → α → ℂ) (m : Fin n → Bool) :
    Fin (Fintype.card (Occupied m)) → α → ℂ := fun j => φ (occupationIndex m j)

lemma occupationIndex_sum {n : ℕ} {R : Type*} [AddCommMonoid R]
    (m : Fin n → Bool) (f : Fin n → R) :
    (∑ j : Fin (Fintype.card (Occupied m)), f (occupationIndex m j)) =
      ∑ i : Fin n, if m i then f i else 0 := by
  calc
    _ = ∑ i : Occupied m, f i.1 :=
      Equiv.sum_comp (Fintype.equivFin (Occupied m)).symm (fun i : Occupied m => f i.1)
    _ = _ := by
      simpa only [Finset.subtype_univ,Finset.sum_filter] using (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
        (p := fun i : Fin n => m i = true) f)

lemma occupationIndex_pair_sum {n : ℕ} {R : Type*} [AddCommMonoid R]
    (m : Fin n → Bool) (f : Fin n → Fin n → R) :
    (∑ j : Fin (Fintype.card (Occupied m)), ∑ k : Fin (Fintype.card (Occupied m)),
      f (occupationIndex m j) (occupationIndex m k)) =
      ∑ i : Fin n, ∑ l : Fin n, if m i && m l then f i l else 0 := by
  calc
    _ = ∑ j : Fin (Fintype.card (Occupied m)), ∑ l : Fin n,
        if m l then f (occupationIndex m j) l else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact occupationIndex_sum m (f (occupationIndex m j))
    _ = ∑ i : Fin n, if m i then (∑ l : Fin n, if m l then f i l else 0) else 0 :=
      occupationIndex_sum m (fun i => ∑ l : Fin n, if m l then f i l else 0)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      cases m i <;> simp

lemma occupationOrbitals_orthonormal {n : ℕ} {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {φ : Fin n → α → ℂ}
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂μ) = if i=k then 1 else 0)
    (m : Fin n → Bool) :
    ∀ j k, (∫ z, conj (occupationOrbitals φ m j z)*occupationOrbitals φ m k z ∂μ) =
      if j=k then 1 else 0 := by
  intro j k
  rw [occupationOrbitals,occupationOrbitals,ho]
  simp only [EmbeddingLike.apply_eq_iff_eq]

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_WeightedPairDensity
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open scoped BigOperators ComplexConjugate

namespace CoulombAtom

def weightedSlaterDensity {n : ℕ} {α : Type*} (p : Fin n → ℝ)
    (φ : Fin n → α → ℂ) (u : α) : ℝ := ∑ i, p i * ‖φ i u‖^2

def weightedSlaterExchange {n : ℕ} {α : Type*} (p : Fin n → ℝ)
    (φ : Fin n → α → ℂ) (u v : α) : ℝ :=
  ‖∑ i : Fin n, (p i : ℂ) * (φ i u * conj (φ i v))‖^2

lemma slaterPairContraction_weighted_sum {n : ℕ} {α : Type*}
    (p : Fin n → ℝ) (φ : Fin n → α → ℂ) (u v : α) :
    (∑ i : Fin n, ∑ l : Fin n, (p i : ℂ)*(p l : ℂ)*slaterPairContraction φ i l u v) =
      (Complex.ofReal (weightedSlaterDensity p φ u * weightedSlaterDensity p φ v -
        weightedSlaterExchange p φ u v)) := by
  have hnorm (z : ℂ) : Complex.ofReal (‖z‖^2) = conj z*z := by
    simpa only [Complex.sq_norm] using Complex.normSq_eq_conj_mul_self (z := z)
  simp only [weightedSlaterDensity,weightedSlaterExchange,Complex.ofReal_sub,
    Complex.ofReal_mul,Complex.ofReal_sum,hnorm]
  simp only [slaterPairContraction,mul_sub,Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    simp only [map_mul]
    ring
  · simp only [map_sum,map_mul,starRingEnd_self_apply,Complex.conj_ofReal]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ComplexOccupation
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open scoped BigOperators

namespace CoulombAtom
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma occupation_pair_sum_complex (p : ι → ℝ) (f : ι → ι → ℂ) (hf : ∀ i, f i i = 0) :
    (∑ m : ι → Bool, (occupationWeight p m : ℂ) *
      ∑ i, ∑ j, if m i && m j then f i j else 0) =
      ∑ i, ∑ j, (p i : ℂ)*(p j : ℂ)*f i j := by
  have hre (b : Bool) (z : ℂ) : (if b then z else 0).re = if b then z.re else 0 := by
    cases b <;> rfl
  have him (b : Bool) (z : ℂ) : (if b then z else 0).im = if b then z.im else 0 := by
    cases b <;> rfl
  apply Complex.ext
  · simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_mul,sub_zero,hre,Complex.mul_im,add_zero] using
      occupation_pair_sum p (fun i j => (f i j).re) (fun i => by rw [hf i]; rfl)
  · simpa only [Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_mul,zero_add,add_zero,him,Complex.mul_re,sub_zero] using
      occupation_pair_sum p (fun i j => (f i j).im) (fun i => by rw [hf i]; rfl)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_OccupationPairDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_OccupationPairDensity_scope

open scoped BigOperators ComplexConjugate

def slaterPairDensity {n : ℕ} {α : Type*} (φ : Fin n → α → ℂ) (u v : α) : ℝ :=
  (∑ i, ‖φ i u‖^2)*(∑ i, ‖φ i v‖^2) - ‖∑ i, φ i u*conj (φ i v)‖^2

lemma occupationPairDensity {n : ℕ} {α : Type*} (p : Fin n → ℝ)
    (φ : Fin n → α → ℂ) (u v : α) :
    (∑ m : Fin n → Bool, occupationWeight p m *
      slaterPairDensity (occupationOrbitals φ m) u v) =
      weightedSlaterDensity p φ u * weightedSlaterDensity p φ v -
        weightedSlaterExchange p φ u v := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum,Complex.ofReal_mul]
  have he (m : Fin n → Bool) :
      (slaterPairDensity (occupationOrbitals φ m) u v : ℂ) =
        ∑ i : Fin n, ∑ j : Fin n, if m i && m j then slaterPairContraction φ i j u v else 0 := by
    rw [slaterPairDensity,← slaterPairContraction_sum]
    exact occupationIndex_pair_sum m (fun i j => slaterPairContraction φ i j u v)
  simp_rw [he]
  rw [occupation_pair_sum_complex p _ (fun i => slaterPairContraction_self φ i u v)]
  exact slaterPairContraction_weighted_sum p φ u v

end Work_OccupationPairDensity_scope

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_StripAveraging
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace CoulombRadialAveraging

def slidingBit (l r d t : ℝ) : ℝ := if d-r ≤ t ∧ t ≤ d+l then 1 else 0

def slidingCount {N : ℕ} (d : Fin N → ℝ) (l r t : ℝ) : ℝ :=
  ∑ i, slidingBit l r (d i) t

def upperCount {N : ℕ} (d : Fin N → ℝ) (R : ℝ) : ℝ :=
  ∑ i, if d i ≤ R then 1 else 0

lemma slidingBit_nonneg (l r d t : ℝ) : 0 ≤ slidingBit l r d t := by
  unfold slidingBit; split_ifs <;> norm_num

lemma slidingBit_le_one (l r d t : ℝ) : slidingBit l r d t ≤ 1 := by
  unfold slidingBit; split_ifs <;> norm_num

lemma slidingBit_measurable {α : Type*} [MeasurableSpace α]
    {d t : α → ℝ} (hd : Measurable d) (ht : Measurable t) (l r : ℝ) :
    Measurable (fun x => slidingBit l r (d x) (t x)) := by
  exact Measurable.ite ((measurableSet_le (hd.sub_const r) ht).inter
    (measurableSet_le ht (hd.add_const l))) measurable_const measurable_const

lemma slidingCount_nonneg {N : ℕ} (d : Fin N → ℝ) (l r t : ℝ) :
    0 ≤ slidingCount d l r t := Finset.sum_nonneg (fun _ _ => slidingBit_nonneg _ _ _ _)

lemma slidingCount_le {N : ℕ} (d : Fin N → ℝ) (l r t : ℝ) :
    slidingCount d l r t ≤ N := by
  calc
    _ ≤ ∑ _ : Fin N, (1:ℝ) := Finset.sum_le_sum (fun _ _ => slidingBit_le_one _ _ _ _)
    _ = N := by simp

lemma upperCount_nonneg {N : ℕ} (d : Fin N → ℝ) (R : ℝ) :
    0 ≤ upperCount d R := by
  apply Finset.sum_nonneg; intro i _; split_ifs <;> norm_num

lemma upperCount_le {N : ℕ} (d : Fin N → ℝ) (R : ℝ) : upperCount d R ≤ N := by
  calc
    _ ≤ ∑ _ : Fin N, (1:ℝ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)
    _ = N := by simp

lemma slidingCount_measurable {α : Type*} [MeasurableSpace α] {N : ℕ}
    {d : α → Fin N → ℝ} {t : α → ℝ}
    (hd : ∀ i, Measurable (fun x => d x i)) (ht : Measurable t) (l r : ℝ) :
    Measurable (fun x => slidingCount (d x) l r (t x)) :=
  Finset.measurable_sum _ (fun i _ => slidingBit_measurable (hd i) ht l r)

lemma upperCount_measurable {α : Type*} [MeasurableSpace α] {N : ℕ}
    {d : α → Fin N → ℝ} (hd : ∀ i, Measurable (fun x => d x i)) (R : ℝ) :
    Measurable (fun x => upperCount (d x) R) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_le (hd i) measurable_const) measurable_const measurable_const

lemma slidingCount_sq_integrable {α : Type*} [MeasurableSpace α] {N : ℕ}
    {d : α → Fin N → ℝ} {t : α → ℝ} {μ : Measure α} [IsFiniteMeasure μ]
    (hd : ∀ i, Measurable (fun x => d x i)) (ht : Measurable t) (l r : ℝ) :
    Integrable (fun x => slidingCount (d x) l r (t x)^2) μ := by
  apply Integrable.of_bound ((slidingCount_measurable hd ht l r).pow_const 2).aestronglyMeasurable
    ((N:ℝ)^2)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (slidingCount_nonneg _ _ _ _) (slidingCount_le _ _ _ _) 2)

lemma upperCount_sq_integrable {α : Type*} [MeasurableSpace α] {N : ℕ}
    {d : α → Fin N → ℝ} {μ : Measure α} [IsFiniteMeasure μ]
    (hd : ∀ i, Measurable (fun x => d x i)) (R : ℝ) :
    Integrable (fun x => upperCount (d x) R^2) μ := by
  apply Integrable.of_bound ((upperCount_measurable hd R).pow_const 2).aestronglyMeasurable
    ((N:ℝ)^2)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (upperCount_nonneg _ _) (upperCount_le _ _) 2)

lemma slidingBit_eq_indicator (l r d : ℝ) :
    slidingBit l r d = (Icc (d-r) (d+l)).indicator (fun _ => (1:ℝ)) := by
  funext t
  simp only [slidingBit,Set.indicator,mem_Icc]

lemma slidingBit_integrable (l r d : ℝ) : Integrable (slidingBit l r d) := by
  rw [slidingBit_eq_indicator]
  rw [integrable_indicator_iff measurableSet_Icc]
  exact integrable_const 1

lemma slidingBit_integral {l r : ℝ} (h : 0 ≤ l+r) (d : ℝ) :
    ∫ t, slidingBit l r d t = l+r := by
  rw [slidingBit_eq_indicator]
  rw [integral_indicator_const 1 measurableSet_Icc]
  simp only [Measure.real,Real.volume_Icc,smul_eq_mul,mul_one]
  rw [show d+l-(d-r)=l+r by ring,ENNReal.toReal_ofReal h]

lemma slidingBit_setIntegral_le {l r : ℝ} (h : 0 ≤ l+r) (d lo hi : ℝ) :
    ∫ t in Icc lo hi, slidingBit l r d t ≤ l+r := by
  rw [←slidingBit_integral h d]
  exact integral_mono_measure Measure.restrict_le_self
    (ae_of_all _ (slidingBit_nonneg l r d)) (slidingBit_integrable l r d)

lemma upperCount_eq_card {N : ℕ} (d : Fin N → ℝ) (R : ℝ) :
    upperCount d R = ((Finset.univ.filter (fun i => d i ≤ R)).card:ℝ) := by
  classical
  simp [upperCount,Finset.sum_boole]

end CoulombRadialAveraging

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_BlockEnergetics
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

lemma finite_pair_core_out_cross {N M : ℕ} (f : Fin (N+M) → Fin (N+M) → ℝ) :
    (∑ i : Fin (N+M), ∑ j : Fin (N+M), if i < j then f i j else 0) =
      (∑ i : Fin N, ∑ j : Fin N, if i < j then f (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) else 0)+
      (∑ i : Fin M, ∑ j : Fin M, if i < j then f (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) else 0)+
      ∑ i : Fin N, ∑ j : Fin M, f (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) := by
  have hl (i j : Fin N) : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) < finSumFinEquiv (Sum.inl j) ↔ i < j := Iff.rfl
  have hr (i j : Fin M) : (finSumFinEquiv (Sum.inr i) : Fin (N+M)) < finSumFinEquiv (Sum.inr j) ↔ i < j := by
    change N+i.val < N+j.val ↔ i.val < j.val
    omega
  have hlr (i : Fin N) (j : Fin M) : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) < finSumFinEquiv (Sum.inr j) := by
    change i.val < N+j.val
    omega
  have hrl (i : Fin M) (j : Fin N) : ¬ (finSumFinEquiv (Sum.inr i) : Fin (N+M)) < finSumFinEquiv (Sum.inl j) := by
    change ¬ N+i.val < j.val
    omega
  rw [←Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]
  have he (i : Fin (N+M)) : (∑ j : Fin (N+M), if i < j then f i j else 0) =
      (∑ j : Fin N, if i < finSumFinEquiv (Sum.inl j) then f i (finSumFinEquiv (Sum.inl j)) else 0)+
      ∑ j : Fin M, if i < finSumFinEquiv (Sum.inr j) then f i (finSumFinEquiv (Sum.inr j)) else 0 := by
    rw [←Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]
  simp_rw [he]
  simp only [hl,hr,hlr,hrl,ite_true,ite_false,Finset.sum_const_zero,zero_add,Finset.sum_add_distrib]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketCloud
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators


lemma packetGrid_card (n : ℕ) : Fintype.card (Fin 3 → Fin n) = n^3 := by simp


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_GridPacketRadius
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
namespace CoulombAtom

def gridPacketRadius (B : ℝ) (n : ℕ) : ℝ := B/(20*(n:ℝ))

lemma gridPacketRadius_pos {B : ℝ} (hB : 0 < B) {n : ℕ} (hn : 0 < n) :
    0 < gridPacketRadius B n := div_pos hB (by positivity)

lemma gridPacketRadius_mul {B : ℝ} {n : ℕ} (hn : 0 < n) :
    gridPacketRadius B n * n = B/20 := by
  have hn' : (n:ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  unfold gridPacketRadius
  field_simp

lemma gridPacketRadius_le {B : ℝ} (hB : 0 < B) {n : ℕ} (hn : 0 < n) :
    gridPacketRadius B n ≤ B/20 := by
  have hn' : (1:ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hr := gridPacketRadius_pos hB hn
  have he := gridPacketRadius_mul (B := B) hn
  nlinarith

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PacketFieldConstant
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
namespace CoulombAtom

lemma exists_nat_cube_between {M : ℝ} (hM : 1 ≤ M) :
    ∃ n : ℕ, 0 < n ∧ M ≤ (n:ℝ)^3 ∧ (n:ℝ)^3 ≤ 8*M := by
  have hex : ∃ n : ℕ, M ≤ (n:ℝ)^3 := by
    obtain ⟨n,hn⟩ := exists_nat_gt M
    have hn1 : (1:ℝ) ≤ n := le_trans hM hn.le
    have hn0 : (0:ℝ) ≤ n := by positivity
    have hpow : (n:ℝ) ≤ (n:ℝ)^3 := by
      nlinarith [mul_nonneg (sq_nonneg (n:ℝ)) (sub_nonneg.mpr hn1)]
    exact ⟨n,le_trans hn.le hpow⟩
  let n := Nat.find hex
  have hl : M ≤ (n:ℝ)^3 := Nat.find_spec hex
  have hn : 0 < n := by
    by_contra hh
    have he : n = 0 := by omega
    rw [he] at hl
    norm_num at hl
    linarith
  refine ⟨n,hn,hl,?_⟩
  by_cases he : n = 1
  · rw [he]; norm_num; linarith
  have hn2 : 2 ≤ n := by omega
  have hp : ((n-1:ℕ):ℝ)^3 < M := lt_of_not_ge (Nat.find_min hex (by dsimp [n]; omega))
  have hb : (n:ℝ) ≤ 2*((n-1:ℕ):ℝ) := by exact_mod_cast (show n ≤ 2*(n-1) by omega)
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ n) hb 3
  nlinarith

lemma packet_kinetic_absorb {B x : ℝ} (hB : 0 < B) (hx : 0 ≤ x) :
    x^2/B^2 ≤ 1/B^4+x^3/B := by
  have hu : 0 ≤ x*B := mul_nonneg hx hB.le
  have hcube : (x*B)^2 ≤ 1+(x*B)^3 := by
    by_cases hh : x*B ≤ 1
    · have hc : 0 ≤ (x*B)^3 := pow_nonneg hu _
      nlinarith [mul_nonneg hu (sub_nonneg.mpr hh)]
    · have hh : 1 ≤ x*B := (not_le.mp hh).le
      nlinarith [mul_nonneg (sq_nonneg (x*B)) (sub_nonneg.mpr hh)]
  apply (div_le_iff₀ (pow_pos hB 2)).mpr
  have he : (1/B^4+x^3/B)*B^2 = (1+(x*B)^3)/B^2 := by field_simp
  rw [he]
  apply (le_div_iff₀ (pow_pos hB 2)).mpr
  nlinarith

lemma field_cap_of_grid_bounds {B δ A C F : ℝ} (hB : 0 < B) (hδ : 0 ≤ δ)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, 0 < n → (n:ℝ)^3*F ≤ δ+A*(n:ℝ)^5/B^2+C*(n:ℝ)^6/B) :
    F ≤ (1+9*A+8*C)*(1/B^4+1/B+Real.sqrt (δ/B)) := by
  let s := Real.sqrt (δ/B)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : δ = B*s^2 := by
    have hh := Real.sq_sqrt (div_nonneg hδ hB.le)
    dsimp only [s]
    exact (eq_div_iff hB.ne').mp hh |>.symm.trans (mul_comm _ _)
  obtain ⟨n,hn,hlo,hhi⟩ := exists_nat_cube_between (le_max_left 1 (B*s))
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have ht : 0 < (n:ℝ)^3 := pow_pos hn' _
  have hlo' : B*s ≤ (n:ℝ)^3 := le_trans (le_max_right _ _) hlo
  have hhi' : (n:ℝ)^3 ≤ 8*(1+B*s) := by
    have hb : max 1 (B*s) ≤ 1+B*s := max_le (by linarith [mul_nonneg hB.le hs]) (by linarith)
    linarith
  have hdiv : δ/(n:ℝ)^3 ≤ s := by
    apply (div_le_iff₀ ht).mpr
    rw [hs2]
    nlinarith [mul_le_mul_of_nonneg_right hlo' hs]
  have hkin := packet_kinetic_absorb hB hn'.le
  have hrep : (n:ℝ)^3/B ≤ 8/B+8*s := by
    apply (div_le_iff₀ hB).mpr
    have he : (8/B+8*s)*B = 8*(1+B*s) := by field_simp
    rw [he]
    exact hhi'
  have hbasic : F ≤ δ/(n:ℝ)^3+A*((n:ℝ)^2/B^2)+C*((n:ℝ)^3/B) := by
    calc
      F = ((n:ℝ)^3*F)/(n:ℝ)^3 := by field_simp
      _ ≤ (δ+A*(n:ℝ)^5/B^2+C*(n:ℝ)^6/B)/(n:ℝ)^3 :=
        div_le_div_of_nonneg_right (h n hn) ht.le
      _ = _ := by field_simp
  have hstep : F ≤ A*(1/B^4)+(1+8*(A+C))*s+8*(A+C)*(1/B) := by
    have hk := mul_le_mul_of_nonneg_left hkin hA
    have hr := mul_le_mul_of_nonneg_left hrep (add_nonneg hA hC)
    simp only [div_eq_mul_inv] at hbasic hk hr hdiv ⊢
    nlinarith only [hbasic,hk,hr,hdiv]
  have hb4 : 0 ≤ 1/B^4 := by positivity
  have hb1 : 0 ≤ 1/B := by positivity
  have h1 : A ≤ 1+9*A+8*C := by linarith
  have h2 : 1+8*(A+C) ≤ 1+9*A+8*C := by linarith
  have h3 : 8*(A+C) ≤ 1+9*A+8*C := by linarith
  nlinarith [mul_le_mul_of_nonneg_right h1 hb4,mul_le_mul_of_nonneg_right h2 hs,
    mul_le_mul_of_nonneg_right h3 hb1]

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoherentHilbert
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

lemma inner_integral_rankOne {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]
    (μ : Measure α) (v : α → H)
    (hi : Integrable (fun q => InnerProductSpace.rankOne ℂ (v q) (v q)) μ) (u : H) :
    inner ℂ u ((∫ q, InnerProductSpace.rankOne ℂ (v q) (v q) ∂μ) u) =
      (∫ q, ‖inner ℂ (v q) u‖^2 ∂μ : ℝ) := by
  rw [ContinuousLinearMap.integral_apply hi]
  have ha : Integrable (fun q => InnerProductSpace.rankOne ℂ (v q) (v q) u) μ :=
    (ContinuousLinearMap.apply ℂ H u).integrable_comp hi
  rw [← integral_inner (𝕜 := ℂ) ha u]
  have he (q : α) : inner ℂ u (InnerProductSpace.rankOne ℂ (v q) (v q) u) =
      (‖inner ℂ (v q) u‖^2 : ℝ) := by
    rw [InnerProductSpace.rankOne_apply,inner_smul_right,
      ← inner_conj_symm u (v q),RCLike.mul_conj,Complex.ofReal_pow]
    rfl
  simp_rw [he]
  exact integral_ofReal

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoherentSchwartz
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CoherentSchwartz_scope

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff FourierTransform

lemma coherentWindow_compact {g u : Space → ℂ} (hcg : HasCompactSupport g) (z : Space) :
    HasCompactSupport (fun x : Space => conj (g (x-z))*u x) := by
  have hct : HasCompactSupport (fun x : Space => g (x-z)) :=
    hcg.comp_homeomorph (Homeomorph.subRight z)
  have hcj : HasCompactSupport (fun x : Space => conj (g (x-z))) :=
    hct.comp_left (map_zero (starRingEnd ℂ))
  exact hcj.mul_right

lemma coherent_position_integrable_schwartz {g : Space → ℂ}
    (hg : Continuous g) (hcg : HasCompactSupport g) (u : SchwartzMap Space ℂ) :
    Integrable (fun q : Space × Space => ‖g (q.2-q.1)‖^2 * ‖u q.2‖^2) := by
  have hgs : Integrable (fun z : Space => ‖g z‖^2) :=
    (hg.memLp_of_hasCompactSupport hcg (p := 2)).norm.integrable_sq
  have hus : Integrable (fun z : Space => ‖u z‖^2) := (u.memLp 2 volume).norm.integrable_sq
  have hu := u.continuous
  apply (integrable_prod_iff' (by fun_prop)).mpr
  constructor
  · filter_upwards [] with x
    exact (hgs.comp_sub_left x).mul_const _
  · have he (x : Space) :
        (∫ z : Space, ‖‖g (x-z)‖^2 * ‖u x‖^2‖) = (∫ z : Space, ‖g z‖^2) * ‖u x‖^2 := by
      simp_rw [norm_mul,norm_pow,Real.norm_of_nonneg (norm_nonneg _)]
      rw [integral_mul_const,integral_sub_left_eq_self (fun t : Space => ‖g t‖^2) volume x]
    change Integrable (fun x : Space => ∫ z : Space, ‖‖g (x-z)‖^2 * ‖u x‖^2‖)
    simp_rw [he]
    exact hus.const_mul _

end Work_CoherentSchwartz_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CompactEigenbasis
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

section Work_HilbertCountable_scope

open scoped Topology

universe u v
lemma orthonormal_countable {H : Type u} {ι : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H]
    {v : ι → H} (hv : Orthonormal ℂ v) : Countable ι := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (v i) (1/2 : ℝ)) (Metric.ball (v j) (1/2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hs : ‖v i-v j‖^2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ),hv.norm_eq_one,hv.norm_eq_one,hv.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i-v j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun _ => Metric.nonempty_ball.mpr (by norm_num))

end Work_HilbertCountable_scope

section Work_HilbertTrace_scope

open MeasureTheory Filter
open scoped BigOperators Topology

universe u v w
variable {H : Type u} {ι : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma hilbertBasis_hasSum_norm_inner (b : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i => ‖inner ℂ (b i) x‖^2) (‖x‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,b.repr_apply_apply,
    LinearIsometryEquiv.norm_map] using lp.hasSum_norm (by norm_num : 0 < (2:ENNReal).toReal) (b.repr x)

lemma hilbertBasis_frame_trace {α : Type w} [MeasurableSpace α]
    (μ : Measure α) (b : HilbertBasis ι ℂ H) [Countable ι] (v : α → H)
    (hv : AEStronglyMeasurable v μ) (hn : Integrable (fun x => ‖v x‖^2) μ) :
    HasSum (fun i => ∫ x, ‖inner ℂ (b i) (v x)‖^2 ∂μ) (∫ x, ‖v x‖^2 ∂μ) := by
  have hmeas (i : ι) : AEStronglyMeasurable (fun x => ‖inner ℂ (b i) (v x)‖^2) μ :=
    (((continuous_const.inner continuous_id).norm.pow 2).comp_aestronglyMeasurable hv)
  apply hasSum_integral_of_dominated_convergence
    (fun i x => ‖inner ℂ (b i) (v x)‖^2) hmeas
  · intro i
    exact Eventually.of_forall (fun x => (Real.norm_of_nonneg (sq_nonneg _)).le)
  · exact Eventually.of_forall (fun x => b.orthonormal.inner_products_summable (v x))
  · convert hn using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    exact (hilbertBasis_hasSum_norm_inner b (v x)).tsum_eq
  · exact Eventually.of_forall (fun x => hilbertBasis_hasSum_norm_inner b (v x))

end Work_HilbertTrace_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SmoothCompactIntegral
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SmoothCompactIntegral_scope

open MeasureTheory Filter Metric
open scoped ContDiff Topology

universe u v
variable {X : Type u} {A : Type v} {E : Type u}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [SMulCommClass ℝ ℂ E]

def firstPartial (F : X × A → E) (p : X × A) : X →L[ℝ] E :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ X A)

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ A] [MeasurableSpace A]
  [BorelSpace A] [NormedSpace ℂ E] [SMulCommClass ℝ ℂ E] in
lemma firstPartial_hasFDerivAt {F : X × A → E} (hF : Differentiable ℝ F) (x : X) (a : A) :
    HasFDerivAt (fun y => F (y,a)) (firstPartial F (x,a)) x := by
  simpa only [firstPartial, Function.comp_def] using (hF (x,a)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const a x))

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ A] [MeasurableSpace A]
  [BorelSpace A] [NormedSpace ℂ E] [SMulCommClass ℝ ℂ E] in
lemma firstPartial_contDiff {F : X × A → E} {n : ℕ∞ω} (hF : ContDiff ℝ (n+1) F) :
    ContDiff ℝ n (firstPartial F) := by
  exact (contDiff_succ_iff_fderiv.mp hF).2.2.clm_comp contDiff_const

lemma weightedSetIntegral_hasFDerivAt (μ : Measure A) [IsFiniteMeasure μ]
    (K : Set A) (hK : IsCompact K) {F : X × A → E} (hF : ContDiff ℝ 1 F)
    {w : A → ℂ} (hw : Continuous w) (x : X) :
    HasFDerivAt (fun y => ∫ a in K, w a • F (y,a) ∂μ)
      (∫ a in K, w a • firstPartial F (x,a) ∂μ) x := by
  have hD : Continuous (firstPartial F) := by
    exact (firstPartial_contDiff (n := 0) (by simpa using hF)).continuous
  have hcont : Continuous (fun p : X × A => w p.2 • firstPartial F p) :=
    (hw.comp continuous_snd).smul hD
  obtain ⟨M,hM⟩ := ((isCompact_closedBall x 1).prod hK).exists_bound_of_continuousOn
    hcont.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := closedBall x 1) (bound := fun _ => M) (closedBall_mem_nhds x (by norm_num))
  · exact Eventually.of_forall (fun y => ((hw.smul
      (hF.continuous.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable))
  · exact ((hw.smul (hF.continuous.comp (continuous_const.prodMk continuous_id))).continuousOn).integrableOn_compact hK
  · exact (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro y hy
    exact hM (y,a) ⟨hy,ha⟩
  · exact integrable_const _
  · exact Eventually.of_forall (fun a y _ =>
      (firstPartial_hasFDerivAt (hF.differentiable (by norm_num)) y a).const_smul (w a))

lemma weightedSetIntegral_contDiff_nat (μ : Measure A) [IsFiniteMeasure μ]
    (K : Set A) (hK : IsCompact K) (n : ℕ) {F : X × A → E}
    (hF : ContDiff ℝ (n : ℕ∞ω) F) {w : A → ℂ} (hw : Continuous w) :
    ContDiff ℝ (n : ℕ∞ω) (fun y => ∫ a in K, w a • F (y,a) ∂μ) := by
  induction n generalizing E with
  | zero =>
    apply contDiff_zero.mpr
    exact continuous_parametric_integral_of_continuous
      ((hw.comp continuous_snd).smul hF.continuous) hK
  | succ n ih =>
    have h1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hd (x : X) := weightedSetIntegral_hasFDerivAt μ K hK h1 hw x
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hd x).differentiableAt, ?_, ?_⟩
    · intro h
      simp at h
    · have he : (fderiv ℝ (fun y => ∫ a in K, w a • F (y,a) ∂μ)) =
          (fun y => ∫ a in K, w a • firstPartial F (y,a) ∂μ) :=
        funext (fun x => (hd x).fderiv)
      rw [he]
      exact ih (firstPartial_contDiff (by simpa only [Nat.cast_add, Nat.cast_one] using hF))

lemma weightedSetIntegral_contDiff (μ : Measure A) [IsFiniteMeasure μ]
    (K : Set A) (hK : IsCompact K) {F : X × A → E}
    (hF : ContDiff ℝ ∞ F) {w : A → ℂ} (hw : Continuous w) :
    ContDiff ℝ ∞ (fun y => ∫ a in K, w a • F (y,a) ∂μ) := by
  apply contDiff_infty.mpr
  intro n
  exact weightedSetIntegral_contDiff_nat μ K hK n (contDiff_infty.mp hF n) hw

end Work_SmoothCompactIntegral_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

def coherentSpatialSupport (g : Space → ℂ) (K : Set (Space × Space)) : Set Space :=
  (fun r : (Space × Space) × Space => r.2 + r.1.1) '' (K ×ˢ tsupport g)

lemma coherentSpatialSupport_compact {g : Space → ℂ} (hcg : HasCompactSupport g)
    {K : Set (Space × Space)} (hK : IsCompact K) : IsCompact (coherentSpatialSupport g K) :=
  (hK.prod hcg).image (by fun_prop)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_OccupationTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

lemma occupation_expect_sum {n : ℕ} {α : Type*} [Fintype α] (p : Fin n → ℝ)
    (f : (Fin n → Bool) → α → ℝ) :
    (∑ m : Fin n → Bool, occupationWeight p m * ∑ a, f m a) =
      ∑ a, ∑ m : Fin n → Bool, occupationWeight p m * f m a := by
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

lemma occupation_count {n : ℕ} (p : Fin n → ℝ) :
    (∑ m : Fin n → Bool, occupationWeight p m * (Fintype.card (Occupied m) : ℝ)) =
      ∑ i : Fin n, p i := by
  have he (m : Fin n → Bool) : (Fintype.card (Occupied m) : ℝ) =
      ∑ i : Fin n, if m i then (1:ℝ) else 0 := by
    rw [← occupationIndex_sum m (fun _ => (1:ℝ))]
    simp
  simp_rw [he,occupation_sum,mul_one]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FiniteFermionEnsemble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

lemma occupation_mean_lower {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (f : (Fin n → Bool) → ℝ) {c : ℝ}
    (h : ∀ m, c ≤ f m) : c ≤ ∑ m : Fin n → Bool, occupationWeight p m * f m := by
  calc
    c = ∑ m : Fin n → Bool, occupationWeight p m * c := by rw [← Finset.sum_mul,occupationWeight_sum,one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left (h m) (occupationWeight_nonneg hp m))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CorrelatedFiniteInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

universe u

def finiteOrbitalDensity {ι : Type u} [Fintype ι] (p : ι → ℝ)
    (φ : ι → SlaterParticle → ℂ) (z : SlaterParticle) : ℝ := ∑ i, p i * ‖φ i z‖^2

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CoreFieldRegularity
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

local instance instFactNeENNRealHDivOfNatTop_solutions : Fact ((5/2:ℝ≥0∞) ≠ ⊤) := ⟨by finiteness⟩

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CoherentBessel
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

namespace CoulombAtom

lemma lp_complex_norm_sq {A : Type*} [MeasurableSpace A] (μ : Measure A) (f : Lp ℂ 2 μ) :
    ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K,← RCLike.ofReal_pow]
  rw [integral_ofReal]
  rfl

lemma coherentParam_memLp {F : Space × Space → ℂ} (hF : Continuous F)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) : MemLp F 2 μ := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  apply MemLp.of_bound hF.aestronglyMeasurable C
  filter_upwards [hμ] with q hq
  exact hC q hq

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CoherentDensityTrace
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ContDiff Topology

lemma nonneg_series_eq_of_integral {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) {f : ι → α → ℝ} {d : α → ℝ}
    (hf : ∀ i, Integrable (f i) μ) (hn : ∀ i x, 0 ≤ f i x) (hd : Integrable d μ)
    (hle : ∀ s : Finset ι, ∀ x, (∑ i ∈ s, f i x) ≤ d x)
    (htrace : HasSum (fun i => ∫ x, f i x ∂μ) (∫ x, d x ∂μ)) :
    (fun x => ∑' i, f i x) =ᵐ[μ] d := by
  have hs (x) : Summable (fun i => f i x) := summable_of_sum_le (fun i => hn i x) (fun s => hle s x)
  have hb (x) : (∑' i, f i x) ≤ d x := (hs x).tsum_le_of_sum_le (fun s => hle s x)
  have hi : Integrable (fun x => ∑' i, f i x) μ :=
    hd.mono' (AEStronglyMeasurable.tsum (fun i => (hf i).aestronglyMeasurable))
      (Eventually.of_forall (fun x => by rw [Real.norm_of_nonneg (tsum_nonneg (fun i => hn i x))]; exact hb x))
  have hh := hasSum_integral_of_dominated_convergence (fun i x => f i x)
    (fun i => (hf i).aestronglyMeasurable)
    (fun i => Eventually.of_forall (fun x => (Real.norm_of_nonneg (hn i x)).le))
    (Eventually.of_forall hs) hi (Eventually.of_forall (fun x => (hs x).hasSum))
  exact (integral_eq_iff_of_ae_le hi hd (Eventually.of_forall hb)).1 (hh.unique htrace)

open MeasureTheory Filter
open scoped BigOperators ContDiff Topology

lemma nonneg_series_weight_hasSum {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) {f : ι → α → ℝ} {d W : α → ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hn : ∀ i x, 0 ≤ f i x)
    (hw : AEStronglyMeasurable W μ) (hwd : Integrable (fun x => |W x| *d x) μ)
    (htrace : ∀ᵐ x ∂μ, HasSum (fun i => f i x) (d x)) :
    HasSum (fun i => ∫ x, W x*f i x ∂μ) (∫ x, W x*d x ∂μ) := by
  apply hasSum_integral_of_dominated_convergence (fun i x => |W x| *f i x)
    (fun i => hw.mul (hf i))
  · intro i
    filter_upwards [] with x
    rw [Pi.mul_apply,Real.norm_eq_abs,abs_mul,abs_of_nonneg (hn i x)]
  · filter_upwards [htrace] with x hx
    exact (hx.mul_left |W x|).summable
  · apply hwd.congr
    filter_upwards [htrace] with x hx
    exact (hx.mul_left |W x|).tsum_eq.symm
  · filter_upwards [htrace] with x hx
    exact hx.mul_left (W x)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

lemma packetScale_factor {b : ℝ} (hb : 0 < b) :
    (b ^ (-(3/2 : ℝ)))^2*b^3 = 1 := by
  rw [← Real.rpow_mul_natCast hb.le,← Real.rpow_natCast b 3,← Real.rpow_add hb]
  norm_num

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PatchRandomVariables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace CoulombNeumann
open CoulombAtom
local instance instFactNeENNRealHDivOfNatTop_solutions : Fact ((5/3:ℝ≥0∞) ≠ ⊤) := ⟨by finiteness⟩

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ConditionalRetainedGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombNeumann

def finiteCorePatchBound (N : ℕ) (Z lam b : ℝ) : ℝ := |Z|/b+|lam|+N/b

lemma finiteCorePatchBound_nonneg (N : ℕ) (Z lam : ℝ) {b : ℝ} (hb : 0 < b) :
    0 ≤ finiteCorePatchBound N Z lam b := by unfold finiteCorePatchBound; positivity

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialPatchGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombNeumann

lemma sqrt_three_le_three : Real.sqrt 3 ≤ 3 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_nonneg (3:ℝ)]

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombNeumann

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_WeightedCauchy
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators

namespace CoulombAtom

lemma weighted_sum_integral_cauchy {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) (w f g : ∀ i, X i → ℝ)
    (hw : ∀ i x, 0 ≤ w i x)
    (hf : ∀ i, Integrable (fun x => f i x^2*w i x) (μ i))
    (hg : ∀ i, Integrable (fun x => g i x^2*w i x) (μ i))
    (hfg : ∀ i, Integrable (fun x => f i x*g i x*w i x) (μ i)) :
    (∑ i, ∫ x, f i x*g i x*w i x ∂μ i) ≤
      Real.sqrt (∑ i, ∫ x, f i x^2*w i x ∂μ i)*
        Real.sqrt (∑ i, ∫ x, g i x^2*w i x ∂μ i) := by
  let A := ∑ i, ∫ x, f i x^2*w i x ∂μ i
  let B := ∑ i, ∫ x, g i x^2*w i x ∂μ i
  let C := ∑ i, ∫ x, f i x*g i x*w i x ∂μ i
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw i x)))
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw i x)))
  have hq (r : ℝ) : 0 ≤ A*(r*r)+(-2*C)*r+B := by
    have he (i : ι) : (∫ x, (r*f i x-g i x)^2*w i x ∂μ i) =
        r^2*(∫ x, f i x^2*w i x ∂μ i)-
          (2*r)*(∫ x, f i x*g i x*w i x ∂μ i)+∫ x, g i x^2*w i x ∂μ i := by
      have hp (x : X i) : (r*f i x-g i x)^2*w i x =
          r^2*(f i x^2*w i x)-(2*r)*(f i x*g i x*w i x)+(g i x^2*w i x) := by ring
      simp_rw [hp]
      have hadd := integral_add (((hf i).const_mul (r^2)).sub ((hfg i).const_mul (2*r))) (hg i)
      have hsub := integral_sub ((hf i).const_mul (r^2)) ((hfg i).const_mul (2*r))
      simp only [Pi.sub_apply,integral_const_mul] at hadd hsub
      rw [hadd,hsub]
    have hn : 0 ≤ ∑ i, ∫ x, (r*f i x-g i x)^2*w i x ∂μ i :=
      Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw i x)))
    simp only [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at hn
    dsimp only [A,B,C]
    nlinarith
  have hd := discrim_le_zero hq
  have hsq : C^2 ≤ A*B := by
    unfold discrim at hd
    nlinarith
  change C ≤ Real.sqrt A*Real.sqrt B
  rw [←Real.sqrt_mul hA]
  nlinarith [Real.sq_sqrt (mul_nonneg hA hB),Real.sqrt_nonneg (A*B)]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialSelectedCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombAtom

lemma bounded_probability_first_le_second {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Measurable f)
    (hn : ∀ x, 0 ≤ f x) {C : ℝ} (hC : ∀ x, f x ≤ C) :
    (∫ x, f x ∂μ) ≤ (∫ x, f x^2 ∂μ)^(1/2:ℝ) := by
  have hm : MemLp f (ENNReal.ofReal 2) μ :=
    MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (hn x)]; exact hC x))
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩)
    (ae_of_all μ hn) (ae_of_all μ (fun _ => (by norm_num : (0:ℝ) ≤ 1))) hm
    (memLp_const (1:ℝ))
  simpa only [mul_one,Real.rpow_two,one_pow,integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,
    smul_eq_mul,Real.one_rpow] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RootMomentCauchyBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_RootMomentCauchy_barrier_scope

open MeasureTheory Filter
open scoped BigOperators

lemma integrable_sqrt_mul_sqrt {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    Integrable (fun x => Real.sqrt (f x)*Real.sqrt (g x)) μ := by
  apply (hf.add hg).mono'
    ((Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable))
  apply ae_of_all
  intro x
  change ‖Real.sqrt (f x)*Real.sqrt (g x)‖ ≤ f x+g x
  rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  nlinarith [sq_nonneg (Real.sqrt (f x)-Real.sqrt (g x)),
    Real.sq_sqrt (hfn x),Real.sq_sqrt (hgn x)]

lemma sum_integral_sqrt_mul_sqrt_le {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    (f g : ∀ i, X i → ℝ) (hf : ∀ i, Integrable (f i) (μ i))
    (hg : ∀ i, Integrable (g i) (μ i)) (hfn : ∀ i x, 0 ≤ f i x) (hgn : ∀ i x, 0 ≤ g i x) :
    (∑ i, ∫ x, Real.sqrt (f i x)*Real.sqrt (g i x) ∂μ i) ≤
      Real.sqrt (∑ i, ∫ x, f i x ∂μ i)*Real.sqrt (∑ i, ∫ x, g i x ∂μ i) := by
  have hh := weighted_sum_integral_cauchy μ (fun _ _ => 1)
    (fun i x => Real.sqrt (f i x)) (fun i x => Real.sqrt (g i x))
    (fun _ _ => zero_le_one)
    (fun i => by simpa only [mul_one,Real.sq_sqrt (hfn i _)] using hf i)
    (fun i => by simpa only [mul_one,Real.sq_sqrt (hgn i _)] using hg i)
    (fun i => by simpa only [mul_one] using integrable_sqrt_mul_sqrt (hf i) (hg i) (hfn i) (hgn i))
  simpa only [mul_one,Real.sq_sqrt (hfn _ _),Real.sq_sqrt (hgn _ _)] using hh

end Work_RootMomentCauchy_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LocalFieldBootstrapBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

def localFieldScale (a D B : ℝ) : ℝ :=
  (1/a^4+1/a)^2+1/a^4+D/a+B/a^2

lemma localFieldScale_nonneg {a D B : ℝ} (ha : 0 < a) (hD : 0 ≤ D) (hB : 0 ≤ B) :
    0 ≤ localFieldScale a D B := by unfold localFieldScale; positivity

lemma sqrt_count_reciprocal_young {a B : ℝ} (_ha : 0 < a) (hB : 0 ≤ B) :
    2*Real.sqrt B/a^3 ≤ 1/a^4+B/a^2 := by
  have he : (Real.sqrt B/a)^2 = B/a^2 := by rw [div_pow,Real.sq_sqrt hB]
  have hp : (1/a^2)^2 = (1:ℝ)/a^4 := by ring
  calc
    2*Real.sqrt B/a^3 = 2*(Real.sqrt B/a)*(1/a^2) := by ring
    _ ≤ (Real.sqrt B/a)^2+(1/a^2)^2 := by nlinarith [sq_nonneg (Real.sqrt B/a-1/a^2)]
    _ = _ := by rw [he,hp]; ring

lemma localFieldScale_mono {a D D' B B' : ℝ} (ha : 0 < a) (hD : D ≤ D') (hB : B ≤ B') :
    localFieldScale a D B ≤ localFieldScale a D' B' := by
  unfold localFieldScale
  exact add_le_add (add_le_add le_rfl (div_le_div_of_nonneg_right hD ha.le))
    (div_le_div_of_nonneg_right hB (sq_nonneg a))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CellScaleBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma cell_reciprocal_bounds {a m : ℝ} (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) :
    1/a ≤ m ∧ 1/a^2 ≤ m := by
  by_cases ha1 : 1 ≤ a
  · have h2 : 1 ≤ a^2 := by nlinarith
    exact ⟨(div_le_one ha).mpr ha1 |>.trans hm,
      (div_le_one (sq_pos_of_pos ha)).mpr h2 |>.trans hm⟩
  · have ha1 : a ≤ 1 := le_of_not_ge ha1
    have h2 : a^2 ≤ a := by nlinarith
    have h32 : a^3 ≤ a^2 := by nlinarith [mul_le_mul_of_nonneg_left h2 ha.le]
    exact ⟨(one_div_le_one_div_of_le (pow_pos ha 3) (le_trans h32 h2)).trans h3,
      (one_div_le_one_div_of_le (pow_pos ha 3) h32).trans h3⟩

lemma cell_mass_product {a m : ℝ} (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) :
    1 ≤ a*m := by
  have hh := (cell_reciprocal_bounds ha hm h3).1
  exact (div_le_iff₀ ha).mp hh |>.trans_eq (by ring)

lemma cell_four_thirds_bound {a m : ℝ} (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) :
    m^(4/3:ℝ) ≤ a*m^2 := by
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have ham : 1 ≤ a^3*m := by
    have := (div_le_iff₀ (pow_pos ha 3)).mp h3
    nlinarith
  have ham2 : 1 ≤ a^3*m^2 := by
    have := mul_le_mul_of_nonneg_left hm (mul_nonneg (pow_nonneg ha.le 3) hm0)
    nlinarith
  have hp : (m^(4/3:ℝ))^3 = m^4 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hm0]
    norm_num
  have hh := mul_le_mul_of_nonneg_right ham2 (show 0 ≤ m^4 by positivity)
  have hpow : (m^(4/3:ℝ))^3 ≤ (a*m^2)^3 := by rw [hp]; nlinarith
  exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg hm0 _) (by positivity : 0 ≤ a*m^2) (by decide : (3:ℕ) ≠ 0)).mp hpow

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CellFieldNormalizationBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma sqrt_count_scale {B C P m : ℝ} (_hB : 0 ≤ B) (hC : 1 ≤ C) (hP : 0 ≤ P)
    (hm : 0 ≤ m) (hh : B ≤ C*P*m^2) : Real.sqrt B ≤ C*Real.sqrt P*m := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hcc : C ≤ C^2 := by nlinarith
  have hs := Real.sq_sqrt hP
  have he : (C*Real.sqrt P*m)^2 = C^2*P*m^2 := by rw [mul_pow,mul_pow,hs]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,hh.trans ?_⟩
  rw [he]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcc hP) (sq_nonneg m)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_SqrtMultiplier
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SqrtMultiplier_scope

open Filter Set
open scoped Topology NNReal

lemma sqrt_lipschitz_of_fderiv_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : Differentiable ℝ f)
    (hn : ∀ x, 0 ≤ f x) (K : ℝ≥0)
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ 2*(K:ℝ)*Real.sqrt (f x)) :
    LipschitzWith K (fun x => Real.sqrt (f x)) := by
  have hreg (δ : ℝ) (hδ : 0 < δ) : LipschitzWith K (fun x => Real.sqrt (f x + δ)) := by
    have hg (x : E) := ((hf x).hasFDerivAt.add_const δ).sqrt (by linarith [hn x] : f x + δ ≠ 0)
    apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hg x).differentiableAt)
    intro x
    change ‖fderiv ℝ (fun x => Real.sqrt (f x+δ)) x‖ ≤ (K:ℝ)
    have hs : 0 < 2*Real.sqrt (f x+δ) := by apply mul_pos (by norm_num); exact Real.sqrt_pos.mpr (by linarith [hn x])
    rw [(hg x).fderiv, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hs), one_div, inv_mul_eq_div, div_le_iff₀ hs]
    calc
      _ ≤ 2*(K:ℝ)*Real.sqrt (f x) := hb x
      _ ≤ (K:ℝ)*(2*Real.sqrt (f x+δ)) := by
        have hh := Real.sqrt_le_sqrt (show f x ≤ f x+δ by linarith)
        nlinarith [K.coe_nonneg]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc : Continuous (fun δ : ℝ => dist (Real.sqrt (f x+δ)) (Real.sqrt (f y+δ))) := by fun_prop
  have ht : Tendsto (fun δ : ℝ => dist (Real.sqrt (f x+δ)) (Real.sqrt (f y+δ)))
      (𝓝[>] 0) (𝓝 (dist (Real.sqrt (f x)) (Real.sqrt (f y)))) := by
    simpa only [add_zero] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (hreg δ hδ).dist_le_mul x y

end Work_SqrtMultiplier_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservationIntegral
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ObservationIntegral_scope

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

def eventMomentOrder (p : ℝ) : ℕ := ⌈-Real.log p⌉₊+1

end Work_ObservationIntegral_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_DyadicObservation
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombObservation

def dyadicObservationWidth (r : ℝ) (k : ℕ) : ℝ := ((2:ℝ)^k * r)^(1.01:ℝ)

end CoulombObservation

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombObservation

def scaleObservationArray {J I : Type*} [Fintype J] [Fintype I]
    (ell : J → ℝ) : (J × I → ℝ) →L[ℝ] (J × I → ℝ) :=
  ContinuousLinearMap.pi (fun q => ell q.1 • ContinuousLinearMap.proj q)

@[simp] lemma scaleObservationArray_apply {J I : Type*} [Fintype J] [Fintype I]
    (ell : J → ℝ) (u : J × I → ℝ) (q : J × I) :
    scaleObservationArray ell u q = ell q.1 * u q := rfl

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterWidth
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Metric
open scoped NNReal

lemma powerProfile_interval {w s x y : ℝ} (hw : 0 ≤ w) (hx : 0 < x)
    (hxy : x ≤ y) (hys : y ≤ s) :
    ‖y^(1+w)-x^(1+w)‖ ≤ (1+w)*s^w*(y-x) := by
  have hp : 0 ≤ 1+w := by linarith
  have hd (z : ℝ) (hz : z ∈ Icc x y) :
      HasDerivWithinAt (fun u : ℝ => u^(1+w)) ((1+w)*z^w) (Icc x y) z := by
    have hh := (Real.hasDerivAt_rpow_const (x := z) (p := 1+w)
      (Or.inl (ne_of_gt (hx.trans_le hz.1)))).hasDerivWithinAt (s := Icc x y)
    simpa only [add_sub_cancel_left] using hh
  have hb (z : ℝ) (hz : z ∈ Icc x y) : ‖(1+w)*z^w‖ ≤ (1+w)*s^w := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp (Real.rpow_nonneg (hx.le.trans hz.1) _))]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hx.le.trans hz.1) (hz.2.trans hys) hw) hp
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc x y)
    (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hxy)] using H

def cappedWidthProfile (s w d : ℝ) : ℝ := d*(min d s)^w

lemma cappedWidthProfile_small {s w d : ℝ} (hd : 0 < d) (hw : 0 ≤ w) (hs : d ≤ s) :
    cappedWidthProfile s w d = d^(1+w) := by
  rw [cappedWidthProfile,min_eq_left hs,Real.rpow_one_add' hd.le (by linarith)]

lemma cappedWidthProfile_large {s w d : ℝ} (hs : s ≤ d) :
    cappedWidthProfile s w d = d*s^w := by rw [cappedWidthProfile,min_eq_right hs]

lemma cappedWidthProfile_ordered_bound {w s x y : ℝ} (hw : 0 ≤ w) (hs : 0 < s)
    (hx : 0 < x) (hxy : x ≤ y) :
    ‖cappedWidthProfile s w y-cappedWidthProfile s w x‖ ≤ (1+w)*s^w*(y-x) := by
  have hy : 0 < y := hx.trans_le hxy
  by_cases hys : y ≤ s
  · rw [cappedWidthProfile_small hy hw hys,cappedWidthProfile_small hx hw (hxy.trans hys)]
    exact powerProfile_interval hw hx hxy hys
  have hsy : s ≤ y := le_of_not_ge hys
  by_cases hsx : s ≤ x
  · rw [cappedWidthProfile_large hsy,cappedWidthProfile_large hsx,←sub_mul,
      norm_mul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hxy),
      Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hs.le _)]
    nlinarith [mul_nonneg hw (mul_nonneg (Real.rpow_nonneg hs.le w) (sub_nonneg.mpr hxy))]
  have hxs : x ≤ s := le_of_not_ge hsx
  have hsmall : ‖cappedWidthProfile s w s-cappedWidthProfile s w x‖ ≤
      (1+w)*s^w*(s-x) := by
    rw [cappedWidthProfile_small hs hw le_rfl,cappedWidthProfile_small hx hw hxs]
    exact powerProfile_interval hw hx hxs le_rfl
  have hlarge : ‖cappedWidthProfile s w y-cappedWidthProfile s w s‖ ≤
      (1+w)*s^w*(y-s) := by
    rw [cappedWidthProfile_large hsy,cappedWidthProfile_large le_rfl,←sub_mul,
      norm_mul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hsy),
      Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hs.le _)]
    nlinarith [mul_nonneg hw (mul_nonneg (Real.rpow_nonneg hs.le w) (sub_nonneg.mpr hsy))]
  calc
    _ = ‖(cappedWidthProfile s w y-cappedWidthProfile s w s)+
        (cappedWidthProfile s w s-cappedWidthProfile s w x)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ (1+w)*s^w*(y-s)+(1+w)*s^w*(s-x) := add_le_add hlarge hsmall
    _ = _ := by ring

lemma cappedWidthProfile_norm_bound {w s x y : ℝ} (hw : 0 ≤ w) (hs : 0 < s)
    (hx : 0 < x) (hy : 0 < y) :
    ‖cappedWidthProfile s w x-cappedWidthProfile s w y‖ ≤ (1+w)*s^w*‖x-y‖ := by
  rcases le_total y x with h|h
  · simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr h)] using
      cappedWidthProfile_ordered_bound hw hs hy h
  · simpa only [norm_sub_rev x y,norm_sub_rev (cappedWidthProfile s w x) _,
      Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr h)] using
      cappedWidthProfile_ordered_bound hw hs hx h

open Set Metric
open scoped NNReal

lemma invCube_norm_sub_le {q a b : ℝ} (hq : 0 < q) (ha : q ≤ a) (hb : q ≤ b) :
    ‖a⁻¹^3-b⁻¹^3‖ ≤ 3*q⁻¹^4*‖a-b‖ := by
  have hd (z : ℝ) (hz : z ∈ Ici q) :
      HasDerivWithinAt (fun u : ℝ => u⁻¹^3) (-3*z⁻¹^4) (Ici q) z := by
    have hh := ((hasDerivAt_inv (ne_of_gt (hq.trans_le hz))).pow 3).hasDerivWithinAt (s := Ici q)
    convert! hh using 1; simp only [Nat.cast_ofNat, Nat.reduceSub, ←inv_pow]
    ring
  have hbound (z : ℝ) (hz : z ∈ Ici q) : ‖-3*z⁻¹^4‖ ≤ 3*q⁻¹^4 := by
    rw [norm_mul,Real.norm_eq_abs,abs_of_neg (by norm_num : (-3:ℝ) < 0)]
    norm_num only [neg_neg,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hq.le.trans hz)) 4)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr (hq.le.trans hz))
      (inv_anti₀ hq hz) 4) (by norm_num)
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound (convex_Ici q) hb ha

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_CellDensityBoundBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma cell_count_rpow_scale {a m B C P : ℝ} (ha : 0 < a) (hm : 1 ≤ m)
    (h3 : 1/a^3 ≤ m) (hB : 0 ≤ B) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hBC : B ≤ C*P*m^2) :
    B^(2/3:ℝ) ≤ C^(2/3:ℝ)*P^(2/3:ℝ)*a*m^2 := by
  have hm0 := le_trans zero_le_one hm
  have hh := Real.rpow_le_rpow hB hBC (by norm_num : (0:ℝ) ≤ 2/3)
  have he : (C*P*m^2)^(2/3:ℝ) = C^(2/3:ℝ)*P^(2/3:ℝ)*m^(4/3:ℝ) := by
    rw [Real.mul_rpow (mul_nonneg hC hP) (sq_nonneg m),Real.mul_rpow hC hP,
      ←Real.rpow_natCast,←Real.rpow_mul hm0]
    norm_num
  rw [he] at hh
  calc _ ≤ C^(2/3:ℝ)*P^(2/3:ℝ)*m^(4/3:ℝ) := hh
       _ ≤ C^(2/3:ℝ)*P^(2/3:ℝ)*(a*m^2) :=
         mul_le_mul_of_nonneg_left (cell_four_thirds_bound ha hm h3) (by positivity)
       _ = _ := by ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CellCountAbsorptionBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped ContDiff

namespace CoulombAtom

lemma count_sublinear_absorption {P C : ℝ} (hP : 1 ≤ P) (hC : 0 ≤ C)
    (hh : P ≤ 1+P/4+C*(P^(2/3:ℝ)+Real.sqrt P+1)) :
    P ≤ (4*(1+3*C)/3)^3 := by
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  have hv : 1 ≤ P^(2/3:ℝ) := Real.one_le_rpow hP (by norm_num)
  have hs : Real.sqrt P ≤ P^(2/3:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hP
    norm_num
  have hW : P^(2/3:ℝ)+Real.sqrt P+1 ≤ 3*P^(2/3:ℝ) := by linarith
  have hCW := mul_le_mul_of_nonneg_left hW hC
  have hlin : P ≤ (4*(1+3*C)/3)*P^(2/3:ℝ) := by nlinarith
  have hp := pow_le_pow_left₀ hP0 hlin 3
  have he : (P^(2/3:ℝ))^3 = P^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hP0]
    norm_num
  rw [mul_pow,he] at hp
  have hpow : P*P^2 ≤ (4*(1+3*C)/3)^3*P^2 := by nlinarith only [hp]
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (by linarith : 0 < P))).mp hpow

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LocalFieldScalarBoundBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma localFieldScale_linear_bound {a m D B C : ℝ}
    (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (_hC : 1 ≤ C)
    (hBC : B ≤ C*m^2) :
    localFieldScale a D B ≤ D/a+(5+C)*(m/a)^2 := by
  let S := (m/a)^2
  have h4 : 1/a^4 ≤ m/a := by
    have hh := div_le_div_of_nonneg_right h3 ha.le
    calc _ = (1/a^3)/a := by ring
         _ ≤ m/a := hh
  have h1 : 1/a ≤ m/a := div_le_div_of_nonneg_right hm ha.le
  have hfirst : (1/a^4+1/a)^2 ≤ 4*S := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1/a^4+1/a) (add_le_add h4 h1) 2
    dsimp [S]
    nlinarith only [hh]
  have hsecond : 1/a^4 ≤ S := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1/a) (cell_reciprocal_bounds ha hm h3).1 2
    have ht := div_le_div_of_nonneg_right hh (sq_nonneg a)
    calc _ = (1/a)^2/a^2 := by ring
         _ ≤ m^2/a^2 := ht
         _ = S := by dsimp [S]; ring
  have hb : B/a^2 ≤ C*S := by
    have hh := div_le_div_of_nonneg_right hBC (sq_nonneg a)
    calc _ ≤ (C*m^2)/a^2 := hh
         _ = C*S := by dsimp [S]; ring
  unfold localFieldScale
  change _ ≤ D/a+(5+C)*S
  nlinarith only [hfirst,hsecond,hb]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ArbitraryCutExcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Metric
noncomputable section
namespace CoulombAtom

 lemma sqrt_product_weighted_young {a O B : ℝ} (ha : 0 < a)
    (hO : 0 ≤ O) (hB : 0 ≤ B) :
    Real.sqrt O*Real.sqrt B ≤ (a*O+B/a)/2 := by
  have hh := sq_nonneg (a*Real.sqrt O-Real.sqrt B)
  have hOs := Real.sq_sqrt hO
  have hBs := Real.sq_sqrt hB
  have hn : 2*a*(Real.sqrt O*Real.sqrt B) ≤ a^2*O+B := by nlinarith
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).2
  apply (mul_le_mul_iff_left₀ ha).mp
  calc (Real.sqrt O*Real.sqrt B*2)*a ≤ a^2*O+B := by nlinarith only [hn]
       _ = (a*O+B/a)*a := by field_simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_AnnularCellGeometryBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric

def annularOffsetMass (D u : ℝ) : ℝ := max (1/u^3) 1+Real.sqrt (D*u)
lemma annularOffsetMass_one_le (D u : ℝ) : 1 ≤ annularOffsetMass D u := by
  unfold annularOffsetMass
  linarith [le_max_right (1/u^3) 1,Real.sqrt_nonneg (D*u)]

def annularCellScaleConstant (alpha beta : ℝ) : ℝ :=
    max ((100000/alpha)^3) 1+Real.sqrt (beta/100000)
lemma annularCellScaleConstant_one_le (alpha beta : ℝ) : 1 ≤ annularCellScaleConstant alpha beta := by
  unfold annularCellScaleConstant
  linarith [le_max_right ((100000/alpha)^3) 1,Real.sqrt_nonneg (beta/100000)]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_AnnularCutExcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Metric
noncomputable section
namespace CoulombAtom

 def annularCellCostConstant (alpha beta : ℝ) : ℝ :=
    (annularCellScaleConstant alpha beta)^2*100000/alpha

 lemma annularCellCostConstant_pos {alpha beta : ℝ} (ha : 0 < alpha) :
    0 < annularCellCostConstant alpha beta := by
  have := annularCellScaleConstant_one_le alpha beta
  unfold annularCellCostConstant
  positivity

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CoulombTailNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter Set
open scoped BigOperators

def tailRadius (h : ℝ) (k : ℕ) : ℝ := (4:ℝ)^k*h
def tailWeight (k : ℕ) : ℝ := (1/2:ℝ)^k
lemma tailRadius_pos {h : ℝ} (hh : 0 < h) (k : ℕ) : 0 < tailRadius h k := by
  unfold tailRadius; positivity
lemma tailWeight_pos (k : ℕ) : 0 < tailWeight k := by unfold tailWeight; positivity
lemma tailRadius_succ (h : ℝ) (k : ℕ) : tailRadius h (k+1) = 4*tailRadius h k := by
  unfold tailRadius; rw [pow_succ]; ring
lemma tailRadius_zero (h : ℝ) : tailRadius h 0 = h := by simp [tailRadius]
lemma tailRadius_mono {h : ℝ} (hh : 0 ≤ h) (k : ℕ) : h ≤ tailRadius h k := by
  exact le_mul_of_one_le_left hh (one_le_pow₀ (by norm_num))
lemma sum_tailWeight_le (K : ℕ) : (∑ k ∈ Finset.range K, tailWeight k) ≤ 2 := by
  have h := geom_sum_mul_neg (x := (1/2:ℝ)) K
  have hp : 0 ≤ (1/2:ℝ)^K := by positivity
  simp only [tailWeight]
  nlinarith

lemma annularOffsetMass_sq_le {D u : ℝ} (hD : 0 ≤ D) (hu : 0 < u) :
    (annularOffsetMass D u)^2 ≤ 3*(1/u^6+1+D*u) := by
  have hs := Real.sq_sqrt (mul_nonneg hD hu.le)
  have hp : 0 ≤ 1/u^3 := by positivity
  have hq : 0 ≤ Real.sqrt (D*u) := Real.sqrt_nonneg _
  have hm : max (1/u^3) 1 ≤ 1/u^3+1 := max_le (by linarith) (by linarith)
  have ht := pow_le_pow_left₀ (by positivity : 0 ≤ max (1/u^3) 1+Real.sqrt (D*u))
    (add_le_add hm le_rfl) 2
  have he : (1/u^3)^2 = 1/u^6 := by ring
  unfold annularOffsetMass
  nlinarith only [ht,hs,he,sq_nonneg (1/u^3-1),sq_nonneg (1/u^3-Real.sqrt (D*u)),
    sq_nonneg (1-Real.sqrt (D*u))]

lemma tailRadius_weight_identity (h : ℝ) (k : ℕ) :
    tailRadius h k*(tailWeight k)^2 = h := by
  unfold tailRadius tailWeight
  have he : (4:ℝ)^k*((1/2:ℝ)^k)^2 = 1 := by
    rw [←pow_mul, Nat.mul_comm k 2, pow_mul, ←mul_pow]
    norm_num
  calc _ = (4^k*((1/2:ℝ)^k)^2)*h := by ring
       _ = h := by rw [he,one_mul]
lemma tailWeight_le_one (k : ℕ) : tailWeight k ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

lemma tail_annular_scale {D h : ℝ} (hD : 0 ≤ D) (hh : 0 < h) (k : ℕ) :
    (1/(tailRadius h k)^6+1+D*tailRadius h k)/((tailRadius h k)^2*tailWeight k) ≤
      tailWeight k*(1/h^8+1/h^2+D/h) := by
  let u := tailRadius h k
  let w := tailWeight k
  have hu : 0 < u := tailRadius_pos hh k
  have hw : 0 < w := tailWeight_pos k
  have hw1 : w ≤ 1 := tailWeight_le_one k
  have he : u*w^2 = h := tailRadius_weight_identity h k
  have huH : h ≤ u := tailRadius_mono hh.le k
  have h1 : 1/u^6 ≤ 1/h^6 := one_div_le_one_div_of_le (pow_pos hh 6)
    (pow_le_pow_left₀ hh.le huH 6)
  have h2 : 1/(u^2*w) ≤ w/h^2 := by
    apply (div_le_iff₀ (by positivity : 0 < u^2*w)).2
    rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hh 2)]
    have hw2 : w^2 ≤ w := by nlinarith
    nlinarith [sq_nonneg (u*w),mul_le_mul_of_nonneg_left hw2 (sq_nonneg u)]
  have h3 : D*u/(u^2*w) = w*(D/h) := by
    rw [←he]
    field_simp
  calc
    _ = (1/u^6+1)/(u^2*w)+D*u/(u^2*w) := by ring
    _ ≤ (1/h^6+1)*(w/h^2)+w*(D/h) := by
      apply add_le_add _ h3.le
      calc _ = (1/u^6+1)*(1/(u^2*w)) := by ring
           _ ≤ _ := mul_le_mul (add_le_add h1 le_rfl) h2 (by positivity) (by positivity)
    _ = _ := by dsimp [w]; field_simp

lemma finite_tail_cauchy (K : ℕ) (b : ℕ → ℝ) :
    (∑ k ∈ Finset.range K, b k)^2 ≤ 2*∑ k ∈ Finset.range K, (b k)^2/tailWeight k := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range K)
    (fun k _ => (tailWeight_pos k).le)
    (fun k _ => div_nonneg (sq_nonneg (b k)) (tailWeight_pos k).le)
    (r := b) (fun k _ => by apply le_of_eq; field_simp [(tailWeight_pos k).ne'])
  exact h.trans (mul_le_mul_of_nonneg_right (sum_tailWeight_le K)
    (Finset.sum_nonneg (fun k _ => div_nonneg (sq_nonneg _) (tailWeight_pos k).le)))

open MeasureTheory Filter Set
open scoped BigOperators
open CoulombObservation

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ObservedFieldScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Metric
noncomputable section
namespace CoulombAtom

def innerScale (D h : ℝ) : ℝ := 1/h^8+1/h^2+D/h
lemma innerScale_nonneg {D h : ℝ} (hD : 0 ≤ D) (hh : 0 < h) : 0 ≤ innerScale D h := by
  unfold innerScale; positivity

lemma annularOffsetMass_sq_div {D h : ℝ} (hD : 0 ≤ D) (hh : 0 < h) :
    (annularOffsetMass D h)^2/h^2 ≤ 3*innerScale D h := by
  calc
    _ ≤ (3*(1/h^6+1+D*h))/h^2 := div_le_div_of_nonneg_right (annularOffsetMass_sq_le hD hh) (sq_nonneg _)
    _ = _ := by unfold innerScale; field_simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_AllSectorEnergy
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
open MeasureTheory Set Metric
open scoped ENNReal
namespace CoulombAtom

def allSectorEnergy (Z : ℝ) : ℝ := sInf (Set.range (energy Z))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_LocalDensityTraceBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombLT

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ENNReal

open CoulombPauli CoulombPackets CoulombAtom
variable {N : ℕ} {κ : Type*}

 def indexedFermionFamily
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := Space)))))
    (ψ : Fin (N+1) → fermionL2 (V := Space) (N+1))
    (p : Fin (N+1) × Fin 2 × κ) : Lp ℂ 2 (volume : Measure Space) :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • spinMarginal (splitFermion p.1 (ψ p.1)) p.2.1 (b p.2.2)

 def coordinateWeightedTrace (ψ : Fin (N+1) → fermionL2 (V := Space) (N+1))
    (w : Space → ℝ) : ℝ≥0∞ :=
   ∑ i : Fin (N+1), ∫⁻ q, ENNReal.ofReal (w (q i).1)*ENNReal.ofReal (‖ψ i q‖^2)
     ∂(configMeasure (N+1) (spinSpaceMeasure (V := Space)))

end CoulombLT

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_BarrierConditionalBarrier
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CoulombBarrier

def reaction (k t : ℝ) : ℝ := 4*Real.pi*k*(max t 0)^(3/2:ℝ)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierSmoothMaxBarrier
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter Laplacian InnerProductSpace MeasureTheory
open scoped Topology BigOperators

namespace CoulombBarrier

def smoothPositive (ε t : ℝ) : ℝ := (t+Real.sqrt (t^2+ε^2))/2

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierRetainedComparisonBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierRetainedComparison_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom

def InverseComparisonAt (d H μ κ hₗ hₕ ξ C : ℝ) : Prop :=
  d^4*H ≤ C ∧
  (∀ h ∈ Icc hₗ hₕ, κ*h^(3/2:ℝ) < d^6*μ → h-ξ ≤ d^4*H) ∧
  (∀ h ∈ Icc hₗ hₕ, d^6*μ < κ*h^(3/2:ℝ) → d^4*H ≤ h+ξ)

end Work_BarrierRetainedComparison_barrier_scope

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology ContDiff

open CoulombAtom

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierStepGeometryBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom

def barrierGap (B : ℝ) : ℝ := B/(16*(11/10:ℝ)^5)

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierRetainedFiniteBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom

structure OutwardCalibration (κ B C M lam1 lam2 e ξ hl hh : ℝ) : Prop where
  k_nonneg : 0 ≤ κ
  B_pos : 0 < B
  C_nonneg : 0 ≤ C
  B_le_C : B ≤ C
  M_large : 2 < M
  xi_nonneg : 0 ≤ ξ
  low_shift : ξ < lam2
  shift_order : lam2 ≤ lam1
  shift_small : lam1 < barrierGap B
  gap : 16*ξ+2*e < lam1-lam2
  e_pos : 0 < e
  e_small : 2*e*(2*M)^4 < B/4
  cap_shift : C/M^4 < lam2
  height_low : hl < B/4
  height_high : C < hh
  subsolution : 4*Real.pi*κ*Real.sqrt B ≤ 19/2

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierStepWeakBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter
open scoped Topology

namespace CoulombAtom
open CoulombObservation

def initialDensityConstant : ℝ :=
  (2*Pauli.globalDensityConstant)^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)*4^(1/5:ℝ)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierNuclearScaleBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter Set
open scoped Topology

namespace CoulombBarrier
open CoulombAtom

def initialQuadraticConstant (k : ℝ) : ℝ := 1+(4*Real.pi*k*2^(3/2:ℝ))/6

def initialQuadratic (C Z r : ℝ) : ℝ := C*(Z/r)^(3/2:ℝ)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SelectionNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Filter Set Metric
open scoped Topology
namespace CoulombBarrier
open CoulombAtom

def selectedDyadicIndex (r t : ℝ) : ℕ := by
  classical
  exact if h : @Exists ℕ (fun J => (2:ℝ)^J*r ≤ t ∧ t < 2*((2:ℝ)^J*r)) then Classical.choose h else 0

end CoulombBarrier

end

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_TailObservationEventBarrier
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set

namespace CoulombAtom
open CoulombObservation

@[instance_reducible] def tailInvariantArraySpace (N K j : ℕ) :
    MeasurableSpace (Fin K × (Fin N × Fin 3) → ℝ) where
  MeasurableSet' A := ∀ (u v : Fin K × (Fin N × Fin 3) → ℝ), (∀ k : Fin K, j ≤ k.val → ∀ (i : Fin N) (a : Fin 3), u (k,i,a) = v (k,i,a)) →
    (u ∈ A ↔ v ∈ A)
  measurableSet_empty := fun _ _ _ => Iff.rfl
  measurableSet_compl := fun _ h u v huv => not_congr (h u v huv)
  measurableSet_iUnion := by
    intro f h u v huv
    simp only [mem_iUnion]
    exact exists_congr (fun n => h n u v huv)

def tailObservationCoefficient {K : ℕ} (ell : Fin K → ℝ) (j : ℕ) (k : Fin K) : ℝ :=
  if j ≤ k.val then (ell k)⁻¹ else 0

end CoulombAtom

open MeasureTheory Set Finset
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TailInitialEventuallyBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_TailInitialEventually_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

open CoulombAtom CoulombObservation

def tailPolynomialThreshold (r : ℝ) {K : ℕ} (j : Fin (K+1)) : ℝ :=
  min 1 (((2:ℝ)^j.val*r)^40)

end Work_TailInitialEventually_barrier_scope

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

open CoulombAtom CoulombObservation

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_InverseThresholdLimitBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

namespace CoulombAtom

 def localTFResponse (h : ℝ) : ℝ :=
  (max h 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservedInnerCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Set

lemma annular_cut_cost_innerScale {D h u : ℝ} (hD : 0 ≤ D) (hh : 0 < h) (hu : h ≤ u) :
    (annularOffsetMass D u)^2/u/h ≤ 3*innerScale D h := by
  have hup : 0 < u := hh.trans_le hu
  calc
    _ ≤ (3*(1/u^6+1+D*u))/u/h :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (annularOffsetMass_sq_le hD hup) hup.le) hh.le
    _ = 3*((1/u^7)/h+(1/u)/h+D/h) := by field_simp
    _ ≤ 3*((1/h^7)/h+(1/h)/h+D/h) := by gcongr
    _ = _ := by unfold innerScale; field_simp

end
open MeasureTheory Filter
open scoped BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TinyProbabilityFloorBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped Topology

namespace CoulombAtom
open CoulombBarrier

 def tinyProbabilityFloor (Z u : ℝ) : ℝ := min 1 (u^80)/(1+Z)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_PricedSubsequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

open Filter
open scoped Topology
namespace CoulombAtom

def fixedSectorScale (t m : ℝ) : ℝ := t^(-1/4:ℝ)*m^(-1/3:ℝ)
end CoulombAtom

end

end OAI
end


