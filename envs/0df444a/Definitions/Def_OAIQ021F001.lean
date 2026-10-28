-- Prove2me | Definitions.Def_OAIQ021F001
-- name    : OAIQ021F001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T18:04:37.214876+00:00
-- url     : https://prove2.me/theorems/7498b12b-ee68-4b5b-b7fe-dd5cc109de7b
-- title:
--   Definitions bundle OAIQ021F001 of the split of OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt`, carved from OpenAI's openai/math development (OpenAI, *Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)*, OpenAI Math Release, September 24, 2026, result family 211, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 396 declarations of OpenAI's Lean: 194 definitions, 3 inductive types or structures, 8 instances and 191 theorems. The definitions and types are `OAI.FKCRT.Inventory.bottom`, `OAI.FKCRT.Inventory.criticalApproach`, `OAI.FKCRT.Inventory.dartInsert`, `OAI.FKCRT.Inventory.heightFactor`, `OAI.FKCRT.Inventory.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions`, `OAI.FKCRT.Inventory.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_1`, `OAI.FKCRT.Inventory.listDartEquiv`, `OAI.FKCRT.Inventory.liveAt`, `OAI.FKCRT.Inventory.seamIntervals`, `OAI.FKCRT.Inventory.startingSupply`, `OAI.FKCRT.Inventory.typeSign`, `OAI.FKCRT.MapCycles.JoinRel`, `OAI.FKCRT.Multiforest`, `OAI.FKCRT.PermutationWedge.Side`, `OAI.FKCRT.PermutationWedge.flipRetractD`, `OAI.FKCRT.PermutationWedge.retractD`, `OAI.FKCRT.PermutationWedge.sideCongr`, `OAI.FKCRT.PermutationWedge.sideGraph`, `OAI.FKCRT.PermutationWedge.sideGraphCongr`, `OAI.FKCRT.PermutationWedge.sideMk`, `OAI.FKCRT.PermutationWedge.sideSetoid`, `OAI.FKCRT.Radial.Space`, `OAI.FKCRT.Radial.axis`, `OAI.FKCRT.Radial.bridgeDensity`, `OAI.FKCRT.Radial.bridgeRatio`, `OAI.FKCRT.Radial.bridgeResidual`, `OAI.FKCRT.Radial.bridgeVariance`, `OAI.FKCRT.Radial.bridgeVector`, `OAI.FKCRT.Radial.chain`, `OAI.FKCRT.Radial.chainDensity`, `OAI.FKCRT.Radial.coordinates`, `OAI.FKCRT.Radial.innovation`, `OAI.FKCRT.Radial.step`, `OAI.FKCRT.Radial.transition`, `OAI.FKCRT.SimpleWalk.arrayPolygon`, `OAI.FKCRT.SimpleWalk.chooseInt`, `OAI.FKCRT.SimpleWalk.cylindricalDensity`, `OAI.FKCRT.SimpleWalk.durationRatio`, `OAI.FKCRT.SimpleWalk.durationVariance`, `OAI.FKCRT.SimpleWalk.evenGrid` and 157 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/FKMaps, in whole or in part: `FKMaps_BlockCritical`, `FKMaps_BlockLaw`, `FKMaps_BridgeLimit`, `FKMaps_CanonicalBijection`, `FKMaps_Convergence`, `FKMaps_CoreCompression`, `FKMaps_CoreWords`, `FKMaps_CornerMass`, `FKMaps_ExcursionGeometry`, `FKMaps_ExcursionKernel`, `FKMaps_ExcursionLaw`, `FKMaps_GHPBounds`, `FKMaps_GraphWedge`, `FKMaps_HeightBounds`, `FKMaps_HeightCoding`, `FKMaps_HeightTightness`, `FKMaps_InventoryStopping`, `FKMaps_LadderCuts`, `FKMaps_LadderRecords`, `FKMaps_MapCycles`, `FKMaps_MapEncoding`, `FKMaps_MarkedBounds`, `FKMaps_MarkedSpines`, `FKMaps_Matching`, `FKMaps_MeasuredCoding`, `FKMaps_MetricLimit`, `FKMaps_NodeOrder`, `FKMaps_Offspring`, `FKMaps_PathCLT`, `FKMaps_PieceLaws`, `FKMaps_PieceWalks`, `FKMaps_PlanarActivity`, `FKMaps_PlaneTrees`, `FKMaps_RadialBridge`, `FKMaps_SimpleWalk`, `FKMaps_SpineBounds`, `FKMaps_SpineMoments`, `FKMaps_StationaryCuts`, `FKMaps_TraceLimit`, `FKMaps_TreeCode`, `FKMaps_UniformSeams`, `FKMaps_Vervaat`, `FKMaps_WalkBounds`, `FKMaps_WordCoefficients`.
--
--   **Imports.** It imports the published bundle `Def_FKCRT`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ021F002` and `OAIQ021F003`.
-- source:
--   OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 211; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/FKMaps at commit adc7f12

import Mathlib
import Definitions.Def_FKCRT

section
-- module Solutions.OAIQ021_FK.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_WalkBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


lemma independent_sum_martingale {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hXi : ∀ k, Integrable (X k) μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0) :
    Martingale (fun n ω => ∑ k ∈ Finset.range (n+1), X k ω)
      (Filtration.natural X hXm) μ := by
  have hadp : StronglyAdapted (Filtration.natural X hXm)
      (fun n ω => ∑ k ∈ Finset.range (n+1), X k ω) := by
    intro n
    have h : ∀ k ∈ Finset.range (n+1),
        StronglyMeasurable[(Filtration.natural X hXm) n] (X k) := by
      intro k hk
      exact ((Filtration.stronglyAdapted_natural hXm) k).mono
        ((Filtration.natural X hXm).mono (show k ≤ n from by simpa using hk))
    convert Finset.stronglyMeasurable_sum _ h using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp

  have hint : ∀ n, Integrable (fun ω => ∑ k ∈ Finset.range (n+1), X k ω) μ := by
    intro n
    exact integrable_finsetSum _ (fun k _ => hXi k)
  apply martingale_nat hadp hint
  intro n
  have heq : (fun ω => ∑ k ∈ Finset.range (n+1+1), X k ω) =
      (fun ω => ∑ k ∈ Finset.range (n+1), X k ω) + X (n+1) := by
    funext ω
    exact Finset.sum_range_succ _ _
  rw [heq]
  filter_upwards [condExp_add (hint n) (hXi (n+1)) (Filtration.natural X hXm n),
    hX.condExp_natural_ae_eq_of_lt hXm (show n < n+1 by omega)] with ω hsum hnew
  rw [condExp_of_stronglyMeasurable (Filtration.le _ n) (hadp n) (hint n),
    Pi.add_apply, hnew, hzero, add_zero] at hsum
  exact hsum.symm


def hat (N i : ℕ) : C(unitInterval, ℝ) where
  toFun t := max 0 (1 - |(N : ℝ) * (t : ℝ) - i|)
  continuous_toFun := continuous_const.max
    (continuous_const.sub ((continuous_const.mul continuous_subtype_val).sub continuous_const).abs)


def interpolation (N : ℕ) (a : Fin (N+1) → ℝ) : C(unitInterval, ℝ) :=
  ∑ i : Fin (N+1), a i • hat N i.val


def tailValue (R x : ℝ) : ℝ := if R < |x| then x else 0


def centeredTail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (R : ℝ) (ω : Ω) : ℝ :=
  tailValue R (X ω) - ∫ z, tailValue R (X z) ∂μ


def centeredHead {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (R : ℝ) (ω : Ω) : ℝ :=
  (X ω - tailValue R (X ω)) - ∫ z, X z - tailValue R (X z) ∂μ


def scaledWalk {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : C(unitInterval, ℝ) :=
  interpolation n (fun i => (∑ j ∈ Finset.range i.val, X j ω) / Real.sqrt n)


def gridPoint (N : ℕ) (i : Fin (N+1)) : unitInterval :=
  ⟨(i.val : ℝ)/(N : ℝ), by
    constructor
    · positivity
    · by_cases hN : N = 0
      · simp [hN]
      · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).mpr
          (by exact_mod_cast Nat.le_of_lt_succ i.isLt)⟩


def pathApprox (N : ℕ) (f : C(unitInterval, ℝ)) : C(unitInterval, ℝ) :=
  interpolation N (fun i => f (gridPoint N i))


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PathCLT
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions : MeasurableSpace C(unitInterval, ℝ) := borel _

def coarseWalk {Ω : Type*} (X : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω) : C(unitInterval, ℝ) :=
  interpolation m (fun i => (∑ j ∈ Finset.range (i.val*(n/m)), X j ω)/Real.sqrt n)

def coarseIndex (m n : ℕ) (i : Fin (m+1)) : Fin (n+1) :=
  ⟨i.val*(n/m), lt_of_le_of_lt (le_trans
    (Nat.mul_le_mul_right (n/m) (Nat.le_of_lt_succ i.isLt)) (Nat.mul_div_le n m)) (Nat.lt_succ_self n)⟩

def cumulative (m : ℕ) (a : Fin m → ℝ) (i : Fin (m+1)) : ℝ :=
  ∑ j ∈ Finset.range i.val, if h : j < m then a ⟨j,h⟩ else 0

local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_1 : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance instBorelSpaceContinuousMapElemRealUnitInterval_solutions_1 : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

def gridTime (m : ℕ) (i : Fin (m+1)) : ℝ≥0 := ⟨(i.val:ℝ)/(m:ℝ), by positivity⟩

def meshIncrement {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (m : ℕ) (i : Fin m) (ω : Ω) : ℝ :=
  B (gridTime m i.succ) ω-B (gridTime m i.castSucc) ω

def brownianPath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : C(unitInterval, ℝ) :=
  ContinuousMap.mkD (fun t => B ⟨(t:ℝ),t.property.1⟩ ω) 0

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_Offspring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_2 : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance instBorelSpaceContinuousMapElemRealUnitInterval_solutions_2 : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩


def totalStep {N : ℕ} (d : Fin N → ℕ) : ℤ := ∑ i, ((d i : ℤ) - 1)


lemma totalStep_eq_sum_sub {N : ℕ} (d : Fin N → ℕ) :
    totalStep d = (∑ i, d i : ℕ) - (N : ℤ) := by
  simp [totalStep, Finset.sum_sub_distrib]


lemma totalStep_measurable (N : ℕ) : Measurable (@totalStep N) := by
  unfold totalStep
  fun_prop


def iidSplit (m r : ℕ) : (Fin (m+r) → ℕ) ≃ᵐ ((Fin m → ℕ) × (Fin r → ℕ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (m+r) => ℕ) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin r => ℕ))


@[simp] lemma iidSplit_fst (m r : ℕ) (d : Fin (m+r) → ℕ) :
    (iidSplit m r d).1 = fun i => d (Fin.castAdd r i) := rfl


@[simp] lemma iidSplit_snd (m r : ℕ) (d : Fin (m+r) → ℕ) :
    (iidSplit m r d).2 = fun i => d (Fin.natAdd m i) := rfl


def stopTime (t : unitInterval) : C(unitInterval,unitInterval) where
  toFun s := min s t
  continuous_toFun := continuous_id.min continuous_const


def stopPath (t : unitInterval) (f : C(unitInterval,ℝ)) : C(unitInterval,ℝ) :=
  f.comp (stopTime t)


lemma norm_tsum_smul_lt_one {α : Type*} [DecidableEq α]
    (w : α → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : HasSum w 1)
    (z : α → ℂ) (hz : ∀ k, ‖z k‖ = 1)
    {a b : α} (hab : a ≠ b) (ha : 0 < w a) (hb : 0 < w b)
    (hne : z a ≠ z b) : ‖∑' k, w k • z k‖ < 1 := by
  have hnorm : ∀ k, ‖w k • z k‖ = w k := by
    intro k
    rw [norm_smul, Real.norm_of_nonneg (hw k), hz, mul_one]
  have hsumNorm : Summable (fun k => ‖w k • z k‖) := by simpa only [hnorm] using hs.summable
  have hsum : Summable (fun k => w k • z k) := hsumNorm.of_norm
  have hstrict : ‖w a • z a + w b • z b‖ < w a + w b := by
    have hraw : ‖w a • z a + w b • z b‖ < ‖w a • z a‖ + ‖w b • z b‖ := by
      apply norm_add_lt_of_not_sameRay
      intro hr
      have he := hr.norm_smul_eq
      rw [hnorm a, hnorm b, smul_smul, smul_smul, mul_comm (w b) (w a)] at he
      exact hne ((smul_right_injective ℂ (mul_pos ha hb).ne' he).symm)
    simpa only [hnorm] using hraw
  have hdecomp := hsum.sum_add_tsum_compl (s := {a,b})
  have hwdecomp := hs.summable.sum_add_tsum_compl (s := {a,b})
  simp only [Finset.sum_pair hab] at hdecomp hwdecomp
  rw [hs.tsum_eq] at hwdecomp
  rw [← hdecomp]
  calc
    ‖w a • z a + w b • z b + ∑' k : {k : α // k ∉ ({a,b} : Finset α)}, w k.val • z k.val‖ ≤
        ‖w a • z a + w b • z b‖ +
          ‖∑' k : {k : α // k ∉ ({a,b} : Finset α)}, w k.val • z k.val‖ := norm_add_le _ _
    _ < w a + w b + ∑' k : {k : α // k ∉ ({a,b} : Finset α)}, w k.val := by
      apply add_lt_add_of_lt_of_le hstrict
      simpa only [hnorm] using norm_tsum_le_tsum_norm (hsumNorm.subtype _)
    _ = 1 := hwdecomp


lemma gaussian_fourier_shift (x : ℝ) :
    (∫ t : ℝ, Complex.exp (-(t:ℂ)^2/2) *
      Complex.exp ((-x*t : ℝ) * Complex.I)) =
      (Real.sqrt (2*Real.pi) * Real.exp (-x^2/2) : ℝ) := by
  have h := fourierIntegral_gaussian (b := (1/2:ℂ)) (by norm_num) (-(x:ℂ))
  have hpow : (Real.pi / (1/2:ℂ)) ^ (1/2:ℂ) = (Real.sqrt (2*Real.pi) : ℝ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    congr 1
    ring
  rw [hpow] at h
  convert h using 1
  · apply integral_congr_ae
    filter_upwards [] with t
    rw [mul_comm]
    congr 2 <;> push_cast <;> ring
  · push_cast
    congr 2
    ring


lemma gaussian_phase_integrable (x : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (-(t:ℂ)^2/2) *
      Complex.exp ((-x*t : ℝ) * Complex.I)) := by
  apply (integrable_exp_neg_mul_sq (show (0:ℝ)<1/2 by norm_num)).mono' (by fun_prop)
  filter_upwards [] with t
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_exp]
  apply le_of_eq
  congr 1
  simp only [Complex.neg_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.div_ofNat]
  ring


lemma totalStep_split (m r : ℕ) (d : Fin (m+r) → ℕ) :
    totalStep d = totalStep (iidSplit m r d).1 + totalStep (iidSplit m r d).2 := by
  exact Fin.sum_univ_add _


def endpointWindow (s : Finset ℤ) (w : ℤ → ℝ) (z : ℤ) : ℝ :=
  ∑ j ∈ s, if z=j then w j else 0


def softCutoff (ε x : ℝ) : ℝ := max 0 (1-|x|/ε)


def latticeWindow (N : ℕ) (R : ℝ) : Finset ℤ :=
  (Finset.Icc (-(⌈R⌉₊ : ℤ)) (⌈R⌉₊ : ℤ)).filter
    (fun j => Even ((N:ℤ)+j) ∧ |(j:ℝ)| < R)


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_BridgeLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_3 : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance instBorelSpaceContinuousMapElemRealUnitInterval_solutions_3 : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

def bridgePath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : C(unitInterval, ℝ) :=
  brownianPath B ω - B 1 ω • ⟨fun t => (t:ℝ), continuous_subtype_val⟩

def reverseArray (N : ℕ) : (Fin N → ℕ) ≃ᵐ (Fin N → ℕ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℕ) Fin.revPerm

def earlyTime (j : ℕ) : unitInterval :=
  ⟨1/((j:ℝ)+2),by constructor <;> (try positivity); apply (div_le_one (by positivity)).mpr; linarith [Nat.cast_nonneg j (α := ℝ)]⟩

def freezeGauge (M : ℝ) (L : ℝ≥0) (f : C(unitInterval,ℝ)) : ℝ :=
  min (2*M) (2*(L:ℝ)*‖f‖)

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_Vervaat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_4 : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance instBorelSpaceContinuousMapElemRealUnitInterval_solutions_4 : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

def clipTime (x : ℝ) : unitInterval := projIcc 0 1 zero_le_one x

@[fun_prop] lemma continuous_clipTime : Continuous clipTime := continuous_projIcc (h := zero_le_one)

def cyclePath (c : unitInterval) (f : C(unitInterval,ℝ)) : C(unitInterval,ℝ) where
  toFun t := f (clipTime ((c:ℝ)+(t:ℝ)))+
    f (clipTime ((c:ℝ)+(t:ℝ)-1))-f 0-f c
  continuous_toFun := by
    apply Continuous.sub _ continuous_const
    apply Continuous.sub _ continuous_const
    exact (f.continuous.comp (continuous_clipTime.comp (continuous_const.add continuous_subtype_val))).add
      (f.continuous.comp (continuous_clipTime.comp ((continuous_const.add continuous_subtype_val).sub continuous_const)))

lemma exists_minTime (f : C(unitInterval,ℝ)) : ∃ c, ∀ t, f c ≤ f t := by
  obtain ⟨c,_,hc⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (univ : Set unitInterval).Nonempty)
    f.continuous.continuousOn
  exact ⟨c,fun t => hc (mem_univ t)⟩

lemma exists_firstMinimum (f : C(unitInterval,ℝ)) :
    ∃ c, (∀ t, f c ≤ f t) ∧ ∀ d, (∀ t, f d ≤ f t) → c ≤ d := by
  obtain ⟨d,hd⟩ := exists_minTime f
  have hK : IsCompact {t | f t=f d} := (isClosed_eq f.continuous continuous_const).isCompact
  obtain ⟨c,hc,hleast⟩ := hK.exists_isLeast ⟨d,rfl⟩
  refine ⟨c,fun t => hc.trans_le (hd t),?_⟩
  intro e he
  exact hleast (le_antisymm (he d) (hd e))

def minTime (f : C(unitInterval,ℝ)) : unitInterval := (exists_firstMinimum f).choose

def UniqueMinimum (f : C(unitInterval,ℝ)) (c : unitInterval) : Prop :=
  (∀ t, f c ≤ f t) ∧ ∀ t, f t=f c → t=c

def vervaat (f : C(unitInterval,ℝ)) : C(unitInterval,ℝ) := cyclePath (minTime f) f

def restrictedMin (K : Set unitInterval) (hK : IsCompact K) (hne : K.Nonempty)
    (f : C(unitInterval,ℝ)) : ℝ :=
  f (hK.exists_isMinOn hne f.continuous.continuousOn).choose

def reversePath (f : C(unitInterval,ℝ)) : C(unitInterval,ℝ) :=
  f.comp ⟨unitInterval.symm,unitInterval.continuous_symm⟩

def lastMinTime (f : C(unitInterval,ℝ)) : unitInterval :=
  unitInterval.symm (minTime (reversePath f))

def HasUniqueMinimum (f : C(unitInterval,ℝ)) : Prop := ∃ c, UniqueMinimum f c

def tiltPath (a : ℝ) (f : C(unitInterval,ℝ)) : C(unitInterval,ℝ) :=
  f+a • ⟨Subtype.val,continuous_subtype_val⟩

def TiltMinimum (f : unitInterval → ℝ) (a : ℝ) (t : unitInterval) : Prop :=
  ∀ s, f t+a*(t:ℝ) ≤ f s+a*(s:ℝ)

def prefixTimePath (a : unitInterval) (f : C(unitInterval,ℝ)) : C(unitInterval,ℝ) :=
  f.comp ⟨fun t => a*t,by fun_prop⟩

def prefixResidual {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (a : unitInterval) (ω : Ω) :
    C(unitInterval,ℝ) := prefixTimePath a (brownianPath B ω)-
      B ⟨(a:ℝ),a.property.1⟩ ω • ⟨Subtype.val,continuous_subtype_val⟩

def bridgeAt {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (a : unitInterval) (ω : Ω) : ℝ :=
  B ⟨(a:ℝ),a.property.1⟩ ω-(a:ℝ)*B 1 ω

def circleTime (c t : unitInterval) : unitInterval :=
  if h : (c:ℝ)+(t:ℝ) ≤ 1 then
    ⟨(c:ℝ)+(t:ℝ),add_nonneg c.property.1 t.property.1,h⟩
  else ⟨(c:ℝ)+(t:ℝ)-1,by linarith,by linarith [c.property.2,t.property.2]⟩

def bbCov (s t : ℝ) : ℝ := min s t-s*t

def minAtSet (c : unitInterval) : Set C(unitInterval,ℝ) := {f | ∀ t, f c ≤ f t}

def reciprocalTime (n : ℕ) : unitInterval :=
  ⟨1/((n:ℝ)+2),by positivity,by rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg n (α := ℝ)]⟩

def innerCut (n : ℕ) : unitInterval :=
  ⟨1-(reciprocalTime n:ℝ),sub_nonneg.mpr (reciprocalTime n).property.2,
    sub_le_self _ (reciprocalTime n).property.1⟩

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_TreeCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_5 : MeasurableSpace C(unitInterval, ℝ) := borel _


def binaryCombDegrees (n : ℕ) : Fin (2*n+1) → Fin (2*n+1) := fun i =>
  ⟨if i.val < n then 2 else 0, by split_ifs <;> omega⟩


def prefixSum (l : List ℤ) (j : ℕ) : ℤ := (l.take j).sum


def IsExcursionList (l : List ℤ) : Prop :=
  l.sum = -1 ∧ ∀ j < l.length, 0 ≤ prefixSum l j


def FirstMinimum (l : List ℤ) (m : ℕ) : Prop :=
  m < l.length ∧ (∀ j < l.length, prefixSum l m ≤ prefixSum l j) ∧
    ∀ j < m, prefixSum l m < prefixSum l j


@[simp] lemma prefixSum_zero (l : List ℤ) : prefixSum l 0 = 0 := by simp [prefixSum]


@[simp] lemma prefixSum_length (l : List ℤ) : prefixSum l l.length = l.sum := by
  simp [prefixSum]


lemma prefixSum_drop (l : List ℤ) (m j : ℕ) :
    prefixSum (l.drop m) j = prefixSum l (m + j) - prefixSum l m := by
  simp only [prefixSum, List.take_add, List.sum_append]
  omega


lemma sum_drop (l : List ℤ) (m : ℕ) :
    (l.drop m).sum = l.sum - prefixSum l m := by
  have := congrArg List.sum (List.take_append_drop m l)
  simp only [List.sum_append] at this
  unfold prefixSum
  omega


lemma prefixSum_rotate_left (l : List ℤ) {m j : ℕ} (hm : m ≤ l.length)
    (hj : j ≤ l.length - m) :
    prefixSum (l.rotate m) j = prefixSum l (m + j) - prefixSum l m := by
  rw [List.rotate_eq_drop_append_take hm]
  rw [prefixSum, List.take_append_of_le_length (by simpa using hj)]
  exact prefixSum_drop l m j


lemma prefixSum_rotate_right (l : List ℤ) {m j : ℕ} (hm : m ≤ l.length)
    (hj : l.length - m ≤ j) (hj' : j ≤ l.length) :
    prefixSum (l.rotate m) j = l.sum - prefixSum l m +
      prefixSum l (j - (l.length - m)) := by
  rw [List.rotate_eq_drop_append_take hm]
  simp only [prefixSum, List.take_append, List.length_drop, List.sum_append]
  rw [List.take_of_length_le (by simpa using hj), List.take_take,
    Nat.min_eq_left (by omega)]
  rw [sum_drop]
  rfl


lemma exists_firstListMinimum {l : List ℤ} (hl : l ≠ []) : ∃ m, FirstMinimum l m := by
  have hex : ∃ m, m < l.length ∧ ∀ j < l.length, prefixSum l m ≤ prefixSum l j := by
    obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.range l.length)
      (prefixSum l) (by simpa using hl)
    exact ⟨m, Finset.mem_range.mp hm, fun j hj => hmin j (Finset.mem_range.mpr hj)⟩
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  refine ⟨m, hm.1, hm.2, ?_⟩
  intro j hj
  have hjN : j < l.length := lt_trans hj hm.1
  by_contra h
  have hle : prefixSum l j ≤ prefixSum l m := le_of_not_gt h
  have hjmin : j < l.length ∧ ∀ k < l.length, prefixSum l j ≤ prefixSum l k :=
    ⟨hjN, fun k hk => hle.trans (hm.2 k hk)⟩
  have hfind := Nat.find_min' hex hjmin
  omega


lemma FirstMinimum.unique {l : List ℤ} {m r : ℕ}
    (hm : FirstMinimum l m) (hr : FirstMinimum l r) : m = r := by
  rcases lt_trichotomy m r with h | h | h
  · have h1 := hm.2.1 r hr.1
    have h2 := hr.2.2 m h
    omega
  · exact h
  · have h1 := hr.2.1 m hm.1
    have h2 := hm.2.2 r h
    omega


lemma isExcursionList_rotate_of_firstMinimum {l : List ℤ} (hs : l.sum = -1)
    {m : ℕ} (hm : FirstMinimum l m) : IsExcursionList (l.rotate m) := by
  refine ⟨(List.rotate_perm l m).sum_eq.trans hs, ?_⟩
  intro j hj
  rw [List.length_rotate] at hj
  by_cases hleft : j < l.length - m
  · rw [prefixSum_rotate_left l hm.1.le hleft.le]
    exact sub_nonneg.mpr (hm.2.1 _ (by omega))
  · rw [prefixSum_rotate_right l hm.1.le (by omega) hj.le, hs]
    have hmin := hm.2.2 (j - (l.length - m)) (by omega)
    omega


lemma firstMinimum_of_isExcursionList_rotate {l : List ℤ} (hs : l.sum = -1)
    {m : ℕ} (hm : m < l.length) (he : IsExcursionList (l.rotate m)) :
    FirstMinimum l m := by
  have hnonneg : ∀ j < l.length, 0 ≤ prefixSum (l.rotate m) j := by
    simpa only [List.length_rotate] using he.2
  have hstrict : ∀ j < m, prefixSum l m < prefixSum l j := by
    intro j hj
    have hsum := hnonneg (l.length - m + j) (by omega)
    rw [prefixSum_rotate_right l hm.le (by omega) (by omega), hs] at hsum
    have hcancel : l.length - m + j - (l.length - m) = j := by omega
    rw [hcancel] at hsum
    omega
  refine ⟨hm, ?_, hstrict⟩
  intro j hj
  by_cases hjm : j < m
  · exact (hstrict j hjm).le
  · have hsum := hnonneg (j - m) (by omega)
    rw [prefixSum_rotate_left l hm.le (by omega)] at hsum
    have hcancel : m + (j - m) = j := by omega
    rw [hcancel] at hsum
    omega


theorem existsUnique_excursion_rotation {l : List ℤ} (hs : l.sum = -1) :
    ∃! m : ℕ, m < l.length ∧ IsExcursionList (l.rotate m) := by
  have hl : l ≠ [] := by rintro rfl; simp at hs
  obtain ⟨m, hm⟩ := exists_firstListMinimum hl
  refine ⟨m, ⟨hm.1, isExcursionList_rotate_of_firstMinimum hs hm⟩, ?_⟩
  rintro r ⟨hr, he⟩
  exact (firstMinimum_of_isExcursionList_rotate hs hr he).unique hm


lemma weighted_unique_rotation {α J : Type*} [Fintype α] [Fintype J]
    (r : J → Equiv.Perm α) (w : α → ℝ) (good : α → Prop) [DecidablePred good]
    (hinv : ∀ j a, w (r j a) = w a)
    (hunique : ∀ a, ∃! j, good (r j a)) :
    ∑ a : α, w a = (Fintype.card J : ℝ) * ∑ a : α, if good a then w a else 0 := by
  classical
  have hrow : ∀ a, (∑ j : J, if good (r j a) then w (r j a) else 0) = w a := by
    intro a
    obtain ⟨j, hj, heq⟩ := hunique a
    rw [Finset.sum_eq_single j]
    · simp [hj, hinv]
    · intro k _ hkj
      have hk : ¬ good (r k a) := fun hk => hkj (heq k hk)
      simp [hk]
    · simp
  calc
    ∑ a : α, w a = ∑ a : α, ∑ j : J, if good (r j a) then w (r j a) else 0 :=
      Finset.sum_congr rfl (fun a _ => (hrow a).symm)
    _ = ∑ j : J, ∑ a : α, if good (r j a) then w (r j a) else 0 := Finset.sum_comm
    _ = ∑ _j : J, ∑ a : α, if good a then w a else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact Equiv.sum_comp (r j) (fun a => if good a then w a else 0)
    _ = _ := by simp [nsmul_eq_mul]


def degreeList {N : ℕ} (d : Fin N → Fin N) : List ℤ :=
  List.ofFn (fun i => ((d i).val : ℤ) - 1)


@[simp] lemma degreeList_length {N : ℕ} (d : Fin N → Fin N) :
    (degreeList d).length = N := List.length_ofFn


def rotateDegrees {N : ℕ} [NeZero N] (m : Fin N) : Equiv.Perm (Fin N → Fin N) where
  toFun d i := d (i + m)
  invFun d i := d (i - m)
  left_inv d := by funext i; simp
  right_inv d := by funext i; simp


lemma degreeList_rotate {N : ℕ} [NeZero N] (m : Fin N) (d : Fin N → Fin N) :
    degreeList (rotateDegrees m d) = (degreeList d).rotate m.val := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [degreeList, List.getElem_ofFn, List.getElem_rotate, List.length_ofFn,
      rotateDegrees, Equiv.coe_fn_mk, Fin.add_def]


def firstZero {Ω : Type*} (S : ℕ → Ω → ℤ) (ω : Ω) : WithTop ℕ := by
  classical
  exact if h : ∃ n, S n ω=0 then WithTop.some (Nat.find h) else ⊤


lemma firstZero_le_iff {Ω : Type*} (S : ℕ → Ω → ℤ) (ω : Ω) (n : ℕ) :
    firstZero S ω ≤ WithTop.some n ↔ ∃ k  ≤  n, S k ω=0 := by
  classical
  unfold firstZero
  split_ifs with h
  · norm_cast
    exact Nat.find_le_iff h n
  · simp only [WithTop.top_le_iff,WithTop.coe_ne_top,false_iff,not_exists,not_and]
    intro k _ hk
    exact h ⟨k,hk⟩


lemma firstZero_isStoppingTime {Ω : Type*} [MeasurableSpace Ω]
    {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {S : ℕ → Ω → ℤ}
    (hS : StronglyAdapted ℱ S) : IsStoppingTime ℱ (firstZero S) := by
  intro n
  have he : {ω | firstZero S ω ≤ WithTop.some n}=⋃ k ≤ n,{ω | S k ω=0} := by
    ext ω
    change (firstZero S ω ≤ WithTop.some n) ↔ _
    rw [firstZero_le_iff]
    simp
  change MeasurableSet[ℱ n] {ω | firstZero S ω ≤ WithTop.some n}
  rw [he]
  exact MeasurableSet.biUnion (Set.to_countable _) fun k hk =>
    measurableSet_eq_fun ((hS k).measurable.mono (ℱ.mono hk) le_rfl) measurable_const


lemma integer_path_nonneg_before_zero (S : ℕ → ℤ) (h₀ : 0 ≤ S 0)
    (hstep : ∀ n, S n-1 ≤ S (n+1)) (n : ℕ) (hn : ∀ k < n, S k≠0) : 0 ≤ S n := by
  induction n with
  | zero => exact h₀
  | succ n ih =>
    have hpos : 0 < S n := lt_of_le_of_ne (ih (fun k hk => hn k (by omega))) (Ne.symm (hn n (by omega)))
    have := hstep n
    omega


lemma martingale_stoppedProcess_real {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {f : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ}
    (hf : Martingale f ℱ μ) (hτ : IsStoppingTime ℱ τ) :
    Martingale (stoppedProcess f τ) ℱ μ := by
  apply martingale_iff.mpr
  constructor
  · have hh := (hf.neg.submartingale.stoppedProcess hτ).neg
    simpa using hh
  · exact hf.submartingale.stoppedProcess hτ


def integerSum (x : ℕ → ℕ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, ((x k : ℤ)-1)


@[simp] lemma integerSum_zero (x : ℕ → ℕ) : integerSum x 0=0 := by simp [integerSum]


@[simp] lemma integerSum_succ (x : ℕ → ℕ) (n : ℕ) :
    integerSum x (n+1)=integerSum x n+(x n:ℤ)-1 := by
  simp only [integerSum,Finset.sum_range_succ]
  ring


def reverseIndex (n k : ℕ) : ℕ := if k < n then n-1-k else k


def reverseFirst (n : ℕ) (x : ℕ → ℕ) : ℕ → ℕ := fun k => x (reverseIndex n k)


def negativeSurvival (x : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ k, 0 < k → k ≤ n → integerSum x k < 0


def firstHitBelow (x : ℕ → ℕ) (j n : ℕ) : Prop :=
  integerSum x n=-(j:ℤ) ∧ ∀ k, k < n → -(j:ℤ) < integerSum x k


def truncateStream (n : ℕ) (x : ℕ → ℕ) : ℕ → ℕ := fun k => if k<n then x k else 0


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_LadderRecords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

def weakLadderHit (x : ℕ → ℕ) (n k : ℕ) : Prop :=
  negativeSurvival x n ∧ integerSum x (n+1)=(k:ℤ)


def streamShift (n : ℕ) (x : ℕ → ℕ) : ℕ → ℕ := fun k => x (n+k)


def ladderPredicate (x : ℕ → ℕ) (n : ℕ) : Prop :=
  0 ≤ integerSum x (n+1) ∨ (¬ ∃ m, 0 ≤ integerSum x (m+1)) ∧ n=0


lemma ladderPredicate_exists (x : ℕ → ℕ) : ∃ n, ladderPredicate x n := by
  by_cases h : ∃ n, 0 ≤ integerSum x (n+1)
  · obtain ⟨n,hn⟩ := h
    exact ⟨n,Or.inl hn⟩
  · exact ⟨0,Or.inr ⟨h,rfl⟩⟩


def ladderIndex (x : ℕ → ℕ) : ℕ := by
  classical
  exact Nat.find (ladderPredicate_exists x)


def ladderOvershoot (x : ℕ → ℕ) : ℕ := (integerSum x (ladderIndex x+1)).toNat


def ladderTail (x : ℕ → ℕ) : ℕ → ℕ := streamShift (ladderIndex x+1) x


lemma regenerative_cylinder {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → β) (T : Ω → Ω)
    (hY : Measurable Y) (hT : MeasurePreserving T μ μ) (h : IndepFun Y T μ)
    (A : ℕ → Set β) (hA : ∀ i, MeasurableSet (A i)) (n : ℕ) :
    μ {x | ∀ i < n, Y (T^[i] x) ∈ A i} =
      ∏ i ∈ Finset.range n, μ (Y ⁻¹' A i) := by
  induction n generalizing A with
  | zero => simp
  | succ n ih =>
    let E : Set Ω := {x | ∀ i < n, Y (T^[i] x) ∈ A (i+1)}
    have hE : MeasurableSet E := by
      dsimp [E]
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun (_ : i < n) =>
        (hY.comp (hT.measurable.iterate i)) (hA (i+1))
    have he : {x | ∀ i < n+1, Y (T^[i] x) ∈ A i}=Y ⁻¹' A 0 ∩ T ⁻¹' E := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_preimage,E]
      constructor
      · intro hx
        refine ⟨by simpa using hx 0 (by omega),?_⟩
        intro i hi
        simpa only [Function.iterate_succ_apply] using hx (i+1) (by omega)
      · rintro ⟨h₀,hs⟩ i hi
        cases i with
        | zero => simpa using h₀
        | succ i => simpa only [Function.iterate_succ_apply] using hs i (by omega)
    rw [he,h.measure_inter_preimage_eq_mul _ _ (hA 0) hE,
      hT.measure_preimage hE.nullMeasurableSet,ih (fun i => A (i+1)) (fun i => hA (i+1)),
      Finset.prod_range_succ']
    exact mul_comm _ _


lemma regenerative_iIndepFun {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → β) (T : Ω → Ω)
    (hY : Measurable Y) (hT : MeasurePreserving T μ μ) (h : IndepFun Y T μ) :
    iIndepFun (fun i x => Y (T^[i] x)) μ := by
  classical
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S A hA
  let n := S.sup id+1
  have hsub : S ⊆ Finset.range n := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  let B : ℕ → Set β := fun i => if i ∈ S then A i else Set.univ
  have hB : ∀ i, MeasurableSet (B i) := by
    intro i
    dsimp [B]
    split_ifs with hi
    · exact hA i hi
    · exact MeasurableSet.univ
  have he : (⋂ i ∈ S, (fun x => Y (T^[i] x)) ⁻¹' A i) =
      {x | ∀ i < n, Y (T^[i] x) ∈ B i} := by
    ext x
    simp only [Set.mem_iInter,Set.mem_preimage,Set.mem_ofPred_eq]
    constructor
    · intro hx i _
      dsimp [B]
      split_ifs with hi
      · exact hx i hi
      · trivial
    · intro hx i hi
      simpa [B,hi] using hx i (Finset.mem_range.mp (hsub hi))
  rw [he,regenerative_cylinder μ Y T hY hT h B hB]
  calc
    ∏ i ∈ Finset.range n, μ (Y ⁻¹' B i) = ∏ i ∈ S, μ (Y ⁻¹' B i) := by
      symm
      apply Finset.prod_subset hsub
      intro i _ hi
      simp [B,hi]
    _ = ∏ i ∈ S, μ ((fun x => Y (T^[i] x)) ⁻¹' A i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [show B i=A i by simp [B,hi]]
      symm
      exact (hT.iterate i).measure_preimage (hY (hA i hi)).nullMeasurableSet


def renewalIncrement (i : ℕ) (x : ℕ → ℕ) : ℕ :=
  ladderOvershoot (ladderTail^[i] x)


def renewalCount (τ : ℕ → ℕ) (n : ℕ) : ℕ := Nat.findGreatest (fun r => τ r ≤ n) n


structure LadderEnumeration {α : Type*} [LinearOrder α] (S : ℕ → α) (τ : ℕ → ℕ) : Prop where
  zero : τ 0=0
  strictMono : StrictMono τ
  level_mono : Monotone (S ∘ τ)
  between : ∀ r k, τ r < k → k < τ (r+1) → S k < S (τ r)


def weakRecords {α : Type*} [LinearOrder α] (S : ℕ → α) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun k => ∀ j ≤ k, S j ≤ S k


@[simp] lemma mem_weakRecords {α : Type*} [LinearOrder α] (S : ℕ → α) (n k : ℕ) :
    k ∈ weakRecords S n ↔ 1 ≤ k ∧ k ≤ n ∧ ∀ j ≤ k, S j ≤ S k := by
  simp only [weakRecords,Finset.mem_filter,Finset.mem_Icc,and_assoc]


def ladderTime (x : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | r+1 => ladderTime x r+(ladderIndex (ladderTail^[r] x)+1)


@[simp] lemma ladderTime_zero (x : ℕ → ℕ) : ladderTime x 0=0 := rfl


def HasAllLadders (x : ℕ → ℕ) : Prop :=
  ∀ r, ∃ n k, weakLadderHit (ladderTail^[r] x) n k


def renewalLevel (r : ℕ) (x : ℕ → ℕ) : ℝ :=
  ∑ i ∈ Finset.range r,(renewalIncrement i x:ℝ)


def reverseRecords {α : Type*} [LinearOrder α] (S : ℕ → α) (a b : ℕ) : Finset ℕ :=
  (Finset.Ico a b).filter fun j => ∀ r, j ≤ r → r ≤ b → S j ≤ S r


def recordHeight {α : Type*} [LinearOrder α] (S : ℕ → α) (a b : ℕ) : ℕ :=
  (reverseRecords S a b).card


@[simp] lemma mem_reverseRecords {α : Type*} [LinearOrder α] (S : ℕ → α) (a b j : ℕ) :
    j ∈ reverseRecords S a b ↔ a ≤ j ∧ j < b ∧ ∀ r, j ≤ r → r ≤ b → S j ≤ S r := by
  simp only [reverseRecords, Finset.mem_filter, Finset.mem_Ico, and_assoc]


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_HeightCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

def reversedPath (S : ℕ → ℤ) (b k : ℕ) : ℤ := S b-S (b-k)


def heightModulusFailure (N m : ℕ) (d : ℝ) : Set (ℕ → ℕ) :=
  {x | ∃ a b, a ≤ b ∧ b ≤ N ∧
    (∀ u v, a ≤ u → u ≤ b → a ≤ v → v ≤ b →
      (integerSum x u:ℝ)-(integerSum x v:ℝ)<d) ∧
    ¬(recordHeight (integerSum x) 0 b ≤ recordHeight (integerSum x) 0 a+m ∧
      recordHeight (integerSum x) 0 a ≤ recordHeight (integerSum x) 0 b+m)}


def standardExcursion {Ω : Type} (B : Fin 3 → ℝ≥0 → Ω → ℝ) (ω : Ω)
    (t : unitInterval) : ℝ :=
  Real.sqrt (∑ i : Fin 3, (B i ⟨(t : ℝ), t.property.1⟩ ω -
    (t : ℝ) * B i 1 ω) ^ 2)


def circularReversePath (S : ℕ → ℤ) (N v k : ℕ) : ℤ :=
  if k ≤ v then S v-S (v-k) else S v-1-S (N+v-k)


def prefixMaximum (S : ℕ → ℤ) (N : ℕ) : ℤ :=
  (Finset.range (N+1)).sup' Finset.nonempty_range_add_one S


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_HeightBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

def streamPrefix (N : ℕ) (x : ℕ → ℕ) : Fin N → ℕ := fun i => x i.val

def arrayStream {N : ℕ} (d : Fin N → ℕ) : ℕ → ℕ :=
  fun k => if h:k<N then d ⟨k,h⟩ else 0

def recordError (ν : ℝ) (S : ℕ → ℤ) (k : ℕ) : ℝ :=
  |(prefixMaximum S k:ℝ)-ν*(weakRecords S k).card|

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_HeightTightness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

abbrev ClosePairs (δ : ℝ) := {st : unitInterval × unitInterval // dist st.1 st.2 ≤ δ}

instance instCompactSpaceClosePairs (δ : ℝ) : CompactSpace (ClosePairs δ) :=
  isCompact_iff_compactSpace.mp ((isClosed_le (continuous_fst.dist continuous_snd) continuous_const).isCompact)

def oscillationPath (δ : ℝ) (f : C(unitInterval,ℝ)) : C(ClosePairs δ,ℝ) :=
  ⟨fun st => f st.val.1-f st.val.2, by fun_prop⟩

def pathOscillation (δ : ℝ) (f : C(unitInterval,ℝ)) : ℝ := ‖oscillationPath δ f‖


local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_9 : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance instBorelSpaceContinuousMapElemRealUnitInterval_solutions_9 : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

def oscillationGauge (δ ε : ℝ) (f : C(unitInterval,ℝ)) := min 1 (pathOscillation δ f/ε)

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_10 : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance instBorelSpaceContinuousMapElemRealUnitInterval_solutions_10 : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
local instance instMeasurableSpaceContinuousMapElemRealUnitIntervalProd_solutions : MeasurableSpace C(unitInterval,ℝ×ℝ) := borel _
local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_12_rf86716_1 : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩
local instance instBorelSpaceContinuousMapElemRealUnitIntervalProd_solutions : BorelSpace C(unitInterval,ℝ×ℝ) := ⟨rfl⟩

def diagonalPath (f : C(unitInterval,ℝ)) : C(unitInterval,ℝ×ℝ) := f.prodMk f

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SimpleWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

/-- Exact probabilities for the symmetric nearest-neighbour walk on the integers. -/
def kernel : ℕ → ℤ → ℝ
  | 0,z => if z=0 then 1 else 0
  | n+1,z => (kernel n (z-1)+kernel n (z+1))/2

@[simp] lemma kernel_zero (z : ℤ) : kernel 0 z = if z=0 then 1 else 0 := rfl
lemma kernel_succ (n : ℕ) (z : ℤ) : kernel (n+1) z = (kernel n (z-1)+kernel n (z+1))/2 := rfl
lemma kernel_symm (n : ℕ) (z : ℤ) : kernel n (-z)=kernel n z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [kernel_succ,kernel_succ,show -z-1=-(z+1) by ring,show -z+1=-(z-1) by ring,ih,ih]
    ring
lemma kernel_nonneg (n : ℕ) (z : ℤ) : 0≤kernel n z := by
  induction n generalizing z with
  | zero => rw [kernel_zero]; split_ifs <;> norm_num
  | succ n ih => exact div_nonneg (add_nonneg (ih _) (ih _)) (by norm_num)

/-- Binomial coefficients extended by zero to negative lower arguments. -/
def chooseInt (n : ℕ) (k : ℤ) : ℝ := if 0≤k then (n.choose k.toNat:ℝ) else 0

lemma chooseInt_pascal (n : ℕ) (k : ℤ) :
    chooseInt (n+1) k=chooseInt n (k-1)+chooseInt n k := by
  by_cases hk : 0<k
  · have hk0 : 0≤k := by omega
    have hk1 : 0≤k-1 := by omega
    have he : k.toNat=(k-1).toNat+1 := by omega
    simp only [chooseInt,hk0,hk1,ite_true]
    rw [he,Nat.choose_succ_succ,Nat.cast_add]
  · by_cases hz : k=0
    · subst k; simp [chooseInt]
    · have hneg : ¬0≤k := by omega
      have hneg' : ¬0≤k-1 := by omega
      simp only [chooseInt,hneg,hneg',ite_false,add_zero]

lemma chooseInt_adjacent (n : ℕ) (k : ℤ) (hk : 0≤k) :
    ((k:ℝ)+1)*chooseInt n (k+1)=((n:ℝ)-k)*chooseInt n k := by
  have hc : (k+1).toNat=k.toNat+1 := by omega
  simp only [chooseInt,hk,show 0≤k+1 by omega,ite_true,hc]
  have hcast : (k.toNat:ℝ)=(k:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
  by_cases hn : k.toNat≤n
  · have he := congrArg (fun x : ℕ => (x:ℝ)) (Nat.choose_succ_right_eq n k.toNat)
    push_cast [Nat.cast_sub hn] at he
    rw [hcast] at he
    nlinarith
  · rw [Nat.choose_eq_zero_of_lt (by omega : n<k.toNat),
      Nat.choose_eq_zero_of_lt (by omega : n<k.toNat+1)]
    simp

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

def binaryMass (k : ℕ) : ℝ := (if k=0 then 1/2 else 0)+(if k=2 then 1/2 else 0)

lemma binaryMass_nonneg (k : ℕ) : 0≤binaryMass k := by
  unfold binaryMass; positivity
lemma binaryMass_total : HasSum binaryMass 1 := by
  change HasSum (fun k : ℕ => (if k=0 then (1/2:ℝ) else 0)+(if k=2 then 1/2 else 0)) 1
  convert (hasSum_ite_eq (0:ℕ) (1/2:ℝ)).add (hasSum_ite_eq (2:ℕ) (1/2:ℝ)) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma binaryMass_moment (r : ℕ) (hr : 0 < r) :
    HasSum (fun k : ℕ => (k:ℝ)^r*binaryMass k) ((2:ℝ)^r/2) := by
  have he : (fun k : ℕ => (k:ℝ)^r*binaryMass k)=
      (fun k : ℕ => if k=2 then (2:ℝ)^r/2 else 0) := by
    funext k
    by_cases h0 : k=0
    · subst k; simp [binaryMass,zero_pow (by omega : r≠0)]
    · by_cases h2 : k=2
      · subst k; simp [binaryMass,div_eq_mul_inv]
      · simp [binaryMass,h0,h2]
  rw [he]
  exact hasSum_ite_eq (2:ℕ) _

/-- Binary paths really sample critical, variance-one even offspring. -/
def binaryDegree (s : Bool) : ℕ := if s then 2 else 0

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

def arrayWalk {N : ℕ} (d : Fin N → ℕ) (k : ℕ) : ℤ :=
  ∑ i : Fin N, if i.val<k then ((d i:ℤ)-1) else 0

def ArrayGood {N : ℕ} (d : Fin N → ℕ) : Prop :=
  totalStep d= -1 ∧ ∀ k<N,0≤arrayWalk d k

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

def traceSize (R : ℕ) : List (ℕ×ℕ) → ℕ
  | [] => R
  | x::xs => x.1+traceSize R xs

end FKCRT.SimpleWalk
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_ExcursionKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

def located : List (ℕ×ℕ) → List (ℕ×ℕ)
  | [] => []
  | x::xs => x::(located xs).map (fun y => (x.1+y.1,y.2))

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

/-- Even grid time immediately below t, for the odd duration 2n+1. -/
def evenGrid (n : ℕ) (t : ℝ) : ℕ := 2*⌊((2*n+1:ℕ):ℝ)*t/2⌋₊

@[simp] lemma evenGrid_zero (n : ℕ) : evenGrid n 0=0 := by simp [evenGrid]

/-- Successive durations at a deterministic increasing list of observation times. -/
def gridDurations {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ) (i : Fin m) : ℕ :=
  evenGrid n (u i.succ)-evenGrid n (u i.castSucc)

def gridRemainder {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ) : ℕ :=
  2*n-evenGrid n (u (Fin.last m))

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
open TreeCoding

/-- The heat density for one-dimensional standard Brownian motion. -/
def heat (t x : ℝ) : ℝ := Real.exp (-x^2/(2*t))/Real.sqrt (2*Real.pi*t)

lemma heat_pos {t : ℝ} (ht : 0<t) (x : ℝ) : 0<heat t x := by
  exact div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (by positivity))

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

/-- The killed heat kernel obtained from the proved discrete reflection principle. -/
def killedHeat (t x y : ℝ) : ℝ := heat t (y-x)-heat t (y+x)

end FKCRT.SimpleWalk
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_InventoryStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def typeSign (b : Bool) : ℤ := if b then 1 else -1
lemma typeSign_not (b : Bool) : typeSign (!b)= -typeSign b := by cases b <;> norm_num [typeSign]
lemma abs_typeSign (b : Bool) : |typeSign b|=1 := by cases b <;> norm_num [typeSign]
lemma typeSign_sq (b : Bool) : typeSign b^2=1 := by cases b <;> norm_num [typeSign]

lemma sum_typeSign_abs_le (l : List Bool) : |(l.map typeSign).sum| ≤ l.length := by
  induction l with
  | nil => simp
  | cons b bs ih =>
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,abs_typeSign,add_comm]
      using (abs_add_le (typeSign b) (bs.map typeSign).sum).trans (add_le_add (le_of_eq (abs_typeSign b)) ih)

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MapCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cut/join identities for tour permutations. Fixed points are retained as
one-element cycles, as required by the Euler-characteristic map definition. -/


noncomputable section
open Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] in
lemma sameCycle_mono {p q : Perm α}
    (h : ∀ x,q.SameCycle x (p x)) {x y : α} (hxy : p.SameCycle x y) : q.SameCycle x y := by
  obtain ⟨n,rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => simpa using SameCycle.refl q x
  | succ n ih =>
    rw [pow_succ',mul_apply]
    exact ih.trans (h _)

def JoinRel (p : Perm α) (a b x y : α) : Prop :=
  p.SameCycle x y ∨
    ((p.SameCycle x a ∨ p.SameCycle x b) ∧ (p.SameCycle y a ∨ p.SameCycle y b))

omit [DecidableEq α] [Fintype α] in
lemma JoinRel.refl (p : Perm α) (a b x : α) : JoinRel p a b x x :=
  Or.inl (SameCycle.refl p x)

omit [DecidableEq α] [Fintype α] in
lemma JoinRel.trans {p : Perm α} {a b x y z : α}
    (h : JoinRel p a b x y) (h' : JoinRel p a b y z) : JoinRel p a b x z := by
  rcases h with h|⟨hx,hy⟩
  · rcases h' with h'|⟨hy,hz⟩
    · exact Or.inl (h.trans h')
    · exact Or.inr ⟨hy.imp (h.trans) (h.trans),hz⟩
  · rcases h' with h'|⟨_,hz⟩
    · exact Or.inr ⟨hx,hy.imp (h'.symm.trans) (h'.symm.trans)⟩
    · exact Or.inr ⟨hx,hz⟩

omit [Fintype α] in
lemma JoinRel.step (p : Perm α) (a b x : α) : JoinRel p a b x ((swap a b*p) x) := by
  have hx : p.SameCycle x (p x) := sameCycle_apply_right.mpr (SameCycle.refl p x)
  by_cases ha : p x=a
  · rw [mul_apply,ha,swap_apply_left]
    exact Or.inr ⟨Or.inl (ha ▸ hx),Or.inr (SameCycle.refl p b)⟩
  · by_cases hb : p x=b
    · rw [mul_apply,hb,swap_apply_right]
      exact Or.inr ⟨Or.inr (hb ▸ hx),Or.inl (SameCycle.refl p a)⟩
    · rw [mul_apply,swap_apply_of_ne_of_ne ha hb]
      exact Or.inl hx

end FKCRT.MapCycles
end


noncomputable section
open Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] in
lemma sameCycle_partition {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) {x y : α} (hxy : p.SameCycle x y) : x∈S ↔ y∈S := by
  obtain ⟨n,rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => simp
  | succ n ih => simpa only [pow_succ',mul_apply,hp] using ih

omit [DecidableEq α] in
lemma not_sameCycle_partition {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) {a b : α} (ha : a∈S) (hb : b∉S) : ¬p.SameCycle a b :=
  fun h => hb ((sameCycle_partition hp h).mp ha)

omit [Fintype α] in
lemma formPerm_other_mem_iff {l r : List α} (hd : l.Disjoint r) (x : α) :
    r.formPerm x∈l ↔ x∈l := by
  by_cases hx : x∈l
  · have hxr : x∉r := fun h => List.disjoint_left.mp hd hx h
    simp only [List.formPerm_apply_of_notMem hxr]
  · constructor
    · intro h
      have hxr : r.formPerm x∉r := fun hr => List.disjoint_left.mp hd h hr
      have he : r.formPerm x=x := List.formPerm_apply_of_notMem
        (fun hr => hxr (r.formPerm_apply_mem_of_mem hr))
      exact he ▸ h
    · exact False.elim ∘ hx

end FKCRT.MapCycles
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_GraphWedge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Equiv Equiv.Perm
namespace FKCRT.PermutationWedge
open MapCycles
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α] [Fintype α]

def sideSetoid (p : Perm α) (S : Set α) : Setoid S where
  r x y := p.SameCycle x.val y.val
  iseqv := ⟨fun x => SameCycle.refl p x.val,fun h => h.symm,fun h h' => h.trans h'⟩

abbrev Side (p : Perm α) (S : Set α) := Quotient (sideSetoid p S)
def sideMk (p : Perm α) (S : Set α) (d : α) (hd : d∈S) : Side p S := Quotient.mk _ ⟨d,hd⟩

def sideGraph (e p : Perm α) (S : Set α) (he : ∀ d,e d∈S ↔ d∈S) : SimpleGraph (Side p S) :=
  SimpleGraph.fromRel (fun v w => ∃ d,∃ hd : d∈S,sideMk p S d hd=v ∧ sideMk p S (e d) ((he d).mpr hd)=w)

variable {p e : Perm α} {S : Set α} {a b : α}
variable (hp : ∀ d,p d∈S ↔ d∈S) (ha : a∈S) (hb : b∉S)

/- The maps below operate on the actual rotation-cycle quotients. -/

def retractD (d : α) : Side p S :=
  if hd : d∈S then sideMk p S d hd else sideMk p S a ha

def flipRetractD (d : α) : Side p Sᶜ :=
  if hd : d∈Sᶜ then sideMk p Sᶜ d hd else sideMk p Sᶜ b hb

end FKCRT.PermutationWedge
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_ExcursionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal

namespace FKCRT

lemma interval_image_bddBelow {e : unitInterval → ℝ} (he : Continuous e)
    (s t : unitInterval) : BddBelow (e '' Set.uIcc s t) :=
  (isCompact_uIcc.image he).bddBelow

lemma interval_inf_le_left {e : unitInterval → ℝ} (he : Continuous e)
    (s t : unitInterval) : sInf (e '' Set.uIcc s t) ≤ e s :=
  csInf_le (interval_image_bddBelow he s t) (mem_image_of_mem e left_mem_uIcc)

lemma interval_inf_le_right {e : unitInterval → ℝ} (he : Continuous e)
    (s t : unitInterval) : sInf (e '' Set.uIcc s t) ≤ e t :=
  csInf_le (interval_image_bddBelow he s t) (mem_image_of_mem e right_mem_uIcc)

lemma excursionDist_self (e : unitInterval → ℝ) (s : unitInterval) :
    excursionDist e s s = 0 := by
  simp [excursionDist, two_mul]

lemma excursionDist_comm (e : unitInterval → ℝ) (s t : unitInterval) :
    excursionDist e s t = excursionDist e t s := by
  simp only [excursionDist, uIcc_comm t s]
  ring

lemma interval_inf_ge_min {e : unitInterval → ℝ} (he : Continuous e)
    (s t u : unitInterval) :
    min (sInf (e '' Set.uIcc s t)) (sInf (e '' Set.uIcc t u)) ≤
      sInf (e '' Set.uIcc s u) := by
  apply le_csInf (nonempty_uIcc.image e)
  rintro _ ⟨v, hv, rfl⟩
  rcases uIcc_subset_uIcc_union_uIcc hv with h | h
  · exact (min_le_left _ _).trans
      (csInf_le (interval_image_bddBelow he s t) (mem_image_of_mem e h))
  · exact (min_le_right _ _).trans
      (csInf_le (interval_image_bddBelow he t u) (mem_image_of_mem e h))

lemma excursionDist_triangle {e : unitInterval → ℝ} (he : Continuous e)
    (s t u : unitInterval) :
    excursionDist e s u ≤ excursionDist e s t + excursionDist e t u := by
  have h1 := interval_inf_le_right he s t
  have h2 := interval_inf_le_left he t u
  have h3 := interval_inf_ge_min he s t u
  dsimp [excursionDist, two_mul]
  rcases le_total (sInf (e '' Set.uIcc s t)) (sInf (e '' Set.uIcc t u)) with h | h
  · rw [min_eq_left h] at h3
    linarith
  · rw [min_eq_right h] at h3
    linarith

/-- The excursion quotient, with the genuine induced metric. -/
@[instance_reducible]
def excursionTreeMetric {e : unitInterval → ℝ} (he : Continuous e) :
    MetricSpace (ExcursionTree e) where
  dist x y := excursionDist e x.out y.out
  dist_self x := excursionDist_self e x.out
  dist_comm x y := excursionDist_comm e x.out y.out
  dist_triangle x y z := excursionDist_triangle he x.out y.out z.out
  eq_of_dist_eq_zero {x y} h := by
    rw [← x.out_eq, ← y.out_eq]
    exact Quotient.sound (Relation.EqvGen.rel _ _ h)


lemma graph_connected {n : ℕ} (M : RootedMap n) : (graph M univ).Connected :=
  M.out.property.2.2.1

@[instance_reducible]
def mapMetric {n : ℕ} {scale : ℝ} (hscale : 0 < scale) (M : RootedMap n) :
    MetricSpace (Vertex M) where
  dist v w := scale * ((graph M univ).dist v w : ℝ)
  dist_self v := by simp
  dist_comm v w := by rw [SimpleGraph.dist_comm]
  dist_triangle v w z := by
    have h := (graph_connected M).dist_triangle (u := v) (v := w) (w := z)
    have h' : ((graph M univ).dist v z : ℝ) ≤
        ((graph M univ).dist v w : ℝ) + ((graph M univ).dist w z : ℝ) := by exact_mod_cast h
    simpa only [mul_add] using mul_le_mul_of_nonneg_left h' hscale.le
  eq_of_dist_eq_zero {v w} h := by
    have hdist : (graph M univ).dist v w = 0 := by
      exact_mod_cast (mul_eq_zero.mp h).resolve_left hscale.ne'
    exact (graph_connected M).dist_eq_zero_iff.mp hdist

end FKCRT
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MapEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT

lemma MapIso.refl {n : ℕ} (M : LabelledMap n) : MapIso M M :=
  ⟨Equiv.refl _,rfl,fun _ => rfl,fun _ => rfl⟩

lemma MapIso.symm {n : ℕ} {M N : LabelledMap n} (h : MapIso M N) : MapIso N M := by
  obtain ⟨r,h₀,ha,hs⟩ := h
  refine ⟨r.symm,?_,?_,?_⟩
  · exact (r.symm_apply_eq).2 h₀.symm
  · intro d
    apply r.injective
    simpa using (ha (r.symm d)).symm
  · intro d
    apply r.injective
    simpa using (hs (r.symm d)).symm

lemma MapIso.trans {n : ℕ} {M N K : LabelledMap n} (h : MapIso M N) (h' : MapIso N K) :
    MapIso M K := by
  obtain ⟨r,hr,ha,hs⟩ := h
  obtain ⟨r',hr',ha',hs'⟩ := h'
  refine ⟨r.trans r',?_,?_,?_⟩
  · simp [hr,hr']
  · intro d
    simp only [Equiv.trans_apply,ha',ha]
  · intro d
    simp only [Equiv.trans_apply,hs',hs]

lemma mapIso_eqvGen {n : ℕ} {M N : LabelledMap n} :
    Relation.EqvGen MapIso M N ↔ MapIso M N := by
  constructor
  · intro h
    induction h with
    | rel _ _ he => exact he
    | refl M => exact MapIso.refl M
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
  · exact Relation.EqvGen.rel _ _

end FKCRT
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT

def pathRotation (n : ℕ) : Equiv.Perm (Dart n) := finRotate (2*(n+1))*Fin.revPerm

lemma rotate_sameCycle (n : ℕ) (d e : Dart n) : (finRotate (2*(n+1))).SameCycle d e := by
  apply (isCycle_finRotate_of_le (by omega : 2≤2*(n+1))).sameCycle
  · apply Equiv.Perm.mem_support.mp
    rw [support_finRotate_of_le (by omega : 2≤2*(n+1))]
    exact Finset.mem_univ _
  · apply Equiv.Perm.mem_support.mp
    rw [support_finRotate_of_le (by omega : 2≤2*(n+1))]
    exact Finset.mem_univ _

lemma pathRotation_face (n : ℕ) : pathRotation n*Fin.revPerm=finRotate (2*(n+1)) := by
  ext d
  simp only [pathRotation,Equiv.Perm.mul_apply,Fin.revPerm_apply,Fin.rev_rev]

lemma rotate_orbits (n : ℕ) : Nat.card (Orbit (finRotate (2*(n+1))))=1 := by
  have : Subsingleton (Orbit (finRotate (2*(n+1)))) := ⟨fun v w => by
    induction v using Quotient.inductionOn with | h d =>
      induction w using Quotient.inductionOn with | h e =>
        exact Quotient.sound (rotate_sameCycle n d e)⟩
  have : Nonempty (Orbit (finRotate (2*(n+1)))) := ⟨orbit _ 0⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩

end FKCRT
end



/-! The exact edge-reversal tour of the rotation-system maps. -/


noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

/-- An edge's unordered endpoints; representatives do not change this pair. -/
def edgeEnds (a s : Perm (Dart n)) (e : Orbit a) : Sym2 (Orbit s) :=
  s(orbit s e.out, orbit s (a e.out))

end FKCRT
end



/-! A genuine multigraph spanning tree has one complete edge-reversal tour.
This is the converse direction of the source's finite encoding, proved
without invoking a topological thickening or assuming planarity. -/



/-! Exact reconstruction in the rotation-system convention. The
Euler equalities on the two coloured matchings are equivalent to their
noncrossing property; maximum orbit counts are proved for stack matchings
in `WorkNoncrossing`, rather than postulated for a map. -/

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_Matching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
variable {N : ℕ}

def liveAt (a : Perm (Fin N)) (k : ℕ) : List (Fin N) :=
  ((List.finRange N).filter (fun x => decide (x.val<k ∧ k≤(a x).val))).reverse

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CoreCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Equiv Equiv.Perm
namespace FKCRT.PermutationWedge
variable {α : Type*} [Fintype α]
attribute [local instance] Classical.propDecidable

lemma sameCycle_congr_on {p q : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (_hq : ∀ d,q d∈S ↔ d∈S)
    (he : ∀ d∈S,p d=q d) {x y : α} (hx : x∈S) :
    p.SameCycle x y ↔ q.SameCycle x y := by
  have hpow : ∀ n : ℕ,(p^n) x=(q^n) x ∧ (p^n) x∈S := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      simp only [pow_succ',mul_apply]
      exact ⟨(he _ ih.2).trans (congrArg q ih.1),(hp _).mpr ih.2⟩
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n:ℤ),by simpa only [zpow_natCast] using (hpow n).1.symm.trans hn⟩
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n:ℤ),by simpa only [zpow_natCast] using (hpow n).1.trans hn⟩

/-- Changing the ambient permutation off a retained invariant dart set does
not change its actual rotation vertices. -/
def sideCongr {p q : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (hq : ∀ d,q d∈S ↔ d∈S)
    (he : ∀ d∈S,p d=q d) : Side p S ≃ Side q S :=
  Quotient.congrRight (fun x _ => sameCycle_congr_on hp hq he x.property)

lemma sideCongr_mk {p q : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (hq : ∀ d,q d∈S ↔ d∈S)
    (he : ∀ d∈S,p d=q d) (d : α) (hd : d∈S) :
    sideCongr hp hq he (sideMk p S d hd)=sideMk q S d hd := rfl

/-- The all-edge graph is invariant under restriction/normalization on a
closed set of darts; only the two literal permutation actions are used. -/
def sideGraphCongr {p q e f : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (hq : ∀ d,q d∈S ↔ d∈S)
    (he : ∀ d,e d∈S ↔ d∈S) (hf : ∀ d,f d∈S ↔ d∈S)
    (hpq : ∀ d∈S,p d=q d) (hef : ∀ d∈S,e d=f d) :
    sideGraph e p S he ≃g sideGraph f q S hf where
  toEquiv := sideCongr hp hq hpq
  map_rel_iff' := by
    intro x y
    constructor
    · rintro ⟨hne,h⟩
      refine ⟨fun h => hne (congrArg (sideCongr hp hq hpq) h),?_⟩
      have transport (x y : Side p S) (d : α) (hd : d∈S)
          (hx : sideMk q S d hd=sideCongr hp hq hpq x)
          (hy : sideMk q S (f d) ((hf d).mpr hd)=sideCongr hp hq hpq y) :
          ∃ d,∃ hd : d∈S,sideMk p S d hd=x ∧ sideMk p S (e d) ((he d).mpr hd)=y := by
        refine ⟨d,hd,(sideCongr hp hq hpq).injective hx,?_⟩
        apply (sideCongr hp hq hpq).injective
        rw [sideCongr_mk]
        simpa only [hef d hd] using hy
      rcases h with ⟨d,hd,hx,hy⟩|⟨d,hd,hy,hx⟩
      · exact Or.inl (transport x y d hd hx hy)
      · exact Or.inr (transport y x d hd hy hx)
    · rintro ⟨hne,h⟩
      refine ⟨fun h => hne ((sideCongr hp hq hpq).injective h),?_⟩
      have transport (x y : Side p S) (d : α) (hd : d∈S)
          (hx : sideMk p S d hd=x) (hy : sideMk p S (e d) ((he d).mpr hd)=y) :
          ∃ d,∃ hd : d∈S,sideMk q S d hd=sideCongr hp hq hpq x ∧
            sideMk q S (f d) ((hf d).mpr hd)=sideCongr hp hq hpq y := by
        refine ⟨d,hd,congrArg (sideCongr hp hq hpq) hx,?_⟩
        have hh := congrArg (sideCongr hp hq hpq) hy
        simpa only [sideCongr_mk,hef d hd] using hh
      rcases h with ⟨d,hd,hx,hy⟩|⟨d,hd,hy,hx⟩
      · exact Or.inl (transport x y d hd hx hy)
      · exact Or.inr (transport y x d hd hy hx)

end FKCRT.PermutationWedge
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
lemma filter_delete_interval (u v z : List α) (hn : (u++(v++z)).Nodup) :
    (u++(v++z)).filter (fun d => decide (d∉v))=u++z := by
  have hu : u.Disjoint v := List.disjoint_iff_ne.mpr (fun x hx y hy he =>
    (List.nodup_append.mp hn).2.2 x hx y (List.mem_append_left _ hy) he)
  have hz : v.Disjoint z := List.disjoint_iff_ne.mpr
    (List.nodup_append.mp (List.nodup_append.mp hn).2.1).2.2
  simp only [List.filter_append]
  have hfU : u.filter (fun d => decide (d∉v))=u := by
    apply List.filter_eq_self.mpr
    intro d hd
    exact decide_eq_true (fun h => List.disjoint_left.mp hu hd h)
  have hfV : v.filter (fun d => decide (d∉v))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hd
    simp [hd]
  have hfZ : z.filter (fun d => decide (d∉v))=z := by
    apply List.filter_eq_self.mpr
    intro d hd
    exact decide_eq_true (fun h => List.disjoint_left.mp hz h hd)
  rw [hfU,hfV,hfZ,List.nil_append]

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
lemma complement_disjoint_interval (u v z : List α) (hn : (u++(v++z)).Nodup) :
    (u++z).Disjoint v := by
  apply List.disjoint_append_left.mpr
  constructor
  · apply List.disjoint_iff_ne.mpr
    intro x hx y hy h
    exact (List.nodup_append.mp hn).2.2 x hx y (List.mem_append_left _ hy) h
  · exact (List.disjoint_iff_ne.mpr
      (List.nodup_append.mp (List.nodup_append.mp hn).2.1).2.2).symm

/-- Literal dart order for all successive corner insertions. -/
def dartInsert (l : List (α×List α)) : List α := l.flatMap fun p => p.1::p.2

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
lemma filter_keep_interval (u v z : List α) (hn : (u++(v++z)).Nodup) :
    (u++(v++z)).filter (fun d => decide (d∈v))=v := by
  have hd := complement_disjoint_interval u v z hn
  rw [List.filter_append,List.filter_append]
  have hu : u.filter (fun d => decide (d∈v))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hm
    simp only [decide_eq_true_eq]
    exact fun h => List.disjoint_left.mp hd (List.mem_append_left _ hm) h
  have hz : z.filter (fun d => decide (d∈v))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hm
    simp only [decide_eq_true_eq]
    exact fun h => List.disjoint_left.mp hd (List.mem_append_right _ hm) h
  have hv : v.filter (fun d => decide (d∈v))=v := by
    apply List.filter_eq_self.mpr
    intro d hd
    exact decide_eq_true hd
  rw [hu,hv,hz,List.nil_append,List.append_nil]

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CoreWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α] [Fintype β]

omit [Fintype α] [Fintype β] in
lemma perm_preserves_range (f : α → β) {p : Perm α} {q : Perm β}
    (h : ∀ x,q (f x)=f (p x)) (y : β) : q y∈Set.range f ↔ y∈Set.range f := by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨p⁻¹ x,q.injective ?_⟩
    rw [h]
    simpa using hx
  · rintro ⟨x,rfl⟩
    exact ⟨p x,(h x).symm⟩

omit [Fintype α] [Fintype β] in
lemma pow_intertwine (f : α → β) {p : Perm α} {q : Perm β}
    (h : ∀ x,q (f x)=f (p x)) (n : ℕ) (x : α) : (q^n) (f x)=f ((p^n) x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',pow_succ',mul_apply,mul_apply,ih,h]

lemma sameCycle_embedding (f : α → β) (hf : Function.Injective f)
    {p : Perm α} {q : Perm β} (h : ∀ x,q (f x)=f (p x)) (x y : α) :
    p.SameCycle x y ↔ q.SameCycle (f x) (f y) := by
  constructor
  · intro hh
    obtain ⟨n,hn⟩ := hh.exists_nat_pow_eq
    exact ⟨(n:ℤ),by rw [zpow_natCast,pow_intertwine f h,hn]⟩
  · intro hh
    obtain ⟨n,hn⟩ := hh.exists_nat_pow_eq
    exact ⟨(n:ℤ),by simpa only [zpow_natCast] using hf ((pow_intertwine f h n x).symm.trans hn)⟩

end FKCRT.PermutationWedge
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PlaneTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

/-- Ordered rooted trees; the empty child list is an actual leaf. -/
inductive PlaneTree where
  | node : List PlaneTree → PlaneTree

noncomputable instance instDecidableEqPlaneTree : DecidableEq PlaneTree := Classical.decEq _
namespace PlaneTree

@[elab_as_elim] theorem inductionMem {P : PlaneTree → Prop}
    (hn : ∀ ts, (∀ t ∈ ts, P t) → P (node ts)) (t : PlaneTree) : P t :=
  PlaneTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ t ∈ ts, P t)
    hn (by simp) (by intro t ts ht hts t' ht'; rcases List.mem_cons.mp ht' with rfl | ht'; exact ht; exact hts _ ht') t

def degrees : PlaneTree → List ℕ
  | node ts => ts.length :: ts.flatMap degrees

def forestDegrees (ts : List PlaneTree) : List ℕ := ts.flatMap degrees

def build : List ℕ → List PlaneTree → List PlaneTree
  | [],ts => ts
  | k::l,ts => let fs := build l ts; node (fs.take k)::fs.drop k

lemma build_append (l l' : List ℕ) (ts : List PlaneTree) :
    build (l++l') ts=build l (build l' ts) := by
  induction l with
  | nil => rfl
  | cons k l ih => simp only [List.cons_append,build,ih]

lemma build_degrees (t : PlaneTree) (ts : List PlaneTree) : build t.degrees ts=t::ts := by
  induction t using inductionMem generalizing ts with
  | hn fs ih =>
    have hf : ∀ (fs' : List PlaneTree), (∀ f∈fs',∀ ts,build f.degrees ts=f::ts) →
        ∀ ts,build (fs'.flatMap degrees) ts=fs'++ts := by
      intro fs' hf ts
      induction fs' with
      | nil => rfl
      | cons f fs' ih' =>
        rw [List.flatMap_cons,build_append,hf f (by simp),ih' (by aesop)]
        rfl
    rw [degrees,build,hf fs (by exact ih)]
    simp

lemma degrees_injective : Function.Injective degrees := by
  intro t t' h
  have hh := congrArg (fun l => build l []) h
  simpa only [build_degrees,List.cons.injEq,and_true] using hh

def incrementWord (l : List ℕ) : List ℤ := l.map (fun k : ℕ => (k:ℤ)-1)

def SuffixNegative (l : List ℕ) : Prop := ∀ j<l.length,(incrementWord (l.drop j)).sum<0

lemma suffixNegative_tail {k : ℕ} {l : List ℕ} (h : SuffixNegative (k::l)) : SuffixNegative l := by
  intro j hj
  simpa only [List.drop_succ_cons] using h (j+1) (by simpa using hj)

lemma build_correct {l : List ℕ} (h : SuffixNegative l) :
    forestDegrees (build l [])=l ∧ ((build l []).length:ℤ)= -(incrementWord l).sum := by
  induction l with
  | nil => simp [build,forestDegrees,incrementWord]
  | cons k l ih =>
    obtain ⟨he,hlen⟩ := ih (suffixNegative_tail h)
    have hneg := h 0 (by simp)
    simp only [List.drop_zero,incrementWord,List.map_cons,List.sum_cons] at hneg
    have hk : k≤(build l []).length := by
      change ((build l []).length:ℤ)= -(incrementWord l).sum at hlen
      unfold incrementWord at hlen
      omega
    constructor
    · simp only [build, forestDegrees, List.flatMap_cons, degrees, List.cons_append]
      change ((List.take k (build l [])).length)::
        (forestDegrees (List.take k (build l []))++forestDegrees (List.drop k (build l [])))=k::l
      rw [List.length_take,Nat.min_eq_left hk]
      rw [forestDegrees, forestDegrees, ← List.flatMap_append, List.take_append_drop]
      exact congrArg (List.cons k) he
    · simp only [build,List.length_cons,List.length_drop,incrementWord,List.map_cons,List.sum_cons]
      rw [Nat.cast_add, Nat.cast_sub hk]
      simp only [Nat.cast_one]
      unfold incrementWord at hlen
      omega

lemma suffixNegative_of_excursion {l : List ℕ} (h : IsExcursionList (incrementWord l)) :
    SuffixNegative l := by
  intro j hj
  have hp := h.2 j (by simpa [incrementWord] using hj)
  have hh : (incrementWord (l.drop j)).sum=(incrementWord l).sum-prefixSum (incrementWord l) j := by
    rw [incrementWord,List.map_drop,sum_drop]
    rfl
  rw [hh,h.1]
  omega

lemma exists_tree_of_excursion {l : List ℕ} (h : IsExcursionList (incrementWord l)) :
    ∃ t : PlaneTree,t.degrees=l := by
  obtain ⟨he,hlen⟩ := build_correct (suffixNegative_of_excursion h)
  rw [h.1] at hlen
  have hlen' : (build l []).length=1 := by omega
  obtain ⟨t,ht⟩ := List.length_eq_one_iff.mp hlen'
  exact ⟨t,by simpa [ht,forestDegrees] using he⟩

/-- Reversal of all child orders, without imposing any symmetry on marks. -/
def mirror : PlaneTree → PlaneTree
  | node ts => node (ts.reverse.map mirror)

lemma mirror_mirror (t : PlaneTree) : t.mirror.mirror=t := by
  induction t using inductionMem with
  | hn ts ih =>
    simp only [mirror,List.map_reverse,List.reverse_reverse,List.map_map]
    congr 1
    apply Eq.trans ?_ (List.map_id' _)
    apply List.map_congr_left
    intro t ht
    exact ih t ht

lemma incrementWord_append (l l' : List ℕ) :
    incrementWord (l++l')=incrementWord l++incrementWord l' := by
  simp [incrementWord]

lemma suffixNegative_append {l l' : List ℕ} (h : SuffixNegative l)
    (h' : SuffixNegative l') (hs : (incrementWord l').sum≤0) : SuffixNegative (l++l') := by
  intro j hj
  by_cases hja : j<l.length
  · rw [List.drop_append_of_le_length (Nat.le_of_lt hja),incrementWord_append,List.sum_append]
    exact add_lt_of_lt_of_nonpos (h j hja) hs
  · rw [List.drop_append,List.drop_eq_nil_of_le (by omega : l.length≤j),List.nil_append]
    exact h' (j-l.length) (by simp only [List.length_append] at hj; omega)

lemma degrees_properties (t : PlaneTree) :
    (incrementWord t.degrees).sum= -1 ∧ SuffixNegative t.degrees := by
  induction t using inductionMem with
  | hn ts ih =>
    have hf : ∀ fs : List PlaneTree,
        (∀ f ∈ fs, (incrementWord f.degrees).sum= -1 ∧ SuffixNegative f.degrees) →
        (incrementWord (forestDegrees fs)).sum= -(fs.length:ℤ) ∧
          SuffixNegative (forestDegrees fs) := by
      intro fs hfs
      induction fs with
      | nil => simp [forestDegrees,incrementWord,SuffixNegative]
      | cons f fs ih' =>
        have hp := hfs f (by simp)
        obtain ⟨hs,hn⟩ := ih' (by intro f hf; exact hfs f (by simp [hf]))
        have he : forestDegrees (f::fs)=f.degrees++forestDegrees fs := by simp [forestDegrees]
        rw [he]
        constructor
        · rw [incrementWord_append,List.sum_append,hp.1,hs]
          simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
          omega
        · exact suffixNegative_append hp.2 hn (by rw [hs]; omega)
    obtain ⟨hs,hn⟩ := hf ts ih
    have hsum : (incrementWord (node ts).degrees).sum= -1 := by
      rw [degrees]
      change (incrementWord (ts.length::forestDegrees ts)).sum= -1
      simp only [incrementWord,List.map_cons,List.sum_cons]
      change (ts.length:ℤ)-1+(incrementWord (forestDegrees ts)).sum= -1
      rw [hs]; omega
    exact ⟨hsum,fun j hj => by
      cases j with
      | zero => simpa only [List.drop_zero,hsum] using (by norm_num : (-1:ℤ)<0)
      | succ j =>
        simpa only [degrees,List.drop_succ_cons,forestDegrees] using
          hn j (by simpa only [degrees,List.length_cons,Nat.succ_lt_succ_iff,forestDegrees] using hj)⟩

lemma degrees_excursion (t : PlaneTree) : IsExcursionList (incrementWord t.degrees) := by
  obtain ⟨hs,hn⟩ := degrees_properties t
  refine ⟨hs,fun j hj => ?_⟩
  have hneg := hn j (by simpa [incrementWord] using hj)
  have he : (incrementWord (t.degrees.drop j)).sum =
      (incrementWord t.degrees).sum-prefixSum (incrementWord t.degrees) j := by
    rw [incrementWord,List.map_drop,sum_drop]; rfl
  rw [he,hs] at hneg
  omega

lemma mirror_degrees_perm (t : PlaneTree) : t.mirror.degrees.Perm t.degrees := by
  induction t using inductionMem with
  | hn ts ih =>
    simp only [mirror,degrees,List.length_map,List.length_reverse]
    apply List.Perm.cons
    rw [List.flatMap_map]
    exact (List.reverse_perm ts).flatMap (fun t ht => ih t (by simpa using ht))

lemma mirror_size (t : PlaneTree) : t.mirror.degrees.length=t.degrees.length :=
  t.mirror_degrees_perm.length_eq

end PlaneTree
end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_WordCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT
namespace TreeCoding

lemma firstZero_eq_iff {Ω : Type*} (S : ℕ → Ω → ℤ) (x : Ω) (n : ℕ) :
    firstZero S x=WithTop.some n ↔ S n x=0 ∧ ∀ j<n,S j x≠0 := by
  classical
  unfold firstZero
  split_ifs with h
  · rw [WithTop.coe_inj]
    exact Nat.find_eq_iff h
  · simp only [WithTop.top_ne_coe,false_iff,not_and]
    intro hn
    exact (h ⟨n,hn⟩).elim

end TreeCoding
end FKCRT
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PieceWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma sum_difference_shift_le (f : ℕ → ℝ) (hf : ∀ j,0≤f j) (d N : ℕ) :
    (∑ j∈Finset.range N,(f j-f (j+d))) ≤ ∑ j∈Finset.range d,f j := by
  have h1 := Finset.sum_range_add f N d
  have h2 := Finset.sum_range_add f d N
  have ht : (∑ j∈Finset.range N,f j)+(∑ j∈Finset.range d,f (j+N))=
      (∑ j∈Finset.range d,f j)+(∑ j∈Finset.range N,f (j+d)) := by
    rw [Nat.add_comm N d] at h1
    simpa only [Nat.add_comm] using h1.symm.trans h2
  have hp : 0≤∑ j∈Finset.range d,f (j+N) := Finset.sum_nonneg (fun _ _ => hf _)
  rw [Finset.sum_sub_distrib]
  linarith

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def bottom {α : Type*} (s : List α) (k : ℕ) : List α := s.drop (s.length-k)
lemma bottom_cons {α : Type*} (b : α) (s : List α) {k : ℕ} (hk : k ≤ s.length) :
    bottom (b::s) k=bottom s k := by
  unfold bottom
  have he : (b::s).length-k=(s.length-k)+1 := by simp only [List.length_cons]; omega
  rw [he,List.drop_succ_cons]
lemma bottom_all {α : Type*} (s : List α) : bottom s s.length=s := by simp [bottom]
lemma count_bottom_le (s : List Bool) (k : ℕ) (a : Bool) : (bottom s k).count a ≤ s.count a :=
  List.Sublist.count_le a (List.drop_sublist _ _)

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma term_div_zero_of_averages {a : ℕ → ℝ} {l : ℝ}
    (h : Tendsto (fun n => (∑ i∈Finset.range n,a i)/(n:ℝ)) atTop (𝓝 l)) :
    Tendsto (fun n => a n/(n:ℝ)) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ => ((n:ℝ)+1)/(n:ℝ)) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1:ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp
  have hs := (h.comp (tendsto_add_atTop_nat 1)).mul hr
  have ht := hs.sub h
  have hz : l*1-l=0 := by ring
  rw [hz] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hnp : (n:ℝ)+1≠0 := by positivity
  dsimp only [Function.comp_def]
  rw [Finset.sum_range_succ]
  push_cast
  field_simp
  ring

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_LadderCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def startingSupply (K : ℕ) : List Bool := List.replicate K true++List.replicate K false
lemma startingSupply_count (K : ℕ) (b : Bool) : (startingSupply K).count b=K := by
  cases b <;> simp [startingSupply,List.count_replicate]

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_StationaryCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Stationary
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The nonnegative running maximum of the partial sums of a stationary observable. -/
def maxSum (T : Ω → Ω) (f : Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n+1,x => max 0 (f x+maxSum T f n (T x))

omit [MeasurableSpace Ω] in
lemma maxSum_nonneg (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) :
    0 ≤ maxSum T f n x := by
  cases n <;> simp [maxSum]

omit [MeasurableSpace Ω] in
lemma maxSum_mono (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) :
    maxSum T f n x ≤ maxSum T f (n+1) x := by
  induction n generalizing x with
  | zero => exact maxSum_nonneg T f 1 x
  | succ n ih => exact max_le_max_left 0 (by linarith [ih (T x)])

lemma measurable_maxSum {T : Ω → Ω} {f : Ω → ℝ} (hT : Measurable T) (hf : Measurable f)
    (n : ℕ) : Measurable (maxSum T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max (hf.add (ih.comp hT))

lemma integrable_maxSum {T : Ω → Ω} {f : Ω → ℝ} (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) (n : ℕ) : Integrable (maxSum T f n) μ := by
  induction n with
  | zero => exact integrable_const _
  | succ n ih => exact (integrable_const _).sup (hf.add (hT.integrable_comp_of_integrable ih))

omit [MeasurableSpace Ω] in
lemma maxSum_bound_sum (T : Ω → Ω) (f : Ω → ℝ) (n k : ℕ) (hk : k ≤ n) (x : Ω) :
    ∑ i∈Finset.range k, f (T^[i] x) ≤ maxSum T f n x := by
  induction k generalizing n x with
  | zero => simpa using maxSum_nonneg T f n x
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      rw [Finset.sum_range_succ']
      simp only [Function.iterate_zero_apply,Function.iterate_succ_apply]
      have hh := ih n (by omega) (T x)
      have hb := le_max_right 0 (f x+maxSum T f n (T x))
      change _ ≤ max 0 (f x+maxSum T f n (T x))
      linarith

/-- Finite maximal ergodic inequality.  In particular no independence of the
observations is used in the maximal step. -/
lemma integral_on_maxSum_nonneg {T : Ω → Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (hm : Measurable f) (n : ℕ) :
    0 ≤ ∫ x in {x | 0 < maxSum T f n x},f x ∂μ := by
  cases n with
  | zero => simp [maxSum]
  | succ n =>
    let A : Set Ω := {x | 0 < maxSum T f (n+1) x}
    have hA : MeasurableSet A := measurableSet_lt measurable_const (measurable_maxSum hT.measurable hm _)
    have hg := integrable_maxSum hT hf n
    have hg' := integrable_maxSum hT hf (n+1)
    have hp := hT.integrable_comp_of_integrable hg
    change Integrable (fun x => maxSum T f n (T x)) μ at hp
    have hi : Integrable (A.indicator f) μ := hf.indicator hA
    have hb (x : Ω) : maxSum T f (n+1) x-maxSum T f n (T x) ≤ A.indicator f x := by
      by_cases hx : x∈A
      · rw [Set.indicator_of_mem hx]
        have hx' : 0 < f x+maxSum T f n (T x) := by
          simpa only [A,Set.mem_ofPred_eq,maxSum,lt_max_iff,lt_self_iff_false,false_or] using hx
        rw [maxSum,max_eq_right hx'.le]
        linarith
      · rw [Set.indicator_of_notMem hx]
        have hx' : maxSum T f (n+1) x=0 := le_antisymm (le_of_not_gt hx) (maxSum_nonneg _ _ _ _)
        rw [hx']
        linarith [maxSum_nonneg T f n (T x)]
    have h := integral_mono (hg'.sub hp) hi hb
    change (∫ x,maxSum T f (n+1) x-maxSum T f n (T x) ∂μ) ≤ _ at h
    rw [integral_sub hg' hp] at h
    have he := hT.hasLaw.integral_comp hg.aestronglyMeasurable
    change (∫ x,maxSum T f n (T x) ∂μ)=(∫ x,maxSum T f n x ∂μ) at he
    rw [he] at h
    have hmono := integral_mono hg hg' (maxSum_mono T f n)
    rw [integral_indicator hA] at h
    exact le_trans (by linarith) h

lemma finite_maximal_bound {T : Ω → Ω} {U : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hU : Integrable U μ) (hm : Measurable U)
    (hpos : ∀ x,0 ≤ U x) (η : ℝ) (hη : 0 < η) (n : ℕ) :
    μ.real {x | 0 < maxSum T (fun x => U x-η) n x} ≤ (∫ x,U x ∂μ)/η := by
  let A : Set Ω := {x | 0 < maxSum T (fun x => U x-η) n x}
  have hA : MeasurableSet A := measurableSet_lt measurable_const
    (measurable_maxSum hT.measurable (hm.sub_const η) n)
  have h := integral_on_maxSum_nonneg hT (hU.sub (integrable_const η)) (hm.sub_const η) n
  change 0 ≤ ∫ x in A,U x-η ∂μ at h
  rw [integral_sub hU.integrableOn (integrable_const η),setIntegral_const] at h
  have hb : ∫ x in A,U x ∂μ ≤ ∫ x,U x ∂μ :=
    setIntegral_le_integral hU (Filter.Eventually.of_forall hpos)
  simp only [smul_eq_mul] at h
  apply (le_div_iff₀ hη).mpr
  simpa only [smul_eq_mul] using (by linarith : μ.real A*η ≤ ∫ x,U x ∂μ)

/-- Hopf's stationary maximal bound, for a nonnegative integrable observable. -/
lemma maximal_bound {T : Ω → Ω} {U : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hU : Integrable U μ) (hm : Measurable U)
    (hpos : ∀ x,0 ≤ U x) (η : ℝ) (hη : 0 < η) :
    μ {x | ∃ n : ℕ,(n:ℝ)*η < ∑ i∈Finset.range n,U (T^[i] x)} ≤
      ENNReal.ofReal ((∫ x,U x ∂μ)/η) := by
  let A : ℕ → Set Ω := fun n => {x | 0 < maxSum T (fun x => U x-η) n x}
  have ha : Monotone A := by
    apply monotone_nat_of_le_succ
    intro n x hx
    exact lt_of_lt_of_le hx (maxSum_mono T (fun x => U x-η) n x)
  have hs : {x | ∃ n : ℕ,(n:ℝ)*η < ∑ i∈Finset.range n,U (T^[i] x)} ⊆ ⋃ n,A n := by
    rintro x ⟨n,hn⟩
    apply Set.mem_iUnion.mpr
    refine ⟨n,?_⟩
    have hb := maxSum_bound_sum T (fun x => U x-η) n n le_rfl x
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hb
    change 0 < maxSum T (fun x => U x-η) n x
    linarith
  apply (measure_mono hs).trans
  rw [ha.measure_iUnion]
  apply iSup_le
  intro n
  have h := ENNReal.ofReal_le_ofReal (finite_maximal_bound hT hU hm hpos η hη n)
  rw [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  exact h

def average (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) : ℝ :=
  (∑ i∈Finset.range n, f (T^[i] x))/(n:ℝ)

omit [MeasurableSpace Ω] in
lemma average_sub (T : Ω → Ω) (f g : Ω → ℝ) (n : ℕ) (x : Ω) :
    average T (fun x => f x-g x) n x=average T f n x-average T g n x := by
  simp only [average,Finset.sum_sub_distrib,sub_div]

lemma maximal_abs_average_bound {T : Ω → Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (hm : Measurable f)
    (η : ℝ) (hη : 0 < η) :
    μ {x | ∃ n : ℕ,η < |average T f n x|} ≤
      ENNReal.ofReal ((∫ x,|f x| ∂μ)/η) := by
  apply (measure_mono (show {x | ∃ n : ℕ,η < |average T f n x|} ⊆
      {x | ∃ n : ℕ,(n:ℝ)*η < ∑ i∈Finset.range n,|f (T^[i] x)|} from ?_)).trans
    (maximal_bound hT hf.abs hm.abs (fun _ => abs_nonneg _) η hη)
  rintro x ⟨n,hn⟩
  have hn0 : n≠0 := by rintro rfl; simp only [average,Finset.range_zero,Finset.sum_empty,zero_div,abs_zero] at hn; linarith
  have hnp : (0:ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hh : η*(n:ℝ) < |∑ i∈Finset.range n,f (T^[i] x)| := by
    simpa only [average,abs_div,abs_of_pos hnp] using (lt_div_iff₀ hnp).mp
      (show η < |∑ i∈Finset.range n,f (T^[i] x)|/(n:ℝ) by simpa only [average,abs_div,abs_of_pos hnp] using hn)
  exact ⟨n,by nlinarith [Finset.abs_sum_le_sum_abs (f := fun i => f (T^[i] x)) (s := Finset.range n)]⟩

end FKCRT.Stationary

end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Stationary
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The stationary maximal inequality makes almost-sure convergence of
averages stable under L¹ approximation. -/
theorem ae_average_limit_of_L1_approx {T : Ω → Ω} {f : Ω → ℝ} {g : ℕ → Ω → ℝ}
    {m : ℝ} {a : ℕ → ℝ} (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) (hmf : Measurable f)
    (hg : ∀ k,Integrable (g k) μ) (hmg : ∀ k,Measurable (g k))
    (happrox : Tendsto (fun k => ∫ x,|f x-g k x| ∂μ) atTop (𝓝 0))
    (ha : Tendsto a atTop (𝓝 m))
    (hgood : ∀ k,∀ᵐ x ∂μ,Tendsto (fun n => average T (g k) n x) atTop (𝓝 (a k))) :
    ∀ᵐ x ∂μ,Tendsto (fun n => average T f n x) atTop (𝓝 m) := by
  have hnull (ε : ℝ) (hε : 0 < ε) :
      μ {x | ∃ᶠ n in atTop,ε < |average T f n x-m|}=0 := by
    let B : Set Ω := {x | ∃ᶠ n in atTop,ε < |average T f n x-m|}
    have hb : ∀ᶠ k in atTop,μ B ≤ ENNReal.ofReal ((∫ x,|f x-g k x| ∂μ)/(ε/3)) := by
      filter_upwards [(Metric.tendsto_nhds.mp ha) (ε/3) (by positivity)] with k hk
      have he : B ≤ᵐ[μ] {x | ∃ n,ε/3 < |average T (fun x => f x-g k x) n x|} := by
        filter_upwards [hgood k] with x hx
        intro hB
        have hex := hB.and_eventually ((Metric.tendsto_nhds.mp hx) (ε/3) (by positivity))
        obtain ⟨n,hn,hgn⟩ := hex.exists
        refine ⟨n,?_⟩
        rw [average_sub]
        have hh := abs_add_three (average T f n x-average T (g k) n x)
          (average T (g k) n x-a k) (a k-m)
        have heq : (average T f n x-average T (g k) n x)+
            (average T (g k) n x-a k)+(a k-m)=average T f n x-m := by ring
        rw [heq] at hh
        rw [Real.dist_eq] at hk hgn
        linarith
      exact (measure_mono_ae he).trans
        (maximal_abs_average_bound hT (hf.sub (hg k)) (hmf.sub (hmg k)) _ (by positivity))
    have ht : Tendsto (fun k => ENNReal.ofReal ((∫ x,|f x-g k x| ∂μ)/(ε/3))) atTop (𝓝 0) := by
      simpa only [zero_div,ENNReal.ofReal_zero,Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (happrox.div_const (ε/3))
    exact le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds ht hb) bot_le
  have hae (k : ℕ) : ∀ᵐ x ∂μ,¬(∃ᶠ n in atTop,(1:ℝ)/(k+1) < |average T f n x-m|) :=
    measure_eq_zero_iff_ae_notMem.mp (hnull _ (by positivity))
  filter_upwards [ae_all_iff.mpr hae] with x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_gt (1/ε)
  have hkpos : (0:ℝ)<(k:ℝ)+1 := by positivity
  have hδ : (1:ℝ)/(k+1)<ε := by
    apply (div_lt_iff₀ hkpos).mpr
    have hh : 1<ε*(k:ℝ) := by simpa [mul_comm] using (div_lt_iff₀ hε).mp hk
    nlinarith
  have hh : ∀ᶠ n in atTop,|average T f n x-m| ≤ (1:ℝ)/(k+1) := by
    simpa only [not_frequently,not_lt] using hx k
  filter_upwards [hh] with n hn
  simpa only [Real.dist_eq] using hn.trans_lt hδ

end FKCRT.Stationary
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Stationary

lemma linear_remainder_of_ratio {S : ℕ → ℝ} {m : ℝ}
    (ht : Tendsto (fun n => S n/(n:ℝ)) atTop (𝓝 m)) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ n,|S n-m*n| ≤ ε*n+A := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp ht) ε hε)
  refine ⟨∑ i∈Finset.range (N+1),|S i-m*i|,Finset.sum_nonneg (fun _ _ => abs_nonneg _),fun n => ?_⟩
  by_cases hn : N+1 ≤ n
  · have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0 < n by omega)
    have h := hN n (by omega)
    rw [Real.dist_eq,show S n/(n:ℝ)-m=(S n-m*n)/(n:ℝ) by field_simp,abs_div,abs_of_pos hnpos] at h
    have hh := (div_lt_iff₀ hnpos).mp h
    exact hh.le.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
  · have h := Finset.single_le_sum (f := fun i => |S i-m*i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (show n < N+1 by omega))
    exact h.trans (le_add_of_nonneg_left (mul_nonneg hε.le (Nat.cast_nonneg n)))

lemma ratio_limit_of_linear_remainder {S : ℕ → ℝ} {m : ℝ}
    (h : ∀ ε : ℝ,0 < ε → ∃ A : ℝ,0 ≤ A ∧ ∀ n,|S n-m*n| ≤ ε*n+A) :
    Tendsto (fun n => S n/(n:ℝ)) atTop (𝓝 m) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨A,_,hA⟩ := h (ε/2) (by positivity)
  have ht : Tendsto (fun n : ℕ => A/(n:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,(tendsto_order.mp ht).2 (ε/2) (by positivity)] with n hn hsmall
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr hn
  rw [Real.dist_eq,show S n/(n:ℝ)-m=(S n-m*n)/(n:ℝ) by field_simp,abs_div,abs_of_pos hnpos]
  have hb := (div_le_div_iff_of_pos_right hnpos).mpr (hA n)
  have he : (ε/2*(n:ℝ)+A)/(n:ℝ)=ε/2+A/(n:ℝ) := by field_simp
  rw [he] at hb
  linarith

/-- Monotonicity fills the bounded gaps between a fixed arithmetic subsequence. -/
lemma ratio_limit_of_multiples {S : ℕ → ℝ} (hS : Monotone S) (r : ℕ) (hr : 0 < r)
    (m : ℝ) (ht : Tendsto (fun q => S (r*q)/(q:ℝ)) atTop (𝓝 ((r:ℝ)*m))) :
    Tendsto (fun n => S n/(n:ℝ)) atTop (𝓝 m) := by
  apply ratio_limit_of_linear_remainder
  intro ε hε
  obtain ⟨A,hA,hbound⟩ := linear_remainder_of_ratio ht ε hε
  refine ⟨A+ε+|m| *r,by positivity,fun n => ?_⟩
  let q := n/r
  have hlo : r*q ≤ n := Nat.mul_div_le n r
  have hhi : n < r*(q+1) := by
    have hmod := Nat.mod_lt n hr
    have hdiv := Nat.mod_add_div n r
    dsimp [q]
    nlinarith
  have hq : q ≤ n := Nat.div_le_self n r
  have hslo := hS hlo
  have hshi := hS hhi.le
  have hblo := abs_le.mp (hbound q)
  have hbhi := abs_le.mp (hbound (q+1))
  have hc1 : (r:ℝ)*q ≤ n := by exact_mod_cast hlo
  have hc2 : (n:ℝ) ≤ r*(q+1) := by exact_mod_cast hhi.le
  have hc3 : (q:ℝ) ≤ n := by exact_mod_cast hq
  have habs1 : m*((n:ℝ)-r*q) ≤ |m| *r := by
    have hh : 0 ≤ (n:ℝ)-r*q := by linarith
    have hhh : (n:ℝ)-r*q ≤ r := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self m) hh,abs_nonneg m]
  have habs2 : m*((r:ℝ)*(q+1)-n) ≤ |m| *r := by
    have hh : 0 ≤ (r:ℝ)*(q+1)-n := by linarith
    have hhh : (r:ℝ)*(q+1)-n ≤ r := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self m) hh,abs_nonneg m]
  have hns1 : -m*((n:ℝ)-r*q) ≤ |m| *r := by
    have hh : 0 ≤ (n:ℝ)-r*q := by linarith
    have hhh : (n:ℝ)-r*q ≤ r := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (neg_le_abs m) hh,abs_nonneg m]
  have hns2 : -m*((r:ℝ)*(q+1)-n) ≤ |m| *r := by
    have hh : 0 ≤ (r:ℝ)*(q+1)-n := by linarith
    have hhh : (r:ℝ)*(q+1)-n ≤ r := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (neg_le_abs m) hh,abs_nonneg m]
  push_cast at hblo hbhi
  apply abs_le.mpr
  constructor <;> nlinarith

lemma sum_range_blocks (f : ℕ → ℝ) (r q : ℕ) :
    ∑ j∈Finset.range (r*q),f j=∑ a∈Finset.range r,∑ i∈Finset.range q,f (a+r*i) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ,Finset.sum_range_add,ih]
    simp only [Finset.sum_range_succ,Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    omega

lemma interlaced_nonneg_limit {f : ℕ → ℝ} (hf : ∀ n,0 ≤ f n) (r : ℕ) (hr : 0 < r)
    (m : ℝ) (ht : ∀ a < r,Tendsto (fun q => (∑ i∈Finset.range q,f (a+r*i))/(q:ℝ)) atTop (𝓝 m)) :
    Tendsto (fun n => (∑ i∈Finset.range n,f i)/(n:ℝ)) atTop (𝓝 m) := by
  refine ratio_limit_of_multiples (S := fun n => ∑ i∈Finset.range n,f i) ?_ r hr m ?_
  · apply monotone_nat_of_le_succ
    intro n
    rw [Finset.sum_range_succ]
    linarith [hf n]
  · have h := tendsto_finsetSum (Finset.range r) (fun a ha => ht a (Finset.mem_range.mp ha))
    simpa only [← Finset.sum_div,← sum_range_blocks,Finset.sum_const,Finset.card_range,nsmul_eq_mul] using h

end FKCRT.Stationary
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Stationary
variable {α : Type*} [MeasurableSpace α]

def seqLaw (ν : Measure α) [IsProbabilityMeasure ν] : Measure (ℤ → α) :=
  Measure.infinitePi (fun _ : ℤ => ν)
instance seqLaw_probability (ν : Measure α) [IsProbabilityMeasure ν] : IsProbabilityMeasure (seqLaw ν) := by
  unfold seqLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

def shift (a : ℤ) (x : ℤ → α) : ℤ → α := fun k => x (k+a)

omit [MeasurableSpace α] in
lemma shift_add (a b : ℤ) (x : ℤ → α) : shift a (shift b x)=shift (a+b) x := by
  ext k
  simp [shift,add_assoc]
omit [MeasurableSpace α] in
lemma shift_iterate (n : ℕ) (x : ℤ → α) : (shift 1)^[n] x=shift (n:ℤ) x := by
  induction n with
  | zero => ext k; simp [shift]
  | succ n ih => rw [Function.iterate_succ_apply',ih,shift_add]; congr 1; omega

@[instance_reducible] def coords (S : Set ℤ) : MeasurableSpace (ℤ → α) :=
  ⨆ k∈S,MeasurableSpace.comap (fun x : ℤ → α => x k) inferInstance

lemma coords_mono {S R : Set ℤ} (h : S ⊆ R) : coords (α := α) S ≤ coords R := by
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  exact le_iSup_of_le k (le_iSup_of_le (h hk) le_rfl)

lemma coords_le (S : Set ℤ) : coords (α := α) S ≤ (inferInstance : MeasurableSpace (ℤ → α)) := by
  exact iSup_le fun k => iSup_le fun _ => (measurable_pi_apply k).comap_le

lemma measurable_shift_coords (S : Set ℤ) (a : ℤ) :
    Measurable[coords (S.image (fun k => k+a)),coords S] (shift (α := α) a) := by
  apply measurable_iff_comap_le.mpr
  simp only [coords,MeasurableSpace.comap_iSup]
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  rw [MeasurableSpace.comap_comp]
  change MeasurableSpace.comap (fun x : ℤ → α => x (k+a)) inferInstance ≤ _
  exact le_iSup_of_le (k+a) (le_iSup_of_le (Set.mem_image_of_mem _ hk) le_rfl)

lemma indep_coords (ν : Measure α) [IsProbabilityMeasure ν] {S R : Set ℤ} (h : Disjoint S R) :
    Indep (coords (α := α) S) (coords R) (seqLaw ν) := by
  exact indep_iSup_of_disjoint (fun k => (measurable_pi_apply k).comap_le)
    (iIndepFun_infinitePi (P := fun _ : ℤ => ν) (X := fun _ (a : α) => a) (fun _ => measurable_id)) h

def window (n : ℕ) : Set ℤ := {k | -(n:ℤ) ≤ k ∧ k ≤ n}

lemma window_mono {m n : ℕ} (h : m ≤ n) : window m ⊆ window n := by
  intro k hk
  dsimp [window] at hk ⊢
  omega

lemma window_disjoint (r i j : ℕ) (a : ℤ) (hij : i≠j) :
    Disjoint ((window r).image (fun k => k+(a+(2*(r:ℤ)+1)*i)))
      ((window r).image (fun k => k+(a+(2*(r:ℤ)+1)*j))) := by
  apply Set.disjoint_left.mpr
  rintro k ⟨s,hs,rfl⟩ ⟨t,ht,he⟩
  dsimp [window] at hs ht
  have hii : (i:ℤ)≠j := by exact_mod_cast hij
  rcases lt_or_gt_of_ne hii with hi | hi
  · have hh : (i:ℤ)+1 ≤ j := by omega
    have hmult := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2*(r:ℤ)+1)
    nlinarith
  · have hh : (j:ℤ)+1 ≤ i := by omega
    have hmult := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2*(r:ℤ)+1)
    nlinarith

lemma finite_window_progression_indep (ν : Measure α) [IsProbabilityMeasure ν]
    {f : (ℤ → α) → ℝ} {r : ℕ} (hf : Measurable[coords (window r)] f) (a : ℤ) :
    Pairwise (fun i j : ℕ => IndepFun (fun x => f (shift (a+(2*(r:ℤ)+1)*i) x))
      (fun x => f (shift (a+(2*(r:ℤ)+1)*j) x)) (seqLaw ν)) := by
  intro i j hij
  have hfi := hf.comp (measurable_shift_coords (window r) (a+(2*(r:ℤ)+1)*i))
  have hfj := hf.comp (measurable_shift_coords (window r) (a+(2*(r:ℤ)+1)*j))
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_coords ν (window_disjoint r i j a hij)) hfi.comap_le) hfj.comap_le

def windowFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℤ → α)) where
  seq r := coords (window r)
  mono' _ _ h := coords_mono (window_mono h)
  le' _ := coords_le _

lemma windowFiltration_sup : (⨆ r,windowFiltration (α := α) r)=(inferInstance : MeasurableSpace (ℤ → α)) := by
  apply le_antisymm (iSup_le (fun r => (windowFiltration (α := α)).le r))
  change (⨆ k : ℤ,MeasurableSpace.comap (fun x : ℤ → α => x k) inferInstance) ≤ _
  apply iSup_le
  intro k
  apply le_iSup_of_le k.natAbs
  change _ ≤ coords (window k.natAbs)
  exact le_iSup_of_le k (le_iSup_of_le ⟨by simpa using neg_le_neg (@Int.le_natAbs (-k)),Int.le_natAbs⟩ le_rfl)

end FKCRT.Stationary
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Stationary
variable {α : Type*} [MeasurableSpace α]

def reflect (x : ℤ → α) : ℤ → α := fun k => x (-k)
omit [MeasurableSpace α] in
lemma reflected_shift_iterate (n : ℕ) (x : ℤ → α) :
    reflect ((shift 1)^[n] (reflect x))=(shift (-1))^[n] x := by
  induction n with
  | zero => ext k; simp [reflect]
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    have hh (y : ℤ → α) : reflect (shift 1 y)=shift (-1) (reflect y) := by
      ext k; simp [reflect,shift]; congr 1; omega
    rw [hh,ih]

end FKCRT.Stationary
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PieceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT
namespace Stationary
variable {α : Type*}
lemma shift_neg_iterate (n : ℕ) (x : ℤ → α) : (shift (-1))^[n] x=shift (-(n:ℤ)) x := by
  induction n with
  | zero => ext k; simp [shift]
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    ext k
    simp only [shift,Nat.cast_add,Nat.cast_one]
    congr 1
    omega
end Stationary
end FKCRT
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical
variable {α : Type*}
lemma bottom_append {u v : List α} {k : ℕ} (hk : v.length ≤ k) :
    bottom (u++v) k=bottom u (k-v.length)++v := by
  unfold bottom
  rw [List.length_append,List.drop_append_of_le_length (by omega)]
  congr 2
  omega
lemma bottom_append_bounds [BEq α] [LawfulBEq α] (a : α) {u v : List α} {k : ℕ}
    (h₁ : v.length ≤ k) (h₂ : k ≤ u.length+v.length) :
    v.count a ≤ (bottom (u++v) k).count a ∧
      (bottom (u++v) k).count a ≤ v.count a+(k-v.length) := by
  rw [bottom_append h₁,List.count_append]
  have hh : (bottom u (k-v.length)).length=k-v.length := by
    rw [bottom,List.length_drop]
    omega
  have hc := List.count_le_length (a := a) (l := bottom u (k-v.length))
  rw [hh] at hc
  omega
lemma count_real_sum [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    (l.count a:ℝ)=(l.map (fun b => if b=a then (1:ℝ) else 0)).sum := by
  classical
  induction l with
  | nil => simp
  | cons b l ih =>
    by_cases h : b=a
    · subst b; simp [ih,add_comm]
    · simp [h,ih]
lemma count_ofFn_real [BEq α] [LawfulBEq α] (a : α) {n : ℕ} (f : Fin n → α) :
    ((List.ofFn f).count a:ℝ)=∑ j : Fin n,if f j=a then (1:ℝ) else 0 := by
  rw [count_real_sum,List.map_ofFn,List.sum_ofFn]
  rfl
end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_UniformSeams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

lemma exists_measure_pos_of_ae_cover {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A : Set Ω} {S : ℕ → Set Ω} (hA : 0<μ A) (hcover : ∀ᵐ x ∂μ,x∈A → ∃ n,x∈S n) :
    ∃ n,0<μ (S n) := by
  have hs : A ≤ᵐ[μ] ⋃ n,S n := by
    filter_upwards [hcover] with x hx
    exact fun ha => Set.mem_iUnion.mpr (hx ha)
  have hp : 0<μ (⋃ n,S n) := hA.trans_le (measure_mono_ae hs)
  exact exists_measure_pos_of_not_measure_iUnion_null hp.ne'

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_BlockCritical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

def seamIntervals (K : ℕ) : Finset (ℕ×ℕ) := (Finset.range (K+1)).biUnion Finset.HasAntidiagonal.antidiagonal
lemma mem_seamIntervals (K : ℕ) (z : ℕ×ℕ) : z∈seamIntervals K ↔ z.1+z.2≤K := by
  simp only [seamIntervals,Finset.mem_biUnion,Finset.mem_range,Finset.HasAntidiagonal.mem_antidiagonal]
  constructor
  · rintro ⟨N,hN,he⟩
    omega
  · intro h
    exact ⟨z.1+z.2,by omega,rfl⟩
lemma sum_seamIntervals {α : Type*} [AddCommMonoid α] (K : ℕ) (f : ℕ×ℕ → α) :
    (∑ z∈seamIntervals K,f z)=∑ N∈Finset.range (K+1),∑ z∈Finset.HasAntidiagonal.antidiagonal N,f z := by
  apply Finset.sum_biUnion
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro z hi hj
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hi hj
  omega
lemma sum_ite_le_of_injection {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (P : α → Prop) (Q : β → Prop) (f : α → β)
    (hf : ∀ a∈s,P a → f a∈t ∧ Q (f a))
    (hinj : ∀ a∈s,P a → ∀ b∈s,P b → f a=f b → a=b) :
    (∑ a∈s,if P a then (1:ℝ) else 0)≤∑ b∈t,if Q b then (1:ℝ) else 0 := by
  rw [Finset.sum_boole,Finset.sum_boole]
  norm_cast
  apply Finset.card_le_card_of_injOn f
  · intro a ha
    obtain ⟨has,hpa⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr (hf a has hpa)
  · intro a ha b hb he
    obtain ⟨has,hpa⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbs,hpb⟩ := Finset.mem_filter.mp hb
    exact hinj a has hpa b hbs hpb he

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_RadialBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial

/-- Polar integration for an arbitrary nonnegative radial function in a plane. -/
lemma lintegral_plane (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p : ℝ×ℝ,F (Real.sqrt (p.1^2+p.2^2)))=
      ENNReal.ofReal (2*Real.pi)*∫⁻ r : ℝ in Ioi 0,ENNReal.ofReal r*F r := by
  rw [← lintegral_comp_polarCoord_symm]
  have he (r θ : ℝ) : (r*Real.cos θ)^2+(r*Real.sin θ)^2=r^2 := by
    nlinarith [Real.cos_sq_add_sin_sq θ]
  change (∫⁻ p : ℝ×ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal p.1 * F (Real.sqrt ((p.1*Real.cos p.2)^2+(p.1*Real.sin p.2)^2)))=_
  have hh : (∫⁻ p : ℝ×ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 * F (Real.sqrt ((p.1*Real.cos p.2)^2+(p.1*Real.sin p.2)^2)))=
      ∫⁻ p : ℝ×ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,ENNReal.ofReal p.1*F p.1 := by
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    dsimp only
    rw [he,Real.sqrt_sq hp.1.le]
  rw [hh]
  change (∫⁻ p : ℝ×ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,ENNReal.ofReal p.1*F p.1
    ∂(volume.prod volume))=_
  rw [setLIntegral_prod _ (by fun_prop)]
  simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo]
  have hv : Real.pi - -Real.pi=2*Real.pi := by ring
  rw [hv]
  exact (lintegral_mul_const (ENNReal.ofReal (2*Real.pi))
    (show Measurable (fun r : ℝ => ENNReal.ofReal r*F r) by fun_prop)).trans (mul_comm _ _)

lemma sqrt_sum_image (x : ℝ) :
    (fun r : ℝ => Real.sqrt (x^2+r^2)) '' Ioi 0=Ioi |x| := by
  ext s
  constructor
  · rintro ⟨r,hr,rfl⟩
    have hx : |x|=Real.sqrt (x^2) := (Real.sqrt_sq_eq_abs x).symm
    rw [mem_Ioi,hx,Real.sqrt_lt_sqrt_iff (sq_nonneg x)]
    nlinarith [sq_pos_of_pos (show 0 < r from hr)]
  · intro hs
    have hsp : 0 < s := (abs_nonneg x).trans_lt hs
    have hsub : 0 < s^2-x^2 := by
      have hs : |x| < s := hs
      nlinarith [sq_abs x,abs_nonneg x]
    refine ⟨Real.sqrt (s^2-x^2),Real.sqrt_pos.mpr hsub,?_⟩
    dsimp only
    rw [Real.sq_sqrt hsub.le]
    convert Real.sqrt_sq hsp.le using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring

/-- Cylindrical radius substitution with its exact Jacobian. -/
lemma lintegral_radius_substitution (x : ℝ) (G : ℝ → ℝ≥0∞) :
    (∫⁻ r : ℝ in Ioi 0,ENNReal.ofReal r*G (Real.sqrt (x^2+r^2)))=
      ∫⁻ s : ℝ in Ioi |x|,ENNReal.ofReal s*G s := by
  have hd (r : ℝ) (hr : r∈Ioi (0:ℝ)) :
      HasDerivWithinAt (fun u : ℝ => Real.sqrt (x^2+u^2))
        (r/Real.sqrt (x^2+r^2)) (Ioi 0) r := by
    have hp : 0<x^2+r^2 := by nlinarith [sq_nonneg x,sq_pos_of_pos (show 0 < r from hr)]
    have hd : HasDerivAt (fun u : ℝ => Real.sqrt (x^2+u^2))
        ((2*r)/(2*Real.sqrt (x^2+r^2))) r := by
      simpa only [Pi.pow_apply,id_eq,Nat.reduceSub,Nat.cast_ofNat,pow_one,mul_one] using
        (((hasDerivAt_id r).pow 2).const_add (x^2)).sqrt hp.ne'
    have he : (2*r)/(2*Real.sqrt (x^2+r^2))=r/Real.sqrt (x^2+r^2) := by ring
    rw [he] at hd
    exact hd.hasDerivWithinAt
  have hi : InjOn (fun r : ℝ => Real.sqrt (x^2+r^2)) (Ioi (0:ℝ)) := by
    intro a ha b hb hab
    have hh : x^2+a^2=x^2+b^2 := by
      have h := congrArg (fun u : ℝ => u^2) hab
      simpa only [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))] using h
    have ha : 0<a := ha
    have hb : 0<b := hb
    nlinarith
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hd hi
    (fun s => ENNReal.ofReal s*G s)
  rw [sqrt_sum_image] at h
  rw [h]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hr : 0 < r := hr
  have hs : 0<Real.sqrt (x^2+r^2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg x,sq_pos_of_pos hr])
  dsimp only
  rw [abs_of_pos (div_pos hr hs),← mul_assoc,← ENNReal.ofReal_mul (div_nonneg hr.le hs.le),
    div_mul_cancel₀ _ hs.ne']

/-- Tonelli over the cylindrical slice `|x| < s`. -/
lemma lintegral_slice (G : ℝ×ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ x : ℝ,∫⁻ s : ℝ in Ioi |x|,G (x,s))=
      ∫⁻ s : ℝ in Ioi 0,∫⁻ x : ℝ in Ioo (-s) s,G (x,s) := by
  have hmeas : Measurable (fun p : ℝ×ℝ => if |p.1|<p.2 then G p else 0) := by
    exact hG.ite (measurableSet_lt (measurable_fst.abs) measurable_snd) measurable_const
  have hleft : (∫⁻ x : ℝ,∫⁻ s : ℝ in Ioi |x|,G (x,s))=
      ∫⁻ x : ℝ,∫⁻ s : ℝ,if |x| < s then G (x,s) else 0 := by
    apply lintegral_congr
    intro x
    rw [← lintegral_indicator measurableSet_Ioi]
    rfl
  rw [hleft,lintegral_lintegral_swap hmeas.aemeasurable,← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro s
  by_cases hs : 0 < s
  · rw [Set.indicator_of_mem (show s∈Ioi (0:ℝ) from hs),← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro x
    simp only [Set.indicator,Set.mem_Ioo,abs_lt]
  · rw [Set.indicator_of_notMem (show s∉Ioi (0:ℝ) from hs)]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [] with x
    have hh : ¬|x| < s := by linarith [abs_nonneg x]
    simp [hh]

/-- Three-dimensional radial integration, disintegrated along the first coordinate.
This supplies the radial noncentral-Gaussian transition without assuming a Bessel law. -/
theorem lintegral_cylindrical (G : ℝ×ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ p : ℝ×(ℝ×ℝ),G (p.1,Real.sqrt (p.1^2+p.2.1^2+p.2.2^2)))=
      ENNReal.ofReal (2*Real.pi)*
        ∫⁻ s : ℝ in Ioi 0,ENNReal.ofReal s*∫⁻ x : ℝ in Ioo (-s) s,G (x,s) := by
  change (∫⁻ p : ℝ×(ℝ×ℝ),G (p.1,Real.sqrt (p.1^2+p.2.1^2+p.2.2^2))
    ∂(volume.prod volume))=_
  rw [lintegral_prod _ (by fun_prop)]
  have hg (x : ℝ) : Measurable (fun r : ℝ => G (x,Real.sqrt (x^2+r^2))) := by fun_prop
  have hplane (x : ℝ) :
      (∫⁻ p : ℝ×ℝ,G (x,Real.sqrt (x^2+p.1^2+p.2^2)))=
      ENNReal.ofReal (2*Real.pi)*∫⁻ s : ℝ in Ioi |x|,ENNReal.ofReal s*G (x,s) := by
    have h := lintegral_plane (fun r => G (x,Real.sqrt (x^2+r^2))) (hg x)
    simp only [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))] at h
    simp only [← add_assoc] at h
    rw [h]
    congr 1
    exact lintegral_radius_substitution x (fun s => G (x,s))
  simp_rw [hplane]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [lintegral_slice (fun p => ENNReal.ofReal p.2*G p) (by fun_prop)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s _
  exact lintegral_const_mul' (ENNReal.ofReal s) (fun x => G (x,s)) ENNReal.ofReal_ne_top

end FKCRT.Radial
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

/-- Radial transition density of three-dimensional Brownian motion. -/
def radialHeat (t r s : ℝ) : ℝ :=
  if r=0 then 2*s^2/t*heat t s else s/r*killedHeat t r s

/-- Gaussian density in cylindrical coordinates, with the axial coordinate remaining. -/
def cylindricalDensity (t r s x : ℝ) : ℝ :=
  Real.exp (-(s^2+r^2)/(2*t))/(Real.sqrt (2*Real.pi*t))^3 * Real.exp (r*x/t)

lemma cylindricalDensity_continuous (t r : ℝ) :
    Continuous (fun p : ℝ×ℝ => cylindricalDensity t r p.2 p.1) := by
  unfold cylindricalDensity
  fun_prop

lemma cylindricalDensity_nonneg {t : ℝ} (ht : 0<t) (r s x : ℝ) :
    0 ≤ cylindricalDensity t r s x := by
  unfold cylindricalDensity
  positivity

lemma cylindricalDensity_endpoint {t : ℝ} (ht : 0<t) (r s : ℝ) :
    cylindricalDensity t r s s=heat t (s-r)/(2*Real.pi*t) := by
  have hS : (Real.sqrt (2*Real.pi*t))^2=2*Real.pi*t := Real.sq_sqrt (by positivity)
  have hSn : Real.sqrt (2*Real.pi*t)≠0 := by positivity
  have he : -(s^2+r^2)/(2*t)+r*s/t= -(s-r)^2/(2*t) := by ring
  unfold cylindricalDensity heat
  rw [div_mul_eq_mul_div,← Real.exp_add,he]
  rw [show (Real.sqrt (2*Real.pi*t))^3=Real.sqrt (2*Real.pi*t)*(2*Real.pi*t) by
    calc
      _ = Real.sqrt (2*Real.pi*t)*(Real.sqrt (2*Real.pi*t))^2 := by ring
      _ = _ := by rw [hS]]
  field_simp

lemma cylindricalDensity_neg_endpoint {t : ℝ} (ht : 0<t) (r s : ℝ) :
    cylindricalDensity t r s (-s)=heat t (s+r)/(2*Real.pi*t) := by
  have h := cylindricalDensity_endpoint ht r (-s)
  have he : cylindricalDensity t r (-s) (-s)=cylindricalDensity t r s (-s) := by
    simp only [cylindricalDensity,neg_sq]
  rw [he] at h
  rw [h]
  simp only [heat,show (-s-r)^2=(s+r)^2 by ring]

lemma integral_exp_linear {k : ℝ} (hk : k≠0) {s : ℝ} (hs : 0≤ s) :
    (∫ x : ℝ in Ioo (-s) s,Real.exp (k*x))=(Real.exp (k*s)-Real.exp (k*(-s)))/k := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (k*y)/k) (Real.exp (k*x)) x := by
    have h := (((hasDerivAt_id x).const_mul k).exp).div_const k
    simpa only [id_eq,mul_one,mul_div_cancel_right₀ _ hk] using h
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (show IntervalIntegrable (fun x : ℝ => Real.exp (k*x)) volume (-s) s from
      (by fun_prop : Continuous (fun x : ℝ => Real.exp (k*x))).intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le (by linarith),integral_Ioc_eq_integral_Ioo] at h
  exact h.trans (by ring)

lemma cylindricalDensity_of_norm {t : ℝ} (ht : 0<t) (r x y z : ℝ) :
    cylindricalDensity t r (Real.sqrt (x^2+y^2+z^2)) x=
      heat t (x-r)*heat t y*heat t z := by
  have hS : Real.sqrt (2*Real.pi*t)≠0 := by positivity
  have hs : (Real.sqrt (x^2+y^2+z^2))^2=x^2+y^2+z^2 := Real.sq_sqrt (by positivity)
  unfold cylindricalDensity heat
  rw [hs,div_mul_eq_mul_div,← Real.exp_add]
  rw [div_mul_div_comm,div_mul_div_comm,← Real.exp_add,← Real.exp_add]
  congr 1
  · congr 1
    ring
  · ring

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

def hitHeat (t x : ℝ) : ℝ := 2*x/t*heat t x

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory WithLp
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open SimpleWalk
abbrev Space := EuclideanSpace ℝ (Fin 3)

def axis (r : ℝ) : Space := toLp 2 ![r,0,0]

def step (t : ℝ) (v : Space) : Measure Space :=
  (stdGaussian Space).map (fun z => v+Real.sqrt t • z)

instance step_probability (t : ℝ) (v : Space) : IsProbabilityMeasure (step t v) := by
  unfold step
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma norm_axis (r : ℝ) : ‖axis r‖=|r| := by
  unfold axis
  have h := EuclideanSpace.real_norm_sq_eq (toLp 2 ![r,0,0])
  simp [Fin.sum_univ_succ] at h
  nlinarith [norm_nonneg (toLp 2 ![r,0,0]),abs_nonneg r,sq_abs r]

lemma gaussian_affine (a : ℝ) {t : ℝ} (ht : 0≤t) :
    (gaussianReal 0 1).map (fun x => a+Real.sqrt t*x)=gaussianReal a (⟨t,ht⟩ : ℝ≥0) := by
  have he : (fun x : ℝ => a+Real.sqrt t*x)=(fun x : ℝ => a+x) ∘ (fun x : ℝ => Real.sqrt t*x) := rfl
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop),gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  simp only [mul_zero,zero_add,mul_one]
  congr 1
  exact NNReal.eq (Real.sq_sqrt ht)

/-- The orthogonally invariant Gaussian step is exactly the product of its three coordinates. -/
theorem step_coordinates {t : ℝ} (ht : 0≤t) (v : Space) :
    step t v=(Measure.pi (fun i : Fin 3 => gaussianReal (v i) (⟨t,ht⟩ : ℝ≥0))).map (toLp 2) := by
  let f : Fin 3 → ℝ → ℝ := fun i x => v i+Real.sqrt t*x
  have hfm (i : Fin 3) : Measurable (f i) := by fun_prop
  have (i : Fin 3) : IsProbabilityMeasure ((gaussianReal 0 1).map (f i)) :=
    Measure.isProbabilityMeasure_map (hfm i).aemeasurable
  have hp : (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)).map (fun x i => f i (x i))=
      Measure.pi (fun i : Fin 3 => gaussianReal (v i) (⟨t,ht⟩ : ℝ≥0)) := by
    rw [Measure.pi_map_pi (fun i => (hfm i).aemeasurable)]
    congr 1
    funext i
    exact gaussian_affine _ ht
  unfold step
  rw [← map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop),← hp,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

lemma step_rotation (t : ℝ) (v : Space) (U : Space ≃ₗᵢ[ℝ] Space) :
    (step t v).map U=step t (U v) := by
  unfold step
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun z => U (v+Real.sqrt t • z))=(fun z => U v+Real.sqrt t • z) ∘ U := by
    funext z
    simp
  change (stdGaussian Space).map (fun z => U (v+Real.sqrt t • z))=_
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop),stdGaussian_map]

lemma step_norm_rotation (t : ℝ) (v : Space) (U : Space ≃ₗᵢ[ℝ] Space) :
    (step t (U v)).map (fun z => ‖z‖)=(step t v).map (fun z => ‖z‖) := by
  rw [← step_rotation t v U,Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  exact U.norm_map z

lemma step_norm_axis (t : ℝ) (v : Space) :
    (step t v).map (fun z => ‖z‖)=(step t (axis ‖v‖)).map (fun z => ‖z‖) := by
  let U : Space ≃ₗᵢ[ℝ] Space := Submodule.reflection (ℝ ∙ (v-axis ‖v‖))ᗮ
  have hU : U v=axis ‖v‖ := by
    apply Submodule.reflection_sub
    rw [norm_axis,abs_of_nonneg (norm_nonneg v)]
  rw [← hU]
  exact (step_norm_rotation t v U).symm

def coordinates : (Fin 3 → ℝ) ≃ᵐ ℝ×(ℝ×ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)

lemma coordinates_apply (f : Fin 3 → ℝ) : coordinates f=(f 0,(f 1,f 2)) := rfl
lemma coordinates_symm_apply (p : ℝ×(ℝ×ℝ)) : coordinates.symm p=![p.1,p.2.1,p.2.2] := by
  apply coordinates.injective
  rw [MeasurableEquiv.apply_symm_apply,coordinates_apply]
  rfl

lemma coordinates_preserving (μ : Fin 3 → Measure ℝ) [∀ i,SigmaFinite (μ i)] :
    MeasurePreserving coordinates (Measure.pi μ) ((μ 0).prod ((μ 1).prod (μ 2))) := by
  have h0 := measurePreserving_piFinSuccAbove μ 0
  have (i : Fin 2) : SigmaFinite (![μ 1,μ 2] i) := by
    fin_cases i <;> dsimp <;> infer_instance
  have h1 := (MeasurePreserving.id (μ 0)).prod (measurePreserving_finTwoArrow_vec (μ 1) (μ 2))
  have he : (fun j : Fin 2 => μ ((0 : Fin 3).succAbove j))=![μ 1,μ 2] := by
    funext j
    fin_cases j <;> rfl
  rw [he] at h0
  exact h1.comp h0

lemma norm_coordinates (p : ℝ×(ℝ×ℝ)) :
    ‖toLp 2 (coordinates.symm p)‖=Real.sqrt (p.1^2+p.2.1^2+p.2.2^2) := by
  rw [coordinates_symm_apply]
  have h := EuclideanSpace.real_norm_sq_eq (toLp 2 ![p.1,p.2.1,p.2.2])
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero] at h
  have hs := Real.sq_sqrt (show 0≤p.1^2+p.2.1^2+p.2.2^2 by positivity)
  nlinarith [norm_nonneg (toLp 2 ![p.1,p.2.1,p.2.2]),Real.sqrt_nonneg (p.1^2+p.2.1^2+p.2.2^2)]

lemma heat_gaussianPDF (a : ℝ) {t : ℝ} (ht : 0≤t) (x : ℝ) :
    gaussianPDF a (⟨t,ht⟩ : ℝ≥0) x=ENNReal.ofReal (heat t (x-a)) := by
  change ENNReal.ofReal (gaussianPDFReal a (⟨t,ht⟩ : ℝ≥0) x)=_
  congr 1
  simp only [gaussianPDFReal,heat,div_eq_mul_inv]
  change (Real.sqrt (2*Real.pi*t))⁻¹ * Real.exp (-(x-a)^2*(2*t)⁻¹) =
    Real.exp (-(x-a)^2*(2*t)⁻¹)*(Real.sqrt (2*Real.pi*t))⁻¹
  ring

end FKCRT.Radial
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory WithLp
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open SimpleWalk

/-- Lebesgue density supported on strictly positive radii. -/
def transition (t r s : ℝ) : ℝ≥0∞ :=
  (Ioi (0:ℝ)).indicator (fun s => ENNReal.ofReal (radialHeat t r s)) s

lemma measurable_transition : Measurable (fun p : ℝ×ℝ×ℝ => transition p.1 p.2.1 p.2.2) := by
  unfold transition radialHeat killedHeat heat
  apply Measurable.ite (by measurability)
  · apply Measurable.ennreal_ofReal
    apply Measurable.ite (by measurability) <;> fun_prop
  · fun_prop

/-- A finite affine Gaussian Markov chain, including a prescribed initial vector. -/
def chain : {m : ℕ} → Space → (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → Space) → Fin m → Space
  | 0,_,_,_,_ => Fin.elim0
  | _m+1,v,a,t,z =>
    let w := a 0 • v+Real.sqrt (t 0) • z 0
    Fin.cons w (chain w (Fin.tail a) (Fin.tail t) (Fin.tail z))

lemma continuous_chain (m : ℕ) (a t : Fin m → ℝ) :
    Continuous (fun p : Space×(Fin m → Space) => chain p.1 a t p.2) := by
  induction m with
  | zero => exact continuous_pi fun i => Fin.elim0 i
  | succ m ih =>
    have hw : Continuous (fun p : Space×(Fin (m+1) → Space) =>
      a 0 • p.1+Real.sqrt (t 0) • p.2 0) := by fun_prop
    have hh := (ih (Fin.tail a) (Fin.tail t)).comp (hw.prodMk
      (show Continuous (fun p : Space×(Fin (m+1) → Space) => Fin.tail p.2) from by fun_prop))
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hw
    · exact (continuous_apply j).comp hh

/-- Joint density, in chronological order, for the radii of that chain. -/
def chainDensity : {m : ℕ} → ℝ → (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ) → ℝ≥0∞
  | 0,_,_,_,_ => 1
  | _m+1,r,a,t,x => transition (t 0) (|a 0| *r) (x 0)*
    chainDensity (x 0) (Fin.tail a) (Fin.tail t) (Fin.tail x)

lemma measurable_chainDensity (m : ℕ) (a t : Fin m → ℝ) :
    Measurable (fun p : ℝ×(Fin m → ℝ) => chainDensity p.1 a t p.2) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    change Measurable (fun p : ℝ×(Fin (m+1) → ℝ) =>
      transition (t 0) (|a 0| * p.1) (p.2 0)*chainDensity (p.2 0) (Fin.tail a) (Fin.tail t) (Fin.tail p.2))
    apply Measurable.mul
    · exact measurable_transition.comp (show Measurable (fun p : ℝ×(Fin (m+1) → ℝ) =>
        (t 0,|a 0| * p.1,p.2 0)) from by fun_prop)
    · exact (ih (Fin.tail a) (Fin.tail t)).comp (show Measurable
        (fun p : ℝ×(Fin (m+1) → ℝ) => (p.2 0,Fin.tail p.2)) from by fun_prop)

end FKCRT.Radial
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_TraceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

/-- Durations followed by a terminal first-hitting segment. -/
def segments {m : ℕ} (d b : Fin m → ℕ) : List (ℕ×ℕ) :=
  List.ofFn (fun i => (d i,b i))

/-- Macroscopic bridge parameters expressed directly in successive durations. -/
def remaining {m : ℕ} (s : Fin m → ℝ) (r : ℝ) (i : Fin m) : ℝ :=
  r+∑ j∈Finset.univ.filter (fun j : Fin m => i<j),s j

def durationRatio {m : ℕ} (s : Fin m → ℝ) (r : ℝ) (i : Fin m) : ℝ :=
  remaining s r i/(s i+remaining s r i)

def durationVariance {m : ℕ} (s : Fin m → ℝ) (r : ℝ) (i : Fin m) : ℝ :=
  s i*remaining s r i/(s i+remaining s r i)

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory WithLp
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open TreeCoding

def bridgeRatio (a b : unitInterval) : ℝ := (1-(b:ℝ))/(1-(a:ℝ))
def bridgeVariance (a b : unitInterval) : ℝ := ((b:ℝ)-(a:ℝ))*(1-(b:ℝ))/(1-(a:ℝ))
def bridgeResidual {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (a b : unitInterval) (ω : Ω) : ℝ :=
  bridgeAt B b ω-bridgeRatio a b*bridgeAt B a ω

lemma bridgeVariance_pos {a b : unitInterval} (hab : a<b) (hb : (b:ℝ)<1) :
    0<bridgeVariance a b := by
  have ha : (a:ℝ)<1 := lt_trans hab hb
  exact div_pos (mul_pos (sub_pos.mpr hab) (sub_pos.mpr hb)) (sub_pos.mpr ha)

/-- The standardized regression innovations at arbitrary increasing interior times. -/
def innovation {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (i : Fin m) (ω : Ω) : ℝ :=
  (Real.sqrt (bridgeVariance (u i.castSucc) (u i.succ)))⁻¹*
    bridgeResidual B (u i.castSucc) (u i.succ) ω

end FKCRT.Radial
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory WithLp
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open TreeCoding SimpleWalk

def bridgeVector {Ω : Type} (B : Fin 3 → ℝ≥0 → Ω → ℝ) (u : unitInterval) (ω : Ω) : Space :=
  toLp 2 (fun k => bridgeAt (B k) u ω)

def bridgeDensity {m : ℕ} (u : Fin (m+1) → unitInterval) (x : Fin m → ℝ) : ℝ≥0∞ :=
  chainDensity 0 (fun i => bridgeRatio (u i.castSucc) (u i.succ))
    (fun i => bridgeVariance (u i.castSucc) (u i.succ)) x

end FKCRT.Radial
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_ExcursionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

/-- Lattice mesh and actual sampled heights, not a reference density. -/
def mesh (n : ℕ) : ℝ := 2/Real.sqrt ((2*n+1:ℕ):ℝ)

lemma mesh_pos (n : ℕ) : 0< mesh n := div_pos (by norm_num) (Real.sqrt_pos.mpr (by positivity))

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
open TreeCoding

def arrayPolygon {N : ℕ} (d : Fin N → ℕ) : C(unitInterval,ℝ) :=
  interpolation N (fun i => (arrayWalk d i.val:ℝ)/Real.sqrt (N:ℝ))

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
open TreeCoding

def pathEvaluation {m : ℕ} (u : Fin (m+1) → unitInterval) (f : C(unitInterval,ℝ)) : Fin m → ℝ :=
  fun i => f (u i.succ)

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_13 : MeasurableSpace C(unitInterval,ℝ) := borel _

/-- Strictly interior mesh, with the initial zero included only as a reference. -/
def interiorTimes (m : ℕ) (i : Fin (m+2)) : unitInterval :=
  gridPoint (m+2) i.castSucc

def interiorIndex (m : ℕ) (j : Fin (m+3)) : Fin (m+1) := ⟨min (j.val-1) m,by omega⟩

def interiorReconstruct (m : ℕ) (x : Fin (m+1) → ℝ) : C(unitInterval,ℝ) :=
  interpolation (m+2) (fun j => x (interiorIndex m j))

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_14 : MeasurableSpace C(unitInterval,ℝ) := borel _

def excursionPath {Ω : Type} (B : Fin 3 → ℝ≥0 → Ω → ℝ) (ω : Ω) : C(unitInterval,ℝ) :=
  ContinuousMap.mkD (standardExcursion B ω) 0

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_BlockLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Filter
open scoped BigOperators Topology
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

def criticalApproach (n : ℕ) : ℝ := 1-(1/2:ℝ)^(n+2)

lemma criticalApproach_bounds (n : ℕ) : (3:ℝ)/4 ≤ criticalApproach n ∧ criticalApproach n<1 := by
  have hpos : 0<(1/2:ℝ)^(n+2) := pow_pos (by norm_num) _
  have hle : (1/2:ℝ)^(n+2) ≤ (1/2:ℝ)^2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  dsimp [criticalApproach]
  norm_num at hle
  constructor <;> linarith

lemma criticalApproach_tendsto : Tendsto criticalApproach atTop (𝓝 1) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ)<1)).comp (tendsto_add_atTop_nat 2)
  change Tendsto (fun n : ℕ => 1-(1/2:ℝ)^(n+2)) atTop (𝓝 1)
  simpa only [Function.comp_def,sub_zero] using tendsto_const_nhds.sub h

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PlanarActivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

def submapComponents (a s : Perm (Dart n)) (A : Finset (Orbit a)) : ℕ :=
  Nat.card (spanningGraph a s (A : Set (Orbit a))).ConnectedComponent

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

/-- Exact FK polynomial of the graph with C contracted and R remaining.
Using connected-component counts avoids any relabelling or suppressed-edge
convention for the residual multigraph. -/
def residualWeight (t : ℝ) (a s : Perm (Dart n)) (C B : Finset (Orbit a)) : ℝ :=
  t ^ (2*(submapComponents a s (C∪B) : ℤ)+(B.card : ℤ)-
    (submapComponents a s C : ℤ)-1)

def residualPartition (t : ℝ) (a s : Perm (Dart n)) (C R : Finset (Orbit a)) : ℝ :=
  ∑ B∈R.powerset,residualWeight t a s C B

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

def Multiforest (a s : Perm (Dart n)) (A : Finset (Orbit a)) : Prop :=
  (spanningGraph a s (A : Set (Orbit a))).IsAcyclic ∧
  (∀ e∈A,orbit s e.out≠orbit s (a e.out)) ∧
  Set.InjOn (edgeEnds a s) (A : Set (Orbit a))

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

/-- Genuine multigraph spanning-tree completions of a partial exploration. -/
def treeExtensions (a s : Perm (Dart n)) (C R : Finset (Orbit a)) : Finset (Finset (Orbit a)) := by
  classical
  exact Finset.univ.filter (fun T => C⊆T ∧ T⊆C∪R ∧ Multiforest a s T ∧
    (spanningGraph a s (T : Set (Orbit a))).Connected)

lemma mem_treeExtensions (a s : Perm (Dart n)) (C R T : Finset (Orbit a)) :
    T∈treeExtensions a s C R ↔ C⊆T ∧ T⊆C∪R ∧ Multiforest a s T ∧
      (spanningGraph a s (T : Set (Orbit a))).Connected := by
  simp [treeExtensions]

end FKCRT
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CanonicalBijection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
open MapCycles Inventory
variable {n : ℕ}

lemma formPerm_finRange_eq_rotate :
    (List.finRange (2*(n+1))).formPerm=finRotate (2*(n+1)) := by
  apply Equiv.ext
  intro i
  have hh := List.formPerm_apply_getElem (List.finRange (2*(n+1))) (List.nodup_finRange _) i.val
    (by simp)
  simpa [finRotate_apply,Fin.ext_iff,Fin.val_add] using hh

end FKCRT
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SpineMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

/-- Offspring and right-child index seen at a genuine weak ascending record. -/
def ladderType (x : ℕ → ℕ) : ℕ × ℕ := (x (ladderIndex x),ladderOvershoot x)

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

/-- A record's terminal offspring and its increase over the previous running maximum.
This definition uses only the first t offspring, even for streams which have no later records. -/
def recordTypeAt (x : ℕ → ℕ) (t : ℕ) : ℕ×ℕ :=
  (x (t-1),(integerSum x t-prefixMaximum (integerSum x) (t-1)).toNat)

def recordSpineSum (b : ℕ×ℕ → ℝ) (x : ℕ → ℕ) (v : ℕ) : ℝ :=
  ∑ t ∈ weakRecords (integerSum x) v,b (recordTypeAt x t)

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SpineBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
namespace PlaneTree

lemma incrementWord_sum (l : List ℕ) : (incrementWord l).sum=(l.sum:ℤ)-l.length := by
  induction l with
  | nil => simp [incrementWord]
  | cons k l ih =>
    simp only [incrementWord,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at *
    omega

lemma degrees_sum (t : PlaneTree) : t.degrees.sum+1=t.degrees.length := by
  have hh := t.degrees_excursion.1
  rw [incrementWord_sum] at hh
  omega

lemma degree_lt_length (t : PlaneTree) {k : ℕ} (hk : k∈t.degrees) : k<t.degrees.length := by
  have := List.le_sum_of_mem hk
  have := t.degrees_sum
  omega

lemma incrementWord_ofFn {N : ℕ} (d : Fin N → Fin N) :
    incrementWord (List.ofFn (fun i => (d i).val))=degreeList d := by
  simp only [incrementWord,List.map_ofFn,degreeList,Function.comp_def]

abbrev Sized (N : ℕ) := {t : PlaneTree // t.degrees.length=N}

end PlaneTree
end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

def listStream (l : List ℕ) (k : ℕ) : ℕ := l[k]?.getD 0

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

/-- Sum of the genuine ancestral record types of a finite preorder prefix. -/
def profileSum (b : ℕ×ℕ → ℝ) (l : List ℕ) : ℝ :=
  recordSpineSum b (listStream l.reverse) l.length

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
namespace PlaneTree

/-- Literal ancestor offspring/slot list of a preorder vertex. Slot counts siblings to its right. -/
inductive Profile : PlaneTree → ℕ → List (ℕ×ℕ) → Prop
  | root (t) : Profile t 0 []
  | child (pre : List PlaneTree) (t : PlaneTree) (post : List PlaneTree) {v a}
      (h : Profile t v a) :
      Profile (node (pre++t::post)) (1+(forestDegrees pre).length+v)
        (((pre++t::post).length,post.length)::a)

 def flipSlot (z : ℕ×ℕ) : ℕ×ℕ := (z.1,z.1-1-z.2)

end PlaneTree
end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

local instance instMeasurableSpaceContinuousMapElemRealUnitIntervalProd_solutions_2 : MeasurableSpace C(unitInterval,ℝ×ℝ) := borel _

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MarkedSpines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

def spineTail (m : ℕ) (z : ℕ×ℕ) : ℝ := if m < z.1 then (z.1:ℝ) else 0
def spineTrunc (m : ℕ) (b : ℕ×ℕ → ℝ) (z : ℕ×ℕ) : ℝ := if z.1 ≤ m then b z else 0

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MarkedBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
variable {A : Type*} [MeasurableSpace A]

def markedTrunc (m : ℕ) (b : (ℕ×ℕ) → A → ℝ) (z : ℕ×ℕ) (a : A) : ℝ :=
  if z.1 ≤ m then b z a else 0

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_NodeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List
open scoped BigOperators
namespace FKCRT.Inventory.CoreTree
attribute [local instance] Classical.propDecidable

lemma flatMap_find_index {A B : Type*} (f : A → List B) (fs : List A) {r : ℕ}
    (hr : r<(fs.flatMap f).length) :
    ∃ i : Fin fs.length,∃ j,j<(f fs[i.val]).length ∧ r=((fs.take i.val).flatMap f).length+j := by
  induction fs generalizing r with
  | nil => simp at hr
  | cons a fs ih =>
    by_cases ha : r<(f a).length
    · exact ⟨⟨0,by simp⟩,r,ha,by simp⟩
    · obtain ⟨i,j,hj,he⟩ := ih (r := r-(f a).length) (by simp only [List.flatMap_cons,List.length_append] at hr;omega)
      refine ⟨i.succ,j,hj,?_⟩
      simp only [Fin.val_succ,List.take_succ_cons,List.flatMap_cons,List.length_append]
      omega

end FKCRT.Inventory.CoreTree
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CornerMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*}

def listDartEquiv (l : List α) (hn : l.Nodup) (hl : ∀ d,d∈l) {N : ℕ}
    (hN : l.length=N) : Fin N ≃ α :=
  (finCongr hN.symm).trans (Equiv.ofBijective l.get
    ⟨List.nodup_iff_injective_get.mp hn,fun d => by
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp (hl d)
      exact ⟨i,hi⟩⟩)

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MeasuredCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace FKCRT
attribute [local instance] Classical.propDecidable

/-- Equal-Lebesgue-mass time cells. The endpoint one is assigned to the last
cell; this retains a total, surjective coding without changing any mass. -/
def timeCell (N : ℕ) (hN : 0<N) (t : unitInterval) : Fin N :=
  ⟨min ⌊(N:ℝ)*t⌋₊ (N-1),lt_of_le_of_lt (min_le_right _ _) (by omega)⟩

/-- The positive preorder point lies inside its equal-mass time cell. -/
def cellPoint (N : ℕ) (hN : 0<N) (i : Fin N) : unitInterval :=
  ⟨(i.val+1:ℝ)/(N+1:ℝ),by constructor;positivity;apply (div_le_one (by positivity)).mpr;exact_mod_cast Nat.add_le_add_right i.isLt.le 1⟩

end FKCRT
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_GHPBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable
local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_15 : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance instBorelSpaceContinuousMapElemRealUnitInterval_solutions_15 : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

/-- Second continuous coordinate of the actual joint coding. -/
def heightProjection (f : C(unitInterval,ℝ×ℝ)) : C(unitInterval,ℝ) :=
  (⟨Prod.snd,continuous_snd⟩ : C(ℝ×ℝ,ℝ)).comp f

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MetricLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

def heightFactor (n : ℕ) : ℝ := Real.sqrt (1+1/(2*((n:ℝ)+1)))

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_16 : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance instBorelSpaceContinuousMapElemRealUnitInterval_solutions_16 : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

end FKCRT.TreeCoding
namespace FKCRT.Inventory
open FKCRT.TreeCoding
local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance instBorelSpaceContinuousMapElemRealUnitInterval_solutions : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_Convergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable
local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_1 : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

end FKCRT.Inventory
end

end OAI
end


