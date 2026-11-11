-- Prove2me | Definitions.Def_Q238K005
-- name    : Q238K005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:11:04.429406+00:00
-- url     : https://prove2.me/theorems/7e41b014-801e-4a7d-a757-da540c0e458b
-- title:
--   Definitions bundle Q238K005 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 46 declarations of OpenAI's Lean: 25 definitions, 8 instances and 13 theorems. The definitions and types are `OAI.MetricKMedianRecovery.RadiusMenus.additiveRadius`, `OAI.MetricKMedianRecovery.RadiusMenus.menuWeight`, `OAI.MetricKMedianRecovery.RadiusMenus.thirdNormalizer`, `OAI.MetricKMedianRecovery.RadiusMenus.upwardIndex`, `OAI.MetricKMedianRecovery.RationalMetricInput.comparisonSets`, `OAI.MetricKMedianRecovery.RationalMetricInput.optimum`, `OAI.MetricKMedianRecovery.RationalPhaseFuel.exponent`, `OAI.MetricKMedianRecovery.RationalPhaseFuel.next`, `OAI.MetricKMedianRecovery.Rounding.connection`, `OAI.MetricKMedianRecovery.Rounding.cost`, `OAI.MetricKMedianRecovery.Rounding.edge`, `OAI.MetricKMedianRecovery.Rounding.nearest`, `OAI.MetricKMedianRecovery.Sampling.Comparison.colorClass`, `OAI.MetricKMedianRecovery.ShortSelection.chosen`, `OAI.MetricKMedianRecovery.SortedIndex.equiv_dual`, `OAI.MetricKMedianRecovery.SuffixConstraints`, `OAI.MetricKMedianRecovery.dualRowTerm`, `OAI.MetricKMedianRecovery.extendBudget`, `OAI.MetricKMedianRecovery.lastRelation`, `OAI.MetricKMedianRecovery.linearRow`, `OAI.MetricKMedianRecovery.prefixMass`, `OAI.MetricKMedianRecovery.slack`, `OAI.MetricKMedianRecovery.suffixMaximum`, `OAI.circleMeasurableSpace`, `OAI.starSubalgebraCommCStarAlgebra`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_ExtendBudget`, `KMedianRecovery_Machines_FirstSize`, `KMedianRecovery_Model`, `KMedianRecovery_Recovery_Ball`, `KMedianRecovery_Recovery_Chosen`, `KMedianRecovery_Recovery_CommonL`, `KMedianRecovery_Recovery_DestinationFacility`, `KMedianRecovery_Recovery_InitialCorrect`, `KMedianRecovery_Recovery_Removal`, `KMedianRecovery_Recovery_RemovalReplay`, `KMedianRecovery_Strictness_RegularDualWitness`, `KMedianRecovery_Strictness_SortedDual`, `KMedianRecovery_Strictness_StrictnessGap`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`.
--
--   **Imported by** (directly, in this split): the bundles `Q238K015` and `Q238K016`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery

section
-- module Solutions.Q238_KM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

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
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Removal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

noncomputable def dualRowTerm {D : Type*} [DecidableEq D]
    (P : Finset D) (r : D → D → Prop) (alpha d : D → ℝ) (k j : D) : ℝ := by
  classical
  exact (if k ∈ P ∧ j ∈ P then alpha j else alpha k) - d j -
    (if r j k then d j + d k else 0)

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_StrictnessGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

def SuffixConstraints {q : ℕ} (lam : ℝ) (d a A : Fin q → ℝ) : Prop :=
  (∀ p, 0 ≤ d p) ∧
  (∑ p, d p) = 1 ∧
  (∀ p s, p ≤ s → a s - d s ≤ A p) ∧
  (∀ p,
    (∑ j ∈ Finset.univ.filter (fun j => p ≤ j), max (a p - d j) 0) +
    (∑ j ∈ Finset.univ.filter (fun j => j < p), max (A p - 2 * d j) 0) ≤ lam)

noncomputable def prefixMass {q : ℕ} (d : Fin q → ℝ) (p : Fin q) : ℝ :=
  ∑ j ∈ Finset.Iio p, d j

noncomputable def slack {q : ℕ} (lam : ℝ) (d a : Fin q → ℝ) (p : Fin q) : ℝ :=
  lam + 1 + prefixMass d p + (p.val : ℝ) * d p - (q : ℝ) * a p

noncomputable def linearRow {q : ℕ} (d a : Fin q → ℝ) (p j : Fin q) : ℝ :=
  a p - d j - if j < p then d p + d j else 0

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RemovalReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

noncomputable def suffixMaximum {q : ℕ} (a d : Fin q → ℝ) (p : Fin q) : ℝ :=
  (Finset.Ici p).sup' ⟨p, Finset.mem_Ici.mpr le_rfl⟩ (fun s => a s - d s)

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_RegularDualWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

def lastRelation {D : Type*} [DecidableEq D] (P : Finset D) (r : D → D → Prop)
    (j k : D) : Prop := j ∉ P ∧ (k ∈ P ∨ r j k)

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_ExtendBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

noncomputable def extendBudget {V : Type*} (D : Finset V) (alpha : D → ℝ) (p : V) : ℝ := by
  classical
  exact if hp : p ∈ D then alpha ⟨p,hp⟩ else 0

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FirstSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RadiusMenus

noncomputable def upwardIndex (kappa q r : ℝ) : ℕ := max 1 (Nat.ceil (r/(kappa*q)))
noncomputable def additiveRadius (kappa q : ℝ) (j : ℕ) : ℝ := j*kappa*q

lemma additiveRadius_pos (kappa q : ℝ) (j : ℕ) (hk : 0 < kappa)
    (hq : 0 < q) (hj : 0 < j) : 0 < additiveRadius kappa q j := by
  exact mul_pos (mul_pos (Nat.cast_pos.mpr hj) hk) hq

lemma upward_radius_bounds (kappa q r : ℝ) (hk : 0 < kappa) (hq : 0 < q)
    (hr : 0 ≤ r) :
    r ≤ additiveRadius kappa q (upwardIndex kappa q r) ∧
      additiveRadius kappa q (upwardIndex kappa q r) ≤ r+kappa*q := by
  have hkq : 0 < kappa*q := mul_pos hk hq
  have hcast : (upwardIndex kappa q r : ℝ) = max 1 (Nat.ceil (r/(kappa*q)) : ℝ) := by
    simp only [upwardIndex, Nat.cast_max, Nat.cast_one]
  have hlow : r/(kappa*q) ≤ (upwardIndex kappa q r : ℝ) := by
    rw [hcast]
    exact (Nat.le_ceil _).trans (le_max_right _ _)
  have hu := Nat.ceil_lt_add_one_of_gt_neg_one (show (-1 : ℝ) < r/(kappa*q) by
    have := div_nonneg hr hkq.le
    linarith)
  have hu' : (upwardIndex kappa q r : ℝ) ≤ r/(kappa*q)+1 := by
    rw [hcast]
    exact max_le (by have := div_nonneg hr hkq.le; linarith) hu.le
  constructor
  · have hh := (div_le_iff₀ hkq).mp hlow
    simpa only [additiveRadius, mul_assoc] using hh
  · have hh := mul_le_mul_of_nonneg_right hu' hkq.le
    have he : (r/(kappa*q)+1)*(kappa*q) = r+kappa*q := by field_simp
    rw [he] at hh
    simpa only [additiveRadius, mul_assoc] using hh

noncomputable def thirdNormalizer (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, (1/2 : ℝ)^(j+1)

lemma thirdNormalizer_eq (J : ℕ) :
    thirdNormalizer J = 1-(1/2 : ℝ)^J := by
  induction J with
  | zero => simp [thirdNormalizer]
  | succ J ih =>
    rw [thirdNormalizer, Finset.sum_range_succ, ← thirdNormalizer, ih, pow_succ]
    ring

lemma thirdNormalizer_pos {J : ℕ} (hJ : 0 < J) : 0 < thirdNormalizer J := by
  rw [thirdNormalizer_eq]
  have hh : (1/2 : ℝ)^J < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  linarith

noncomputable def menuWeight (M E J : ℕ) : Fin M ⊕ (Fin (E+1) ⊕ Fin J) → ℝ
  | .inl _ => 1/(3*M)
  | .inr (.inl _) => 1/(3*(E+1))
  | .inr (.inr j) => (1/3) * ((1/2 : ℝ)^(j.val+1)/thirdNormalizer J)

lemma menuWeight_total (M E J : ℕ) (hM : 0 < M) (hJ : 0 < J) :
    ∑ x, menuWeight M E J x = 1 := by
  have hMr : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hEr : (E : ℝ)+1 ≠ 0 := by positivity
  have hJr : thirdNormalizer J ≠ 0 := ne_of_gt (thirdNormalizer_pos hJ)
  simp only [Fintype.sum_sum_type, menuWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (1/2 : ℝ)^(j+1)) J]
  change (M : ℝ)*(1/(3*M)) +
    (((E+1 : ℕ) : ℝ)*(1/(3*((E : ℝ)+1))) +
      (1/3)*(thirdNormalizer J/thirdNormalizer J)) = 1
  rw [div_self hJr]
  push_cast
  field_simp
  ring

end MetricKMedianRecovery.RadiusMenus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

namespace RationalMetricInput

def comparisonSets (I : RationalMetricInput) : Finset (Finset (Fin I.pointCount)) :=
  I.facilities.powerset.filter (fun S => S.Nonempty ∧ S.card ≤ I.budget)

lemma comparisonSets_nonempty (I : RationalMetricInput) : I.comparisonSets.Nonempty := by
  obtain ⟨i, hi⟩ := I.facilities_nonempty
  refine ⟨{i}, ?_⟩
  simp only [comparisonSets, Finset.mem_filter, Finset.mem_powerset,
    Finset.singleton_subset_iff, Finset.singleton_nonempty, Finset.card_singleton, true_and]
  exact ⟨hi, I.budget_pos⟩

def optimum (I : RationalMetricInput) : ℚ :=
  I.comparisonSets.inf' I.comparisonSets_nonempty I.cost

end RationalMetricInput

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Population
variable {V : Type*} [PseudoMetricSpace V]

omit [PseudoMetricSpace V] in

lemma disjoint_population_budget {I : Type*} [DecidableEq V]
    (D : Finset V) (A : Finset I) (C : I → Finset V) (q r : I → ℝ)
    (cost : V → ℝ) (P : ℝ) (m : ℕ) (hP : 0 < P) (hm : 0 < m)
    (hcost : ∀ p ∈ D, 0 ≤ cost p) (hPsum : ∑ p ∈ D, cost p = P)
    (hC : ∀ i ∈ A, C i ⊆ D) (hdis : Set.PairwiseDisjoint (↑A) C)
    (hq : ∀ i ∈ A, 0 < q i) (hr : ∀ i ∈ A, 0 ≤ r i)
    (hpop : ∀ i ∈ A, P/(m : ℝ) ≤ q i * (C i).card)
    (hcharge : ∀ i ∈ A, ∀ p ∈ C i, (9/10 : ℝ)*r i ≤ cost p) :
    ∑ i ∈ A, r i / q i ≤ (10/9 : ℝ)*m := by
  classical
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hsub : A.biUnion C ⊆ D := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
    exact hC i hi hpi
  have htotal : (∑ i ∈ A, (9/10 : ℝ)*r i*(C i).card) ≤ P := by
    calc
      _ = ∑ i ∈ A, ∑ _p ∈ C i, (9/10 : ℝ)*r i := by simp [mul_comm]
      _ ≤ ∑ i ∈ A, ∑ p ∈ C i, cost p := by
        exact Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hcharge i hi))
      _ = ∑ p ∈ A.biUnion C, cost p := (Finset.sum_biUnion hdis).symm
      _ ≤ ∑ p ∈ D, cost p := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p hp _ => hcost p hp)
      _ = P := hPsum
  have hpoint : ∀ i ∈ A, (9/10 : ℝ)*(P/m)*(r i/q i) ≤ (9/10 : ℝ)*r i*(C i).card := by
    intro i hi
    have hh := mul_le_mul_of_nonneg_right (hpop i hi)
      (show 0 ≤ (9/10 : ℝ)*r i/q i from div_nonneg (mul_nonneg (by norm_num) (hr i hi)) (hq i hi).le)
    have he : q i*(C i).card*((9/10 : ℝ)*r i/q i) = (9/10 : ℝ)*r i*(C i).card := by
      field_simp [ne_of_gt (hq i hi)]
    rw [he] at hh
    calc
      _ = P/m*((9/10 : ℝ)*r i/q i) := by ring
      _ ≤ _ := hh
  have hs := (Finset.sum_le_sum hpoint).trans htotal
  rw [← Finset.mul_sum] at hs
  have he : (9/10 : ℝ)*(P/m)*((10/9 : ℝ)*m) = P := by field_simp
  have hs' : (9/10 : ℝ)*(P/m)*(∑ i ∈ A, r i/q i) ≤
      (9/10 : ℝ)*(P/m)*((10/9 : ℝ)*m) := hs.trans_eq he.symm
  exact (mul_le_mul_iff_right₀ (mul_pos (by norm_num : (0 : ℝ)<9/10) (div_pos hP hm'))).mp hs'

end MetricKMedianRecovery.Population

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Chosen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.ShortSelection

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def chosen (Q : Finset I) (neighbor : I → I) (c : I → Bool) : Finset I :=
  Q.filter (fun i => c i = false ∧ c (neighbor i) = true)

end MetricKMedianRecovery.ShortSelection

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DestinationFacility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

noncomputable def colorClass (H : Finset V) (colors : V → Fin 3) (c : Fin 3) : Finset V :=
  H.filter (fun v => colors v = c)

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CommonL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Rounding
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

noncomputable def edge (u : ℝ) (C : ℕ) (x y : V) : ℕ :=
  if x = y then 0 else min C (max 1 ⌈dist x y/u⌉₊)

lemma edge_self (u : ℝ) (C : ℕ) (x : V) : edge u C x x = 0 := by simp [edge]
lemma edge_symm (u : ℝ) (C : ℕ) (x y : V) : edge u C x y = edge u C y x := by
  simp only [edge,dist_comm y x,eq_comm]

noncomputable def connection (u : ℝ) (C : ℕ) (S : Finset V) (p : V) : ℕ :=
  if h : S.Nonempty then S.inf' h (edge u C p) else 0
noncomputable def cost (u : ℝ) (C : ℕ) (D S : Finset V) : ℕ :=
  ∑ p ∈ D, connection u C S p
noncomputable def nearest (u : ℝ) (C : ℕ) (S : Finset V) (hS : S.Nonempty) (p : V) : V :=
  Classical.choose (Finset.exists_min_image S (edge u C p) hS)

end MetricKMedianRecovery.Rounding

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhaseFuel

noncomputable def exponent (K Z : ℚ) : ℕ := ⌈Real.log (Z:ℝ) / Real.log (K:ℝ)⌉₊

def next (K Z : ℚ) (q : ℕ) : ℕ := if Z ≤ K^q then q else q+1

end MetricKMedianRecovery.RationalPhaseFuel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_SortedDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {V : Type*} [LinearOrder V]
def equiv_dual (D : Finset V) : Fin D.card ≃ D := (D.orderIsoOfFin rfl).toEquiv
end MetricKMedianRecovery.SortedIndex

end OAI
end


