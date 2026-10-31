-- Prove2me | Definitions.Def_OAIQ028V002
-- name    : OAIQ028V002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T00:07:34.771974+00:00
-- url     : https://prove2.me/theorems/547c5598-2c66-4a14-a280-c4655dbe0d5d
-- title:
--   Definitions bundle OAIQ028V002 of the split of OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.VertexCover.explicit_cover_gap` and `OAI.VertexCover.every_fixed_factor_below_two`, carved from OpenAI's openai/math development (OpenAI, *The Factor-Two Hardness Threshold for Vertex Cover (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 519 declarations of OpenAI's Lean: 209 definitions, 5 inductive types or structures, 20 instances and 285 theorems. The definitions and types are `OAI.VertexCover.ClauseProjection.Pattern`, `OAI.VertexCover.ClauseProjection.flipSign`, `OAI.VertexCover.ClauseProjection.patternEquiv`, `OAI.VertexCover.Cube.blockLaw`, `OAI.VertexCover.Cube.boundedVersion`, `OAI.VertexCover.Cube.carrier`, `OAI.VertexCover.Cube.intervalLaw`, `OAI.VertexCover.Cube.law`, `OAI.VertexCover.ExplicitGraph.numbered`, `OAI.VertexCover.FiniteAntiConcentration.choices`, `OAI.VertexCover.FiniteAntiConcentration.coordinateShift`, `OAI.VertexCover.FiniteAntiConcentration.grid`, `OAI.VertexCover.FiniteAntiConcentration.gridShift`, `OAI.VertexCover.FiniteAntiConcentration.gridTailDensity`, `OAI.VertexCover.FiniteAntiConcentration.intervalFamily`, `OAI.VertexCover.FiniteAntiConcentration.orderedChoice`, `OAI.VertexCover.FiniteAntiConcentration.rawChoice`, `OAI.VertexCover.FiniteAntiConcentration.subsetSum`, `OAI.VertexCover.FiniteAntiConcentration.toggleEquiv`, `OAI.VertexCover.GridCoupling.index`, `OAI.VertexCover.GridCoupling.midpoint`, `OAI.VertexCover.LabelCover`, `OAI.VertexCover.LabelCover.AffineIndex`, `OAI.VertexCover.LabelCover.BatchWeights`, `OAI.VertexCover.LabelCover.Compatible`, `OAI.VertexCover.LabelCover.Coordinate`, `OAI.VertexCover.LabelCover.Decoding.PairHit`, `OAI.VertexCover.LabelCover.Decoding.leftAt`, `OAI.VertexCover.LabelCover.Decoding.pairHits`, `OAI.VertexCover.LabelCover.Decoding.rightAt`, `OAI.VertexCover.LabelCover.HiddenSeeds`, `OAI.VertexCover.LabelCover.InWeightCube`, `OAI.VertexCover.LabelCover.Iso`, `OAI.VertexCover.LabelCover.Iso.labeling`, `OAI.VertexCover.LabelCover.Iso.symm`, `OAI.VertexCover.LabelCover.Labeling`, `OAI.VertexCover.LabelCover.ListHit`, `OAI.VertexCover.LabelCover.OppositePairKey`, `OAI.VertexCover.LabelCover.PairSeedHit`, `OAI.VertexCover.LabelCover.ParallelCoherent` and 174 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `VertexCover_Analysis_BaseReductionCoherent`, `VertexCover_Analysis_BatchFunctionOwnLipschitz`, `VertexCover_Analysis_BatchGradientForm`, `VertexCover_Analysis_BlockLawAc`, `VertexCover_Analysis_BlockLawNegInvariant`, `VertexCover_Analysis_CanonicalGradientValid`, `VertexCover_Analysis_DenseHighFraction`, `VertexCover_Analysis_DenseSeparatorData`, `VertexCover_Analysis_DistanceMinusSelect`, `VertexCover_Analysis_ErasedSeedSeparatorAverage`, `VertexCover_Analysis_GraphCompleteness`, `VertexCover_Analysis_GridCentralCard`, `VertexCover_Analysis_LawNegInvariant`, `VertexCover_Analysis_ListMassHitMaximum`, `VertexCover_Analysis_MidpointGridTail`, `VertexCover_Analysis_OppositePairSeparatorResidual`, `VertexCover_Analysis_OwnGradientMeasurable`, `VertexCover_Analysis_OwnGradientUnsupported`, `VertexCover_Analysis_OwnMeanPartialAe`, `VertexCover_Analysis_PoincareOne`, `VertexCover_Analysis_PowerValueRepetition`, `VertexCover_Analysis_PrivateMassSumHits`, `VertexCover_Analysis_Restriction`, `VertexCover_Analysis_RoundingError`, `VertexCover_Analysis_SeedEnergyBudget`, `VertexCover_Analysis_SelectedIntegralAbs`, `VertexCover_Analysis_SeparatorBoundCube`, `VertexCover_Analysis_SeparatorRoundingErrorAe`, `VertexCover_Analysis_StarEnergyBudget`, `VertexCover_Analysis_StarMeanContinuous`, `VertexCover_Analysis_ThresholdListEnergy`, `VertexCover_Analysis_VarianceCoordinateSum`, `VertexCover_Analysis_VariancePi`, `VertexCover_Analysis_VarianceProduct`, `VertexCover_Analysis_WeightEnergyBudget`, `VertexCover_Machines_Address`, `VertexCover_Machines_Approximation`, `VertexCover_Machines_BinaryOutput`, `VertexCover_Machines_BoundedBinary`, `VertexCover_Machines_Cloud`, `VertexCover_Machines_CloudIndex`, `VertexCover_Machines_DenseParse`, `VertexCover_Machines_DescriptorMath`, `VertexCover_Machines_ExpanderBound`, `VertexCover_Machines_ExpanderStep`, `VertexCover_Machines_FinalCNFBase`, `VertexCover_Machines_FixedOps`, `VertexCover_Machines_GraphFrame`, `VertexCover_Machines_GraphNumber`, `VertexCover_Machines_InitialTable`, `VertexCover_Machines_LCData`, `VertexCover_Machines_LCNumber`, `VertexCover_Machines_ListGrowing`, `VertexCover_Machines_ListIndex`, `VertexCover_Machines_ListMore`, `VertexCover_Machines_ListNat`, `VertexCover_Machines_ListParam`, `VertexCover_Machines_ListSearch`, `VertexCover_Machines_NatDiv`, `VertexCover_Machines_NatLog`, `VertexCover_Machines_NormRepresentation`, `VertexCover_Machines_NumberedGraph`, `VertexCover_Machines_Option`, `VertexCover_Machines_ParseClause`, `VertexCover_Machines_ParseFrame`, `VertexCover_Machines_ParseName`, `VertexCover_Machines_PowerLC`, `VertexCover_Machines_PowerRow`, `VertexCover_Machines_Profile`, `VertexCover_Machines_SimpleLC`, `VertexCover_Machines_TableCodeBound`, `VertexCover_Reduction_AverageCommute`, `VertexCover_Reduction_BatchesTripleSum`, `VertexCover_Reduction_CompatibleSingleton`, `VertexCover_Reduction_ConditionNested`, `VertexCover_Reduction_CoordinateProductInvariant`, `VertexCover_Reduction_DecodingUpperThreeHalves`, `VertexCover_Reduction_FiniteMeanUnionBound`, `VertexCover_Reduction_GraphSoundness`, `VertexCover_Reduction_GraphSoundness2`, `VertexCover_Reduction_GridBudget`, `VertexCover_Reduction_HighVectorsSeparated`, `VertexCover_Reduction_HonestLargeSumIndependent`, `VertexCover_Reduction_HonestSelectionCompatible`, `VertexCover_Reduction_IncrementNorm`, `VertexCover_Reduction_IntegralCoe`, `VertexCover_Reduction_ListHitMaximum`, `VertexCover_Reduction_NormAttainedSupport`, `VertexCover_Reduction_PairEventMean`, `VertexCover_Reduction_PairHitsProbability`, `VertexCover_Reduction_PairSeedFiberCard`, `VertexCover_Reduction_PrivateProjectionBatchLower`, `VertexCover_Reduction_PrivateTotalEnergyLaw`, `VertexCover_Reduction_RejectionCount`, `VertexCover_Reduction_RestrictionStarBudget`, `VertexCover_Reduction_SeparatorContinuousSumOdd`, `VertexCover_Reduction_SeparatorStarOscillation`.
--
--   **Imports.** It imports the published bundle `Def_VertexCover`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ028V004` and `OAIQ028V005`.
-- source:
--   OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_VertexCover

section
-- module Solutions.OAIQ028_VC.Compat
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_CompatibleSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover

structure LabelCover where
  u : ℕ
  v : ℕ
  qU : ℕ
  qV : ℕ
  M : ℕ
  qU_pos : 0 < qU
  qV_pos : 0 < qV
  M_pos : 0 < M
  left : Fin M → Fin u
  right : Fin M → Fin v
  projection : Fin M → Fin qU → Fin qV

namespace LabelCover

abbrev Labeling (Φ : LabelCover) := (Fin Φ.u → Fin Φ.qU) × (Fin Φ.v → Fin Φ.qV)

def Satisfies (Φ : LabelCover) (A : Φ.Labeling) (c : Fin Φ.M) : Prop :=
  Φ.projection c (A.1 (Φ.left c)) = A.2 (Φ.right c)

instance instDecidableSatisfies (Φ : LabelCover) (A : Φ.Labeling) (c : Fin Φ.M) :
    Decidable (Φ.Satisfies A c) := inferInstanceAs (Decidable (_ = _))

def satisfiedCount (Φ : LabelCover) (A : Φ.Labeling) : ℕ :=
  (Finset.univ.filter (Φ.Satisfies A)).card

def maxSatisfied (Φ : LabelCover) : ℕ :=
  Finset.univ.sup Φ.satisfiedCount

noncomputable def value (Φ : LabelCover) : ℝ := (Φ.maxSatisfied : ℝ) / Φ.M

def defaultLabeling (Φ : LabelCover) : Φ.Labeling :=
  (fun _ => ⟨0, Φ.qU_pos⟩, fun _ => ⟨0, Φ.qV_pos⟩)

theorem satisfiedCount_le_max (Φ : LabelCover) (A : Φ.Labeling) :
    Φ.satisfiedCount A ≤ Φ.maxSatisfied := by
  exact Finset.le_sup (f := Φ.satisfiedCount) (Finset.mem_univ A)

theorem count_le_of_value_le (Φ : LabelCover) {σ : ℝ} (h : Φ.value ≤ σ)
    (A : Φ.Labeling) : (Φ.satisfiedCount A : ℝ) ≤ σ * Φ.M := by
  have hM : (0 : ℝ) < Φ.M := Nat.cast_pos.mpr Φ.M_pos
  have hm : (Φ.maxSatisfied : ℝ) ≤ σ * Φ.M := (div_le_iff₀ hM).mp h
  exact le_trans (Nat.cast_le.mpr (Φ.satisfiedCount_le_max A)) hm

abbrev Query (Φ : LabelCover) (d : ℕ) :=
  Σ j : Fin d,
    ({k : Fin d // j < k} → Fin Φ.u) × ({k : Fin d // k < j} → Fin Φ.v)

namespace Query

def scopeU {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) : Finset (Fin Φ.u) :=
  Finset.univ.image i.2.1

def scopeV {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) : Finset (Fin Φ.v) :=
  Finset.univ.image i.2.2

abbrev Assignment {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) :=
  ({x // x ∈ i.scopeU} → Fin Φ.qU) × ({y // y ∈ i.scopeV} → Fin Φ.qV)

def Valid {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) (A : i.Assignment) : Prop :=
  ∀ c : Fin Φ.M, ∀ hx : Φ.left c ∈ i.scopeU, ∀ hy : Φ.right c ∈ i.scopeV,
    Φ.projection c (A.1 ⟨Φ.left c, hx⟩) = A.2 ⟨Φ.right c, hy⟩

instance instDecidableValid {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) (A : i.Assignment) :
    Decidable (i.Valid A) := inferInstanceAs (Decidable (∀ _c _hx _hy, _ = _))

abbrev LocalLabel {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) :=
  {A : i.Assignment // i.Valid A}

end Query

abbrev Coordinate (Φ : LabelCover) (d : ℕ) := Σ i : Φ.Query d, i.LocalLabel

def Compatible (Φ : LabelCover) {d : ℕ} (I : Finset (Φ.Coordinate d)) : Prop :=
  (∀ p ∈ I, ∀ q ∈ I, p.1 = q.1 → p = q) ∧
  (∀ p ∈ I, ∀ q ∈ I, ∀ x (hp : x ∈ p.1.scopeU) (hq : x ∈ q.1.scopeU),
    p.2.1.1 ⟨x, hp⟩ = q.2.1.1 ⟨x, hq⟩) ∧
  (∀ p ∈ I, ∀ q ∈ I, ∀ y (hp : y ∈ p.1.scopeV) (hq : y ∈ q.1.scopeV),
    p.2.1.2 ⟨y, hp⟩ = q.2.1.2 ⟨y, hq⟩) ∧
  (∀ p ∈ I, ∀ q ∈ I, ∀ c (hp : Φ.left c ∈ p.1.scopeU)
      (hq : Φ.right c ∈ q.1.scopeV),
    Φ.projection c (p.2.1.1 ⟨Φ.left c, hp⟩) = q.2.1.2 ⟨Φ.right c, hq⟩)

theorem compatible_mono (Φ : LabelCover) {d : ℕ} {I J : Finset (Φ.Coordinate d)}
    (h : Φ.Compatible I) (hJI : J ⊆ I) : Φ.Compatible J := by
  rcases h with ⟨hu, hx, hy, hc⟩
  exact ⟨fun p hp q hq => hu p (hJI hp) q (hJI hq),
    fun p hp q hq => hx p (hJI hp) q (hJI hq),
    fun p hp q hq => hy p (hJI hp) q (hJI hq),
    fun p hp q hq => hc p (hJI hp) q (hJI hq)⟩

end LabelCover
end VertexCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_RejectionCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.ClauseProjection

abbrev Pattern := {s : Fin 3 → Bool // ∃ k, s k = true}

instance instFintypePattern : Fintype Pattern := inferInstanceAs (Fintype {s : Fin 3 → Bool // ∃ k, s k = true})

theorem pattern_card : Fintype.card Pattern = 7 := by decide

noncomputable def patternEquiv : Pattern ≃ Fin 7 :=
  (Fintype.equivFin Pattern).trans (finCongr pattern_card)

def flipSign (positive b : Bool) : Bool := if positive then b else !b

@[simp] theorem flipSign_flipSign (p b : Bool) : flipSign p (flipSign p b) = b := by
  cases p <;> cases b <;> rfl

end VertexCover.ClauseProjection


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_BaseReductionCoherent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

theorem value_le_of_counts (Φ : LabelCover) (σ : ℝ)
    (h : ∀ A : Φ.Labeling, (Φ.satisfiedCount A : ℝ) ≤ σ * Φ.M) : Φ.value ≤ σ := by
  classical
  obtain ⟨A, _, hA⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset Φ.Labeling)
    ⟨Φ.defaultLabeling, Finset.mem_univ _⟩ Φ.satisfiedCount
  apply (div_le_iff₀ (Nat.cast_pos.mpr Φ.M_pos)).mpr
  change ((Finset.univ.sup Φ.satisfiedCount : ℕ) : ℝ) ≤ _
  rw [hA]
  exact h A

def ParallelCoherent (Φ : LabelCover) : Prop :=
  ∀ e e', Φ.left e = Φ.left e' → Φ.right e = Φ.right e' → Φ.projection e = Φ.projection e'

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_PoincareOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Cube
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def intervalLaw : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • volume.restrict (Set.Icc (-1 : ℝ) 1)

instance instIsProbabilityMeasureRealIntervalLaw : IsProbabilityMeasure intervalLaw := by
  constructor
  norm_num [intervalLaw, Measure.smul_apply, Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem integral_intervalLaw (f : ℝ → ℝ) :
    ∫ x, f x ∂intervalLaw = (1/2 : ℝ) * ∫ x in Set.Icc (-1 : ℝ) 1, f x := by
  simp [intervalLaw, integral_smul_measure]

noncomputable def law (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => intervalLaw)

instance law_probability (ι : Type*) [Fintype ι] : IsProbabilityMeasure (law ι) := by
  unfold law
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

end VertexCover.Cube

namespace VertexCover.Cube
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem sq_integral_le_measure_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ)^2 ≤ μ.real Set.univ * ∫ x, (f x)^2 ∂μ := by
  have ha := norm_integral_le_integral_norm (μ := μ) f
  have hb := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
    (f := f) (g := fun _ => (1 : ℝ)) (by simpa using hf) (by simpa using memLp_const (1 : ℝ))
  simp only [Real.norm_eq_abs, abs_one, mul_one, Real.rpow_two, sq_abs,
    integral_const, smul_eq_mul, mul_one, one_pow] at hb
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hb
  have hz : 0 ≤ ∫ x, (f x)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hm : 0 ≤ μ.real Set.univ := ENNReal.toReal_nonneg
  have hc : |∫ x, f x ∂μ| ≤ Real.sqrt (∫ x, (f x)^2 ∂μ) * Real.sqrt (μ.real Set.univ) :=
    (show |∫ x, f x ∂μ| ≤ ∫ x, ‖f x‖ ∂μ from ha).trans hb
  have hd := sq_le_sq₀ (abs_nonneg (∫ x, f x ∂μ))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) |>.mpr hc
  simpa only [sq_abs, mul_pow, Real.sq_sqrt hz, Real.sq_sqrt hm, mul_comm] using hd

end VertexCover.Cube

namespace VertexCover.Cube
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem deriv_memLp {w : ℝ → ℝ} {C : NNReal} (hw : LipschitzWith C w)
    (a b : ℝ) : MemLp (deriv w) 2 (volume.restrict (Set.Icc a b)) := by
  exact MemLp.of_bound (measurable_deriv w).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun _ => norm_deriv_le_of_lipschitz hw))

theorem anchored_sq_le {w : ℝ → ℝ} {C : NNReal} (hw : LipschitzWith C w)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (w x - w 0)^2 ≤ ∫ y in Set.Icc (-1 : ℝ) 1, (deriv w y)^2 := by
  let a := min (0 : ℝ) x
  let b := max (0 : ℝ) x
  have hab : a ≤ b := (min_le_left _ _).trans (le_max_left _ _)
  have hlen : b - a ≤ 1 := by
    dsimp [a, b]
    rcases le_total 0 x with h | h
    · rw [min_eq_left h, max_eq_right h]; linarith [hx.2]
    · rw [min_eq_right h, max_eq_left h]; linarith [hx.1]
  have hsub : Set.Icc a b ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro y hy
    exact ⟨(le_min (by norm_num) hx.1).trans hy.1,
      hy.2.trans (max_le (by norm_num) hx.2)⟩
  have hftc := (hw.lipschitzOnWith (s := Set.uIcc (0 : ℝ) x)).absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have heq : (w x - w 0)^2 = (∫ y in Set.Icc a b, deriv w y)^2 := by
    rw [← hftc]
    rcases le_total 0 x with h | h
    · rw [intervalIntegral.integral_of_le h, ← integral_Icc_eq_integral_Ioc]
      simp [a, b, min_eq_left h, max_eq_right h]
    · rw [intervalIntegral.integral_of_ge h, ← integral_Icc_eq_integral_Ioc]
      simp [a, b, min_eq_right h, max_eq_left h]
  rw [heq]
  have hcs := sq_integral_le_measure_mul (volume.restrict (Set.Icc a b)) (deriv_memLp hw a b)
  have hm : (volume.restrict (Set.Icc a b)).real Set.univ = b - a := by
    simp [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [hm] at hcs
  have hnon : 0 ≤ ∫ y in Set.Icc a b, (deriv w y)^2 := integral_nonneg (fun _ => sq_nonneg _)
  refine hcs.trans ((mul_le_of_le_one_left hnon hlen).trans ?_)
  exact setIntegral_mono_set (deriv_memLp hw (-1) 1).integrable_sq
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall hsub)

theorem poincare_one {w : ℝ → ℝ} {C : NNReal} (hw : LipschitzWith C w) :
    variance w intervalLaw ≤ 2 * ∫ x, (deriv w x)^2 ∂intervalLaw := by
  have hm : AEStronglyMeasurable w intervalLaw := hw.continuous.measurable.aestronglyMeasurable
  have hs : AEStronglyMeasurable (fun x => w x - w 0) intervalLaw := hm.sub aestronglyMeasurable_const
  have hi : Integrable (fun x => (w x - w 0)^2) intervalLaw := by
    exact ((hw.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_Icc.smul_measure (by norm_num)
  have hbound : (fun x => (w x - w 0)^2) ≤ᵐ[intervalLaw]
      (fun _ => ∫ y in Set.Icc (-1 : ℝ) 1, (deriv w y)^2) := by
    have hae : ∀ᵐ x ∂intervalLaw, x ∈ Set.Icc (-1 : ℝ) 1 := by
      exact (Measure.ae_ennreal_smul_measure_iff (by norm_num : (1/2 : ℝ≥0∞) ≠ 0)).mpr
        (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hae] with x hx
    exact anchored_sq_le hw hx
  calc
    variance w intervalLaw = variance (fun x => w x - w 0) intervalLaw :=
      (variance_sub_const hm (w 0)).symm
    _ ≤ ∫ x, (w x - w 0)^2 ∂intervalLaw := variance_le_expectation_sq hs
    _ ≤ ∫ x, (∫ y in Set.Icc (-1 : ℝ) 1, (deriv w y)^2) ∂intervalLaw :=
      integral_mono_ae hi (integrable_const _) hbound
    _ = 2 * ∫ x, (deriv w x)^2 ∂intervalLaw := by
      rw [integral_const, integral_intervalLaw]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      ring

end VertexCover.Cube


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_BlockLawAc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Cube
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem law_eq_restrict_volume (ι : Type*) [Fintype ι] :
    law ι = (1/2 : ℝ≥0∞) ^ Fintype.card ι •
    volume.restrict (Set.univ.pi (fun _ : ι => Set.Icc (-1 : ℝ) 1)) := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs),
    ← Set.pi_inter_distrib, volume_pi_pi]
  simp only [intervalLaw, Measure.smul_apply, Measure.restrict_apply (hs _),
    smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end VertexCover.Cube

namespace VertexCover.Cube
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def blockLaw (ι κ : Type*) [Fintype ι] [Fintype κ] :
    Measure (ι → κ → ℝ) := Measure.pi (fun _ : ι => law κ)

instance blockLaw_probability (ι κ : Type*) [Fintype ι] [Fintype κ] :
    IsProbabilityMeasure (blockLaw ι κ) := by
  unfold blockLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

theorem blockLaw_eq_restrict_volume (ι κ : Type*) [Fintype ι] [Fintype κ] :
    blockLaw ι κ = ((1/2 : ℝ≥0∞) ^ Fintype.card κ) ^ Fintype.card ι •
      volume.restrict (Set.univ.pi (fun _ : ι =>
        Set.univ.pi (fun _ : κ => Set.Icc (-1 : ℝ) 1))) := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs),
    ← Set.pi_inter_distrib, volume_pi_pi]
  simp only [law_eq_restrict_volume, Measure.smul_apply,
    Measure.restrict_apply (hs _), smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

theorem blockLaw_ac (ι κ : Type*) [Fintype ι] [Fintype κ] :
    blockLaw ι κ ≪ volume := by
  rw [blockLaw_eq_restrict_volume]
  intro s hs
  have hz : volume.restrict (Set.univ.pi (fun _ : ι =>
      Set.univ.pi (fun _ : κ => Set.Icc (-1 : ℝ) 1))) s = 0 :=
    le_antisymm ((Measure.restrict_le_self s).trans_eq hs) zero_le
  simp only [Measure.smul_apply, hz, smul_zero]

end VertexCover.Cube


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_HonestSelectionCompatible
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

abbrev PositionPair (d : ℕ) := {jk : Fin d × Fin d // jk.1 < jk.2}
abbrev Seeds (Φ : LabelCover) (d : ℕ) := PositionPair d → Fin Φ.M

def query (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d) (j : Fin d) : Φ.Query d :=
  ⟨j, (fun k => Φ.left (seed ⟨(j, k.1), k.2⟩)),
    (fun k => Φ.right (seed ⟨(k.1, j), k.2⟩))⟩

namespace Query

theorem scope_card_le {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) :
    i.scopeU.card + i.scopeV.card ≤ d - 1 := by
  have hU : i.scopeU.card ≤ d - 1 - i.1.val := by
    calc
      i.scopeU.card ≤ Fintype.card {k : Fin d // i.1 < k} := Finset.card_image_le
      _ = (Finset.Ioi i.1).card := by simp [Fintype.card_subtype, Finset.filter_lt_eq_Ioi]
      _ = d - 1 - i.1.val := Fin.card_Ioi i.1
  have hV : i.scopeV.card ≤ i.1.val := by
    calc
      i.scopeV.card ≤ Fintype.card {k : Fin d // k < i.1} := Finset.card_image_le
      _ = (Finset.Iio i.1).card := by simp [Fintype.card_subtype, Finset.filter_gt_eq_Iio]
      _ = i.1.val := Fin.card_Iio i.1
  have := i.1.isLt
  omega

theorem localLabel_card_le {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) :
    Fintype.card i.LocalLabel ≤ (max Φ.qU Φ.qV)^(d - 1) := by
  let q := max Φ.qU Φ.qV
  have hq : 0 < q := lt_of_lt_of_le Φ.qU_pos (le_max_left _ _)
  calc
    Fintype.card i.LocalLabel ≤ Fintype.card i.Assignment := Fintype.card_subtype_le _
    _ = Φ.qU^i.scopeU.card * Φ.qV^i.scopeV.card := by
      simp [Assignment, Fintype.card_prod, ]
    _ ≤ q^i.scopeU.card * q^i.scopeV.card :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (le_max_left _ _) _)
        (Nat.pow_le_pow_left (le_max_right _ _) _)
    _ = q^(i.scopeU.card + i.scopeV.card) := (pow_add _ _ _).symm
    _ ≤ q^(d - 1) := Nat.pow_le_pow_right hq i.scope_card_le

end Query

def localOfSatisfying (Φ : LabelCover) (A : Φ.Labeling)
    (hA : ∀ c, Φ.Satisfies A c) {d : ℕ} (i : Φ.Query d) : i.LocalLabel :=
  ⟨(fun x => A.1 x.1, fun y => A.2 y.1), fun c _ _ => hA c⟩

def honestSelection (Φ : LabelCover) (A : Φ.Labeling)
    (hA : ∀ c, Φ.Satisfies A c) (d : ℕ) : Finset (Φ.Coordinate d) :=
  Finset.univ.image (fun i => ⟨i, Φ.localOfSatisfying A hA i⟩)

theorem honestSelection_compatible (Φ : LabelCover) (A : Φ.Labeling)
    (hA : ∀ c, Φ.Satisfies A c) (d : ℕ) :
    Φ.Compatible (Φ.honestSelection A hA d) := by
  classical
  have shape : ∀ p ∈ Φ.honestSelection A hA d,
      p = ⟨p.1, Φ.localOfSatisfying A hA p.1⟩ := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp q hq heq
    calc
      p = ⟨p.1, Φ.localOfSatisfying A hA p.1⟩ := shape p hp
      _ = ⟨q.1, Φ.localOfSatisfying A hA q.1⟩ :=
        congrArg (fun i => (⟨i, Φ.localOfSatisfying A hA i⟩ : Φ.Coordinate d)) heq
      _ = q := (shape q hq).symm
  · intro p hp q hq x hx hy
    have ep := shape p hp
    have eq := shape q hq
    cases p with | mk i a =>
      cases q with | mk j b =>
        simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at ep eq
        subst a; subst b; rfl
  · intro p hp q hq y hx hy
    have ep := shape p hp
    have eq := shape q hq
    cases p with | mk i a =>
      cases q with | mk j b =>
        simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at ep eq
        subst a; subst b; rfl
  · intro p hp q hq c hx hy
    have ep := shape p hp
    have eq := shape q hq
    cases p with | mk i a =>
      cases q with | mk j b =>
        simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at ep eq
        subst a; subst b
        exact hA c

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_NormAttainedSupport
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

noncomputable def compatibleSelections (Φ : LabelCover) (d : ℕ) :
    Finset (Finset (Φ.Coordinate d)) := by
  classical
  exact Finset.univ.filter Φ.Compatible

@[simp] theorem mem_compatibleSelections (Φ : LabelCover) {d : ℕ}
    (I : Finset (Φ.Coordinate d)) : I ∈ Φ.compatibleSelections d ↔ Φ.Compatible I := by
  classical
  simp [compatibleSelections]

theorem compatible_empty (Φ : LabelCover) (d : ℕ) :
    Φ.Compatible (∅ : Finset (Φ.Coordinate d)) := by
  simp [Compatible]

theorem compatibleSelections_nonempty (Φ : LabelCover) (d : ℕ) :
    (Φ.compatibleSelections d).Nonempty :=
  ⟨∅, (mem_compatibleSelections Φ ∅).mpr (Φ.compatible_empty d)⟩

noncomputable def compatibilityNorm (Φ : LabelCover) {d : ℕ}
    (z : Φ.Coordinate d → ℝ) : ℝ :=
  (Φ.compatibleSelections d).sup' (Φ.compatibleSelections_nonempty d)
    (fun I => |∑ p ∈ I, z p|)

theorem form_le_norm (Φ : LabelCover) {d : ℕ} (z : Φ.Coordinate d → ℝ)
    (I : Finset (Φ.Coordinate d)) (hI : Φ.Compatible I) :
    |∑ p ∈ I, z p| ≤ Φ.compatibilityNorm z := by
  exact Finset.le_sup' (fun J : Finset (Φ.Coordinate d) => |∑ p ∈ J, z p|)
    ((mem_compatibleSelections Φ I).mpr hI)

theorem norm_le_iff (Φ : LabelCover) {d : ℕ} (z : Φ.Coordinate d → ℝ) (b : ℝ) :
    Φ.compatibilityNorm z ≤ b ↔ ∀ I, Φ.Compatible I → |∑ p ∈ I, z p| ≤ b := by
  constructor
  · intro hb I hI
    exact (Φ.form_le_norm z I hI).trans hb
  · intro h
    exact Finset.sup'_le _ _ (fun I hI => h I ((mem_compatibleSelections Φ I).mp hI))

theorem norm_nonneg (Φ : LabelCover) {d : ℕ} (z : Φ.Coordinate d → ℝ) :
    0 ≤ Φ.compatibilityNorm z := by
  simpa using Φ.form_le_norm z ∅ (Φ.compatible_empty d)

theorem norm_zero (Φ : LabelCover) (d : ℕ) :
    Φ.compatibilityNorm (fun _ : Φ.Coordinate d => (0 : ℝ)) = 0 := by
  apply le_antisymm ((Φ.norm_le_iff _ _).mpr ?_) (Φ.norm_nonneg _)
  intro I _
  simp

theorem norm_add_le (Φ : LabelCover) {d : ℕ} (z w : Φ.Coordinate d → ℝ) :
    Φ.compatibilityNorm (z + w) ≤ Φ.compatibilityNorm z + Φ.compatibilityNorm w := by
  apply (Φ.norm_le_iff _ _).mpr
  intro I hI
  calc
    |∑ p ∈ I, (z + w) p| = |(∑ p ∈ I, z p) + ∑ p ∈ I, w p| := by
      simp only [Pi.add_apply, Finset.sum_add_distrib]
    _ ≤ |∑ p ∈ I, z p| + |∑ p ∈ I, w p| := abs_add_le _ _
    _ ≤ Φ.compatibilityNorm z + Φ.compatibilityNorm w :=
      add_le_add (Φ.form_le_norm z I hI) (Φ.form_le_norm w I hI)

theorem norm_mul (Φ : LabelCover) {d : ℕ} (a : ℝ) (z : Φ.Coordinate d → ℝ) :
    Φ.compatibilityNorm (fun p => a * z p) = |a| * Φ.compatibilityNorm z := by
  apply le_antisymm
  · apply (Φ.norm_le_iff _ _).mpr
    intro I hI
    rw [← Finset.mul_sum, abs_mul]
    exact mul_le_mul_of_nonneg_left (Φ.form_le_norm z I hI) (abs_nonneg a)
  · obtain ⟨I, hI, hmax⟩ := Finset.exists_mem_eq_sup'
      (Φ.compatibleSelections_nonempty d) (fun I => |∑ p ∈ I, z p|)
    change Φ.compatibilityNorm z = _ at hmax
    rw [hmax]
    have hh := Φ.form_le_norm (fun p => a * z p) I ((mem_compatibleSelections Φ I).mp hI)
    simpa only [← Finset.mul_sum, abs_mul] using hh

theorem norm_neg (Φ : LabelCover) {d : ℕ} (z : Φ.Coordinate d → ℝ) :
    Φ.compatibilityNorm (-z) = Φ.compatibilityNorm z := by
  change Φ.compatibilityNorm (fun p => -z p) = Φ.compatibilityNorm z
  simpa only [neg_one_mul, abs_neg, abs_one, one_mul] using Φ.norm_mul (-1) z

theorem norm_attained_on_support (Φ : LabelCover) {d : ℕ}
    (z : Φ.Coordinate d → ℝ) (B : Finset (Φ.Query d))
    (hz : ∀ p, p.1 ∉ B → z p = 0) :
    ∃ I : Finset (Φ.Coordinate d), Φ.Compatible I ∧
      (∀ p ∈ I, p.1 ∈ B) ∧ Φ.compatibilityNorm z = |∑ p ∈ I, z p| := by
  classical
  obtain ⟨J, hJ, heq⟩ := Finset.exists_mem_eq_sup'
    (Φ.compatibleSelections_nonempty d) (fun I => |∑ p ∈ I, z p|)
  let I := J.filter (fun p => p.1 ∈ B)
  have hIJ : I ⊆ J := Finset.filter_subset _ _
  refine ⟨I, Φ.compatible_mono ((mem_compatibleSelections Φ J).mp hJ) hIJ,
    fun p hp => (Finset.mem_filter.mp hp).2, ?_⟩
  change Φ.compatibilityNorm z = _ at heq
  rw [heq]
  congr 1
  symm
  apply Finset.sum_subset hIJ
  intro p hp hpI
  apply hz p
  intro hpB
  exact hpI (Finset.mem_filter.mpr ⟨hp, hpB⟩)

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_IncrementNorm
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
namespace Query

noncomputable abbrev localLabelLinearOrder {Φ : LabelCover} {d : ℕ}
    (i : Φ.Query d) : LinearOrder i.LocalLabel :=
  LinearOrder.lift'
    (fun a : i.LocalLabel => toLex (toLex a.1.1, toLex a.1.2))
    (fun _ _ h => Subtype.ext h)

noncomputable def labels {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) : List i.LocalLabel := by
  letI : LinearOrder i.LocalLabel := localLabelLinearOrder i
  exact (Finset.univ : Finset i.LocalLabel).sort (localLabelLinearOrder i).le

@[simp] theorem mem_labels {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) (a : i.LocalLabel) :
    a ∈ i.labels := by
  simp [labels]

@[simp] theorem labels_length {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) :
    i.labels.length = Fintype.card i.LocalLabel := by
  simp [labels]

noncomputable def slot {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) (a : i.LocalLabel) :
    Fin ((max Φ.qU Φ.qV)^(d - 1)) :=
  ⟨i.labels.idxOf a, lt_of_lt_of_le
    (by simpa only [labels_length] using List.idxOf_lt_length_iff.mpr (i.mem_labels a))
    i.localLabel_card_le⟩

theorem slot_injective {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) :
    Function.Injective i.slot := by
  intro a b h
  exact (List.idxOf_inj (i.mem_labels a)).mp (congrArg Fin.val h)

end Query

abbrev WeightDimension (Φ : LabelCover) (d : ℕ) := (max Φ.qU Φ.qV)^(d - 1)

noncomputable def increment (Φ : LabelCover) {d : ℕ} (i : Φ.Query d)
    (s : Fin (Φ.WeightDimension d) → ℝ) : Φ.Coordinate d → ℝ :=
  fun p => (Pi.single (M := fun j : Φ.Query d => j.LocalLabel → ℝ)
    i (fun a => s (i.slot a)) p.1) p.2

@[simp] theorem increment_same (Φ : LabelCover) {d : ℕ} (i : Φ.Query d)
    (s : Fin (Φ.WeightDimension d) → ℝ) (a : i.LocalLabel) :
    Φ.increment i s ⟨i, a⟩ = s (i.slot a) := by
  simp [increment]

theorem increment_other (Φ : LabelCover) {d : ℕ} (i : Φ.Query d)
    (s : Fin (Φ.WeightDimension d) → ℝ) (p : Φ.Coordinate d) (h : p.1 ≠ i) :
    Φ.increment i s p = 0 := by
  simp [increment, Pi.single_eq_of_ne h]

theorem increment_add (Φ : LabelCover) {d : ℕ} (i : Φ.Query d)
    (s t : Fin (Φ.WeightDimension d) → ℝ) :
    Φ.increment i (s + t) = Φ.increment i s + Φ.increment i t := by
  funext p
  rcases p with ⟨j, a⟩
  by_cases h : j = i
  · subst j
    simp
  · simp [Φ.increment_other i _ ⟨j, a⟩ h]

theorem increment_mul (Φ : LabelCover) {d : ℕ} (i : Φ.Query d) (a : ℝ)
    (s : Fin (Φ.WeightDimension d) → ℝ) :
    Φ.increment i (fun k => a * s k) = fun p => a * Φ.increment i s p := by
  funext p
  rcases p with ⟨j, b⟩
  by_cases h : j = i
  · subst j
    simp
  · simp [Φ.increment_other i _ ⟨j, b⟩ h]

theorem increment_norm_le (Φ : LabelCover) {d : ℕ} (i : Φ.Query d)
    (s : Fin (Φ.WeightDimension d) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hs : ∀ k, |s k| ≤ B) : Φ.compatibilityNorm (Φ.increment i s) ≤ B := by
  classical
  apply (Φ.norm_le_iff _ _).mpr
  intro I hI
  by_cases hex : ∃ p ∈ I, p.1 = i
  · obtain ⟨p, hp, hip⟩ := hex
    have heq : (∑ q ∈ I, Φ.increment i s q) = Φ.increment i s p := by
      apply Finset.sum_eq_single p
      · intro q hq hqp
        apply Φ.increment_other
        intro hqi
        exact hqp (hI.1 q hq p hp (hqi.trans hip.symm))
      · intro hn
        exact (hn hp).elim
    rw [heq]
    rcases p with ⟨j, a⟩
    change j = i at hip
    subst j
    simpa using hs (i.slot a)
  · have hz : ∀ p ∈ I, Φ.increment i s p = 0 := by
      intro p hp
      exact Φ.increment_other i s p (fun h => hex ⟨p, hp, h⟩)
    simpa [Finset.sum_eq_zero hz] using hB

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_PairHitsProbability
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
namespace Decoding

variable (Φ : LabelCover) {d : ℕ}
variable (iU : Fin Φ.u → Φ.Query d) (iV : Fin Φ.v → Φ.Query d)
variable (pU : ∀ x, x ∈ (iU x).scopeU) (pV : ∀ y, y ∈ (iV y).scopeV)
variable (LU : ∀ x, List (iU x).LocalLabel) (LV : ∀ y, List (iV y).LocalLabel)

def leftAt (ρ : ℕ) (x : Fin Φ.u) : Fin Φ.qU :=
  if h : ρ < (LU x).length then ((LU x)[ρ]).1.1 ⟨x, pU x⟩ else ⟨0, Φ.qU_pos⟩

def rightAt (τ : ℕ) (y : Fin Φ.v) : Fin Φ.qV :=
  if h : τ < (LV y).length then ((LV y)[τ]).1.2 ⟨y, pV y⟩ else ⟨0, Φ.qV_pos⟩

def PairHit (c : Fin Φ.M) : Prop :=
  ∃ labU ∈ LU (Φ.left c), ∃ labV ∈ LV (Φ.right c),
    Φ.Compatible {⟨iU (Φ.left c), labU⟩, ⟨iV (Φ.right c), labV⟩}

noncomputable def pairHits : Finset (Fin Φ.M) := by
  classical
  exact Finset.univ.filter (PairHit Φ iU iV LU LV)

end Decoding
end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_PairSeedFiberCard
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

def leftTemplate (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (e : PositionPair d) (x : Fin Φ.u) : Φ.Query d :=
  ⟨e.1.1, Function.update (Φ.query seed e.1.1).2.1 ⟨e.1.2, e.2⟩ x,
    (Φ.query seed e.1.1).2.2⟩

def rightTemplate (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (e : PositionPair d) (y : Fin Φ.v) : Φ.Query d :=
  ⟨e.1.2, (Φ.query seed e.1.2).2.1,
    Function.update (Φ.query seed e.1.2).2.2 ⟨e.1.1, e.2⟩ y⟩

theorem leftTemplate_mem (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (e : PositionPair d) (x : Fin Φ.u) : x ∈ (Φ.leftTemplate seed e x).scopeU := by
  refine Finset.mem_image.mpr ⟨⟨e.1.2, e.2⟩, Finset.mem_univ _, ?_⟩
  exact Function.update_self _ _ _

theorem rightTemplate_mem (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (e : PositionPair d) (y : Fin Φ.v) : y ∈ (Φ.rightTemplate seed e y).scopeV := by
  refine Finset.mem_image.mpr ⟨⟨e.1.1, e.2⟩, Finset.mem_univ _, ?_⟩
  exact Function.update_self _ _ _

def replaceSeed (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (e : PositionPair d) (c : Fin Φ.M) : Φ.Seeds d :=
  Function.update seed e c

abbrev PrivateLists (Φ : LabelCover) (d : ℕ) := ∀ i : Φ.Query d, List i.LocalLabel

def PairSeedHit (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (e : PositionPair d) : Prop :=
  ∃ a ∈ L (Φ.query seed e.1.1), ∃ b ∈ L (Φ.query seed e.1.2),
    Φ.Compatible {⟨Φ.query seed e.1.1, a⟩, ⟨Φ.query seed e.1.2, b⟩}

noncomputable def pairSeedFiber (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (e : PositionPair d) : Finset (Fin Φ.M) := by
  classical
  exact Finset.univ.filter (fun c => Φ.PairSeedHit L (Φ.replaceSeed seed e c) e)

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_ListHitMaximum
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
attribute [-simp] _root_.OAI.VertexCover.LabelCover.Query.labels_length _root_.OAI.VertexCover.LabelCover.Query.mem_labels _root_.OAI.VertexCover.LabelCover.increment_same
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

def ListHit (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (I : Finset (Φ.Coordinate d)) (j : Fin d) : Prop :=
  ∃ a ∈ L (Φ.query seed j), (⟨Φ.query seed j, a⟩ : Φ.Coordinate d) ∈ I

noncomputable def hitPositions (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (I : Finset (Φ.Coordinate d)) (J : Finset (Fin d)) : Finset (Fin d) := by
  classical
  exact J.filter (Φ.ListHit L seed I)

noncomputable def pairEvents (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (J : Finset (Fin d)) : Finset (PositionPair d) := by
  classical
  exact Finset.univ.filter (fun e => e.1.1 ∈ J ∧ e.1.2 ∈ J ∧ Φ.PairSeedHit L seed e)

theorem pairSeedHit_of_hits (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) {I : Finset (Φ.Coordinate d)} (hI : Φ.Compatible I)
    (e : PositionPair d) (hj : Φ.ListHit L seed I e.1.1)
    (hk : Φ.ListHit L seed I e.1.2) : Φ.PairSeedHit L seed e := by
  classical
  obtain ⟨a, haL, haI⟩ := hj
  obtain ⟨b, hbL, hbI⟩ := hk
  refine ⟨a, haL, b, hbL, Φ.compatible_mono hI ?_⟩
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact haI
  · exact hbI

theorem hitPositions_card_le (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (I : Finset (Φ.Coordinate d)) (hI : Φ.Compatible I)
    (J : Finset (Fin d)) :
    (Φ.hitPositions L seed I J).card ≤ 1 + (Φ.pairEvents L seed J).card := by
  classical
  let A := Φ.hitPositions L seed I J
  by_cases hA : A.Nonempty
  · let j := A.min' hA
    have hj : j ∈ A := Finset.min'_mem _ _
    have keep : ∀ k : ↥(A.erase j), j < k.1 := by
      intro k
      have hk := Finset.mem_erase.mp k.2
      exact lt_of_le_of_ne (Finset.min'_le A k.1 hk.2) (Ne.symm hk.1)
    let inject : ↥(A.erase j) → ↥(Φ.pairEvents L seed J) := fun k =>
      ⟨⟨(j, k.1), keep k⟩, by
        have hmj := Finset.mem_filter.mp hj
        have hmk := Finset.mem_filter.mp (Finset.mem_erase.mp k.2).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmj.1, hmk.1,
          Φ.pairSeedHit_of_hits L seed hI _ hmj.2 hmk.2⟩⟩
    have hinj : Function.Injective inject := by
      intro k l h
      apply Subtype.ext
      exact congrArg (fun e : ↥(Φ.pairEvents L seed J) => e.1.1.2) h
    have hcard := Fintype.card_le_of_injective inject hinj
    simp only [Fintype.card_coe] at hcard
    have herase := Finset.card_erase_add_one hj
    change A.card ≤ _
    omega
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change A.card ≤ _
    simp [he]

noncomputable def listHitMaximum (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (J : Finset (Fin d)) : ℕ :=
  (Φ.compatibleSelections d).sup (fun I => (Φ.hitPositions L seed I J).card)

theorem listHitMaximum_le (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (J : Finset (Fin d)) :
    Φ.listHitMaximum L seed J ≤ 1 + (Φ.pairEvents L seed J).card := by
  classical
  apply Finset.sup_le
  intro I hI
  exact Φ.hitPositions_card_le L seed I ((Φ.mem_compatibleSelections I).mp hI) J

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_PairEventMean
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
attribute [-simp] _root_.OAI.VertexCover.LabelCover.Query.labels_length _root_.OAI.VertexCover.LabelCover.Query.mem_labels _root_.OAI.VertexCover.LabelCover.increment_same _root_.OAI.VertexCover.LabelCover.mem_compatibleSelections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover

noncomputable def updateSwap {ι α : Type*} [DecidableEq ι] (j : ι) :
    ((ι → α) × α) ≃ ((ι → α) × α) where
  toFun p := (Function.update p.1 j p.2, p.1 j)
  invFun p := (Function.update p.1 j p.2, p.1 j)
  left_inv p := by
    apply Prod.ext
    · funext k
      by_cases h : k = j <;> simp [h]
    · simp
  right_inv p := by
    apply Prod.ext
    · funext k
      by_cases h : k = j <;> simp [h]
    · simp

theorem sum_updates {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (j : ι) (f : (ι → α) → ℝ) :
    (∑ seed : ι → α, ∑ a : α, f (Function.update seed j a)) =
      Fintype.card α * ∑ seed : ι → α, f seed := by
  classical
  have he := (updateSwap (α := α) j).sum_comp (fun p => f p.1)
  simp only [Fintype.sum_prod_type, updateSwap, Equiv.coe_fn_mk] at he
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] using he

end VertexCover

namespace VertexCover.LabelCover

noncomputable def internalPairs {d : ℕ} (J : Finset (Fin d)) : Finset (PositionPair d) := by
  classical
  exact Finset.univ.filter (fun e => e.1.1 ∈ J ∧ e.1.2 ∈ J)

abbrev HiddenSeeds (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d)) :=
  ↥(internalPairs J) → Fin Φ.M

noncomputable def spliceSeeds (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (hidden : Φ.HiddenSeeds J) : Φ.Seeds d := by
  classical
  exact fun e => if h : e ∈ internalPairs J then hidden ⟨e, h⟩ else frozen e

theorem spliceSeeds_update (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (hidden : Φ.HiddenSeeds J) (e : ↥(internalPairs J))
    (c : Fin Φ.M) :
    Φ.spliceSeeds J frozen (Function.update hidden e c) =
      Φ.replaceSeed (Φ.spliceSeeds J frozen hidden) e.1 c := by
  classical
  funext pair
  by_cases hp : pair = e.1
  · subst pair
    simp [spliceSeeds, replaceSeed, e.2]
  · by_cases hj : pair ∈ internalPairs J
    · have hne : (⟨pair, hj⟩ : ↥(internalPairs J)) ≠ e := by
        intro h
        exact hp (congrArg Subtype.val h)
      simp [spliceSeeds, replaceSeed, hp, hj, hne]
    · simp [spliceSeeds, replaceSeed, hp, hj]

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_ListMassHitMaximum
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

noncomputable def listMass (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (J : Finset (Fin d))
    (g : Fin d → Fin (Φ.WeightDimension d) → ℝ) : ℝ :=
  ∑ j ∈ J, ∑ a ∈ (L (Φ.query seed j)).toFinset, |g j ((Φ.query seed j).slot a)|

theorem listMass_convex_sublevel (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (J : Finset (Fin d)) (C : ℝ) :
    Convex ℝ {g | Φ.listMass L seed J g ≤ C} := by
  classical
  intro x hx y hy a b ha hb hab
  change Φ.listMass L seed J (a • x + b • y) ≤ C
  calc
    _ ≤ ∑ j ∈ J, ∑ z ∈ (L (Φ.query seed j)).toFinset,
        (a * |x j ((Φ.query seed j).slot z)| + b * |y j ((Φ.query seed j).slot z)|) := by
      apply Finset.sum_le_sum; intro j hj
      apply Finset.sum_le_sum; intro z hz
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg ha, abs_of_nonneg hb] using
        abs_add_le (a*x j ((Φ.query seed j).slot z)) (b*y j ((Φ.query seed j).slot z))
    _ = a * Φ.listMass L seed J x + b * Φ.listMass L seed J y := by
      simp [listMass, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ a*C + b*C := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
    _ = C := by rw [← add_mul, hab, one_mul]

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_HonestLargeSumIndependent
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

def gridRational (d : ℕ) (v : Fin (2*d+1)) : ℚ :=
  2 * ((v.val : ℚ) - d) / (2*d+1)

abbrev Vertex (Φ : LabelCover) (d : ℕ) :=
  Φ.Seeds d × (Fin d → Fin (Φ.WeightDimension d) → Fin (2*d+1))

noncomputable def sumVector (Φ : LabelCover) {d : ℕ} (v : Φ.Vertex d) :
    Φ.Coordinate d → ℝ :=
  ∑ j, Φ.increment (Φ.query v.1 j) (fun k => (gridRational d (v.2 j k) : ℝ))

noncomputable def graph (Φ : LabelCover) (d : ℕ) (t : ℝ) : SimpleGraph (Φ.Vertex d) where
  Adj v w := v ≠ w ∧ Φ.compatibilityNorm (Φ.sumVector v + Φ.sumVector w) ≤ 2*t
  symm := ⟨by intro v w h; exact ⟨h.1.symm, by simpa only [add_comm] using h.2⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

theorem low_norm_adjacent (Φ : LabelCover) {d : ℕ} {t : ℝ} {v w : Φ.Vertex d}
    (hne : v ≠ w) (hv : Φ.compatibilityNorm (Φ.sumVector v) ≤ t)
    (hw : Φ.compatibilityNorm (Φ.sumVector w) ≤ t) : (Φ.graph d t).Adj v w := by
  refine ⟨hne, (Φ.norm_add_le _ _).trans ?_⟩
  linarith

theorem low_norm_subsingleton (Φ : LabelCover) {d : ℕ} {t : ℝ}
    (A : Set (Φ.Vertex d)) (hA : (Φ.graph d t).IsIndepSet A) :
    {v ∈ A | Φ.compatibilityNorm (Φ.sumVector v) ≤ t}.Subsingleton := by
  intro v hv w hw
  by_contra hne
  exact ((SimpleGraph.isIndepSet_iff _).mp hA hv.1 hw.1 hne)
    (Φ.low_norm_adjacent hne hv.2 hw.2)

theorem honestSelection_form_increment (Φ : LabelCover) {d : ℕ}
    (A : Φ.Labeling) (hA : ∀ c, Φ.Satisfies A c) (i : Φ.Query d)
    (s : Fin (Φ.WeightDimension d) → ℝ) :
    ∑ p ∈ Φ.honestSelection A hA d, Φ.increment i s p =
      s (i.slot (Φ.localOfSatisfying A hA i)) := by
  classical
  unfold honestSelection
  rw [Finset.sum_image]
  · have hz : ∀ j : Φ.Query d, Φ.increment i s ⟨j, Φ.localOfSatisfying A hA j⟩ =
        if j = i then s (i.slot (Φ.localOfSatisfying A hA i)) else 0 := by
      intro j
      split_ifs with h
      · subst j; exact Φ.increment_same _ _ _
      · exact Φ.increment_other _ _ _ h
    simp only [hz]
    simp
  · intro i _ j _ h
    exact congrArg Sigma.fst h

noncomputable def honestSum (Φ : LabelCover) {d : ℕ} (A : Φ.Labeling)
    (hA : ∀ c, Φ.Satisfies A c) (v : Φ.Vertex d) : ℝ :=
  ∑ j, (gridRational d (v.2 j ((Φ.query v.1 j).slot
    (Φ.localOfSatisfying A hA (Φ.query v.1 j)))) : ℝ)

theorem honestSelection_form_sumVector (Φ : LabelCover) {d : ℕ}
    (A : Φ.Labeling) (hA : ∀ c, Φ.Satisfies A c) (v : Φ.Vertex d) :
    ∑ p ∈ Φ.honestSelection A hA d, Φ.sumVector v p = Φ.honestSum A hA v := by
  classical
  simp only [sumVector, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp only [honestSelection_form_increment, honestSum]

theorem honest_large_sum_independent (Φ : LabelCover) {d : ℕ} (t : ℝ)
    (A : Φ.Labeling) (hA : ∀ c, Φ.Satisfies A c) :
    (Φ.graph d t).IsIndepSet {v | t < Φ.honestSum A hA v} := by
  rw [SimpleGraph.isIndepSet_iff]
  intro v hv w hw _ hadj
  have hform := Φ.form_le_norm (Φ.sumVector v + Φ.sumVector w)
    (Φ.honestSelection A hA d) (Φ.honestSelection_compatible A hA d)
  simp only [Pi.add_apply, Finset.sum_add_distrib, honestSelection_form_sumVector] at hform
  have hsum := (le_abs_self (Φ.honestSum A hA v + Φ.honestSum A hA w)).trans
    (hform.trans hadj.2)
  change t < Φ.honestSum A hA v at hv
  change t < Φ.honestSum A hA w at hw
  linarith

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_FiniteMeanUnionBound
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

theorem internalPairs_card {d : ℕ} (J : Finset (Fin d)) :
    (internalPairs J).card = J.card.choose 2 := by
  classical
  rw [← Finset.card_powersetCard]
  apply Finset.card_bij (fun e _ => ({e.1.1, e.1.2} : Finset (Fin d)))
  · intro e he
    have hjk := (Finset.mem_filter.mp he).2
    apply Finset.mem_powersetCard.mpr
    exact ⟨by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using hjk,
      Finset.card_pair (ne_of_lt e.2)⟩
  · intro e he f hf h
    have hj : e.1.1 ∈ ({f.1.1, f.1.2} : Finset (Fin d)) := by rw [← h]; simp
    have hk : e.1.2 ∈ ({f.1.1, f.1.2} : Finset (Fin d)) := by rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj hk
    apply Subtype.ext
    apply Prod.ext
    · rcases hj with hj | hj
      · exact hj
      · rcases hk with hk | hk
        · have := e.2
          rw [hj, hk] at this
          exact False.elim (lt_asymm f.2 this)
        · exact False.elim ((ne_of_lt e.2) (hj.trans hk.symm))
    · rcases hk with hk | hk
      · rcases hj with hj | hj
        · exact False.elim ((ne_of_lt e.2) (hj.trans hk.symm))
        · have := e.2
          rw [hj, hk] at this
          exact False.elim (lt_asymm f.2 this)
      · exact hk
  · intro A hA
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hA
    obtain ⟨j, k, hne, rfl⟩ := Finset.card_eq_two.mp hcard
    have hj := hsub (Finset.mem_insert_self j {k})
    have hk := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self k))
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨⟨(j,k), hlt⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hk⟩
    · refine ⟨⟨(k,j), hgt⟩, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hj⟩
      · simp [Finset.pair_comm]

theorem positionPair_card (d : ℕ) : Fintype.card (PositionPair d) = d.choose 2 := by
  classical
  have h := internalPairs_card (Finset.univ : Finset (Fin d))
  simpa [internalPairs] using h

theorem vertex_card (Φ : LabelCover) (d : ℕ) :
    Fintype.card (Φ.Vertex d) = Φ.M^(d.choose 2) * (2*d+1)^(Φ.WeightDimension d * d) := by
  simp [Vertex, Seeds, positionPair_card, pow_mul]

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_HighVectorsSeparated
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

namespace VertexCover.LabelCover

theorem norm_sub_rev (Φ : LabelCover) {d : ℕ} (x y : Φ.Coordinate d → ℝ) :
    Φ.compatibilityNorm (x-y) = Φ.compatibilityNorm (y-x) := by
  rw [← Φ.norm_neg (y-x)]
  congr 1
  funext p
  simp

theorem norm_sub_triangle (Φ : LabelCover) {d : ℕ} (x y z : Φ.Coordinate d → ℝ) :
    Φ.compatibilityNorm (x-z) ≤ Φ.compatibilityNorm (x-y) + Φ.compatibilityNorm (y-z) := by
  have h := Φ.norm_add_le (x-y) (y-z)
  simpa only [sub_add_sub_cancel] using h

noncomputable def distanceTo (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (x : Φ.Coordinate d → ℝ) : ℝ :=
  A.inf' hA (fun a => Φ.compatibilityNorm (x-a))

theorem distanceTo_nonneg (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (x : Φ.Coordinate d → ℝ) :
    0 ≤ Φ.distanceTo A hA x := by
  exact Finset.le_inf' _ _ (fun _ _ => Φ.norm_nonneg _)

theorem distanceTo_le (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (x a : Φ.Coordinate d → ℝ)
    (ha : a ∈ A) : Φ.distanceTo A hA x ≤ Φ.compatibilityNorm (x-a) := by
  exact Finset.inf'_le _ ha

theorem distanceTo_self (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (x : Φ.Coordinate d → ℝ)
    (hx : x ∈ A) : Φ.distanceTo A hA x = 0 := by
  apply le_antisymm _ (Φ.distanceTo_nonneg A hA x)
  have h := Φ.distanceTo_le A hA x x hx
  rw [sub_self] at h
  exact h.trans_eq (Φ.norm_zero d)

theorem distanceTo_triangle (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (x y : Φ.Coordinate d → ℝ) :
    Φ.distanceTo A hA x ≤ Φ.compatibilityNorm (x-y) + Φ.distanceTo A hA y := by
  obtain ⟨a, ha, heq⟩ := Finset.exists_mem_eq_inf' hA
    (fun a => Φ.compatibilityNorm (y-a))
  calc
    Φ.distanceTo A hA x ≤ Φ.compatibilityNorm (x-a) := Φ.distanceTo_le A hA x a ha
    _ ≤ Φ.compatibilityNorm (x-y) + Φ.compatibilityNorm (y-a) := Φ.norm_sub_triangle x y a
    _ = Φ.compatibilityNorm (x-y) + Φ.distanceTo A hA y := by rw [← heq]; rfl

noncomputable def separator (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (x : Φ.Coordinate d → ℝ) : ℝ :=
  (Φ.distanceTo A hA (-x) - Φ.distanceTo A hA x) / 2

theorem separator_odd (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (x : Φ.Coordinate d → ℝ) :
    Φ.separator A hA (-x) = -Φ.separator A hA x := by
  simp only [separator, neg_neg]
  ring

theorem separator_lipschitz (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (x y : Φ.Coordinate d → ℝ) :
    |Φ.separator A hA x - Φ.separator A hA y| ≤ Φ.compatibilityNorm (x-y) := by
  have hxy := Φ.distanceTo_triangle A hA x y
  have hyx := Φ.distanceTo_triangle A hA y x
  have hnxy := Φ.distanceTo_triangle A hA (-x) (-y)
  have hnyx := Φ.distanceTo_triangle A hA (-y) (-x)
  have hn : -x - -y = y-x := by abel
  have hn' : -y - -x = x-y := by abel
  rw [hn, ← Φ.norm_sub_rev x y] at hnxy
  rw [hn'] at hnyx
  rw [← Φ.norm_sub_rev x y] at hyx
  unfold separator
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem separator_pos_on (Φ : LabelCover) {d : ℕ} {t : ℝ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, 2*t < Φ.compatibilityNorm (x+y))
    (x : Φ.Coordinate d → ℝ) (hx : x ∈ A) : t < Φ.separator A hA x := by
  have hdist : 2*t < Φ.distanceTo A hA (-x) := by
    obtain ⟨y, hy, heq⟩ := Finset.exists_mem_eq_inf' hA
      (fun y => Φ.compatibilityNorm (-x-y))
    rw [distanceTo, heq]
    have hn : -x-y = -(x+y) := by abel
    rw [hn, Φ.norm_neg]
    exact hsep x hx y hy
  rw [separator, Φ.distanceTo_self A hA x hx]
  linarith

noncomputable def highVectors (Φ : LabelCover) {d : ℕ} (t : ℝ)
    (A : Finset (Φ.Vertex d)) : Finset (Φ.Coordinate d → ℝ) := by
  classical
  exact (A.filter (fun v => t < Φ.compatibilityNorm (Φ.sumVector v))).image Φ.sumVector

theorem highVectors_separated (Φ : LabelCover) {d : ℕ} (t : ℝ)
    (A : Finset (Φ.Vertex d)) (hA : (Φ.graph d t).IsIndepSet (A : Set (Φ.Vertex d))) :
    ∀ x ∈ Φ.highVectors t A, ∀ y ∈ Φ.highVectors t A,
      2*t < Φ.compatibilityNorm (x+y) := by
  classical
  intro x hx y hy
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hvA, hv⟩ := Finset.mem_filter.mp hv
  obtain ⟨hwA, _⟩ := Finset.mem_filter.mp hw
  by_cases heq : v = w
  · subst w
    have htwice : Φ.sumVector v + Φ.sumVector v = fun p => (2 : ℝ) * Φ.sumVector v p := by
      funext p
      simp only [Pi.add_apply]
      ring
    rw [htwice, Φ.norm_mul]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  · have hn := (SimpleGraph.isIndepSet_iff _).mp hA hvA hwA heq
    exact lt_of_not_ge (fun h => hn ⟨heq, h⟩)

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_BatchGradientForm
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

noncomputable def selectionForm (Φ : LabelCover) {d : ℕ}
    (I : Finset (Φ.Coordinate d)) : (Φ.Coordinate d → ℝ) →L[ℝ] ℝ :=
  ∑ p ∈ I, ContinuousLinearMap.proj p

@[simp] theorem selectionForm_apply (Φ : LabelCover) {d : ℕ}
    (I : Finset (Φ.Coordinate d)) (x : Φ.Coordinate d → ℝ) :
    Φ.selectionForm I x = ∑ p ∈ I, x p := by
  simp [selectionForm]

theorem compatibilityNorm_continuous (Φ : LabelCover) (d : ℕ) :
    Continuous (Φ.compatibilityNorm (d := d)) := by
  unfold compatibilityNorm
  apply Continuous.finset_sup'_apply
  intro I hI
  simpa only [Φ.selectionForm_apply] using (Φ.selectionForm I).continuous.abs

theorem distanceTo_continuous (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Continuous (Φ.distanceTo A hA) := by
  unfold distanceTo
  apply Continuous.finset_inf'_apply
  intro a ha
  exact (Φ.compatibilityNorm_continuous d).comp (continuous_id.sub continuous_const)

abbrev BatchWeights (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d)) :=
  J → Fin (Φ.WeightDimension d) → ℝ

noncomputable def batchSum (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (s : Φ.BatchWeights J) : Φ.Coordinate d → ℝ :=
  ∑ j : J, Φ.increment (Φ.query seed j) (s j)

noncomputable def batchSumCLM (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) : Φ.BatchWeights J →L[ℝ] (Φ.Coordinate d → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := Φ.batchSum seed J
    map_add' := by
      intro s t
      simp only [batchSum, Pi.add_apply, Φ.increment_add, Finset.sum_add_distrib]
    map_smul' := by
      intro a s
      change (∑ j : J, Φ.increment (Φ.query seed j) (fun k => a*s j k)) = _
      simp only [Φ.increment_mul]
      ext p
      simp [batchSum, Finset.mul_sum]
  }

@[simp] theorem batchSumCLM_apply (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (s : Φ.BatchWeights J) :
    Φ.batchSumCLM seed J s = Φ.batchSum seed J s := rfl

noncomputable def batchGradient (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (D : Φ.BatchWeights J →L[ℝ] ℝ) : Φ.BatchWeights J := by
  classical
  exact fun j k => D (Pi.single j (Pi.single k 1))

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_DistanceMinusSelect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

def affineSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem affineSign_true : affineSign true = 1 := rfl
@[simp] theorem affineSign_false : affineSign false = -1 := rfl

theorem norm_select_affine (Φ : LabelCover) {d : ℕ} (x : Φ.Coordinate d → ℝ) :
    ∃ I, Φ.Compatible I ∧ ∃ e : Bool,
      Φ.compatibilityNorm x = affineSign e * Φ.selectionForm I x := by
  obtain ⟨I, hI, heq⟩ := (Φ.compatibleSelections d).exists_mem_eq_sup'
    (Φ.compatibleSelections_nonempty d) (fun I => |∑ p ∈ I, x p|)
  change Φ.compatibilityNorm x = |∑ p ∈ I, x p| at heq
  rw [← Φ.selectionForm_apply] at heq
  refine ⟨I, (Φ.mem_compatibleSelections I).mp hI, ?_⟩
  by_cases h : 0 ≤ Φ.selectionForm I x
  · refine ⟨true, ?_⟩
    simpa only [affineSign_true, one_mul, ← Φ.selectionForm_apply, abs_of_nonneg h] using heq
  · refine ⟨false, ?_⟩
    simpa only [affineSign_false, neg_one_mul, ← Φ.selectionForm_apply,
      abs_of_neg (lt_of_not_ge h)] using heq

abbrev AffineIndex (Φ : LabelCover) {d : ℕ} (A : Finset (Φ.Coordinate d → ℝ)) :=
  A × (Φ.compatibleSelections d) × Bool × Bool

noncomputable def affineSlope (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) {A : Finset (Φ.Coordinate d → ℝ)}
    (i : Φ.AffineIndex A) : Φ.BatchWeights J →L[ℝ] ℝ :=
  affineSign i.2.2.2 • (Φ.selectionForm i.2.1.val).comp (Φ.batchSumCLM seed J)

noncomputable def affineOffset (Φ : LabelCover) {d : ℕ}
    (c0 : Φ.Coordinate d → ℝ) {A : Finset (Φ.Coordinate d → ℝ)}
    (i : Φ.AffineIndex A) : ℝ :=
  affineSign i.2.2.2 * Φ.selectionForm i.2.1.val (c0 - affineSign i.2.2.1 • i.1.val)

theorem affine_value (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    {A : Finset (Φ.Coordinate d → ℝ)} (i : Φ.AffineIndex A) (s : Φ.BatchWeights J) :
    Φ.affineSlope seed J i s + Φ.affineOffset c0 i =
      affineSign i.2.2.2 * Φ.selectionForm i.2.1.val
        (c0 + Φ.batchSum seed J s - affineSign i.2.2.1 • i.1.val) := by
  simp only [affineSlope, affineOffset, smul_apply,
    ContinuousLinearMap.comp_apply, Φ.batchSumCLM_apply, smul_eq_mul, map_sub, map_add]
  ring

theorem distance_plus_select (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J) :
    ∃ i : Φ.AffineIndex A, Φ.distanceTo A hA (c0 + Φ.batchSum seed J s) =
      Φ.affineSlope seed J i s + Φ.affineOffset c0 i := by
  classical
  obtain ⟨z, hz, heq⟩ := A.exists_mem_eq_inf' hA
    (fun z => Φ.compatibilityNorm (c0 + Φ.batchSum seed J s - z))
  obtain ⟨I, hI, e, hnorm⟩ := Φ.norm_select_affine (c0 + Φ.batchSum seed J s - z)
  let i : Φ.AffineIndex A := (⟨z,hz⟩, ⟨I,(Φ.mem_compatibleSelections I).mpr hI⟩, true,e)
  change Φ.distanceTo A hA (c0 + Φ.batchSum seed J s) = _ at heq
  refine ⟨i, ?_⟩
  rw [Φ.affine_value]
  simpa only [i, affineSign_true, one_smul] using heq.trans hnorm

theorem distance_minus_select (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J) :
    ∃ i : Φ.AffineIndex A, Φ.distanceTo A hA (-(c0 + Φ.batchSum seed J s)) =
      Φ.affineSlope seed J i s + Φ.affineOffset c0 i := by
  classical
  obtain ⟨z, hz, heq⟩ := A.exists_mem_eq_inf' hA
    (fun z => Φ.compatibilityNorm (-(c0 + Φ.batchSum seed J s)-z))
  have heq' : Φ.distanceTo A hA (-(c0 + Φ.batchSum seed J s)) =
      Φ.compatibilityNorm (c0 + Φ.batchSum seed J s + z) := by
    change _ = _ at heq
    rw [show -(c0 + Φ.batchSum seed J s)-z =
      -(c0 + Φ.batchSum seed J s + z) by abel, Φ.norm_neg] at heq
    exact heq
  obtain ⟨I, hI, e, hnorm⟩ := Φ.norm_select_affine (c0 + Φ.batchSum seed J s + z)
  let i : Φ.AffineIndex A := (⟨z,hz⟩, ⟨I,(Φ.mem_compatibleSelections I).mpr hI⟩, false,e)
  refine ⟨i, ?_⟩
  rw [Φ.affine_value]
  simpa only [i, affineSign_false, neg_one_smul, sub_neg_eq_add] using heq'.trans hnorm

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_CanonicalGradientValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
open MeasureTheory

theorem separator_continuous (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Continuous (Φ.separator A hA) :=
  ((Φ.distanceTo_continuous A hA).comp continuous_neg |>.sub
    (Φ.distanceTo_continuous A hA)).div_const 2

noncomputable def batchFunction (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J) : ℝ :=
  Φ.separator A hA (c0 + Φ.batchSum seed J s)

theorem batchFunction_continuous (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Continuous (Φ.batchFunction seed J c0 A hA) :=
  (Φ.separator_continuous A hA).comp
    (continuous_const.add (Φ.batchSumCLM seed J).continuous)

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_SeparatorContinuousSumOdd
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
attribute [-simp] _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.selectionForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

theorem norm_sum_le (Φ : LabelCover) {d : ℕ} {ι : Type*}
    (T : Finset ι) (f : ι → Φ.Coordinate d → ℝ) :
    Φ.compatibilityNorm (∑ i ∈ T, f i) ≤ ∑ i ∈ T, Φ.compatibilityNorm (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (Φ.norm_zero d).le
  | @insert i T hi ih =>
    simp only [Finset.sum_insert hi]
    exact (Φ.norm_add_le _ _).trans (add_le_add_right ih _)

theorem increment_sub (Φ : LabelCover) {d : ℕ} (i : Φ.Query d)
    (s t : Fin (Φ.WeightDimension d) → ℝ) :
    Φ.increment i (s-t) = Φ.increment i s - Φ.increment i t := by
  have hn : Φ.increment i (-t) = -Φ.increment i t := by
    ext p
    change Φ.increment i (fun k => -t k) p = -Φ.increment i t p
    have h := congrFun (Φ.increment_mul i (-1) t) p
    simpa only [neg_one_mul] using h
  rw [sub_eq_add_neg, Φ.increment_add, hn, sub_eq_add_neg]

noncomputable def continuousSum (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) : Φ.Coordinate d → ℝ :=
  ∑ j, Φ.increment (Φ.query seed j) (s j)

theorem sumVector_eq_continuousSum (Φ : LabelCover) {d : ℕ} (v : Φ.Vertex d) :
    Φ.sumVector v = Φ.continuousSum v.1 (fun j k => (gridRational d (v.2 j k) : ℝ)) := rfl

theorem continuousSum_neg (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) :
    Φ.continuousSum seed (-s) = -Φ.continuousSum seed s := by
  unfold continuousSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ext p
  change Φ.increment (Φ.query seed j) (fun k => -s j k) p =
    -Φ.increment (Φ.query seed j) (s j) p
  have h := congrFun (Φ.increment_mul (Φ.query seed j) (-1) (s j)) p
  simpa only [neg_one_mul] using h

theorem continuousSum_sub_same_seed (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (s t : Fin d → Fin (Φ.WeightDimension d) → ℝ) :
    Φ.continuousSum seed s - Φ.continuousSum seed t = Φ.continuousSum seed (s-t) := by
  simp only [continuousSum, ← Finset.sum_sub_distrib, Pi.sub_apply, increment_sub]

theorem continuousSum_close (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (s t : Fin d → Fin (Φ.WeightDimension d) → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hclose : ∀ j k, |s j k - t j k| ≤ b) :
    Φ.compatibilityNorm (Φ.continuousSum seed s - Φ.continuousSum seed t) ≤ d*b := by
  rw [Φ.continuousSum_sub_same_seed]
  apply (Φ.norm_sum_le _ _).trans
  calc
    (∑ j, Φ.compatibilityNorm (Φ.increment (Φ.query seed j) ((s-t) j))) ≤
        ∑ _j : Fin d, b := by
      apply Finset.sum_le_sum
      intro j _
      exact Φ.increment_norm_le _ _ hb (hclose j)
    _ = d*b := by simp

def InWeightCube (Φ : LabelCover) {d : ℕ}
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) : Prop :=
  ∀ j k, |s j k| ≤ 1

theorem separator_continuousSum_odd (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (seed : Φ.Seeds d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) :
    Φ.separator A hA (Φ.continuousSum seed (-s)) =
      -Φ.separator A hA (Φ.continuousSum seed s) := by
  rw [Φ.continuousSum_neg, Φ.separator_odd]

end VertexCover.LabelCover

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_BatchFunctionOwnLipschitz
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Cube
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem integrable_continuous {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (law ι) := by
  rw [law_eq_restrict_volume]
  exact (hf.continuousOn.integrableOn_compact
    (isCompact_univ_pi (fun _ => isCompact_Icc))).smul_measure (by finiteness)

theorem integrable_continuous_block {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : (ι → κ → ℝ) → ℝ} (hf : Continuous f) : Integrable f (blockLaw ι κ) := by
  rw [blockLaw_eq_restrict_volume]
  exact (hf.continuousOn.integrableOn_compact
    (isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc)))).smul_measure
      (by finiteness)

end VertexCover.Cube

namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory

noncomputable def batchLaw (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d)) :
    Measure (Φ.BatchWeights J) := VertexCover.Cube.blockLaw J (Fin (Φ.WeightDimension d))

instance batchLaw_probability (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d)) :
    IsProbabilityMeasure (Φ.batchLaw J) := by
  unfold batchLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

theorem batchSum_update_sub (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (s : Φ.BatchWeights J) (j : J)
    (u v : Fin (Φ.WeightDimension d) → ℝ) :
    Φ.batchSum seed J (Function.update s j u) -
      Φ.batchSum seed J (Function.update s j v) = Φ.increment (Φ.query seed j) (u-v) := by
  classical
  simp only [batchSum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j]
  · simp only [Function.update_self, ← Φ.increment_sub]
  · intro k _ hkj
    rw [Function.update_of_ne hkj, Function.update_of_ne hkj, sub_self]
  · simp

theorem batchFunction_own_lipschitz (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (s : Φ.BatchWeights J) (j : J) :
    LipschitzWith 1 (fun u => Φ.batchFunction seed J c0 A hA (Function.update s j u)) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (Φ.separator_lipschitz A hA _ _).trans
  rw [add_sub_add_left_eq_sub, Φ.batchSum_update_sub]
  apply Φ.increment_norm_le _ _ (_root_.norm_nonneg _)
  intro k
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (u-v) k

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_RoundingError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.GridCoupling
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def midpoint (p : ℕ) (i : Fin p) : ℝ := -1 + (2*(i:ℝ)+1)/p

noncomputable def index (p : ℕ) (hp : 0 < p) (x : ℝ) : Fin p :=
  ⟨min ⌊(p:ℝ)*(x+1)/2⌋₊ (p-1), (min_le_right _ _).trans_lt (by omega)⟩

theorem index_measurable (p : ℕ) (hp : 0 < p) : Measurable (index p hp) := by
  let g : ℕ → Fin p := fun k => ⟨min k (p-1), (min_le_right _ _).trans_lt (by omega)⟩
  exact (measurable_of_countable g).comp
    (((measurable_const.mul (measurable_id.add_const 1)).div_const 2).nat_floor)

theorem floor_lt_on_interval (p : ℕ) (hp : 0 < p) {x : ℝ}
    (hx : x ∈ Set.Ico (-1 : ℝ) 1) : ⌊(p:ℝ)*(x+1)/2⌋₊ < p := by
  apply (Nat.floor_lt' (Nat.ne_of_gt hp)).mpr
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  nlinarith [mul_lt_mul_of_pos_left hx.2 hpR]

theorem index_val_on_interval (p : ℕ) (hp : 0 < p) {x : ℝ}
    (hx : x ∈ Set.Ico (-1 : ℝ) 1) : (index p hp x).val = ⌊(p:ℝ)*(x+1)/2⌋₊ := by
  exact min_eq_left (by have h := floor_lt_on_interval p hp hx; omega)

theorem index_eq_iff_on_interval (p : ℕ) (hp : 0 < p) {x : ℝ}
    (hx : x ∈ Set.Ico (-1 : ℝ) 1) (i : Fin p) :
    index p hp x = i ↔ -1 + 2*(i:ℝ)/p ≤ x ∧ x < -1 + 2*((i:ℝ)+1)/p := by
  have hz : 0 ≤ (p:ℝ)*(x+1)/2 := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith [hx.1])) (by norm_num)
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  rw [Fin.ext_iff, index_val_on_interval p hp hx, Nat.floor_eq_iff hz]
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · have h : 2*(i:ℝ)/p ≤ x+1 := (div_le_iff₀ hpR).mpr (by nlinarith)
      linarith
    · have h : x+1 < 2*((i:ℝ)+1)/p := (lt_div_iff₀ hpR).mpr (by nlinarith)
      linarith
  · rintro ⟨hl, hu⟩
    have hL : 2*(i:ℝ) ≤ (x+1)*p := (div_le_iff₀ hpR).mp (by linarith)
    have hU : (x+1)*p < 2*((i:ℝ)+1) := (lt_div_iff₀ hpR).mp (by linarith)
    constructor <;> nlinarith

end VertexCover.GridCoupling
namespace VertexCover.GridCoupling
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem cell_subset_interval (p : ℕ) (hp : 0 < p) (i : Fin p) :
    Set.Ico (-1 + 2*(i:ℝ)/p) (-1 + 2*((i:ℝ)+1)/p) ⊆ Set.Ico (-1:ℝ) 1 := by
  intro x hx
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have hi : (i:ℝ)+1 ≤ p := by exact_mod_cast i.isLt
  have hz : 0 ≤ 2*(i:ℝ)/p := div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hpR.le
  have hu : 2*((i:ℝ)+1)/p ≤ 2 := (div_le_iff₀ hpR).mpr (by nlinarith)
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem preimage_cell (p : ℕ) (hp : 0 < p) (i : Fin p) :
    (index p hp ⁻¹' {i}) ∩ Set.Ico (-1:ℝ) 1 =
      Set.Ico (-1 + 2*(i:ℝ)/p) (-1 + 2*((i:ℝ)+1)/p) := by
  ext x
  constructor
  · rintro ⟨hi, hx⟩
    exact (index_eq_iff_on_interval p hp hx i).mp hi
  · intro hx
    have hx' := cell_subset_interval p hp i hx
    exact ⟨(index_eq_iff_on_interval p hp hx' i).mpr hx, hx'⟩

theorem rounding_error (p : ℕ) (hp : 0 < p) {x : ℝ}
    (hx : x ∈ Set.Ico (-1 : ℝ) 1) : |x - midpoint p (index p hp x)| ≤ 1/p := by
  have h := (index_eq_iff_on_interval p hp hx (index p hp x)).mp rfl
  unfold midpoint
  rw [abs_le]
  simp only [mul_add, mul_one, add_div] at h ⊢
  have he : (2:ℝ)/p = 2*(1/p) := by ring
  rw [he] at h
  constructor <;> linarith

end VertexCover.GridCoupling

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_LawNegInvariant
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.GridCoupling
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem intervalLaw_eq_Ico : VertexCover.Cube.intervalLaw =
    (1/2 : ℝ≥0∞) • volume.restrict (Set.Ico (-1:ℝ) 1) := by
  unfold VertexCover.Cube.intervalLaw
  rw [Measure.restrict_congr_set (Ico_ae_eq_Icc (μ := volume)).symm]

theorem index_atom (p : ℕ) (hp : 0 < p) (i : Fin p) :
    VertexCover.Cube.intervalLaw (index p hp ⁻¹' {i}) = (p:ℝ≥0∞)⁻¹ := by
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  rw [intervalLaw_eq_Ico, Measure.smul_apply,
    Measure.restrict_apply ((index_measurable p hp) (measurableSet_singleton i)),
    preimage_cell p hp i, Real.volume_Ico]
  have he : (-1 + 2*((i:ℝ)+1)/p) - (-1 + 2*(i:ℝ)/p) = 2/p := by ring
  rw [he]
  have hpE : (p:ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.ne'
  have hpT : (p:ℝ≥0∞) ≠ ⊤ := by finiteness
  simp only [smul_eq_mul]
  rw [ENNReal.ofReal_div_of_pos hpR]
  simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast, div_eq_mul_inv]
  rw [one_mul, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

theorem index_measurePreserving (p : ℕ) (hp : 0 < p) :
    MeasurePreserving (index p hp) VertexCover.Cube.intervalLaw
      (uniformOn (Set.univ : Set (Fin p))) := by
  refine ⟨index_measurable p hp, Measure.ext_of_singleton (fun i => ?_)⟩
  rw [Measure.map_apply (index_measurable p hp) (measurableSet_singleton i),
    index_atom p hp i, uniformOn_univ]
  simp

theorem rounding_error_ae (p : ℕ) (hp : 0 < p) :
    ∀ᵐ x ∂VertexCover.Cube.intervalLaw, |x - midpoint p (index p hp x)| ≤ 1/p := by
  have ha : ∀ᵐ x ∂VertexCover.Cube.intervalLaw, x ∈ Set.Ico (-1:ℝ) 1 := by
    rw [intervalLaw_eq_Ico]
    exact (Measure.ae_ennreal_smul_measure_iff (by norm_num : (1/2:ℝ≥0∞) ≠ 0)).mpr
      (ae_restrict_mem measurableSet_Ico)
  filter_upwards [ha] with x hx
  exact rounding_error p hp hx

end VertexCover.GridCoupling
namespace VertexCover.Cube
open MeasureTheory
open scoped ENNReal

instance intervalLaw_negInvariant : intervalLaw.IsNegInvariant := by
  have he : (Neg.neg : ℝ → ℝ) ⁻¹' Set.Icc (-1:ℝ) 1 = Set.Icc (-1:ℝ) 1 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage (s := Set.Icc (-1:ℝ) 1) measurableSet_Icc
  rw [he] at h
  exact ⟨(h.smul_measure (1/2 : ℝ≥0∞)).map_eq⟩

instance law_negInvariant (ι : Type*) [Fintype ι] : (law ι).IsNegInvariant := by
  unfold law
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

end VertexCover.Cube

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_BlockLawNegInvariant
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

namespace VertexCover.GridCoupling
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem pi_uniformOn_univ {ι E : Type*} [Fintype ι] [Fintype E] [Nonempty E]
    [MeasurableSpace E] [MeasurableSingletonClass E] :
    Measure.pi (fun _ : ι => uniformOn (Set.univ : Set E)) =
      uniformOn (Set.univ : Set (ι → E)) := by
  classical
  apply Measure.ext_of_singleton
  intro s
  rw [Measure.pi_singleton]
  rw [uniformOn_univ]
  simp [uniformOn_univ, ENNReal.inv_pow]

theorem integral_uniform_finite {E : Type*} [Fintype E] [Nonempty E]
    [MeasurableSpace E] [MeasurableSingletonClass E] (f : E → ℝ) :
    (∫ x, f x ∂uniformOn (Set.univ : Set E)) = (∑ x, f x) / Fintype.card E := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [measureReal_def, uniformOn_univ, Measure.count_singleton,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast, smul_eq_mul]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, mul_comm, mul_one]

end VertexCover.GridCoupling

namespace VertexCover.Cube
open MeasureTheory
instance blockLaw_negInvariant (ι κ : Type*) [Fintype ι] [Fintype κ] :
    (blockLaw ι κ).IsNegInvariant := by
  unfold blockLaw
  exact Measure.pi.isNegInvariant (fun _ : ι => law κ)
end VertexCover.Cube


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_GridBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Parameters

noncomputable section

def a (m : ℕ) : ℝ := 1 / (4*m)
def b₀ (m : ℕ) : ℝ := 1 / (2*m)
def ν (m : ℕ) : ℝ := 1 / (2^7 * (m:ℝ)^3)
def β (m : ℕ) : ℝ := 1 / (2^10 * (m:ℝ)^3)
def ell (m : ℕ) : ℕ := 2^11*m^3
def h (m : ℕ) : ℕ := 2^12*m^3
def d (m : ℕ) : ℕ := 2^38*m^10
def σ (m : ℕ) : ℝ := 1 / (2^46 * (m:ℝ)^12)
def p (m : ℕ) : ℕ := 2*d m+1
def t (m : ℕ) : ℕ := 2^17*m^4

theorem d_square (m : ℕ) : d m = (2^19*m^5)^2 := by
  unfold d
  ring

theorem sqrt_d (m : ℕ) : Real.sqrt (d m) = 2^19*(m:ℝ)^5 := by
  rw [d_square]
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (by positivity)

theorem t_eq (m : ℕ) (hm : 0 < m) : (t m : ℝ) = a m * Real.sqrt (d m) := by
  rw [sqrt_d]
  have hp : (m:ℝ) ≠ 0 := by positivity
  simp only [t, a, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  ring

theorem positive (m : ℕ) (hm : 0 < m) :
    0 < ν m ∧ 0 < β m ∧ 0 < ell m ∧ 0 < h m ∧ 0 < d m ∧ 0 < σ m := by
  dsimp [ν, β, ell, h, d, σ]
  constructor <;> try positivity
  constructor <;> try positivity
  constructor <;> try positivity
  constructor <;> try positivity
  constructor <;> positivity

theorem dimensions (m : ℕ) (hm : 4 ≤ m) :
    4 ≤ d m ∧ 2 ≤ h m ∧ h m < d m ∧ Even (d m) := by
  have h1 : 1 ≤ m := by omega
  have h3 : 1 ≤ m^3 := one_le_pow₀ h1
  have h310 : m^3 ≤ m^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h10 : 1 ≤ m^10 := one_le_pow₀ h1
  dsimp [d, h]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · omega
  · exact ⟨137438953472*m^10, by omega⟩

theorem restriction_budget (m : ℕ) (hm : 4 ≤ m) :
    16*(h m : ℝ)+32*(h m : ℝ)^2 ≤ ν m*(d m : ℝ)/2 := by
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hp : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have h36 : (m:ℝ)^3 ≤ (m:ℝ)^6 := pow_le_pow_right₀ hm1 (by decide)
  have h67 : (m:ℝ)^6 ≤ (m:ℝ)^7 := pow_le_pow_right₀ hm1 (by decide)
  have h6 : (0:ℝ) ≤ (m:ℝ)^6 := by positivity
  have heq : ν m*(d m : ℝ)/2 = 2^30*(m:ℝ)^7 := by
    simp only [ν, d, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  rw [heq]
  simp only [h, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith [sq_nonneg ((m:ℝ)^3)]

theorem β_h (m : ℕ) (hm : 0 < m) : β m*(h m : ℝ)/2 = 2 := by
  have hp : (m:ℝ) ≠ 0 := by positivity
  simp only [β, h, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

theorem ell_eq (m : ℕ) (hm : 0 < m) : (ell m : ℝ) = 2/β m := by
  have hp : (m:ℝ) ≠ 0 := by positivity
  simp only [ell, β, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

theorem σ_eq (m : ℕ) : σ m = 1 / ((h m : ℝ)^2*(ell m : ℝ)^2) := by
  unfold σ h ell
  push_cast
  congr 1
  ring

theorem grid_budget (m : ℕ) (hm : 4 ≤ m) :
    (d m : ℝ)/(p m : ℝ) < 1/2 ∧ (1:ℝ)/2 < (t m : ℝ)/2 ∧ 2*m < p m := by
  have hd := (dimensions m hm).1
  have hm1 : 1 ≤ m := by omega
  have hm4 : 1 ≤ m^4 := one_le_pow₀ hm1
  have hmd : m ≤ d m := by
    have hpow : m^1 ≤ m^10 := Nat.pow_le_pow_right (by omega) (by decide)
    simp only [pow_one] at hpow
    dsimp [d]
    omega
  refine ⟨?_, ?_, ?_⟩
  · have hp : (0:ℝ) < p m := by unfold p; positivity
    apply (div_lt_iff₀ hp).mpr
    simp only [p, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    linarith
  · have ht : 1 < t m := by dsimp [t]; omega
    have ht' : (1:ℝ) < t m := by exact_mod_cast ht
    linarith
  · dsimp [p]; omega

end

end VertexCover.Parameters

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_DenseHighFraction
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability
attribute [-simp] _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.selectionForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory

theorem high_count_lower (Φ : LabelCover) {d : ℕ} {t : ℝ}
    (A : Finset (Φ.Vertex d)) (hA : (Φ.graph d t).IsIndepSet (A : Set (Φ.Vertex d))) :
    A.card ≤ (A.filter (fun v => t < Φ.compatibilityNorm (Φ.sumVector v))).card + 1 := by
  classical
  have hl : (A.filter (fun v => Φ.compatibilityNorm (Φ.sumVector v) ≤ t)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro v hv w hw
    exact Φ.low_norm_subsingleton (A : Set (Φ.Vertex d)) hA
      (Finset.mem_filter.mp hv) (Finset.mem_filter.mp hw)
  have he := Finset.card_filter_add_card_filter_not (s := A)
    (fun v => t < Φ.compatibilityNorm (Φ.sumVector v))
  simp only [not_lt] at he
  omega

theorem vertex_card_ge_grid (Φ : LabelCover) {d : ℕ} (hd : 0 < d) :
    2*d+1 ≤ Fintype.card (Φ.Vertex d) := by
  classical
  have hq : 0 < Φ.WeightDimension d := by
    dsimp [WeightDimension]
    exact pow_pos (lt_of_lt_of_le Φ.qU_pos (le_max_left _ _)) _
  have he : 1 ≤ Φ.WeightDimension d * d := Nat.mul_pos hq hd
  rw [Φ.vertex_card]
  have hM : 1 ≤ Φ.M^(d.choose 2) := one_le_pow₀ Φ.M_pos
  have hp : 2*d+1 ≤ (2*d+1)^(Φ.WeightDimension d*d) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2*d+1) he
  exact hp.trans (Nat.le_mul_of_pos_left _ hM)

theorem dense_high_fraction (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (A : Finset (Φ.Vertex (Parameters.d m)))
    (hA : (Φ.graph (Parameters.d m) (Parameters.t m)).IsIndepSet
      (A : Set (Φ.Vertex (Parameters.d m))))
    (hdense : (Fintype.card (Φ.Vertex (Parameters.d m)):ℝ)/(m:ℝ) ≤ A.card) :
    Parameters.b₀ m ≤
      ((A.filter (fun v => (Parameters.t m:ℝ) < Φ.compatibilityNorm (Φ.sumVector v))).card:ℝ) /
        Fintype.card (Φ.Vertex (Parameters.d m)) := by
  classical
  have hmR : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hN : 2*m < Fintype.card (Φ.Vertex (Parameters.d m)) :=
    (Parameters.grid_budget m hm).2.2.trans_le
      (Φ.vertex_card_ge_grid (by have h := (Parameters.dimensions m hm).1; omega))
  have hNR : (2:ℝ)*m < Fintype.card (Φ.Vertex (Parameters.d m)) := by exact_mod_cast hN
  have hNP : (0:ℝ) < Fintype.card (Φ.Vertex (Parameters.d m)) := by linarith
  have hc : (A.card:ℝ) ≤
      (A.filter (fun v => (Parameters.t m:ℝ) < Φ.compatibilityNorm (Φ.sumVector v))).card + 1 := by
    exact_mod_cast Φ.high_count_lower A hA
  unfold Parameters.b₀
  apply (le_div_iff₀ hNP).mpr
  have hd := (div_le_iff₀ hmR).mp hdense
  have hh : (1/(2*(m:ℝ))) * Fintype.card (Φ.Vertex (Parameters.d m)) =
      Fintype.card (Φ.Vertex (Parameters.d m))/(2*(m:ℝ)) := by ring
  rw [hh]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2*m)).mpr
  nlinarith

end VertexCover.LabelCover

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_GridCentralCard
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.FiniteAntiConcentration
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def subsetSum (w : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, w i

def intervalFamily (w : ι → ℝ) (L U : ℝ) : Finset (Finset ι) :=
  Finset.univ.filter (fun s => L ≤ subsetSum w s ∧ subsetSum w s ≤ U)

omit [Fintype ι] in
theorem subsetSum_increase (w : ι → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hw : ∀ i, δ ≤ w i) {s t : Finset ι} (hst : s ⊂ t) :
    subsetSum w s + δ ≤ subsetSum w t := by
  obtain ⟨i, hit, his⟩ := Finset.exists_of_ssubset hst
  have hd := Finset.single_le_sum (s := t \ s) (f := w)
    (fun j _ => hδ.trans (hw j)) (Finset.mem_sdiff.mpr ⟨hit, his⟩)
  have he := Finset.sum_sdiff (f := w) (Finset.Subset.refl s |>.trans hst.le)
  unfold subsetSum
  linarith [hw i]

theorem interval_card_le (w : ι → ℝ) (L U δ : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hw : ∀ i, δ ≤ w i) (hwide : U - L < N * δ) :
    (intervalFamily w L U).card ≤ N * (Fintype.card ι).choose (Fintype.card ι / 2) := by
  classical
  let bucket : Finset ι → ℕ := fun s => ⌊(subsetSum w s - L) / δ⌋₊
  have hb : ∀ s ∈ intervalFamily w L U, bucket s < N := by
    intro s hs
    have hs' := (Finset.mem_filter.mp hs).2
    apply (Nat.floor_lt (div_nonneg (sub_nonneg.mpr hs'.1) hδ.le)).mpr
    apply (div_lt_iff₀ hδ).mpr
    linarith [hs'.2]
  have hc : ∀ k, ((intervalFamily w L U).filter (fun s => bucket s = k)).card ≤
      (Fintype.card ι).choose (Fintype.card ι / 2) := by
    intro k
    apply IsAntichain.sperner
    intro s hs t ht hne hst
    have hs' := Finset.mem_filter.mp hs
    have ht' := Finset.mem_filter.mp ht
    have hsL := (Finset.mem_filter.mp hs'.1).2.1
    have hi := subsetSum_increase w hδ.le hw
      (Finset.ssubset_iff_subset_ne.mpr ⟨hst, hne⟩)
    have hlo := Nat.floor_le (div_nonneg (sub_nonneg.mpr hsL) hδ.le)
    have hhi := Nat.lt_floor_add_one ((subsetSum w t - L) / δ)
    change (bucket s : ℝ) ≤ (subsetSum w s - L) / δ at hlo
    change (subsetSum w t - L) / δ < (bucket t : ℝ) + 1 at hhi
    rw [hs'.2] at hlo
    rw [ht'.2] at hhi
    have hlo' := (le_div_iff₀ hδ).mp hlo
    have hhi' := (div_lt_iff₀ hδ).mp hhi
    nlinarith
  have ht : Set.MapsTo bucket (intervalFamily w L U) (Finset.range N) := by
    intro s hs
    exact Finset.mem_range.mpr (hb s hs)
  rw [Finset.card_eq_sum_card_fiberwise ht]
  calc
    _ ≤ ∑ _k ∈ Finset.range N, (Fintype.card ι).choose (Fintype.card ι / 2) :=
      Finset.sum_le_sum (fun k _ => hc k)
    _ = _ := by simp

def choices (lo hi : ι → ℝ) (s : Finset ι) : ℝ :=
  ∑ i, if i ∈ s then hi i else lo i

theorem choices_eq (lo hi : ι → ℝ) (s : Finset ι) :
    choices lo hi s = (∑ i, lo i) + subsetSum (fun i => hi i - lo i) s := by
  classical
  unfold choices subsetSum
  have hs : (∑ i ∈ s, (hi i - lo i)) = ∑ i, if i ∈ s then hi i - lo i else 0 := by
    symm
    simp
  rw [hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi'
  by_cases h : i ∈ s <;> simp [h]

theorem choice_card_le (lo hi : ι → ℝ) (L U δ : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hdiff : ∀ i, lo i + δ ≤ hi i) (hwide : U - L < N * δ) :
    (Finset.univ.filter (fun s : Finset ι => L ≤ choices lo hi s ∧ choices lo hi s ≤ U)).card ≤
      N * (Fintype.card ι).choose (Fintype.card ι / 2) := by
  classical
  have he : (Finset.univ.filter (fun s : Finset ι => L ≤ choices lo hi s ∧ choices lo hi s ≤ U)) =
      intervalFamily (fun i => hi i - lo i) (L - ∑ i, lo i) (U - ∑ i, lo i) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, intervalFamily, choices_eq]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [he]
  apply interval_card_le _ _ _ δ N hδ (fun i => by linarith [hdiff i])
  linarith

def toggleEquiv (mask : Finset ι) : Finset ι ≃ Finset ι where
  toFun s := symmDiff s mask
  invFun s := symmDiff s mask
  left_inv s := by
    ext i
    simp only [Finset.mem_symmDiff]
    tauto
  right_inv s := by
    ext i
    simp only [Finset.mem_symmDiff]
    tauto

variable {α : Type*} [Fintype α]

def orderedChoice (g : α → ℝ) (τ : α ≃ α) (x : ι → α) (s : Finset ι) : ℝ :=
  choices (fun i => min (g (x i)) (g (τ (x i))))
    (fun i => max (g (x i)) (g (τ (x i)))) s

def rawChoice (g : α → ℝ) (τ : α ≃ α) (x : ι → α) (s : Finset ι) : ℝ :=
  ∑ i, if i ∈ s then g (τ (x i)) else g (x i)

omit [Fintype α] in
theorem orderedChoice_eq (g : α → ℝ) (τ : α ≃ α) (x : ι → α) (s : Finset ι) :
    orderedChoice g τ x s = rawChoice g τ x
      (toggleEquiv (Finset.univ.filter (fun i => g (τ (x i)) < g (x i))) s) := by
  classical
  unfold orderedChoice rawChoice choices toggleEquiv
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hm : i ∈ s <;> by_cases ho : g (τ (x i)) < g (x i)
  · simp [Finset.mem_symmDiff, hm, ho, max_eq_left ho.le]
  · simp [Finset.mem_symmDiff, hm, ho, max_eq_right (le_of_not_gt ho)]
  · simp [Finset.mem_symmDiff, hm, ho, min_eq_right ho.le]
  · simp [Finset.mem_symmDiff, hm, ho, min_eq_left (le_of_not_gt ho)]

def coordinateShift (τ : α ≃ α) (s : Finset ι) : (ι → α) ≃ (ι → α) :=
  Equiv.piCongrRight (fun i => if i ∈ s then τ else Equiv.refl α)

omit [Fintype α] in
theorem rawChoice_eq (g : α → ℝ) (τ : α ≃ α) (x : ι → α) (s : Finset ι) :
    rawChoice g τ x s = ∑ i, g (coordinateShift τ s x i) := by
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hm : i ∈ s <;> simp [coordinateShift, hm]

theorem sum_orderedChoices (g : α → ℝ) (τ : α ≃ α) (f : ℝ → ℝ) :
    (∑ x : ι → α, ∑ s : Finset ι, f (orderedChoice g τ x s)) =
      (2 : ℝ) ^ Fintype.card ι * ∑ x : ι → α, f (∑ i, g (x i)) := by
  classical
  calc
    _ = ∑ x : ι → α, ∑ s : Finset ι, f (rawChoice g τ x s) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [orderedChoice_eq]
      exact (toggleEquiv (Finset.univ.filter (fun i => g (τ (x i)) < g (x i)))).sum_comp (fun s => f (rawChoice g τ x s))
    _ = ∑ s : Finset ι, ∑ x : ι → α, f (rawChoice g τ x s) := Finset.sum_comm
    _ = ∑ _s : Finset ι, ∑ x : ι → α, f (∑ i, g (x i)) := by
      apply Finset.sum_congr rfl
      intro s hs
      simp only [rawChoice_eq]
      exact (coordinateShift τ s).sum_comp (fun x => f (∑ i, g (x i)))
    _ = _ := by simp [Fintype.card_finset]

def grid (d : ℕ) (u : Fin (2*d+1)) : ℝ :=
  2 * ((u.val : ℝ) - d) / (2*d+1)

def gridShift (d : ℕ) : Fin (2*d+1) ≃ Fin (2*d+1) :=
  Equiv.addRight ⟨d, by omega⟩

theorem grid_gap (d : ℕ) (u : Fin (2*d+1)) :
    (2*d : ℝ)/(2*d+1) ≤ |grid d (gridShift d u) - grid d u| := by
  have hp : (0 : ℝ) < 2*d+1 := by positivity
  have hv : (gridShift d u).val =
      if 2*d+1 ≤ u.val+d then u.val+d-(2*d+1) else u.val+d := by
    exact Fin.val_add_eq_ite u ⟨d, by omega⟩
  unfold grid
  rw [hv]
  split_ifs with h
  · have hs : ((u.val+d-(2*d+1) : ℕ) : ℝ) = (u.val : ℝ)+d-(2*d+1) := by
      rw [Nat.cast_sub h]
      push_cast
      rfl
    rw [hs]
    have he : 2*((u.val:ℝ)+d-(2*d+1)-d)/(2*d+1) -
        2*((u.val:ℝ)-d)/(2*d+1) = -(2*(d+1)/(2*d+1)) := by ring
    rw [he, abs_neg, abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right (by linarith) hp.le
  · push_cast
    have he : 2*((u.val:ℝ)+d-d)/(2*d+1) -
        2*((u.val:ℝ)-d)/(2*d+1) = 2*d/(2*d+1) := by ring
    rw [he, abs_of_nonneg (by positivity)]

theorem grid_ordered_gap (d : ℕ) (u : Fin (2*d+1)) :
    min (grid d u) (grid d (gridShift d u)) + (2*d : ℝ)/(2*d+1) ≤
      max (grid d u) (grid d (gridShift d u)) := by
  have h := grid_gap d u
  rw [← max_sub_min_eq_abs] at h
  linarith

theorem grid_neg (d : ℕ) (u : Fin (2*d+1)) : grid d (Fin.rev u) = - grid d u := by
  unfold grid
  rw [Fin.val_rev, Nat.cast_sub (by omega)]
  push_cast
  ring

theorem grid_interval_card (d n N : ℕ) (hd : 0 < d) (L U : ℝ)
    (hwide : U-L < N * ((2*d : ℝ)/(2*d+1))) :
    (2 : ℝ)^n *
      ((Finset.univ.filter (fun x : Fin n → Fin (2*d+1) =>
        L ≤ ∑ i, grid d (x i) ∧ (∑ i, grid d (x i)) ≤ U)).card : ℝ) ≤
    ((2*d+1 : ℕ)^n : ℝ) * N * (n.choose (n/2)) := by
  classical
  let f : ℝ → ℝ := fun y => if L ≤ y ∧ y ≤ U then 1 else 0
  have hlaw := sum_orderedChoices (ι := Fin n) (grid d) (gridShift d) f
  have hc (x : Fin n → Fin (2*d+1)) :
      ∑ s : Finset (Fin n), f (orderedChoice (grid d) (gridShift d) x s) ≤
        (N * n.choose (n/2) : ℕ) := by
    have h := choice_card_le
      (fun i => min (grid d (x i)) (grid d (gridShift d (x i))))
      (fun i => max (grid d (x i)) (grid d (gridShift d (x i))))
      L U ((2*d : ℝ)/(2*d+1)) N
      (by positivity) (fun i => grid_ordered_gap d (x i)) hwide
    have hs : (∑ s : Finset (Fin n), f (orderedChoice (grid d) (gridShift d) x s)) =
        ((Finset.univ.filter (fun s : Finset (Fin n) =>
          L ≤ orderedChoice (grid d) (gridShift d) x s ∧
          orderedChoice (grid d) (gridShift d) x s ≤ U)).card : ℝ) := by
      exact Finset.sum_boole _ _
    rw [hs]
    simp only [Fintype.card_fin] at h
    exact_mod_cast h
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hc x)
  rw [hlaw] at hs
  have hcount : (∑ x : Fin n → Fin (2*d+1), f (∑ i, grid d (x i))) =
      ((Finset.univ.filter (fun x : Fin n → Fin (2*d+1) =>
        L ≤ ∑ i, grid d (x i) ∧ (∑ i, grid d (x i)) ≤ U)).card : ℝ) := by
    exact Finset.sum_boole _ _
  rw [hcount] at hs
  simpa [Fintype.card_fun, mul_assoc] using hs

theorem symmetric_tail_count {Ω : Type*} [Fintype Ω] (f : Ω → ℝ)
    (rev : Ω ≃ Ω) (hrev : ∀ x, f (rev x) = -f x) (t : ℝ) (ht : 0 ≤ t) :
    2 * ((Finset.univ.filter (fun x => t < f x)).card : ℝ) +
      ((Finset.univ.filter (fun x => -t ≤ f x ∧ f x ≤ t)).card : ℝ) = Fintype.card Ω := by
  classical
  let pos : Ω → ℝ := fun x => if t < f x then 1 else 0
  let neg : Ω → ℝ := fun x => if f x < -t then 1 else 0
  let mid : Ω → ℝ := fun x => if -t ≤ f x ∧ f x ≤ t then 1 else 0
  have he (x : Ω) : pos x + neg x + mid x = 1 := by
    dsimp [pos, neg, mid]
    split_ifs <;> simp_all <;> linarith
  have hn : (∑ x, neg x) = ∑ x, pos x := by
    have h : (∑ x, pos (rev x)) = ∑ x, neg x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [pos, neg, hrev, lt_neg]
    rw [← h]
    exact rev.sum_comp pos
  have hs : (∑ x, pos x) + (∑ x, neg x) + (∑ x, mid x) = Fintype.card Ω := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp only [he]
    simp
  rw [hn] at hs
  have hpcount : (∑ x, pos x) = ((Finset.univ.filter (fun x => t < f x)).card : ℝ) :=
    Finset.sum_boole _ _
  have hmcount : (∑ x, mid x) =
      ((Finset.univ.filter (fun x => -t ≤ f x ∧ f x ≤ t)).card : ℝ) :=
    Finset.sum_boole _ _
  rw [hpcount, hmcount] at hs
  linarith

theorem grid_tail_count (d n t : ℕ) :
    2 * ((Finset.univ.filter (fun x : Fin n → Fin (2*d+1) =>
      (t : ℝ) < ∑ i, grid d (x i))).card : ℝ) +
    ((Finset.univ.filter (fun x : Fin n → Fin (2*d+1) =>
      -(t : ℝ) ≤ ∑ i, grid d (x i) ∧ (∑ i, grid d (x i)) ≤ t)).card : ℝ) =
      ((2*d+1 : ℕ)^n : ℝ) := by
  classical
  have hr (x : Fin n → Fin (2*d+1)) :
      (∑ i, grid d ((Equiv.piCongrRight (fun _ : Fin n => Fin.revPerm)) x i)) =
      -(∑ i, grid d (x i)) := by
    change (∑ i, grid d (Fin.rev (x i))) = -(∑ i, grid d (x i))
    simp only [grid_neg, Finset.sum_neg_distrib]
  simpa [Fintype.card_fun] using symmetric_tail_count
    (fun x : Fin n → Fin (2*d+1) => ∑ i, grid d (x i))
    (Equiv.piCongrRight (fun _ : Fin n => Fin.revPerm)) hr (t : ℝ) (by positivity)

theorem grid_central_card (d n t : ℕ) (ht : t < d) :
    (2 : ℝ)^n *
      ((Finset.univ.filter (fun x : Fin n → Fin (2*d+1) =>
        -(t : ℝ) ≤ ∑ i, grid d (x i) ∧ (∑ i, grid d (x i)) ≤ t)).card : ℝ) ≤
    ((2*d+1 : ℕ)^n : ℝ) * (2*t+1) * (n.choose (n/2) : ℝ) := by
  have htr : (t:ℝ) < d := Nat.cast_lt.mpr ht
  have hwide : (t:ℝ)-(-t) < (2*t+1 : ℕ)*((2*d : ℝ)/(2*d+1)) := by
    push_cast
    rw [mul_div, lt_div_iff₀ (by positivity : (0:ℝ) < 2*d+1)]
    nlinarith
  simpa using grid_interval_card d n (2*t+1) (by omega) (-(t:ℝ)) (t:ℝ) hwide

end
end VertexCover.FiniteAntiConcentration


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_DecodingUpperThreeHalves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Parameters

 theorem pair_budget (m : ℕ) (hm : 4 ≤ m) :
    (((h m).choose 2 : ℕ) : ℝ)*(ell m : ℝ)^2*σ m = ((h m : ℝ)-1)/(2*(h m : ℝ)) := by
  have hpos := positive m (by omega : 0 < m)
  have hh : (h m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos.2.2.2.1)
  have hl : (ell m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos.2.2.1)
  rw [Nat.cast_choose_two, σ_eq]
  field_simp

 theorem pair_budget_lt (m : ℕ) (hm : 4 ≤ m) :
    (((h m).choose 2 : ℕ) : ℝ)*(ell m : ℝ)^2*σ m < (1:ℝ)/2 := by
  rw [pair_budget m hm]
  have hh : (0:ℝ) < h m := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<2) (dimensions m hm).2.1)
  apply (div_lt_iff₀ (by positivity : (0:ℝ) < 2*(h m : ℝ))).mpr
  linarith

 theorem σ_between (m : ℕ) (hm : 4 ≤ m) : 0 < σ m ∧ σ m < 1 := by
  refine ⟨(positive m (by omega)).2.2.2.2.2, ?_⟩
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hp : (1:ℝ) ≤ (m:ℝ)^12 := one_le_pow₀ hm1
  unfold σ
  apply (div_lt_one (by positivity)).mpr
  norm_num only [Nat.reducePow]
  nlinarith

 theorem sqrt_d_gt (m : ℕ) (hm : 4 ≤ m) : 4*(m:ℝ) < Real.sqrt (d m) := by
  rw [sqrt_d]
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hp : (m:ℝ)^1 ≤ (m:ℝ)^5 := pow_le_pow_right₀ hm1 (by decide)
  simp only [pow_one] at hp
  norm_num only [Nat.reducePow]
  nlinarith

end VertexCover.Parameters


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_MidpointGridTail
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.FiniteAntiConcentration
noncomputable section

def gridTailDensity (d n t : ℕ) : ℝ :=
  ((Finset.univ.filter (fun x : Fin n → Fin (2*d+1) =>
    (t : ℝ) < ∑ i, grid d (x i))).card : ℝ) / ((2*d+1 : ℕ)^n : ℝ)

end
end VertexCover.FiniteAntiConcentration

namespace VertexCover.Parameters
noncomputable section

 theorem t_lt_d (m : ℕ) (hm : 4 ≤ m) : t m < d m := by
  have hm1 : 1 ≤ m := by omega
  have hpow : m^4 ≤ m^10 := Nat.pow_le_pow_right hm1 (by decide)
  have hp : 1 ≤ m^4 := one_le_pow₀ hm1
  unfold t d
  norm_num only [Nat.reducePow]
  omega

 theorem tail_error_lt (m : ℕ) (hm : 4 ≤ m) :
    Real.sqrt 2 * (a m + 1/Real.sqrt (d m)) < 1/(m:ℝ) := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have ha : 0 < a m := by unfold a; positivity
  have hinv : (1:ℝ)/Real.sqrt (d m) < a m := by
    exact one_div_lt_one_div_of_lt (by positivity) (sqrt_d_gt m hm)
  have hsq : Real.sqrt (2:ℝ) < 3/2 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hp := Real.sqrt_nonneg (2:ℝ)
    nlinarith
  have hmul : Real.sqrt 2 * (a m + 1/Real.sqrt (d m)) < 3*a m := by
    have h1 := mul_lt_mul_of_pos_left hinv (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))
    have h2 := mul_lt_mul_of_pos_right hsq (by linarith : 0 < 2*a m)
    nlinarith
  have he : 3*a m < 1/(m:ℝ) := by
    unfold a
    rw [mul_one_div]
    apply (div_lt_div_iff₀ (by positivity : (0:ℝ)<4*m) hmpos).mpr
    nlinarith
  exact hmul.trans he

end
end VertexCover.Parameters


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_GraphCompleteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover
noncomputable section

def splitSelected {ι κ α : Type*} [DecidableEq κ] (slot : ι → κ) :
    (ι → κ → α) ≃ (ι → α) × ((i : ι) → {k : κ // k ≠ slot i} → α) where
  toFun w := (fun i => w i (slot i), fun i k => w i k.1)
  invFun v i k := if h : k = slot i then v.1 i else v.2 i ⟨k,h⟩
  left_inv w := by funext i k; dsimp; split_ifs with h <;> simp_all
  right_inv v := by
    apply Prod.ext
    · funext i; simp
    · funext i k; simp [k.2]

end
end VertexCover

namespace VertexCover.LabelCover
noncomputable section

 theorem gridRational_real (d : ℕ) (u : Fin (2*d+1)) :
    (gridRational d u : ℝ) = FiniteAntiConcentration.grid d u := by
  unfold gridRational FiniteAntiConcentration.grid
  push_cast
  rfl

end
end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_SeparatorRoundingErrorAe
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.GridCoupling
open MeasureTheory ProbabilityTheory

theorem block_rounding_error_ae {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℕ) (hp : 0 < p) :
    ∀ᵐ s ∂VertexCover.Cube.blockLaw ι κ, ∀ j k,
      |s j k - midpoint p (index p hp (s j k))| ≤ 1/p := by
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro k
  have h1 := measurePreserving_eval (fun _ : ι => VertexCover.Cube.law κ) j
  have h2 := measurePreserving_eval (fun _ : κ => VertexCover.Cube.intervalLaw) k
  exact (h2.comp h1).quasiMeasurePreserving.ae (rounding_error_ae p hp)

theorem midpoint_eq_gridRational (d : ℕ) (i : Fin (2*d+1)) :
    midpoint (2*d+1) i = (VertexCover.LabelCover.gridRational d i : ℝ) := by
  have hn : (2*(d:ℝ)+1) ≠ 0 := by positivity
  simp only [midpoint, VertexCover.LabelCover.gridRational]
  push_cast
  field_simp
  ring
end VertexCover.GridCoupling

namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory

noncomputable def continuousSumCLM (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d) :
    (Fin d → Fin (Φ.WeightDimension d) → ℝ) →L[ℝ] (Φ.Coordinate d → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := Φ.continuousSum seed
    map_add' := by
      intro s t
      simp only [continuousSum, Pi.add_apply, Φ.increment_add, Finset.sum_add_distrib]
    map_smul' := by
      intro a s
      change (∑ j, Φ.increment (Φ.query seed j) (fun k => a*s j k)) = _
      simp only [Φ.increment_mul]
      ext p
      simp [continuousSum, Finset.mul_sum]
  }

theorem separator_continuousSum_continuous (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (seed : Φ.Seeds d) :
    Continuous (fun s => Φ.separator A hA (Φ.continuousSum seed s)) :=
  (Φ.separator_continuous A hA).comp (Φ.continuousSumCLM seed).continuous

theorem separator_continuousSum_mean_zero (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (seed : Φ.Seeds d) :
    (∫ s, Φ.separator A hA (Φ.continuousSum seed s)
      ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) = 0 := by
  have h := integral_neg_eq_self
    (fun s => Φ.separator A hA (Φ.continuousSum seed s))
    (VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))
  simp only [Φ.separator_continuousSum_odd, integral_neg] at h
  linarith

noncomputable def roundedVertex (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) : Φ.Vertex d :=
  (seed, fun j k => VertexCover.GridCoupling.index (2*d+1) (by omega) (s j k))

theorem separator_rounding_error_ae (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (seed : Φ.Seeds d) :
    ∀ᵐ s ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)),
      |Φ.separator A hA (Φ.continuousSum seed s) -
        Φ.separator A hA (Φ.sumVector (Φ.roundedVertex seed s))| ≤
          (d:ℝ)/(2*d+1) := by
  filter_upwards [VertexCover.GridCoupling.block_rounding_error_ae
    (ι := Fin d) (κ := Fin (Φ.WeightDimension d)) (2*d+1) (by omega)] with s hs
  apply (Φ.separator_lipschitz A hA _ _).trans
  rw [Φ.sumVector_eq_continuousSum]
  have h := Φ.continuousSum_close seed s
    (fun j k => (gridRational d ((Φ.roundedVertex seed s).2 j k) : ℝ))
    (b := 1/(2*d+1)) (by positivity) (by
      intro j k
      simpa only [roundedVertex, ← VertexCover.GridCoupling.midpoint_eq_gridRational,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hs j k)
  simpa only [div_eq_mul_inv, one_mul, roundedVertex] using h

end VertexCover.LabelCover

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_DenseSeparatorData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Parameters

theorem variance_scale (m : ℕ) (hm : 0 < m) :
    b₀ m * ((t m:ℝ)/2)^2 = ν m * (d m:ℝ) := by
  have hmR : (m:ℝ) ≠ 0 := by positivity
  simp only [b₀, t, ν, d, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

end VertexCover.Parameters

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_SelectedIntegralAbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Average
open MeasureTheory

theorem selected_integral_abs_le {α Ω K : Type*} [Fintype α] [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Finset K) (F : α → Ω → K → ℝ)
    (hF : ∀ a k, Integrable (fun x => F a x k) μ) :
    (∑ k ∈ T, |(∑ a, ∫ x, F a x k ∂μ) / Fintype.card α|) ≤
      (∑ a, ∫ x, ∑ k ∈ T, |F a x k| ∂μ) / Fintype.card α := by
  classical
  have hc : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  simp_rw [abs_div, abs_of_nonneg hc]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ hc
  calc
    _ ≤ ∑ k ∈ T, ∑ a, ∫ x, |F a x k| ∂μ := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        _ ≤ ∑ a, |∫ x, F a x k ∂μ| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := Finset.sum_le_sum (fun a _ => by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (F a · k))
    _ = ∑ a, ∑ k ∈ T, ∫ x, |F a x k| ∂μ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (integral_finsetSum T (fun k _ => (hF a k).abs)).symm

end VertexCover.Average


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_SeparatorStarOscillation
attribute [-instance] _root_.OAI.VertexCover.LabelCover.batchLaw_probability
attribute [-simp] _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.selectionForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

theorem query_eq_of_questions (Φ : LabelCover) {d : ℕ} (seed seed' : Φ.Seeds d)
    (j : Fin d)
    (hL : ∀ k (h : j < k), Φ.left (seed ⟨(j,k),h⟩) = Φ.left (seed' ⟨(j,k),h⟩))
    (hR : ∀ k (h : k < j), Φ.right (seed ⟨(k,j),h⟩) = Φ.right (seed' ⟨(k,j),h⟩)) :
    Φ.query seed j = Φ.query seed' j := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Prod.ext
  · funext k; exact hL k.1 k.2
  · funext k; exact hR k.1 k.2

theorem query_replaceSeed_other (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (e : PositionPair d) (c : Fin Φ.M) (j : Fin d)
    (hjl : j ≠ e.1.1) (hjr : j ≠ e.1.2) :
    Φ.query seed j = Φ.query (Φ.replaceSeed seed e c) j := by
  apply Φ.query_eq_of_questions
  · intro k h
    have hn : (⟨(j,k),h⟩ : PositionPair d) ≠ e := by
      intro he; exact hjl (congrArg (fun e : PositionPair d => e.1.1) he)
    simp [replaceSeed, Function.update_of_ne hn]
  · intro k h
    have hn : (⟨(k,j),h⟩ : PositionPair d) ≠ e := by
      intro he; exact hjr (congrArg (fun e : PositionPair d => e.1.2) he)
    simp [replaceSeed, Function.update_of_ne hn]

theorem query_eq_away (Φ : LabelCover) {d : ℕ} (seed seed' : Φ.Seeds d) (k : Fin d)
    (hL : ∀ e : PositionPair d, e.1.1 ≠ k → Φ.left (seed e) = Φ.left (seed' e))
    (hR : ∀ e : PositionPair d, e.1.2 ≠ k → Φ.right (seed e) = Φ.right (seed' e))
    (j : Fin d) (hj : j ≠ k) : Φ.query seed j = Φ.query seed' j := by
  apply Φ.query_eq_of_questions
  · intro l h; exact hL ⟨(j,l),h⟩ hj
  · intro l h; exact hR ⟨(l,j),h⟩ hj

end VertexCover.LabelCover

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_StarMeanContinuous
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

namespace VertexCover.LabelCover
open MeasureTheory

def StarKey (Φ : LabelCover) (d : ℕ) :=
  PositionPair d → Option (Fin Φ.M) × Option (Fin Φ.u) × Option (Fin Φ.v)

noncomputable def starKey (Φ : LabelCover) {d : ℕ} (k : Fin d) (seed : Φ.Seeds d) :
    Φ.StarKey d := by
  classical
  exact fun e => (if e.1.1 = k ∨ e.1.2 = k then none else some (seed e),
    if e.1.1 = k then none else some (Φ.left (seed e)),
    if e.1.2 = k then none else some (Φ.right (seed e)))

noncomputable def starFiber (Φ : LabelCover) {d : ℕ} (k : Fin d) (seed : Φ.Seeds d) :
    Finset (Φ.Seeds d) := by
  classical
  exact Finset.univ.filter (fun seed' => Φ.starKey k seed' = Φ.starKey k seed)

theorem mem_starFiber (Φ : LabelCover) {d : ℕ} (k : Fin d) (seed seed' : Φ.Seeds d) :
    seed' ∈ Φ.starFiber k seed ↔ Φ.starKey k seed' = Φ.starKey k seed := by
  classical
  simp [starFiber]

theorem self_mem_starFiber (Φ : LabelCover) {d : ℕ} (k : Fin d) (seed : Φ.Seeds d) :
    seed ∈ Φ.starFiber k seed := (Φ.mem_starFiber k seed seed).mpr rfl

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_StarEnergyBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Cube
open MeasureTheory
open scoped ENNReal

theorem ae_interval : ∀ᵐ x ∂intervalLaw, |x| ≤ (1 : ℝ) := by
  have h : ∀ᵐ x ∂intervalLaw, x ∈ Set.Icc (-1 : ℝ) 1 :=
    (Measure.ae_ennreal_smul_measure_iff (by norm_num : (1/2 : ℝ≥0∞) ≠ 0)).mpr
      (ae_restrict_mem measurableSet_Icc)
  filter_upwards [h] with x hx
  exact abs_le.mpr hx

theorem ae_block_cube {ι κ : Type*} [Fintype ι] [Fintype κ] :
    ∀ᵐ s ∂blockLaw ι κ, ∀ j k, |s j k| ≤ (1 : ℝ) := by
  classical
  rw [ae_all_iff]
  intro j
  have hinner : ∀ᵐ v ∂law κ, ∀ k, |v k| ≤ (1 : ℝ) := by
    rw [ae_all_iff]
    intro k
    exact (measurePreserving_eval (fun _ : κ => intervalLaw) k).quasiMeasurePreserving.ae ae_interval
  exact (measurePreserving_eval (fun _ : ι => law κ) j).quasiMeasurePreserving.ae hinner

end VertexCover.Cube


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_SeedEnergyBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

noncomputable instance starKeyFintype (Φ : LabelCover) (d : ℕ) : Fintype (Φ.StarKey d) := by
  unfold StarKey
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_OppositePairSeparatorResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

def OppositePairKey (Φ : LabelCover) (d : ℕ) :=
  Φ.Seeds d × (Fin Φ.u ⊕ Fin Φ.v)

noncomputable instance oppositePairKeyFintype (Φ : LabelCover) (d : ℕ) :
    Fintype (Φ.OppositePairKey d) := by
  unfold OppositePairKey
  infer_instance

noncomputable def oppositePairKey (Φ : LabelCover) {d : ℕ}
    (k : Fin d) (e : PositionPair d) (seed : Φ.Seeds d) : Φ.OppositePairKey d := by
  classical
  exact (Function.update seed e ⟨0, Φ.M_pos⟩,
    if e.1.1 = k then Sum.inr (Φ.right (seed e)) else Sum.inl (Φ.left (seed e)))

noncomputable def starFromOppositePair (Φ : LabelCover) {d : ℕ}
    (k : Fin d) (e : PositionPair d) (data : Φ.OppositePairKey d) : Φ.StarKey d := by
  classical
  exact fun b => if b = e then
    (none,
      if e.1.1 = k then none else data.2.elim some (fun _ => none),
      if e.1.2 = k then none else data.2.elim (fun _ => none) some)
    else Φ.starKey k data.1 b

theorem starFromOppositePair_key (Φ : LabelCover) {d : ℕ}
    (k : Fin d) (e : PositionPair d) (he : e.1.1 = k ∨ e.1.2 = k)
    (seed : Φ.Seeds d) :
    Φ.starFromOppositePair k e (Φ.oppositePairKey k e seed) = Φ.starKey k seed := by
  classical
  funext b
  by_cases hb : b = e
  · subst b
    rcases he with hL | hR
    · have hR : e.1.2 ≠ k := by
        intro hh
        have hn := ne_of_lt e.2
        exact hn (hL.trans hh.symm)
      simp [starFromOppositePair, oppositePairKey, starKey, hL, hR]
    · have hL : e.1.1 ≠ k := by
        intro hh
        have hn := ne_of_lt e.2
        exact hn (hh.trans hR.symm)
      simp [starFromOppositePair, oppositePairKey, starKey, hL, hR]
  · simp [starFromOppositePair, oppositePairKey, starKey, hb]

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_ErasedSeedSeparatorAverage
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

namespace VertexCover.LabelCover

noncomputable def erasedSeedFiber (Φ : LabelCover) {d : ℕ}
    (e : PositionPair d) (seed : Φ.Seeds d) : Finset (Φ.Seeds d) := by
  classical
  exact Finset.univ.filter (fun seed' =>
    Function.update seed' e ⟨0, Φ.M_pos⟩ = Function.update seed e ⟨0, Φ.M_pos⟩)

noncomputable def erasedSeedFiberEquiv (Φ : LabelCover) {d : ℕ}
    (e : PositionPair d) (seed : Φ.Seeds d) : Φ.erasedSeedFiber e seed ≃ Fin Φ.M := by
  classical
  exact {
    toFun := fun seed' => seed'.1 e
    invFun := fun c => ⟨Function.update seed e c, by
      simp [erasedSeedFiber, Function.update_idem]⟩
    left_inv := fun seed' => by
      apply Subtype.ext
      funext b
      by_cases hb : b = e
      · subst b
        simp
      · have hh := (Finset.mem_filter.mp seed'.2).2
        have he := congrFun hh b
        simp only [Function.update_of_ne hb] at he ⊢
        exact he.symm
    right_inv := fun c => by simp }

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_OwnGradientUnsupported
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Average
open MeasureTheory

theorem integral_l1_le {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [IsProbabilityMeasure μ] (g : α → ι → ℝ)
    (hg : ∀ i, AEStronglyMeasurable (fun a => g a i) μ)
    (hb : ∀ a, ∑ i, |g a i| ≤ 1) :
    ∑ i, |∫ a, g a i ∂μ| ≤ 1 := by
  have hbi : ∀ a i, |g a i| ≤ 1 := by
    intro a i
    exact (Finset.single_le_sum (fun j _ => abs_nonneg (g a j)) (Finset.mem_univ i)).trans (hb a)
  have hi : ∀ i, Integrable (fun a => |g a i|) μ := by
    intro i
    exact (Integrable.of_bound (hg i) 1
      (Filter.Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hbi a i))).abs
  calc
    (∑ i, |∫ a, g a i ∂μ|) ≤ ∑ i, ∫ a, |g a i| ∂μ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun a => g a i)
    _ = ∫ a, ∑ i, |g a i| ∂μ := (integral_finsetSum _ (fun i _ => hi i)).symm
    _ ≤ ∫ _a, (1 : ℝ) ∂μ := integral_mono
      (integrable_finsetSum _ (fun i _ => hi i)) (integrable_const 1) hb
    _ = 1 := by simp

theorem finite_l1_le {α ι : Type*} [Fintype α] [Fintype ι]
    (g : α → ι → ℝ) (hb : ∀ a, ∑ i, |g a i| ≤ 1) :
    ∑ i, |(∑ a, g a i) / Fintype.card α| ≤ 1 := by
  classical
  by_cases he : IsEmpty α
  · let := he
    simp
  · have : Nonempty α := not_isEmpty_iff.mp he
    have hc : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
    simp only [abs_div, abs_of_nonneg hc.le, ← Finset.sum_div]
    apply (div_le_iff₀ hc).mpr
    calc
      (∑ i, |∑ a, g a i|) ≤ ∑ i, ∑ a, |g a i| := by
        exact Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ a, ∑ i, |g a i| := Finset.sum_comm
      _ ≤ ∑ _a : α, (1 : ℝ) := Finset.sum_le_sum (fun a _ => hb a)
      _ = 1 * Fintype.card α := by simp

end VertexCover.Average

namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory

noncomputable def ownFiber (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (j : J) (i : Φ.Query d) : Finset (Φ.HiddenSeeds J) := by
  classical
  exact Finset.univ.filter (fun hidden => Φ.query (Φ.spliceSeeds J frozen hidden) j = i)

@[simp] theorem mem_ownFiber (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (j : J) (i : Φ.Query d) (hidden : Φ.HiddenSeeds J) :
    hidden ∈ Φ.ownFiber J frozen j i ↔ Φ.query (Φ.spliceSeeds J frozen hidden) j = i := by
  classical
  simp [ownFiber]

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_OwnGradientMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Average
open MeasureTheory

theorem finite_abs_le {α : Type*} [Fintype α] (g : α → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hg : ∀ a, |g a| ≤ B) :
    |(∑ a, g a) / Fintype.card α| ≤ B := by
  classical
  by_cases he : IsEmpty α
  · let := he
    simpa using hB
  · have : Nonempty α := not_isEmpty_iff.mp he
    have hc : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
    rw [abs_div, abs_of_nonneg hc.le]
    apply (div_le_iff₀ hc).mpr
    calc
      |∑ a, g a| ≤ ∑ a, |g a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : α, B := Finset.sum_le_sum (fun a _ => hg a)
      _ = B * Fintype.card α := by simp [mul_comm]

theorem integral_lipschitz {α E : Type*} [MeasurableSpace α] [PseudoMetricSpace E]
    (μ : Measure α) [IsProbabilityMeasure μ] {C : NNReal} (F : E → α → ℝ)
    (hi : ∀ x, Integrable (F x) μ) (hF : ∀ a, LipschitzWith C (fun x => F x a)) :
    LipschitzWith C (fun x => ∫ a, F x a ∂μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, ← integral_sub (hi x) (hi y)]
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun a => F x a - F y a) (C := (C : ℝ) * dist x y)
    (Filter.Eventually.of_forall (fun a => by
      simpa only [dist_eq_norm] using (hF a).dist_le_mul x y))
  simpa only [Real.dist_eq, Real.norm_eq_abs, probReal_univ, mul_one] using h

end VertexCover.Average


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_ThresholdListEnergy
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
attribute [-simp] _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.selectionForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Threshold

noncomputable def slots {ι : Type*} [Fintype ι] (b : ℝ) (g : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun k => b ≤ |g k|)

@[simp] theorem mem_slots {ι : Type*} [Fintype ι] (b : ℝ) (g : ι → ℝ) (k : ι) :
    k ∈ slots b g ↔ b ≤ |g k| := by
  classical
  simp [slots]

theorem coordinate_bound {ι : Type*} [Fintype ι] {g : ι → ℝ}
    (hg : ∑ k, |g k| ≤ 1) (k : ι) : |g k| ≤ 1 := by
  classical
  exact (Finset.single_le_sum (fun i _ => abs_nonneg (g i)) (Finset.mem_univ k)).trans hg

end VertexCover.Threshold

namespace VertexCover.LabelCover.Query

noncomputable def thresholdList {Φ : LabelCover} {d : ℕ} (i : Φ.Query d)
    (b : ℝ) (g : Fin (Φ.WeightDimension d) → ℝ) : List i.LocalLabel := by
  classical
  exact i.labels.filter (fun a => decide (b ≤ |g (i.slot a)|))

@[simp] theorem mem_thresholdList {Φ : LabelCover} {d : ℕ} (i : Φ.Query d)
    (b : ℝ) (g : Fin (Φ.WeightDimension d) → ℝ) (a : i.LocalLabel) :
    a ∈ i.thresholdList b g ↔ b ≤ |g (i.slot a)| := by
  classical
  simp [thresholdList]

theorem thresholdList_nodup {Φ : LabelCover} {d : ℕ} (i : Φ.Query d)
    (b : ℝ) (g : Fin (Φ.WeightDimension d) → ℝ) : (i.thresholdList b g).Nodup := by
  classical
  apply List.Nodup.filter
  unfold labels
  exact Finset.sort_nodup _ _

theorem thresholdList_slots {Φ : LabelCover} {d : ℕ} (i : Φ.Query d)
    (b : ℝ) (hb : 0 < b) (g : Fin (Φ.WeightDimension d) → ℝ)
    (hzero : ∀ k, (∀ a : i.LocalLabel, i.slot a ≠ k) → g k = 0) :
    (i.thresholdList b g).toFinset.image i.slot = VertexCover.Threshold.slots b g := by
  classical
  ext k
  simp only [Finset.mem_image, List.mem_toFinset, mem_thresholdList,
    VertexCover.Threshold.mem_slots]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hk
    by_contra hc
    have hz : ∀ a : i.LocalLabel, i.slot a ≠ k := by
      intro a heq
      exact hc ⟨a, heq ▸ hk, heq⟩
    rw [hzero k hz, abs_zero] at hk
    exact (not_le_of_gt hb) hk

theorem thresholdList_card {Φ : LabelCover} {d : ℕ} (i : Φ.Query d)
    (b : ℝ) (g : Fin (Φ.WeightDimension d) → ℝ)
    (hg : ∑ k, |g k| ≤ 1) : (i.thresholdList b g).length * b ≤ (1 : ℝ) := by
  classical
  have hsub : (i.thresholdList b g).toFinset.image i.slot ⊆ VertexCover.Threshold.slots b g := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨a, ha, rfl⟩
    exact (VertexCover.Threshold.mem_slots b g _).mpr ((i.mem_thresholdList b g a).mp
      (List.mem_toFinset.mp ha))
  calc
    (i.thresholdList b g).length * b = ∑ _k ∈ (i.thresholdList b g).toFinset.image i.slot, b := by
      simp [Finset.card_image_of_injective _ i.slot_injective,
        List.toFinset_card_of_nodup (i.thresholdList_nodup b g)]
    _ ≤ ∑ k ∈ (i.thresholdList b g).toFinset.image i.slot, |g k| := by
      apply Finset.sum_le_sum
      intro k hk
      exact (VertexCover.Threshold.mem_slots b g k).mp (hsub hk)
    _ ≤ ∑ k, |g k| := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => abs_nonneg (g k))
    _ ≤ 1 := hg

end VertexCover.LabelCover.Query


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_OwnMeanPartialAe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Product

theorem update_lipschitz {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℝ) (k : ι) : LipschitzWith 1 (Function.update s k) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro l
  by_cases hl : l = k
  · subst l; simp
  · simp [Function.update_of_ne hl, dist_nonneg]

theorem hasDerivAt_nested_update {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (other : ι → κ → ℝ) (j : ι)
    (s : κ → ℝ) (k : κ) :
    HasDerivAt (fun x => Function.update other j (Function.update s k x))
      (Pi.single j (Pi.single k 1)) (s k) := by
  apply hasDerivAt_pi.mpr
  intro l
  by_cases hl : l = j
  · subst l
    simpa only [Function.update_self, Pi.single_eq_same] using
      hasDerivAt_update s k (s k)
  · simpa only [Function.update_of_ne hl, Pi.single_eq_of_ne hl] using
      hasDerivAt_const (s k) (other l)

end VertexCover.Product


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_PowerValueRepetition
attribute [-instance] _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
noncomputable section

def questionProjection (Φ : LabelCover) (x : Fin Φ.u) (y : Fin Φ.v) (a : Fin Φ.qU) : Fin Φ.qV :=
  if h : ∃ e, Φ.left e = x ∧ Φ.right e = y then Φ.projection h.choose a
  else ⟨0, Φ.qV_pos⟩

theorem questionProjection_at (Φ : LabelCover) (hc : Φ.ParallelCoherent)
    (e : Fin Φ.M) (a : Fin Φ.qU) :
    Φ.questionProjection (Φ.left e) (Φ.right e) a = Φ.projection e a := by
  unfold questionProjection
  split
  · rename_i h
    exact congrFun (hc h.choose e h.choose_spec.1 h.choose_spec.2) a
  · rename_i h
    exact False.elim (h ⟨e, rfl, rfl⟩)

def tupleEquiv (a n : ℕ) : (Fin n → Fin a) ≃ Fin (a ^ n) :=
  Fintype.equivFinOfCardEq (by simp)

def parallelPower (Φ : LabelCover) (n : ℕ) : LabelCover where
  u := Φ.u ^ n
  v := Φ.v ^ n
  qU := Φ.qU ^ n
  qV := Φ.qV ^ n
  M := Φ.M ^ n
  qU_pos := pow_pos Φ.qU_pos _
  qV_pos := pow_pos Φ.qV_pos _
  M_pos := pow_pos Φ.M_pos _
  left e := tupleEquiv Φ.u n (fun i => Φ.left ((tupleEquiv Φ.M n).symm e i))
  right e := tupleEquiv Φ.v n (fun i => Φ.right ((tupleEquiv Φ.M n).symm e i))
  projection e a := tupleEquiv Φ.qV n (fun i => Φ.projection ((tupleEquiv Φ.M n).symm e i)
    ((tupleEquiv Φ.qU n).symm a i))

def repeatLabeling (Φ : LabelCover) (n : ℕ) (A : Φ.Labeling) : (Φ.parallelPower n).Labeling :=
  (fun x => tupleEquiv Φ.qU n (fun i => A.1 ((tupleEquiv Φ.u n).symm x i)),
   fun y => tupleEquiv Φ.qV n (fun i => A.2 ((tupleEquiv Φ.v n).symm y i)))

theorem repeat_perfect (Φ : LabelCover) (n : ℕ) (A : Φ.Labeling) (hA : ∀ e, Φ.Satisfies A e) :
    ∀ e, (Φ.parallelPower n).Satisfies (Φ.repeatLabeling n A) e := by
  intro e
  change tupleEquiv Φ.qV n _ = tupleEquiv Φ.qV n _
  apply congrArg (tupleEquiv Φ.qV n)
  funext i
  simpa only [Satisfies, repeatLabeling, parallelPower, Equiv.symm_apply_apply] using hA ((tupleEquiv Φ.M n).symm e i)

end
end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_PrivateMassSumHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Average
open MeasureTheory

theorem selected_sum_measurable {Ω K : Type*} [MeasurableSpace Ω] [Fintype K] [DecidableEq K]
    (L : Ω → List K) (hL : ∀ k, MeasurableSet {x | k ∈ L x})
    (f : Ω → K → ℝ) (hf : ∀ k, Measurable (fun x => f x k)) :
    Measurable (fun x => ∑ k ∈ (L x).toFinset, f x k) := by
  classical
  have he : ∀ x, (L x).toFinset = Finset.univ.filter (fun k => k ∈ L x) := by
    intro x; ext k; simp
  simp_rw [he, Finset.sum_filter]
  exact Finset.measurable_sum _ (fun k _ => Measurable.ite (hL k) (hf k) measurable_const)

end VertexCover.Average


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_Restriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                               

namespace VertexCover.Restriction

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

structure EnergyForm (E : Type*) [AddCommGroup E] [Module ℝ E] where
  form : E →ₗ[ℝ] E →ₗ[ℝ] ℝ
  symm : ∀ x y, form x y = form y x
  nonneg : ∀ x, 0 ≤ form x x

namespace EnergyForm
variable (B : EnergyForm E)

def energy (x : E) : ℝ := B.form x x

@[simp] theorem energy_zero : B.energy 0 = 0 := by simp [energy]
theorem energy_nonneg (x : E) : 0 ≤ B.energy x := B.nonneg x

theorem energy_add (x y : E) :
    B.energy (x + y) = B.energy x + B.energy y + 2 * B.form x y := by
  simp only [energy, map_add, LinearMap.add_apply]
  rw [B.symm y x]
  ring

theorem energy_sub (x y : E) :
    B.energy (x - y) = B.energy x + B.energy y - 2 * B.form x y := by
  simp only [energy, map_sub, LinearMap.sub_apply]
  rw [B.symm y x]
  ring

structure Projection where
  toLinearMap : E →ₗ[ℝ] E
  idem : ∀ x, toLinearMap (toLinearMap x) = toLinearMap x
  selfAdjoint : ∀ x y, B.form (toLinearMap x) y = B.form x (toLinearMap y)

namespace Projection
variable {B : EnergyForm E}
instance instCoeFunForall : CoeFun (B.Projection) (fun _ => E → E) := ⟨fun P => P.toLinearMap⟩

@[simp] theorem apply_idem (P : B.Projection) (x : E) : P (P x) = P x := P.idem x
@[simp] theorem map_zero (P : B.Projection) : P 0 = 0 := P.toLinearMap.map_zero
@[simp] theorem map_add (P : B.Projection) (x y : E) : P (x + y) = P x + P y :=
  P.toLinearMap.map_add x y
@[simp] theorem map_sub (P : B.Projection) (x y : E) : P (x - y) = P x - P y :=
  P.toLinearMap.map_sub x y
@[simp] theorem map_smul (P : B.Projection) (a : ℝ) (x : E) : P (a • x) = a • P x :=
  P.toLinearMap.map_smul a x

@[ext] theorem ext {P Q : B.Projection} (h : ∀ x, P x = Q x) : P = Q := by
  cases P with
  | mk p hp hs =>
    cases Q with
    | mk q hq ht =>
      have : p = q := LinearMap.ext h
      subst q
      rfl

def ident : B.Projection where
  toLinearMap := LinearMap.id
  idem _ := rfl
  selfAdjoint _ _ := rfl

@[simp] theorem ident_apply (x : E) : (ident : B.Projection) x = x := rfl

def zero : B.Projection where
  toLinearMap := 0
  idem _ := rfl
  selfAdjoint x y := by simp

@[simp] theorem zero_apply (x : E) : (zero : B.Projection) x = 0 := rfl

def residual (P : B.Projection) : B.Projection where
  toLinearMap := LinearMap.id - P.toLinearMap
  idem x := by simp
  selfAdjoint x y := by
    simpa only [LinearMap.sub_apply, LinearMap.id_apply, _root_.map_sub] using
      congrArg (fun value => B.form x y - value) (P.selfAdjoint x y)

@[simp] theorem residual_apply (P : B.Projection) (x : E) : P.residual x = x - P x := rfl
@[simp] theorem residual_residual (P : B.Projection) : P.residual.residual = P := by
  ext x
  simp

theorem inner_image (P : B.Projection) (x : E) : B.form x (P x) = B.energy (P x) := by
  simpa only [P.apply_idem, energy] using (P.selfAdjoint x (P x)).symm

theorem pythagoras (P : B.Projection) (x : E) :
    B.energy x = B.energy (P x) + B.energy (P.residual x) := by
  rw [residual_apply, B.energy_sub, P.inner_image]
  ring

theorem energy_le (P : B.Projection) (x : E) : B.energy (P x) ≤ B.energy x := by
  have h := P.pythagoras x
  have := B.energy_nonneg (P.residual x)
  linarith

def comp (P Q : B.Projection) (h : ∀ x, P (Q x) = Q (P x)) : B.Projection where
  toLinearMap := P.toLinearMap.comp Q.toLinearMap
  idem x := by
    change P (Q (P (Q x))) = P (Q x)
    rw [← h, P.apply_idem, Q.apply_idem]
  selfAdjoint x y := by
    change B.form (P (Q x)) y = B.form x (P (Q y))
    rw [P.selfAdjoint, Q.selfAdjoint, h]

@[simp] theorem comp_apply (P Q : B.Projection) (h) (x : E) : P.comp Q h x = P (Q x) := rfl

theorem residual_commute (P Q : B.Projection) (h : ∀ x, P (Q x) = Q (P x)) (x : E) :
    P.residual (Q x) = Q (P.residual x) := by
  simp [h]

theorem comp_loss_le (P Q : B.Projection) (h : ∀ x, P (Q x) = Q (P x)) (x : E) :
    B.energy ((P.comp Q h).residual x) ≤
      B.energy (P.residual x) + B.energy (Q.residual x) := by
  have h₁ := P.pythagoras (Q x)
  have h₂ := Q.pythagoras x
  have h₃ := (P.comp Q h).pythagoras x
  have h₄ := Q.energy_le (P.residual x)
  rw [← P.residual_commute Q h] at h₄
  simp only [comp_apply] at h₃
  linarith

theorem residual_le_of_nested (P Q : B.Projection) (h : ∀ x, P (Q x) = Q x) (x : E) :
    B.energy (P.residual x) ≤ B.energy (Q.residual x) := by
  have horth : B.form (P.residual x) (P x - Q x) = 0 := by
    rw [residual_apply]
    simp only [_root_.map_sub, LinearMap.sub_apply]
    rw [P.selfAdjoint x (P x), P.apply_idem, P.selfAdjoint x (Q x), h]
    ring
  have he := B.energy_add (P.residual x) (P x - Q x)
  have hs : P.residual x + (P x - Q x) = Q.residual x := by simp
  rw [hs, horth, mul_zero, add_zero] at he
  have := B.energy_nonneg (P x - Q x)
  linarith

def productMap {ι : Type*} (P : ι → B.Projection) : List ι → E →ₗ[ℝ] E
  | [] => LinearMap.id
  | i :: is => (P i).toLinearMap.comp (productMap P is)

@[simp] theorem productMap_nil {ι : Type*} (P : ι → B.Projection) (x : E) :
    productMap P [] x = x := rfl
@[simp] theorem productMap_cons {ι : Type*} (P : ι → B.Projection)
    (i : ι) (is : List ι) (x : E) :
    productMap P (i :: is) x = P i (productMap P is x) := rfl

@[simp] theorem productMap_append {ι : Type*} (P : ι → B.Projection)
    (is js : List ι) (x : E) :
    productMap P (is ++ js) x = productMap P is (productMap P js x) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, productMap_cons, ih]

theorem productMap_commute {ι : Type*} (P : ι → B.Projection)
    (Q : B.Projection) (h : ∀ i, ∀ x, P i (Q x) = Q (P i x))
    (is : List ι) (x : E) :
    productMap P is (Q x) = Q (productMap P is x) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [productMap_cons, ih, h]

theorem productMap_fixed_of_mem {ι : Type*} (P : ι → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (is : List ι) (j : ι) (hj : j ∈ is) (x : E) :
    P j (productMap P is x) = productMap P is x := by
  induction is with
  | nil => simp at hj
  | cons i is ih =>
    rcases List.mem_cons.mp hj with rfl | ht
    · simp only [productMap_cons, apply_idem]
    · simp only [productMap_cons, h j i, ih ht]

def product {ι : Type*} (P : ι → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (is : List ι) : B.Projection where
  toLinearMap := productMap P is
  idem x := by
    induction is with
    | nil => rfl
    | cons i is ih =>
      simp only [productMap_cons]
      rw [productMap_commute P (P i) (fun j => h j i), (P i).apply_idem, ih]
  selfAdjoint x y := by
    induction is generalizing x y with
    | nil => rfl
    | cons i is ih =>
      simp only [productMap_cons]
      rw [(P i).selfAdjoint, ih,
        productMap_commute P (P i) (fun j => h j i)]

@[simp] theorem product_apply {ι : Type*} (P : ι → B.Projection) (h) (is : List ι)
    (x : E) : product P h is x = productMap P is x := rfl

theorem product_loss_le {ι : Type*} (P : ι → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (is : List ι) (x : E) :
    B.energy ((product P h is).residual x) ≤
      (is.map (fun i => B.energy ((P i).residual x))).sum := by
  induction is with
  | nil => simp [residual_apply]
  | cons i is ih =>
    have hc : ∀ x, P i (product P h is x) = product P h is (P i x) :=
      fun x => (productMap_commute P (P i) (fun j => h j i) is x).symm
    have he : product P h (i :: is) = (P i).comp (product P h is) hc := by
      ext x
      rfl
    rw [he, List.map_cons, List.sum_cons]
    exact ((P i).comp_loss_le (product P h is) hc x).trans (add_le_add le_rfl ih)

def difference (P : ℕ → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x)) (i : ℕ) : B.Projection :=
  (P i).residual.comp (product P h (List.range i)) (fun x => by
    simp only [residual_apply, product_apply, _root_.map_sub]
    rw [productMap_commute P (P i) (fun k => h k i)])

@[simp] theorem difference_apply (P : ℕ → B.Projection) (h) (i : ℕ) (x : E) :
    difference P h i x = productMap P (List.range i) x -
      P i (productMap P (List.range i) x) := rfl

theorem difference_energy_sum (P : ℕ → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x)) (n : ℕ) (x : E) :
    (∑ i ∈ Finset.range n, B.energy (difference P h i x)) +
      B.energy (productMap P (List.range n) x) = B.energy x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, productMap_append]
    simp only [productMap_cons, productMap_nil]
    rw [productMap_commute P (P n) (fun k => h k n)]
    have he := (P n).pythagoras (productMap P (List.range n) x)
    simp only [residual_apply] at he
    rw [difference_apply]
    linarith

theorem difference_energy_sum_le (P : ℕ → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x)) (n : ℕ) (x : E) :
    (∑ i ∈ Finset.range n, B.energy (difference P h i x)) ≤ B.energy x := by
  have := difference_energy_sum P h n x
  have := B.energy_nonneg (productMap P (List.range n) x)
  linarith

theorem difference_commute (P : ℕ → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (Q : B.Projection) (hq : ∀ i, ∀ x, P i (Q x) = Q (P i x))
    (i : ℕ) (x : E) : difference P h i (Q x) = Q (difference P h i x) := by
  simp only [difference_apply, productMap_commute P Q hq, map_sub, hq]

theorem difference_residual_budget (P : ℕ → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (Q : B.Projection) (hq : ∀ i, ∀ x, P i (Q x) = Q (P i x))
    (n : ℕ) (x : E) :
    (∑ i ∈ Finset.range n, B.energy (Q.residual (difference P h i x))) ≤
      B.energy (Q.residual x) := by
  have hr : ∀ i, ∀ x, P i (Q.residual x) = Q.residual (P i x) := by
    intro i x
    simp [hq]
  simpa only [← difference_commute P h Q.residual hr] using
    difference_energy_sum_le P h n (Q.residual x)

theorem difference_retained_le (P : ℕ → B.Projection)
    (h : ∀ i j, ∀ x, P i (P j x) = P j (P i x))
    (Q : B.Projection) (hq : ∀ i, ∀ x, P i (Q x) = Q (P i x))
    (i : ℕ) (x : E) : B.energy (Q (difference P h i x)) ≤ B.energy (Q x) := by
  rw [← difference_commute P h Q hq]
  exact (difference P h i).energy_le (Q x)

theorem productMap_map {ι κ : Type*} (P : κ → B.Projection) (g : ι → κ)
    (is : List ι) (x : E) :
    productMap P (is.map g) x = productMap (fun i => P (g i)) is x := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [List.map_cons, productMap_cons, ih]

def natExtension {d : ℕ} (P : Fin d → B.Projection) (i : ℕ) : B.Projection :=
  if h : i < d then P ⟨i,h⟩ else ident

end Projection
end EnergyForm
end VertexCover.Restriction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_SeparatorBoundCube
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
attribute [-simp] _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.mem_ownFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory

theorem query_splice_outside (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (hidden : Φ.HiddenSeeds J) (j : Fin d) (hj : j ∉ J) :
    Φ.query (Φ.spliceSeeds J frozen hidden) j = Φ.query frozen j := by
  classical
  apply Φ.query_eq_of_questions
  · intro k h
    have hn : (⟨(j,k),h⟩ : PositionPair d) ∉ internalPairs J := by
      simp [internalPairs, hj]
    simp [spliceSeeds, hn]
  · intro k h
    have hn : (⟨(k,j),h⟩ : PositionPair d) ∉ internalPairs J := by
      simp [internalPairs, hj]
    simp [spliceSeeds, hn]

noncomputable def spliceWeights (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Fin d → Fin (Φ.WeightDimension d) → ℝ) (s : Φ.BatchWeights J) :
      Fin d → Fin (Φ.WeightDimension d) → ℝ := by
  classical
  exact fun j => if h : j ∈ J then s ⟨j,h⟩ else frozen j

noncomputable def outsideSum (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (weights : Fin d → Fin (Φ.WeightDimension d) → ℝ) :
    Φ.Coordinate d → ℝ := ∑ j ∈ Jᶜ, Φ.increment (Φ.query frozen j) (weights j)

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_VarianceProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Product
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem bounded_memLp (f : X → ℝ) (hf : Measurable f) {C : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hb)

theorem bounded_integral_norm (f : X → ℝ) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) :
    ‖∫ x, f x ∂μ‖ ≤ C := by
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hb)

theorem mean_measurable (f : X → Y → ℝ) (hf : Measurable (Function.uncurry f)) :
    Measurable (fun x => ∫ y, f x y ∂ν) :=
  hf.stronglyMeasurable.integral_prod_right.measurable

theorem mean_memLp (f : X → Y → ℝ) (hf : Measurable (Function.uncurry f)) {C : ℝ}
    (hb : ∀ x y, ‖f x y‖ ≤ C) : MemLp (fun x => ∫ y, f x y ∂ν) 2 μ :=
  bounded_memLp μ _ (mean_measurable ν f hf) (fun x => bounded_integral_norm ν _ (hb x))

theorem variance_product (f : X → Y → ℝ) (hf : Measurable (Function.uncurry f)) {C : ℝ}
    (hb : ∀ x y, ‖f x y‖ ≤ C) :
    variance (Function.uncurry f) (μ.prod ν) =
      (∫ x, variance (f x) ν ∂μ) + variance (fun x => ∫ y, f x y ∂ν) μ := by
  have hp := bounded_memLp (μ.prod ν) _ hf (fun p => hb p.1 p.2)
  have hs : ∀ x, MemLp (f x) 2 ν := fun x =>
    bounded_memLp ν _ (hf.comp (measurable_const.prodMk measurable_id)) (hb x)
  have hm := mean_memLp μ ν f hf hb
  simp_rw [variance_eq_sub (hs _)]
  rw [variance_eq_sub hp, variance_eq_sub hm]
  simp only [Pi.pow_apply]
  dsimp only [Function.uncurry] at hp ⊢
  have hi : Integrable (fun x => ∫ y, (f x y)^2 ∂ν) μ := hp.integrable_sq.integral_prod_left
  have he2 : (∫ p : X × Y, (f p.1 p.2)^2 ∂μ.prod ν) =
      ∫ x, ∫ y, (f x y)^2 ∂ν ∂μ := integral_prod _ hp.integrable_sq
  have he1 : (∫ p : X × Y, f p.1 p.2 ∂μ.prod ν) =
      ∫ x, ∫ y, f x y ∂ν ∂μ := integral_prod _ (hp.integrable (by norm_num))
  rw [integral_sub hi hm.integrable_sq, he2, he1]
  ring

theorem section_variance_integrable (f : X → Y → ℝ)
    (hf : Measurable (Function.uncurry f)) {C : ℝ} (hb : ∀ x y, ‖f x y‖ ≤ C) :
    Integrable (fun x => variance (f x) ν) μ := by
  have hp := bounded_memLp (μ.prod ν) _ hf (fun p => hb p.1 p.2)
  have hs : ∀ x, MemLp (f x) 2 ν := fun x =>
    bounded_memLp ν _ (hf.comp (measurable_const.prodMk measurable_id)) (hb x)
  have hm := mean_memLp μ ν f hf hb
  simp_rw [variance_eq_sub (hs _)]
  exact hp.integrable_sq.integral_prod_left.sub hm.integrable_sq

theorem variance_mean_le (f : X → Y → ℝ) (hf : Measurable (Function.uncurry f)) {C : ℝ}
    (hb : ∀ x y, ‖f x y‖ ≤ C) :
    variance (fun x => ∫ y, f x y ∂ν) μ ≤ ∫ y, variance (fun x => f x y) μ ∂ν := by
  let g : Y → ℝ := fun y => ∫ x, f x y ∂μ
  let D : X → Y → ℝ := fun x y => f x y - g y
  have hg : Measurable g := mean_measurable μ (fun y x => f x y) (hf.comp measurable_swap)
  have hgb : ∀ y, ‖g y‖ ≤ C := fun y => bounded_integral_norm μ _ (fun x => hb x y)
  have hd : Measurable (Function.uncurry D) := hf.sub (hg.comp measurable_snd)
  have hdb : ∀ x y, ‖D x y‖ ≤ 2*C := fun x y => by
    exact (norm_sub_le _ _).trans (by linarith [hb x y, hgb y])
  have hp := bounded_memLp (μ.prod ν) _ hd (fun p => hdb p.1 p.2)
  have hs : ∀ x, MemLp (D x) 2 ν := fun x =>
    bounded_memLp ν _ (hd.comp (measurable_const.prodMk measurable_id)) (hdb x)
  have hm := mean_memLp μ ν f hf hb
  have hfp := bounded_memLp (μ.prod ν) _ hf (fun p => hb p.1 p.2)
  have hfx : ∀ x, Integrable (f x) ν := fun x =>
    (bounded_memLp ν _ (hf.comp (measurable_const.prodMk measurable_id)) (hb x)).integrable (by norm_num)
  have hgi := (bounded_memLp ν g hg hgb).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hei : ∫ y, g y ∂ν = ∫ x, ∫ y, f x y ∂ν ∂μ := by
    exact (integral_integral_swap (hfp.integrable (by norm_num))).symm
  have he : ∀ x, (∫ y, f x y ∂ν) - ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, D x y ∂ν := by
    intro x
    dsimp only [D]
    rw [integral_sub (hfx x) hgi, hei]
  rw [variance_eq_integral hm.aemeasurable]
  simp_rw [he]
  calc
    _ ≤ ∫ x, ∫ y, (D x y)^2 ∂ν ∂μ := by
      apply integral_mono
      · exact (mean_memLp μ ν D hd hdb).integrable_sq
      · exact hp.integrable_sq.integral_prod_left
      · intro x
        simpa only [probReal_univ, one_mul] using Cube.sq_integral_le_measure_mul ν (hs x)
    _ = ∫ y, ∫ x, (D x y)^2 ∂μ ∂ν := integral_integral_swap hp.integrable_sq
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y =>
        (variance_eq_integral (hf.comp (measurable_id.prodMk measurable_const)).aemeasurable).symm)

theorem variance_product_le (f : X → Y → ℝ) (hf : Measurable (Function.uncurry f)) {C : ℝ}
    (hb : ∀ x y, ‖f x y‖ ≤ C) :
    variance (Function.uncurry f) (μ.prod ν) ≤
      (∫ x, variance (f x) ν ∂μ) + ∫ y, variance (fun x => f x y) μ ∂ν := by
  rw [variance_product μ ν f hf hb]
  exact add_le_add le_rfl (variance_mean_le μ ν f hf hb)

end VertexCover.Product


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_VariancePi
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Product
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem cons_measurePreserving (n : ℕ) :
    MeasurePreserving (fun p : X × (Fin n → X) => Fin.cons p.1 p.2)
      (μ.prod (Measure.pi (fun _ : Fin n => μ))) (Measure.pi (fun _ : Fin (n+1) => μ)) := by
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero', Fin.zero_succAbove] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm

theorem integral_cons (n : ℕ) (f : (Fin (n+1) → X) → ℝ)
    (hi : Integrable f (Measure.pi (fun _ => μ))) :
    ∫ v, f v ∂Measure.pi (fun _ : Fin (n+1) => μ) =
      ∫ x, ∫ s, f (Fin.cons x s) ∂Measure.pi (fun _ : Fin n => μ) ∂μ := by
  have hp := cons_measurePreserving μ n
  calc
    _ = ∫ p : X × (Fin n → X), f (Fin.cons p.1 p.2) ∂μ.prod (Measure.pi (fun _ => μ)) := by
      rw [← hp.map_eq]
      exact integral_map hp.aemeasurable (by rw [hp.map_eq]; exact hi.aestronglyMeasurable)
    _ = _ := integral_prod _ (hp.integrable_comp_of_integrable hi)

noncomputable def coordinateVariance {n : ℕ} (f : (Fin n → X) → ℝ)
    (j : Fin n) (s : Fin n → X) : ℝ :=
  variance (fun x => f (Function.update s j x)) μ

end VertexCover.Product


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_VarianceCoordinateSum
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Cube.law_negInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

namespace VertexCover.Cube
open MeasureTheory ProbabilityTheory
open scoped ENNReal

abbrev carrier (n : ℕ) : Set (Fin n → ℝ) := Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1)

theorem measurableSet_carrier (n : ℕ) : MeasurableSet (carrier n) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

theorem ae_carrier (n : ℕ) : ∀ᵐ s ∂law (Fin n), s ∈ carrier n := by
  rw [law_eq_restrict_volume]
  exact (Measure.ae_ennreal_smul_measure_iff (pow_ne_zero _ (by norm_num) :
    (1/2 : ℝ≥0∞) ^ Fintype.card (Fin n) ≠ 0)).mpr
    (ae_restrict_mem (measurableSet_carrier n))

theorem norm_le_one_of_mem_carrier {n : ℕ} {s : Fin n → ℝ} (hs : s ∈ carrier n) :
    ‖s‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro k
  exact (abs_le.mpr (Set.mem_univ_pi.mp hs k))

noncomputable def boundedVersion {n : ℕ} (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  (carrier n).indicator f

theorem boundedVersion_measurable {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) : Measurable (boundedVersion f) :=
  hf.indicator (measurableSet_carrier n)

theorem boundedVersion_ae {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    boundedVersion f =ᵐ[law (Fin n)] f := by
  filter_upwards [ae_carrier n] with s hs
  exact Set.indicator_of_mem hs f

theorem boundedVersion_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith 1 f) (s : Fin n → ℝ) :
    ‖boundedVersion f s‖ ≤ ‖f 0‖ + 1 := by
  by_cases hs : s ∈ carrier n
  · rw [boundedVersion, Set.indicator_of_mem hs]
    have h := hf.dist_le_mul s 0
    simp only [NNReal.coe_one, one_mul, dist_zero_right, Real.dist_eq] at h
    calc
      ‖f s‖ ≤ ‖f s - f 0‖ + ‖f 0‖ := by simpa using norm_add_le (f s - f 0) (f 0)
      _ ≤ 1 + ‖f 0‖ := by simpa only [Real.norm_eq_abs, add_comm] using add_le_add_right (h.trans (norm_le_one_of_mem_carrier hs)) ‖f 0‖
      _ = _ := add_comm _ _
  · rw [boundedVersion, Set.indicator_of_notMem hs]
    simp only [norm_zero]
    positivity

end VertexCover.Cube

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_WeightEnergyBudget
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Cube
open MeasureTheory

theorem ae_cube {ι : Type*} [Fintype ι] :
    ∀ᵐ s ∂law ι, ∀ j, |s j| ≤ (1 : ℝ) := by
  rw [ae_all_iff]
  intro j
  exact (measurePreserving_eval (fun _ : ι => intervalLaw) j).quasiMeasurePreserving.ae ae_interval

end VertexCover.Cube

namespace VertexCover.LabelCover
open MeasureTheory

noncomputable def weightMean (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) : ℝ :=
  ∫ x, Φ.separator A hA (Φ.continuousSum seed (Function.update s k x))
    ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d))

theorem weightMean_measurable (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) : Measurable (Φ.weightMean A hA k seed) := by
  classical
  have hc : Continuous (fun p : (Fin d → Fin (Φ.WeightDimension d) → ℝ) ×
      (Fin (Φ.WeightDimension d) → ℝ) =>
      Φ.separator A hA (Φ.continuousSum seed (Function.update p.1 k p.2))) :=
    (Φ.separator_continuousSum_continuous A hA seed).comp
      (continuous_fst.update k continuous_snd)
  exact hc.stronglyMeasurable.integral_prod_right.measurable

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_ConditionNested
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Restriction
open scoped BigOperators
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace EnergyForm

namespace Projection
variable {B : EnergyForm E}

section Conditional
variable {S T : Type*} [Fintype S]

noncomputable def fiberSize (q : S → T) (t : T) : ℕ := by
  classical
  exact (Finset.univ.filter (fun s => q s = t)).card

noncomputable def fiberKernel (q : S → T) (s t : S) : ℝ := by
  classical
  exact if q t = q s then (fiberSize q (q s) : ℝ)⁻¹ else 0

end Conditional
end Projection
end EnergyForm
end VertexCover.Restriction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_NatDiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                       
section

namespace VertexCover.Machine
namespace Divide
abbrev State := ℕ × (ℕ × ℕ)

def body (p : State) : Bool × State :=
  if 0 < p.1 ∧ p.1 ≤ p.2.1 then (true,(p.1,(p.2.1-p.1,p.2.2+1))) else (false,p)

def result (p : State) : State := (p.1,(p.2.1%p.1,p.2.2+p.2.1/p.1))

end Divide

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_FixedOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                             
section

namespace VertexCover.Machine

noncomputable def fixedSelect {α ι β : Type} [DecidableEq ι]
    (f : α → ι → β) (i₀ : ι) : List ι → α × ι → β
  | [], x => f x.1 i₀
  | i::xs, x => if x.2=i then f x.1 i else fixedSelect f i₀ xs x

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListMore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                         
section

namespace VertexCover.Machine

theorem foldl_cons_eq_reverse_append {α : Type} (xs b : List α) :
    xs.foldl (fun b a => a::b) b = xs.reverse ++ b := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih => simp [ih, List.append_assoc]

theorem foldl_map_cons {α β : Type} (f : α → β) (xs : List α) (b : List β) :
    xs.foldl (fun b a => f a::b) b = (xs.map f).reverse++b := by
  induction xs generalizing b with
  | nil => rfl
  | cons a as ih => simp [ih, List.append_assoc]

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                        
section

namespace VertexCover.Machine

namespace Range

def step (p : ℕ × List ℕ) : ℕ × List ℕ := (p.1+1,p.1::p.2)

end Range

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListParam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                          
section

namespace VertexCover.Machine

namespace WithParam
variable {α β : Type}

def step (p : (α × List (α × β)) × β) : α × List (α × β) :=
  (p.1.1,(p.1.1,p.2)::p.1.2)

theorem fold (xs : List β) (a : α) (out : List (α × β)) :
    xs.foldl (fun s b => step (s,b)) (a,out) = (a,(xs.map (a,·)).reverse++out) := by
  induction xs generalizing out with
  | nil => rfl
  | cons b xs ih =>
    change xs.foldl (fun s b => step (s,b)) (a,(a,b)::out) = _
    rw [ih]
    simp only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]

end WithParam

theorem foldl_reverseAppend {α : Type} (xs : List (List α)) (out : List α) :
    xs.foldl (fun b a => a.reverse++b) out = xs.flatten.reverse++out := by
  induction xs generalizing out with
  | nil => rfl
  | cons a xs ih => simp [List.foldl_cons,ih,List.append_assoc]

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Option
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                          
section

namespace VertexCover.Machine

def optionBits {α : Type} (ea : α → List Bool) : Option α → List Bool
  | none => [false]
  | some a => true::ea a

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ExpanderStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine

namespace ExpandMachine

def lookup (q : ℕ) (p : List ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  let r := p.1.getD (p.2.2+q*p.2.1) 0
  (r/q,r%q)

end ExpandMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ExpanderBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                  
section

namespace VertexCover.Machine

namespace ExpandMachine

theorem encoding_bound (q g n p v₀ v l N L : ℕ)
    (hn : n ≤ N) (hp : p ≤ N) (hv : v₀ ≤ N) (hl : l ≤ n)
    (hb : v ≤ max v₀ (g*p)) (hlen : L ≤ 2*v+2+(v*q)*(2*(v*q)+2)) :
    2*l+1+(2*p+1+L) ≤ 20*((g+1)*(q+1)+1)^2*(N+1)^2 := by
  let C := g+1
  let R := C*(q+1)+1
  let B := R*(N+1)
  have hm : v ≤ C*N := by
    apply hb.trans
    apply max_le
    · dsimp [C]; nlinarith only [hv,Nat.zero_le (g*N)]
    · exact (Nat.mul_le_mul_left g hp).trans (by dsimp [C]; nlinarith only [Nat.zero_le N])
  have hr : 1 ≤ R := by dsimp [R]; omega
  have hc : C ≤ R := by dsimp [R]; nlinarith only [Nat.zero_le (C*q)]
  have hcq : C*q ≤ R := by dsimp [R]; nlinarith only [Nat.zero_le C]
  have hB : 1 ≤ B := Nat.mul_le_mul hr (Nat.succ_le_succ (Nat.zero_le N))
  have hNB : N ≤ B := (Nat.le_succ N).trans (by
    simpa only [one_mul] using Nat.mul_le_mul_right (N+1) hr)
  have hvB : v ≤ B := hm.trans (Nat.mul_le_mul hc (Nat.le_succ N))
  have hqB : v*q ≤ B := by
    calc
      v*q ≤ C*N*q := Nat.mul_le_mul_right q hm
      _ = (C*q)*N := by ring
      _ ≤ B := Nat.mul_le_mul hcq (Nat.le_succ N)
  have hsquare := Nat.mul_le_mul hqB hqB
  have hlinear : B ≤ B*B := by simpa only [one_mul] using Nat.mul_le_mul_right B hB
  have hlB := (hl.trans hn).trans hNB
  have hpB := hp.trans hNB
  change _ ≤ 20*R^2*(N+1)^2
  rw [show 20*R^2*(N+1)^2=20*B^2 by dsimp [B]; ring]
  nlinarith only [hB,hlinear,hvB,hqB,hsquare,hlen,hlB,hpB]

end ExpandMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Cloud
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine

namespace CloudMachine

 theorem map_finRange_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

end CloudMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                           
section

namespace VertexCover.Machine

 theorem foldl_bits_le {α β : Type} (eb : β → List Bool)
    (f : β × α → β) (h : ∀ b a, (eb (f (b,a))).length ≤ (eb b).length)
    (xs : List α) (b : β) :
    (eb (xs.foldl (fun b a => f (b,a)) b)).length ≤ (eb b).length := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih => exact (ih (f (b,a))).trans (h b a)

namespace ListCompare
variable {α : Type} [DecidableEq α]
def step (p : (List α × Bool) × α) : List α × Bool :=
  (p.1.1.tail, p.1.2 && match p.1.1 with | [] => false | b::_ => decide (p.2=b))

theorem result (xs ys : List α) (b : Bool) :
    let p := xs.foldl (fun p a => step (p,a)) (ys,b)
    (p.2 && p.1.isEmpty) = (b && decide (xs=ys)) := by
  induction xs generalizing ys b with
  | nil => cases ys <;> simp
  | cons a xs ih =>
    dsimp only
    trans ((step ((ys,b),a)).2 && decide (xs=(step ((ys,b),a)).1))
    · exact ih _ _
    · cases ys with
      | nil => simp [step]
      | cons y ys =>
        by_cases h : a=y <;> simp [step,h]

end ListCompare

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListGrowing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                            
section

namespace VertexCover.Machine

 theorem foldl_or_any {α : Type} (f : α → Bool) (xs : List α) (b : Bool) :
    (xs.map f).foldl (· || ·) b = (b || xs.any f) := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih => simp [ih,Bool.or_assoc]

namespace Dedup
variable {α : Type} [BEq α]
def step (p : List α × α) : List α := if p.1.any (p.2 == ·) then p.1 else p.2::p.1

theorem fold (xs out : List α) :
    (xs.foldl (fun s a => step (s,a)) out).reverse = List.eraseDupsBy.loop (· == ·) xs out := by
  induction xs generalizing out with
  | nil => rfl
  | cons a xs ih =>
    change (xs.foldl (fun s a => step (s,a)) (step (out,a))).reverse = _
    rw [ih]
    simp only [step,List.eraseDupsBy.loop]
    cases h : out.any (a == ·) <;> rfl

end Dedup

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                              
section

namespace VertexCover.Machine
namespace Index
variable {α : Type} [BEq α]
def step (p : (α × ℕ) × α) : α × ℕ :=
  (p.1.1,if p.2 == p.1.1 then 0 else p.1.2+1)

theorem foldr (xs : List α) (a : α) :
    xs.foldr (fun x s => step (s,x)) (a,0) = (a,xs.idxOf a) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldr_cons,ih]
    simp only [step,List.idxOf_cons,cond_eq_if]

end Index

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_CloudIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                      
section

namespace VertexCover.Machine.CloudMachine

 theorem idxOf_map_injective {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hf : Function.Injective f) (xs : List α) (a : α) :
    (xs.map f).idxOf (f a) = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.idxOf_cons]
    have h : (f x == f a) = (x == a) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq,hf.eq_iff]
    rw [h,ih]

 theorem getD_idxOf {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (a d : α) (h : a ∈ xs) : xs.getD (xs.idxOf a) d = a := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_idxOf h]
  rfl

end VertexCover.Machine.CloudMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Address
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine

namespace FixedSearch

def run {α ι β : Type} (p : α → ι → Bool) (f : α → ι → β) (z : β) : List ι → α → β
  | [], _ => z
  | i::xs, a => if p a i then f a i else run p f z xs a

end FixedSearch

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_BoundedBinary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                  
section

namespace VertexCover.Machine
open UniqueGames.BinaryEncoding

namespace CappedBinary

theorem min_bit (B n : ℕ) (b : Bool) :
    min B (Nat.bit b (min B n)) = min B (Nat.bit b n) := by
  cases b <;> simp only [Nat.bit,Bool.cond_false,Bool.cond_true] <;> omega

end CappedBinary

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ParseFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                               
section

namespace VertexCover.Machine.FrameParser
open UniqueGames.BinaryEncoding

def next (q : Fin 3) (b : Bool) : Fin 3 :=
  if q=0 then (if b then 1 else 2) else if q=1 then 0 else 2

def state : Fin 3 → List Bool → Fin 3
  | q,[] => q
  | q,b::bs => state (next q b) bs

def trans (mode : Fin 3) (q : Fin 3) (b : Bool) : Fin 3 × List Bool :=
  (next q b, if (mode=0 ∧ q=1) ∨ (mode=1 ∧ q=2) then [b] else [])

def finish (mode : Fin 3) (q : Fin 3) : List Bool :=
  if mode=2 then [decide (q=2)] else []

theorem after_state (bs : List Bool) : state 2 bs = 2 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa only [state,next,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,ite_false] using ih

end VertexCover.Machine.FrameParser
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ParseName
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                              
section

namespace VertexCover.Machine.NameParser
open UniqueGames.BinaryEncoding

def canonical : List Bool → Bool
  | [] => true
  | [b] => b
  | _::b::bs => canonical (b::bs)

def trans (_ : Bool) (b : Bool) : Bool × List Bool := (b,[])

end VertexCover.Machine.NameParser
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ParseClause
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                
section

namespace VertexCover.Machine

namespace Parser
abbrev P (α : Type) := List Bool → Option (α × List Bool)

def seq {α β : Type} (pa : P α) (pb : P β) : P (α × β) := fun input => do
  let (a,rest) ← pa input
  let (b,rest) ← pb rest
  return ((a,b),rest)

end Parser

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Approximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                             
section

namespace VertexCover
open Machine

theorem rational_threshold (m n k : ℕ) (hm : 1 ≤ m) :
    m*k < (m-1)*n ↔ (k : ℝ) < (1-1/(m:ℝ))*(n:ℝ) := by
  have hmp : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have he : (1-1/(m:ℝ))*(n:ℝ) = (((m-1:ℕ):ℝ)*n)/(m:ℝ) := by
    rw [Nat.cast_sub hm,Nat.cast_one]
    field_simp
  rw [he,lt_div_iff₀ hmp]
  rw [mul_comm (k:ℝ) (m:ℝ)]
  exact_mod_cast Iff.rfl

end VertexCover
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_DenseParse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                               
section

namespace VertexCover.Machine
namespace FormulaParser
open UniqueGames.BinaryFormula

abbrev Triple (α : Type) := (α × α) × α
abbrev FormulaData := ℕ × List (Triple (Bool × ℕ))

end FormulaParser
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_BinaryOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine
namespace BinaryOutput
 theorem bits_step (n : ℕ) (hn : n≠0) : n.bits=decide (n%2=1)::(n/2).bits := by
  have he : Nat.bit (decide (n%2=1)) (n/2)=n := by
    have hm := Nat.mod_lt n (by decide : 0<2)
    have hv := Nat.mod_add_div n 2
    by_cases h : n%2=1 <;> simp [Nat.bit,h] <;> omega
  conv_lhs => rw [← he]
  rw [Nat.bits_append_bit _ _ (by
    intro hz
    by_contra hb
    have hh : decide (n%2=1)=false := by cases h : decide (n%2=1) <;> simp_all
    rw [hh,hz] at he
    exact hn he.symm)]
end BinaryOutput
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_NormRepresentation
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                       
section

namespace VertexCover.LabelCover
 theorem finset_lift_injective {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (I : Finset β) (hI : ∀ p ∈ I, ∃ a, f a=p) :
    ∃ S : Finset α, S.image f=I ∧ Set.InjOn f S := by
  classical
  let g : I → α := fun p => (hI p p.property).choose
  have hg (p : I) : f (g p)=p := (hI p p.property).choose_spec
  refine ⟨Finset.univ.image g,?_,?_⟩
  · ext p
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨a,⟨q,rfl⟩,rfl⟩; rw [hg]; exact q.property
    · intro hp; exact ⟨g ⟨p,hp⟩,⟨⟨p,hp⟩,rfl⟩,hg ⟨p,hp⟩⟩
  · intro a ha b hb h
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hb
    rw [hg,hg] at h
    exact congrArg g (Subtype.ext h)
 theorem norm_le_representations (Φ : LabelCover) {d : ℕ} {α : Type*} [Fintype α]
    (f : α → Φ.Coordinate d) (z : Φ.Coordinate d → ℝ) (B : Finset (Φ.Query d))
    (hz : ∀ p, p.1 ∉ B → z p=0)
    (hc : ∀ p : Φ.Coordinate d, p.1 ∈ B → ∃ a, f a=p) (C : ℝ) :
    Φ.compatibilityNorm z ≤ C ↔
      ∀ S : Finset α, Set.InjOn f S → Φ.Compatible (S.image f) → |∑ a ∈ S, z (f a)| ≤ C := by
  classical
  constructor
  · intro h S hi hs
    have he : ∑ p ∈ S.image f, z p = ∑ a ∈ S, z (f a) := Finset.sum_image hi
    rw [← he]
    exact (Φ.form_le_norm z _ hs).trans h
  · intro h
    obtain ⟨I,hi,hb,he⟩ := Φ.norm_attained_on_support z B hz
    obtain ⟨S,hs,hinj⟩ := finset_lift_injective f I (fun p hp => hc p (hb p hp))
    rw [he,← hs,Finset.sum_image hinj]
    exact h S hinj (hs.symm ▸ hi)
end VertexCover.LabelCover
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Profile
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
attribute [-simp] _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.selectionForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                            
section

namespace VertexCover.LabelCover.Query

variable {Φ : LabelCover} {d : ℕ}
abbrev Profile (a b d : ℕ) := (Fin d → Fin a) × (Fin d → Fin b)
def encodeAssignment (i : Φ.Query d) (A : i.Assignment) : Profile Φ.qU Φ.qV d :=
  (fun k => if h : i.1 < k then A.1 ⟨i.2.1 ⟨k,h⟩,Finset.mem_image.mpr ⟨⟨k,h⟩,by simp,rfl⟩⟩ else ⟨0,Φ.qU_pos⟩,
   fun k => if h : k < i.1 then A.2 ⟨i.2.2 ⟨k,h⟩,Finset.mem_image.mpr ⟨⟨k,h⟩,by simp,rfl⟩⟩ else ⟨0,Φ.qV_pos⟩)
def encode (i : Φ.Query d) (A : i.LocalLabel) : Profile Φ.qU Φ.qV d := encodeAssignment i A.val
end VertexCover.LabelCover.Query
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_DescriptorMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.LabelCover
abbrev TracePos (d : ℕ) := Bool × Fin d
abbrev TraceWeights (a b d : ℕ) := TracePos d → Fin ((max a b)^(d-1)) → Fin (2*d+1)
end VertexCover.LabelCover
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_FinalCNFBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine.FinalCNFMachine
open FormulaParser

def splitData : List (Bool × ℕ) → List ℕ → List (Triple (Bool × ℕ))
  | [a,b,c],[] => [((a,b),c)]
  | a::b::rest,y::ys => ((a,b),(true,y))::splitData ((false,y)::rest) ys
  | _,_ => []

end VertexCover.Machine.FinalCNFMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_LCData
attribute [-instance] _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                           
section

namespace VertexCover.Machine

structure FixedLC (a b : ℕ) where
  u : ℕ
  v : ℕ
  M : ℕ
  apos : 0<a
  bpos : 0<b
  Mpos : 0<M
  left : Fin M → Fin u
  right : Fin M → Fin v
  projection : Fin M → Fin a → Fin b

namespace FixedLC
variable {a b : ℕ}
def toLC (I : FixedLC a b) : LabelCover where
  u := I.u
  v := I.v
  qU := a
  qV := b
  M := I.M
  qU_pos := I.apos
  qV_pos := I.bpos
  M_pos := I.Mpos
  left := I.left
  right := I.right
  projection := I.projection

def one (ha : 0<a) (hb : 0<b) : FixedLC a b where
  u := 1
  v := 1
  M := 1
  apos := ha
  bpos := hb
  Mpos := by decide
  left := fun _ => 0
  right := fun _ => 0
  projection := fun _ _ => ⟨0,hb⟩

abbrev Map (a b : ℕ) := Fin a → Fin b
abbrev Row (a b : ℕ) := (ℕ × ℕ) × Map a b
abbrev Data (a b : ℕ) := ℕ × (ℕ × List (Row a b))
def data (I : FixedLC a b) : Data a b :=
  (I.u,(I.v,List.ofFn (fun e => ((I.left e |>.val,I.right e |>.val),I.projection e))))
def rowDefault (hb : 0<b) : Row a b := ((0,0),fun _ => ⟨0,hb⟩)
def lookup (hb : 0<b) (p : FixedLC a b × ℕ) : Row a b := p.1.data.2.2.getD p.2 (rowDefault hb)
 theorem lookup_valid (hb : 0<b) (I : FixedLC a b) (e : Fin I.M) :
    lookup hb (I,e.val) = ((I.left e |>.val,I.right e |>.val),I.projection e) := by
  simp only [lookup,data,List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp)]
  simp
end FixedLC
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_GraphFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                               
section

namespace VertexCover.Machine
 theorem foldl_and_all (xs : List Bool) (b : Bool) : xs.foldl (· && ·) b=(b && xs.all id) := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih => simp [ih,Bool.and_assoc]

namespace GraphMachine
open LabelCover
variable {a b d : ℕ}
abbrev Weight (a b d : ℕ) := Fin d → Fin ((max a b)^(d-1)) → Fin (2*d+1)
abbrev RawVertex (a b d : ℕ) := ℕ × Weight a b d
abbrev Frame (a b d : ℕ) := FixedLC a b × (RawVertex a b d × RawVertex a b d)
def defaultWeight : Weight a b d := fun _ _ => ⟨0,by omega⟩
def defaultFrame (ha : 0<a) (hb : 0<b) : Frame a b d :=
  (FixedLC.one ha hb,((0,defaultWeight),(0,defaultWeight)))
def vertexAt (p : Frame a b d) (x : Bool) : RawVertex a b d := if x then p.2.2 else p.2.1
def W (p : Frame a b d) : TraceWeights a b d := fun x => (vertexAt p x.1).2 x.2
end GraphMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_BatchesTripleSum
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Restriction
open scoped BigOperators

noncomputable def batches (d h : ℕ) : Finset (Finset (Fin d)) := by
  classical
  exact Finset.univ.powersetCard h

@[simp] theorem mem_batches {d h : ℕ} {J : Finset (Fin d)} :
    J ∈ batches d h ↔ J.card = h := by
  classical
  simp [batches]

@[simp] theorem card_batches (d h : ℕ) : (batches d h).card = d.choose h := by
  classical
  simp [batches]

theorem sum_if_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Finset ι) (g : ι → ℝ) : (∑ i : ι, if i ∈ J then g i else 0) = ∑ i ∈ J, g i := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

theorem batches_subset_count {d h : ℕ} (S : Finset (Fin d)) (hs : S.card ≤ h) (z : ℝ) :
    (∑ J ∈ batches d h, if S ⊆ J then z else 0) = (d-S.card).choose (h-S.card) * z := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hc : ((batches d h).filter (S ⊆ ·)).card = (d-S.card).choose (h-S.card) := by
    simpa only [batches, Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_powersetCard_subset S Finset.univ h (Finset.subset_univ _) hs
  exact_mod_cast hc

theorem batches_singleton_sum {d h : ℕ} (hh : 1 ≤ h) (g : Fin d → ℝ) :
    (∑ J ∈ batches d h, ∑ j ∈ J, g j) = ((d-1).choose (h-1) : ℝ) * ∑ j, g j := by
  classical
  have he : (∑ J ∈ batches d h, ∑ j ∈ J, g j) =
      ∑ J ∈ batches d h, ∑ j : Fin d, if j ∈ J then g j else 0 := by
    apply Finset.sum_congr rfl
    intro J _
    exact (sum_if_mem J g).symm
  rw [he, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Finset.singleton_subset_iff, Finset.card_singleton] using
    batches_subset_count ({j} : Finset (Fin d)) (by simpa using hh) (g j)

theorem batches_pair_sum_le {d h : ℕ} (hh : 2 ≤ h) (g : Fin d → Fin d → ℝ)
    (hg : ∀ j k, 0 ≤ g j k) :
    (∑ J ∈ batches d h, ∑ j ∈ J, ∑ k ∈ J.erase j, g j k) ≤
      ((d-2).choose (h-2) : ℝ) * ∑ j, ∑ k, g j k := by
  classical
  have he : (∑ J ∈ batches d h, ∑ j ∈ J, ∑ k ∈ J.erase j, g j k) =
      ∑ J ∈ batches d h, ∑ j : Fin d, ∑ k : Fin d,
        if j ∈ J ∧ k ∈ J.erase j then g j k else 0 := by
    apply Finset.sum_congr rfl
    intro J _
    rw [← sum_if_mem J (fun j => ∑ k ∈ J.erase j, g j k)]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ J
    · simpa only [hj, ite_true, true_and] using (sum_if_mem (J.erase j) (g j)).symm
    · simp only [hj, ite_false, false_and, Finset.sum_const_zero]
  rw [he, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k = j
  · subst k
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, and_false, ite_false, Finset.sum_const_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (hg j j)
  · have hc : ({j,k} : Finset (Fin d)).card = 2 := by simp [Ne.symm hk]
    have hc' := batches_subset_count ({j,k} : Finset (Fin d)) (by omega : _ ≤ h) (g j k)
    simpa only [hc, Finset.insert_subset_iff, Finset.singleton_subset_iff,
      Finset.mem_erase, hk, ne_eq, not_false_eq_true, true_and] using hc'.le

theorem batches_triple_sum_le {d h : ℕ} {E : Type*} [Fintype E]
    (hh : 3 ≤ h) (a b : E → Fin d) (hab : ∀ e, a e ≠ b e)
    (g : Fin d → E → ℝ) (hg : ∀ j e, 0 ≤ g j e) :
    (∑ J ∈ batches d h, ∑ j ∈ J,
      ∑ e ∈ Finset.univ.filter (fun e => a e ∈ J ∧ b e ∈ J ∧ ¬ (a e = j ∨ b e = j)),
        g j e) ≤ ((d-3).choose (h-3) : ℝ) * ∑ j, ∑ e, g j e := by
  classical
  have he : (∑ J ∈ batches d h, ∑ j ∈ J,
      ∑ e ∈ Finset.univ.filter (fun e => a e ∈ J ∧ b e ∈ J ∧ ¬ (a e = j ∨ b e = j)),
        g j e) = ∑ J ∈ batches d h, ∑ j : Fin d, ∑ e : E,
      if j ∈ J ∧ a e ∈ J ∧ b e ∈ J ∧ ¬ (a e = j ∨ b e = j) then g j e else 0 := by
    apply Finset.sum_congr rfl
    intro J _
    rw [← sum_if_mem J (fun j => ∑ e ∈ Finset.univ.filter
      (fun e => a e ∈ J ∧ b e ∈ J ∧ ¬ (a e = j ∨ b e = j)), g j e)]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ J
    · simp only [hj, ite_true, true_and, Finset.sum_filter]
    · simp only [hj, ite_false, false_and, Finset.sum_const_zero]
  rw [he, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  by_cases hje : a e = j ∨ b e = j
  · simp only [hje, not_true_eq_false, and_false, ite_false, Finset.sum_const_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (hg j e)
  · obtain ⟨ha, hb⟩ := not_or.mp hje
    have hc : ({j, a e, b e} : Finset (Fin d)).card = 3 := by
      simp [Ne.symm ha, Ne.symm hb, hab e]
    have hc' := batches_subset_count ({j,a e,b e} : Finset (Fin d))
      (by omega : _ ≤ h) (g j e)
    simpa only [hc, Finset.insert_subset_iff, Finset.singleton_subset_iff,
      hje, not_false_eq_true, and_true] using hc'.le

end VertexCover.Restriction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_CoordinateProductInvariant
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Restriction.EnergyForm.Projection
open scoped BigOperators
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {I C T : Type*} [DecidableEq I]

def coordinateKey (c0 : C) (i : I) (q : C → T) (s : I → C) :=
  (Function.update s i c0, q (s i))

@[simp] theorem coordinateKey_update (c0 : C) (i : I) (q : C → T)
    (s : I → C) (c : C) :
    coordinateKey c0 i q (Function.update s i c) = (Function.update s i c0, q c) := by
  simp [coordinateKey]

theorem coordinateKey_eq_iff (c0 : C) (i : I) (q : C → T) (s t : I → C) :
    coordinateKey c0 i q s = coordinateKey c0 i q t ↔
      (∀ j, j ≠ i → s j = t j) ∧ q (s i) = q (t i) := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, congrArg Prod.snd h⟩
    have he := congrFun (congrArg Prod.fst h) j
    simpa only [coordinateKey, Function.update_of_ne hj] using he
  · rintro ⟨h, hq⟩
    apply Prod.ext _ hq
    change Function.update s i c0 = Function.update t i c0
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp only [Function.update_of_ne hj, h j hj]

variable [Fintype I] [Fintype C]

open Classical in
theorem coordinateKey_fiber (c0 : C) (i : I) (q : C → T) (s : I → C) :
    (Finset.univ.filter (fun t => coordinateKey c0 i q t = coordinateKey c0 i q s)) =
      (Finset.univ.filter (fun c => q c = q (s i))).image (Function.update s i) := by
  classical
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro ht
    obtain ⟨ho, hq⟩ := (coordinateKey_eq_iff c0 i q t s).mp ht
    refine ⟨t i, hq, ?_⟩
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp only [Function.update_of_ne hj, ho j hj]
  · rintro ⟨c, hc, rfl⟩
    rw [coordinateKey_update]
    exact Prod.ext rfl hc

omit [AddCommGroup E] [Module ℝ E] [Fintype C] in

theorem invariant_of_coordinate_invariant (q : I → C → T) (f : (I → C) → E)
    (hf : ∀ i s c, q i c = q i (s i) → f (Function.update s i c) = f s)
    (s t : I → C) (hst : ∀ i, q i (s i) = q i (t i)) : f s = f t := by
  classical
  let mix (A : Finset I) : I → C := fun i => if i ∈ A then t i else s i
  have hm : ∀ A : Finset I, f (mix A) = f s := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp [mix]
    | @insert i A hi ih =>
      have hu : mix (insert i A) = Function.update (mix A) i (t i) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [mix]
        · simp [mix, hj]
      rw [hu, hf i (mix A) (t i) (by simpa [mix, hi] using (hst i).symm)]
      exact ih
  have hall := hm Finset.univ
  simpa [mix] using hall.symm

end VertexCover.Restriction.EnergyForm.Projection


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_AverageCommute
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Restriction
open MeasureTheory
open scoped BigOperators

namespace EnergyForm

section Integral
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem continuous_mul_integrable (f g : C(X, ℝ)) :
    Integrable (fun x => f x * g x) μ :=
  (f.continuous.mul g.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end Integral

namespace Projection
section Averaging
variable {ι X : Type*} [Fintype ι] [DecidableEq ι]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

noncomputable def updateFunction (i : ι) (f : C(ι → X, ℝ)) : C(X, C(ι → X, ℝ)) :=
  ContinuousMap.curry ⟨fun p : X × (ι → X) => f (Function.update p.2 i p.1),
    f.continuous.comp (continuous_snd.update i continuous_fst)⟩

end Averaging
end Projection
end EnergyForm
end VertexCover.Restriction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_IntegralCoe
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Restriction
open MeasureTheory
open scoped BigOperators

def plug {ι X : Type*} [DecidableEq ι] (J : Finset ι) (s t : ι → X) : ι → X :=
  fun i => if i ∈ J then t i else s i

@[simp] theorem plug_empty {ι X : Type*} [DecidableEq ι] (s t : ι → X) :
    plug ∅ s t = s := by funext i; simp [plug]

@[simp] theorem plug_univ {ι X : Type*} [Fintype ι] [DecidableEq ι] (s t : ι → X) :
    plug Finset.univ s t = t := by funext i; simp [plug]

theorem plug_insert_update {ι X : Type*} [DecidableEq ι] (J : Finset ι) (i : ι)
    (hi : i ∉ J) (s t : ι → X) (x : X) :
    plug J (Function.update s i x) t = plug (insert i J) s (Function.update t i x) := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [plug, hi]
  · simp [plug, hk]

theorem restrict_preserving {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (J : Finset ι) :
    MeasurePreserving (fun s : ι → X => fun i : J => s i)
      (Measure.pi (fun _ : ι => μ)) (Measure.pi (fun _ : J => μ)) := by
  classical
  have hp : MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) (fun i => i ∈ J))
      (Measure.pi (fun _ : ι => μ))
      ((Measure.pi (fun _ : J => μ)).prod (Measure.pi (fun _ : {i : ι // i ∉ J} => μ))) := by
    convert measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun i => i ∈ J) using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    exact Subsingleton.elim _ _
  exact (measurePreserving_fst (μ := Measure.pi (fun _ : J => μ))
    (ν := Measure.pi (fun _ : {i : ι // i ∉ J} => μ))).comp hp

theorem integral_restrict {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (J : Finset ι)
    {g : (J → X) → ℝ} (hg : AEStronglyMeasurable g (Measure.pi (fun _ : J => μ))) :
    (∫ s, g (fun i : J => s i) ∂Measure.pi (fun _ : ι => μ)) =
      ∫ t, g t ∂Measure.pi (fun _ : J => μ) := by
  have hp := restrict_preserving μ J
  rw [← hp.map_eq] at hg ⊢
  exact (integral_map hp.measurable.aemeasurable hg).symm

def splice {ι X : Type*} [DecidableEq ι] (J : Finset ι) (s : ι → X) (t : J → X) : ι → X :=
  fun i => if h : i ∈ J then t ⟨i,h⟩ else s i

theorem plug_erase_eq_splice_update {ι X : Type*} [DecidableEq ι]
    (J : Finset ι) (j : J) (s t : ι → X) :
    plug (J.erase j) s t = splice J s (Function.update (fun i : J => t i) j (s j)) := by
  funext i
  by_cases hi : i ∈ J
  · by_cases hij : i = j
    · subst i
      simp [plug, splice]
    · have hij' : (⟨i,hi⟩ : J) ≠ j := fun h => hij (congrArg Subtype.val h)
      simp [plug, splice, hi, hij, hij']
  · simp [plug, splice, hi]

namespace CompactCube

abbrev Interval := Set.Icc (-1 : ℝ) 1

noncomputable def intervalLaw : Measure Interval :=
  VertexCover.Cube.intervalLaw.comap Subtype.val

theorem ae_interval_mem : ∀ᵐ x ∂VertexCover.Cube.intervalLaw, x ∈ Set.Icc (-1 : ℝ) 1 := by
  filter_upwards [VertexCover.Cube.ae_interval] with x hx
  exact (abs_le.mp hx)

instance instIsProbabilityMeasureElemRealIntervalIntervalLaw : IsProbabilityMeasure intervalLaw :=
  (MeasurableEmbedding.subtype_coe measurableSet_Icc).isProbabilityMeasure_comap
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using ae_interval_mem)

theorem interval_preserving : MeasurePreserving (Subtype.val : Interval → ℝ)
    intervalLaw VertexCover.Cube.intervalLaw := by
  refine ⟨measurable_subtype_coe, ?_⟩
  rw [intervalLaw, (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_comap]
  simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using
    Measure.restrict_eq_self_of_ae_mem ae_interval_mem

noncomputable def law (ι : Type*) [Fintype ι] : Measure (ι → Interval) :=
  Measure.pi (fun _ : ι => intervalLaw)

instance instIsProbabilityMeasureForallElemRealIntervalLaw {ι : Type*} [Fintype ι] : IsProbabilityMeasure (law ι) := by
  unfold law
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

def realWeights {ι κ : Type*} (s : ι → κ → Interval) : ι → κ → ℝ :=
  fun i k => (s i k).1

theorem continuous_realWeights {ι κ : Type*} :
    Continuous (realWeights (ι := ι) (κ := κ)) :=
  continuous_pi (fun i => continuous_pi (fun k =>
    continuous_subtype_val.comp ((continuous_apply k).comp (continuous_apply i))))

theorem law_preserving {ι : Type*} [Fintype ι] :
    MeasurePreserving (fun s : ι → Interval => fun i => (s i).1)
      (law ι) (VertexCover.Cube.law ι) :=
  measurePreserving_pi _ _ (fun _ => interval_preserving)

noncomputable def blockLaw (ι κ : Type*) [Fintype ι] [Fintype κ] :
    Measure (ι → κ → Interval) := Measure.pi (fun _ : ι => law κ)

instance instIsProbabilityMeasureForallForallElemRealIntervalBlockLaw {ι κ : Type*} [Fintype ι] [Fintype κ] : IsProbabilityMeasure (blockLaw ι κ) := by
  unfold blockLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

theorem blockLaw_preserving {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurePreserving (realWeights (ι := ι) (κ := κ))
      (blockLaw ι κ) (VertexCover.Cube.blockLaw ι κ) :=
  measurePreserving_pi _ _ (fun _ => law_preserving)

theorem integral_realWeights {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : (ι → κ → ℝ) → ℝ} (hf : AEStronglyMeasurable f (VertexCover.Cube.blockLaw ι κ)) :
    (∫ s, f (realWeights s) ∂blockLaw ι κ) =
      ∫ s, f s ∂VertexCover.Cube.blockLaw ι κ := by
  have hp := blockLaw_preserving (ι := ι) (κ := κ)
  rw [← hp.map_eq] at hf ⊢
  exact (integral_map hp.measurable.aemeasurable hf).symm

theorem integral_coe {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} (hf : AEStronglyMeasurable f (VertexCover.Cube.law ι)) :
    (∫ s, f (fun i => (s i).1) ∂law ι) = ∫ s, f s ∂VertexCover.Cube.law ι := by
  have hp := law_preserving (ι := ι)
  rw [← hp.map_eq] at hf ⊢
  exact (integral_map hp.measurable.aemeasurable hf).symm

end CompactCube
end VertexCover.Restriction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_RestrictionStarBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

namespace VertexCover.Restriction.CompactCube

theorem realWeights_update {ι κ : Type*} [DecidableEq ι]
    (s : ι → κ → Interval) (j : ι) (x : κ → Interval) :
    realWeights (Function.update s j x) =
      Function.update (realWeights s) j (fun k => (x k).1) := by
  funext i k
  by_cases hi : i = j
  · subst i
    simp [realWeights]
  · simp [realWeights, Function.update_of_ne hi]

end VertexCover.Restriction.CompactCube


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_PrivateProjectionBatchLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Restriction

theorem choose_step (d h : ℕ) (hd : 0 < d) (hh : 0 < h) :
    (d:ℝ)*((d-1).choose (h-1):ℝ) = (h:ℝ)*(d.choose h:ℝ) := by
  have he := Nat.add_one_mul_choose_eq (d-1) (h-1)
  rw [Nat.sub_add_cancel hd, Nat.sub_add_cancel hh] at he
  exact_mod_cast he.trans (Nat.mul_comm _ _)

theorem batch_pair_scale (d h : ℕ) (hd : 4 ≤ d) (hh : 3 ≤ h) :
    (d:ℝ)*((d-2).choose (h-2):ℝ) ≤ 2*(h:ℝ)*((d-1).choose (h-1):ℝ) := by
  have he := choose_step (d-1) (h-1) (by omega) (by omega)
  have hed : d-1-1 = d-2 := by omega
  have heh : h-1-1 = h-2 := by omega
  rw [hed, heh, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_sub (by omega : 1 ≤ h)] at he
  norm_num only [Nat.cast_one] at he
  have hdR : (4:ℝ) ≤ d := by exact_mod_cast hd
  have hC1 : (0:ℝ) ≤ (d-1).choose (h-1) := Nat.cast_nonneg _
  have hC2 : (0:ℝ) ≤ (d-2).choose (h-2) := Nat.cast_nonneg _
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d-2) hC2]

theorem batch_triple_scale (d h : ℕ) (hd : 4 ≤ d) (hh : 3 ≤ h) :
    (d:ℝ)^2*((d-3).choose (h-3):ℝ) ≤ 4*(h:ℝ)^2*((d-1).choose (h-1):ℝ) := by
  have he := choose_step (d-2) (h-2) (by omega) (by omega)
  have hed : d-2-1 = d-3 := by omega
  have heh : h-2-1 = h-3 := by omega
  rw [hed, heh, Nat.cast_sub (by omega : 2 ≤ d), Nat.cast_sub (by omega : 2 ≤ h)] at he
  norm_num only [Nat.cast_ofNat] at he
  have hdR : (4:ℝ) ≤ d := by exact_mod_cast hd
  have hhR : (0:ℝ) ≤ h := Nat.cast_nonneg _
  have hC2 : (0:ℝ) ≤ (d-2).choose (h-2) := Nat.cast_nonneg _
  have hC3 : (0:ℝ) ≤ (d-3).choose (h-3) := Nat.cast_nonneg _
  have hl : (d:ℝ)*((d-3).choose (h-3):ℝ) ≤ 2*(h:ℝ)*((d-2).choose (h-2):ℝ) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d-4) hC3]
  have hl' := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg d : (0:ℝ) ≤ d)
  have hp := mul_le_mul_of_nonneg_left (batch_pair_scale d h hd hh) (by positivity : (0:ℝ) ≤ 2*h)
  nlinarith

end VertexCover.Restriction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_PrivateTotalEnergyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Restriction
open scoped BigOperators

def spliceSwap {ι X : Type*} [DecidableEq ι] (J : Finset ι) :
    ((ι → X) × (J → X)) ≃ ((ι → X) × (J → X)) where
  toFun p := (splice J p.1 p.2, fun i => p.1 i)
  invFun p := (splice J p.1 p.2, fun i => p.1 i)
  left_inv p := by
    apply Prod.ext
    · funext i
      by_cases hi : i ∈ J <;> simp [splice, hi]
    · funext i
      simp [splice, i.2]
  right_inv p := by
    apply Prod.ext
    · funext i
      by_cases hi : i ∈ J <;> simp [splice, hi]
    · funext i
      simp [splice, i.2]

end VertexCover.Restriction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_GraphSoundness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Parameters

theorem h_ge_three (m : ℕ) (hm : 0 < m) : 3 ≤ h m := by
  have hpow : 1 ≤ m^3 := one_le_pow₀ hm
  unfold h
  norm_num only [Nat.reducePow]
  omega

theorem private_variance_threshold (m : ℕ) (hm : 0 < m) : ν m*(h m:ℝ)/4 = 8 := by
  have hn : (m:ℝ) ≠ 0 := by positivity
  simp only [ν, h, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  norm_num

end VertexCover.Parameters


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_GraphSoundness2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.ExplicitGraph

theorem coverNumber_witness (G : ExplicitGraph) :
    ∃ S : Finset (Fin G.n), G.Cover S ∧ S.card = G.coverNumber := by
  have hex : ∃ k : ℕ, ∃ S : Finset (Fin G.n), G.Cover S ∧ S.card = k :=
    ⟨G.n, Finset.univ, by simp [Cover], by simp⟩
  exact Nat.find_spec hex

end VertexCover.ExplicitGraph

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_NumberedGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                  
section

namespace VertexCover.ExplicitGraph
noncomputable section

def numbered {n : ℕ} (G : SimpleGraph (Fin n)) : ExplicitGraph := by
  classical
  let E := (List.ofFn fun e : Fin (n*n) => finProdFinEquiv.symm e).filter
    (fun p => decide (p.1<p.2 ∧ G.Adj p.1 p.2))
  refine ⟨n,E,?_,?_⟩
  · intro p hp
    exact (of_decide_eq_true (List.mem_filter.mp hp).2).1
  · exact (List.nodup_ofFn.mpr finProdFinEquiv.symm.injective).filter _
@[simp] theorem numbered_n {n : ℕ} (G : SimpleGraph (Fin n)) : (numbered G).n=n := rfl
 theorem numbered_mem_edges {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    (u,v) ∈ (numbered G).edges ↔ u<v ∧ G.Adj u v := by
  classical
  change (u,v) ∈ ((List.ofFn fun e : Fin (n*n) => finProdFinEquiv.symm e).filter
    (fun p => decide (p.1<p.2 ∧ G.Adj p.1 p.2))) ↔ _
  simp only [List.mem_filter,List.mem_ofFn,decide_eq_true_iff]
  exact and_iff_right ⟨finProdFinEquiv (u,v),finProdFinEquiv.symm_apply_apply (u,v)⟩
 theorem numbered_cover_iff {n : ℕ} (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) :
    (numbered G).Cover C ↔ G.IsVertexCover (C : Set (Fin n)) := by
  constructor
  · intro h u v huv
    rcases lt_trichotomy u v with hl | he | hg
    · exact h (u,v) ((numbered_mem_edges G u v).mpr ⟨hl,huv⟩)
    · exact (huv.ne he).elim
    · exact (h (v,u) ((numbered_mem_edges G v u).mpr ⟨hg,huv.symm⟩)).symm
  · intro h p hp
    exact h ((numbered_mem_edges G p.1 p.2).mp hp).2
 theorem numbered_sound {V : Type} [Fintype V] {n : ℕ} (G : SimpleGraph V)
    (E : Fin n ≃ V) (ρ : ℝ) (hb : ∀ C : Finset V, G.IsVertexCover (C : Set V) →
      ρ*Fintype.card V < (C.card:ℝ)) :
    ρ*(numbered (G.comap E)).n < ((numbered (G.comap E)).coverNumber:ℝ) := by
  classical
  obtain ⟨S,hS,hs⟩ := coverNumber_witness (numbered (G.comap E))
  let C := S.map E.toEmbedding
  have hc : G.IsVertexCover (C : Set V) := by
    intro u v huv
    have h := (numbered_cover_iff (G.comap E) S).mp hS
      (by simpa only [SimpleGraph.comap_adj,Equiv.apply_symm_apply] using huv :
        (G.comap E).Adj (E.symm u) (E.symm v))
    exact h.imp
      (fun hu => Finset.mem_map.mpr ⟨E.symm u,hu,E.apply_symm_apply u⟩)
      (fun hv => Finset.mem_map.mpr ⟨E.symm v,hv,E.apply_symm_apply v⟩)
  have hn : n=Fintype.card V := by simpa using Fintype.card_congr E
  have hcard : C.card=S.card := Finset.card_map _
  have h := hb C hc
  rw [hcard,hs] at h
  simpa only [numbered_n,hn] using h
end
end VertexCover.ExplicitGraph
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_GraphNumber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                
section

namespace VertexCover.Machine.GraphMachine
open LabelCover
noncomputable section
variable {a b d : ℕ}
def weightCount (a b d : ℕ) : ℕ := Fintype.card (Weight a b d)
theorem weightCount_pos : 0<weightCount a b d :=
  Fintype.card_pos_iff.mpr ⟨defaultWeight⟩
def decode (n : ℕ) : RawVertex a b d :=
  (n / weightCount a b d, (Fintype.equivFin (Weight a b d)).symm ⟨n % weightCount a b d,Nat.mod_lt _ weightCount_pos⟩)

def numberFrame (p : FixedLC a b × (ℕ × ℕ)) : Frame a b d :=
  (p.1,(decode p.2.1,decode p.2.2))
end
end VertexCover.Machine.GraphMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_InitialTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine
open FormulaParser

namespace InitialTable

abbrev ClauseData := Triple (Bool × ℕ)
abbrev Signs := Triple Bool
def clauseDefault : ClauseData := (((false,0),(false,0)),(false,0))
def signs (cs : ClauseData) : Signs := ((cs.1.1.1,cs.1.2.1),cs.2.1)
def lit (cs : ClauseData) (slot : Fin 3) : Bool × ℕ :=
  if slot=0 then cs.1.1 else if slot=1 then cs.1.2 else cs.2

end InitialTable
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_LCNumber
attribute [-instance] _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
attribute [-simp] _root_.OAI.VertexCover.LabelCover.Query.labels_length _root_.OAI.VertexCover.LabelCover.Query.mem_labels _root_.OAI.VertexCover.LabelCover.Query.mem_thresholdList _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.increment_same _root_.OAI.VertexCover.LabelCover.mem_compatibleSelections _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.selectionForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                             
section

namespace VertexCover.LabelCover

structure Iso (Φ Ψ : LabelCover) where
  u : Fin Φ.u ≃ Fin Ψ.u
  v : Fin Φ.v ≃ Fin Ψ.v
  a : Fin Φ.qU ≃ Fin Ψ.qU
  b : Fin Φ.qV ≃ Fin Ψ.qV
  e : Fin Φ.M ≃ Fin Ψ.M
  left : ∀ c, Ψ.left (e c) = u (Φ.left c)
  right : ∀ c, Ψ.right (e c) = v (Φ.right c)
  projection : ∀ c s, Ψ.projection (e c) (a s) = b (Φ.projection c s)

namespace Iso
variable {Φ Ψ : LabelCover} (E : Iso Φ Ψ)
def labeling (A : Φ.Labeling) : Ψ.Labeling :=
  (fun x => E.a (A.1 (E.u.symm x)),fun y => E.b (A.2 (E.v.symm y)))
 theorem satisfies (A : Φ.Labeling) (c : Fin Φ.M) :
    Ψ.Satisfies (E.labeling A) (E.e c) ↔ Φ.Satisfies A c := by
  simp only [Satisfies,labeling,E.left,E.right,Equiv.symm_apply_apply,E.projection,Equiv.apply_eq_iff_eq]
 theorem count (A : Φ.Labeling) : Ψ.satisfiedCount (E.labeling A) = Φ.satisfiedCount A := by
  classical
  have h := Fintype.card_congr (E.e.subtypeEquiv (fun c => (E.satisfies A c).symm))
  simpa only [Fintype.card_subtype,satisfiedCount] using h.symm
 include E
 theorem value_le : Φ.value ≤ Ψ.value := by
  have hM : Φ.M = Ψ.M := by simpa using Fintype.card_congr E.e
  apply value_le_of_counts
  intro A
  rw [← E.count A,hM]
  exact Ψ.count_le_of_value_le le_rfl (E.labeling A)
 def symm : Iso Ψ Φ where
  u := E.u.symm
  v := E.v.symm
  a := E.a.symm
  b := E.b.symm
  e := E.e.symm
  left c := by
    apply E.u.injective
    simpa only [Equiv.apply_symm_apply] using (E.left (E.e.symm c)).symm
  right c := by
    apply E.v.injective
    simpa only [Equiv.apply_symm_apply] using (E.right (E.e.symm c)).symm
  projection c s := by
    apply E.b.injective
    simpa only [Equiv.apply_symm_apply] using (E.projection (E.e.symm c) (E.a.symm s)).symm
 theorem value_eq : Φ.value = Ψ.value := le_antisymm E.value_le E.symm.value_le
 theorem perfect (A : Φ.Labeling) (hA : ∀ c, Φ.Satisfies A c) :
    ∀ c, Ψ.Satisfies (E.labeling A) c := by
  intro c
  rw [← E.e.apply_symm_apply c]
  exact (E.satisfies A _).mpr (hA _)
end Iso

def numberedPower (Φ : LabelCover) (n : ℕ) : LabelCover where
  u := Φ.u^n
  v := Φ.v^n
  qU := Φ.qU^n
  qV := Φ.qV^n
  M := Φ.M^n
  qU_pos := pow_pos Φ.qU_pos _
  qV_pos := pow_pos Φ.qV_pos _
  M_pos := pow_pos Φ.M_pos _
  left c := finFunctionFinEquiv (fun i => Φ.left (finFunctionFinEquiv.symm c i))
  right c := finFunctionFinEquiv (fun i => Φ.right (finFunctionFinEquiv.symm c i))
  projection c s := finFunctionFinEquiv
    (fun i => Φ.projection (finFunctionFinEquiv.symm c i) (finFunctionFinEquiv.symm s i))
noncomputable def numberIso (Φ : LabelCover) (n : ℕ) : Iso (Φ.numberedPower n) (Φ.parallelPower n) where
  u := finFunctionFinEquiv.symm.trans (tupleEquiv Φ.u n)
  v := finFunctionFinEquiv.symm.trans (tupleEquiv Φ.v n)
  a := finFunctionFinEquiv.symm.trans (tupleEquiv Φ.qU n)
  b := finFunctionFinEquiv.symm.trans (tupleEquiv Φ.qV n)
  e := finFunctionFinEquiv.symm.trans (tupleEquiv Φ.M n)
  left c := by
    change (tupleEquiv Φ.u n) (fun i => Φ.left ((tupleEquiv Φ.M n).symm
      ((tupleEquiv Φ.M n) (finFunctionFinEquiv.symm c)) i)) =
      (tupleEquiv Φ.u n) (finFunctionFinEquiv.symm (finFunctionFinEquiv
        (fun i => Φ.left (finFunctionFinEquiv.symm c i))))
    simp only [Equiv.symm_apply_apply]
  right c := by
    change (tupleEquiv Φ.v n) (fun i => Φ.right ((tupleEquiv Φ.M n).symm
      ((tupleEquiv Φ.M n) (finFunctionFinEquiv.symm c)) i)) =
      (tupleEquiv Φ.v n) (finFunctionFinEquiv.symm (finFunctionFinEquiv
        (fun i => Φ.right (finFunctionFinEquiv.symm c i))))
    simp only [Equiv.symm_apply_apply]
  projection c s := by
    change (tupleEquiv Φ.qV n) (fun i => Φ.projection
      ((tupleEquiv Φ.M n).symm ((tupleEquiv Φ.M n) (finFunctionFinEquiv.symm c)) i)
      ((tupleEquiv Φ.qU n).symm ((tupleEquiv Φ.qU n) (finFunctionFinEquiv.symm s)) i)) =
      (tupleEquiv Φ.qV n) (finFunctionFinEquiv.symm (finFunctionFinEquiv
        (fun i => Φ.projection (finFunctionFinEquiv.symm c i) (finFunctionFinEquiv.symm s i))))
    simp only [Equiv.symm_apply_apply]
end VertexCover.LabelCover
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_NatLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                           
section

namespace VertexCover.Machine
namespace Logarithm
abbrev State := ℕ × ℕ

def body (p : State) : Bool × State :=
  if 2 ≤ p.1 then (true,(p.1/2,p.2+1)) else (false,p)
def result (p : State) : State := (min p.1 1,p.2+p.1.log2)
end Logarithm
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_PowerLC
attribute [-instance] _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine.FixedLC

variable {a b : ℕ}
def power (n : ℕ) (I : FixedLC a b) : FixedLC (a^n) (b^n) where
  u := I.u^n
  v := I.v^n
  M := I.M^n
  apos := pow_pos I.apos _
  bpos := pow_pos I.bpos _
  Mpos := pow_pos I.Mpos _
  left := (I.toLC.numberedPower n).left
  right := (I.toLC.numberedPower n).right
  projection := (I.toLC.numberedPower n).projection

def powerMap (n : ℕ) (maps : Fin n → Map a b) : Map (a^n) (b^n) :=
  fun s => finFunctionFinEquiv (fun i => maps i (finFunctionFinEquiv.symm s i))
def powerRow (hb : 0<b) (n : ℕ) (p : FixedLC a b × ℕ) : Row (a^n) (b^n) :=
  let row := fun i : Fin n => lookup hb (p.1,p.2/p.1.M^i.val%p.1.M)
  ((∑ i, (row i).1.1*p.1.u^i.val,∑ i, (row i).1.2*p.1.v^i.val),
      powerMap n (fun i => (row i).2))

 theorem powerRow_correct (hb : 0<b) (n : ℕ) (I : FixedLC a b) (e : Fin (I.power n).M) :
    powerRow hb n (I,e.val)=(((I.power n).left e |>.val,(I.power n).right e |>.val),
      (I.power n).projection e) := by
  have he (i : Fin n) :
      lookup hb (I,e.val/I.M^i.val%I.M) =
        (((I.left (finFunctionFinEquiv.symm e i)).val,
          (I.right (finFunctionFinEquiv.symm e i)).val),I.projection (finFunctionFinEquiv.symm e i)) :=
    lookup_valid hb I (finFunctionFinEquiv.symm e i)
  simp only [powerRow,he]
  rfl
end VertexCover.Machine.FixedLC
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_PowerRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                    
section

namespace VertexCover.Machine.PowerRowMachine

abbrev Block (d n : ℕ) := Fin (2*d^(n+1))

end VertexCover.Machine.PowerRowMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_SimpleLC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                    
section

namespace VertexCover.Machine.SimpleLC
open FormulaParser InitialTable ClauseProjection

abbrev Signature := (Fin 3 → Bool) × (Fin 3 × Fin 3 → Bool)
def signature (cs : ClauseData) : Signature :=
  (fun k => (lit cs k).1,fun kl => decide ((lit cs kl.1).2=(lit cs kl.2).2))
noncomputable def relation (s : Signature) (k : Fin 3) : FixedLC.Map 7 2 := fun label =>
  let P := patternEquiv.symm label
  let good := ∀ k l, s.2 (k,l)=true → flipSign (s.1 k) (P.val k)=flipSign (s.1 l) (P.val l)
  let norm := if good then P.val else fun j => flipSign (s.1 j) (if s.2 (j,0) then s.1 0 else false)
  finTwoEquiv.symm (flipSign (s.1 k) (norm k))

noncomputable def row (p : FormulaData × ℕ) : FixedLC.Row 7 2 :=
  let cs := p.1.2.getD (p.2/3) clauseDefault
  let k : Fin 3 := ⟨p.2%3,Nat.mod_lt _ (by decide)⟩
  ((p.2/3,(lit cs k).2),relation (signature cs) k)

end VertexCover.Machine.SimpleLC
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_TableCodeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine
namespace TableMachine
noncomputable def lengthPolynomial : Polynomial ℕ := 10000*(Polynomial.X+1)^2
end TableMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end


