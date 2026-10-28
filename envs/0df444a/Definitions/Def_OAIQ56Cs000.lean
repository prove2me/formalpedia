-- Prove2me | Definitions.Def_OAIQ56Cs000
-- name    : OAIQ56Cs000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T18:32:00.580995+00:00
-- url     : https://prove2.me/theorems/83b4b0cb-35c1-4581-9f1d-df28650822d3
-- title:
--   Definitions bundle OAIQ56Cs000 of the split of OpenAI, Conditional information under deterministic coordinate sweeps
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoordinateSweeps.all_grid_moment` and `OAI.CoordinateSweeps.conditional_main`, carved from OpenAI's openai/math development (OpenAI, *Conditional information under deterministic coordinate sweeps*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 668 declarations of OpenAI's Lean: 429 definitions, 3 inductive types or structures, 21 instances and 215 theorems. The definitions and types are `OAI.CoordinateSweeps.BlockCycles.block`, `OAI.CoordinateSweeps.BlockCycles.blocks`, `OAI.CoordinateSweeps.BlockCycles.edgeFiber`, `OAI.CoordinateSweeps.BlockCycles.edgeWeight`, `OAI.CoordinateSweeps.BlockCycles.evenWord`, `OAI.CoordinateSweeps.BlockCycles.tupleSplit`, `OAI.CoordinateSweeps.BlockCycles.walk`, `OAI.CoordinateSweeps.CharacterCount.pairing`, `OAI.CoordinateSweeps.CommutingRestriction.homAction`, `OAI.CoordinateSweeps.CommutingRestriction.inclusion`, `OAI.CoordinateSweeps.Coverage.Witness`, `OAI.CoordinateSweeps.Coverage.covered`, `OAI.CoordinateSweeps.Coverage.cutEdges`, `OAI.CoordinateSweeps.Coverage.encodeSmallSet`, `OAI.CoordinateSweeps.Coverage.glue`, `OAI.CoordinateSweeps.Coverage.heavySet`, `OAI.CoordinateSweeps.Coverage.occupancy`, `OAI.CoordinateSweeps.Coverage.probability`, `OAI.CoordinateSweeps.Coverage.productMass`, `OAI.CoordinateSweeps.Coverage.rootPredicate`, `OAI.CoordinateSweeps.Coverage.sharingCoverage`, `OAI.CoordinateSweeps.Coverage.starEvent`, `OAI.CoordinateSweeps.Coverage.starSystem`, `OAI.CoordinateSweeps.DependentTensor.tensor`, `OAI.CoordinateSweeps.FiberBlocks.action`, `OAI.CoordinateSweeps.FiberBlocks.cards`, `OAI.CoordinateSweeps.FiberBlocks.chart`, `OAI.CoordinateSweeps.FiberBlocks.regroup`, `OAI.CoordinateSweeps.FiberBlocks.restrict`, `OAI.CoordinateSweeps.FiberBlocks.size`, `OAI.CoordinateSweeps.FiberBlocks.slots`, `OAI.CoordinateSweeps.FiniteLaw.assignments`, `OAI.CoordinateSweeps.FiniteLaw.independent`, `OAI.CoordinateSweeps.FiniteLaw.mix`, `OAI.CoordinateSweeps.Grid.BoundedCode`, `OAI.CoordinateSweeps.Grid.BoundedCode.grid`, `OAI.CoordinateSweeps.Grid.Holes.ColumnCard`, `OAI.CoordinateSweeps.Grid.Holes.ColumnChoices`, `OAI.CoordinateSweeps.Grid.Holes.ColumnLocalChoices`, `OAI.CoordinateSweeps.Grid.Holes.EndpointPossible` and 392 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `CoordinateSweeps_Attachment`, `CoordinateSweeps_BaseCase`, `CoordinateSweeps_Conditioning`, `CoordinateSweeps_Decomposition`, `CoordinateSweeps_Grid`, `CoordinateSweeps_Induction`, `CoordinateSweeps_Kernel`, `CoordinateSweeps_Main`, `CoordinateSweeps_Perturbation`, `CoordinateSweeps_PlacementMoment`, `CoordinateSweeps_SparseBound`, `CoordinateSweeps_SparseDimension`, `CoordinateSweeps_SparseMoment`, `CoordinateSweeps_TrajectoryMoment`, `CoordinateSweeps_Transition`, `Graphs_Coverage`, `Matrix_BlockCycles`, `Matrix_Holder`, `Matrix_TensorMoment`, `Moments_LineExpansion`, `Placement_Chart`, `Placement_Occurrence`, `SignedTensor_Basic`, `SignedTensor_Blocks`, `SignedTensor_Domination`, `SignedTensor_Overlap`, `SignedTensor_Resolution`, `Tensor_Postselection`, `Unitary_Basic`, `Unitary_Spectral`, `Young_Classification`, `Young_Entropy`, `Young_Restriction`.
--
--   **Imports.** It imports the published bundle `Def_CoordinateSweeps`.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.CoordinateSweeps.Grid.Holes.conditional_sparse_main`, `OAI.CoordinateSweeps.all_grid_moment` and `OAI.CoordinateSweeps.conditional_main`.
-- source:
--   OpenAI, Conditional information under deterministic coordinate sweeps, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Conditional-information-under-deterministic-coordinate-sweeps-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_CoordinateSweeps

section
-- module Solutions.OAIQ56_CS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
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
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps

/- A probability law on a finite sample space, with real-valued masses. -/

namespace FiniteLaw

variable {Ω X Y : Type*}

variable [Fintype Ω] [Fintype X] [Fintype Y]

@[simp] theorem uniform_apply [Nonempty Ω] (x : Ω) : uniform Ω x =
    (Fintype.card Ω : ℝ)⁻¹ := rfl

@[simp] theorem map_apply (μ : FiniteLaw Ω) (f : Ω → X) (y : X) :
    μ.map f y = ∑ x, if f x = y then μ x else 0 := rfl

/- Mixture of two laws, with the real probability range explicit. -/
def mix (μ ν : FiniteLaw Ω) (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1) : FiniteLaw Ω where
  mass x := (1 - z) * μ x + z * ν x
  nonneg x := add_nonneg (mul_nonneg (sub_nonneg.mpr hz') (μ.nonneg x))
    (mul_nonneg hz (ν.nonneg x))
  total := by
    rw [finsum_eq_sum_of_fintype]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, μ.sum_mass, ν.sum_mass]
    ring

/- Independent laws on finitely many (possibly different) finite spaces. -/
def independent {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, Fintype (A i)]
    (μ : ∀ i, FiniteLaw (A i)) : FiniteLaw (∀ i, A i) where
  mass x := ∏ i, μ i (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (μ i).nonneg (x i))
  total := by
    rw [finsum_eq_sum_of_fintype]
    rw [← Fintype.prod_sum]
    simp only [FiniteLaw.sum_mass, Finset.prod_const_one]

/- The finite total-variation convention of the source: half the l1 distance. -/

end FiniteLaw

def lineCost (m u : ℕ) : ℝ :=
  Real.log ((m : ℝ)^u / (m.descFactorial u : ℝ))

def lineLaw (d : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1) :
    FiniteLaw (Equiv.Perm (Cube d)) :=
  (FiniteLaw.uniform _).mix (binaryLaw d) z hz hz'

/- An ordered power-of-two grid. Its coordinate bounds are kept in the theorem,
not hidden in a change to the definition of the process. -/

namespace Grid

def stageLaw (G : Grid) (j : Fin G.b) (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1) :
    FiniteLaw (G.Line j → Equiv.Perm (Cube (G.bits j))) :=
  FiniteLaw.independent (fun _ : G.Line j => lineLaw (G.bits j) z hz hz')

/- All stage-lines randomize independently, exactly as in 03-paths:5-17. -/
def choiceLaw (G : Grid) (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1) : FiniteLaw G.Choices :=
  FiniteLaw.independent (fun j => G.stageLaw j z hz hz')

/- Allowed grid, with R=2^r. This is precisely m_j ∈ [R,R²] in bit coordinates. -/

@[simp] theorem choiceWeight_eq (G : Grid) (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1)
    (ω : G.Choices) : G.choiceWeight z ω = G.choiceLaw z hz hz' ω := rfl

end Grid

namespace Grid

variable (G : Grid)

@[simp] theorem boundary_zero (ω : G.Choices) : G.boundary ω 0 = 1 := by
  simp [boundary]

theorem boundary_succ (ω : G.Choices) {t : ℕ} (ht : t < G.b) :
    G.boundary ω (t+1) = G.stage ω ⟨t,ht⟩ * G.boundary ω t := by
  unfold boundary
  rw [List.take_succ_eq_append_getElem (by simpa using ht)]
  simp [List.reverse_append]

@[simp] theorem stage_apply_same (ω : G.Choices) (j : Fin G.b) (x : G.Slot) :
    G.stage ω j x j = ω j (fun k => x k) (x j) := by
  simp [stage, fiberPerm, Equiv.piSplitAt_apply, Equiv.piSplitAt_symm_apply]

theorem stage_apply_ne (ω : G.Choices) (j k : Fin G.b) (hk : k ≠ j) (x : G.Slot) :
    G.stage ω j x k = x k := by
  simp [stage, fiberPerm, Equiv.piSplitAt_apply, Equiv.piSplitAt_symm_apply, hk]

namespace Holes
variable {G} {h : ℕ}

def StepCompatible (H : G.Holes h) (ω : G.Choices) : Prop :=
  ∀ i (j : Fin G.b), G.stage ω j (H.path i j.castSucc) = H.path i j.succ

theorem compatible_iff_step (H : G.Holes h) (ω : G.Choices) :
    H.Compatible ω ↔ H.StepCompatible ω := by
  constructor
  · intro hω i j
    have hs := congrArg (fun g : Equiv.Perm G.Slot => g (H.path i 0))
      (G.boundary_succ ω j.isLt)
    change G.boundary ω (j.val+1) (H.path i 0) =
      G.stage ω j (G.boundary ω j.val (H.path i 0)) at hs
    have h1 := hω i j.succ
    have h0 := hω i j.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h0
    rw [h1, h0] at hs
    exact hs.symm
  · intro hω i t
    have hb : ∀ n (hn : n ≤ G.b), G.boundary ω n (H.path i 0) =
        H.path i ⟨n, by omega⟩ := by
      intro n
      induction n with
      | zero => intro hn; simp
      | succ n ih =>
        intro hn
        have hnb : n < G.b := by omega
        rw [G.boundary_succ ω hnb]
        change G.stage ω ⟨n,hnb⟩ (G.boundary ω n (H.path i 0)) = _
        rw [ih (by omega)]
        exact hω i ⟨n,hnb⟩
    exact hb t.val (by omega)

/- Compatibility is a product of independent line assignment events. -/
theorem step_iff_coordinate (H : G.Holes h) (ω : G.Choices) :
    H.StepCompatible ω ↔ ∀ i (j : Fin G.b),
      ω j (fun k => H.path i j.castSucc k) (H.path i j.castSucc j) = H.path i j.succ j := by
  constructor
  · intro hω i j
    have hh := congrFun (hω i j) j
    simpa using hh
  · intro hω i j
    funext k
    by_cases hk : k = j
    · subst k
      exact (G.stage_apply_same ω j _).trans (hω i j)
    · exact (G.stage_apply_ne ω j k hk _).trans (H.coordinate_step i j k hk).symm

def OnLine (H : G.Holes h) (j : Fin G.b) (L : G.Line j) (i : Fin h) : Prop :=
  (fun k : {k : Fin G.b // k ≠ j} => H.path i j.castSucc k) = L

theorem line_input_injective (H : G.Holes h) (j : Fin G.b) (L : G.Line j) :
    Function.Injective (fun i : {i : Fin h // H.OnLine j L i} => H.path i j.castSucc j) := by
  intro i i' he
  apply Subtype.ext
  apply H.disjoint j.castSucc
  funext k
  by_cases hk : k = j
  · subst k; exact he
  · exact (congrFun i.property ⟨k,hk⟩).trans (congrFun i'.property ⟨k,hk⟩).symm

theorem line_output_injective (H : G.Holes h) (j : Fin G.b) (L : G.Line j) :
    Function.Injective (fun i : {i : Fin h // H.OnLine j L i} => H.path i j.succ j) := by
  intro i i' he
  apply Subtype.ext
  apply H.disjoint j.succ
  funext k
  by_cases hk : k = j
  · subst k; exact he
  · change H.path i.val j.succ k = H.path i'.val j.succ k
    rw [H.coordinate_step _ _ _ hk, H.coordinate_step _ _ _ hk]
    exact (congrFun i.property ⟨k,hk⟩).trans (congrFun i'.property ⟨k,hk⟩).symm

/- Disjoint source trajectories really are feasible; no probability event
is postulated to be nonempty. The main target still retains its explicit
feasibility hypothesis. -/
theorem feasible_of_disjoint (H : G.Holes h) : H.Feasible := by
  have hex : ∀ (j : Fin G.b) (L : G.Line j), ∃ σ : Equiv.Perm (Cube (G.bits j)),
      ∀ i : {i : Fin h // H.OnLine j L i}, σ (H.path i j.castSucc j) = H.path i j.succ j := by
    intro j L
    exact Equiv.Perm.exists_extending_pair _ _ (H.line_input_injective j L)
      (H.line_output_injective j L)
  choose ω hω using hex
  refine ⟨ω, (H.compatible_iff_step ω).mpr ((H.step_iff_coordinate ω).mpr ?_)⟩
  intro i j
  exact hω j (fun k => H.path i j.castSucc k) ⟨i, rfl⟩

end Holes
end Grid

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

variable [DecidableEq Ω]

def assignments {h : ℕ} (μ : FiniteLaw (Equiv.Perm Ω))
    (x y : Fin h ↪ Ω) : ℝ :=
  ∑ g : Equiv.Perm Ω, if x.trans g.toEmbedding = y then μ g else 0

end FiniteLaw

namespace Grid.Holes
variable {G : Grid} {h : ℕ}

def LineCompatible (H : G.Holes h) (j : Fin G.b) (L : G.Line j)
    (σ : Equiv.Perm (Cube (G.bits j))) : Prop :=
  ∀ i : {i : Fin h // H.OnLine j L i}, σ (H.path i j.castSucc j) = H.path i j.succ j

theorem compatible_iff_lines (H : G.Holes h) (ω : G.Choices) :
    H.Compatible ω ↔ ∀ j L, H.LineCompatible j L (ω j L) := by
  rw [H.compatible_iff_step, H.step_iff_coordinate]
  constructor
  · intro hω j L i
    have hh := hω i.val j
    rw [i.property] at hh
    exact hh
  · intro hω i j
    exact hω j (fun k => H.path i j.castSucc k) ⟨i,rfl⟩

def compatibleEquiv (H : G.Holes h) :
    {ω : G.Choices // H.Compatible ω} ≃
      (∀ j L, {σ : Equiv.Perm (Cube (G.bits j)) // H.LineCompatible j L σ}) where
  toFun ω j L := ⟨ω.val j L, (H.compatible_iff_lines ω.val).mp ω.property j L⟩
  invFun σ := ⟨(fun j L => (σ j L).val),
    (H.compatible_iff_lines _).mpr (fun j L => (σ j L).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/- Probability of the prescribed trajectory event, with the root definition. -/

theorem card_onLine (H : G.Holes h) (j : Fin G.b) (L : G.Line j) :
    Fintype.card {i : Fin h // H.OnLine j L i} = H.lineCount j L := by
  have hh := Fintype.card_subtype (H.OnLine j L)
  unfold lineCount
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 2

def lineCards (H : G.Holes h) (j : Fin G.b) (L : G.Line j) :
    Fin (H.lineCount j L) ≃ {i : Fin h // H.OnLine j L i} :=
  (Fintype.equivFinOfCardEq (H.card_onLine j L)).symm

def lineInput (H : G.Holes h) (j : Fin G.b) (L : G.Line j) :
    Fin (H.lineCount j L) ↪ Cube (G.bits j) :=
  H.lineCards j L |>.toEmbedding |>.trans ⟨_, H.line_input_injective j L⟩

def lineOutput (H : G.Holes h) (j : Fin G.b) (L : G.Line j) :
    Fin (H.lineCount j L) ↪ Cube (G.bits j) :=
  H.lineCards j L |>.toEmbedding |>.trans ⟨_, H.line_output_injective j L⟩

end Grid.Holes
end CoordinateSweeps

end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Matrix_TensorMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.PositiveTensor

variable {J : Type*} [Fintype J] [DecidableEq J]

/- Finite positive operators are dominated by their trace times identity. -/

variable {K : Type*} [Fintype K] [DecidableEq K]

def outer (v : J → ℂ) : Matrix J J ℂ := Matrix.vecMulVec v (star v)

/- Finite Cauchy--Schwarz for a decomposition of the purification vector.
The only loss is the number of actual exception patterns, later polynomial. -/
def partialTrace (A : Matrix (J × K) (J × K) ℂ) : Matrix J J ℂ := fun i j => ∑ k, A (i,k) (j,k)

end CoordinateSweeps.PositiveTensor
namespace CoordinateSweeps.PositiveTensor
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

def productMatrix (r : I → Matrix A A ℂ) : Matrix (I → A) (I → A) ℂ :=
  fun u w => ∏ i, r i (u i) (w i)

end CoordinateSweeps.PositiveTensor

namespace CoordinateSweeps.PositiveTensor
variable {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

def inclusion (e : K ↪ J) : Matrix J K ℂ := fun j k => if j=e k then 1 else 0

end CoordinateSweeps.PositiveTensor
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CoordinateSweeps.DependentTensor
variable {I : Type*} [Fintype I] [DecidableEq I] {J : I → Type*}
  [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]

def tensor (A : ∀ i, Matrix (J i) (J i) ℂ) : Matrix (∀ i, J i) (∀ i, J i) ℂ :=
  fun x y => ∏ i, A i (x i) (y i)

end CoordinateSweeps.DependentTensor
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.TensorBoard
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def tensor (A : I → Matrix J J ℂ) : Matrix (I → J) (I → J) ℂ :=
  fun x y => ∏ i, A i (x i) (y i)

end CoordinateSweeps.TensorBoard

namespace CoordinateSweeps.TensorBoard
variable {R C J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype J] [DecidableEq J]

/- Regularization is genuine positive definite, not an inverse assumption. -/

open scoped MatrixOrder CFC in
lemma exists_whitening (B : Matrix J J ℂ) (hB : B.PosDef) :
    ∃ A : Matrix J J ℂ, A.PosSemidef ∧ A*B*A=1 ∧
      ∀ D : Matrix J J ℂ, Commute B D → Commute A D := by
  refine ⟨B ^ (-(1/2) : ℝ), Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg,
    CFC.conjugate_rpow_neg_one_half B hB.isStrictlyPositive, ?_⟩
  intro D hD
  exact hD.cfc_nnreal _

end CoordinateSweeps.TensorBoard
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Unitary_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps
namespace UnitaryIrrep
variable {Γ : Type*} [Group Γ] (ρ : UnitaryIrrep Γ)

def asRepresentation : Representation ℂ Γ (Fin ρ.dimension → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp ρ.matrix

@[simp] lemma asRepresentation_apply (g : Γ) (v : Fin ρ.dimension → ℂ) :
    ρ.asRepresentation g v=(ρ.matrix g).mulVec v := rfl

instance asRepresentation_irreducible : ρ.asRepresentation.IsIrreducible := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  have hn : (⊥ : Subrepresentation ρ.asRepresentation) ≠ ⊤ := by
    intro hh
    have h := congrArg Subrepresentation.toSubmodule hh
    exact bot_ne_top h
  refine { exists_pair_ne := ⟨⊥,⊤,hn⟩, eq_bot_or_eq_top := ?_ }
  intro S
  rcases ρ.irreducible S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with hh | hh
  · exact Or.inl (Subrepresentation.toSubmodule_injective hh)
  · exact Or.inr (Subrepresentation.toSubmodule_injective hh)

lemma character_asRepresentation (g : Γ) :
    ρ.asRepresentation.character g=Matrix.trace (ρ.matrix g) :=
  Matrix.trace_toLin'_eq _

/- Schur's scalar-commutant statement with all irreducibility obligations
proved directly from the exact source realization. -/

variable [Fintype Γ]

/- Character normalization in exactly the unnormalized trace convention. -/
def coefficient (g : Γ) : ℂ :=
  (ρ.dimension : ℂ)/(Fintype.card Γ : ℂ) * Matrix.trace (ρ.matrix g⁻¹)

lemma coefficient_conj (k g : Γ) : ρ.coefficient (k*g*k⁻¹)=ρ.coefficient g := by
  unfold coefficient
  congr 1
  have h := Representation.char_conj ρ.asRepresentation g⁻¹ k
  simpa [character_asRepresentation,mul_inv_rev,mul_assoc] using h

variable {A : Type*} [Semiring A] [Algebra ℂ A]

def projector (τ : Γ →* A) : A := ∑ g, ρ.coefficient g • τ g

lemma projector_commute (τ : Γ →* A) (k : Γ) :
    τ k * ρ.projector τ=ρ.projector τ * τ k := by
  have hcoef (g : Γ) : ρ.coefficient (k*(g*k⁻¹))=ρ.coefficient g := by
    simpa only [mul_assoc] using ρ.coefficient_conj k g
  have hh := Equiv.sum_comp (MulAut.conj k).toEquiv
    (fun g => ρ.coefficient g • (τ g * τ k))
  simpa [projector,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    MulAut.conj_apply,hcoef,coefficient_conj,← map_mul,mul_assoc] using hh

/- The isotypic projector acts as identity in its own irreducible. -/

end UnitaryIrrep
end CoordinateSweeps

/- Multiplicity in a unitary matrix representation is controlled by the
commutant dimension, with exact (unnormalized) character conventions. -/
namespace CoordinateSweeps
namespace UnitaryIrrep
variable {Γ : Type*} [Group Γ] [Fintype Γ]
variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixRepresentation (τ : Γ →* Matrix n n ℂ) : Representation ℂ Γ (n → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp τ

end UnitaryIrrep
end CoordinateSweeps
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.UnitaryIrrep
variable {Γ n : Type*} [Group Γ] [Fintype Γ] [Fintype n] [DecidableEq n]

/- The projected trace formula applies to actual elements of the group algebra,
not just to individual group elements. -/
def averageMatrix {Ω : Type*} [Fintype Ω] (τ : Γ →* Matrix n n ℂ)
    (w : Ω → ℂ) (g : Ω → Γ) : Matrix n n ℂ := ∑ ω, w ω • τ (g ω)

def averageAlgebra {Ω : Type*} [Fintype Ω] (w : Ω → ℂ) (g : Ω → Γ) :
    MonoidAlgebra ℂ Γ := ∑ ω, MonoidAlgebra.single (g ω) (w ω)

end CoordinateSweeps.UnitaryIrrep

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.UnitaryIrrep
variable {Γ Λ : Type*} [Group Γ] [Group Λ]

def pullback (ρ : UnitaryIrrep Λ) (e : Γ ≃* Λ) : UnitaryIrrep Γ where
  dimension := ρ.dimension
  positive := ρ.positive
  matrix := ρ.matrix.comp e.toMonoidHom
  unitary g := ρ.unitary (e g)
  irreducible S hS := ρ.irreducible S (by
    intro g v hv
    have hh := hS (e.symm g) v hv
    change (ρ.matrix (e (e.symm g))).mulVec v ∈ S at hh
    rwa [MulEquiv.apply_symm_apply] at hh)

end CoordinateSweeps.UnitaryIrrep
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.UnitaryRealization
variable {G J : Type*} [Group G] [Fintype G] [Fintype J] [DecidableEq J]

/- Gram averaging produces the invariant positive form directly from the
finite action; no invariant inner product is postulated. -/
lemma gram_posDef (τ : G →* Matrix J J ℂ) :
    (∑ g, (τ g).conjTranspose * τ g).PosDef := by
  apply Matrix.posDef_sum Finset.univ_nonempty
  intro g hg
  apply Matrix.PosDef.conjTranspose_mul_self
  intro x y h
  have hh := congrArg (fun v => (τ g⁻¹).mulVec v) h
  simpa only [Matrix.mulVec_mulVec,← map_mul,inv_mul_cancel,map_one,Matrix.one_mulVec] using hh

lemma gram_invariant (τ : G →* Matrix J J ℂ) (h : G) :
    (τ h).conjTranspose*(∑ g, (τ g).conjTranspose*τ g)*τ h=
      ∑ g, (τ g).conjTranspose*τ g := by
  have hh := Equiv.sum_comp (Equiv.mulRight h) (fun g => (τ g).conjTranspose*τ g)
  calc
    _ = ∑ g, (τ (g*h)).conjTranspose * τ (g*h) := by
      simp only [Matrix.mul_sum,Matrix.sum_mul,map_mul,Matrix.conjTranspose_mul]
      apply Finset.sum_congr rfl
      intro g hg
      simp only [mul_assoc]
    _ = _ := hh

/- Actual conjugating matrices and a unitary action for any finite complex
matrix representation. -/
theorem unitarize (τ : G →* Matrix J J ℂ) :
    ∃ A B : Matrix J J ℂ, A*B=1 ∧ B*A=1 ∧ A.IsHermitian ∧ B.IsHermitian ∧
      (∀ g, (B*τ g*A).conjTranspose*(B*τ g*A)=1) := by
  let M : Matrix J J ℂ := ∑ g, (τ g).conjTranspose*τ g
  obtain ⟨A,hA,hAMA,hcomm⟩ := TensorBoard.exists_whitening M (gram_posDef τ)
  have hAM : A*M=M*A := (hcomm M (Commute.refl M)).eq
  let B := M*A
  have hAB : A*B=1 := by simpa only [B,mul_assoc] using hAMA
  have hBA : B*A=1 := by change M*A*A=1; rw [← hAM]; exact hAMA
  have hB : B.IsHermitian := by
    change (M*A).conjTranspose=M*A
    rw [Matrix.conjTranspose_mul,hA.isHermitian.eq,(gram_posDef τ).isHermitian.eq,hAM]
  have hB2 : B*B=M := by
    calc
      _ = M*(A*B) := by simp only [B,mul_assoc]
      _ = M := by rw [hAB,mul_one]
  refine ⟨A,B,hAB,hBA,hA.isHermitian,hB,?_⟩
  intro g
  calc
    _ = A*((τ g).conjTranspose*(B*B)*τ g)*A := by
      rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hA.isHermitian.eq,hB.eq]
      simp only [mul_assoc]
    _ = A*M*A := by rw [hB2,gram_invariant τ g]
    _ = 1 := hAMA

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/- A genuine irreducible representation has a unitary finite matrix
realization, with the intertwining equivalence retained. -/
theorem exists_unitary (σ : Representation ℂ G V) [σ.IsIrreducible] :
    ∃ ρ : UnitaryIrrep G, Nonempty (Representation.Equiv σ ρ.asRepresentation) := by
  let d := Module.finrank ℂ V
  let e : V ≃ₗ[ℂ] (Fin d → ℂ) := (Module.finBasis ℂ V).equivFun
  let τ : G →* Matrix (Fin d) (Fin d) ℂ :=
    LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp ((e.conjAlgEquiv ℂ).toMonoidHom.comp σ)
  obtain ⟨A,B,hAB,hBA,hA,hB,hu⟩ := unitarize τ
  let f : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofLinearMap
    (Matrix.toLinAlgEquiv' B) (Matrix.toLinAlgEquiv' A)
    (by change Matrix.toLinAlgEquiv' B * Matrix.toLinAlgEquiv' A=1
        rw [← map_mul,hBA,map_one])
    (by change Matrix.toLinAlgEquiv' A * Matrix.toLinAlgEquiv' B=1
        rw [← map_mul,hAB,map_one])
  let E := e.trans f
  let ν : G →* Matrix (Fin d) (Fin d) ℂ :=
    { toFun := fun g => B*τ g*A
      map_one' := by rw [map_one,mul_one,hBA]
      map_mul' := by intro g h; rw [map_mul]; simp only [mul_assoc];
                     rw [← mul_assoc A B,hAB,one_mul] }
  have he (g : G) (v : V) : (τ g).mulVec (e v)=e (σ g v) := by
    change (LinearMap.toMatrix' (e.conj (σ g))).mulVec (e v)=_
    rw [LinearMap.toMatrix'_mulVec]
    simp
  have hE (g : G) (v : V) : (ν g).mulVec (E v)=E (σ g v) := by
    change (B*τ g*A).mulVec (B.mulVec (e v))=B.mulVec (e (σ g v))
    rw [Matrix.mulVec_mulVec]
    have hh : B*τ g*A*B=B*τ g := by simp only [mul_assoc,hAB,mul_one]
    rw [hh,← Matrix.mulVec_mulVec,he]
  have hd : 0 < d := by
    have : Nontrivial σ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) σ.asModule
    have : Nontrivial V := inferInstanceAs (Nontrivial σ.asModule)
    exact Module.finrank_pos
  let ρ : UnitaryIrrep G :=
    { dimension := d
      positive := hd
      matrix := ν
      unitary := hu
      irreducible := by
        intro S hS
        let T : Subrepresentation σ :=
          { toSubmodule := S.comap E.toLinearMap
            apply_mem_toSubmodule := by
              intro g v hv
              change E (σ g v) ∈ S
              rw [← hE]
              exact hS g (E v) hv }
        rcases eq_bot_or_eq_top T with ht | ht
        · left
          apply le_antisymm _ bot_le
          intro w hw
          have hv : E.symm w ∈ T := by change E (E.symm w)∈S; simpa using hw
          rw [ht] at hv
          have hh : E.symm w=0 := hv
          simpa using congrArg E hh
        · right
          apply le_antisymm le_top
          intro w hw
          have hv : E.symm w ∈ T := by rw [ht]; trivial
          change E (E.symm w) ∈ S at hv
          simpa using hv }
  refine ⟨ρ,⟨Representation.Equiv.mk E ?_⟩⟩
  intro g
  apply LinearMap.ext
  intro v
  exact (hE g v).symm

end CoordinateSweeps.UnitaryRealization

end
end
end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Conditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.Grid

/- Concatenation of the *ordered* coordinate sequences. -/
def concat (A B : Grid) : Grid where
  b := A.b+B.b
  positive := Nat.add_pos_left A.positive _
  bits := Fin.addCases A.bits B.bits

@[simp] lemma concat_bits_left (A B : Grid) (i : Fin A.b) :
    (concat A B).bits (Fin.castAdd B.b i)=A.bits i := by simp [concat]
@[simp] lemma concat_bits_right (A B : Grid) (i : Fin B.b) :
    (concat A B).bits (Fin.natAdd A.b i)=B.bits i := by simp [concat]

/- Literal Cartesian identification for the split, retaining all bit labels. -/
def splitSlots (A B : Grid) : (concat A B).Slot ≃ A.Slot × B.Slot :=
  ((Equiv.prodPiEquivSumPi (fun i => Cube (A.bits i)) (fun j => Cube (B.bits j))).trans
    (Equiv.piCongr finSumFinEquiv (fun i => by
      cases i with
      | inl i => exact Equiv.cast (by simp [concat])
      | inr j => exact Equiv.cast (by simp [concat])))).symm

@[simp] lemma splitSlots_left (A B : Grid) (x : (concat A B).Slot) (i : Fin A.b) :
    (splitSlots A B x).1 i = (Equiv.cast (by simp : Cube ((concat A B).bits (Fin.castAdd B.b i))=Cube (A.bits i)))
      (x (Fin.castAdd B.b i)) := by
  rfl

@[simp] lemma splitSlots_right (A B : Grid) (x : (concat A B).Slot) (j : Fin B.b) :
    (splitSlots A B x).2 j = (Equiv.cast (by simp : Cube ((concat A B).bits (Fin.natAdd A.b j))=Cube (B.bits j)))
      (x (Fin.natAdd A.b j)) := by
  rfl

end CoordinateSweeps.Grid

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps

/- Deleting a head coordinate commutes with the literal Fin concatenation. -/
def finDeleteLeft {m n : ℕ} (i : Fin m) :
    ({j : Fin m // j ≠ i} ⊕ Fin n) ≃ {j : Fin (m+n) // j ≠ Fin.castAdd n i} where
  toFun z := match z with
    | Sum.inl j => ⟨Fin.castAdd n j.val,by simpa using j.property⟩
    | Sum.inr j => ⟨Fin.natAdd m j,by intro h; have ht := congrArg Fin.val h; simp at ht; omega⟩
  invFun z := Fin.addCases (motive := fun j : Fin (m+n) => j ≠ Fin.castAdd n i → ({j : Fin m // j ≠ i} ⊕ Fin n))
    (fun j (h : Fin.castAdd n j ≠ Fin.castAdd n i) => Sum.inl ⟨j,by simpa using h⟩)
    (fun j (_h : Fin.natAdd m j ≠ Fin.castAdd n i) => Sum.inr j) z.val z.property
  left_inv z := by cases z <;> simp
  right_inv z := by
    rcases z with ⟨j,hj⟩
    induction j using Fin.addCases with
    | left j => simp
    | right j => simp

@[simp] lemma finDeleteLeft_inl {m n : ℕ} (i : Fin m) (j : {j : Fin m // j ≠ i}) :
    (finDeleteLeft (n := n) i (Sum.inl j)).val=Fin.castAdd n j.val := rfl
@[simp] lemma finDeleteLeft_inr {m n : ℕ} (i : Fin m) (j : Fin n) :
    (finDeleteLeft (n := n) i (Sum.inr j)).val=Fin.natAdd m j := rfl

/- Deleting a tail coordinate, in the same original head-then-tail order. -/
def finDeleteRight {m n : ℕ} (i : Fin n) :
    (Fin m ⊕ {j : Fin n // j ≠ i}) ≃ {j : Fin (m+n) // j ≠ Fin.natAdd m i} where
  toFun z := match z with
    | Sum.inl j => ⟨Fin.castAdd n j,by intro h; have ht := congrArg Fin.val h; simp at ht; omega⟩
    | Sum.inr j => ⟨Fin.natAdd m j.val,by simpa using j.property⟩
  invFun z := Fin.addCases (motive := fun j : Fin (m+n) => j ≠ Fin.natAdd m i → (Fin m ⊕ {j : Fin n // j ≠ i}))
    (fun j (_h : Fin.castAdd n j ≠ Fin.natAdd m i) => Sum.inl j)
    (fun j (h : Fin.natAdd m j ≠ Fin.natAdd m i) => Sum.inr ⟨j,by simpa using h⟩) z.val z.property
  left_inv z := by cases z <;> simp
  right_inv z := by
    rcases z with ⟨j,hj⟩
    induction j using Fin.addCases with
    | left j => simp
    | right j => simp

@[simp] lemma finDeleteRight_inl {m n : ℕ} (i : Fin n) (j : Fin m) :
    (finDeleteRight (m := m) i (Sum.inl j)).val=Fin.castAdd n j := rfl
@[simp] lemma finDeleteRight_inr {m n : ℕ} (i : Fin n) (j : {j : Fin n // j ≠ i}) :
    (finDeleteRight (m := m) i (Sum.inr j)).val=Fin.natAdd m j.val := rfl

end CoordinateSweeps

namespace CoordinateSweeps.Grid

/- Row line chart: the other head coordinates and the fixed tail row label. -/
def rowLines (A B : Grid) (i : Fin A.b) :
    (A.Line i × B.Slot) ≃ (concat A B).Line (Fin.castAdd B.b i) :=
  (Equiv.prodPiEquivSumPi (fun j : {j : Fin A.b // j ≠ i} => Cube (A.bits j))
    (fun k => Cube (B.bits k))).trans
    (Equiv.piCongr (finDeleteLeft (n := B.b) i) (fun j => by
      cases j with
      | inl j => exact Equiv.cast (by
          change Cube (A.bits j)=Cube (Fin.addCases A.bits B.bits (Fin.castAdd B.b j))
          simp)
      | inr k => exact Equiv.cast (by
          change Cube (B.bits k)=Cube (Fin.addCases A.bits B.bits (Fin.natAdd A.b k))
          simp)))

/- Column line chart: the fixed head label and the other tail coordinates. -/
def columnLines (A B : Grid) (i : Fin B.b) :
    (A.Slot × B.Line i) ≃ (concat A B).Line (Fin.natAdd A.b i) :=
  (Equiv.prodPiEquivSumPi (fun j => Cube (A.bits j))
    (fun k : {k : Fin B.b // k ≠ i} => Cube (B.bits k))).trans
    (Equiv.piCongr (finDeleteRight (m := A.b) i) (fun j => by
      cases j with
      | inl j => exact Equiv.cast (by
          change Cube (A.bits j)=Cube (Fin.addCases A.bits B.bits (Fin.castAdd B.b j))
          simp)
      | inr k => exact Equiv.cast (by
          change Cube (B.bits k)=Cube (Fin.addCases A.bits B.bits (Fin.natAdd A.b k))
          simp)))

lemma rowLines_evaluation (A B : Grid) (i : Fin A.b) (x : (concat A B).Slot) :
    (rowLines A B i).symm (fun j => x j.val)=
      ((fun j : {j : Fin A.b // j ≠ i} => (splitSlots A B x).1 j.val),(splitSlots A B x).2) := by
  apply Prod.ext
  · funext j
    rfl
  · funext j
    rfl

lemma columnLines_evaluation (A B : Grid) (i : Fin B.b) (x : (concat A B).Slot) :
    (columnLines A B i).symm (fun j => x j.val)=
      ((splitSlots A B x).1,(fun j : {j : Fin B.b // j ≠ i} => (splitSlots A B x).2 j.val)) := by
  apply Prod.ext
  · funext j
    rfl
  · funext j
    rfl

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid

def leftCube (A B : Grid) (i : Fin A.b) :
    Cube ((concat A B).bits (Fin.castAdd B.b i)) ≃ Cube (A.bits i) :=
  Equiv.cast (by simp)
def rightCube (A B : Grid) (j : Fin B.b) :
    Cube ((concat A B).bits (Fin.natAdd A.b j)) ≃ Cube (B.bits j) :=
  Equiv.cast (by simp)

def prefixFiber (A B : Grid) (i : Fin A.b) :
    ((concat A B).Line (Fin.castAdd B.b i) → Equiv.Perm (Cube ((concat A B).bits (Fin.castAdd B.b i)))) ≃
      (B.Slot → A.Line i → Equiv.Perm (Cube (A.bits i))) :=
  (Equiv.arrowCongr ((rowLines A B i).symm.trans (Equiv.prodComm _ _))
    (leftCube A B i).permCongr).trans (Equiv.curry _ _ _)

def suffixFiber (A B : Grid) (i : Fin B.b) :
    ((concat A B).Line (Fin.natAdd A.b i) → Equiv.Perm (Cube ((concat A B).bits (Fin.natAdd A.b i)))) ≃
      (A.Slot → B.Line i → Equiv.Perm (Cube (B.bits i))) :=
  (Equiv.arrowCongr (columnLines A B i).symm
    (rightCube A B i).permCongr).trans (Equiv.curry _ _ _)

/- Exact two-part choice-space equivalence, not just an equality in law. -/
def choicesSplit (A B : Grid) : (concat A B).Choices ≃
    ((B.Slot → A.Choices) × (A.Slot → B.Choices)) :=
  ((Equiv.prodCongr
    (Equiv.piComm (fun (_y : B.Slot) (i : Fin A.b) => A.Line i → Equiv.Perm (Cube (A.bits i))))
    (Equiv.piComm (fun (_x : A.Slot) (i : Fin B.b) => B.Line i → Equiv.Perm (Cube (B.bits i))))).trans
    ((Equiv.prodPiEquivSumPi
      (fun i : Fin A.b => B.Slot → A.Line i → Equiv.Perm (Cube (A.bits i)))
      (fun i : Fin B.b => A.Slot → B.Line i → Equiv.Perm (Cube (B.bits i)))).trans
      (Equiv.piCongr finSumFinEquiv (fun i => by
        cases i with
        | inl i => exact (prefixFiber A B i).symm
        | inr j => exact (suffixFiber A B j).symm)))).symm

def rowChoices (A B : Grid) (ω : (concat A B).Choices) (y : B.Slot) : A.Choices :=
  (choicesSplit A B ω).1 y
def columnChoices (A B : Grid) (ω : (concat A B).Choices) (x : A.Slot) : B.Choices :=
  (choicesSplit A B ω).2 x

lemma rowChoices_apply (A B : Grid) (ω : (concat A B).Choices) (y : B.Slot)
    (i : Fin A.b) (L : A.Line i) :
    rowChoices A B ω y i L=(leftCube A B i).permCongr
      (ω (Fin.castAdd B.b i) (rowLines A B i (L,y))) := by rfl

lemma columnChoices_apply (A B : Grid) (ω : (concat A B).Choices) (x : A.Slot)
    (i : Fin B.b) (L : B.Line i) :
    columnChoices A B ω x i L=(rightCube A B i).permCongr
      (ω (Fin.natAdd A.b i) (columnLines A B i (x,L))) := by rfl

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid

lemma rowLines_at_slot (A B : Grid) (i : Fin A.b) (x : (concat A B).Slot) :
    rowLines A B i ((fun j => (splitSlots A B x).1 j.val),(splitSlots A B x).2)=
      (fun (j : {j : Fin (concat A B).b // j ≠ Fin.castAdd B.b i}) => x j.val) := by
  have hh := congrArg (rowLines A B i) (rowLines_evaluation A B i x)
  simpa using hh.symm

lemma columnLines_at_slot (A B : Grid) (i : Fin B.b) (x : (concat A B).Slot) :
    columnLines A B i ((splitSlots A B x).1,(fun j => (splitSlots A B x).2 j.val))=
      (fun (j : {j : Fin (concat A B).b // j ≠ Fin.natAdd A.b i}) => x j.val) := by
  have hh := congrArg (columnLines A B i) (columnLines_evaluation A B i x)
  simpa using hh.symm

/- A head stage really acts by independent row stages in the Cartesian chart. -/
theorem stage_split_left (A B : Grid) (ω : (concat A B).Choices) (i : Fin A.b)
    (x : (concat A B).Slot) :
    splitSlots A B ((concat A B).stage ω (Fin.castAdd B.b i) x)=
      (A.stage (rowChoices A B ω (splitSlots A B x).2) i (splitSlots A B x).1,
        (splitSlots A B x).2) := by
  apply Prod.ext
  · funext j
    by_cases h : j=i
    · subst j
      change leftCube A B i ((concat A B).stage ω (Fin.castAdd B.b i) x (Fin.castAdd B.b i))=A.stage (rowChoices A B ω (splitSlots A B x).2) i (splitSlots A B x).1 i
      erw [stage_apply_same,stage_apply_same,rowChoices_apply]
      simp only [Equiv.permCongr_apply,rowLines_at_slot]
      change leftCube A B i (ω _ _ (x _))=leftCube A B i (ω _ _ ((leftCube A B i).symm (leftCube A B i (x _))))
      rw [Equiv.symm_apply_apply]
    · change leftCube A B j ((concat A B).stage ω (Fin.castAdd B.b i) x (Fin.castAdd B.b j))=A.stage (rowChoices A B ω (splitSlots A B x).2) i (splitSlots A B x).1 j
      erw [stage_apply_ne _ _ _ _ h]
      change leftCube A B j ((concat A B).stage ω (Fin.castAdd B.b i) x (Fin.castAdd B.b j))=leftCube A B j (x _)
      erw [stage_apply_ne _ _ _ _ (by intro hh; apply h; apply Fin.ext; have := congrArg Fin.val hh; simp at this; omega)]
  · funext j
    change rightCube A B j ((concat A B).stage ω (Fin.castAdd B.b i) x (Fin.natAdd A.b j))=rightCube A B j (x _)
    erw [stage_apply_ne _ _ _ _ (by intro h; have hh := congrArg Fin.val h; simp at hh; omega)]

/- A tail stage really acts by independent column stages. -/
theorem stage_split_right (A B : Grid) (ω : (concat A B).Choices) (i : Fin B.b)
    (x : (concat A B).Slot) :
    splitSlots A B ((concat A B).stage ω (Fin.natAdd A.b i) x)=
      ((splitSlots A B x).1,B.stage (columnChoices A B ω (splitSlots A B x).1) i (splitSlots A B x).2) := by
  apply Prod.ext
  · funext j
    change leftCube A B j ((concat A B).stage ω (Fin.natAdd A.b i) x (Fin.castAdd B.b j))=leftCube A B j (x _)
    erw [stage_apply_ne _ _ _ _ (by intro h; have hh := congrArg Fin.val h; simp at hh; omega)]
  · funext j
    by_cases h : j=i
    · subst j
      change rightCube A B i ((concat A B).stage ω (Fin.natAdd A.b i) x (Fin.natAdd A.b i))=B.stage (columnChoices A B ω (splitSlots A B x).1) i (splitSlots A B x).2 i
      erw [stage_apply_same,stage_apply_same,columnChoices_apply]
      simp only [Equiv.permCongr_apply,columnLines_at_slot]
      change rightCube A B i (ω _ _ (x _))=rightCube A B i (ω _ _ ((rightCube A B i).symm (rightCube A B i (x _))))
      rw [Equiv.symm_apply_apply]
    · change rightCube A B j ((concat A B).stage ω (Fin.natAdd A.b i) x (Fin.natAdd A.b j))=B.stage (columnChoices A B ω (splitSlots A B x).1) i (splitSlots A B x).2 j
      erw [stage_apply_ne _ _ _ _ h]
      change rightCube A B j ((concat A B).stage ω (Fin.natAdd A.b i) x (Fin.natAdd A.b j))=rightCube A B j (x _)
      erw [stage_apply_ne _ _ _ _ (by intro hh; apply h; apply Fin.ext; have := congrArg Fin.val hh; simp at this; omega)]

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid

lemma boundary_split_prefix (A B : Grid) (ω : (concat A B).Choices)
    (x : (concat A B).Slot) (t : ℕ) (ht : t≤A.b) :
    splitSlots A B ((concat A B).boundary ω t x)=
      (A.boundary (rowChoices A B ω (splitSlots A B x).2) t (splitSlots A B x).1,
       (splitSlots A B x).2) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ha : t<A.b := by omega
    have hc : t<(concat A B).b := by change t<A.b+B.b; omega
    have hi : (⟨t,hc⟩ : Fin (concat A B).b)=Fin.castAdd B.b (⟨t,ha⟩ : Fin A.b) := rfl
    rw [(concat A B).boundary_succ ω hc,A.boundary_succ _ ha]
    simp only [Equiv.Perm.mul_apply]
    rw [hi,stage_split_left,ih (by omega)]

lemma boundary_split_suffix (A B : Grid) (ω : (concat A B).Choices)
    (x : (concat A B).Slot) (t : ℕ) (ht : t≤B.b) :
    splitSlots A B ((concat A B).boundary ω (A.b+t) x)=
      (A.sweep (rowChoices A B ω (splitSlots A B x).2) (splitSlots A B x).1,
       B.boundary (columnChoices A B ω
         (A.sweep (rowChoices A B ω (splitSlots A B x).2) (splitSlots A B x).1)) t
         (splitSlots A B x).2) := by
  induction t with
  | zero => simpa [sweep] using boundary_split_prefix A B ω x A.b le_rfl
  | succ t ih =>
    have hb : t<B.b := by omega
    have hc : A.b+t<(concat A B).b := by change A.b+t<A.b+B.b; omega
    have hi : (⟨A.b+t,hc⟩ : Fin (concat A B).b)=Fin.natAdd A.b (⟨t,hb⟩ : Fin B.b) := rfl
    rw [Nat.add_succ,(concat A B).boundary_succ ω hc,B.boundary_succ _ hb]
    simp only [Equiv.Perm.mul_apply]
    rw [hi,stage_split_right,ih (by omega)]

/- Actual ordered permutation factorization: row sweeps, then column sweeps. -/
theorem sweep_split (A B : Grid) (ω : (concat A B).Choices) (x : (concat A B).Slot) :
    splitSlots A B ((concat A B).sweep ω x)=
      (A.sweep (rowChoices A B ω (splitSlots A B x).2) (splitSlots A B x).1,
       B.sweep (columnChoices A B ω
         (A.sweep (rowChoices A B ω (splitSlots A B x).2) (splitSlots A B x).1))
         (splitSlots A B x).2) :=
  boundary_split_suffix A B ω x B.b le_rfl

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid

def prefixTime (A B : Grid) (t : Fin (A.b+1)) : Fin ((concat A B).b+1) :=
  ⟨t.val,by change t.val<A.b+B.b+1; have := t.isLt; omega⟩
def suffixTime (A B : Grid) (t : Fin (B.b+1)) : Fin ((concat A B).b+1) :=
  ⟨A.b+t.val,by change A.b+t.val<A.b+B.b+1; have := t.isLt; omega⟩

namespace Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

def rowOf (i : Fin h) : B.Slot := (splitSlots A B (H.path i 0)).2
def columnOf (i : Fin h) : A.Slot := (splitSlots A B (H.path i (suffixTime A B 0))).1

lemma row_constant (i : Fin h) (t : Fin (A.b+1)) :
    (splitSlots A B (H.path i (prefixTime A B t))).2=H.rowOf i := by
  obtain ⟨ω,hω⟩ := H.feasible_of_disjoint
  rw [← hω i (prefixTime A B t)]
  change (splitSlots A B ((concat A B).boundary ω t.val (H.path i 0))).2=_
  rw [boundary_split_prefix A B ω _ t.val (by have := t.isLt; omega)]
  rfl

lemma column_constant (i : Fin h) (t : Fin (B.b+1)) :
    (splitSlots A B (H.path i (suffixTime A B t))).1=H.columnOf i := by
  obtain ⟨ω,hω⟩ := H.feasible_of_disjoint
  unfold columnOf
  rw [← hω i (suffixTime A B t),← hω i (suffixTime A B 0)]
  change (splitSlots A B ((concat A B).boundary ω (A.b+t.val) (H.path i 0))).1=
    (splitSlots A B ((concat A B).boundary ω (A.b+0) (H.path i 0))).1
  rw [boundary_split_suffix A B ω _ t.val (by have := t.isLt; omega),
      boundary_split_suffix A B ω _ 0 (Nat.zero_le _)]

abbrev RowCard (y : B.Slot) := {i : Fin h // H.rowOf i=y}
abbrev ColumnCard (x : A.Slot) := {i : Fin h // H.columnOf i=x}
def rowCount (y : B.Slot) : ℕ := Fintype.card (H.RowCard y)
def columnCount (x : A.Slot) : ℕ := Fintype.card (H.ColumnCard x)
def rowCards (y : B.Slot) : Fin (H.rowCount y) ≃ H.RowCard y := (Fintype.equivFin _).symm
def columnCards (x : A.Slot) : Fin (H.columnCount x) ≃ H.ColumnCard x := (Fintype.equivFin _).symm

/- All holes in one actual row, with the inherited ordered trajectories. -/
def rowHoles (y : B.Slot) : A.Holes (H.rowCount y) where
  path i t := (splitSlots A B (H.path (H.rowCards y i).val (prefixTime A B t))).1
  disjoint t := by
    intro i j hij
    apply (H.rowCards y).injective
    apply Subtype.ext
    apply H.disjoint (prefixTime A B t)
    apply (splitSlots A B).injective
    apply Prod.ext hij
    exact (H.row_constant _ t).trans ((H.rowCards y i).property.trans
      ((H.rowCards y j).property.symm.trans (H.row_constant _ t).symm))
  coordinate_step i j k hk := by
    change leftCube A B k (H.path (H.rowCards y i).val (Fin.castAdd B.b j).succ (Fin.castAdd B.b k))=
      leftCube A B k (H.path (H.rowCards y i).val (Fin.castAdd B.b j).castSucc (Fin.castAdd B.b k))
    apply congrArg
    apply H.coordinate_step
    intro hh
    apply hk
    apply Fin.ext
    exact congrArg (fun u : Fin (A.b+B.b) => u.val) hh

/- All holes in one junction column, with the inherited tail trajectories. -/
def columnHoles (x : A.Slot) : B.Holes (H.columnCount x) where
  path i t := (splitSlots A B (H.path (H.columnCards x i).val (suffixTime A B t))).2
  disjoint t := by
    intro i j hij
    apply (H.columnCards x).injective
    apply Subtype.ext
    apply H.disjoint (suffixTime A B t)
    apply (splitSlots A B).injective
    apply Prod.ext _ hij
    exact (H.column_constant _ t).trans ((H.columnCards x i).property.trans
      ((H.columnCards x j).property.symm.trans (H.column_constant _ t).symm))
  coordinate_step i j k hk := by
    change rightCube A B k (H.path (H.columnCards x i).val (Fin.natAdd A.b j).succ (Fin.natAdd A.b k))=
      rightCube A B k (H.path (H.columnCards x i).val (Fin.natAdd A.b j).castSucc (Fin.natAdd A.b k))
    apply congrArg
    apply H.coordinate_step
    intro hh
    apply hk
    apply Fin.ext
    have := congrArg Fin.val hh
    simp at this
    omega

end Holes
end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid.Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

lemma row_step_iff (y : B.Slot) (τ : A.Choices) :
    (H.rowHoles y).StepCompatible τ ↔ ∀ i : Fin h, H.rowOf i=y → ∀ j : Fin A.b,
      A.stage τ j (splitSlots A B (H.path i (prefixTime A B j.castSucc))).1=
        (splitSlots A B (H.path i (prefixTime A B j.succ))).1 := by
  constructor
  · intro hs i hi j
    obtain ⟨k,hk⟩ := (H.rowCards y).surjective ⟨i,hi⟩
    have he := hs k j
    change A.stage τ j (splitSlots A B (H.path (H.rowCards y k).val (prefixTime A B j.castSucc))).1=
      (splitSlots A B (H.path (H.rowCards y k).val (prefixTime A B j.succ))).1 at he
    simpa only [hk] using he
  · intro hs k j
    exact hs (H.rowCards y k).val (H.rowCards y k).property j

lemma column_step_iff (x : A.Slot) (τ : B.Choices) :
    (H.columnHoles x).StepCompatible τ ↔ ∀ i : Fin h, H.columnOf i=x → ∀ j : Fin B.b,
      B.stage τ j (splitSlots A B (H.path i (suffixTime A B j.castSucc))).2=
        (splitSlots A B (H.path i (suffixTime A B j.succ))).2 := by
  constructor
  · intro hs i hi j
    obtain ⟨k,hk⟩ := (H.columnCards x).surjective ⟨i,hi⟩
    have he := hs k j
    change B.stage τ j (splitSlots A B (H.path (H.columnCards x k).val (suffixTime A B j.castSucc))).2=
      (splitSlots A B (H.path (H.columnCards x k).val (suffixTime A B j.succ))).2 at he
    simpa only [hk] using he
  · intro hs k j
    exact hs (H.columnCards x k).val (H.columnCards x k).property j

/- The trajectory event is exactly the product of all child trajectory events. -/
theorem compatible_split (ω : (concat A B).Choices) :
    H.Compatible ω ↔
      (∀ y : B.Slot, (H.rowHoles y).Compatible (rowChoices A B ω y)) ∧
      (∀ x : A.Slot, (H.columnHoles x).Compatible (columnChoices A B ω x)) := by
  constructor
  · intro hω
    have hs := (H.compatible_iff_step ω).mp hω
    constructor
    · intro y
      apply ((H.rowHoles y).compatible_iff_step _).mpr
      apply (H.row_step_iff y _).mpr
      intro i hi j
      have he := congrArg (fun x => (splitSlots A B x).1) (hs i (Fin.castAdd B.b j))
      rw [stage_split_left] at he
      change A.stage (rowChoices A B ω (splitSlots A B (H.path i (prefixTime A B j.castSucc))).2) j
        (splitSlots A B (H.path i (prefixTime A B j.castSucc))).1=
        (splitSlots A B (H.path i (prefixTime A B j.succ))).1 at he
      rw [H.row_constant i j.castSucc,hi] at he
      exact he
    · intro x
      apply ((H.columnHoles x).compatible_iff_step _).mpr
      apply (H.column_step_iff x _).mpr
      intro i hi j
      have he := congrArg (fun x => (splitSlots A B x).2) (hs i (Fin.natAdd A.b j))
      rw [stage_split_right] at he
      change B.stage (columnChoices A B ω (splitSlots A B (H.path i (suffixTime A B j.castSucc))).1) j
        (splitSlots A B (H.path i (suffixTime A B j.castSucc))).2=
        (splitSlots A B (H.path i (suffixTime A B j.succ))).2 at he
      rw [H.column_constant i j.castSucc,hi] at he
      exact he
  · rintro ⟨hR,hC⟩
    have hr (y : B.Slot) := (H.row_step_iff y _).mp (((H.rowHoles y).compatible_iff_step _).mp (hR y))
    have hc (x : A.Slot) := (H.column_step_iff x _).mp (((H.columnHoles x).compatible_iff_step _).mp (hC x))
    apply (H.compatible_iff_step ω).mpr
    intro i j
    change Fin (A.b+B.b) at j
    induction j using Fin.addCases with
    | left j =>
      apply (splitSlots A B).injective
      rw [stage_split_left]
      apply Prod.ext
      · change A.stage (rowChoices A B ω (splitSlots A B (H.path i (prefixTime A B j.castSucc))).2) j
          (splitSlots A B (H.path i (prefixTime A B j.castSucc))).1=
          (splitSlots A B (H.path i (prefixTime A B j.succ))).1
        rw [H.row_constant i j.castSucc]
        exact hr (H.rowOf i) i rfl j
      · exact (H.row_constant i j.castSucc).trans (H.row_constant i j.succ).symm
    | right j =>
      apply (splitSlots A B).injective
      rw [stage_split_right]
      apply Prod.ext
      · exact (H.column_constant i j.castSucc).trans (H.column_constant i j.succ).symm
      · change B.stage (columnChoices A B ω (splitSlots A B (H.path i (suffixTime A B j.castSucc))).1) j
          (splitSlots A B (H.path i (suffixTime A B j.castSucc))).2=
          (splitSlots A B (H.path i (suffixTime A B j.succ))).2
        rw [H.column_constant i j.castSucc]
        exact hc (H.columnOf i) i rfl j

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid

/- The literal real line mass, without changing any conditioning. -/
def rawLineWeight (k : ℕ) (z : ℝ) (σ : Equiv.Perm (Cube k)) : ℝ :=
  (1-z)*(Fintype.card (Equiv.Perm (Cube k)) : ℝ)⁻¹ + z*binaryLaw k σ

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid.Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

def splitCompatibleChoices : {ω : (concat A B).Choices // H.Compatible ω} ≃
    ((∀ y : B.Slot, {τ : A.Choices // (H.rowHoles y).Compatible τ}) ×
     (∀ x : A.Slot, {τ : B.Choices // (H.columnHoles x).Compatible τ})) where
  toFun ω := ((fun y => ⟨rowChoices A B ω.val y,((H.compatible_split ω.val).mp ω.property).1 y⟩),
    fun x => ⟨columnChoices A B ω.val x,((H.compatible_split ω.val).mp ω.property).2 x⟩)
  invFun τ := ⟨(choicesSplit A B).symm ((fun y => (τ.1 y).val),(fun x => (τ.2 x).val)),by
    apply (H.compatible_split _).mpr
    constructor
    · intro y
      change (H.rowHoles y).Compatible ((choicesSplit A B ((choicesSplit A B).symm _)).1 y)
      rw [Equiv.apply_symm_apply]
      exact (τ.1 y).property
    · intro x
      change (H.columnHoles x).Compatible ((choicesSplit A B ((choicesSplit A B).symm _)).2 x)
      rw [Equiv.apply_symm_apply]
      exact (τ.2 x).property⟩
  left_inv ω := by
    apply Subtype.ext
    change (choicesSplit A B).symm (choicesSplit A B ω.val)=ω.val
    exact Equiv.symm_apply_apply _ _
  right_inv τ := by
    apply Prod.ext
    · funext y
      apply Subtype.ext
      change ((choicesSplit A B) ((choicesSplit A B).symm _)).1 y=(τ.1 y).val
      rw [Equiv.apply_symm_apply]
    · funext x
      apply Subtype.ext
      change ((choicesSplit A B) ((choicesSplit A B).symm _)).2 x=(τ.2 x).val
      rw [Equiv.apply_symm_apply]

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Marked
variable {X Y I : Type*}
abbrev Free (x : I → X) := {z : X // ∀ i, z ≠ x i}

def freeEquiv (x : I → X) (y : I → Y) (e : X ≃ Y) (he : ∀ i, e (x i)=y i) :
    Free x ≃ Free y := e.subtypeEquiv (by
  intro z
  constructor
  · intro hz i hi
    apply hz i
    exact e.injective (hi.trans (he i).symm)
  · intro hz i hi
    apply hz i
    rw [hi,he])

def fix (x : I → X) : Subgroup (Equiv.Perm X) where
  carrier g := ∀ i, g (x i)=x i
  one_mem' _ := rfl
  mul_mem' := by
    intro g h hg hh i
    change g (h (x i))=x i
    rw [hh i,hg i]
  inv_mem' hg i := (Equiv.symm_apply_eq _).mpr (hg i).symm

def freePerm (x : I → X) : fix x →* Equiv.Perm (Free x) where
  toFun g := freeEquiv x x g.val g.property
  map_one' := by ext z; rfl
  map_mul' g h := by ext z; rfl

/- The honest symmetric group on the unmarked sites, including empty sets. -/
def freePermEquiv (x : I → X) : fix x ≃* Equiv.Perm (Free x) where
  toFun := freePerm x
  invFun σ := ⟨Equiv.Perm.ofSubtype σ,by
    intro i
    apply Equiv.Perm.ofSubtype_apply_of_not_mem
    simp only [not_forall,not_not]
    exact ⟨i,rfl⟩⟩
  left_inv g := by
    apply Subtype.ext
    ext z
    by_cases hz : ∀ i, z ≠ x i
    · rw [Equiv.Perm.ofSubtype_apply_of_mem _ hz]
      rfl
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hz]
      push Not at hz
      rcases hz with ⟨i,rfl⟩
      exact (g.property i).symm
  right_inv σ := by
    ext z
    change Equiv.Perm.ofSubtype σ z.val=(σ z).val
    exact Equiv.Perm.ofSubtype_apply_of_mem _ z.property
  map_mul' := (freePerm x).map_mul

lemma card_free [Fintype X] [Fintype I] (x : I → X) (hx : Function.Injective x) :
    Fintype.card (Free x)=Fintype.card X-Fintype.card I := by
  classical
  let e : Free x ≃ {z : X // ¬ z ∈ Set.range x} :=
    Equiv.subtypeEquivRight (fun z => by simp only [Set.mem_range,not_exists]; simp only [ne_eq,eq_comm])
  rw [Fintype.card_congr e,Fintype.card_subtype_compl]
  congr 1
  exact (Fintype.card_congr (Equiv.ofInjective x hx)).symm

end CoordinateSweeps.Marked

namespace CoordinateSweeps.Grid
@[simp] theorem card_slot (G : Grid) : Fintype.card G.Slot=G.size := by
  simp [Slot,size,Cube,Fintype.card_pi]

namespace Holes
variable {G : Grid} {h : ℕ}
abbrev FreeAt (H : G.Holes h) (t : Fin (G.b+1)) := Marked.Free (fun i => H.path i t)

def freeBoundary (H : G.Holes h) (ω : {ω : G.Choices // H.Compatible ω})
    (t : Fin (G.b+1)) : H.FreeAt 0 ≃ H.FreeAt t :=
  Marked.freeEquiv _ _ (G.boundary ω.val t.val) (fun i => ω.property i t)

lemma card_freeAt (H : G.Holes h) (t : Fin (G.b+1)) :
    Fintype.card (H.FreeAt t)=G.size-h := by
  have hh := Marked.card_free (fun i => H.path i t) (H.disjoint t)
  simp only [card_slot,Fintype.card_fin] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  exact Subsingleton.elim _ _

/- Literal target stabilizer isomorphism, not an assumed representation switch. -/
def stabilizerFreeEquiv (H : G.Holes h) : H.stabilizer ≃* Equiv.Perm (H.FreeAt 0) :=
  Marked.freePermEquiv (fun i => H.path i 0)

end Holes
end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid

def rowSweep (A B : Grid) (ω : B.Slot → A.Choices) : Equiv.Perm (concat A B).Slot :=
  Equiv.permCongr (splitSlots A B).symm (fiberPerm (fun y => A.sweep (ω y)))

def columnSweep (A B : Grid) (ω : A.Slot → B.Choices) : Equiv.Perm (concat A B).Slot :=
  Equiv.permCongr ((splitSlots A B).trans (Equiv.prodComm _ _)).symm
    (fiberPerm (fun x => B.sweep (ω x)))

lemma rowSweep_apply (A B : Grid) (ω : B.Slot → A.Choices) (x : (concat A B).Slot) :
    splitSlots A B (rowSweep A B ω x)=
      (A.sweep (ω (splitSlots A B x).2) (splitSlots A B x).1,(splitSlots A B x).2) := by
  unfold rowSweep
  simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  rfl

lemma columnSweep_apply (A B : Grid) (ω : A.Slot → B.Choices) (x : (concat A B).Slot) :
    splitSlots A B (columnSweep A B ω x)=
      ((splitSlots A B x).1,B.sweep (ω (splitSlots A B x).1) (splitSlots A B x).2) := by
  unfold columnSweep
  simp only [Equiv.permCongr_apply,Equiv.symm_trans_apply,Equiv.symm_symm,Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rfl

theorem sweep_eq_column_mul_row (A B : Grid) (ω : (concat A B).Choices) :
    (concat A B).sweep ω=columnSweep A B (columnChoices A B ω)*rowSweep A B (rowChoices A B ω) := by
  apply Equiv.ext
  intro x
  apply (splitSlots A B).injective
  have hr := rowSweep_apply A B (rowChoices A B ω) x
  have hc := columnSweep_apply A B (columnChoices A B ω) (rowSweep A B (rowChoices A B ω) x)
  have ht := congrArg (fun t : A.Slot × B.Slot =>
    (t.1,B.sweep (columnChoices A B ω t.1) t.2)) hr
  exact (sweep_split A B ω x).trans (hc.trans ht).symm

theorem rowSweep_eq_boundary (A B : Grid) (ω : (concat A B).Choices) :
    rowSweep A B (rowChoices A B ω)=(concat A B).boundary ω A.b := by
  apply Equiv.ext
  intro x
  apply (splitSlots A B).injective
  rw [rowSweep_apply,boundary_split_prefix A B ω x A.b le_rfl]
  rfl

namespace Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)
abbrev RowChoices := ∀ y : B.Slot, {τ : A.Choices // (H.rowHoles y).Compatible τ}
abbrev ColumnChoices := ∀ x : A.Slot, {τ : B.Choices // (H.columnHoles x).Compatible τ}

def refPair (hf : H.Feasible) : H.RowChoices × H.ColumnChoices :=
  H.splitCompatibleChoices ⟨H.reference hf,H.reference_compatible hf⟩

def rowAction (τ : H.RowChoices) := rowSweep A B (fun y => (τ y).val)
def columnAction (τ : H.ColumnChoices) := columnSweep A B (fun x => (τ x).val)

lemma split_choice_sweep (τ : H.RowChoices × H.ColumnChoices) :
    (concat A B).sweep (H.splitCompatibleChoices.symm τ).val=H.columnAction τ.2*H.rowAction τ.1 := by
  rw [sweep_eq_column_mul_row]
  change columnSweep A B ((choicesSplit A B ((choicesSplit A B).symm _)).2)*
    rowSweep A B ((choicesSplit A B ((choicesSplit A B).symm _)).1)=_
  rw [Equiv.apply_symm_apply]
  rfl

lemma rowAction_marked (hf : H.Feasible) (τ : H.RowChoices) (i : Fin h) :
    H.rowAction τ (H.path i 0)=H.path i (suffixTime A B 0) := by
  let ω : {ω : (concat A B).Choices // H.Compatible ω} :=
    H.splitCompatibleChoices.symm (τ,(H.refPair hf).2)
  have he : H.rowAction τ=rowSweep A B (rowChoices A B ω.val) := by
    change rowSweep A B (fun y => (τ y).val)=rowSweep A B (fun y =>
      ((choicesSplit A B) ((choicesSplit A B).symm _)).1 y)
    rw [Equiv.apply_symm_apply]
  rw [he,rowSweep_eq_boundary]
  exact ω.property i (suffixTime A B 0)

lemma columnAction_marked (hf : H.Feasible) (τ : H.ColumnChoices) (i : Fin h) :
    H.columnAction τ (H.path i (suffixTime A B 0))=H.path i (Fin.last _) := by
  let ω : {ω : (concat A B).Choices // H.Compatible ω} :=
    H.splitCompatibleChoices.symm ((H.refPair hf).1,τ)
  have hs := H.split_choice_sweep ((H.refPair hf).1,τ)
  have hr := H.rowAction_marked hf (H.refPair hf).1 i
  have he := ω.property i (Fin.last _)
  change (concat A B).sweep ω.val (H.path i 0)=_ at he
  rw [hs] at he
  change H.columnAction τ (H.rowAction (H.refPair hf).1 (H.path i 0))=_ at he
  rwa [hr] at he

abbrev JunctionFix := Marked.fix (fun i => H.path i (suffixTime A B 0))

def rowResidual (hf : H.Feasible) (τ : H.RowChoices) : H.JunctionFix :=
  ⟨H.rowAction τ*(H.rowAction (H.refPair hf).1)⁻¹,by
    intro i
    change H.rowAction τ ((H.rowAction (H.refPair hf).1).symm (H.path i (suffixTime A B 0)))=_
    rw [← H.rowAction_marked hf (H.refPair hf).1 i,Equiv.symm_apply_apply,H.rowAction_marked hf τ i]⟩

def columnResidual (hf : H.Feasible) (τ : H.ColumnChoices) : H.JunctionFix :=
  ⟨(H.columnAction (H.refPair hf).2)⁻¹*H.columnAction τ,by
    intro i
    change (H.columnAction (H.refPair hf).2).symm (H.columnAction τ (H.path i (suffixTime A B 0)))=_
    rw [H.columnAction_marked hf τ i,← H.columnAction_marked hf (H.refPair hf).2 i,Equiv.symm_apply_apply]⟩

end Holes
end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid.Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

/- Move the target's reference identification to the actual junction layer. -/
def junctionEquiv (hf : H.Feasible) : H.stabilizer ≃* H.JunctionFix where
  toFun g := ⟨H.rowAction (H.refPair hf).1*g.val*(H.rowAction (H.refPair hf).1)⁻¹,by
    intro i
    change H.rowAction (H.refPair hf).1 (g.val
      ((H.rowAction (H.refPair hf).1).symm (H.path i (suffixTime A B 0))))=_
    rw [← H.rowAction_marked hf (H.refPair hf).1 i,Equiv.symm_apply_apply,g.property i]
    exact H.rowAction_marked hf (H.refPair hf).1 i⟩
  invFun g := ⟨(H.rowAction (H.refPair hf).1)⁻¹*g.val*H.rowAction (H.refPair hf).1,by
    intro i
    change (H.rowAction (H.refPair hf).1).symm
      (g.val (H.rowAction (H.refPair hf).1 (H.path i 0)))=_
    rw [H.rowAction_marked hf (H.refPair hf).1 i,g.property i]
    exact (Equiv.symm_apply_eq _).mpr (H.rowAction_marked hf (H.refPair hf).1 i).symm⟩
  left_inv g := by
    apply Subtype.ext
    change (H.rowAction (H.refPair hf).1)⁻¹*
      (H.rowAction (H.refPair hf).1*g.val*(H.rowAction (H.refPair hf).1)⁻¹)*H.rowAction (H.refPair hf).1=g.val
    group
  right_inv g := by
    apply Subtype.ext
    change H.rowAction (H.refPair hf).1*
      ((H.rowAction (H.refPair hf).1)⁻¹*g.val*H.rowAction (H.refPair hf).1)*(H.rowAction (H.refPair hf).1)⁻¹=g.val
    group
  map_mul' g k := by
    apply Subtype.ext
    change H.rowAction (H.refPair hf).1*(g.val*k.val)*(H.rowAction (H.refPair hf).1)⁻¹=
      (H.rowAction (H.refPair hf).1*g.val*(H.rowAction (H.refPair hf).1)⁻¹)*
      (H.rowAction (H.refPair hf).1*k.val*(H.rowAction (H.refPair hf).1)⁻¹)
    group

instance rowChoicesFintype : Fintype H.RowChoices := by
  letI (y : B.Slot) : Fintype {ω : A.Choices // (H.rowHoles y).Compatible ω} := Subtype.fintype _
  unfold RowChoices
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance columnChoicesFintype : Fintype H.ColumnChoices := by
  letI (x : A.Slot) : Fintype {ω : B.Choices // (H.columnHoles x).Compatible ω} := Subtype.fintype _
  unfold ColumnChoices
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

/- Arbitrary matrix representations may be used: the equality is at the law level. -/
def rowAverage {n : Type*} [Fintype n] [DecidableEq n] (hf : H.Feasible) (z : ℝ)
    (τ : H.JunctionFix →* Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ ω : H.RowChoices, ((∏ y, A.choiceWeight z (ω y).val/(H.rowHoles y).probability z : ℝ) : ℂ) •
    τ (H.rowResidual hf ω)

def columnAverage {n : Type*} [Fintype n] [DecidableEq n] (hf : H.Feasible) (z : ℝ)
    (τ : H.JunctionFix →* Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ ω : H.ColumnChoices, ((∏ x, B.choiceWeight z (ω x).val/(H.columnHoles x).probability z : ℝ) : ℂ) •
    τ (H.columnResidual hf ω)

/- Exact factorization of the faithful conditional matrix average at the
junction. -/

end CoordinateSweeps.Grid.Holes

end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.SignedTensor_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps

namespace SignedTensor

/- p even basis symbols followed by p odd ones, exactly E⊕O in05. -/
abbrev Letter (p : ℕ) := Fin (2*p)
abbrev Word (p l : ℕ) := Fin l → Letter p

def odd {p : ℕ} (a : Letter p) : Prop := p ≤ a.val

/- The sign from reordering the odd factors, with positions ordered as in
ordinary tensor words. There is no choice of orientation hidden here. -/
def koszulExponent {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l) : ℕ :=
  ((Equiv.Perm.finPairsLT l).filter (fun ij =>
    odd (w ij.1) ∧ odd (w ij.2) ∧ σ ij.1 < σ ij.2)).card

def phase {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l) : ℂ :=
  (-1)^koszulExponent σ w

/- The underlying ordinary slot permutation; gh applies h first. -/
def wordPerm {p l : ℕ} (σ : Equiv.Perm (Fin l)) : Equiv.Perm (Word p l) where
  toFun w i := w (σ⁻¹ i)
  invFun w i := w (σ i)
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

/- Matrix of the exact parity-signed action in the tensor word basis. -/
def matrix {p l : ℕ} (σ : Equiv.Perm (Fin l)) : Matrix (Word p l) (Word p l) ℂ :=
  fun u w => if u=wordPerm σ w then phase σ w else 0

lemma phase_star_mul {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l) :
    star (phase σ w)*phase σ w=1 := by
  simp only [phase,star_pow,star_neg,star_one]
  rw [← mul_pow]
  simp

lemma phase_prod {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l) :
    phase σ w = ∏ ij ∈ Equiv.Perm.finPairsLT l,
      (if odd (w ij.1) ∧ odd (w ij.2) ∧ σ ij.1 < σ ij.2 then (-1 : ℂ) else 1) := by
  rw [Finset.prod_ite]
  simp [phase,koszulExponent]

lemma wordPerm_mul {p l : ℕ} (σ τ : Equiv.Perm (Fin l)) :
    wordPerm (p := p) (σ*τ) = wordPerm σ * wordPerm τ := by
  ext w i
  simp [wordPerm]

/- The exact Koszul cocycle, proved from pair inversions, not an action axiom. -/
theorem phase_mul {p l : ℕ} (σ τ : Equiv.Perm (Fin l)) (w : Word p l) :
    phase (σ*τ) w = phase σ (wordPerm τ w) * phase τ w := by
  rw [phase_prod,phase_prod,phase_prod]
  have hreindex :
      (∏ ij ∈ Equiv.Perm.finPairsLT l,
        (if odd (wordPerm τ w ij.1) ∧ odd (wordPerm τ w ij.2) ∧ σ ij.1 < σ ij.2
        then (-1 : ℂ) else 1)) =
      ∏ ij ∈ Equiv.Perm.finPairsLT l,
        (if odd (wordPerm τ w (Equiv.Perm.signBijAux τ ij).1) ∧
          odd (wordPerm τ w (Equiv.Perm.signBijAux τ ij).2) ∧
          σ (Equiv.Perm.signBijAux τ ij).1 < σ (Equiv.Perm.signBijAux τ ij).2
        then (-1 : ℂ) else 1) := by
    symm
    exact Finset.prod_nbij (Equiv.Perm.signBijAux τ)
      Equiv.Perm.signBijAux_mem Equiv.Perm.signBijAux_injOn
      Equiv.Perm.signBijAux_surj (fun _ _ => rfl)
  rw [hreindex,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  rintro ⟨i,j⟩ hij
  have hji : j < i := Equiv.Perm.mem_finPairsLT.mp hij
  have hne : τ j ≠ τ i := τ.injective.ne hji.ne
  have hneσ : σ (τ j) ≠ σ (τ i) := σ.injective.ne hne
  by_cases hi : odd (w i)
  · by_cases hj : odd (w j)
    · by_cases ht : τ j < τ i
      · simp [Equiv.Perm.signBijAux,wordPerm,Equiv.Perm.mul_apply,ht,hi,hj,ht.not_gt]
      · have ht' : τ i < τ j := lt_of_le_of_ne (le_of_not_gt ht) hne.symm
        by_cases hs : σ (τ i) < σ (τ j)
        · simp [Equiv.Perm.signBijAux,wordPerm,Equiv.Perm.mul_apply,ht,ht',hi,hj,hs,hs.not_gt]
        · have hs' : σ (τ j) < σ (τ i) := lt_of_le_of_ne (le_of_not_gt hs) hneσ
          simp [Equiv.Perm.signBijAux,wordPerm,Equiv.Perm.mul_apply,ht,ht',hi,hj,hs,hs']
    · by_cases ht : τ j < τ i <;>
        simp [Equiv.Perm.signBijAux,wordPerm,Equiv.Perm.mul_apply,ht,hi,hj]
  · by_cases ht : τ j < τ i <;>
      simp [Equiv.Perm.signBijAux,wordPerm,Equiv.Perm.mul_apply,ht,hi]

/- Unitarity follows directly, without assuming the Schur-Weyl
or Pieri decomposition. -/

lemma phase_one {p l : ℕ} (w : Word p l) : phase (1 : Equiv.Perm (Fin l)) w=1 := by
  rw [phase_prod]
  apply Finset.prod_eq_one
  intro ij hij
  have hji := Equiv.Perm.mem_finPairsLT.mp hij
  simp [Equiv.Perm.one_apply,hji.not_gt]

theorem matrix_one (p l : ℕ) : matrix (p := p) (1 : Equiv.Perm (Fin l))=1 := by
  ext u w
  simp [matrix,wordPerm,phase_one,Matrix.one_apply]

theorem matrix_mul {p l : ℕ} (σ τ : Equiv.Perm (Fin l)) :
    matrix (p := p) (σ*τ)=matrix σ * matrix τ := by
  ext u w
  simp only [Matrix.mul_apply,matrix]
  rw [Finset.sum_eq_single (wordPerm τ w)]
  · simp only [ite_true,wordPerm_mul,Equiv.Perm.mul_apply,phase_mul]
    split_ifs <;> simp
  · intro v hv hne
    simp [hne]
  · simp

/- Exact signed tensor representation of the symmetric group. -/
def action (p l : ℕ) : Equiv.Perm (Fin l) →* Matrix (Word p l) (Word p l) ℂ where
  toFun := matrix
  map_one' := matrix_one p l
  map_mul' := matrix_mul

/- Ordinary (not graded) tensor power of a one-site density, as in05. -/
def densityPower {p : ℕ} (l : ℕ) (r : Matrix (Letter p) (Letter p) ℂ) :
    Matrix (Word p l) (Word p l) ℂ := fun u w => ∏ i, r (u i) (w i)

def EvenDensity (p : ℕ) := {r : Matrix (Letter p) (Letter p) ℂ //
  r.PosSemidef ∧ Matrix.trace r=1 ∧
    ∀ i j, (odd i ↔ ¬ odd j) → r i j=0}

instance instMeasurableSpaceEvenDensity (p : ℕ) : MeasurableSpace (EvenDensity p) :=
  MeasurableSpace.comap Subtype.val (borel (Matrix (Letter p) (Letter p) ℂ))

def isotypic {p l : ℕ} (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    Matrix (Word p l) (Word p l) ℂ :=
  ((ρ.dimension : ℂ)/(Fintype.card (Equiv.Perm (Fin l)) : ℂ)) •
    ∑ σ, Matrix.trace (ρ.matrix σ⁻¹) • matrix σ

/- Exact signed-density domination05 eq13, expressed for every irreducible
(including absent ones whose projection is zero). The mixture is a genuine
probability measure on the source's even density matrices, not an unproved
positive operator supplied as a hypothesis. -/

end SignedTensor
end CoordinateSweeps

/- A direct counting approach to the polynomial multiplicity bound in05,
without replacing Schur-Weyl or the density inequality by an axiom.
The signed tensor commutant is determined by pair-word histograms. -/
namespace CoordinateSweeps.SignedTensor

lemma phase_ne_zero {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l) : phase σ w ≠ 0 := by
  intro h
  have hh := phase_star_mul σ w
  simp [h] at hh

lemma mul_signed_entry {p l : ℕ} (A : Matrix (Word p l) (Word p l) ℂ)
    (σ : Equiv.Perm (Fin l)) (u w : Word p l) :
    (A*matrix (p := p) σ) u w=A u (wordPerm σ w)*phase σ w := by
  simp only [Matrix.mul_apply,matrix]
  rw [Finset.sum_eq_single (wordPerm σ w)]
  · simp
  · intro v hv hne; simp [hne]
  · simp

lemma signed_mul_entry {p l : ℕ} (A : Matrix (Word p l) (Word p l) ℂ)
    (σ : Equiv.Perm (Fin l)) (u w : Word p l) :
    (matrix (p := p) σ*A) (wordPerm σ u) w=phase σ u*A u w := by
  simp only [Matrix.mul_apply,matrix]
  rw [Finset.sum_eq_single u]
  · simp
  · intro v hv hne
    have hne' : wordPerm σ u ≠ wordPerm σ v :=
      fun hh => hne (((wordPerm σ).injective hh).symm)
    simp [hne']
  · simp

/- The actual signed-action commutant as a linear subspace of matrices. -/
def commutant (p l : ℕ) : Submodule ℂ (Matrix (Word p l) (Word p l) ℂ) where
  carrier := {A | ∀ σ : Equiv.Perm (Fin l), A*matrix σ=matrix σ*A}
  zero_mem' := by simp
  add_mem' hA hB := by intro σ; simp only [add_mul,mul_add,hA σ,hB σ]
  smul_mem' c A hA := by intro σ; simp only [smul_mul_assoc,mul_smul_comm,hA σ]

lemma commutant_zero_transport {p l : ℕ} (A : commutant p l)
    (σ : Equiv.Perm (Fin l)) {u w : Word p l} (h : A.val u w=0) :
    A.val (wordPerm σ u) (wordPerm σ w)=0 := by
  have hh := congrArg (fun B : Matrix (Word p l) (Word p l) ℂ => B (wordPerm σ u) w)
    (A.property σ)
  rw [mul_signed_entry,signed_mul_entry,h,mul_zero] at hh
  exact (mul_eq_zero.mp hh).resolve_right (phase_ne_zero σ w)

abbrev Profile (p l : ℕ) := (Letter p × Letter p) → Fin (l+1)

def profile {p l : ℕ} (u w : Word p l) : Profile p l := fun a =>
  ⟨(Finset.univ.filter (fun i => (u i,w i)=a)).card,
    Nat.lt_succ_iff.mpr (by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin l))
        (fun i => (u i,w i)=a))⟩

abbrev OccurringProfile (p l : ℕ) :=
  {q : Profile p l // q ∈ Set.range (fun uw : Word p l × Word p l => profile uw.1 uw.2)}

def profileRep {p l : ℕ} (q : OccurringProfile p l) : Word p l × Word p l :=
  Classical.choose q.property

def commutantEval (p l : ℕ) : commutant p l →ₗ[ℂ] (OccurringProfile p l → ℂ) where
  toFun A q := A.val (profileRep q).1 (profileRep q).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor

abbrev tensorRepresentation (p l : ℕ) := UnitaryIrrep.matrixRepresentation (action p l)

/- An actual intertwining endomorphism has its coefficient matrix in the
signed commutant. This is not an assumed decomposition of the tensor action. -/
def endomorphismMatrix (p l : ℕ) :
    (tensorRepresentation p l).IntertwiningMap (tensorRepresentation p l) →ₗ[ℂ]
      commutant p l where
  toFun F := ⟨LinearMap.toMatrixAlgEquiv' F.toLinearMap,by
    intro σ
    apply Matrix.toLinAlgEquiv'.injective
    simp only [map_mul,Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
    exact F.isIntertwining' σ⟩
  map_add' F H := by
    apply Subtype.ext
    exact map_add LinearMap.toMatrixAlgEquiv' _ _
  map_smul' c F := by
    apply Subtype.ext
    exact map_smul LinearMap.toMatrixAlgEquiv'.toLinearMap c _

end CoordinateSweeps.SignedTensor

/- Mismatched symbols in a purification
obey a Pauli exclusion rule. This is derived from the literal Koszul action. -/
namespace CoordinateSweeps.SignedTensor

lemma swap01_inversion_iff (n : ℕ) (i j : Fin (n+2)) :
    (j < i ∧ Equiv.swap (0 : Fin (n+2)) 1 i < Equiv.swap 0 1 j) ↔
      i = 1 ∧ j = 0 := by
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all
  omega

lemma phase_swap01 {p n : ℕ} (w : Word p (n+2)) :
    phase (Equiv.swap (0 : Fin (n+2)) 1) w =
      if odd (w 1) ∧ odd (w 0) then (-1 : ℂ) else 1 := by
  have he : ((Equiv.Perm.finPairsLT (n+2)).filter (fun ij =>
      odd (w ij.1) ∧ odd (w ij.2) ∧
        Equiv.swap (0 : Fin (n+2)) 1 ij.1 < Equiv.swap 0 1 ij.2)) =
      if odd (w 1) ∧ odd (w 0) then {⟨1,0⟩} else ∅ := by
    ext ⟨i,j⟩
    simp only [Finset.mem_filter, Equiv.Perm.mem_finPairsLT]
    have hi := swap01_inversion_iff n i j
    split_ifs with hw
    · simp only [Finset.mem_singleton, Sigma.mk.inj_iff, heq_eq_eq]
      constructor
      · rintro ⟨hji,hiw,hjw,hs⟩
        exact hi.mp ⟨hji,hs⟩
      · rintro ⟨rfl,rfl⟩
        exact ⟨by simp, hw.1, hw.2, by simp⟩
    · simp only [Finset.notMem_empty, iff_false]
      rintro ⟨hji,hiw,hjw,hs⟩
      obtain ⟨rfl,rfl⟩ := hi.mp ⟨hji,hs⟩
      exact hw ⟨hiw,hjw⟩
  unfold phase koszulExponent
  rw [he]
  split_ifs <;> simp

lemma wordPerm_swap01_of_equal {p n : ℕ} (w : Word p (n+2)) (hw : w 0 = w 1) :
    wordPerm (Equiv.swap (0 : Fin (n+2)) 1) w = w := by
  ext i
  simp only [wordPerm, Equiv.coe_fn_mk, Equiv.swap_inv, Equiv.swap_apply_def]
  split_ifs <;> simp_all

/- Two repeated, parity-mismatched pair symbols force a zero entry in every
commuting matrix, hence in the canonical purification of an isotypic projector. -/
theorem commutant_entry_zero_adjacent_mismatch {p n : ℕ} (A : commutant p (n+2))
    (u w : Word p (n+2)) (hu : u 0 = u 1) (hw : w 0 = w 1)
    (hm : odd (u 0) ↔ ¬ odd (w 0)) : A.val u w = 0 := by
  let σ := Equiv.swap (0 : Fin (n+2)) 1
  have h := congrArg (fun B : Matrix (Word p (n+2)) (Word p (n+2)) ℂ =>
    B (wordPerm σ u) w) (A.property σ)
  rw [mul_signed_entry, signed_mul_entry,
    wordPerm_swap01_of_equal u hu, wordPerm_swap01_of_equal w hw] at h
  dsimp [σ] at h
  rw [phase_swap01, phase_swap01, ← hu, ← hw] at h
  by_cases ho : odd (u 0)
  · have hw' : ¬ odd (w 0) := hm.mp ho
    simp only [ho, hw', and_self, ↓reduceIte, mul_one, neg_one_mul] at h
    linear_combination (1/2 : ℂ)*h
  · have hw' : odd (w 0) := Classical.byContradiction (fun hh => ho (hm.mpr hh))
    simp only [ho, hw', and_self, ↓reduceIte, one_mul, mul_neg_one] at h
    linear_combination (-1/2 : ℂ)*h

/- An explicit two-point transporter, avoiding any unproved transitivity
principle or choice of ordering of the other positions. -/
lemma exists_perm_pair {X : Type*} [DecidableEq X] (a b c d : X)
    (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : Equiv.Perm X, g a = c ∧ g b = d := by
  let s := Equiv.swap a c
  have hs : s b ≠ c := by
    intro h
    have he : s a = c := by simp [s]
    exact hab (s.injective (he.trans h.symm))
  refine ⟨Equiv.swap (s b) d * s, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply]
    have he : s a = c := by simp [s]
    rw [he, Equiv.swap_apply_of_ne_of_ne hs.symm hcd]
  · simp

/- All repeated parity-mismatched pair symbols are impossible, at arbitrary
positions. Distinct mismatched symbols will therefore account for every
exceptional slot in the postselection argument. -/
theorem commutant_entry_zero_repeated_mismatch {p l : ℕ} (A : commutant p l)
    (u w : Word p l) (i j : Fin l) (hij : i ≠ j) (hu : u i = u j) (hw : w i = w j)
    (hm : odd (u i) ↔ ¬ odd (w i)) : A.val u w = 0 := by
  have hl : 2 ≤ l := by
    have hn : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hi := i.isLt
    have hj := j.isLt
    omega
  obtain ⟨n, rfl⟩ : ∃ n, l = n+2 := ⟨l-2, by omega⟩
  obtain ⟨g,hi,hj⟩ := exists_perm_pair i j (0 : Fin (n+2)) 1 hij (by simp)
  let u' := wordPerm g u
  let w' := wordPerm g w
  have hue (x : Fin (n+2)) : u' (g x) = u x := by simp [u',wordPerm]
  have hwe (x : Fin (n+2)) : w' (g x) = w x := by simp [w',wordPerm]
  have hui : u' 0 = u i := hi ▸ hue i
  have huj : u' 1 = u j := hj ▸ hue j
  have hwi : w' 0 = w i := hi ▸ hwe i
  have hwj : w' 1 = w j := hj ▸ hwe j
  have hz : A.val u' w' = 0 := by
    apply commutant_entry_zero_adjacent_mismatch A u' w'
    · exact hui.trans (hu.trans huj.symm)
    · exact hwi.trans (hw.trans hwj.symm)
    · simpa [hui,hwi] using hm
  have hz' := commutant_zero_transport A g⁻¹ hz
  simpa [u',w',wordPerm] using hz'
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
/- Exceptional slots of a vectorized commuting matrix. -/
def mismatchSlots {p l : ℕ} (u w : Word p l) : Finset (Fin l) :=
  Finset.univ.filter (fun i => odd (u i) ↔ ¬ odd (w i))

/- The exclusion bound needed for even-density postselection. The coarse
constant four rather than two is harmless in the source's absolute Cp² error. -/
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
/- The actual Koszul regrouping phase from (V⊗V̄)^⊗l to
V^⊗l⊗V̄^⊗l. It will cancel, not be dropped, under partial trace. -/
def regroupPhase {p l : ℕ} (u w : Word p l) : ℂ :=
  ∏ ij ∈ Equiv.Perm.finPairsLT l,
    if odd (u ij.1) ∧ odd (w ij.2) then (-1 : ℂ) else 1

end CoordinateSweeps.SignedTensor

end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Tensor_Postselection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.OrdinaryTensor
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

/- Occupancies of single alphabet symbols in an ordinary tensor word. -/
def count (w : I → A) (a : A) : ℕ := Fintype.card {i : I // w i = a}

/- Ordinary tensor permutation, with the manuscript's product convention. -/
def permute (σ : Equiv.Perm I) : Equiv.Perm (I → A) where
  toFun w i := w (σ⁻¹ i)
  invFun w i := w (σ i)
  left_inv w := by ext i; simp
  right_inv w := by ext i; simp

omit [DecidableEq I] in
lemma sum_count (w : I → A) : ∑ a, count w a = Fintype.card I := by
  classical
  simpa only [count, Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv w)

def fiberPermEquiv (w : I → A) :
    {σ : Equiv.Perm I // ∀ i, w (σ i) = w i} ≃ (∀ a : A, Equiv.Perm {i : I // w i = a}) where
  toFun σ a := σ.val.subtypePerm (fun i => by rw [σ.property i])
  invFun τ := ⟨Equiv.ofFiberEquiv τ, Equiv.ofFiberEquiv_map τ⟩
  left_inv σ := by
    apply Subtype.ext
    ext i
    rfl
  right_inv τ := by
    funext a
    apply Equiv.ext
    rintro ⟨i,hi⟩
    apply Subtype.ext
    subst a
    rfl

def transporterEquiv (u w : I → A) (σ : Equiv.Perm I) (hσ : permute σ u = w) :
    {g : Equiv.Perm I // permute g u = w} ≃
      {g : Equiv.Perm I // ∀ i, u (g i) = u i} where
  toFun g := ⟨σ⁻¹*g.val, by
    intro i
    have hg : u (g.val⁻¹ (g.val i)) = w (g.val i) := congrFun g.property (g.val i)
    have hs : u (σ⁻¹ (g.val i)) = w (g.val i) := congrFun hσ (g.val i)
    simpa using hs.trans hg.symm⟩
  invFun g := ⟨σ*g.val, by
    ext i
    change u (g.val⁻¹ (σ⁻¹ i)) = w i
    have hg := g.property (g.val⁻¹ (σ⁻¹ i))
    have hs : u (σ⁻¹ i) = w i := congrFun hσ i
    have hh : u (g.val⁻¹ (σ⁻¹ i)) = u (σ⁻¹ i) := by simpa using hg.symm
    exact hh.trans hs⟩
  left_inv g := Subtype.ext (by simp)
  right_inv g := Subtype.ext (by simp)

omit [Fintype A] [DecidableEq I] in
lemma permute_count (σ : Equiv.Perm I) (w : I → A) : count (permute σ w) = count w := by
  ext a
  apply Fintype.card_congr
  exact
    { toFun := fun i => ⟨σ⁻¹ i.val, i.property⟩
      invFun := fun i => ⟨σ i.val, by simpa [permute] using i.property⟩
      left_inv := fun i => Subtype.ext (by simp)
      right_inv := fun i => Subtype.ext (by simp) }

end CoordinateSweeps.OrdinaryTensor

namespace CoordinateSweeps.OrdinaryTensor

/- A factorial ratio is bounded by the largest factor; used to avoid
any assumed entropy/Stirling estimate in the empirical postselection measure. -/

variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

def orbitFiberEquiv (u : I → A) :
    (Σ w : {w : I → A // count w = count u}, {σ : Equiv.Perm I // permute σ u = w.val}) ≃
      Equiv.Perm I where
  toFun x := x.2.val
  invFun σ := ⟨⟨permute σ u, permute_count σ u⟩,⟨σ,rfl⟩⟩
  left_inv := by
    rintro ⟨⟨w,hw⟩,⟨σ,hσ⟩⟩
    change permute σ u = w at hσ
    subst w
    rfl
  right_inv σ := rfl

abbrev Histogram (I A : Type*) [Fintype I] [Fintype A] [DecidableEq A] :=
  Set.range (count (I := I) (A := A))

instance instFiniteElemForallNatHistogram : Finite (Histogram I A) := Finite.Set.finite_range _
noncomputable instance instFintypeElemForallNatHistogram : Fintype (Histogram I A) := Fintype.ofFinite _

def histogram (w : I → A) : Histogram I A := ⟨count w, w, rfl⟩

def typeWeight (r : A → ℕ) (u : I → A) : ℕ :=
  Fintype.card {w : I → A // count w = count u} * ∏ a, r a ^ count u a

def histogramWeight (r : A → ℕ) (h : Histogram I A) : ℕ :=
  Fintype.card {w : I → A // histogram w = h} * ∏ a, r a ^ h.val a

end CoordinateSweeps.OrdinaryTensor

namespace CoordinateSweeps.OrdinaryTensor
open AddChar
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

/- Finite independent root phases. The modulus is strictly larger than
any occupancy, so it distinguishes every histogram without an analytic limit. -/
abbrev PhaseSpace (I A : Type*) [Fintype I] := A → ZMod (Fintype.card I+1)

def wordPhase (t : PhaseSpace I A) (w : I → A) : ℂ :=
  ∏ a, ZMod.stdAddChar (t a * (count w a : ZMod (Fintype.card I+1)))

end CoordinateSweeps.OrdinaryTensor

namespace CoordinateSweeps.OrdinaryTensor
open AddChar
open scoped ComplexOrder
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

def tensorVector (z : A → ℂ) (w : I → A) : ℂ := ∏ i, z (w i)
def outer {J : Type*} (v : J → ℂ) : Matrix J J ℂ := Matrix.vecMulVec v (star v)

def empiricalVector (h : Histogram I A) (t : PhaseSpace I A) (a : A) : ℂ :=
  (Real.sqrt ((h.val a : ℝ)/Fintype.card I) : ℂ) * ZMod.stdAddChar (t a)

def amplitude (h : Histogram I A) (w : I → A) : ℝ :=
  ∏ i, Real.sqrt ((h.val (w i) : ℝ)/Fintype.card I)

omit [DecidableEq I] in
lemma char_star_mul (t : ZMod (Fintype.card I+1)) :
    ZMod.stdAddChar t * star (ZMod.stdAddChar t) = 1 := by
  rw [Complex.star_def, ← AddChar.map_neg_eq_conj, ← map_add_eq_mul]
  simp

omit [DecidableEq I] in
lemma empiricalVector_square (h : Histogram I A) (t : PhaseSpace I A) (a : A) :
    empiricalVector h t a * star (empiricalVector h t a) =
      (((h.val a : ℝ)/Fintype.card I : ℝ) : ℂ) := by
  unfold empiricalVector
  simp only [star_mul, RCLike.star_def, Complex.conj_ofReal]
  calc
    _ = (Real.sqrt ((h.val a : ℝ)/Fintype.card I) : ℂ)^2 *
        (ZMod.stdAddChar (t a) * star (ZMod.stdAddChar (t a))) := by
      simp only [Complex.star_def]; ring
    _ = _ := by
      rw [char_star_mul, mul_one, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]

omit [DecidableEq I] in
lemma empiricalVector_unit (hn : 0 < Fintype.card I) (h : Histogram I A) (t : PhaseSpace I A) :
    (∑ a, empiricalVector h t a * star (empiricalVector h t a)) = 1 := by
  simp_rw [empiricalVector_square]
  rw [← Complex.ofReal_sum, ← Finset.sum_div]
  obtain ⟨w,hw⟩ := h.property
  rw [← hw, ← Nat.cast_sum, sum_count, div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]
  rfl

def phaseFrame (h : Histogram I A) : Matrix (I → A) (I → A) ℂ :=
  (Fintype.card (PhaseSpace I A) : ℂ)⁻¹ •
    ∑ t : PhaseSpace I A, outer (tensorVector (empiricalVector h t))

end CoordinateSweeps.OrdinaryTensor

namespace CoordinateSweeps.OrdinaryTensor
open scoped ComplexOrder
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

def orbitSize (h : Histogram I A) : ℕ := Fintype.card {w : I → A // histogram w = h}
def representative (h : Histogram I A) : I → A := Classical.choose h.property

def block (h : Histogram I A) : Matrix (I → A) (I → A) ℂ :=
  outer (fun w => if histogram w = h then 1 else 0)

def symProjector : Matrix (I → A) (I → A) ℂ :=
  ∑ h : Histogram I A, (orbitSize h : ℂ)⁻¹ • block h

def histogramAmplitude (h k : Histogram I A) : ℝ := amplitude h (representative k)

end CoordinateSweeps.OrdinaryTensor

namespace CoordinateSweeps.OrdinaryTensor
open scoped ComplexOrder
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

instance instNonemptyElemForallNatHistogram [Nonempty A] : Nonempty (Histogram I A) := ⟨histogram (fun _ => Classical.arbitrary A)⟩

/- Literal finite average of empirical pure product tensors, grouped first
by histogram and then by independent roots. -/
def finiteMixture : Matrix (I → A) (I → A) ℂ :=
  (Fintype.card (Histogram I A) : ℂ)⁻¹ • ∑ h : Histogram I A, phaseFrame h

end CoordinateSweeps.OrdinaryTensor

/- Positive-operator inequalities needed for the actual purification proof
of signed tensor density domination (05:eq13), not standalone main results. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.OrdinaryTensor
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

def rawMixture : Matrix (I → A) (I → A) ℂ :=
  ∑ h : Histogram I A, ∑ t : PhaseSpace I A, outer (tensorVector (empiricalVector h t))
end CoordinateSweeps.OrdinaryTensor
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.SignedTensor_Domination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.SignedTensor
open PositiveTensor

/- Partial-trace invariance of the actual regrouping signs on each fixed
exception sector. No assumption of complex conditional probabilities occurs. -/

abbrev Pair (p : ℕ) := Letter p × Letter p
abbrev MatchedPair (p : ℕ) := {a : Pair p // odd a.1 ↔ odd a.2}

/- Valid pinned exceptional data. Injectivity is essential: it is supplied
by the proved repeated-mismatch cancellation, not imposed on the kernel. -/
structure ExceptionPattern (p l : ℕ) where
  sites : Finset (Fin l)
  pair : sites → Pair p
  mismatch : ∀ i, odd (pair i).1 ↔ ¬ odd (pair i).2
  injective : Function.Injective pair
  deriving Fintype

/- Every nonzero commuting matrix entry has literal valid exceptional data. -/
def entryPattern {p l : ℕ} (A : commutant p l) (u w : Word p l) (h : A.val u w ≠ 0) :
    ExceptionPattern p l where
  sites := mismatchSlots u w
  pair i := (u i.val,w i.val)
  mismatch i := (Finset.mem_filter.mp i.property).2
  injective := by
    intro i j he
    apply Subtype.ext
    by_contra hij
    exact h (commutant_entry_zero_repeated_mismatch A u w i.val j.val hij
      (congrArg Prod.fst he) (congrArg Prod.snd he) (Finset.mem_filter.mp i.property).2)

namespace ExceptionPattern
variable {p l : ℕ}

def encode (F : ExceptionPattern p l) (a : Pair p) : Option (Fin l) :=
  if h : ∃ i : F.sites, F.pair i = a then some (Classical.choose h).val else none

lemma sites_card_le (F : ExceptionPattern p l) : F.sites.card ≤ (2*p)*(2*p) := by
  have hc := Fintype.card_le_of_injective F.pair F.injective
  simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] using hc

/- Slots not occupied by a pinned exceptional symbol. -/
abbrev Free (F : ExceptionPattern p l) := {i : Fin l // i ∉ F.sites}
abbrev FreeWord (F : ExceptionPattern p l) := F.Free → MatchedPair p

def fillPair (F : ExceptionPattern p l) (x : F.FreeWord) (i : Fin l) : Pair p :=
  if hi : i ∈ F.sites then F.pair ⟨i,hi⟩ else (x ⟨i,hi⟩).val

def fill (F : ExceptionPattern p l) (x : F.FreeWord) : Word p l × Word p l :=
  (fun i => (F.fillPair x i).1, fun i => (F.fillPair x i).2)

lemma fillPair_at_free (F : ExceptionPattern p l) (x : F.FreeWord) (i : F.Free) :
    F.fillPair x i.val = (x i).val := by simp [fillPair,i.property]

lemma fill_injective (F : ExceptionPattern p l) : Function.Injective F.fill := by
  intro x y he
  funext i
  apply Subtype.ext
  have hh : F.fillPair x i.val = F.fillPair y i.val :=
    Prod.ext (congrFun (congrArg Prod.fst he) i.val) (congrFun (congrArg Prod.snd he) i.val)
  simpa only [F.fillPair_at_free] using hh

def extendPerm (F : ExceptionPattern p l) (σ : Equiv.Perm F.Free) : Equiv.Perm (Fin l) :=
  Equiv.Perm.ofSubtype σ

def purified (F : ExceptionPattern p l) (A : commutant p l) (x : F.FreeWord) : ℂ :=
  regroupPhase (F.fill x).1 (F.fill x).2 * A.val (F.fill x).1 (F.fill x).2

end ExceptionPattern
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor.ExceptionPattern
open PositiveTensor
variable {p l : ℕ}

def embedding (F : ExceptionPattern p l) : F.FreeWord ↪ (Word p l × Word p l) :=
  ⟨F.fill,F.fill_injective⟩

def component (F : ExceptionPattern p l) (A : commutant p l) (uw : Word p l × Word p l) : ℂ :=
  if uw ∈ Set.range F.fill then A.val uw.1 uw.2 else 0

end CoordinateSweeps.SignedTensor.ExceptionPattern

namespace CoordinateSweeps.SignedTensor.ExceptionPattern
open PositiveTensor
variable {p l : ℕ}
lemma free_card (F : ExceptionPattern p l) : Fintype.card F.Free = l-F.sites.card := by
  simp only [Free,Fintype.card_subtype_compl,Fintype.card_coe,Fintype.card_fin]
lemma free_card_pos (F : ExceptionPattern p l) (hl : (2*p)*(2*p) < l) : 0 < Fintype.card F.Free := by
  rw [F.free_card]
  exact Nat.sub_pos_of_lt (lt_of_le_of_lt F.sites_card_le hl)
end CoordinateSweeps.SignedTensor.ExceptionPattern

namespace CoordinateSweeps.SignedTensor

def pairAmplitude {p : ℕ} (z : MatchedPair p → ℂ) : Matrix (Letter p) (Letter p) ℂ :=
  fun a b => if h : odd a ↔ odd b then z ⟨(a,b),h⟩ else 0

lemma pairAmplitude_unit_trace {p : ℕ} (z : MatchedPair p → ℂ)
    (hz : ∑ a, z a * star (z a) = 1) :
    Matrix.trace (pairAmplitude z * (pairAmplitude z).conjTranspose) = 1 := by
  have hs := Fintype.sum_of_injective
    (Subtype.val : MatchedPair p → Pair p) Subtype.val_injective
    (fun a => z a * star (z a))
    (fun a : Pair p => pairAmplitude z a.1 a.2 * star (pairAmplitude z a.1 a.2))
    (by
      intro a ha
      have hn : ¬ (odd a.1 ↔ odd a.2) := by
        intro h
        exact ha ⟨⟨a,h⟩,rfl⟩
      simp [pairAmplitude,hn])
    (by intro a; simp [pairAmplitude,a.property])
  rw [hz] at hs
  simpa only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type] using hs.symm

lemma pairAmplitude_even {p : ℕ} (z : MatchedPair p → ℂ) (a b : Letter p)
    (hab : odd a ↔ ¬ odd b) :
    (pairAmplitude z * (pairAmplitude z).conjTranspose) a b = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hac : odd a ↔ odd c
  · have hbc : ¬ (odd b ↔ odd c) := by tauto
    simp [Matrix.conjTranspose_apply,pairAmplitude,hbc]
  · simp [Matrix.conjTranspose_apply,pairAmplitude,hac]

/- The real even one-site density obtained by the literal auxiliary partial
trace of a unit matched-pair vector. -/
def pairDensity {p : ℕ} (z : MatchedPair p → ℂ) (hz : ∑ a, z a * star (z a) = 1) : EvenDensity p :=
  ⟨pairAmplitude z * (pairAmplitude z).conjTranspose,
    Matrix.posSemidef_self_mul_conjTranspose _, pairAmplitude_unit_trace z hz,
    pairAmplitude_even z⟩
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
variable {p : ℕ}

def basisDensity (a : Letter p) : Matrix (Letter p) (Letter p) ℂ :=
  Matrix.diagonal (fun b => if b=a then 1 else 0)

def pinAmplitude (a : Pair p) : Matrix (Letter p) (Letter p) ℂ :=
  fun i j => if (i,j)=a then 1 else 0

def keep (s : ℕ) : ℝ := s/(s+1)
def noise (s p : ℕ) : ℝ := 1/((s+1)*(2*p))

lemma keep_nonneg (s : ℕ) : 0 ≤ keep s := div_nonneg (Nat.cast_nonneg _) (by positivity)
lemma noise_nonneg (s p : ℕ) : 0 ≤ noise s p := by unfold noise; positivity
lemma keep_add_noise (s p : ℕ) (hp : 0 < p) : keep s + noise s p*(2*p) = 1 := by
  have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hs : (s : ℝ)+1 ≠ 0 := by positivity
  unfold keep noise
  field_simp

def depolarized (s : ℕ) (r : EvenDensity p) : Matrix (Letter p) (Letter p) ℂ :=
  (keep s : ℂ) • r.val + (noise s p : ℂ) • 1

lemma depolarized_posSemidef (s : ℕ) (r : EvenDensity p) : (depolarized s r).PosSemidef := by
  exact (r.property.1.smul (by exact_mod_cast keep_nonneg s)).add
    (Matrix.PosSemidef.one.smul (by exact_mod_cast noise_nonneg s p))

lemma depolarized_trace (s : ℕ) (hp : 0 < p) (r : EvenDensity p) : Matrix.trace (depolarized s r) = 1 := by
  rw [depolarized,Matrix.trace_add,Matrix.trace_smul,Matrix.trace_smul,r.property.2.1]
  simp only [Matrix.trace_one,Fintype.card_fin,smul_eq_mul,mul_one]
  exact_mod_cast keep_add_noise s p hp

lemma depolarized_even (s : ℕ) (r : EvenDensity p) (i j : Letter p)
    (hij : odd i ↔ ¬ odd j) : depolarized s r i j = 0 := by
  have hne : i ≠ j := by intro h; subst j; tauto
  simp [depolarized,Matrix.smul_apply,r.property.2.2 i j hij,hne]

def depolarizedDensity (s : ℕ) (hp : 0 < p) (r : EvenDensity p) : EvenDensity p :=
  ⟨depolarized s r,depolarized_posSemidef s r,depolarized_trace s hp r,depolarized_even s r⟩

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open PositiveTensor
variable {p l : ℕ}

def pinnedDensity (E : Finset (Fin l)) (a : E → Letter p) (r : EvenDensity p) :
    Matrix (Word p l) (Word p l) ℂ :=
  productMatrix (fun i => if hi : i ∈ E then basisDensity (a ⟨i,hi⟩) else r.val)

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor.ExceptionPattern
open PositiveTensor
variable {p l : ℕ}

def siteAmplitude (F : ExceptionPattern p l) (z : MatchedPair p → ℂ) (i : Fin l) :
    Matrix (Letter p) (Letter p) ℂ :=
  if hi : i ∈ F.sites then pinAmplitude (F.pair ⟨i,hi⟩) else pairAmplitude z

def pairProduct (F : ExceptionPattern p l) (z : MatchedPair p → ℂ)
    (q : Word p l × Word p l) : ℂ := ∏ i, F.siteAmplitude z i (q.1 i) (q.2 i)

end CoordinateSweeps.SignedTensor.ExceptionPattern

namespace CoordinateSweeps.SignedTensor.ExceptionPattern
open PositiveTensor
variable {p l : ℕ}

abbrev Data (F : ExceptionPattern p l) :=
  OrdinaryTensor.Histogram F.Free (MatchedPair p) × OrdinaryTensor.PhaseSpace F.Free (MatchedPair p)

def dataDensity (F : ExceptionPattern p l) (hn : 0 < Fintype.card F.Free) (d : F.Data) : EvenDensity p :=
  pairDensity (OrdinaryTensor.empiricalVector d.1 d.2) (OrdinaryTensor.empiricalVector_unit hn d.1 d.2)

def dataPoint (F : ExceptionPattern p l) (s : ℕ) (hp : 0 < p)
    (hn : 0 < Fintype.card F.Free) (d : F.Data) : EvenDensity p :=
  depolarizedDensity s hp (F.dataDensity hn d)

def rawPinned (F : ExceptionPattern p l) (hn : 0 < Fintype.card F.Free) :
    Matrix (Word p l) (Word p l) ℂ :=
  ∑ d : F.Data, pinnedDensity F.sites (fun i => (F.pair i).1) (F.dataDensity hn d)

def rawDensity (F : ExceptionPattern p l) (s : ℕ) (hp : 0 < p) (hn : 0 < Fintype.card F.Free) :
    Matrix (Word p l) (Word p l) ℂ :=
  ∑ d : F.Data, densityPower l (F.dataPoint s hp hn d).val

end CoordinateSweeps.SignedTensor.ExceptionPattern

namespace CoordinateSweeps.SignedTensor
open PositiveTensor
variable {p l : ℕ}

namespace ExceptionPattern

def empty (p l : ℕ) : ExceptionPattern p l where
  sites := ∅
  pair i := False.elim (Finset.notMem_empty i.val i.property)
  mismatch i := False.elim (Finset.notMem_empty i.val i.property)
  injective i := False.elim (Finset.notMem_empty i.val i.property)

instance instNonempty : Nonempty (ExceptionPattern p l) := ⟨empty p l⟩

end ExceptionPattern

abbrev DensityProfile (p l : ℕ) := Σ F : ExceptionPattern p l, F.Data

def profilePoint (s p l : ℕ) (hp : 0 < p) (hl : (2*p)*(2*p) < l)
    (d : DensityProfile p l) : EvenDensity p := d.1.dataPoint s hp (d.1.free_card_pos hl) d.2

def rawProfileDensity (s p l : ℕ) (hp : 0 < p) (hl : (2*p)*(2*p) < l) :
    Matrix (Word p l) (Word p l) ℂ :=
  ∑ d : DensityProfile p l, densityPower l (profilePoint s p l hp hl d).val

end CoordinateSweeps.SignedTensor

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

namespace CoordinateSweeps.SignedTensor
open PositiveTensor MeasureTheory

instance instMeasurableSingletonClassEvenDensity (p : ℕ) : MeasurableSingletonClass (EvenDensity p) := by
  let : MeasurableSpace (Matrix (Letter p) (Letter p) ℂ) := borel _
  let : BorelSpace (Matrix (Letter p) (Letter p) ℂ) := ⟨rfl⟩
  change MeasurableSingletonClass {r : Matrix (Letter p) (Letter p) ℂ // _}
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def uniformDensity (p : ℕ) (hp : 0 < p) : EvenDensity p :=
  ⟨((2*p : ℕ) : ℂ)⁻¹ • 1, Matrix.PosSemidef.one.smul (by positivity), by
    rw [Matrix.trace_smul,Matrix.trace_one]
    have hc : ((2*p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa only [Letter,Fintype.card_fin,smul_eq_mul] using inv_mul_cancel₀ hc,
    by
      intro i j hij
      have hne : i ≠ j := by intro he; subst j; tauto
      simp [hne]⟩

end CoordinateSweeps.SignedTensor

end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.SignedTensor_Blocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.OrderedBlocks
variable {r : ℕ} (n : Fin r → ℕ)

def offset (i : Fin r) : ℕ := ∑ j ∈ Finset.Iio i, n j

lemma offset_next_le (i j : Fin r) (hij : i < j) : offset n i+n i ≤ offset n j := by
  have he : Finset.Iic i=insert i (Finset.Iio i) := by ext x; simp [le_iff_lt_or_eq,or_comm]
  have hh : ∑ k ∈ Finset.Iic i, n k ≤ ∑ k ∈ Finset.Iio j, n k :=
    Finset.sum_le_sum_of_subset (fun k hk => Finset.mem_Iio.mpr (lt_of_le_of_lt (Finset.mem_Iic.mp hk) hij))
  rw [he,Finset.sum_insert (by simp)] at hh
  simpa only [offset,add_comm] using hh

lemma offset_next_le_total (i : Fin r) : offset n i+n i ≤ ∑ j, n j := by
  have he : Finset.Iic i=insert i (Finset.Iio i) := by ext x; simp [le_iff_lt_or_eq,or_comm]
  have hh : ∑ k ∈ Finset.Iic i, n k ≤ ∑ k, n k := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [he,Finset.sum_insert (by simp)] at hh
  simpa only [offset,add_comm] using hh

def encode (x : (i : Fin r) × Fin (n i)) : Fin (∑ i, n i) :=
  ⟨offset n x.1+x.2,lt_of_lt_of_le (Nat.add_lt_add_left x.2.isLt _) (offset_next_le_total n x.1)⟩

lemma encode_lt_of_block {i j : Fin r} (hij : i < j) (a : Fin (n i)) (b : Fin (n j)) :
    encode n ⟨i,a⟩ < encode n ⟨j,b⟩ := by
  change offset n i+a.val < offset n j+b.val
  have hh := offset_next_le n i j hij
  have ha := a.isLt
  omega

lemma encode_injective : Function.Injective (encode n) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have hi : i=j := by
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim ((ne_of_lt (encode_lt_of_block n hij a b)) h)
    · exact hij
    · exact False.elim ((ne_of_lt (encode_lt_of_block n hij b a)) h.symm)
  subst j
  have hab : a=b := Fin.ext (by have hh := congrArg Fin.val h; dsimp [encode] at hh; omega)
  subst b
  rfl

/- Explicit contiguous coordinate chart, including zero-length blocks. -/
def positions : ((i : Fin r) × Fin (n i)) ≃ Fin (∑ i, n i) :=
  Equiv.ofBijective (encode n) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨encode_injective n,by simp [Fintype.card_sigma]⟩)

def perm (σ : ∀ i, Equiv.Perm (Fin (n i))) : Equiv.Perm (Fin (∑ i, n i)) :=
  (positions n).permCongr (Equiv.sigmaCongrRight σ)

@[simp] lemma perm_apply (σ : ∀ i, Equiv.Perm (Fin (n i))) (i : Fin r) (j : Fin (n i)) :
    perm n σ (positions n ⟨i,j⟩)=positions n ⟨i,σ i j⟩ := by
  simp [perm,Equiv.permCongr_apply]

def permHom : (∀ i, Equiv.Perm (Fin (n i))) →* Equiv.Perm (Fin (∑ i, n i)) where
  toFun := perm n
  map_one' := by
    apply Equiv.ext; intro x
    obtain ⟨⟨i,j⟩,rfl⟩ := (positions n).surjective x
    simp
  map_mul' σ τ := by
    apply Equiv.ext; intro x
    obtain ⟨⟨i,j⟩,rfl⟩ := (positions n).surjective x
    simp

end CoordinateSweeps.OrderedBlocks

namespace CoordinateSweeps.SignedTensor
open OrderedBlocks
variable {p r : ℕ} (n : Fin r → ℕ)

def groupWord (p : ℕ) : Word p (∑ i, n i) ≃ (∀ i, Word p (n i)) where
  toFun w i j := w (positions n ⟨i,j⟩)
  invFun w x := w ((positions n).symm x).1 ((positions n).symm x).2
  left_inv w := by funext x; simp
  right_inv w := by
    funext i j
    change (fun x : (i : Fin r) × Fin (n i) => w x.1 x.2) ((positions n).symm (positions n ⟨i,j⟩)) = _
    rw [Equiv.symm_apply_apply]

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open OrderedBlocks UnitaryIrrep
variable {p r : ℕ} (n : Fin r → ℕ)

/- The subgroup operator is an actual group-algebra average on the full set
of slots, not an operator posited to factor. -/
def groupedAverage {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (w : ∀ i, Ω i → ℂ) (g : ∀ i, Ω i → Equiv.Perm (Fin (n i))) :
    Matrix (Word p (∑ i, n i)) (Word p (∑ i, n i)) ℂ :=
  averageMatrix (action p (∑ i, n i)) (fun ω : ∀ i, Ω i => ∏ i, w i (ω i))
    (fun ω => perm n (fun i => g i (ω i)))

def groupedProjector (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) :
    Matrix (Word p (∑ i, n i)) (Word p (∑ i, n i)) ℂ :=
  groupedAverage n (fun i => (ρ i).coefficient) (fun _ => id)

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
variable {p : ℕ}

def IsEven (A : Matrix (Letter p) (Letter p) ℂ) : Prop :=
  ∀ i j, (odd i ↔ ¬ odd j) → A i j=0

def grading (p : ℕ) : Matrix (Letter p) (Letter p) ℂ :=
  Matrix.diagonal (fun i => if odd i then 1 else 0)

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open OrderedBlocks
variable {p r : ℕ} (n : Fin r → ℕ)

def groupedSite (a : Fin r → EvenDensity p) (k : Fin (∑ i, n i)) : EvenDensity p :=
  a ((positions n).symm k).1

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open OrderedBlocks UnitaryIrrep
variable {p r l : ℕ} (n : Fin r → ℕ)

def lengthMatrix {a b : ℕ} (h : a=b) (M : Matrix (Word p a) (Word p a) ℂ) :
    Matrix (Word p b) (Word p b) ℂ := h ▸ M

def ambientProjector (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) : Matrix (Word p l) (Word p l) ℂ :=
  matrix σ*lengthMatrix h (groupedProjector n ρ)*(matrix σ).conjTranspose

def ambientProjectorAlgebra (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) : MonoidAlgebra ℂ (Equiv.Perm (Fin l)) :=
  averageAlgebra (fun ω : ∀ i, Equiv.Perm (Fin (n i)) => ∏ i, (ρ i).coefficient (ω i))
    (fun ω => σ*(Equiv.permCongr (finCongr h) (perm n ω))*σ⁻¹)

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open OrderedBlocks UnitaryIrrep
variable {p r l : ℕ} (n : Fin r → ℕ)

def ambientAverage (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (w : ∀ i, Ω i → ℂ) (g : ∀ i, Ω i → Equiv.Perm (Fin (n i))) :
    Matrix (Word p l) (Word p l) ℂ :=
  averageMatrix (action p l) (fun ω : ∀ i, Ω i => ∏ i, w i (ω i))
    (fun ω => σ*Equiv.permCongr (finCongr h) (perm n (fun i => g i (ω i)))*σ⁻¹)

end CoordinateSweeps.SignedTensor

/-!
All definitions are finite and use ordinary probability and trace normalizations.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.FiberBlocks
open OrderedBlocks
variable {L : Type*} [Fintype L] {r : ℕ} (f : L → Fin r)

def size (i : Fin r) : ℕ := Fintype.card {x : L // f x=i}
def cards (i : Fin r) : Fin (size f i) ≃ {x : L // f x=i} := (Fintype.equivFin _).symm

/- Contiguous finite label fibers give a genuine ordered slot chart. -/
def slots : Fin (∑ i, size f i) ≃ L :=
  (positions (size f)).symm.trans
    ((Equiv.sigmaCongrRight (cards f)).trans (Equiv.sigmaFiberEquiv f))

lemma total : ∑ i, size f i=Fintype.card L := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (slots f)

def chart : Fin (Fintype.card L) ≃ L :=
  (finCongr (total f).symm).trans (slots f)

/- Permutation changing the contiguous fiber chart to any given ambient chart. -/
def regroup (e : Fin (Fintype.card L) ≃ L) : Equiv.Perm (Fin (Fintype.card L)) :=
  (chart f).trans e.symm

end CoordinateSweeps.FiberBlocks

namespace CoordinateSweeps.FiberBlocks
open OrderedBlocks
variable {L : Type*} [Fintype L] {r : ℕ} (f : L → Fin r)

def action : (∀ i, Equiv.Perm (Fin (size f i))) →* Equiv.Perm L :=
  (slots f).permCongrHom.toMonoidHom.comp (permHom (size f))

def restrict (σ : Equiv.Perm L) (hσ : ∀ x, f (σ x)=f x) (i : Fin r) : Equiv.Perm (Fin (size f i)) :=
  Equiv.permCongr (cards f i).symm (Equiv.subtypeEquiv σ (by
    intro x
    change f x=i ↔ f (σ x)=i
    rw [hσ x]))

end CoordinateSweeps.FiberBlocks
namespace CoordinateSweeps.SignedTensor
variable {p r : ℕ} {L : Type*} [Fintype L] (f : L → Fin r)

def fiberProjector (e : Fin (Fintype.card L) ≃ L)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size f i)))) :=
  ambientProjector (p := p) (FiberBlocks.size f) (FiberBlocks.total f) (FiberBlocks.regroup f e) ρ

def fiberProjectorAlgebra (e : Fin (Fintype.card L) ≃ L)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size f i)))) :=
  ambientProjectorAlgebra (FiberBlocks.size f) (FiberBlocks.total f) (FiberBlocks.regroup f e) ρ

end CoordinateSweeps.SignedTensor
end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Decomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps

namespace Grid.Holes
variable {G : Grid} {h : ℕ} (H : G.Holes h)

def residualWithReference (ω0 : {ω : G.Choices // H.Compatible ω})
    (ω : {ω : G.Choices // H.Compatible ω}) : H.stabilizer :=
  ⟨(G.sweep ω0.val)⁻¹*G.sweep ω.val,by
    intro i
    change (G.sweep ω0.val).symm (G.sweep ω.val (H.path i 0))=_
    apply (Equiv.symm_apply_eq _).mpr
    exact (ω.property i (Fin.last _)).trans (ω0.property i (Fin.last _)).symm⟩

def averageWithReference (ω0 : {ω : G.Choices // H.Compatible ω}) (z : ℝ)
    (ρ : UnitaryIrrep H.stabilizer) : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ :=
  ∑ ω : {ω : G.Choices // H.Compatible ω}, ((G.choiceWeight z ω.val/H.probability z : ℝ) : ℂ) •
    ρ.matrix (H.residualWithReference ω0 ω)

/- Arbitrary feasible reference choices preserve the literal, unnormalized moment. -/

end Grid.Holes

end CoordinateSweeps

namespace CoordinateSweeps.Grid.Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)
abbrev JunctionFree := H.FreeAt (suffixTime A B 0)
def rowLabel (x : H.JunctionFree) : B.Slot := (splitSlots A B x.val).2
def columnLabel (x : H.JunctionFree) : A.Slot := (splitSlots A B x.val).1

lemma junctionTime : prefixTime A B (Fin.last A.b)=suffixTime A B 0 := by apply Fin.ext; simp [prefixTime,suffixTime]

/- The actual free row at the split layer is the child's terminal free set. -/
def freeRow (y : B.Slot) : {x : H.JunctionFree // H.rowLabel x=y} ≃
    (H.rowHoles y).FreeAt (Fin.last A.b) where
  toFun x := ⟨(splitSlots A B x.val.val).1,by
    intro i hi
    apply x.val.property (H.rowCards y i).val
    apply (splitSlots A B).injective
    apply Prod.ext
    · simpa only [rowHoles,junctionTime] using hi
    · change H.rowLabel x.val=_
      rw [x.property]
      exact ((H.rowCards y i).property).symm.trans (H.row_constant _ (Fin.last A.b)).symm⟩
  invFun x := ⟨⟨(splitSlots A B).symm (x.val,y),by
    intro i hi
    have hh := congrArg (splitSlots A B) hi
    simp only [Equiv.apply_symm_apply] at hh
    have hy : H.rowOf i=y := (H.row_constant i (Fin.last A.b)).symm.trans (congrArg Prod.snd hh).symm
    let j := (H.rowCards y).symm ⟨i,hy⟩
    have hj : (H.rowCards y j).val=i := congrArg Subtype.val ((H.rowCards y).apply_symm_apply ⟨i,hy⟩)
    apply x.property j
    change x.val=(splitSlots A B (H.path (H.rowCards y j).val (prefixTime A B (Fin.last A.b)))).1
    rw [hj,junctionTime]
    exact congrArg Prod.fst hh⟩,by simp [rowLabel]⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply (splitSlots A B).injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext rfl x.property.symm
  right_inv x := by apply Subtype.ext; simp

/- The actual free column at the split layer is the child's initial free set. -/
def freeColumn (x : A.Slot) : {y : H.JunctionFree // H.columnLabel y=x} ≃
    (H.columnHoles x).FreeAt 0 where
  toFun y := ⟨(splitSlots A B y.val.val).2,by
    intro i hi
    apply y.val.property (H.columnCards x i).val
    apply (splitSlots A B).injective
    apply Prod.ext
    · change H.columnLabel y.val=_
      exact y.property.trans (H.columnCards x i).property.symm
    · exact hi⟩
  invFun y := ⟨⟨(splitSlots A B).symm (x,y.val),by
    intro i hi
    have hh := congrArg (splitSlots A B) hi
    simp only [Equiv.apply_symm_apply] at hh
    have hx : H.columnOf i=x := (congrArg Prod.fst hh).symm
    let j := (H.columnCards x).symm ⟨i,hx⟩
    have hj : (H.columnCards x j).val=i := congrArg Subtype.val ((H.columnCards x).apply_symm_apply ⟨i,hx⟩)
    apply y.property j
    change y.val=(splitSlots A B (H.path (H.columnCards x j).val (suffixTime A B 0))).2
    rw [hj]
    exact congrArg Prod.snd hh⟩,by simp [columnLabel]⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    apply (splitSlots A B).injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext y.property.symm rfl
  right_inv y := by apply Subtype.ext; simp

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid
lemma rowSweep_inv_apply (A B : Grid) (ω : B.Slot → A.Choices) (x : (concat A B).Slot) :
    splitSlots A B ((rowSweep A B ω)⁻¹ x)=
      ((A.sweep (ω (splitSlots A B x).2))⁻¹ (splitSlots A B x).1,(splitSlots A B x).2) := by
  change splitSlots A B ((splitSlots A B).symm
    ((A.sweep (ω (splitSlots A B x).2)).symm (splitSlots A B x).1,(splitSlots A B x).2))=_
  rw [Equiv.apply_symm_apply]
  rfl
lemma columnSweep_inv_apply (A B : Grid) (ω : A.Slot → B.Choices) (x : (concat A B).Slot) :
    splitSlots A B ((columnSweep A B ω)⁻¹ x)=
      ((splitSlots A B x).1,(B.sweep (ω (splitSlots A B x).1))⁻¹ (splitSlots A B x).2) := by
  change splitSlots A B ((splitSlots A B).symm
    ((splitSlots A B x).1,(B.sweep (ω (splitSlots A B x).1)).symm (splitSlots A B x).2))=_
  rw [Equiv.apply_symm_apply]
  rfl
end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h : ℕ} (J : G.Holes h)

def outputStabilizerEquiv (ω₀ : {ω : G.Choices // J.Compatible ω}) :
    J.stabilizer ≃* Equiv.Perm (J.FreeAt (Fin.last G.b)) :=
  J.stabilizerFreeEquiv.trans (J.freeBoundary ω₀ (Fin.last _)).permCongrHom

variable {A B : Grid} (H : (concat A B).Holes h)

def junctionFreeEquiv : H.JunctionFix ≃* Equiv.Perm H.JunctionFree :=
  Marked.freePermEquiv (fun i => H.path i (suffixTime A B 0))

lemma rowResidual_split (hf : H.Feasible) (ω : H.RowChoices) (x : (concat A B).Slot) :
    splitSlots A B ((H.rowResidual hf ω).val x)=
      (A.sweep (ω (splitSlots A B x).2).val
        ((A.sweep ((H.refPair hf).1 (splitSlots A B x).2).val)⁻¹ (splitSlots A B x).1),
       (splitSlots A B x).2) := by
  change splitSlots A B (H.rowAction ω ((H.rowAction (H.refPair hf).1)⁻¹ x))=_
  rw [rowAction,rowSweep_apply]
  rw [rowAction,rowSweep_inv_apply]

lemma columnResidual_split (hf : H.Feasible) (ω : H.ColumnChoices) (x : (concat A B).Slot) :
    splitSlots A B ((H.columnResidual hf ω).val x)=
      ((splitSlots A B x).1,(B.sweep ((H.refPair hf).2 (splitSlots A B x).1).val)⁻¹
        (B.sweep (ω (splitSlots A B x).1).val (splitSlots A B x).2)) := by
  change splitSlots A B ((H.columnAction (H.refPair hf).2)⁻¹ (H.columnAction ω x))=_
  rw [columnAction,columnSweep_inv_apply,columnAction,columnSweep_apply]

lemma rowResidual_label (hf : H.Feasible) (ω : H.RowChoices) (x : H.JunctionFree) :
    H.rowLabel (H.junctionFreeEquiv (H.rowResidual hf ω) x)=H.rowLabel x := by
  have hh := congrArg Prod.snd (H.rowResidual_split hf ω x.val)
  exact hh
lemma columnResidual_label (hf : H.Feasible) (ω : H.ColumnChoices) (x : H.JunctionFree) :
    H.columnLabel (H.junctionFreeEquiv (H.columnResidual hf ω) x)=H.columnLabel x := by
  have hh := congrArg Prod.fst (H.columnResidual_split hf ω x.val)
  exact hh

/- Literal row-fiber permutation and the child's compatible residual agree in
its output frame. -/
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open FiberBlocks
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)
def rowIndex (x : H.JunctionFree) : Fin (Fintype.card B.Slot) := Fintype.equivFin B.Slot (H.rowLabel x)
def columnIndex (x : H.JunctionFree) : Fin (Fintype.card A.Slot) := Fintype.equivFin A.Slot (H.columnLabel x)
def rowSite (_ : (concat A B).Holes h) (i : Fin (Fintype.card B.Slot)) : B.Slot := (Fintype.equivFin B.Slot).symm i
def columnSite (_ : (concat A B).Holes h) (i : Fin (Fintype.card A.Slot)) : A.Slot := (Fintype.equivFin A.Slot).symm i

def rowLocalChart (i : Fin (Fintype.card B.Slot)) : Fin (FiberBlocks.size H.rowIndex i) ≃
    (H.rowHoles (H.rowSite i)).FreeAt (Fin.last A.b) :=
  (cards H.rowIndex i).trans ((Equiv.subtypeEquivRight (fun x => by
    exact (Fintype.equivFin B.Slot).eq_symm_apply.symm)).trans (H.freeRow (H.rowSite i)))
def columnLocalChart (i : Fin (Fintype.card A.Slot)) : Fin (FiberBlocks.size H.columnIndex i) ≃
    (H.columnHoles (H.columnSite i)).FreeAt 0 :=
  (cards H.columnIndex i).trans ((Equiv.subtypeEquivRight (fun x => by
    exact (Fintype.equivFin A.Slot).eq_symm_apply.symm)).trans (H.freeColumn (H.columnSite i)))

def rowChildEquiv (hf : H.Feasible) (i : Fin (Fintype.card B.Slot)) :
    (H.rowHoles (H.rowSite i)).stabilizer ≃* Equiv.Perm (Fin (FiberBlocks.size H.rowIndex i)) :=
  ((H.rowHoles (H.rowSite i)).outputStabilizerEquiv ((H.refPair hf).1 (H.rowSite i))).trans
    (H.rowLocalChart i).symm.permCongrHom

def columnChildEquiv (i : Fin (Fintype.card A.Slot)) :
    (H.columnHoles (H.columnSite i)).stabilizer ≃* Equiv.Perm (Fin (FiberBlocks.size H.columnIndex i)) :=
  (H.columnHoles (H.columnSite i)).stabilizerFreeEquiv.trans (H.columnLocalChart i).symm.permCongrHom

lemma rowResidual_index (hf : H.Feasible) (ω : H.RowChoices) (x : H.JunctionFree) :
    H.rowIndex (H.junctionFreeEquiv (H.rowResidual hf ω) x)=H.rowIndex x :=
  congrArg (Fintype.equivFin B.Slot) (H.rowResidual_label hf ω x)
lemma columnResidual_index (hf : H.Feasible) (ω : H.ColumnChoices) (x : H.JunctionFree) :
    H.columnIndex (H.junctionFreeEquiv (H.columnResidual hf ω) x)=H.columnIndex x :=
  congrArg (Fintype.equivFin A.Slot) (H.columnResidual_label hf ω x)

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open FiberBlocks SignedTensor UnitaryIrrep
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

abbrev RowLocalChoices (i : Fin (Fintype.card B.Slot)) :=
  {ω : A.Choices // (H.rowHoles (H.rowSite i)).Compatible ω}
abbrev ColumnLocalChoices (i : Fin (Fintype.card A.Slot)) :=
  {ω : B.Choices // (H.columnHoles (H.columnSite i)).Compatible ω}
instance instFintypeRowLocalChoices (i : Fin (Fintype.card B.Slot)) : Fintype (H.RowLocalChoices i) := Subtype.fintype _
instance instFintypeColumnLocalChoices (i : Fin (Fintype.card A.Slot)) : Fintype (H.ColumnLocalChoices i) := Subtype.fintype _

def rowChoiceFinEquiv : H.RowChoices ≃ (∀ i, H.RowLocalChoices i) :=
  (Equiv.piCongrLeft (fun y => {ω : A.Choices // (H.rowHoles y).Compatible ω})
    (Fintype.equivFin B.Slot).symm).symm
def columnChoiceFinEquiv : H.ColumnChoices ≃ (∀ i, H.ColumnLocalChoices i) :=
  (Equiv.piCongrLeft (fun x => {ω : B.Choices // (H.columnHoles x).Compatible ω})
    (Fintype.equivFin A.Slot).symm).symm

def rowLocalWeight (z : ℝ) (i : Fin (Fintype.card B.Slot)) (ω : H.RowLocalChoices i) : ℂ :=
  ((A.choiceWeight z ω.val/(H.rowHoles (H.rowSite i)).probability z : ℝ) : ℂ)
def columnLocalWeight (z : ℝ) (i : Fin (Fintype.card A.Slot)) (ω : H.ColumnLocalChoices i) : ℂ :=
  ((B.choiceWeight z ω.val/(H.columnHoles (H.columnSite i)).probability z : ℝ) : ℂ)
def rowLocalPerm (hf : H.Feasible) (i : Fin (Fintype.card B.Slot)) (ω : H.RowLocalChoices i) :=
  H.rowChildEquiv hf i ((H.rowHoles (H.rowSite i)).residualWithReference ((H.refPair hf).1 (H.rowSite i)) ω)
def columnLocalPerm (hf : H.Feasible) (i : Fin (Fintype.card A.Slot)) (ω : H.ColumnLocalChoices i) :=
  H.columnChildEquiv i ((H.columnHoles (H.columnSite i)).residualWithReference ((H.refPair hf).2 (H.columnSite i)) ω)

def junctionTensorAction (p : ℕ) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree) :
    H.JunctionFix →* Matrix (Word p (Fintype.card H.JunctionFree)) (Word p (Fintype.card H.JunctionFree)) ℂ :=
  (SignedTensor.action p _).comp (e.symm.permCongrHom.toMonoidHom.comp H.junctionFreeEquiv.toMonoidHom)

end CoordinateSweeps.Grid.Holes

end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Matrix_Holder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
/- Required analytic interpolation for the matrix trace Hölder step06 (23).
A bounded holomorphic function on a tube over a box is bounded on the tube
over the convex hull of its bounded vertices. No Schatten assertion assumed. -/
noncomputable section
open Set Complex
open scoped BigOperators Topology
namespace CoordinateSweeps.TraceHolder

variable {ι : Type*} [Fintype ι]

def inBox (M : ℝ) (x : ι → ℝ) : Prop := ∀ i, 0 ≤ x i ∧ x i ≤ M

def tubeUnit (f : (ι → ℂ) → ℂ) (x : ι → ℝ) : Prop :=
  ∀ z : ι → ℂ, (∀ i, (z i).re=x i) → ‖f z‖ ≤ 1

end CoordinateSweeps.TraceHolder

open scoped Matrix.Norms.L2Operator
namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n]

def positivePower (x : ℝ) (z : ℂ) : ℂ :=
  if x=0 then 0 else Complex.exp ((Real.log x : ℂ)*z)

def traceFamily {m : ℕ} (U V : Fin m → Matrix n n ℂ) (dval : Fin m → n → ℝ)
    (z : Fin m → ℂ) : ℂ :=
  Matrix.trace ((List.ofFn (fun j => U j*Matrix.diagonal (fun i => positivePower (dval j i) (z j))*V j)).prod)

end CoordinateSweeps.TraceHolder

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev gramHermitian (A : Matrix n n ℂ) := Matrix.isHermitian_conjTranspose_mul_self A

def singular (A : Matrix n n ℂ) (i : n) : ℝ := Real.sqrt ((gramHermitian A).eigenvalues i)

def rightBasis (A : Matrix n n ℂ) : Matrix.unitaryGroup n ℂ :=
  (gramHermitian A).eigenvectorUnitary

def rawPolar (A : Matrix n n ℂ) : Matrix n n ℂ :=
  A*(rightBasis A : Matrix n n ℂ)

def leftFrame (A : Matrix n n ℂ) : Matrix n n ℂ :=
  rawPolar A*Matrix.diagonal (fun i => (((singular A i)⁻¹ : ℝ) : ℂ))

end CoordinateSweeps.TraceHolder

namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n]

def singularMass (m : ℕ) (A : Matrix n n ℂ) : ℝ := ∑ i, singular A i^m

def schatten (m : ℕ) (A : Matrix n n ℂ) : ℝ := (singularMass m A)^((m : ℝ)⁻¹)

end CoordinateSweeps.TraceHolder

namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n]
open scoped ComplexOrder

def oddWord (q : ℕ) (A : Matrix n n ℂ) : List (Matrix n n ℂ) :=
  A :: (List.replicate q [A.conjTranspose,A]).flatten

end CoordinateSweeps.TraceHolder

end
end
end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Unitary_Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.SpectralBlock
variable {Γ : Type*} [Group Γ] [Fintype Γ]
variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Level (r : n → ℝ) (v : ℝ) := {i : n // r i=v}

omit [DecidableEq n] in
lemma mul_restrict (r : n → ℝ) (v : ℝ) (A B : Matrix n n ℂ)
    (hA : ∀ i j, r i ≠ r j → A i j=0) :
    (A*B).submatrix (Subtype.val : Level r v → n) (Subtype.val : Level r v → n) =
      A.submatrix (Subtype.val : Level r v → n) (Subtype.val : Level r v → n) * B.submatrix (Subtype.val : Level r v → n) (Subtype.val : Level r v → n) := by
  ext i j
  rw [Matrix.submatrix_apply,Matrix.mul_apply,Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => r k=v)]
  have hz : ∑ k : {k : n // ¬ r k=v}, A i.val k.val * B k.val j.val = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hne : r i.val ≠ r k.val := by rw [i.property]; exact Ne.symm k.property
    rw [hA _ _ hne,zero_mul]
  rw [hz,add_zero]
  rfl

def representation (τ : Γ →* Matrix n n ℂ) (r : n → ℝ) (v : ℝ)
    (hτ : ∀ g i j, r i ≠ r j → τ g i j=0) : Γ →* Matrix (Level r v) (Level r v) ℂ where
  toFun g := (τ g).submatrix Subtype.val Subtype.val
  map_one' := by
    rw [map_one]
    ext i j
    simp [Matrix.one_apply,Subtype.val_inj]
  map_mul' g h := by
    rw [map_mul]
    exact mul_restrict r v (τ g) (τ h) (hτ g)

end CoordinateSweeps.SpectralBlock

end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.SignedTensor_Overlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.SignedTensor
open TensorBoard
variable {R C I J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype I] [Fintype J]

abbrev groupOperator {p l : ℕ} (x : MonoidAlgebra ℂ (Equiv.Perm (Fin l))) :
    Matrix (Word p l) (Word p l) ℂ := MonoidAlgebra.lift ℂ _ _ (action p l) x

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open TensorBoard
variable {R C I J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype I] [Fintype J]

def labelRowProduct {p l : ℕ} (e : Fin l → R × C) (r : R → EvenDensity p) :
    Matrix (Word p l) (Word p l) ℂ := TensorBoard.tensor (fun x => (r (e x).1).val)

def labelColumnProduct {p l : ℕ} (e : Fin l → R × C) (r : C → EvenDensity p) :
    Matrix (Word p l) (Word p l) ℂ := TensorBoard.tensor (fun x => (r (e x).2).val)

/- Literal deleted-board overlap with actual signed tensor action. The two
mixture dominations will be obtained by tensoring the local density theorem;
the whitening and the full-group dimension loss are constructed here. -/

end CoordinateSweeps.SignedTensor

end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Young_Classification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.YoungCorner

abbrev Boxes (μ : YoungDiagram) := ↥μ.cells

def colorStabilizer {X A : Type*} (f : X → A) : Subgroup (Equiv.Perm X) where
  carrier := {σ | ∀ x, f (σ x)=f x}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb x; exact (ha (b x)).trans (hb x)
  inv_mem' := by
    intro a ha x
    simpa only [Equiv.Perm.inv_def,Equiv.apply_symm_apply] using (ha (a⁻¹ x)).symm

def rows (μ : YoungDiagram) : Subgroup (Equiv.Perm (Boxes μ)) := colorStabilizer (fun x => x.val.1)
def cols (μ : YoungDiagram) : Subgroup (Equiv.Perm (Boxes μ)) := colorStabilizer (fun x => x.val.2)

lemma row_lt (μ : YoungDiagram) (x : Boxes μ) : x.val.1 < μ.colLen 0 := by
  apply YoungDiagram.mem_iff_lt_colLen.mp
  exact μ.up_left_mem le_rfl (Nat.zero_le _) x.property

lemma col_lt (μ : YoungDiagram) (x : Boxes μ) : x.val.2 < μ.rowLen x.val.1 :=
  YoungDiagram.mem_iff_lt_rowLen.mp x.property

def rowDecomp (μ : YoungDiagram) : Boxes μ ≃ Σ i : Fin (μ.colLen 0), Fin (μ.rowLen i) where
  toFun x := ⟨⟨x.val.1,row_lt μ x⟩,⟨x.val.2,col_lt μ x⟩⟩
  invFun x := ⟨(x.1,x.2),YoungDiagram.mem_iff_lt_rowLen.mpr x.2.isLt⟩
  left_inv x := rfl
  right_inv x := by rcases x with ⟨i,j⟩; rfl

def values {n : ℕ} (f : Fin n → ℕ) : Finset ℕ := Finset.univ.image f

lemma values_card {n : ℕ} (f : Fin n → ℕ) (hf : Function.Injective f) : (values f).card=n := by
  simp [values,Finset.card_image_of_injective _ hf]

def valuesEquiv {n : ℕ} (f : Fin n → ℕ) (hf : Function.Injective f) : Fin n ≃ ↥(values f) :=
  Equiv.ofBijective (fun x => ⟨f x,Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun x y h => hf (congrArg Subtype.val h),by
      rintro ⟨y,hy⟩
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact ⟨x,rfl⟩⟩

/- Sort a finite injective natural-valued list without changing its indices. -/
def sortPerm {n : ℕ} (f : Fin n → ℕ) (hf : Function.Injective f) : Equiv.Perm (Fin n) :=
  ((values f).orderIsoOfFin (values_card f hf)).toEquiv.trans (valuesEquiv f hf).symm

def NoCollision (μ : YoungDiagram) (σ : Equiv.Perm (Boxes μ)) : Prop :=
  ∀ x y, x.val.1=y.val.1 → (σ x).val.2=(σ y).val.2 → x=y

def rowColumn (μ : YoungDiagram) (σ : Equiv.Perm (Boxes μ))
    (i : Fin (μ.colLen 0)) (j : Fin (μ.rowLen i)) : ℕ :=
  (σ ((rowDecomp μ).symm ⟨i,j⟩)).val.2

lemma rowColumn_injective (μ : YoungDiagram) (σ : Equiv.Perm (Boxes μ))
    (h : NoCollision μ σ) (i : Fin (μ.colLen 0)) : Function.Injective (rowColumn μ σ i) := by
  intro j k hjk
  have hx := h ((rowDecomp μ).symm ⟨i,j⟩) ((rowDecomp μ).symm ⟨i,k⟩) rfl hjk
  exact Fin.ext (congrArg (fun x : Boxes μ => x.val.2) hx)

def sortingRows (μ : YoungDiagram) (σ : Equiv.Perm (Boxes μ)) (h : NoCollision μ σ) :
    Equiv.Perm (Boxes μ) :=
  (rowDecomp μ).trans ((Equiv.sigmaCongrRight fun i => sortPerm (rowColumn μ σ i)
    (rowColumn_injective μ σ h i)).trans (rowDecomp μ).symm)

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

def rowPrefix (μ : YoungDiagram) (t : ℕ) : Finset (Boxes μ) :=
  Finset.univ.filter (fun x => x.val.1<t)

def columnPrefixEquiv (μ : YoungDiagram) (t j : ℕ) :
    {x : Boxes μ // x ∈ (rowPrefix μ t).filter (fun x => x.val.2=j)} ≃ Fin (min t (μ.colLen j)) where
  toFun x := ⟨x.val.val.1,by
    have hx := Finset.mem_filter.mp x.property
    have ht := (Finset.mem_filter.mp hx.1).2
    have hc := YoungDiagram.mem_iff_lt_colLen.mp x.val.property
    rw [hx.2] at hc
    exact lt_min ht hc⟩
  invFun i := ⟨⟨(i,j),YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_lt_of_le i.isLt (min_le_right _ _))⟩,by
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,rowPrefix,and_true]
    exact lt_of_lt_of_le i.isLt (min_le_left _ _)⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (Finset.mem_filter.mp x.property).2.symm
  right_inv i := rfl

def rowEquiv (μ : YoungDiagram) (i : ℕ) :
    {x : Boxes μ // x.val.1=i} ≃ Fin (μ.rowLen i) where
  toFun x := ⟨x.val.val.2,by
    have hx := YoungDiagram.mem_iff_lt_rowLen.mp x.val.property
    rwa [x.property] at hx⟩
  invFun j := ⟨⟨(i,j),YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩,rfl⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.property.symm rfl
  right_inv j := rfl

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.RepDetection
variable {G V : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] [FiniteDimensional ℂ V] in
@[simp] lemma subrep_bot (τ : Representation ℂ G V) :
    (⊥ : Subrepresentation τ).toSubmodule=⊥ := rfl
omit [Fintype G] [FiniteDimensional ℂ V] in
@[simp] lemma subrep_top (τ : Representation ℂ G V) :
    (⊤ : Subrepresentation τ).toSubmodule=⊤ := rfl

def nested {τ : Representation ℂ G V} (S : Subrepresentation τ)
    (T : Subrepresentation S.toRepresentation) : Subrepresentation τ where
  toSubmodule := T.toSubmodule.map S.toSubmodule.subtype
  apply_mem_toSubmodule := by
    intro g v hv
    obtain ⟨w,hw,rfl⟩ := hv
    exact ⟨S.toRepresentation g w,T.apply_mem_toSubmodule g hw,rfl⟩

theorem exists_irreducible_detecting (τ : Representation ℂ G V)
    (A : Module.End ℂ V) (hA : A ≠ 0) :
    ∃ S : Subrepresentation τ, S.toRepresentation.IsIrreducible ∧
      ∃ v : S.toSubmodule, A v ≠ 0 := by
  classical
  obtain ⟨v,hv⟩ : ∃ v, A v ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (LinearMap.ext h)
  have hp : ∃ n, ∃ S : Subrepresentation τ,
      (∃ v : S.toSubmodule, A v ≠ 0) ∧ Module.finrank ℂ S.toSubmodule=n :=
    ⟨Module.finrank ℂ V,⊤,⟨⟨v,Submodule.mem_top⟩,hv⟩,by simp⟩
  obtain ⟨S,⟨w,hw⟩,hSdim⟩ := Nat.find_spec hp
  have hmin (T : Subrepresentation τ) (ht : ∃ v : T.toSubmodule, A v ≠ 0) :
      Module.finrank ℂ S.toSubmodule ≤ Module.finrank ℂ T.toSubmodule := by
    rw [hSdim]
    exact Nat.find_min' hp ⟨T,ht,rfl⟩
  have : Nontrivial S.toSubmodule := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    have hz : w=0 := Subsingleton.elim _ _
    simp [hz] at hw
  refine ⟨S,?_,w,hw⟩
  refine { exists_pair_ne := ⟨⊥,⊤,?_⟩, eq_bot_or_eq_top := ?_ }
  · intro he
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule he)
  · intro T
    by_cases hT : T=⊥
    · exact Or.inl hT
    right
    by_contra htop
    let : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
    obtain ⟨U,hU⟩ := exists_isCompl T
    have hUt : U ≠ ⊤ := by
      intro he
      have hh := hU.inf_eq_bot
      rw [he,inf_top_eq] at hh
      exact hT hh
    have hw' : w ∈ T.toSubmodule ⊔ U.toSubmodule := by
      have he := congrArg Subrepresentation.toSubmodule hU.sup_eq_top
      rw [← Subrepresentation.toSubmodule_sup,he]
      exact Submodule.mem_top
    obtain ⟨t,ht,u,hu,hwu⟩ := Submodule.mem_sup.mp hw'
    have hdetect : (A (t : V) ≠ 0) ∨ (A (u : V) ≠ 0) := by
      by_contra hn
      push Not at hn
      apply hw
      rw [← hwu]
      simp [map_add,hn]
    rcases hdetect with htA | huA
    · have hlow := hmin (nested S T) ⟨⟨t,⟨t,ht,rfl⟩⟩,htA⟩
      have hdim : Module.finrank ℂ (nested S T).toSubmodule = Module.finrank ℂ T.toSubmodule :=
        S.toSubmodule.finrank_map_subtype_eq T.toSubmodule
      have hhigh : Module.finrank ℂ T.toSubmodule < Module.finrank ℂ S.toSubmodule :=
        Submodule.finrank_lt (fun he => htop (Subrepresentation.toSubmodule_injective he))
      omega
    · have hlow := hmin (nested S U) ⟨⟨u,⟨u,hu,rfl⟩⟩,huA⟩
      have hdim : Module.finrank ℂ (nested S U).toSubmodule = Module.finrank ℂ U.toSubmodule :=
        S.toSubmodule.finrank_map_subtype_eq U.toSubmodule
      have hhigh : Module.finrank ℂ U.toSubmodule < Module.finrank ℂ S.toSubmodule :=
        Submodule.finrank_lt (fun he => hUt (Subrepresentation.toSubmodule_injective he))
      omega

end CoordinateSweeps.RepDetection

namespace CoordinateSweeps.YoungCorner
variable {X A : Type*} [Fintype X] [DecidableEq X] [Ring A] [Algebra ℂ A]

/- Ordinary source sign. -/
def signScalar {X : Type*} [Fintype X] [DecidableEq X] : Equiv.Perm X →* ℂ :=
  (Int.castRingHom ℂ).toMonoidHom.comp ((Units.coeHom ℤ).comp Equiv.Perm.sign)

@[simp] lemma signScalar_swap {X : Type*} [Fintype X] [DecidableEq X] (a b : X) (hab : a ≠ b) :
    signScalar (Equiv.swap a b) = -1 := by
  simp [signScalar,Equiv.Perm.sign_swap hab]

def fixedSum (f : X → ℕ) (ρ : Equiv.Perm X →* A) : A :=
  ∑ r : colorStabilizer f, ρ r

def alternatingSum (f : X → ℕ) (ρ : Equiv.Perm X →* A) : A :=
  ∑ r : colorStabilizer f, signScalar (r : Equiv.Perm X) • ρ r

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable {X V : Type*} [Fintype X] [DecidableEq X] [AddCommGroup V] [Module ℂ V]

def rowColor {μ : YoungDiagram} (t : X ≃ Boxes μ) : X → ℕ := fun x => (t x).val.1
def colColor {μ : YoungDiagram} (t : X ≃ Boxes μ) : X → ℕ := fun x => (t x).val.2

def hasShape (μ : YoungDiagram) (t : X ≃ Boxes μ) (τ : Representation ℂ (Equiv.Perm X) V) : Prop :=
  fixedSum (rowColor t) τ * alternatingSum (colColor t) τ ≠ 0

variable (G : Type*) [Group G]

def regular : Representation ℂ G (G → ℂ) where
  toFun g :=
    { toFun := fun f x => f (g⁻¹*x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_inv_rev,mul_assoc]

@[simp] lemma regular_apply (g : G) (f : G → ℂ) (x : G) : regular G g f x=f (g⁻¹*x) := rfl

omit [AddCommGroup V] [Module ℂ V] [Fintype X] [DecidableEq X] in
lemma row_column_intersection (μ : YoungDiagram) (t : X ≃ Boxes μ)
    (r : colorStabilizer (rowColor t)) (c : colorStabilizer (colColor t)) :
    (r : Equiv.Perm X)*(c : Equiv.Perm X)=1 ↔ r=1 ∧ c=1 := by
  constructor
  · intro h
    have he : (r : Equiv.Perm X)=(c : Equiv.Perm X)⁻¹ := by
      calc
        _ = ((r : Equiv.Perm X)*(c : Equiv.Perm X))*(c : Equiv.Perm X)⁻¹ := by simp [mul_assoc]
        _ = _ := by rw [h,one_mul]
    have hr : r=1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro x
      apply t.injective
      apply Subtype.ext
      apply Prod.ext
      · exact r.property x
      · have hc := (colorStabilizer (colColor t)).inv_mem c.property
        change colColor t ((r : Equiv.Perm X) x)=colColor t x
        rw [he]
        exact hc x
    refine ⟨hr,?_⟩
    apply Subtype.ext
    simpa [hr] using h
  · rintro ⟨rfl,rfl⟩
    simp

/- Every diagram has a nonzero row-column corner in the genuine regular law. -/
lemma regular_hasShape (μ : YoungDiagram) (t : X ≃ Boxes μ) :
    hasShape μ t (regular (Equiv.Perm X)) := by
  let v : Equiv.Perm X → ℂ := fun g => if g=1 then 1 else 0
  have hv : (fixedSum (rowColor t) (regular (Equiv.Perm X)) *
      alternatingSum (colColor t) (regular (Equiv.Perm X))) v 1=1 := by
    simp only [fixedSum,alternatingSum,Module.End.mul_apply,LinearMap.sum_apply,regular_apply,
      Finset.sum_apply,LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul,mul_one,v,
      ← mul_inv_rev,inv_eq_one,row_column_intersection]
    simp [ite_and]
  intro hz
  have hh := congrArg (fun A : Module.End ℂ (Equiv.Perm X → ℂ) => A v 1) hz
  rw [hv] at hh
  exact one_ne_zero hh

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable {X V : Type*} [Fintype X] [DecidableEq X] [AddCommGroup V] [Module ℂ V]

lemma fixedSum_subrepresentation (f : X → ℕ) (τ : Representation ℂ (Equiv.Perm X) V)
    (S : Subrepresentation τ) (v : S.toSubmodule) :
    (fixedSum f S.toRepresentation v : V)=fixedSum f τ (v : V) := by
  simp [fixedSum,Subrepresentation.toRepresentation]

lemma alternatingSum_subrepresentation (f : X → ℕ) (τ : Representation ℂ (Equiv.Perm X) V)
    (S : Subrepresentation τ) (v : S.toSubmodule) :
    (alternatingSum f S.toRepresentation v : V)=alternatingSum f τ (v : V) := by
  simp [alternatingSum,Subrepresentation.toRepresentation]

lemma exists_shape_constituent (μ : YoungDiagram) (t : X ≃ Boxes μ) :
    ∃ S : Subrepresentation (regular (Equiv.Perm X)),
      S.toRepresentation.IsIrreducible ∧ hasShape μ t S.toRepresentation := by
  obtain ⟨S,hS,v,hv⟩ := RepDetection.exists_irreducible_detecting (regular (Equiv.Perm X))
    (fixedSum (rowColor t) (regular (Equiv.Perm X))*alternatingSum (colColor t) (regular (Equiv.Perm X)))
    (regular_hasShape μ t)
  refine ⟨S,hS,?_⟩
  intro hh
  apply hv
  have hz := congrArg (fun A : Module.End ℂ S.toSubmodule => (A v : Equiv.Perm X → ℂ)) hh
  simp only [Module.End.mul_apply,fixedSum_subrepresentation,alternatingSum_subrepresentation] at hz
  exact hz

/- Chosen regular constituent. -/
def shapeSubrep (μ : YoungDiagram) (t : X ≃ Boxes μ) : Subrepresentation (regular (Equiv.Perm X)) :=
  Classical.choose (exists_shape_constituent μ t)

instance shapeSubrep_irreducible (μ : YoungDiagram) (t : X ≃ Boxes μ) :
    (shapeSubrep μ t).toRepresentation.IsIrreducible :=
  (Classical.choose_spec (exists_shape_constituent μ t)).1

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

def diagramOfPartition {n : ℕ} (p : Nat.Partition n) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (Multiset.pairwise_sort _ _).sortedGE

lemma partitionRows_pos {n : ℕ} (p : Nat.Partition n) (x : ℕ)
    (hx : x ∈ p.parts.sort (· ≥ ·)) : 0 < x := by
  apply p.parts_pos
  have hh : x ∈ (↑(p.parts.sort (· ≥ ·)) : Multiset ℕ) := hx
  simpa only [Multiset.sort_eq] using hh

lemma diagramOfPartition_rowLens {n : ℕ} (p : Nat.Partition n) :
    (diagramOfPartition p).rowLens=p.parts.sort (· ≥ ·) :=
  YoungDiagram.rowLens_ofRowLens_eq_self (partitionRows_pos p)

lemma card_boxes_eq_rowLens_sum (μ : YoungDiagram) :
    Fintype.card (Boxes μ)=μ.rowLens.sum := by
  rw [Fintype.card_congr (rowDecomp μ),Fintype.card_sigma]
  simp only [Fintype.card_fin,YoungDiagram.rowLens]
  have he : List.map μ.rowLen (List.range (μ.colLen 0)) =
      List.ofFn (fun i : Fin (μ.colLen 0) => μ.rowLen i) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj; simp
  rw [he,List.sum_ofFn]

lemma card_diagramOfPartition {n : ℕ} (p : Nat.Partition n) :
    Fintype.card (Boxes (diagramOfPartition p))=n := by
  rw [card_boxes_eq_rowLens_sum,diagramOfPartition_rowLens,← Multiset.sum_coe,
    Multiset.sort_eq,p.parts_sum]

def partitionFilling {X : Type*} [Fintype X] (p : Nat.Partition (Fintype.card X)) :
    X ≃ Boxes (diagramOfPartition p) := Fintype.equivOfCardEq (card_diagramOfPartition p).symm

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.CharacterCount
universe u v w
variable {G : Type u} [Group G] [Fintype G]
variable {I : Type v} (V : I → Type w) [∀ i, AddCommGroup (V i)]
  [∀ i, Module ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
  (τ : ∀ i, Representation ℂ G (V i)) [∀ i, (τ i).IsIrreducible]

def pairing (i : I) : (G → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (Fintype.card G : ℂ)⁻¹ * ∑ g, f g * (τ i).character g⁻¹
  map_add' f g := by simp [add_mul,Finset.sum_add_distrib,mul_add]
  map_smul' c f := by simp [Finset.mul_sum,mul_assoc,mul_left_comm]

end CoordinateSweeps.CharacterCount

namespace CoordinateSweeps.YoungCorner
variable {X : Type} [Fintype X] [DecidableEq X]

abbrev PartitionSpace (p : Nat.Partition (Fintype.card X)) :=
  (shapeSubrep (diagramOfPartition p) (partitionFilling p (X := X))).toSubmodule

def partitionRep (p : Nat.Partition (Fintype.card X)) :
    Representation ℂ (Equiv.Perm X) (PartitionSpace (X := X) p) :=
  (shapeSubrep (diagramOfPartition p) (partitionFilling p (X := X))).toRepresentation

instance partitionRep_irreducible (p : Nat.Partition (Fintype.card X)) :
    (partitionRep (X := X) p).IsIrreducible := shapeSubrep_irreducible _ _

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable (X : Type) [Fintype X] [DecidableEq X]

def partitionUnitary (p : Nat.Partition (Fintype.card X)) : UnitaryIrrep (Equiv.Perm X) :=
  Classical.choose (UnitaryRealization.exists_unitary (partitionRep p (X := X)))

end CoordinateSweeps.YoungCorner

end
end
end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.SignedTensor_Resolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.SignedTensor

def ActiveType (p l : ℕ) :=
  { a : Nat.Partition (Fintype.card (Fin l)) // (YoungCorner.partitionUnitary (Fin l) a).projector (action p l) ≠ 0 }

instance instFintypeActiveType (p l : ℕ) : Fintype (ActiveType p l) := by
  unfold ActiveType
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance instDecidableEqActiveType (p l : ℕ) : DecidableEq (ActiveType p l) := Classical.decEq _

def activeIrrep {p l : ℕ} (a : ActiveType p l) : UnitaryIrrep (Equiv.Perm (Fin l)) :=
  YoungCorner.partitionUnitary (Fin l) a.val

def activeProjector {p l : ℕ} (a : ActiveType p l) : commutant p l :=
  ⟨(activeIrrep a).projector (action p l),fun σ =>
    ((activeIrrep a).projector_commute (action p l) σ).symm⟩

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
variable {p r : ℕ} (n : Fin r → ℕ)
abbrev BlockType (p : ℕ) := ∀ i, ActiveType p (n i)

abbrev blockProjector (α : BlockType n p) := groupedProjector (p := p) n (fun i => activeIrrep (α i))

/- Actual polynomial-size identity resolution of each product subgroup. -/

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open UnitaryIrrep FiberBlocks
variable {p r l : ℕ} (n : Fin r → ℕ)

variable {L : Type*} [Fintype L]

def blockEntropy {n : Fin r → ℕ} (α : BlockType n p) : ℝ :=
  ∑ i, Real.log (activeIrrep (α i)).dimension

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.YoungCorner
variable {μ : YoungDiagram} {p : ℕ}

def Hook (μ : YoungDiagram) (p : ℕ) : Prop := ∀ x : Boxes μ, x.val.1<p ∨ x.val.2<p

def hookLetter (h : Hook μ p) (x : Boxes μ) : SignedTensor.Letter p :=
  if hx : x.val.1<p then ⟨x.val.1,by omega⟩ else ⟨p+x.val.2,by have hh:=(h x).resolve_left hx; omega⟩

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable {μ : YoungDiagram} {p l : ℕ}

def signedRep (p l : ℕ) : Representation ℂ (Equiv.Perm (Fin l)) (SignedTensor.Word p l → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp (SignedTensor.action p l)

end CoordinateSweeps.YoungCorner

end
end
end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Induction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.Grid.Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

lemma onLine_row_iff (j : Fin A.b) (L : A.Line j) (y : B.Slot) (i : Fin h) :
    H.OnLine (Fin.castAdd B.b j) (rowLines A B j (L,y)) i ↔
      H.rowOf i=y ∧ (fun k : {k : Fin A.b // k≠j} =>
        (splitSlots A B (H.path i (prefixTime A B j.castSucc))).1 k.val)=L := by
  have hh := rowLines_evaluation A B j (H.path i (prefixTime A B j.castSucc))
  constructor
  · intro hi
    have he := congrArg (rowLines A B j).symm hi
    change (rowLines A B j).symm (fun k => H.path i (prefixTime A B j.castSucc) k.val)=
      (rowLines A B j).symm (rowLines A B j (L,y)) at he
    rw [hh,Equiv.symm_apply_apply] at he
    exact ⟨(H.row_constant i j.castSucc).symm.trans (congrArg Prod.snd he),congrArg Prod.fst he⟩
  · rintro ⟨hi,hl⟩
    apply (rowLines A B j).symm.injective
    change (rowLines A B j).symm (fun k => H.path i (prefixTime A B j.castSucc) k.val)=
      (rowLines A B j).symm (rowLines A B j (L,y))
    rw [hh,Equiv.symm_apply_apply]
    exact Prod.ext hl ((H.row_constant i j.castSucc).trans hi)

lemma onLine_column_iff (j : Fin B.b) (x : A.Slot) (L : B.Line j) (i : Fin h) :
    H.OnLine (Fin.natAdd A.b j) (columnLines A B j (x,L)) i ↔
      H.columnOf i=x ∧ (fun k : {k : Fin B.b // k≠j} =>
        (splitSlots A B (H.path i (suffixTime A B j.castSucc))).2 k.val)=L := by
  have hh := columnLines_evaluation A B j (H.path i (suffixTime A B j.castSucc))
  constructor
  · intro hi
    have he := congrArg (columnLines A B j).symm hi
    change (columnLines A B j).symm (fun k => H.path i (suffixTime A B j.castSucc) k.val)=
      (columnLines A B j).symm (columnLines A B j (x,L)) at he
    rw [hh,Equiv.symm_apply_apply] at he
    exact ⟨(H.column_constant i j.castSucc).symm.trans (congrArg Prod.fst he),congrArg Prod.snd he⟩
  · rintro ⟨hi,hl⟩
    apply (columnLines A B j).symm.injective
    change (columnLines A B j).symm (fun k => H.path i (suffixTime A B j.castSucc) k.val)=
      (columnLines A B j).symm (columnLines A B j (x,L))
    rw [hh,Equiv.symm_apply_apply]
    exact Prod.ext ((H.column_constant i j.castSucc).trans hi) hl

def rowOnLineEquiv (j : Fin A.b) (L : A.Line j) (y : B.Slot) :
    {k : Fin (H.rowCount y) // (H.rowHoles y).OnLine j L k} ≃
      {i : Fin h // H.OnLine (Fin.castAdd B.b j) (rowLines A B j (L,y)) i} where
  toFun k := ⟨(H.rowCards y k.val).val,(H.onLine_row_iff j L y _).mpr
    ⟨(H.rowCards y k.val).property,k.property⟩⟩
  invFun i := ⟨(H.rowCards y).symm ⟨i.val,((H.onLine_row_iff j L y _).mp i.property).1⟩,by
    change (fun (k : {k : Fin A.b // k ≠ j}) => (splitSlots A B (H.path
      (H.rowCards y ((H.rowCards y).symm _)).val (prefixTime A B j.castSucc))).1 k.val)=L
    simp only [Equiv.apply_symm_apply]
    exact ((H.onLine_row_iff j L y _).mp i.property).2⟩
  left_inv k := by
    apply Subtype.ext
    apply (H.rowCards y).injective
    simp only [Equiv.apply_symm_apply]
  right_inv i := by
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]

def columnOnLineEquiv (j : Fin B.b) (x : A.Slot) (L : B.Line j) :
    {k : Fin (H.columnCount x) // (H.columnHoles x).OnLine j L k} ≃
      {i : Fin h // H.OnLine (Fin.natAdd A.b j) (columnLines A B j (x,L)) i} where
  toFun k := ⟨(H.columnCards x k.val).val,(H.onLine_column_iff j x L _).mpr
    ⟨(H.columnCards x k.val).property,k.property⟩⟩
  invFun i := ⟨(H.columnCards x).symm ⟨i.val,((H.onLine_column_iff j x L _).mp i.property).1⟩,by
    change (fun (k : {k : Fin B.b // k ≠ j}) => (splitSlots A B (H.path
      (H.columnCards x ((H.columnCards x).symm _)).val (suffixTime A B j.castSucc))).2 k.val)=L
    simp only [Equiv.apply_symm_apply]
    exact ((H.onLine_column_iff j x L _).mp i.property).2⟩
  left_inv k := by
    apply Subtype.ext
    apply (H.columnCards x).injective
    simp only [Equiv.apply_symm_apply]
  right_inv i := by
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open UnitaryIrrep SignedTensor YoungCorner
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)
def junctionChart (hf : H.Feasible) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree) :
    H.stabilizer ≃* Equiv.Perm (Fin (Fintype.card H.JunctionFree)) :=
  (H.junctionEquiv hf).trans (H.junctionFreeEquiv.trans e.symm.permCongrHom)

end CoordinateSweeps.Grid.Holes

end
end
end
end
end
end
end
end
end
end

open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Graphs_Coverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.Coverage
variable {I H : Type*} [Fintype I] [DecidableEq I]

/- Oriented edges crossing a two-color cut. -/
def cutEdges (R : I → I → Prop) (c : I → Bool) : Finset (I × I) :=
  Finset.univ.filter (fun p => R p.1 p.2 ∧ c p.1 ≠ c p.2)

omit [DecidableEq I] in
@[simp] theorem mem_cutEdges (R : I → I → Prop) (c : I → Bool) (i j : I) :
    (i,j) ∈ cutEdges R c ↔ R i j ∧ c i ≠ c j := by simp [cutEdges]

/- A maximum cut has an opposite-color neighbor at every nonisolated vertex.
Only symmetry and absence of loops are used. -/
def covered (R : I → I → Prop) (T : I → H → Prop) : Finset I :=
  Finset.univ.filter (fun i => (∃ j, R i j) ∨ (∃ l, T i l))

omit [DecidableEq I] in
@[simp] theorem mem_covered (R : I → I → Prop) (T : I → H → Prop) (i : I) :
    i ∈ covered R T ↔ (∃ j, R i j) ∨ (∃ l, T i l) := by simp [covered]

/- A star forest supplies at least half as many distinct particle tails as
there are covered particles, with all parents outside the chosen tails. -/

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

/- Product mass of independent particle data. -/
def productMass (w : X → ℝ) (x : I → X) : ℝ := ∏ i, w (x i)

/- Finite event probability, with the product law on the full endpoint array. -/
def probability (w : X → ℝ) (P : (I → X) → Prop) : ℝ :=
  ∑ x : I → X, if P x then productMass w x else 0

def glue (A : Finset I) (x : A → X) (y : {i : I // i ∉ A} → X) : I → X :=
  (Equiv.piEquivPiSubtypeProd (fun i => i ∈ A) (fun _ => X)).symm (x,y)

omit [Fintype I] [Fintype X] in
@[simp] theorem glue_mem (A : Finset I) (x : A → X) (y : {i : I // i ∉ A} → X)
    (i : A) : glue A x y i = x i := by
  simp [glue, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]

omit [Fintype I] [Fintype X] in
@[simp] theorem glue_not_mem (A : Finset I) (x : A → X) (y : {i : I // i ∉ A} → X)
    (i : {i : I // i ∉ A}) : glue A x y i = y i := by
  simp [glue, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I H : Type*} [Fintype I] [DecidableEq I]

/- A finite directed star system. Distinct tails are indexed by the subtype A;
the parent lies outside A or is a hole. -/
def starSystem (R : I → I → Prop) (T : I → H → Prop)
    (A : Finset I) (p : A → I ⊕ H) : Prop :=
  ∀ i : A, match p i with
    | .inl j => j ∉ A ∧ R i j
    | .inr l => T i l

/- The witness can be trimmed to any requested number of tails up to half
(rounded up) of the number of covered particles. -/

variable {X : Type*} [Fintype X]

/- The sharing event of one directed system under the full independent data.
Forbidden parent choices simply give an empty event. -/
def starEvent (S : X → X → Prop) (holes : H → X)
    (A : Finset I) (p : A → I ⊕ H) (x : I → X) : Prop :=
  starSystem (fun i j => S (x i) (x j)) (fun i l => S (x i) (holes l)) A p

/- A tail predicate with the values at all its possible roots fixed. -/
def rootPredicate (S : X → X → Prop) (holes : H → X)
    (A : Finset I) (p : A → I ⊕ H)
    (y : {i : I // i ∉ A} → X) (i : A) (t : X) : Prop :=
  match p i with
  | .inl j => if hj : j ∉ A then S t (y ⟨j,hj⟩) else False
  | .inr l => S t (holes l)

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I H : Type*} [Fintype I] [DecidableEq I] [Fintype H]

/- Data encoding exactly j distinct tails and one arbitrary parent per tail.
The sub-event enforces the star/root restrictions. -/
abbrev Witness (I H : Type*) [Fintype I] (j : ℕ) :=
  Σ A : {A : Finset I // A.card = j}, (A.val → I ⊕ H)

variable {X : Type*} [Fintype X]

/- Covered particles for the actual symmetric sharing relation on path data. -/
def sharingCoverage (S : X → X → Prop) (holes : H → X) (x : I → X) : Finset I :=
  covered (fun i j => i ≠ j ∧ S (x i) (x j)) (fun i l => S (x i) (holes l))

end CoordinateSweeps.Coverage

end
end
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
open scoped BigOperators
namespace CoordinateSweeps.Coverage
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

/- Independent occupancy of a fixed measurable subset. The set is fixed
BEFORE taking probability, exactly as required in source04:eq12. -/
def encodeSmallSet {L : Type*} [Fintype L] [DecidableEq L] (r : ℕ)
    (S : {S : Finset L // S.card ≤ r}) : Fin r → Option L := fun i =>
  if hi : i.val < S.val.card then
    some (((Fintype.equivFinOfCardEq (Fintype.card_coe S.val)).symm ⟨i.val,hi⟩).val)
  else none

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I X L : Type*} [Fintype I] [DecidableEq I] [Fintype X] [Fintype L] [DecidableEq L]

def heavySet (t : L → ℕ) (v : ℝ) : Finset L := Finset.univ.filter (fun l => v < t l)

def occupancy (line : X → L) (x : I → X) (l : L) : ℕ :=
  (Finset.univ.filter (fun i => line (x i) = l)).card

end CoordinateSweeps.Coverage

end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Kernel
attribute [-instance] _root_.OAI.CoordinateSweeps.Grid.Holes.instFintypeColumnLocalChoices _root_.OAI.CoordinateSweeps.Grid.Holes.instFintypeRowLocalChoices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
All definitions are finite and use the source's ordinary probability and trace
normalizations.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

/-! The alternating placement kernel from 04-sparse:eq7.
Endpoints below need not be injections; invalid specifications have probability
zero automatically. On valid endpoint placements this is exactly the source Q. -/
namespace CoordinateSweeps
namespace Grid

variable (G : Grid)

/- The unique auxiliary trajectory joining two slots. -/
def pathBetween (x y : G.Slot) (t : Fin (G.b+1)) : G.Slot :=
  fun j => if j.val < t.val then y j else x j

@[simp] theorem pathBetween_zero (x y : G.Slot) : G.pathBetween x y 0 = x := by
  ext j
  simp [pathBetween]

@[simp] theorem pathBetween_last (x y : G.Slot) :
    G.pathBetween x y (Fin.last G.b) = y := by
  ext j
  simp [pathBetween, j.isLt]

@[simp] theorem pathBetween_input (x y : G.Slot) (j : Fin G.b) :
    G.pathBetween x y j.castSucc j = x j := by
  simp [pathBetween]

@[simp] theorem pathBetween_output (x y : G.Slot) (j : Fin G.b) :
    G.pathBetween x y j.succ j = y j := by
  simp [pathBetween]

theorem pathBetween_step (x y : G.Slot) (j k : Fin G.b) (hne : k ≠ j) :
    G.pathBetween x y j.succ k = G.pathBetween x y j.castSucc k := by
  have hne' : k.val ≠ j.val := fun he => hne (Fin.ext he)
  simp only [pathBetween, Fin.val_succ, Fin.val_castSucc]
  have hi : k.val < j.val+1 ↔ k.val < j.val := by omega
  simp only [hi]

/- The stage-decorated line used by the auxiliary trajectory. -/
def pathLine (x y : G.Slot) (j : Fin G.b) : G.Line j :=
  fun k => G.pathBetween x y j.castSucc k

/- Endpoint events are equivalent to the unique additional trajectory's
line assignments. No feasibility or injectivity is postulated. -/
def endpointEvent {k : ℕ} (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (ω : G.Choices) : Prop := ∀ i ∈ A, G.sweep ω (x i) = y i

/- A direct finite constraint event on one line for the extra particles. -/
def extraLineEvent {k : ℕ} (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (j : Fin G.b) (L : G.Line j) (σ : Equiv.Perm (Cube (G.bits j))) : Prop :=
  ∀ i ∈ A, G.pathLine (x i) (y i) j = L → σ (x i j) = y i j

namespace Holes
variable {G} {h k : ℕ}

/- Exact one-line probability after the hole assignments are prescribed. -/
def localExtraProbability (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (j : Fin G.b) (L : G.Line j)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j)))) : ℝ :=
  (∑ σ, if H.LineCompatible j L σ ∧ G.extraLineEvent x y A j L σ then μ σ else 0) /
    (∑ σ, if H.LineCompatible j L σ then μ σ else 0)

/- Product form of the exact conditional endpoint probability. The bridge to
the original conditioned sweep event is proved below, not assumed. -/
def extraProbability (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) : ℝ :=
  ∏ j, ∏ L : G.Line j, H.localExtraProbability x y A j L (μ j)

/- The path-weight alternating placement matrix Q, with counting measure and
s, not s-h, in its normalization, exactly as 04-sparse:eq7. -/
def placementKernel (H : G.Holes h) (x y : Fin k → G.Slot)
    (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) : ℝ :=
  (G.size : ℝ)⁻¹ ^ k * ∑ A ∈ (Finset.univ : Finset (Fin k)).powerset,
    (-1 : ℝ) ^ (k-A.card) * (G.size : ℝ)^A.card * H.extraProbability x y A μ

/- A line-isolated additional trajectory, relative to all other additional
paths AND the prescribed holes. Stage indices are never conflated. -/
def LineIsolated (H : G.Holes h) (x y : Fin k → G.Slot) (i : Fin k) : Prop :=
  (∀ j (a : Fin h), ¬ H.OnLine j (G.pathLine (x i) (y i) j) a) ∧
  (∀ j (a : Fin k), a ≠ i →
    G.pathLine (x a) (y a) j ≠ G.pathLine (x i) (y i) j)

def OneCardUniform {d : ℕ} (μ : FiniteLaw (Equiv.Perm (Cube d))) : Prop :=
  ∀ u v : Cube d, (∑ σ, if σ u = v then μ σ else 0) = (2^d : ℝ)⁻¹

end Holes
end Grid
end CoordinateSweeps

namespace CoordinateSweeps.Grid
variable (G : Grid)

theorem boundary_coordinate_before (ω : G.Choices) (x : G.Slot) (k : Fin G.b)
    (t : ℕ) (ht : t ≤ k.val) : G.boundary ω t x k = x k := by
  induction t with
  | zero => simp
  | succ t ih =>
    have htb : t < G.b := by omega
    rw [G.boundary_succ ω htb]
    change G.stage ω ⟨t,htb⟩ (G.boundary ω t x) k = _
    rw [G.stage_apply_ne ω _ k (by intro he; have := congrArg Fin.val he; dsimp at this; omega)]
    exact ih (by omega)

theorem boundary_coordinate_stable (ω : G.Choices) (x : G.Slot) (k : Fin G.b)
    (u v : ℕ) (hku : k.val < u) (huv : u ≤ v) (hvb : v ≤ G.b) :
    G.boundary ω v x k = G.boundary ω u x k := by
  induction v, huv using Nat.le_induction with
  | base => rfl
  | succ v huv ih =>
    have hvb' : v < G.b := by omega
    rw [G.boundary_succ ω hvb']
    change G.stage ω ⟨v,hvb'⟩ (G.boundary ω v x) k = _
    rw [G.stage_apply_ne ω _ k (by intro he; have := congrArg Fin.val he; dsimp at this; omega)]
    exact ih (by omega)

theorem boundary_eq_pathBetween (ω : G.Choices) (x : G.Slot) (t : Fin (G.b+1)) :
    G.boundary ω t x = G.pathBetween x (G.sweep ω x) t := by
  funext k
  unfold pathBetween
  split_ifs with hkt
  · exact (G.boundary_coordinate_stable ω x k t G.b hkt (by omega) le_rfl).symm
  · exact G.boundary_coordinate_before ω x k t (by omega)

/- Actual endpoint events are exactly the auxiliary path constraints. -/

end CoordinateSweeps.Grid

namespace CoordinateSweeps

/- Finite independence, keeping an arbitrary local constraint at every factor. -/

namespace Grid
variable (G : Grid)

def productLineMass
    (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) (ω : G.Choices) : ℝ :=
  ∏ j, ∏ L, μ j (ω j L)

namespace Holes
variable {G} {h k : ℕ}

/- Conditional probability of an endpoint specification, from the original
independent line sample space; the full trajectories of the holes are retained. -/
def conditionalEndpointProbability (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k))
    (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) : ℝ :=
  (∑ ω, if H.Compatible ω ∧ G.endpointEvent x y A ω then G.productLineMass μ ω else 0) /
    (∑ ω, if H.Compatible ω then G.productLineMass μ ω else 0)

/- The kernel's product formula really is the conditioned sweep probability;
no independence of different layers of the auxiliary paths is used. -/

end Holes
end Grid
end CoordinateSweeps

namespace CoordinateSweeps

def binaryBoundary {d : ℕ} (bits : BinaryChoices d) (t : ℕ) : Equiv.Perm (Cube d) :=
  ((List.ofFn (fun j => binaryLayer j (bits j))).take t).reverse.prod

@[simp] theorem binaryBoundary_zero {d : ℕ} (bits : BinaryChoices d) :
    binaryBoundary bits 0 = 1 := by simp [binaryBoundary]

@[simp] theorem binaryBoundary_last {d : ℕ} (bits : BinaryChoices d) :
    binaryBoundary bits d = binarySweep d bits := by
  simp only [binaryBoundary, binarySweep, orderedProduct]
  rw [List.take_of_length_le (by simp)]

@[simp] theorem binaryLayer_apply_same {d : ℕ} (j : Fin d)
    (bits : ({k : Fin d // k ≠ j} → Bool) → Bool) (x : Cube d) :
    binaryLayer j bits x j = Bool.xor (x j) (bits (fun k => x k)) := by
  simp [binaryLayer, pairSwitch, Equiv.funSplitAt_apply, Equiv.funSplitAt_symm_apply]

def binaryPath {d : ℕ} (x y : Cube d) (t : ℕ) : Cube d :=
  fun k => if k.val < t then y k else x k

def binaryPathLine {d : ℕ} (x y : Cube d) (j : Fin d) : {k : Fin d // k ≠ j} → Bool :=
  fun k => binaryPath x y j.val k

@[simp] theorem binaryPath_zero {d : ℕ} (x y : Cube d) : binaryPath x y 0 = x := by
  funext k; simp [binaryPath]

@[simp] theorem binaryPath_last {d : ℕ} (x y : Cube d) : binaryPath x y d = y := by
  funext k; simp [binaryPath, k.isLt]

end CoordinateSweeps

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.Grid
variable (G : Grid)

def spliceEquiv (t : Fin (G.b+1)) : (G.Slot × G.Slot) ≃ (G.Slot × G.Slot) where
  toFun p := (G.pathBetween p.1 p.2 t, G.pathBetween p.2 p.1 t)
  invFun p := (G.pathBetween p.1 p.2 t, G.pathBetween p.2 p.1 t)
  left_inv p := by
    apply Prod.ext <;> funext j <;> simp only [pathBetween] <;> split_ifs <;> rfl
  right_inv p := by
    apply Prod.ext <;> funext j <;> simp only [pathBetween] <;> split_ifs <;> rfl

/- Exact counting identity for one layer of an independent endpoint pair. -/
def endpointWeight (p : G.Slot × G.Slot) : ℝ := FiniteLaw.uniform _ p

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid
variable (G : Grid)

/- Sharing means using the same decorated line at the same stage. -/
def lineShares (p q : G.Slot × G.Slot) : Prop :=
  ∃ j : Fin G.b, G.pathLine p.1 p.2 j = G.pathLine q.1 q.2 j

/- Vertex sharing means the same slot at one fixed stage boundary. -/
def vertexShares (p q : G.Slot × G.Slot) : Prop :=
  ∃ t : Fin (G.b+1), G.pathBetween p.1 p.2 t = G.pathBetween q.1 q.2 t

def lineSharingRate : ℝ := ∑ j : Fin G.b, (2^G.bits j : ℝ) / G.size

def vertexSharingRate : ℝ := (G.b+1 : ℕ) / (G.size : ℝ)

namespace Holes
variable {G} {h k : ℕ}

/- Keep the actual prescribed hole paths, recording their endpoints. -/
def endpointData (H : G.Holes h) (i : Fin h) : G.Slot × G.Slot :=
  (H.path i 0, H.path i (Fin.last G.b))

/- The source's feasibility ensures these endpoints reconstruct the entire
prescribed trajectory, not merely an unrelated bridge between its endpoints. -/

end Holes
end CoordinateSweeps.Grid

end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Transition
attribute [-instance] _root_.OAI.CoordinateSweeps.Grid.Holes.instFintypeColumnLocalChoices _root_.OAI.CoordinateSweeps.Grid.Holes.instFintypeRowLocalChoices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps
namespace Grid.Holes
variable {G : Grid} {h : ℕ}

def Extends {t : ℕ} (J : G.Holes (h+t)) (H : G.Holes h) : Prop :=
  ∀ (i : Fin h) (j : Fin (G.b+1)), J.path (Fin.castAdd t i) j = H.path i j

def extraCount {t : ℕ} (J : G.Holes (h+t)) (j : Fin G.b) (L : G.Line j) : ℕ :=
  (Finset.univ.filter (fun i : Fin t => J.OnLine j L (Fin.natAdd h i))).card

end Grid.Holes

namespace Grid.Holes
variable {G : Grid} {h t : ℕ}

def lineProb (H : G.Holes h) (j : Fin G.b) (L : G.Line j)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j)))) : ℝ :=
  μ.assignments (H.lineInput j L) (H.lineOutput j L)

def usedLine (J : G.Holes (h+t)) (j : Fin G.b) (L : G.Line j) : ℕ :=
  if J.extraCount j L = 0 then 0 else 1

end Grid.Holes

end CoordinateSweeps

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k t : ℕ}

/- An injection into the actual available input slots. -/
def ValidInput (H : G.Holes h) (x : Fin t → G.Slot) : Prop :=
  Function.Injective x ∧ ∀ i a, x i ≠ H.path a 0

/- A feasible endpoint event augments the prescribed holes by the uniquely
determined auxiliary paths. The witness is used only to verify disjointness. -/
def augment (H : G.Holes h) (u v : Fin t → G.Slot) (hu : H.ValidInput u)
    (ω : G.Choices) (hω : H.Compatible ω) (hv : ∀ i, G.sweep ω (u i) = v i) :
    G.Holes (h+t) where
  path i s := Fin.append (fun a => H.path a s) (fun a => G.pathBetween (u a) (v a) s) i
  disjoint s := by
    apply Fin.append_injective_iff.mpr
    refine ⟨H.disjoint s, ?_, ?_⟩
    · intro a b he
      have ha := G.boundary_eq_pathBetween ω (u a) s
      have hb := G.boundary_eq_pathBetween ω (u b) s
      rw [hv a] at ha
      rw [hv b] at hb
      exact hu.1 ((G.boundary ω s).injective (ha.trans (he.trans hb.symm)))
    · intro a b he
      have hb := G.boundary_eq_pathBetween ω (u b) s
      rw [hv b] at hb
      exact hu.2 b a ((G.boundary ω s).injective ((hω a s).trans (he.trans hb.symm))).symm
  coordinate_step i j l hlj := by
    cases i using Fin.addCases with
    | left a => simpa using H.coordinate_step a j l hlj
    | right a => simpa using G.pathBetween_step (u a) (v a) j l hlj

@[simp] theorem augment_old (H : G.Holes h) (u v : Fin t → G.Slot) (hu : H.ValidInput u)
    (ω : G.Choices) (hω : H.Compatible ω) (hv : ∀ i, G.sweep ω (u i) = v i)
    (i : Fin h) (s : Fin (G.b+1)) :
    (H.augment u v hu ω hω hv).path (Fin.castAdd t i) s = H.path i s := by
  simp [augment]

@[simp] theorem augment_new (H : G.Holes h) (u v : Fin t → G.Slot) (hu : H.ValidInput u)
    (ω : G.Choices) (hω : H.Compatible ω) (hv : ∀ i, G.sweep ω (u i) = v i)
    (i : Fin t) (s : Fin (G.b+1)) :
    (H.augment u v hu ω hω hv).path (Fin.natAdd h i) s =
      G.pathBetween (u i) (v i) s := by
  simp [augment]

theorem augment_compatible_iff (H : G.Holes h) (u v : Fin t → G.Slot) (hu : H.ValidInput u)
    (ω : G.Choices) (hω : H.Compatible ω) (hv : ∀ i, G.sweep ω (u i) = v i)
    (ν : G.Choices) :
    (H.augment u v hu ω hω hv).Compatible ν ↔
      H.Compatible ν ∧ ∀ i, G.sweep ν (u i) = v i := by
  constructor
  · intro hJ
    constructor
    · intro a s
      have hh := hJ (Fin.castAdd t a) s
      simpa only [augment_old] using hh
    · intro a
      have hh := hJ (Fin.natAdd h a) (Fin.last G.b)
      simpa only [augment_new, Grid.pathBetween_zero, Grid.pathBetween_last, Grid.sweep, Fin.val_last] using hh
  · rintro ⟨hν,he⟩
    intro i s
    cases i using Fin.addCases with
    | left a => simpa only [augment_old] using hν a s
    | right a =>
      simp only [augment_new, Grid.pathBetween_zero]
      rw [G.boundary_eq_pathBetween, he a]

/- A canonical enumeration of a selected list of auxiliary cards. -/
def selected (A : Finset (Fin k)) : Fin A.card ↪ Fin k :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm.toEmbedding.trans (Function.Embedding.subtype _)

theorem selected_mem (A : Finset (Fin k)) (i : Fin A.card) : selected A i ∈ A :=
  ((Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm i).property

theorem selected_range (A : Finset (Fin k)) (a : Fin k) (ha : a ∈ A) :
    ∃ i, selected A i = a := by
  let i := (Fintype.equivFinOfCardEq (Fintype.card_coe A)) ⟨a,ha⟩
  exact ⟨i, congrArg Subtype.val ((Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm_apply_apply _)⟩

theorem validInput_selected (H : G.Holes h) (u : Fin k → G.Slot) (hu : H.ValidInput u)
    (A : Finset (Fin k)) : H.ValidInput (fun i => u (selected A i)) := by
  exact ⟨hu.1.comp (selected A).injective, fun i a => hu.2 _ a⟩

theorem endpointEvent_iff_selected (u v : Fin k → G.Slot) (A : Finset (Fin k))
    (ω : G.Choices) : G.endpointEvent u v A ω ↔
      ∀ i : Fin A.card, G.sweep ω (u (selected A i)) = v (selected A i) := by
  constructor
  · intro he i
    exact he _ (selected_mem A i)
  · intro he a ha
    obtain ⟨i,rfl⟩ := selected_range A a ha
    exact he i

end CoordinateSweeps.Grid.Holes

/- Multiplicity in a unitary matrix representation is controlled by the
commutant dimension, with exact (unnormalized) character conventions. -/

end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Matrix_BlockCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.BlockCycles
variable {Ω R : Type*} [Fintype Ω] [DecidableEq Ω] [Semiring R]

def tupleSplit (n : ℕ) : (Fin (n+1) → Ω) ≃ Ω × (Fin n → Ω) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv x := by cases x; rfl

def walk {n : ℕ} (A : Fin n → Matrix Ω Ω R) (x : Fin (n+1) → Ω) : R :=
  (List.ofFn (fun i => A i (x i.castSucc) (x i.succ))).prod

end CoordinateSweeps.BlockCycles

namespace CoordinateSweeps.BlockCycles
variable {Ω n R : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype n] [DecidableEq n] [Semiring R]

def block (A : Matrix (Ω × n) (Ω × n) R) : Matrix Ω Ω (Matrix n n R) :=
  Matrix.of fun y x => Matrix.of fun i j => A (y,i) (x,j)

/- Literal placement blocks, with no normalized trace convention. -/
def blocks : Matrix (Ω × n) (Ω × n) R →+* Matrix Ω Ω (Matrix n n R) where
  toFun := block
  map_one' := by
    ext y x i j
    change (if (y,i)=(x,j) then (1 : R) else 0)=
      (if y=x then (1 : Matrix n n R) else 0) i j
    by_cases h : y=x <;> by_cases h' : i=j <;> simp [h,h',Matrix.one_apply]
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' A B := by
    ext y x i j
    have hh : (block A*block B) y x=∑ z, block A y z*block B z x := Matrix.mul_apply ..
    change (A*B) (y,i) (x,j)=(block A*block B) y x i j
    rw [hh]
    simp only [Matrix.mul_apply,Matrix.sum_apply]
    exact Fintype.sum_prod_type _

@[simp] lemma blocks_apply (A : Matrix (Ω × n) (Ω × n) R) (x y : Ω) (i j : n) :
    blocks A y x i j=A (y,i) (x,j) := rfl

end CoordinateSweeps.BlockCycles

namespace CoordinateSweeps.BlockCycles
open TraceHolder
variable {Ω n : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype n] [DecidableEq n] [Nonempty n]

/- Trace Holder applied separately on every literal placement cycle. -/
def evenWord (q : ℕ) (A : Matrix (Ω × n) (Ω × n) ℂ) : List (Matrix (Ω × n) (Ω × n) ℂ) :=
  (List.replicate q [A.conjTranspose,A]).flatten

omit [Fintype Ω] [DecidableEq Ω] [Fintype n] [DecidableEq n] [Nonempty n] in
lemma evenWord_length (q : ℕ) (A : Matrix (Ω × n) (Ω × n) ℂ) :
    (evenWord q A).length=2*q := by
  simp [evenWord,Nat.mul_comm]

end CoordinateSweeps.BlockCycles

namespace CoordinateSweeps.BlockCycles
open TraceHolder
variable {Ω n : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype n] [DecidableEq n] [Nonempty n]

def edgeWeight (A B : Matrix (Ω × n) (Ω × n) ℂ) (p : Ω → Ω → ℝ) (y x : Ω) : ℝ :=
  if B=A then p y x else p x y

def edgeFiber (A B : Matrix (Ω × n) (Ω × n) ℂ)
    (K : Ω → Ω → Matrix n n ℂ) (y x : Ω) : Matrix n n ℂ :=
  if B=A then K y x else (K x y).conjTranspose

end CoordinateSweeps.BlockCycles
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Placement_Chart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.PlacementInduction
variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]

/- A transitive action with actual chosen representatives. For the application,
Ω is the set of ordered placements; the fiber group fixes the base placement. -/
structure Chart (a : G →* Equiv.Perm Ω) where
  base : Ω
  rep : Ω → G
  reaches : ∀ x, a (rep x) base=x

namespace Chart
variable {a : G →* Equiv.Perm Ω} (C : Chart a)

def stabilizer : Subgroup G where
  carrier := {g | a g C.base=C.base}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    change a (g*h) C.base=C.base
    change a g C.base=C.base at hg
    change a h C.base=C.base at hh
    rw [map_mul,Equiv.Perm.mul_apply,hh,hg]
  inv_mem' {g} hg := by
    change a g⁻¹ C.base=C.base
    change a g C.base=C.base at hg
    apply (a g).injective
    have hi : a g⁻¹=(a g)⁻¹ := map_inv a g
    rw [hi,Equiv.Perm.coe_inv,Equiv.apply_symm_apply,hg]

def cocycle (g : G) (x : Ω) : C.stabilizer :=
  ⟨(C.rep (a g x))⁻¹*g*C.rep x,by
    change a ((C.rep (a g x))⁻¹*g*C.rep x) C.base=C.base
    simp only [map_mul,Equiv.Perm.mul_apply,C.reaches,map_inv,Equiv.Perm.coe_inv]
    exact (Equiv.symm_apply_eq _).mpr (C.reaches (a g x)).symm⟩

omit [Fintype G] [Fintype Ω] [DecidableEq Ω] in
@[simp] lemma cocycle_mul (g h : G) (x : Ω) :
    C.cocycle (g*h) x=C.cocycle g (a h x)*C.cocycle h x := by
  apply Subtype.ext
  change (C.rep (a (g*h) x))⁻¹*(g*h)*C.rep x=
    ((C.rep (a g (a h x)))⁻¹*g*C.rep (a h x))*((C.rep (a h x))⁻¹*h*C.rep x)
  rw [map_mul,Equiv.Perm.mul_apply]
  group

omit [Fintype G] [Fintype Ω] [DecidableEq Ω] in
@[simp] lemma cocycle_one (x : Ω) : C.cocycle 1 x=1 := by
  apply Subtype.ext
  change (C.rep (a 1 x))⁻¹*1*C.rep x=1
  rw [map_one,Equiv.Perm.one_apply,mul_one,inv_mul_cancel]

variable (ρ : UnitaryIrrep C.stabilizer)

/- Literal placement-by-fiber block matrix of the induced unitary action. -/
def matrix (g : G) : Matrix (Ω × Fin ρ.dimension) (Ω × Fin ρ.dimension) ℂ :=
  fun y x => if y.1=a g x.1 then ρ.matrix (C.cocycle g x.1) y.2 x.2 else 0

omit [Fintype G] in
lemma matrix_mul (g h : G) : C.matrix ρ (g*h)=C.matrix ρ g*C.matrix ρ h := by
  ext y x
  rcases y with ⟨y,i⟩
  rcases x with ⟨x,j⟩
  rw [Matrix.mul_apply,Fintype.sum_prod_type]
  have hs : (∑ z : Ω, ∑ k : Fin ρ.dimension,
      C.matrix ρ g (y,i) (z,k)*C.matrix ρ h (z,k) (x,j))=
    ∑ k : Fin ρ.dimension, C.matrix ρ g (y,i) (a h x,k)*C.matrix ρ h (a h x,k) (x,j) := by
    apply Finset.sum_eq_single (a h x)
    · intro z _ hz
      simp only [matrix,ite_eq_right hz,mul_zero,Finset.sum_const_zero]
    · simp
  rw [hs]
  by_cases he : y=a (g*h) x
  · have he' : y=a g (a h x) := by simpa only [map_mul,Equiv.Perm.mul_apply] using he
    simp only [matrix,ite_eq_left he,ite_eq_left he',ite_true]
    rw [C.cocycle_mul,map_mul,Matrix.mul_apply]
  · have he' : ¬ y=a g (a h x) := by simpa only [map_mul,Equiv.Perm.mul_apply] using he
    simp only [matrix,ite_eq_right he,ite_eq_right he',zero_mul,Finset.sum_const_zero]

omit [Fintype G] [Fintype Ω] in
lemma matrix_one : C.matrix ρ 1=1 := by
  ext y x
  rcases y with ⟨y,i⟩
  rcases x with ⟨x,j⟩
  simp only [matrix,map_one,Equiv.Perm.one_apply,C.cocycle_one,Matrix.one_apply,Prod.mk.injEq]
  by_cases hy : y=x <;> by_cases hi : i=j <;> simp [hy,hi]

def action : G →* Matrix (Ω × Fin ρ.dimension) (Ω × Fin ρ.dimension) ℂ where
  toFun := C.matrix ρ
  map_one' := C.matrix_one ρ
  map_mul' := C.matrix_mul ρ

end Chart
end CoordinateSweeps.PlacementInduction

namespace CoordinateSweeps.PlacementInduction.Chart
variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
    {a : G →* Equiv.Perm Ω} (C : Chart a)

omit [Fintype G] [Fintype Ω] [DecidableEq Ω] in
lemma invrep_reaches (x : Ω) : a (C.rep x)⁻¹ x=C.base := by
  rw [map_inv,Equiv.Perm.coe_inv]
  exact (Equiv.symm_apply_eq _).mpr (C.reaches x).symm

/- Actual orbit--stabilizer decomposition, including its fiber cardinal factor. -/
def decompose : G ≃ Ω × C.stabilizer where
  toFun g := (a g C.base,⟨(C.rep (a g C.base))⁻¹*g,by
    change a ((C.rep (a g C.base))⁻¹*g) C.base=C.base
    rw [map_mul,Equiv.Perm.mul_apply,C.invrep_reaches]⟩)
  invFun x := C.rep x.1*x.2.val
  left_inv g := by
    change C.rep (a g C.base)*((C.rep (a g C.base))⁻¹*g)=g
    group
  right_inv x := by
    rcases x with ⟨x,h⟩
    have hx : a (C.rep x*h.val) C.base=x := by
      rw [map_mul,Equiv.Perm.mul_apply,h.property,C.reaches]
    apply Prod.ext
    · exact hx
    · apply Subtype.ext
      change (C.rep (a (C.rep x*h.val) C.base))⁻¹*(C.rep x*h.val)=h.val
      rw [hx]
      group

def fixedEquiv (x : Ω) : C.stabilizer ≃ {g : G // a g x=x} where
  toFun h := ⟨C.rep x*h.val*(C.rep x)⁻¹,by
    rw [map_mul,map_mul,Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,C.invrep_reaches,
      h.property,C.reaches]⟩
  invFun g := ⟨(C.rep x)⁻¹*g.val*C.rep x,by
    change a ((C.rep x)⁻¹*g.val*C.rep x) C.base=C.base
    rw [map_mul,map_mul,Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,C.reaches,g.property,C.invrep_reaches]⟩
  left_inv h := by
    apply Subtype.ext
    change (C.rep x)⁻¹*(C.rep x*h.val*(C.rep x)⁻¹)*C.rep x=h.val
    group
  right_inv g := by
    apply Subtype.ext
    change C.rep x*((C.rep x)⁻¹*g.val*C.rep x)*(C.rep x)⁻¹=g.val
    group

end CoordinateSweeps.PlacementInduction.Chart

namespace CoordinateSweeps.OrderedPlacements
variable {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]

def action : Equiv.Perm X →* Equiv.Perm (I ↪ X) where
  toFun g :=
    { toFun := fun x => x.trans g.toEmbedding
      invFun := fun x => x.trans g.symm.toEmbedding
      left_inv := fun x => by ext i; simp
      right_inv := fun x => by ext i; simp }
  map_one' := by ext x i; rfl
  map_mul' g h := by ext x i; rfl

omit [Fintype I] [Fintype X] [DecidableEq X] in
@[simp] lemma action_apply (g : Equiv.Perm X) (x : I ↪ X) (i : I) : action g x i=g (x i) := rfl

def rangeEquiv (x0 x : I ↪ X) : Set.range x0 ≃ Set.range x :=
  (Equiv.ofInjective x0 x0.injective).symm.trans (Equiv.ofInjective x x.injective)

omit [Fintype I] [Fintype X] [DecidableEq X] in
lemma rangeEquiv_apply (x0 x : I ↪ X) (i : I) :
    (rangeEquiv x0 x ⟨x0 i,⟨i,rfl⟩⟩).val=x i := by
  have he : (Equiv.ofInjective x0 x0.injective).symm ⟨x0 i,⟨i,rfl⟩⟩=i :=
    (Equiv.ofInjective x0 x0.injective).symm_apply_apply i
  change x ((Equiv.ofInjective x0 x0.injective).symm ⟨x0 i,⟨i,rfl⟩⟩)=x i
  rw [he]

/- Every ordered placement is reached by an actual permutation extending the
bijection on its marked positions. No cardinal or transitivity axiom is used. -/
def chart (x0 : I ↪ X) : PlacementInduction.Chart (action (I := I) (X := X)) where
  base := x0
  rep x := Equiv.extendSubtype (rangeEquiv x0 x)
  reaches x := by
    ext i
    change Equiv.extendSubtype (rangeEquiv x0 x) (x0 i)=x i
    rw [Equiv.extendSubtype_apply_of_mem _ _ (show x0 i ∈ Set.range x0 from ⟨i,rfl⟩)]
    exact rangeEquiv_apply x0 x i

end CoordinateSweeps.OrderedPlacements

namespace CoordinateSweeps.PlacementInduction.Chart
open UnitaryIrrep
variable {G Ω W : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω] [Fintype W]
    {a : G →* Equiv.Perm Ω} (C : Chart a)

def transition (_ : Chart a) (w : W → ℝ) (g : W → G) (y x : Ω) : ℝ :=
  ∑ ω, if y=a (g ω) x then w ω else 0

def conditionalBlock (ρ : UnitaryIrrep C.stabilizer) (w : W → ℝ) (g : W → G) (y x : Ω) :
    Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ :=
  (C.transition w g y x : ℂ)⁻¹ •
    ∑ ω, if y=a (g ω) x then (w ω : ℂ) • ρ.matrix (C.cocycle (g ω) x) else 0

end CoordinateSweeps.PlacementInduction.Chart

namespace CoordinateSweeps.PlacementInduction.Chart
variable {G Ω W : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω] [Fintype W]
    {a : G →* Equiv.Perm Ω} (C : Chart a)

def pointFix (_ : Chart a) (x : Ω) : Subgroup G where
  carrier g := a g x=x
  one_mem' := by change a 1 x=x; simp
  mul_mem' {g h} hg hh := by change a (g*h) x=x; rw [map_mul,Equiv.Perm.mul_apply,hh,hg]
  inv_mem' {g} hg := by
    change a g⁻¹ x=x
    rw [map_inv,Equiv.Perm.coe_inv]
    exact (Equiv.symm_apply_eq _).mpr hg.symm

def pointEquiv (x : Ω) : C.stabilizer ≃* C.pointFix x where
  toEquiv := C.fixedEquiv x
  map_mul' h k := by
    apply Subtype.ext
    change C.rep x*(h.val*k.val)*(C.rep x)⁻¹=
      (C.rep x*h.val*(C.rep x)⁻¹)*(C.rep x*k.val*(C.rep x)⁻¹)
    group

/- The remaining symmetric-group type transported to the actual input placement. -/
def pointIrrep (ρ : UnitaryIrrep C.stabilizer) (x : Ω) : UnitaryIrrep (C.pointFix x) where
  dimension := ρ.dimension
  positive := ρ.positive
  matrix := ρ.matrix.comp (C.pointEquiv x).symm.toMonoidHom
  unitary g := ρ.unitary _
  irreducible S hS := ρ.irreducible S (by
    intro g v hv
    have hh := hS (C.pointEquiv x g) v hv
    change (ρ.matrix ((C.pointEquiv x).symm (C.pointEquiv x g))).mulVec v ∈ S at hh
    simpa only [MulEquiv.symm_apply_apply] using hh)

def transitionResidual (x y : Ω) (g₀ g : G) (h₀ : y=a g₀ x) (hg : y=a g x) : C.pointFix x :=
  ⟨g₀⁻¹*g,by
    change a (g₀⁻¹*g) x=x
    rw [map_mul,Equiv.Perm.mul_apply,← hg,h₀,map_inv,Equiv.Perm.coe_inv,Equiv.symm_apply_apply]⟩

def transitionAverage (ρ : UnitaryIrrep C.stabilizer) (w : W → ℝ) (g : W → G)
    (x y : Ω) (ω₀ : W) (h₀ : y=a (g ω₀) x) : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ :=
  (C.transition w g y x : ℂ)⁻¹ • ∑ ω : {ω : W // y=a (g ω) x},
    (w ω.val : ℂ) • ρ.matrix
      ((C.pointEquiv x).symm (C.transitionResidual x y (g ω₀) (g ω.val) h₀ ω.property))

/- Exact moving-frame identity for each normalized block. -/

end CoordinateSweeps.PlacementInduction.Chart

end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_PlacementMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.Grid.Holes
open PlacementInduction
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

abbrev Placement := Fin k ↪ H.FreeAt 0

def placementAction : H.stabilizer →* Equiv.Perm (H.Placement (k := k)) :=
  OrderedPlacements.action.comp H.stabilizerFreeEquiv.toMonoidHom

def placementChart (u : H.Placement (k := k)) : Chart (H.placementAction (k := k)) where
  base := u
  rep x := H.stabilizerFreeEquiv.symm ((OrderedPlacements.chart u).rep x)
  reaches x := by
    change OrderedPlacements.action (H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm
      ((OrderedPlacements.chart u).rep x))) u=x
    rw [MulEquiv.apply_symm_apply]
    exact (OrderedPlacements.chart u).reaches x

lemma placement_valid (x : H.Placement (k := k)) : H.ValidInput (fun i => (x i).val) := by
  refine ⟨?_,?_⟩
  · intro i j he
    exact x.injective (Subtype.ext he)
  · intro i a
    exact (x i).property a

lemma pointFix_iff (u x : H.Placement (k := k)) (g : H.stabilizer) :
    g ∈ (H.placementChart u).pointFix x ↔ ∀ i, g.val (x i).val=(x i).val := by
  change H.placementAction g x=x ↔ _
  constructor
  · intro hh i
    exact congrArg (fun z : H.Placement (k := k) => (z i).val) hh
  · intro hh
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact hh i

variable (u x : H.Placement (k := k)) (v : Fin k → G.Slot)
    (ω₀ : G.Choices) (h₀ : H.Compatible ω₀) (hv : ∀ i, G.sweep ω₀ (x i).val=v i)

/- The point--placement stabilizer is the literal stabilizer of all augmented
holes, not an abstract group with the same cardinality. -/
def augmentFixEquiv : (H.placementChart u).pointFix x ≃*
    (H.augment (fun i => (x i).val) v (H.placement_valid x) ω₀ h₀ hv).stabilizer where
  toFun g := ⟨g.val.val,by
    intro i
    cases i using Fin.addCases with
    | left a => simpa only [augment_old] using g.val.property a
    | right a =>
      simpa only [augment_new,Grid.pathBetween_zero] using
        (H.pointFix_iff u x g.val).mp g.property a⟩
  invFun g := ⟨⟨g.val,by
    intro i
    exact (show g.val (H.path i 0)=H.path i 0 by simpa only [augment_old] using g.property (Fin.castAdd k i))⟩,
    (H.pointFix_iff u x _).mpr (fun i => by
      simpa only [augment_new,Grid.pathBetween_zero] using g.property (Fin.natAdd h i))⟩
  left_inv g := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv g := by apply Subtype.ext; rfl
  map_mul' g l := by apply Subtype.ext; rfl

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open PlacementInduction
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

def augmented (x : H.Placement (k := k)) (ω₀ : {ω : G.Choices // H.Compatible ω}) : G.Holes (h+k) :=
  H.augment (fun i => (x i).val) (fun i => G.sweep ω₀.val (x i).val)
    (H.placement_valid x) ω₀.val ω₀.property (fun _ => rfl)

lemma augmented_compatible (x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) (ω : G.Choices) :
    (H.augmented x ω₀).Compatible ω ↔ H.Compatible ω ∧
      ∀ i, G.sweep ω (x i).val=G.sweep ω₀.val (x i).val :=
  H.augment_compatible_iff _ _ _ _ _ _ _

def augmentedReference (x : H.Placement (k := k)) (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    {ω : G.Choices // (H.augmented x ω₀).Compatible ω} :=
  ⟨ω₀.val,(H.augmented_compatible x ω₀ ω₀.val).mpr ⟨ω₀.property,fun _ => rfl⟩⟩

lemma augmented_feasible (x : H.Placement (k := k)) (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    (H.augmented x ω₀).Feasible := ⟨ω₀.val,(H.augmentedReference x ω₀).property⟩

lemma transition_event (hf : H.Feasible) (x : H.Placement (k := k))
    (ω₀ ω : {ω : G.Choices // H.Compatible ω}) :
    H.placementAction (H.residual hf ω₀) x=H.placementAction (H.residual hf ω) x ↔
      ∀ i, G.sweep ω.val (x i).val=G.sweep ω₀.val (x i).val := by
  constructor
  · intro hh i
    have hi := congrArg (fun z : H.Placement (k := k) => (z i).val) hh
    change (G.sweep (H.reference hf)).symm (G.sweep ω₀.val (x i).val)=
      (G.sweep (H.reference hf)).symm (G.sweep ω.val (x i).val) at hi
    exact ((G.sweep (H.reference hf)).symm.injective hi).symm
  · intro hh
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    change (G.sweep (H.reference hf)).symm (G.sweep ω₀.val (x i).val)=
      (G.sweep (H.reference hf)).symm (G.sweep ω.val (x i).val)
    rw [hh i]

/- Conditioning on a placement transition is exactly conditioning on the full,
unique augmented coordinate paths, not an endpoint approximation. -/
def augmentedChoices (hf : H.Feasible) (x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    {ω : {ω : G.Choices // H.Compatible ω} //
      H.placementAction (H.residual hf ω₀) x=H.placementAction (H.residual hf ω) x} ≃
    {ω : G.Choices // (H.augmented x ω₀).Compatible ω} where
  toFun ω := ⟨ω.val.val,(H.augmented_compatible x ω₀ ω.val.val).mpr
    ⟨ω.val.property,(H.transition_event hf x ω₀ ω.val).mp ω.property⟩⟩
  invFun ω := ⟨⟨ω.val,((H.augmented_compatible x ω₀ ω.val).mp ω.property).1⟩,
    (H.transition_event hf x ω₀ _).mpr ((H.augmented_compatible x ω₀ ω.val).mp ω.property).2⟩
  left_inv ω := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv ω := by apply Subtype.ext; rfl

/- A concrete cardinal-free group identity behind the conditional-fiber frame. -/

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open PlacementInduction
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

def placementWeight (z : ℝ) (ω : {ω : G.Choices // H.Compatible ω}) : ℝ :=
  G.choiceWeight z ω.val/H.probability z

def augmentedIrrep (u x : H.Placement (k := k))
    (ω₀ : {ω : G.Choices // H.Compatible ω})
    (ρ : UnitaryIrrep (H.placementChart u).stabilizer) : UnitaryIrrep (H.augmented x ω₀).stabilizer :=
  ((H.placementChart u).pointIrrep ρ x).pullback
    (H.augmentFixEquiv u x (fun i => G.sweep ω₀.val (x i).val) ω₀.val ω₀.property (fun _ => rfl)).symm

end CoordinateSweeps.Grid.Holes

noncomputable section
open Set Complex
open scoped BigOperators Topology

open scoped Matrix.Norms.L2Operator

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps

variable {Ω : Type*} [Fintype Ω]

def tupleSplit (n : ℕ) : (Fin (n+1) → Ω) ≃ Ω × (Fin n → Ω) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv x := by cases x; rfl

def chainWeight {n : ℕ} (P : Fin n → Ω → Ω → ℝ) (x : Fin (n+1) → Ω) : ℝ :=
  ∏ i, P i (x i.castSucc) (x i.succ)

def deletedCycle {n : ℕ} (P : Fin (n+1) → Ω → Ω → ℝ)
    (x : Fin (n+1) → Ω) (r : Fin (n+1)) : ℝ :=
  ∏ i, if i = r then 1 else P i (x i) (x (i+1))

def tupleReindex {n : ℕ} (e : Equiv.Perm (Fin n)) : (Fin n → Ω) ≃ (Fin n → Ω) where
  toFun x := fun i => x (e i)
  invFun x := fun i => x (e.symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

end CoordinateSweeps

end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Young_Restriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.CommutingRestriction
variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- The action of a commuting group on the multiplicity space. -/
def homAction (τ : Representation ℂ G V) (σ : Representation ℂ H V)
    (hc : ∀ g h, Commute (τ g) (σ h)) (ρ : Representation ℂ G W) :
    Representation ℂ H (ρ.IntertwiningMap τ) where
  toFun h :=
    { toFun f :=
        { toLinearMap := σ h ∘ₗ f.toLinearMap
          isIntertwining' g := by
            rw [LinearMap.comp_assoc,f.isIntertwining',← LinearMap.comp_assoc]
            exact congrArg (fun B : Module.End ℂ V => B ∘ₗ f.toLinearMap) (hc g h).eq.symm }
      map_add' f g := by ext w; simp
      map_smul' c f := by ext w; simp }
  map_one' := by ext f w; simp
  map_mul' h k := by ext f w; simp [map_mul]

@[simp] lemma homAction_apply (τ : Representation ℂ G V) (σ : Representation ℂ H V)
    (hc : ∀ g h, Commute (τ g) (σ h)) (ρ : Representation ℂ G W)
    (h : H) (f : ρ.IntertwiningMap τ) (w : W) : homAction τ σ hc ρ h f w=σ h (f w) := rfl

def inclusion (τ : Representation ℂ G V) (S : Subrepresentation τ) :
    S.toRepresentation.IntertwiningMap τ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

end CoordinateSweeps.CommutingRestriction

namespace CoordinateSweeps.YoungCorner

def hookPart (μ : YoungDiagram) (p : ℕ) : YoungDiagram where
  cells := μ.cells.filter (fun x => x.1<p ∨ x.2<p)
  isLowerSet := by
    intro a b hab hb
    obtain ⟨hμ,hp⟩:=Finset.mem_filter.mp hb
    refine Finset.mem_filter.mpr ⟨μ.isLowerSet hab hμ,?_⟩
    rcases hp with h|h
    · exact Or.inl (lt_of_le_of_lt hab.1 h)
    · exact Or.inr (lt_of_le_of_lt hab.2 h)

@[simp] lemma mem_hookPart (μ : YoungDiagram) (p : ℕ) (x : ℕ × ℕ) :
    x ∈ hookPart μ p ↔ x ∈ μ ∧ (x.1<p ∨ x.2<p) := by
  exact Finset.mem_filter

def shifted (p : ℕ) (x : ℕ × ℕ) : ℕ × ℕ := (x.1+p,x.2+p)
lemma shifted_injective (p : ℕ) : Function.Injective (shifted p) := by
  intro x y h
  apply Prod.ext
  · exact Nat.add_right_cancel (congrArg Prod.fst h)
  · exact Nat.add_right_cancel (congrArg Prod.snd h)

def removedPart (μ : YoungDiagram) (p : ℕ) : YoungDiagram where
  cells := μ.cells.preimage (shifted p) (shifted_injective p).injOn
  isLowerSet := by
    intro a b hab hb
    apply Finset.mem_preimage.mpr
    apply μ.isLowerSet (show shifted p b ≤ shifted p a from ⟨Nat.add_le_add_right hab.1 p,Nat.add_le_add_right hab.2 p⟩)
    exact Finset.mem_preimage.mp hb

@[simp] lemma mem_removedPart (μ : YoungDiagram) (p : ℕ) (x : ℕ × ℕ) :
    x ∈ removedPart μ p ↔ shifted p x ∈ μ := by
  change x ∈ μ.cells.preimage (shifted p) (shifted_injective p).injOn ↔ _
  exact Finset.mem_preimage

def boxesSplit (μ : YoungDiagram) (p : ℕ) :
    Boxes (hookPart μ p) ⊕ Boxes (removedPart μ p) ≃ Boxes μ where
  toFun x := match x with
    | Sum.inl x => ⟨x.val,(mem_hookPart μ p x.val).mp x.property |>.1⟩
    | Sum.inr x => ⟨shifted p x.val,(mem_removedPart μ p x.val).mp x.property⟩
  invFun x := if h : x.val.1<p ∨ x.val.2<p then
    Sum.inl ⟨x.val,(mem_hookPart μ p x.val).mpr ⟨x.property,h⟩⟩ else
    Sum.inr ⟨(x.val.1-p,x.val.2-p),(mem_removedPart μ p _).mpr (by
      have hx : p≤x.val.1 ∧ p≤x.val.2 := by push Not at h; exact h
      simp [shifted,Nat.sub_add_cancel hx.1,Nat.sub_add_cancel hx.2])⟩
  left_inv := by
    intro x
    cases x with
    | inl x =>
      have hx: x.val.1<p ∨ x.val.2<p := ((mem_hookPart μ p x.val).mp x.property).2
      simp only [dite_eq_left hx]
    | inr x =>
      simp [shifted]
  right_inv := by
    intro x
    dsimp
    split_ifs with h
    · rfl
    · apply Subtype.ext
      have hx : p≤x.val.1 ∧ p≤x.val.2 := by push Not at h; exact h
      simp [shifted,Nat.sub_add_cancel hx.1,Nat.sub_add_cancel hx.2]

@[simp] lemma boxesSplit_inl (μ : YoungDiagram) (p : ℕ) (x : Boxes (hookPart μ p)) :
    (boxesSplit μ p (Sum.inl x)).val=x.val := rfl
@[simp] lemma boxesSplit_inr (μ : YoungDiagram) (p : ℕ) (x : Boxes (removedPart μ p)) :
    (boxesSplit μ p (Sum.inr x)).val=shifted p x.val := rfl

variable {X Y Z : Type*}

def leftPerm (e : Y ⊕ Z ≃ X) : Equiv.Perm Y →* Equiv.Perm X where
  toFun g := e.permCongr (Equiv.sumCongr g (Equiv.refl Z))
  map_one' := by
    ext x
    obtain ⟨y,rfl⟩:=e.surjective x
    cases y <;> simp [Equiv.permCongr_apply]
  map_mul' g h := by
    ext x
    obtain ⟨y,rfl⟩:=e.surjective x
    cases y <;> simp [Equiv.permCongr_apply]

def rightPerm (e : Y ⊕ Z ≃ X) : Equiv.Perm Z →* Equiv.Perm X where
  toFun g := e.permCongr (Equiv.sumCongr (Equiv.refl Y) g)
  map_one' := by
    ext x
    obtain ⟨y,rfl⟩:=e.surjective x
    cases y <;> simp [Equiv.permCongr_apply]
  map_mul' g h := by
    ext x
    obtain ⟨y,rfl⟩:=e.surjective x
    cases y <;> simp [Equiv.permCongr_apply]

@[simp] lemma leftPerm_inl (e : Y ⊕ Z ≃ X) (g : Equiv.Perm Y) (x : Y) :
    leftPerm e g (e (Sum.inl x))=e (Sum.inl (g x)) := by simp [leftPerm,Equiv.permCongr_apply]
@[simp] lemma leftPerm_inr (e : Y ⊕ Z ≃ X) (g : Equiv.Perm Y) (x : Z) :
    leftPerm e g (e (Sum.inr x))=e (Sum.inr x) := by simp [leftPerm,Equiv.permCongr_apply]
@[simp] lemma rightPerm_inl (e : Y ⊕ Z ≃ X) (g : Equiv.Perm Z) (x : Y) :
    rightPerm e g (e (Sum.inl x))=e (Sum.inl x) := by simp [rightPerm,Equiv.permCongr_apply]
@[simp] lemma rightPerm_inr (e : Y ⊕ Z ≃ X) (g : Equiv.Perm Z) (x : Z) :
    rightPerm e g (e (Sum.inr x))=e (Sum.inr (g x)) := by simp [rightPerm,Equiv.permCongr_apply]

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

lemma split_card (μ : YoungDiagram) (p : ℕ) :
    Fintype.card (Boxes (hookPart μ p))+Fintype.card (Boxes (removedPart μ p))=
      Fintype.card (Boxes μ) := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (boxesSplit μ p)

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

omit [Fintype X] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
lemma leftPerm_range_of_fix_right (e : Y ⊕ Z ≃ X) (g : Equiv.Perm X)
    (hfix : ∀ z, g (e (Sum.inr z))=e (Sum.inr z)) : ∃ h, leftPerm e h=g := by
  let g' := e.permCongr.symm g
  have hf (z : Z) : g' (Sum.inr z)=Sum.inr z := by
    change e.symm (g (e (Sum.inr z)))=Sum.inr z
    rw [hfix,Equiv.symm_apply_apply]
  have hmaps : Set.MapsTo g' (Set.range Sum.inr) (Set.range Sum.inr) := by
    rintro x ⟨z,rfl⟩
    exact ⟨z,(hf z).symm⟩
  have hm:=Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
    ((Equiv.Perm.perm_mapsTo_inl_iff_mapsTo_inr g').mpr hmaps)
  obtain ⟨⟨h,k⟩,he⟩:=hm
  have hk : k=1 := by
    apply Equiv.ext
    intro z
    have hh:=congrArg (fun q : Equiv.Perm (Y ⊕ Z) => q (Sum.inr z)) he
    simpa only [Equiv.Perm.sumCongrHom_apply,Equiv.sumCongr_apply,Sum.map_inr,hf,Sum.inr.injEq,Equiv.Perm.one_apply] using hh
  refine ⟨h,?_⟩
  subst k
  change e.permCongr (Equiv.sumCongr h (Equiv.refl Z))=g
  calc
    _ = e.permCongr g' := congrArg e.permCongr he
    _ = g := e.permCongr.apply_symm_apply g

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable {X Y V : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup V] [Module ℂ V]
def colorEquiv (e : X ≃ Y) (f : Y → ℕ) : colorStabilizer (fun x => f (e x)) ≃* colorStabilizer f where
  toFun g := ⟨e.permCongrHom g.val,by
    intro y
    simpa using g.property (e.symm y)⟩
  invFun g := ⟨e.symm.permCongrHom g.val,by
    intro x
    simpa using g.property (e x)⟩
  left_inv g := by apply Subtype.ext; apply Equiv.ext; intro x; simp
  right_inv g := by apply Subtype.ext; apply Equiv.ext; intro y; simp
  map_mul' g h := by apply Subtype.ext; exact map_mul e.permCongrHom g.val h.val
end CoordinateSweeps.YoungCorner

namespace Representation.IntertwiningMap
open scoped _root_.Representation _root_.Representation.IntertwiningMap
variable {Γ Λ V W : Type*} [Monoid Γ] [Monoid Λ] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
/- Reparameterizing a group does not alter the Hom multiplicity. -/
def reparamEquiv (ρ : Representation ℂ Γ V) (τ : Representation ℂ Γ W) (e : Λ ≃* Γ) :
    ρ.IntertwiningMap τ ≃ₗ[ℂ] Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (τ.comp e.toMonoidHom) where
  toFun f := ⟨f.toLinearMap,fun g => f.isIntertwining' (e g)⟩
  invFun f := ⟨f.toLinearMap,fun g => by
    have h := f.isIntertwining' (e.symm g)
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply] using h⟩
  left_inv f := rfl
  right_inv f := rfl
  map_add' f g := rfl
  map_smul' c f := rfl

/- Changing the source realization by an equivalence preserves Hom. -/
def sourceEquiv {U : Type*} [AddCommGroup U] [Module ℂ U]
    {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ U}
    (e : Representation.Equiv ρ σ) (τ : Representation ℂ Γ W) :
    ρ.IntertwiningMap τ ≃ₗ[ℂ] σ.IntertwiningMap τ where
  toFun f := f.comp e.symm.toIntertwiningMap
  invFun f := f.comp e.toIntertwiningMap
  left_inv f := by ext v; simp
  right_inv f := by ext v; simp
  map_add' f g := by ext v; rfl
  map_smul' c f := by ext v; rfl
end Representation.IntertwiningMap

end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Attachment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.Grid.Holes
open YoungCorner PlacementInduction UnitaryIrrep
variable {G : Grid} {h : ℕ} (H : G.Holes h) (μ : YoungDiagram) (p : ℕ)
    (e : H.FreeAt 0 ≃ Boxes μ)
def removedPlacement : H.Placement (k := Fintype.card (Boxes (removedPart μ p))) where
  toFun i := e.symm (boxesSplit μ p (Sum.inr ((Fintype.equivFin _).symm i)))
  inj' := by
    intro i j hij
    have h₁ := e.symm.injective hij
    have h₂ := (boxesSplit μ p).injective h₁
    exact (Fintype.equivFin _).symm.injective (Sum.inr.inj h₂)
def retainedMap : Equiv.Perm (Boxes (hookPart μ p)) →* H.stabilizer :=
  H.stabilizerFreeEquiv.symm.toMonoidHom.comp
    (e.symm.permCongrHom.toMonoidHom.comp (leftPerm (boxesSplit μ p)))
lemma retainedMap_fixed (g : Equiv.Perm (Boxes (hookPart μ p))) :
    H.placementAction (H.retainedMap μ p e g) (H.removedPlacement μ p e)=H.removedPlacement μ p e := by
  apply Function.Embedding.ext
  intro i
  change H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm
    (e.symm.permCongrHom (leftPerm (boxesSplit μ p) g)))
    (e.symm (boxesSplit μ p (Sum.inr ((Fintype.equivFin _).symm i))))=_
  rw [MulEquiv.apply_symm_apply]
  simp [leftPerm,removedPlacement]
  rfl
def retainedInto : Equiv.Perm (Boxes (hookPart μ p)) →*
    (H.placementChart (H.removedPlacement μ p e)).stabilizer where
  toFun g := ⟨H.retainedMap μ p e g,H.retainedMap_fixed μ p e g⟩
  map_one' := by apply Subtype.ext; exact map_one (H.retainedMap μ p e)
  map_mul' g g' := by apply Subtype.ext; exact map_mul (H.retainedMap μ p e) g g'
lemma retainedInto_bijective : Function.Bijective (H.retainedInto μ p e) := by
  constructor
  · intro g g' hh
    have heq := congrArg (fun t => e.permCongrHom (H.stabilizerFreeEquiv t.val)) hh
    change e.permCongrHom (H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm
      (e.symm.permCongrHom (leftPerm (boxesSplit μ p) g))))=
      e.permCongrHom (H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm
      (e.symm.permCongrHom (leftPerm (boxesSplit μ p) g')))) at heq
    simp only [MulEquiv.apply_symm_apply] at heq
    have hleft : leftPerm (boxesSplit μ p) g=leftPerm (boxesSplit μ p) g' := by simpa using heq
    apply Equiv.ext
    intro x
    have hx := congrArg (fun t : Equiv.Perm (Boxes μ) => (boxesSplit μ p).symm (t (boxesSplit μ p (Sum.inl x)))) hleft
    simpa [leftPerm] using hx
  · intro g
    have hfix : ∀ z : Boxes (removedPart μ p),
        e.permCongrHom (H.stabilizerFreeEquiv g.val) (boxesSplit μ p (Sum.inr z))=boxesSplit μ p (Sum.inr z) := by
      intro z
      have hh := congrArg (fun u : H.Placement (k := Fintype.card (Boxes (removedPart μ p))) => e (u ((Fintype.equivFin _) z))) g.property
      change e ((H.stabilizerFreeEquiv g.val) (e.symm (boxesSplit μ p (Sum.inr ((Fintype.equivFin _).symm ((Fintype.equivFin _) z))))))=e (e.symm (boxesSplit μ p (Sum.inr ((Fintype.equivFin _).symm ((Fintype.equivFin _) z))))) at hh
      change e ((H.stabilizerFreeEquiv g.val) (e.symm (boxesSplit μ p (Sum.inr z))))=_
      simpa only [Equiv.symm_apply_apply,Equiv.apply_symm_apply] using hh
    obtain ⟨a,ha⟩ := leftPerm_range_of_fix_right (boxesSplit μ p)
      (e.permCongrHom (H.stabilizerFreeEquiv g.val)) hfix
    refine ⟨a,?_⟩
    apply Subtype.ext
    apply H.stabilizerFreeEquiv.injective
    change H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm
      (e.symm.permCongrHom (leftPerm (boxesSplit μ p) a)))=H.stabilizerFreeEquiv g.val
    rw [MulEquiv.apply_symm_apply,ha]
    apply Equiv.ext
    intro y
    simp
/- Actual retained-hook subgroup chart inside the original hole stabilizer. -/
def retainedEquiv : Equiv.Perm (Boxes (hookPart μ p)) ≃*
    (H.placementChart (H.removedPlacement μ p e)).stabilizer :=
  MulEquiv.ofBijective (H.retainedInto μ p e) (H.retainedInto_bijective μ p e)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open YoungCorner PlacementInduction UnitaryIrrep
variable {G : Grid} {h : ℕ} (H : G.Holes h) (μ : YoungDiagram) (p : ℕ)
    (e : H.FreeAt 0 ≃ Boxes μ)
def boxesChart : Equiv.Perm (Boxes μ) ≃* H.stabilizer :=
  e.symm.permCongrHom.trans H.stabilizerFreeEquiv.symm

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open YoungCorner PlacementInduction UnitaryIrrep
variable {G : Grid} {h : ℕ} (H : G.Holes h) (μ : YoungDiagram) (p : ℕ)
    (e : H.FreeAt 0 ≃ Boxes μ)
def retainedSite : Boxes (hookPart μ p) ↪ H.FreeAt 0 where
  toFun a := e.symm (boxesSplit μ p (Sum.inl a))
  inj' := by intro a b hh; exact Sum.inl.inj ((boxesSplit μ p).injective (e.symm.injective hh))
lemma retainedSite_ne_removed (a : Boxes (hookPart μ p))
    (i : Fin (Fintype.card (Boxes (removedPart μ p)))) :
    H.retainedSite μ p e a ≠ H.removedPlacement μ p e i := by
  intro hh
  have he := (boxesSplit μ p).injective (e.symm.injective hh)
  cases he

def augmentedRetainedEmbedding
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    Boxes (hookPart μ p) ↪ (H.augmented x ω₀).FreeAt 0 where
  toFun a := ⟨(H.stabilizerFreeEquiv ((H.placementChart (H.removedPlacement μ p e)).rep x)
    (H.retainedSite μ p e a)).val,by
    intro i
    cases i using Fin.addCases with
    | left i =>
      simpa only [augmented,augment_old] using
        (H.stabilizerFreeEquiv ((H.placementChart (H.removedPlacement μ p e)).rep x)
          (H.retainedSite μ p e a)).property i
    | right i =>
      simp only [augmented,augment_new,Grid.pathBetween_zero]
      intro he
      have hr := congrArg (fun y : H.Placement (k := Fintype.card (Boxes (removedPart μ p))) => (y i).val)
        ((H.placementChart (H.removedPlacement μ p e)).reaches x)
      change ((H.placementChart (H.removedPlacement μ p e)).rep x).val
        ((H.removedPlacement μ p e i).val)=(x i).val at hr
      have hh := ((H.placementChart (H.removedPlacement μ p e)).rep x).val.injective (he.trans hr.symm)
      exact H.retainedSite_ne_removed μ p e a i (Subtype.ext hh)⟩
  inj' := by
    intro a b hh
    have he := congrArg Subtype.val hh
    exact (H.retainedSite μ p e).injective
      ((H.stabilizerFreeEquiv ((H.placementChart (H.removedPlacement μ p e)).rep x)).injective (Subtype.ext he))

lemma augmentedRetainedEmbedding_surjective
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    Function.Surjective (H.augmentedRetainedEmbedding μ p e x ω₀) := by
  have hc : Fintype.card (Boxes (hookPart μ p))=Fintype.card ((H.augmented x ω₀).FreeAt 0) := by
    have hsplit := split_card μ p
    have he := Fintype.card_congr e
    rw [H.card_freeAt] at he
    rw [(H.augmented x ω₀).card_freeAt]
    omega
  by_contra hn
  have hh := Fintype.card_lt_of_injective_not_surjective _
    (H.augmentedRetainedEmbedding μ p e x ω₀).injective hn
  omega

def augmentedRetainedEquiv
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    Boxes (hookPart μ p) ≃ (H.augmented x ω₀).FreeAt 0 :=
  Equiv.ofBijective (H.augmentedRetainedEmbedding μ p e x ω₀)
    ⟨(H.augmentedRetainedEmbedding μ p e x ω₀).injective,
      H.augmentedRetainedEmbedding_surjective μ p e x ω₀⟩
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open YoungCorner PlacementInduction UnitaryIrrep
variable {G : Grid} {h : ℕ} (H : G.Holes h) (μ : YoungDiagram) (p : ℕ)
    (e : H.FreeAt 0 ≃ Boxes μ)
def augmentedRetainedChart
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    Equiv.Perm (Boxes (hookPart μ p)) ≃* (H.augmented x ω₀).stabilizer :=
  (H.augmentedRetainedEquiv μ p e x ω₀).permCongrHom.trans (H.augmented x ω₀).stabilizerFreeEquiv.symm
end CoordinateSweeps.Grid.Holes
end
end
end
end
end
end

/-!
Work on the genuinely missing main statements of the pinned manuscript.
All definitions are finite and use the source's ordinary probability and trace
normalizations. No result of the manuscript is assumed.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

/-! New work: the actual alternating placement kernel from 04-sparse:eq7.
The preceding definitions/proofs are reused verbatim from the pinned support.
Endpoints below need not be injections; invalid specifications have probability
zero automatically. On valid endpoint placements this is exactly the source Q. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/- Reused exact conditional transition/potential support from pinned root-02. -/

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}

def ValidOutput (H : G.Holes h) (y : Fin k → G.Slot) : Prop :=
  Function.Injective y ∧ ∀ i a, y i ≠ H.path a (Fin.last G.b)

/- Counting-measure Hilbert--Schmidt square on the actual free placements. -/
def placementHSsq (H : G.Holes h)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) : ℝ :=
  ∑ x : Fin k → G.Slot, ∑ y : Fin k → G.Slot,
    if H.ValidInput x ∧ H.ValidOutput y then (H.placementKernel x y μ)^2 else 0

/- The full endpoint product weight is exactly s^(-2k). -/

end CoordinateSweeps.Grid.Holes

/- Necessary shared-line polynomial expansion for the sparse conditional main.
A variable names a LINE, not a particle. The tensor moment functional is merely
linear, never multiplicative when two factors use the same line. -/
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Moments_LineExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace CoordinateSweeps.MomentExpansion
variable {L : Type*} [Fintype L] [DecidableEq L]

/- The moment functional of independent line variables, defined algebraically
so only the finitely many moments actually used need be integrable. -/
def tensorMoment (m : L → ℕ → ℝ) : MvPolynomial L ℝ →ₗ[ℝ] ℝ :=
  (MvPolynomial.basisMonomials L ℝ).constr ℝ (fun d => ∏ l, m l (d l))

omit [DecidableEq L] in
@[simp] theorem tensorMoment_monomial (m : L → ℕ → ℝ) (d : L →₀ ℕ) (a : ℝ) :
    tensorMoment m (monomial d a) = a * ∏ l, m l (d l) := by
  have hh : monomial d a = a • (MvPolynomial.basisMonomials L ℝ) d := by
    rw [MvPolynomial.coe_basisMonomials]
    rw [← map_smul]
    simp
  rw [hh, map_smul]
  change a • (((MvPolynomial.basisMonomials L ℝ).constr ℝ)
    (fun d => ∏ l, m l (d l))) ((MvPolynomial.basisMonomials L ℝ) d) = _
  rw [Module.Basis.constr_basis, smul_eq_mul]

omit [DecidableEq L] in
@[simp] theorem tensorMoment_one (m : L → ℕ → ℝ) (hm : ∀ l, m l 0 = 1) :
    tensorMoment m 1 = 1 := by
  rw [MvPolynomial.one_def, tensorMoment_monomial]
  simp [hm]

def shiftedMoment (m : L → ℕ → ℝ) (r : L → ℕ) : MvPolynomial L ℝ →ₗ[ℝ] ℝ :=
  (tensorMoment m).comp
    ((LinearMap.mulLeft ℝ (∏ l, (X l : MvPolynomial L ℝ)^r l)).comp
      (MvPolynomial.aeval (fun l => (X l : MvPolynomial L ℝ)-1)).toLinearMap)

def lineCenteredMoment (m : L → ℕ → ℝ) (l : L) (r u : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (u+1), (-1 : ℝ)^(a+u) * (u.choose a : ℝ) * m l (r+a)

end CoordinateSweeps.MomentExpansion

namespace CoordinateSweeps.MomentExpansion
variable {L : Type*} [Fintype L] [DecidableEq L]

def NonnegCoeffs (p : MvPolynomial L ℝ) : Prop := ∀ d, 0 ≤ p.coeff d

end CoordinateSweeps.MomentExpansion

namespace CoordinateSweeps.MomentExpansion
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {I J : Type*} [DecidableEq I] [Fintype J] [DecidableEq J]

/- Positive expansion for a centered particle factor. This is a sum over
NONEMPTY subsets of its stages; no independence of particle factors is used. -/
def pathExpansion (S : Finset J) (f : J → L) : MvPolynomial L ℝ :=
  ∑ T ∈ S.powerset.erase ∅, ∏ j ∈ T, X (f j)

def goodExpansion (G : Finset I) (path : I → J → L) : MvPolynomial L ℝ :=
  ∏ i ∈ G, pathExpansion Finset.univ (path i)

end CoordinateSweeps.MomentExpansion

namespace CoordinateSweeps.MomentExpansion
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {I J : Type*} [DecidableEq I] [Fintype J] [DecidableEq J]

def incidenceCount (A : Finset I) (path : I → J → L) (l : L) : ℕ :=
  ∑ i ∈ A, ∑ j : J, if path i j = l then 1 else 0

/- A monomial counts line uses, including simultaneous uses by distinct paths. -/

end CoordinateSweeps.MomentExpansion

/- Gamma-moment support. -/

/- The analytic light-line obligation 04-sparse.tex (11).  The distribution
is exactly Mathlib's Gamma(shape, unit rate), not an assumed random variable. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators

namespace CoordinateSweeps.MomentExpansion
open MeasureTheory ProbabilityTheory Real

/- Source light-line factorial moment, with its exact finite-population shift. -/
def fallingMoment (m h n : ℕ) : ℝ := (m : ℝ)^n / ((m-h).descFactorial n : ℝ)

@[simp] theorem fallingMoment_zero (m h : ℕ) : fallingMoment m h 0 = 1 := by
  simp [fallingMoment]

/- The algebraic moment is the ACTUAL inverse-gamma moment in every used degree. -/

end CoordinateSweeps.MomentExpansion

end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_TrajectoryMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
namespace CoordinateSweeps.Grid.Holes
open MomentExpansion
variable {G : Grid} {h k : ℕ}

def auxCount (x y : Fin k → G.Slot) (A : Finset (Fin k)) (j : Fin G.b) (L : G.Line j) : ℕ :=
  (A.filter (fun i => G.pathLine (x i) (y i) j = L)).card

def EndpointPossible (H : G.Holes h) (x y : Fin k → G.Slot) (A : Finset (Fin k)) : Prop :=
  ∃ ω, H.Compatible ω ∧ G.endpointEvent x y A ω

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}

/- Geometric validity at EVERY boundary, not only at endpoints. -/
def JointDisjoint (H : G.Holes h) (x y : Fin k → G.Slot) (A : Finset (Fin k)) : Prop :=
  (∀ i ∈ A, ∀ a s, G.pathBetween (x i) (y i) s ≠ H.path a s) ∧
  (∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∀ s,
    G.pathBetween (x i) (y i) s ≠ G.pathBetween (x j) (y j) s)

/- Build the augmented hole family directly from disjoint geometry. -/
def adjoin (H : G.Holes h) (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (hv : H.JointDisjoint x y A) : G.Holes (h+A.card) where
  path i s := Fin.append (fun a => H.path a s)
    (fun a => G.pathBetween (x (selected A a)) (y (selected A a)) s) i
  disjoint s := by
    apply Fin.append_injective_iff.mpr
    refine ⟨H.disjoint s, ?_, ?_⟩
    · intro a b he
      apply (selected A).injective
      by_contra hab
      exact hv.2 (selected A a) (selected_mem A a) (selected A b) (selected_mem A b) hab s he
    · intro a b he
      exact hv.1 (selected A b) (selected_mem A b) a s he.symm
  coordinate_step i j l hlj := by
    cases i using Fin.addCases with
    | left a => simpa using H.coordinate_step a j l hlj
    | right a => simpa using G.pathBetween_step (x (selected A a)) (y (selected A a)) j l hlj

@[simp] theorem adjoin_old (H : G.Holes h) (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (hv : H.JointDisjoint x y A) (a : Fin h) (s : Fin (G.b+1)) :
    (H.adjoin x y A hv).path (Fin.castAdd A.card a) s = H.path a s := by simp [adjoin]

@[simp] theorem adjoin_new (H : G.Holes h) (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (hv : H.JointDisjoint x y A) (a : Fin A.card) (s : Fin (G.b+1)) :
    (H.adjoin x y A hv).path (Fin.natAdd h a) s =
      G.pathBetween (x (selected A a)) (y (selected A a)) s := by simp [adjoin]

/- Every geometrically specified hole family already has a positive uniform
normalizer, whose proved factorial formula yields a real completion witness. -/
def VertexIsolated (H : G.Holes h) (x y : Fin k → G.Slot) (i : Fin k) : Prop :=
  (∀ a s, G.pathBetween (x i) (y i) s ≠ H.path a s) ∧
  (∀ j, i ≠ j → ∀ s, G.pathBetween (x i) (y i) s ≠ G.pathBetween (x j) (y j) s)

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid
/- A line is named by both its stage and its remaining coordinates. -/
abbrev StageLine (G : Grid) := Σ j : Fin G.b, G.Line j

def stagePath (G : Grid) {k : ℕ} (x y : Fin k → G.Slot) (i : Fin k) (j : Fin G.b) : G.StageLine :=
  ⟨j, G.pathLine (x i) (y i) j⟩

namespace Holes
open MomentExpansion
variable {G : Grid} {h k : ℕ}

def Light (H : G.Holes h) (x y : Fin k → G.Slot) (η : ℝ) (l : G.StageLine) : Prop :=
  ((H.lineCount l.1 l.2 + auxCount x y Finset.univ l.1 l.2 : ℕ) : ℝ) ≤
    (2^G.bits l.1 : ℕ)*η

def Good (H : G.Holes h) (x y : Fin k → G.Slot) (η : ℝ) (i : Fin k) : Prop :=
  H.VertexIsolated x y i ∧ ∀ j, H.Light x y η (G.stagePath x y i j)

noncomputable def goodSet (H : G.Holes h) (x y : Fin k → G.Slot) (η : ℝ) : Finset (Fin k) :=
  Finset.univ.filter (H.Good x y η)

@[simp] theorem mem_goodSet (H : G.Holes h) (x y : Fin k → G.Slot) (η : ℝ) (i : Fin k) :
    i ∈ H.goodSet x y η ↔ H.Good x y η i := by simp [goodSet]

def lightMoment (H : G.Holes h) (x y : Fin k → G.Slot) (η : ℝ) (l : G.StageLine) (n : ℕ) : ℝ :=
  if H.Light x y η l then fallingMoment (2^G.bits l.1) (H.lineCount l.1 l.2) n else 1

@[simp] theorem lightMoment_zero (H : G.Holes h) (x y : Fin k → G.Slot) (η : ℝ) (l : G.StageLine) :
    H.lightMoment x y η l 0 = 1 := by simp [lightMoment, fallingMoment_zero]

end Holes
end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid.Holes
open MomentExpansion
variable {G : Grid} {h k : ℕ}

def nonlightFactor (H : G.Holes h) (x y : Fin k → G.Slot) (η : ℝ) (J : Finset (Fin k)) : ℝ :=
  ∏ l : G.StageLine, if H.Light x y η l then 1 else
    fallingMoment (2^G.bits l.1) (H.lineCount l.1 l.2) (incidenceCount J (G.stagePath x y) l)

end CoordinateSweeps.Grid.Holes
/- Finite subset rearrangements needed for the actual good/non-good path
alternation in source04:eq10. -/
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Placement_Occurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.Placement
variable {I U X Y : Type*} [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y]

/- Dependence only on the listed coordinate values of a placement. -/
def DependsOn (coords : Y → I → U) (A : Finset I) (f : Y → ℂ) : Prop :=
  ∀ y y', (∀ i ∈ A, coords y i = coords y' i) → f y = f y'

/- Counting-measure top-level space. Equivalently the orthogonal complement
of the span of proper-coordinate cylinder functions (conjugation preserves that span). -/
def topSpace (coords : Y → I → U) : Submodule ℂ (Y → ℂ) where
  carrier := {v | ∀ A : Finset I, A ≠ Finset.univ → ∀ f : Y → ℂ,
    DependsOn coords A f → ∑ y, f y*v y = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw A hA f hf
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hv A hA f hf, hw A hA f hf, zero_add]
  smul_mem' := by
    intro c v hv A hA f hf
    simp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [← mul_assoc, mul_comm (f _) c, mul_assoc]
    rw [← Finset.mul_sum, hv A hA f hf, mul_zero]

/- The source's s-normalized alternating kernel, over all coordinate subsets. -/
def alternatingKernel (s : ℝ) (p : Finset I → X → Y → ℝ) : Matrix X Y ℂ :=
  fun x y => (s⁻¹^(Fintype.card I) * ∑ A ∈ (Finset.univ : Finset I).powerset,
    (-1 : ℝ)^(Fintype.card I-A.card) * s^A.card * p A x y : ℝ)

/- All proper-subset marginal terms vanish on the top level. This is the
nontrivial algebraic bridge between Q and the actual transition operator. -/
end CoordinateSweeps.Placement

noncomputable section
universe u v
open scoped ComplexConjugate

namespace CoordinateSweeps
/- The pointwise stabilizer of two sites, used in the sparse dimension bridge. -/
def fixTwo {Ω : Type*} (a b : Ω) : Subgroup (Equiv.Perm Ω) where
  carrier := {g | g a = a ∧ g b = b}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' hg hk := by simpa using And.intro (congrArg _ hk.1 |>.trans hg.1) (congrArg _ hk.2 |>.trans hg.2)
  inv_mem' := by
    intro g hg
    constructor
    · apply g.injective
      simpa using hg.1.symm
    · apply g.injective
      simpa using hg.2.symm

namespace SparseDimension
variable {Ω V : Type*} [Fintype Ω] [DecidableEq Ω]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/- Generic Schur commutant lemma, with no classification assumptions. -/

omit [FiniteDimensional ℂ V] in
@[simp] theorem subrep_bot_toSubmodule {Γ : Type*} [Group Γ]
    (ρ : Representation ℂ Γ V) : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl
omit [FiniteDimensional ℂ V] in
@[simp] theorem subrep_top_toSubmodule {Γ : Type*} [Group Γ]
    (ρ : Representation ℂ Γ V) : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl

/- Flatten a subrepresentation of a subrepresentation without changing its dimension. -/
def nested {Γ : Type*} [Group Γ] {ρ : Representation ℂ Γ V}
    (S : Subrepresentation ρ) (T : Subrepresentation S.toRepresentation) : Subrepresentation ρ where
  toSubmodule := T.toSubmodule.map S.toSubmodule.subtype
  apply_mem_toSubmodule := by
    intro g v hv
    obtain ⟨w, hw, rfl⟩ := hv
    refine ⟨S.toRepresentation g w, T.apply_mem_toSubmodule g hw, rfl⟩

/- Existence of a least-dimensional constituent, proved rather than assumed. -/
def fixTwoHom (a b : Ω) : Equiv.Perm {x : Ω // x ≠ a ∧ x ≠ b} →* fixTwo a b where
  toFun g := ⟨Equiv.Perm.ofSubtype g,
    Equiv.Perm.ofSubtype_apply_of_not_mem g (by simp),
    Equiv.Perm.ofSubtype_apply_of_not_mem g (by simp)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g h)

omit [Fintype Ω] in
@[simp] theorem fixTwoHom_val (a b : Ω) (g : Equiv.Perm {x : Ω // x ≠ a ∧ x ≠ b}) :
    (fixTwoHom a b g).val = Equiv.Perm.ofSubtype g := rfl

def signScalar : Equiv.Perm Ω →* ℂ :=
  (Int.castRingHom ℂ).toMonoidHom.comp ((Units.coeHom ℤ).comp Equiv.Perm.sign)

@[simp] theorem signScalar_apply (g : Equiv.Perm Ω) :
    signScalar g = ((Equiv.Perm.sign g : ℤ) : ℂ) := rfl

@[simp] theorem signScalar_swap (a b : Ω) (hab : a ≠ b) :
    signScalar (Equiv.swap a b) = -1 := by
  simp [signScalar_apply, Equiv.Perm.sign_swap hab]

/- Every one-dimensional representation of a finite symmetric group is
literally the trivial or sign representation. This also handles Ω of size 0,1. -/
def fixSet (A : Finset Ω) : Subgroup (Equiv.Perm Ω) where
  carrier := {g | ∀ a ∈ A, g a = a}
  one_mem' := by simp
  mul_mem' hg hh a ha := by simp only [Equiv.Perm.mul_apply, hh a ha, hg a ha]
  inv_mem' {g} hg a ha := by
    apply g.injective
    simpa using (hg a ha).symm

/- The complementary symmetric group onto the pointwise stabilizer. -/
def fixSetHom (A : Finset Ω) : Equiv.Perm {x : Ω // x ∉ A} →* fixSet A where
  toFun g := ⟨Equiv.Perm.ofSubtype g, fun _ ha =>
    Equiv.Perm.ofSubtype_apply_of_not_mem g (not_not.mpr ha)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g h)

omit [Fintype Ω] in
@[simp] theorem fixSetHom_val (A : Finset Ω) (g : Equiv.Perm {x : Ω // x ∉ A}) :
    (fixSetHom A g).val = Equiv.Perm.ofSubtype g := rfl

end SparseDimension
end CoordinateSweeps

noncomputable section
open scoped BigOperators

namespace CoordinateSweeps.PlacementOccurrence
variable {Γ X V : Type*} [Group Γ] [Fintype Γ] [Fintype X] [DecidableEq X] [MulAction Γ X]
    [AddCommGroup V] [Module ℂ V]

/- Sum of orbit vectors against placement coordinates. The repeated
stabilizer fibers are left in the sum, so no transversal choice is needed. -/
def orbitSynthesis (ρ : Representation ℂ Γ V) (u : V) (x₀ : X) : (X → ℂ) →ₗ[ℂ] V where
  toFun f := ∑ g, f (g • x₀) • ρ g u
  map_add' f h := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

/- Exact covariance, with the source's convention that gh applies h first. -/
end CoordinateSweeps.PlacementOccurrence

namespace CoordinateSweeps.SparseDimension
variable {Ω V : Type*} [Fintype Ω] [DecidableEq Ω]
  [AddCommGroup V] [Module ℂ V]

@[simp] theorem signScalar_mul_self (g : Equiv.Perm Ω) :
    signScalar g * signScalar g = (1 : ℂ) := by
  simp only [signScalar_apply]
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h <;> rw [h] <;> norm_num

/- Tensoring with the ordinary sign character, on exactly the same space. -/
def signTwist (ρ : Representation ℂ (Equiv.Perm Ω) V) :
    Representation ℂ (Equiv.Perm Ω) V where
  toFun g := signScalar g • ρ g
  map_one' := by simp
  map_mul' g h := by simp only [map_mul, smul_mul_smul_comm]

@[simp] theorem signTwist_apply (ρ : Representation ℂ (Equiv.Perm Ω) V)
    (g : Equiv.Perm Ω) (v : V) : signTwist ρ g v = signScalar g • ρ g v := rfl

/- The same invariant subspaces for ρ and its sign twist. -/
end CoordinateSweeps.SparseDimension

namespace CoordinateSweeps.PlacementOccurrence
open scoped Matrix.Norms.L2Operator
variable {Γ X : Type*} [Group Γ] [Fintype Γ] [Fintype X] [DecidableEq X] [MulAction Γ X]

def actionMatrix : Γ →* Matrix X X ℂ :=
  Matrix.permMatrixHom.comp (MulAction.toPermHom Γ X)

def synthesisMatrix (ρ : UnitaryIrrep Γ) (u : Fin ρ.dimension → ℂ) (x₀ : X) :
    Matrix (Fin ρ.dimension) X ℂ := LinearMap.toMatrix' (orbitSynthesis ρ.asRepresentation u x₀)

end CoordinateSweeps.PlacementOccurrence

open scoped Matrix.Norms.L2Operator

end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_SparseMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
open scoped BigOperators
namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}
open Coverage

def holeHeavy (H : G.Holes h) (η : ℝ) (j : Fin G.b) : Finset (G.Line j) :=
  heavySet (H.lineCount j) ((2^G.bits j : ℕ)*η/2)

def particleHeavy (p : Fin k → G.Slot × G.Slot) (η : ℝ) (j : Fin G.b) : Finset (G.Line j) :=
  heavySet (occupancy (fun a : G.Slot × G.Slot => G.pathLine a.1 a.2 j) p)
    ((2^G.bits j : ℕ)*η/2)

def holeHeavyHits (H : G.Holes h) (p : Fin k → G.Slot × G.Slot) (η : ℝ) (j : Fin G.b) : Finset (Fin k) :=
  Finset.univ.filter (fun i => G.pathLine (p i).1 (p i).2 j ∈ H.holeHeavy η j)

def particleHeavyHits (p : Fin k → G.Slot × G.Slot) (η : ℝ) (j : Fin G.b) : Finset (Fin k) :=
  Finset.univ.filter (fun i => G.pathLine (p i).1 (p i).2 j ∈ particleHeavy p η j)

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}

/- An explicit absolute prefactor used before asymptotic absorption. -/
def uniformSparsePrefactor (G : Grid) (h k : ℕ) : ℝ :=
  (2 : ℝ)^k * Real.exp ((G.b : ℝ)*(h+k)+Real.log 4*k*G.b) *
    (16*Real.exp 2)^(G.b*k) * (1+16*Real.exp 2)^(G.b*k)

/- The source's good/bad entry split, in counting HS normalization. -/
end CoordinateSweeps.Grid.Holes

/- Required top-placement compression for the conditional main. The top space
is the annihilator of all functions depending on a proper set of coordinates.
This is the exact top level used in source04 around eq7. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}

abbrev InputPlacements (H : G.Holes h) (k : ℕ) := {x : Fin k → G.Slot // H.ValidInput x}
abbrev OutputPlacements (H : G.Holes h) (k : ℕ) := {y : Fin k → G.Slot // H.ValidOutput y}

end CoordinateSweeps.Grid.Holes

end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_SparseDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
universe u v
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
open scoped Matrix.Norms.L2Operator
namespace CoordinateSweeps.Grid.Holes
open PlacementOccurrence Placement
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

def inputPlacementEquiv : (Fin k ↪ H.FreeAt 0) ≃ H.InputPlacements k where
  toFun x := ⟨fun i => (x i).val,⟨fun _ _ he => x.injective (Subtype.ext he),fun i a => (x i).property a⟩⟩
  invFun x := ⟨fun i => ⟨x.val i,x.property.2 i⟩,fun _ _ he => x.property.1 (congrArg Subtype.val he)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def outputFreePlacementEquiv : (Fin k ↪ H.FreeAt (Fin.last G.b)) ≃ H.OutputPlacements k where
  toFun x := ⟨fun i => (x i).val,⟨fun _ _ he => x.injective (Subtype.ext he),fun i a => (x i).property a⟩⟩
  invFun x := ⟨fun i => ⟨x.val i,x.property.2 i⟩,fun _ _ he => x.property.1 (congrArg Subtype.val he)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def outputPlacementEquiv (hf : H.Feasible) : (Fin k ↪ H.FreeAt 0) ≃ H.OutputPlacements k :=
  (Equiv.embeddingCongr (Equiv.refl (Fin k))
    (H.freeBoundary ⟨H.reference hf,H.reference_compatible hf⟩ (Fin.last G.b))).trans H.outputFreePlacementEquiv

def residualFree (hf : H.Feasible) (ω : {ω : G.Choices // H.Compatible ω}) : Equiv.Perm (H.FreeAt 0) :=
  H.stabilizerFreeEquiv (H.residual hf ω)

def referencePartial (hf : H.Feasible) (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (A : Finset (Fin k)) (x y : Fin k ↪ H.FreeAt 0) : ℝ :=
  H.extraProbability (H.inputPlacementEquiv x).val (H.outputPlacementEquiv hf y).val A μ

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps
-- Archived complete binary-sign support, reused without a new-result claim.
/- The real-valued sign character, not a replacement for the permutation. -/
def realSign {Ω : Type*} [Fintype Ω] [DecidableEq Ω] : Equiv.Perm Ω →* ℝ where
  toFun g := ((Equiv.Perm.sign g : ℤ) : ℝ)
  map_one' := by simp
  map_mul' g h := by simp

def boolSwitch (b : Bool) : Equiv.Perm Bool :=
  if b then Equiv.swap false true else 1

end CoordinateSweeps

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

def jointLineEvent (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (j : Fin G.b) (L : G.Line j) (σ : Equiv.Perm (Cube (G.bits j))) : Prop :=
  H.LineCompatible j L σ ∧ G.extraLineEvent x y A j L σ

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.UnitaryIrrep
open SparseDimension
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
def signTwist (ρ : UnitaryIrrep (Equiv.Perm Ω)) : UnitaryIrrep (Equiv.Perm Ω) where
  dimension := ρ.dimension
  positive := ρ.positive
  matrix := {
    toFun g := signScalar g • ρ.matrix g
    map_one' := by simp
    map_mul' g h := by simp only [map_mul,smul_mul_smul_comm] }
  unitary g := by
    change (signScalar g • ρ.matrix g).conjTranspose*(signScalar g • ρ.matrix g)=1
    simp only [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    rw [show star (signScalar g)=signScalar g by simp [signScalar_apply],signScalar_mul_self,one_smul,ρ.unitary]
  irreducible S hS := ρ.irreducible S (by
    intro g v hv
    have hh := S.smul_mem (signScalar g) (hS g v hv)
    change signScalar g • ((signScalar g • ρ.matrix g).mulVec v) ∈ S at hh
    simpa only [Matrix.smul_mulVec,smul_smul,signScalar_mul_self,one_smul] using hh)

@[simp] lemma signTwist_rep (ρ : UnitaryIrrep (Equiv.Perm Ω)) :
    ρ.signTwist.asRepresentation=SparseDimension.signTwist ρ.asRepresentation := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  change (signScalar g • ρ.matrix g).mulVec v=signScalar g • (ρ.matrix g).mulVec v
  exact Matrix.smul_mulVec _ _ _
end CoordinateSweeps.UnitaryIrrep

end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_SparseBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
universe u v
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace CoordinateSweeps.Grid
/- Every choice mass is a real polynomial. No conditional law is extended to complex z. -/
@[simp] lemma eventDistance_zero (G : Grid) (E : Finset G.Choices) : G.eventDistance E 0=0 := by
  simp [eventDistance]
end CoordinateSweeps.Grid
namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h : ℕ}
def event (H : G.Holes h) : Finset G.Choices := Finset.univ.filter H.Compatible
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid
/- Literal finite parameter space of bounded ordered grids; no model of
irreducibles or of conditioned complex measures is involved. -/
def BoundedCode (B r : ℕ) := Σ b : Fin (B+1),
  Subtype (fun _ : Fin b.val → Fin (2*r+1) => 0 < b.val)
instance instFiniteBoundedCode (B r : ℕ) : Finite (BoundedCode B r) := by unfold BoundedCode; infer_instance
def BoundedCode.grid {B r : ℕ} (x : BoundedCode B r) : Grid where
  b := x.1.val
  positive := x.2.property
  bits j := (x.2.val j).val
def boundedCode (G : Grid) (B r : ℕ) (hb : G.b ≤ B) (hbits : ∀ j, G.bits j ≤ 2*r) : BoundedCode B r :=
  ⟨⟨G.b,by omega⟩,⟨(fun j => ⟨G.bits j,by have hh := hbits j; omega⟩),G.positive⟩⟩
@[simp] lemma boundedCode_grid (G : Grid) (B r : ℕ) (hb : G.b ≤ B) (hbits : ∀ j, G.bits j ≤ 2*r) :
    (G.boundedCode B r hb hbits).grid=G := by cases G; rfl
/- Uniform finite real perturbation for all nonempty events on every bounded
allowed grid. Quantifiers include all feasible path events, uniformly in h. -/
end CoordinateSweeps.Grid
end
end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Young_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- Finite Young-corner construction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.YoungCorner
variable {A : Type*} [Ring A] [Algebra ℂ A]
def sumRow (μ : YoungDiagram) (ρ : Equiv.Perm (Boxes μ) →* A) : A :=
  ∑ r : rows μ, ρ r

def sumCol (μ : YoungDiagram) (ρ : Equiv.Perm (Boxes μ) →* A) : A :=
  ∑ c : cols μ, signScalar (c : Equiv.Perm (Boxes μ)) • ρ c

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.RepDetection
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

def orbitSpan (τ : Representation ℂ G V) (v : V) : Subrepresentation τ where
  toSubmodule := Submodule.span ℂ (Set.range (fun g => τ g v))
  apply_mem_toSubmodule := by
    intro g w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨k,rfl⟩ := hw
      apply Submodule.subset_span
      exact ⟨g*k,by simp only [map_mul,Module.End.mul_apply]⟩
    | zero => simp
    | add x y hx hy ix iy => simpa using Submodule.add_mem _ ix iy
    | smul c x hx ix => simpa using Submodule.smul_mem _ c ix

end CoordinateSweeps.RepDetection

namespace CoordinateSweeps.YoungCorner

def unitVector (μ : YoungDiagram) : Equiv.Perm (Boxes μ) → ℂ := fun g => if g=1 then 1 else 0

def columnGenerator (μ : YoungDiagram) := sumCol μ (regular (Equiv.Perm (Boxes μ))) (unitVector μ)
def youngVector (μ : YoungDiagram) := sumRow μ (regular (Equiv.Perm (Boxes μ))) (columnGenerator μ)
abbrev columnModule (μ : YoungDiagram) := RepDetection.orbitSpan (regular (Equiv.Perm (Boxes μ))) (columnGenerator μ)

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

def ranks (μ : YoungDiagram) : Subgroup (Equiv.Perm (Boxes μ)) :=
  colorStabilizer (fun x => x.val.1+x.val.2)

end CoordinateSweeps.YoungCorner
end

open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_BaseCase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Work on the genuinely missing main statements of the pinned manuscript.
All definitions are finite and use the source's ordinary probability and trace
normalizations. No result of the manuscript is assumed.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.UnitaryIrrep

variable {Γ : Type*} [Group Γ] (ρ : UnitaryIrrep Γ)

def fixed : Submodule ℂ (Fin ρ.dimension → ℂ) where
  carrier := {v | ∀ g, (ρ.matrix g).mulVec v=v}
  zero_mem' := by simp
  add_mem' hu hv := by intro g; simp only [Matrix.mulVec_add,hu g,hv g]
  smul_mem' c v hv := by intro g; simp only [Matrix.mulVec_smul,hv g]

end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.Grid

/- A one-coordinate grid, the base of06's induction. -/
abbrev single (d : ℕ) : Grid := ⟨1,by decide,fun _ => d⟩

instance single_line_unique (d : ℕ) (j : Fin (single d).b) :
    Unique ((single d).Line j) := by
  have he : IsEmpty {k : Fin (single d).b // k ≠ j} :=
    ⟨fun k => k.property (Subsingleton.elim _ _)⟩
  exact Pi.uniqueOfIsEmpty _

/- The single coordinate slot identification is explicit. -/
def singleSlot (d : ℕ) : (single d).Slot ≃ Cube d :=
  Equiv.piUnique (fun _ : Fin 1 => Cube d)

@[simp] theorem singleSlot_apply (d : ℕ) (x : (single d).Slot) :
    singleSlot d x = x 0 := rfl

@[simp] theorem singleSlot_symm_apply (d : ℕ) (x : Cube d) (j : Fin 1) :
    (singleSlot d).symm x j=x := rfl

/- Every line-choice array in a one-coordinate grid is one permutation. -/
def singleChoice (d : ℕ) : (single d).Choices ≃ Equiv.Perm (Cube d) where
  toFun ω := ω 0 default
  invFun σ _ _ := σ
  left_inv ω := by
    funext j L
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    exact congrArg (ω 0) (Subsingleton.elim _ _)
  right_inv σ := rfl

lemma single_stage_apply (d : ℕ) (ω : (single d).Choices) (x : (single d).Slot) :
    (single d).stage ω 0 x 0=singleChoice d ω (x 0) := by
  have hs : (single d).stage ω 0 x 0=ω 0 (fun k => x k) (x 0) := by
    simp [stage,fiberPerm,Equiv.piSplitAt_apply,Equiv.piSplitAt_symm_apply]
  rw [hs]
  change ω 0 (fun k => x k) (x 0)=ω 0 default (x 0)
  exact congrArg (fun L => ω 0 L (x 0)) (Subsingleton.elim _ _)

lemma single_sweep (d : ℕ) (ω : (single d).Choices) :
    (single d).sweep ω=(singleSlot d).symm.permCongr (singleChoice d ω) := by
  apply Equiv.ext
  intro x
  funext j
  have hj : j=0 := Subsingleton.elim _ _
  subst j
  change (single d).boundary ω 1 x 0=_
  simp only [boundary,List.ofFn_succ,List.ofFn_zero,List.take_succ_cons,List.take_zero,
    List.reverse_cons,List.reverse_nil,List.nil_append,List.prod_cons,List.prod_nil,mul_one]
  exact single_stage_apply d ω x

/- No hidden fibers in the one-block base: all permutations are possible,
and each one determines the unique line-choice array. -/
def singleSweepEquiv (d : ℕ) : (single d).Choices ≃ Equiv.Perm (single d).Slot :=
  (singleChoice d).trans (Equiv.permCongr (singleSlot d).symm)

@[simp] lemma singleSweepEquiv_apply (d : ℕ) (ω : (single d).Choices) :
    singleSweepEquiv d ω=(single d).sweep ω := (single_sweep d ω).symm

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid.Holes
variable {d h : ℕ} (H : (Grid.single d).Holes h)

lemma single_compatible_iff (ω : (Grid.single d).Choices) :
    H.Compatible ω ↔ ∀ i, (Grid.single d).sweep ω (H.path i 0)=H.path i 1 := by
  constructor
  · intro hω i
    exact hω i 1
  · intro hω i t
    fin_cases t
    · simp [Grid.boundary]
    · exact hω i

/- Exact bijection of conditioned one-block choices with the remaining
symmetric group, not an assumption of uniformity of that residual law. -/
def singleResidualEquiv (hf : H.Feasible) :
    {ω : (Grid.single d).Choices // H.Compatible ω} ≃ H.stabilizer where
  toFun := H.residual hf
  invFun g := ⟨(Grid.singleSweepEquiv d).symm
      ((Grid.single d).sweep (H.reference hf)*g.val), by
    apply (H.single_compatible_iff _).mpr
    intro i
    rw [← Grid.singleSweepEquiv_apply,Equiv.apply_symm_apply]
    change (Grid.single d).sweep (H.reference hf) (g.val (H.path i 0))=H.path i 1
    rw [g.property i]
    exact H.reference_compatible hf i 1⟩
  left_inv ω := by
    apply Subtype.ext
    apply (Grid.singleSweepEquiv d).injective
    simp only [Equiv.apply_symm_apply,Grid.singleSweepEquiv_apply,residual,
      mul_inv_cancel_left]
  right_inv g := by
    apply Subtype.ext
    change ((Grid.single d).sweep (H.reference hf))⁻¹ *
      (Grid.single d).sweep ((Grid.singleSweepEquiv d).symm
        ((Grid.single d).sweep (H.reference hf)*g.val))=g.val
    rw [← Grid.singleSweepEquiv_apply d ((Grid.singleSweepEquiv d).symm
      ((Grid.single d).sweep (H.reference hf)*g.val)),
      Equiv.apply_symm_apply,inv_mul_cancel_left]

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps

lemma baseWidth_one_le (r : ℕ) : 1 ≤ baseWidth r := by
  unfold baseWidth
  exact_mod_cast (show 1 ≤ (2^(2*r)).factorial from Nat.factorial_pos _)

lemma baseZeta_le_half (r : ℕ) : baseZeta r ≤ 1/2 := by
  have h := baseWidth_one_le r
  unfold baseZeta
  apply (div_le_iff₀ (by positivity : 0 < 4*(baseWidth r)^2)).mpr
  nlinarith

end CoordinateSweeps

end

namespace CoordinateSweeps.Grid.Holes
open UnitaryIrrep YoungCorner
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)
/- The unswept free sites and the literal occupied junction board are
identified by the actual reference first-half sweep. -/
noncomputable def initialJunctionFree (hf : H.Feasible) : H.FreeAt 0 ≃ H.JunctionFree :=
  Marked.freeEquiv (fun i => H.path i 0) (fun i => H.path i (suffixTime A B 0))
    (H.rowAction (H.refPair hf).1) (H.rowAction_marked hf (H.refPair hf).1)
end CoordinateSweeps.Grid.Holes

open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Perturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
All definitions are finite and use the source's ordinary probability and trace
normalizations.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

/-! The alternating placement kernel from 04-sparse:eq7.
Endpoints below need not be injections; invalid specifications have probability
zero automatically. On valid endpoint placements this is exactly the source Q. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/- Necessary shared-line polynomial expansion for the sparse conditional main.
A variable names a LINE, not a particle. The tensor moment functional is merely
linear, never multiplicative when two factors use the same line. -/
noncomputable section
open scoped BigOperators
open MvPolynomial

/- The analytic light-line obligation 04-sparse.tex (11).  The distribution
is exactly Mathlib's Gamma(shape, unit rate). -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators

/- Finite subset rearrangements needed for the actual good/non-good path
alternation in source04:eq10. -/
noncomputable section
open scoped BigOperators

/- Required top-placement compression for the conditional main. The top space
is the annihilator of all functions depending on a proper set of coordinates.
This is the exact top level used in source04 around eq7. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable

noncomputable section
universe u v
open scoped ComplexConjugate

noncomputable section
open scoped BigOperators

open scoped Matrix.Norms.L2Operator

noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace CoordinateSweeps.SparseDimension
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
structure Level (ρ : UnitaryIrrep (Equiv.Perm Ω)) (k : ℕ) where
  flipped : Bool
  vector : Fin ρ.dimension → ℂ
  nonzero : vector ≠ 0
  placement : Fin k ↪ Ω
  fixed : ∀ g : Equiv.Perm Ω, (∀ i, g (placement i)=placement i) →
    (if flipped then signTwist ρ.asRepresentation else ρ.asRepresentation) g vector=vector
  minimal : ∀ A : Finset Ω, A.card < k → ∀ v : Fin ρ.dimension → ℂ,
    (∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a=a) →
      (if flipped then signTwist ρ.asRepresentation else ρ.asRepresentation) g v=v) → v=0
end CoordinateSweeps.SparseDimension

end
end
end
end
end
end
end
end
end

open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Matrix.Norms.L2Operator

namespace CoordinateSweeps
noncomputable def cHat (s : ℕ) : ℝ := c s+1/(20*Real.sqrt (Real.log s))
noncomputable def eHat (s : ℕ) : ℝ := e s-1/(20*Real.sqrt (Real.log s))
end CoordinateSweeps

end OAI
end


