-- Prove2me | Definitions.Def_OAIQ076M005
-- name    : OAIQ076M005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:01:09.734217+00:00
-- url     : https://prove2.me/theorems/8782014f-546d-4f33-a6b1-b6dc6ceb91ae
-- title:
--   Definitions bundle OAIQ076M005 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 456 declarations of OpenAI's Lean: 199 definitions, 15 inductive types or structures, 10 instances and 232 theorems. The definitions and types are `OAI.MinUncut.Preprocess.Alphabet.slotGood`, `OAI.MinUncut.Preprocess.Source.Par`, `OAI.MinUncut.Preprocess.Syntax.bin`, `OAI.MinUncut.Preprocess.Syntax.branch`, `OAI.MinUncut.Preprocess.UEncoding.optionEquiv`, `OAI.MinUncut.Preprocess.gridField`, `OAI.MinUncut.Preprocess.gridTail`, `OAI.MinUncut.Preprocess.searchWith`, `OAI.MinUncutGames.Foundations.Complexity.CookLevin.PolynomialMachine.popN`, `OAI.MinUncutGames.Foundations.Complexity.CookLevin.PolynomialMachine.prefixCostPolynomial`, `OAI.MinUncutGames.Foundations.Complexity.CookLevin.PolynomialMachine.prefixValuePolynomial`, `OAI.MinUncutGames.Foundations.Complexity.MachineCountedLoop.totalSteps`, `OAI.MinUncutGames.Foundations.Complexity.MachineFieldProfile.Label`, `OAI.MinUncutGames.Foundations.Complexity.MachineFieldProfile.allPairs`, `OAI.MinUncutGames.Foundations.Complexity.MachineFieldProfile.labelAt`, `OAI.MinUncutGames.Foundations.Complexity.MachineFieldProfile.pairTime`, `OAI.MinUncutGames.Foundations.Complexity.MachineFieldProfile.prefixTime`, `OAI.MinUncutGames.Foundations.Complexity.MachineHorner.Alphabet`, `OAI.MinUncutGames.Foundations.Complexity.MachineHorner.Label`, `OAI.MinUncutGames.Foundations.Complexity.MachineHorner.entryLabel`, `OAI.MinUncutGames.Foundations.Complexity.MachineHorner.perDigitBound`, `OAI.MinUncutGames.Foundations.Complexity.MachineHorner.stepCost`, `OAI.MinUncutGames.Foundations.Complexity.MachineHorner.timePolynomial`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.addressIndex`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.bodyIndex`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.fields`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.rowCostBound`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.rowSizeBound`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.valueBound`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyTable.Tape`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyTable.Tape.enumList`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyTable.dummyRoles`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyTable.dummyView`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyTable.finalTapes`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyTable.finishSteps`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyTable.frame`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyTable.initialTapes`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyTable.oldRoles`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyTable.remaining`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyTable.splitRoles` and 174 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Encoding_Decoder`, `MinUncut_Encoding_DerivedResolver`, `MinUncut_Encoding_UniformEncoding`, `MinUncut_Estimates_Basic2`, `MinUncut_Estimates_Bridge`, `MinUncut_Estimates_ExpressionEffectivity`, `MinUncut_Estimates_InputData`, `MinUncut_Estimates_LocalBodyEffectivity`, `MinUncut_Estimates_UniformAlgebra`, `MinUncut_Estimates_UniformEquation`, `MinUncut_Estimates_UniformProduct`, `MinUncut_Games_PoweringInitializeFrame`, `MinUncut_Games_PoweringPlanBudget`, `MinUncut_Machines_Addresses`, `MinUncut_Machines_AlphabetGraph`, `MinUncut_Machines_Driver`, `MinUncut_Machines_MachineCloudPadding`, `MinUncut_Machines_MachineCloudPrefix`, `MinUncut_Machines_MachineCompare`, `MinUncut_Machines_MachineDummyRows`, `MinUncut_Machines_MachineFiniteAlphabet`, `MinUncut_Machines_MachineLazyRows`, `MinUncut_Machines_MachineLazyTable`, `MinUncut_Machines_MachineLazyTableRuntime`, `MinUncut_Machines_MachineOverlayRows`, `MinUncut_Machines_MachineOverlayTable`, `MinUncut_Machines_MachinePortReindex`, `MinUncut_Machines_MachineRegisterEmit`, `MinUncut_Machines_MachineRegularLift`, `MinUncut_Machines_MachineRegularMetadata`, `MinUncut_Machines_MachineRegularOriginalBody`, `MinUncut_Machines_MachineRegularTableRuntime`, `MinUncut_Machines_MachineRegularTableTrace`, `MinUncut_Machines_MachineRegularVertexBlock`, `MinUncut_Machines_MachineTransducer`, `MinUncut_Machines_MachineTupleOdometer`, `MinUncut_Machines_MachineUnaryAdd`, `MinUncut_Machines_MachineUnaryCounter`, `MinUncut_Machines_PoweringMachineRelation`, `MinUncut_Machines_PoweringMachineRotor`, `MinUncut_Machines_PoweringMachineRow`, `MinUncut_Machines_PoweringMachineVertex`, `MinUncut_Machines_RuntimeFinish`, `MinUncut_Machines_RuntimeModel`, `MinUncut_Machines_RuntimeModel2`, `MinUncut_Machines_RuntimeSpace`, `MinUncut_Machines_SelectorMachine`, `MinUncut_Machines_UniformAlphabet`, `MinUncut_PCP_AddressArithmetic`, `MinUncut_PCP_Bounds`, `MinUncut_PCP_CayleySampling`, `MinUncut_PCP_CayleySpectral`, `MinUncut_PCP_ClauseLookup`, `MinUncut_PCP_ContextClear`, `MinUncut_PCP_ContextLoad`, `MinUncut_PCP_ContextPrepare`, `MinUncut_PCP_DescriptorEmission`, `MinUncut_PCP_EquationEmit`, `MinUncut_PCP_FieldArray`, `MinUncut_PCP_Gap`, `MinUncut_PCP_GraphGap`, `MinUncut_PCP_GraphTableComplexity`, `MinUncut_PCP_HeaderAccumulate`, `MinUncut_PCP_HeaderCounts`, `MinUncut_PCP_Overlay`, `MinUncut_PCP_PortTableLookup`, `MinUncut_PCP_PoweringFinalConstants`, `MinUncut_PCP_PoweringReturn`, `MinUncut_PCP_PoweringTableLayout`, `MinUncut_PCP_PoweringTableSemantics`, `MinUncut_PCP_PreprocessingLazyWords`, `MinUncut_PCP_PreprocessingOverlayWords`, `MinUncut_PCP_PreprocessingPaddingOffsets`, `MinUncut_PCP_PreprocessingRegularLoopWords`, `MinUncut_PCP_PreprocessingTableSpectral`, `MinUncut_PCP_ProfileBridge`, `MinUncut_PCP_RawInitialTables`, `MinUncut_PCP_SpectralCut`, `MinUncut_PCP_TableIteration`, `MinUncut_PCP_TupleBound`, `MinUncut_Search_ArithmeticTactic`, `MinUncut_Search_RawRationalArithmetic`, `MinUncut_Search_UniformFind`, `MinUncut_Search_UniformFiniteSum`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M011`, `OAIQ076M012` and `OAIQ076M013`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ076_MU.Compat
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
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_Decoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem scaled_geometric_power_le_one {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (n : Nat) :
    (n : ℝ) * (1 - t) * t ^ n ≤ 1 := by
  have hsum : (n : ℝ) * t ^ n ≤ ∑ j ∈ Finset.range n, t ^ j := by
    calc
      (n : ℝ) * t ^ n = ∑ _j ∈ Finset.range n, t ^ n := by simp
      _ ≤ ∑ j ∈ Finset.range n, t ^ j := by
        apply Finset.sum_le_sum
        intro j hj
        exact pow_le_pow_of_le_one ht ht' (Nat.le_of_lt (Finset.mem_range.mp hj))
  have hm := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr ht')
  rw [geom_sum_mul_neg] at hm
  have hp : 0 ≤ t ^ n := pow_nonneg ht _
  nlinarith

theorem noise_decay_bound {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    {k : Nat} (hk : 0 < k) :
    4 * ε * ((1 - 2 * ε) ^ k) ^ 2 ≤ 1 / (k : ℝ) := by
  have h := scaled_geometric_power_le_one (t := 1 - 2 * ε)
    (by linarith) (by linarith) (2 * k)
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  apply (le_div_iff₀ hkp).mpr
  have hpow : (1 - 2 * ε) ^ (2 * k) = ((1 - 2 * ε) ^ k) ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
  rw [hpow] at h
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
  nlinarith

end MinUncutGames.Foundations.Hastad

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RawRationalArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
attribute [fun_prop] Computable ComputablePred

end
namespace MinUncut.Preprocess
variable {α β : Type} [Primcodable α] [Primcodable β]

lemma c_rangeMap {f : α → ℕ → β} (hf : Computable₂ f) :
    Computable₂ (fun a n => (List.range n).map (f a)) := by
  have hh := Computable.nat_rec (α:=α × ℕ) (σ:=List β) Computable.snd
    (Computable.const [])
    (Computable.list_concat.comp
      (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))).to₂
  exact hh.of_eq (by
    intro p
    induction p.2 with
    | zero => rfl
    | succ n ih => simp only [List.range_succ,List.map_append,List.map_singleton,ih])

@[fun_prop] lemma ca_range {f : α → ℕ} (hf : Computable f) :
    Computable (fun a=>List.range (f a)) := Primrec.list_range.to_comp.comp hf
@[fun_prop] lemma ca_sum {f : α → List ℕ} (hf : Computable f) :
    Computable (fun a=>(f a).sum) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).to_comp.comp hf

lemma c_boundedSum {f : α → ℕ → ℕ} {n : α → ℕ}
    (hf : Computable₂ f) (hn : Computable n) :
    Computable (fun a=>((List.range (n a)).map (f a)).sum) :=
  ca_sum ((c_rangeMap hf).comp Computable.id hn)

end MinUncut.Preprocess

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_UniformEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
open scoped BigOperators

namespace UEncoding
variable {P : Type} [Primcodable P] {A B C Γ : P → Type}

lemma finRange_values (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

end UEncoding
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_DerivedResolver
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Preprocess

theorem encode_ofLeftInjection_canonical {α β : Type*} (e : α ≃ ℕ)
    (f : β → α) (g : α → Option β) (hfg : ∀ b, g (f b) = some b)
    (hgf : ∀ a b, g a = some b → f b = a) (n : ℕ) (b : β)
    (h : @Encodable.decode β
      (@Encodable.ofLeftInjection α β (Encodable.ofEquiv ℕ e) f g hfg) n = some b) :
    @Encodable.encode β
      (@Encodable.ofLeftInjection α β (Encodable.ofEquiv ℕ e) f g hfg) b = n := by
  change (some (e.symm n)).bind g = some b at h
  change e (f b) = n
  rw [hgf _ _ (by simpa using h), e.apply_symm_apply]

end MinUncut.Preprocess

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RuntimeFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceRuntimeFinish

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Tapes (K : Type) := K → List Bool

def canonicalTapes (output : K) (word : List Bool) : Tapes K :=
  Function.update (fun _ => []) output word

variable [Fintype K]
open scoped BigOperators

def totalLength (base : Tapes K) : Nat := ∑ k, (base k).length

theorem totalLength_erase (base : Tapes K) (source : K) :
    totalLength (Function.update base source []) + (base source).length = totalLength base := by
  calc
    _ = ∑ k, (((Function.update base source []) k).length +
        if k = source then (base source).length else 0) := by
      simp [totalLength, Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : k = source
      · subst k
        simp
      · simp [h]

end MinUncutGames.Foundations.Hastad.SourceRuntimeFinish

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RuntimeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceRuntimeSpace

open _root_.Turing
open scoped BigOperators

attribute [local instance] FinTM2.kFin

def configurationLength (tm : FinTM2) (cfg : tm.Cfg) : Nat :=
  ∑ k : tm.K, (cfg.stk k).length

theorem initial_configurationLength (tm : FinTM2) (input : List (tm.Γ tm.k₀)) :
    configurationLength tm (initList tm input) = input.length := by
  have point (k : tm.K) : ((initList tm input).stk k).length =
      if k = tm.k₀ then input.length else 0 := by
    by_cases h : k = tm.k₀
    · subst k
      simp [initList]
    · simp [initList, h]
  simp [configurationLength, point]

theorem totalLength_eq_configurationLength (tm : FinTM2) (finish : tm.Cfg)
    (base : tm.K → List Bool)
    (sameLengths : ∀ k, (base k).length = (finish.stk k).length) :
    SourceRuntimeFinish.totalLength base = configurationLength tm finish := by
  exact Finset.sum_congr rfl (fun k _ => sameLengths k)

end MinUncutGames.Foundations.Hastad.SourceRuntimeSpace

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineUnaryCounter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineCountedLoop

open _root_.Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

def totalSteps (cost : Nat → Nat) (n : Nat) : Nat :=
  (∑ r ∈ Finset.range n, cost r) + n + 1

@[simp] theorem totalSteps_zero (cost : Nat → Nat) : totalSteps cost 0 = 1 := by
  simp [totalSteps]

theorem totalSteps_succ (cost : Nat → Nat) (n : Nat) :
    totalSteps cost (n + 1) = (totalSteps cost n + cost n) + 1 := by
  simp only [totalSteps, Finset.sum_range_succ]
  omega

theorem totalSteps_le (cost : Nat → Nat) (n B : Nat)
    (bodyBound : ∀ r, r < n → cost r ≤ B) :
    totalSteps cost n ≤ n * (B + 1) + 1 := by
  have hsum : (∑ r ∈ Finset.range n, cost r) ≤ n * B := by
    calc
      (∑ r ∈ Finset.range n, cost r) ≤ ∑ _r ∈ Finset.range n, B :=
        Finset.sum_le_sum (fun r hr => bodyBound r (Finset.mem_range.mp hr))
      _ = n * B := by simp
  simpa only [totalSteps, Nat.mul_add, Nat.mul_one] using
    Nat.add_le_add_right (Nat.add_le_add_right hsum n) 1

end MinUncutGames.Foundations.Complexity.MachineCountedLoop

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineFieldProfile

open _root_.Turing

abbrev Label {q : Nat} (cells : List (Fin q × Fin q)) := Fin (cells.length + 1) × Fin 7

def labelAt {q : Nat} (cells : List (Fin q × Fin q)) (r : Nat) (phase : Fin 7) : Label cells :=
  (⟨min r cells.length, by omega⟩, phase)

def pairTime {q : Nat} (words : Fin q → List Bool) (pair : Fin q × Fin q) : Nat :=
  2 * ((words pair.1).length + 1) + 2 * ((words pair.2).length + 1) +
    max (words pair.1).length (words pair.2).length + 2

def prefixTime {q : Nat} (words : Fin q → List Bool)
    (cells : List (Fin q × Fin q)) (r : Nat) : Nat :=
  ((cells.take r).map (pairTime words)).sum

theorem prefixTime_succ {q : Nat} (words : Fin q → List Bool)
    (cells : List (Fin q × Fin q)) (r : Nat) (hr : r < cells.length) :
    prefixTime words cells (r + 1) = prefixTime words cells r + pairTime words cells[r] := by
  unfold prefixTime
  rw [List.take_succ_eq_append_getElem hr, List.map_append, List.sum_append]
  rfl

def allPairs (q : Nat) : List (Fin q × Fin q) :=
  (List.finRange q).flatMap fun i => (List.finRange q).map fun j => (i, j)

theorem mem_allPairs {q : Nat} (i j : Fin q) : (i, j) ∈ allPairs q := by
  simp [allPairs]

theorem length_allPairs (q : Nat) : (allPairs q).length = q * q := by
  simp [allPairs, List.length_flatMap]

theorem pairTime_le {q : Nat} (words : Fin q → List Bool) (L : Nat)
    (hL : ∀ i, (words i).length ≤ L) (pair : Fin q × Fin q) :
    pairTime words pair ≤ 5 * L + 6 := by
  have hi := hL pair.1
  have hj := hL pair.2
  have hm := max_le hi hj
  dsimp only [pairTime]
  omega

theorem totalTime_le {q : Nat} (words : Fin q → List Bool) (L : Nat)
    (hL : ∀ i, (words i).length ≤ L) (cells : List (Fin q × Fin q)) :
    (cells.map (pairTime words)).sum ≤ cells.length * (5 * L + 6) := by
  induction cells with
  | nil => simp
  | cons pair rest ih =>
    have hp := pairTime_le words L hL pair
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

end MinUncutGames.Foundations.Complexity.MachineFieldProfile

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceBounds

def bitCountFormula (n m u : ℕ) : ℕ :=
  n ^ u * 2 ^ (2 ^ u) + m ^ u * 2 ^ (8 ^ u) + 1

def bitCoefficient (u : ℕ) : ℕ := 2 ^ (2 ^ u) + 2 ^ (8 ^ u) + 1

end MinUncutGames.Foundations.Hastad.SourceBounds

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_FieldArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceFieldArray

open _root_.Turing
open MinUncutGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

def boundedIndex (q j : Nat) : Fin (q + 1) := ⟨min j q, by omega⟩

@[simp] theorem boundedIndex_val {q j : Nat} (hj : j ≤ q) :
    (boundedIndex q j).val = j := Nat.min_eq_left hj

end MinUncutGames.Foundations.Hastad.SourceFieldArray

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ClauseLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceClauseLookup

open _root_.Turing
open MinUncutGames.Foundations.Complexity

inductive Label
  | copyOut | copyBack | headerFirst | headerSecond | guard
  | skip (slot : Fin 6)
  | read (slot : Fin 7 × Bool)
  deriving DecidableEq, Fintype

def readStart (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 6 r, false)
def readLoop (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 6 r, true)
def skipLabel (r : Nat) : Label := if h : r < 6 then .skip ⟨r, h⟩ else .guard
def headerLabel (r : Nat) : Label :=
  if r = 0 then .headerFirst else if r = 1 then .headerSecond else .guard

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 10

theorem timePolynomial_eval (L : Nat) : timePolynomial.eval L = 4 * L + 10 := by
  simp [timePolynomial]

end MinUncutGames.Foundations.Hastad.SourceClauseLookup

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ContextLoad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceContextLoad

open _root_.Turing MinUncutGames.Foundations.Complexity

inductive Label (u : Nat)
  | copyOut (coordinate : Fin u) | copyBack (coordinate : Fin u)
  | lookup (coordinate : Fin u) (localLabel : SourceClauseLookup.Label)
  | clearWork (coordinate : Fin u) | clearIndex (coordinate : Fin u)
  | done
  deriving DecidableEq, Fintype

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

def placedLabel (j : Fin u) : Option SourceClauseLookup.Label → Option (Label u)
  | none => some (.clearWork j)
  | some l => some (.lookup j l)

def nextLabel (j : Fin u) : Label u :=
  if h : j.val + 1 < u then .copyOut ⟨j.val + 1, h⟩ else .done

def labelAt (r : Nat) : Label u :=
  if h : r < u then .copyOut ⟨r, h⟩ else .done

theorem nextLabel_eq (j : Fin u) : nextLabel j = labelAt (j.val + 1) := rfl

def polaritySlot (s : Fin 3) : Fin 6 := ⟨2 * s.val + 1, by omega⟩

end MinUncutGames.Foundations.Hastad.SourceContextLoad

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ProfileBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceSignLoad

open _root_.Turing
open MinUncutGames.Foundations.Complexity

variable {u : ℕ} {K Λ τ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

end MinUncutGames.Foundations.Hastad.SourceSignLoad

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ContextPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MinUncutGames.Foundations.Hastad.SourceLoopInit

open _root_.Turing MinUncutGames.Foundations.Complexity

inductive Label (u : Nat)
  | inputCopyOut | inputCopyBack | read (slot : Fin 3 × Bool) | clearWork
  | seed (j : Fin u) | digitCopyOut (j : Fin u) | digitCopyBack (j : Fin u)
  | trim (j : Fin u) | done
  deriving DecidableEq, Fintype

variable {u : Nat} {Extra : Type}

def readStart (r : Nat) : Label u := .read (SourceFieldArray.boundedIndex 2 r, false)
def readLoop (r : Nat) : Label u := .read (SourceFieldArray.boundedIndex 2 r, true)
def labelAt (r : Nat) : Label u := if h : r < u then .seed ⟨r, h⟩ else .done

variable [DecidableEq Extra]

noncomputable def timePolynomial (u : Nat) : Polynomial Nat :=
  Polynomial.C (2 * u + 3) * Polynomial.X + Polynomial.C (6 * u + 7)

theorem timePolynomial_eval (u L : Nat) :
    (timePolynomial u).eval L = (2 * u + 3) * L + 6 * u + 7 := by
  simp [timePolynomial, Nat.add_assoc]

end MinUncutGames.Foundations.Hastad.SourceLoopInit

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegisterEmit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegisterEmit

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

end MinUncutGames.Foundations.Complexity.MachineRegisterEmit

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineTransducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineUnaryMultiply

open _root_.Turing
open scoped BigOperators

inductive Label
  | copyDrain | copyFork | seed | guard | scan | emitFalse | emitTrue | restore | finish
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyDrain, .copyFork, .seed, .guard, .scan,
  .emitFalse, .emitTrue, .restore, .finish]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def transition (_ : Unit) (_ : Bool) : Unit := ()
def payload (_ : Unit) (bit : Bool) : List Bool := if bit then [true] else []

def emitterLabel (labels : Label → Λ) (_ : Unit) (bit : Bool) : Λ :=
  if bit then labels .emitTrue else labels .emitFalse

def bodySteps (a : ℕ) : ℕ := 3 * (a + 1) + 2
def steps (a b : ℕ) : ℕ := 3 * a * b + 8 * b + 7

theorem totalSteps_eq (a b : ℕ) :
    MachineCountedLoop.totalSteps (fun _ => bodySteps a) b = b * (bodySteps a + 1) + 1 := by
  simp [MachineCountedLoop.totalSteps, Nat.mul_add, Nat.add_assoc]

end MinUncutGames.Foundations.Complexity.MachineUnaryMultiply

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineUnaryAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineRadixStep

open _root_.Turing

inductive Label
  | multiply (label : MachineUnaryMultiply.Label)
  | digitDrain | digitFork | add | finish
  deriving DecidableEq, Fintype

variable {K Λ σ : Type}

abbrev Alphabet (_ : K) := Bool

def multiplySlots (slots : Fin 6 ↪ K) : Fin 5 ↪ K :=
  (Fin.succAboveEmb (2 : Fin 6)).trans slots

@[simp] theorem multiplySlots_zero (slots : Fin 6 ↪ K) : multiplySlots slots 0 = slots 0 := rfl
@[simp] theorem multiplySlots_one (slots : Fin 6 ↪ K) : multiplySlots slots 1 = slots 1 := rfl
@[simp] theorem multiplySlots_two (slots : Fin 6 ↪ K) : multiplySlots slots 2 = slots 3 := rfl
@[simp] theorem multiplySlots_three (slots : Fin 6 ↪ K) : multiplySlots slots 3 = slots 4 := rfl
@[simp] theorem multiplySlots_four (slots : Fin 6 ↪ K) : multiplySlots slots 4 = slots 5 := rfl

variable [DecidableEq K]

def steps (radix acc digit : ℕ) : ℕ := 3 * radix * acc + 8 * acc + 3 * digit + 13

end MinUncutGames.Foundations.Complexity.MachineRadixStep

namespace MinUncutGames.Foundations.Complexity.MachineHorner

open _root_.Turing

variable {K Λ σ : Type} {width : Nat}

abbrev Alphabet (_ : K) := Bool

inductive Label (width : Nat)
  | start
  | radix (i : Fin width) (inner : MachineRadixStep.Label)
  | clear (i : Fin width)
  | finishDrain | finishRestore
  deriving DecidableEq, Fintype

def entryLabel (width n : Nat) : Label width :=
  if h : n < width then .radix ⟨n, h⟩ (.multiply .copyDrain) else .finishDrain

variable [DecidableEq K]

def stepCost (radix acc digit : Nat) : Nat :=
  MachineRadixStep.steps radix acc digit + acc + 1

def perDigitBound (width magnitude : Nat) : Nat :=
  3 * magnitude * (magnitude + 1) ^ width + 9 * (magnitude + 1) ^ width + 3 * magnitude + 14

omit [DecidableEq K] in
theorem stepCost_le (radix acc digit width magnitude : Nat)
    (radixBound : radix ≤ magnitude) (accBound : acc ≤ (magnitude + 1) ^ width)
    (digitBound : digit ≤ magnitude) :
    stepCost radix acc digit ≤ perDigitBound width magnitude := by
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 3 radixBound) accBound
  unfold stepCost MachineRadixStep.steps perDigitBound
  omega

noncomputable def timePolynomial (width : Nat) : Polynomial Nat :=
  Polynomial.C width *
    (3 * Polynomial.X * (Polynomial.X + 1) ^ width +
      9 * (Polynomial.X + 1) ^ width + 3 * Polynomial.X + 14) +
    2 * (Polynomial.X + 1) ^ width + 5

omit [DecidableEq K] in
@[simp] theorem timePolynomial_eval (width magnitude : Nat) :
    (timePolynomial width).eval magnitude =
      width * perDigitBound width magnitude + 2 * (magnitude + 1) ^ width + 5 := by
  simp [timePolynomial, perDigitBound]

open scoped BigOperators

end MinUncutGames.Foundations.Complexity.MachineHorner

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_AddressArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceRankPhase

open _root_.Turing Complexity
open scoped BigOperators

def rank {width : Nat} (radix : Nat) (digits : Fin width → Nat) : Nat :=
  ∑ i : Fin width, digits i * radix ^ i.val

def reverseDigits {width : Nat} (digits : Fin width → Nat) (i : Nat) : Nat :=
  if h : i < width then digits (Fin.rev ⟨i, h⟩) else 0

@[simp] theorem reverseDigits_apply {width : Nat} (digits : Fin width → Nat) (i : Fin width) :
    reverseDigits digits i.val = digits i.rev := by
  simp [reverseDigits, i.isLt]

end MinUncutGames.Foundations.Hastad.SourceRankPhase

namespace MinUncutGames.Foundations.Hastad.SourceAddressDescriptors

abbrev Descriptor := Fin 3 × ℕ

def realize (base : Fin 3 → ℕ) (d : Descriptor) : ℕ := d.2 + base d.1

end MinUncutGames.Foundations.Hastad.SourceAddressDescriptors

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_EquationEmit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceEquationEmit

open _root_.Turing Complexity
open SourceAddressDescriptors

inductive Label
  | seed | thirdDrain | thirdFork | thirdEmit
  | secondDrain | secondFork | secondEmit | firstDrain | firstFork | firstEmit
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.seed, .thirdDrain, .thirdFork, .thirdEmit,
  .secondDrain, .secondFork, .secondEmit, .firstDrain, .firstFork, .firstEmit]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (σ : Type) := σ × Option Bool

end MinUncutGames.Foundations.Hastad.SourceEquationEmit

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_DescriptorEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceTestAppend

open _root_.Turing Complexity
open SourceAddressDescriptors SourceEquationEmit

structure Layout (K : Type) where
  sources : Fin 3 → K
  temporary : K
  scratch : K
  accumulator : K
  sourceTemporary : ∀ side, sources side ≠ temporary
  sourceScratch : ∀ side, sources side ≠ scratch
  sourceAccumulator : ∀ side, sources side ≠ accumulator
  temporaryScratch : temporary ≠ scratch
  temporaryAccumulator : temporary ≠ accumulator
  scratchAccumulator : scratch ≠ accumulator

variable {K Λ : Type} [DecidableEq K]

def resultTapes (layout : Layout K) (base : K → List Bool) (bits : List Bool) : K → List Bool :=
  Function.update base layout.accumulator (bits.reverse ++ base layout.accumulator)

theorem resultTapes_other (layout : Layout K) (base : K → List Bool) (bits : List Bool)
    (k : K) (hk : k ≠ layout.accumulator) : resultTapes layout base bits k = base k := by
  simp [resultTapes, hk]

theorem resultTapes_source (layout : Layout K) (base : K → List Bool) (bits : List Bool)
    (side : Fin 3) : resultTapes layout base bits (layout.sources side) = base (layout.sources side) :=
  resultTapes_other layout base bits _ (layout.sourceAccumulator side)

theorem resultTapes_temporary (layout : Layout K) (base : K → List Bool) (bits : List Bool) :
    resultTapes layout base bits layout.temporary = base layout.temporary :=
  resultTapes_other layout base bits _ layout.temporaryAccumulator

theorem resultTapes_scratch (layout : Layout K) (base : K → List Bool) (bits : List Bool) :
    resultTapes layout base bits layout.scratch = base layout.scratch :=
  resultTapes_other layout base bits _ layout.scratchAccumulator

end MinUncutGames.Foundations.Hastad.SourceTestAppend

namespace MinUncutGames.Foundations.Hastad.SourceQueryLoop

open _root_.Turing Complexity

variable {K Λ : Type} [DecidableEq K]

theorem resultTapes_append (layout : SourceTestAppend.Layout K) (base : K → List Bool)
    (first second : List Bool) :
    SourceTestAppend.resultTapes layout
      (SourceTestAppend.resultTapes layout base first) second =
      SourceTestAppend.resultTapes layout base (first ++ second) := by
  funext k
  by_cases hk : k = layout.accumulator
  · subst k
    simp [SourceTestAppend.resultTapes, List.reverse_append, List.append_assoc]
  · simp [SourceTestAppend.resultTapes, hk]

end MinUncutGames.Foundations.Hastad.SourceQueryLoop

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RuntimeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.CookLevin.PolynomialMachine

section LiteralFields

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K]

def popN (k : K) : Nat → TM2.Stmt (fun _ : K => Bool) Λ σ →
    TM2.Stmt (fun _ : K => Bool) Λ σ
  | 0, continuation => continuation
  | n + 1, continuation => .pop k (fun state _ => state) (popN k n continuation)

theorem stepAux_popN (k : K) (n : Nat)
    (continuation : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (popN k n continuation) state tapes =
      TM2.stepAux continuation state (Function.update tapes k ((tapes k).drop n)) := by
  induction n generalizing tapes with
  | zero => simp [popN]
  | succ n ih =>
    simp only [popN, TM2.stepAux]
    rw [ih]
    simp only [Function.update_self, Function.update_idem, List.drop_tail]

end LiteralFields

noncomputable section

def prefixValuePolynomial (digits : Nat → Nat) : Nat → Polynomial Nat
  | 0 => 0
  | i + 1 => Polynomial.X * prefixValuePolynomial digits i + Polynomial.C (digits i)

def prefixCostPolynomial (digits : Nat → Nat) : Nat → Polynomial Nat
  | 0 => 0
  | i + 1 => prefixCostPolynomial digits i +
      Polynomial.C 3 * Polynomial.X * prefixValuePolynomial digits i +
      Polynomial.C 9 * prefixValuePolynomial digits i + Polynomial.C (3 * digits i + 14)

end

end MinUncutGames.Foundations.Complexity.CookLevin.PolynomialMachine

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_HeaderCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MinUncutGames.Foundations.Hastad.SourceHeaderCounts

open _root_.Turing Complexity

noncomputable section

variable {u D : Nat} {K Λ σ : Type}

variable [DecidableEq K]

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end

end MinUncutGames.Foundations.Hastad.SourceHeaderCounts

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_HeaderAccumulate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceBasePhase

open _root_.Turing Complexity
open SourceAddressDescriptors

inductive Label
  | seed
  | horner (label : MachineHorner.Label 2)
  | clear
  deriving DecidableEq, Fintype

def digits (coefficient offset : Nat) (i : Nat) : Nat :=
  if i = 0 then coefficient else offset

noncomputable def timePolynomial (coefficient : Nat) : Polynomial Nat :=
  (MachineHorner.timePolynomial 2).comp (Polynomial.X + Polynomial.C coefficient) +
    Polynomial.C (coefficient + 2)

theorem timePolynomial_eval (coefficient n : Nat) :
    (timePolynomial coefficient).eval n =
      (MachineHorner.timePolynomial 2).eval (n + coefficient) + coefficient + 2 := by
  simp [timePolynomial, Polynomial.eval_comp, Nat.add_assoc]

end MinUncutGames.Foundations.Hastad.SourceBasePhase

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineTupleOdometer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineTupleOdometer

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K]

section AscendingCycle

open scoped BigOperators

def cycleSteps (cost : ℕ → ℕ) (maximum count : ℕ) : ℕ :=
  (∑ r ∈ Finset.range (count + 1), cost r) + count + maximum + 2

theorem cycleSteps_zero (cost : ℕ → ℕ) (maximum : ℕ) :
    cycleSteps cost maximum 0 = (maximum + 2) + cost 0 := by
  simp [cycleSteps, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem cycleSteps_succ (cost : ℕ → ℕ) (maximum count : ℕ) :
    cycleSteps cost maximum (count + 1) =
      (cycleSteps cost maximum count + 1) + cost (count + 1) := by
  simp only [cycleSteps, Finset.sum_range_succ]
  omega

end AscendingCycle

section Order

omit [DecidableEq K]

open scoped BigOperators

theorem tupleRank_snoc {n q : ℕ} (tail : Fin q → Fin n) (d : Fin n) :
    (finFunctionFinEquiv (Fin.snoc tail d)).val =
      (finFunctionFinEquiv tail).val + d.val * n ^ q := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  rfl

end Order

section Nested

open scoped BigOperators

structure CycleSchedule (K σ : Type) where
  currentSuffix : List Bool
  remainingSuffix : List Bool
  ambient : ℕ → σ
  register : ℕ → Option Bool
  base : ℕ → K → List Bool

omit [DecidableEq K] in

def counterOverhead (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | q + 1 => n * (counterOverhead n q + 2)

namespace NestedCycle

variable {n : ℕ}
  {current remaining : ℕ → K}
  {bodyLabel : Λ}
  {checkLabel resetLabel : ℕ → Λ}

def reverseDigit (d : Fin n) : Fin n := ⟨n - 1 - d.val, by omega⟩

end NestedCycle

omit [DecidableEq K] in
theorem counterOverhead_le (n q : ℕ) (hn : 0 < n) :
    counterOverhead n q ≤ 2 * q * n ^ q := by
  induction q with
  | zero => simp [counterOverhead]
  | succ q ih =>
    have hp : 1 ≤ n ^ q := by apply Nat.one_le_pow; exact hn
    have h := Nat.mul_le_mul_left n (Nat.add_le_add_right ih 2)
    have htwo : 2 ≤ 2 * n ^ q := Nat.mul_le_mul_left 2 hp
    have hinner : 2 * q * n ^ q + 2 ≤ 2 * (q + 1) * n ^ q := by
      rw [Nat.mul_add, Nat.add_mul]
      omega
    exact h.trans (by
      simpa only [counterOverhead, pow_succ, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using Nat.mul_le_mul_left n hinner)

end Nested

end MinUncutGames.Foundations.Complexity.MachineTupleOdometer

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ContextClear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceContextClear

open _root_.Turing Complexity

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.Hastad.SourceContextClear

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Gap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceOdometerSchedule

open _root_.Turing Complexity MachineTupleOdometer

variable {u m : ℕ} {Extra Λ σ : Type} [DecidableEq Extra]

def blockPrefix (blocks : ℕ → List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => blockPrefix blocks n ++ blocks n

theorem blockPrefix_eq_ofFn (blocks : ℕ → List Bool) (n : ℕ) :
    blockPrefix blocks n = (List.ofFn (fun i : Fin n => blocks i.val)).flatten := by
  induction n with
  | zero => simp [blockPrefix]
  | succ n ih =>
    rw [blockPrefix, List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simpa only [Fin.val_castSucc, Fin.val_last, List.flatten_cons,
      List.flatten_nil, List.append_nil] using congrArg (fun xs => xs ++ blocks n) ih

theorem val_snoc {q : ℕ} (c : Fin q → Fin m) (d : Fin m) :
    (fun i : Fin (q + 1) => (Fin.snoc (α := fun _ => Fin m) c d i).val) =
      Fin.snoc (fun i => (c i).val) d.val := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem zeros_snoc (q : ℕ) :
    Fin.snoc (fun _ : Fin q => (0 : ℕ)) 0 = fun _ : Fin (q + 1) => 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

end MinUncutGames.Foundations.Hastad.SourceOdometerSchedule

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_TupleBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceTupleBound

open Complexity

variable {u D : Nat}

noncomputable def rankPolynomial (u : Nat) : Polynomial Nat := Polynomial.X ^ u
noncomputable def numberPolynomial (u : Nat) : Polynomial Nat :=
  Polynomial.C (SourceBounds.bitCoefficient u) * Polynomial.X ^ u

@[simp] theorem rankPolynomial_eval (u L : Nat) : (rankPolynomial u).eval L = L ^ u := by
  simp [rankPolynomial]
@[simp] theorem numberPolynomial_eval (u L : Nat) :
    (numberPolynomial u).eval L = SourceBounds.bitCoefficient u * L ^ u := by
  simp [numberPolynomial]

noncomputable def finishPolynomial (u : Nat) : Polynomial Nat :=
  Polynomial.C 1 + (numberPolynomial u + Polynomial.C 2) + Polynomial.C 2 +
    (Polynomial.C (6 * u) * (Polynomial.X + Polynomial.C 1) + Polynomial.C 1) + Polynomial.C 1

theorem finishPolynomial_eval (u L : Nat) :
    (finishPolynomial u).eval L =
      1 + (SourceBounds.bitCoefficient u * L ^ u + 2) + 2 + (6 * u * (L + 1) + 1) + 1 := by
  simp only [finishPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, numberPolynomial_eval]

end MinUncutGames.Foundations.Hastad.SourceTupleBound

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_CayleySampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.SpectralReturn

open scoped BigOperators

noncomputable section

def edgeProfile {V D : Type*} [Fintype D] (bad : V × D → Bool) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then 1 else 0)

theorem geometric_sum_le (lambda : ℝ) (h0 : 0 ≤ lambda) (h1 : lambda < 1) (n : Nat) :
    (∑ k ∈ Finset.range n, lambda ^ k) ≤ 1 / (1 - lambda) := by
  have hsum : (∑ k ∈ Finset.range n, lambda ^ k) * (1 - lambda) = 1 - lambda ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith
  have hden : 0 < 1 - lambda := by linarith
  apply (le_div_iff₀ hden).2
  rw [hsum]
  linarith [pow_nonneg h0 n]

end

end MinUncutGames.Foundations.PCP.SpectralReturn

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_CayleySpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.ZigzagSpectral

open SpectralReturn

noncomputable section

variable {V D E : Type*}

def liftCloud (f : V → ℝ) (x : V × D) : ℝ := f x.1

end

end MinUncutGames.Foundations.PCP.ZigzagSpectral

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCloudPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineCloudPadding

open _root_.Turing
open MinUncutGames.Foundations.PCP

variable {σ : Type}

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

end MinUncutGames.Foundations.Complexity.MachineCloudPadding

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Overlay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.LazySmoothing

open scoped BigOperators

def bitCount {n : ℕ} (tape : Fin n → Bool) : ℕ :=
  ∑ i, if tape i then 1 else 0

noncomputable def binomialMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  Finset.univ.expect (fun tape : Fin n → Bool => g (bitCount tape))

def splitTape (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Bool × (Fin n → Bool)) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv _ := rfl

theorem bitCount_succ {n : ℕ} (x : Fin (n + 1) → Bool) :
    bitCount x = (if x 0 then 1 else 0) + bitCount (fun i => x i.succ) := by
  exact Fin.sum_univ_succ _

theorem mean_congr {n : ℕ} {f g : ℕ → ℝ} (h : ∀ k, f k = g k) :
    binomialMean n f = binomialMean n g := by
  unfold binomialMean
  exact Finset.expect_congr rfl (fun x _ => h (bitCount x))

@[simp] theorem mean_const (n : ℕ) (c : ℝ) :
    binomialMean n (fun _ => c) = c := Fintype.expect_const c

theorem mean_add (n : ℕ) (f g : ℕ → ℝ) :
    binomialMean n (fun k => f k + g k) = binomialMean n f + binomialMean n g :=
  Finset.expect_add_distrib _ _ _

theorem mean_sub (n : ℕ) (f g : ℕ → ℝ) :
    binomialMean n (fun k => f k - g k) = binomialMean n f - binomialMean n g :=
  Finset.expect_sub_distrib _ _ _

theorem mean_mul (n : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    binomialMean n (fun k => c * f k) = c * binomialMean n f := by
  exact (Finset.mul_expect Finset.univ (fun x : Fin n → Bool => f (bitCount x)) c).symm

@[simp] theorem mean_zero (g : ℕ → ℝ) : binomialMean 0 g = g 0 := by
  simp [binomialMean, bitCount]

theorem expect_bool (f : Bool → ℝ) : Finset.univ.expect f = (f false + f true) / 2 := by
  rw [Finset.expect_eq_sum_div_card]
  simp [Fintype.univ_bool, add_comm]

theorem mean_succ (n : ℕ) (g : ℕ → ℝ) :
    binomialMean (n + 1) g =
      (binomialMean n g + binomialMean n (fun k => g (k + 1))) / 2 := by
  unfold binomialMean
  rw [Fintype.expect_equiv (splitTape n)
    (fun x => g (bitCount x))
    (fun x => g ((if x.1 then 1 else 0) + bitCount x.2))
    (fun x => congrArg g (bitCount_succ x))]
  rw [← Finset.univ_product_univ, Finset.expect_product, expect_bool]
  simp [Nat.add_comm]

def score (n k : ℕ) : ℝ := (n : ℝ) - 2 * (k : ℝ)

noncomputable def scoreMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  binomialMean n (fun k => score n k * g k)

@[simp] theorem scoreMean_zero (g : ℕ → ℝ) : scoreMean 0 g = 0 := by
  simp [scoreMean, score]

theorem scoreMean_succ (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g =
      ((scoreMean n g + binomialMean n g) +
       (scoreMean n (fun k => g (k + 1)) -
        binomialMean n (fun k => g (k + 1)))) / 2 := by
  unfold scoreMean
  rw [mean_succ]
  have h₁ : (fun k => score (n + 1) k * g k) =
      (fun k => score n k * g k + g k) := by
    funext k
    simp only [score, Nat.cast_add, Nat.cast_one]
    ring
  have h₂ : (fun k => score (n + 1) (k + 1) * g (k + 1)) =
      (fun k => score n k * g (k + 1) - g (k + 1)) := by
    funext k
    simp only [score, Nat.cast_add, Nat.cast_one]
    ring
  rw [h₁, h₂, mean_add, mean_sub]

theorem score_identity (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g = ((n : ℝ) + 1) / 2 *
      (binomialMean n g - binomialMean n (fun k => g (k + 1))) := by
  induction n generalizing g with
  | zero => simp [scoreMean_succ]; ring
  | succ n ih =>
    rw [scoreMean_succ, ih g, ih (fun k => g (k + 1))]
    simp only [mean_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem score_mean_zero (n : ℕ) : binomialMean n (score n) = 0 := by
  cases n with
  | zero => simp [score]
  | succ n =>
    have h := score_identity n (fun _ => 1)
    simpa [scoreMean] using h

theorem score_second_moment (n : ℕ) :
    binomialMean n (fun k => score n k ^ 2) = (n : ℝ) := by
  cases n with
  | zero => simp [score]
  | succ n =>
    have h := score_identity n (score (n + 1))
    have hd : binomialMean n (score (n + 1)) -
        binomialMean n (fun k => score (n + 1) (k + 1)) = 2 := by
      rw [← mean_sub]
      calc
        _ = binomialMean n (fun _ => 2) := by
          apply mean_congr
          intro k
          simp only [score, Nat.cast_add, Nat.cast_one]
          ring
        _ = 2 := mean_const _ _
    rw [hd] at h
    simpa [scoreMean, pow_two] using h

theorem score_difference (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g = ((n : ℝ) + 1) *
      (binomialMean n g - binomialMean (n + 1) g) := by
  rw [score_identity, mean_succ]
  ring

theorem adjacent_difference_sq (n : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    4 * ((n : ℝ) + 1) *
      (binomialMean n g - binomialMean (n + 1) g) ^ 2 ≤ 1 := by
  have hc : binomialMean (n + 1)
      (fun k => score (n + 1) k * (g k - 1 / 2)) = scoreMean (n + 1) g := by
    calc
      _ = binomialMean (n + 1) (fun k =>
          score (n + 1) k * g k - (1 / 2) * score (n + 1) k) := by
        apply mean_congr
        intro k
        ring
      _ = scoreMean (n + 1) g := by
        rw [mean_sub, mean_mul, score_mean_zero]
        simp [scoreMean]
  have hv : binomialMean (n + 1) (fun k => (g k - 1 / 2) ^ 2) ≤ 1 / 4 := by
    apply Finset.expect_le Finset.univ_nonempty
    intro tape _
    have h₀ := (hg (bitCount tape)).1
    have h₁ := (hg (bitCount tape)).2
    have hp := mul_nonneg h₀ (sub_nonneg.mpr h₁)
    nlinarith
  have hcs : (binomialMean (n + 1)
        (fun k => score (n + 1) k * (g k - 1 / 2))) ^ 2 ≤
      binomialMean (n + 1) (fun k => score (n + 1) k ^ 2) *
        binomialMean (n + 1) (fun k => (g k - 1 / 2) ^ 2) :=
    Finset.expect_mul_sq_le_sq_mul_sq Finset.univ _ _
  rw [hc, score_difference, score_second_moment] at hcs
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hm := mul_le_mul_of_nonneg_left hv (le_of_lt hn)
  simp only [Nat.cast_add, Nat.cast_one] at hcs
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith

theorem adjacent_difference_le (n : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrn : r ^ 2 ≤ 4 * ((n : ℝ) + 1)) :
    |binomialMean n g - binomialMean (n + 1) g| ≤ 1 / r := by
  have hs := adjacent_difference_sq n g hg
  have hd := sq_nonneg (binomialMean n g - binomialMean (n + 1) g)
  have hh := mul_le_mul_of_nonneg_right hrn hd
  rw [le_div_iff₀ hr]
  have ha := sq_abs (binomialMean n g - binomialMean (n + 1) g)
  have hp : 0 ≤ |binomialMean n g - binomialMean (n + 1) g| * r :=
    mul_nonneg (abs_nonneg _) (le_of_lt hr)
  nlinarith [sq_nonneg (|binomialMean n g - binomialMean (n + 1) g| * r - 1)]

theorem mean_shift_le (n d : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrn : r ^ 2 ≤ 4 * ((n : ℝ) + 1)) :
    |binomialMean (n + d) g - binomialMean n g| ≤ (d : ℝ) / r := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hrnd : r ^ 2 ≤ 4 * ((n + d : ℕ) + 1 : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      linarith
    have ha := adjacent_difference_le (n + d) g hg r hr hrnd
    rw [abs_sub_comm] at ha
    calc
      _ ≤ |binomialMean (n + d + 1) g - binomialMean (n + d) g| +
          |binomialMean (n + d) g - binomialMean n g| := abs_sub_le _ _ _
      _ ≤ 1 / r + (d : ℝ) / r := add_le_add ha ih
      _ = ((d + 1 : ℕ) : ℝ) / r := by push_cast; ring

theorem mean_ordered_difference_le (m n : ℕ) (hmn : m ≤ n) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrm : r ^ 2 ≤ 4 * ((m : ℝ) + 1)) :
    |binomialMean n g - binomialMean m g| ≤ ((n - m : ℕ) : ℝ) / r := by
  simpa [Nat.add_sub_of_le hmn] using mean_shift_le m (n - m) g hg r hr hrm

theorem mean_window_le (N M m : ℕ) (hlo : N - M ≤ m) (hhi : m ≤ N + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1)
    (r : ℝ) (hr : 0 < r) (hbase : r ^ 2 ≤ 4 * (((N - M : ℕ) : ℝ) + 1)) :
    |binomialMean m g - binomialMean N g| ≤ (M : ℝ) / r := by
  by_cases hmN : m ≤ N
  · have hrm : r ^ 2 ≤ 4 * ((m : ℝ) + 1) := by
      have : ((N - M : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlo
      linarith
    have h := mean_ordered_difference_le m N hmN g hg r hr hrm
    rw [abs_sub_comm] at h
    refine h.trans (div_le_div_of_nonneg_right ?_ (le_of_lt hr))
    have : N - m ≤ M := by omega
    exact_mod_cast this
  · have hNm : N ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmN)
    have hrN : r ^ 2 ≤ 4 * ((N : ℝ) + 1) := by
      have : ((N - M : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N M
      linarith
    have h := mean_ordered_difference_le N m hNm g hg r hr hrN
    refine h.trans (div_le_div_of_nonneg_right ?_ (le_of_lt hr))
    have : m - N ≤ M := by omega
    exact_mod_cast this

theorem square_window_le (q M m : ℕ) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    |binomialMean m g - binomialMean ((4 * q * M) ^ 2) g| ≤ 1 / (4 * (q : ℝ)) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hR : (4 : ℝ) * M ≤ ((4 * q * M : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hRM : (M : ℝ) ≤ (((4 * q * M : ℕ) : ℝ)) ^ 2 := by nlinarith
  have hMN : M ≤ (4 * q * M) ^ 2 := by exact_mod_cast hRM
  have hr : (0 : ℝ) < ((4 * q * M : ℕ) : ℝ) := by linarith
  have hb : (((4 * q * M : ℕ) : ℝ)) ^ 2 ≤
      4 * (((((4 * q * M) ^ 2 - M : ℕ)) : ℝ) + 1) := by
    rw [Nat.cast_sub hMN, Nat.cast_pow]
    nlinarith
  have h := mean_window_le ((4 * q * M) ^ 2) M m hlo hhi g hg
    ((4 * q * M : ℕ) : ℝ) hr hb
  have he : (M : ℝ) / ((4 * q * M : ℕ) : ℝ) = 1 / (4 * (q : ℝ)) := by
    push_cast
    have hq0 : (q : ℝ) ≠ 0 := by linarith
    have hM0 : (M : ℝ) ≠ 0 := by linarith
    field_simp
  rw [he] at h
  exact h

theorem modal_transfer (q M m : ℕ) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1)
    (hmodal : 1 / (q : ℝ) ≤ binomialMean ((4 * q * M) ^ 2) g) :
    1 / (2 * (q : ℝ)) ≤ binomialMean m g := by
  have h := square_window_le q M m hq hM hlo hhi g hg
  have hqR : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hrec : 0 < 1 / (q : ℝ) := one_div_pos.mpr hqR
  have he₁ : 1 / (4 * (q : ℝ)) = (1 / (q : ℝ)) / 4 := by ring
  have he₂ : 1 / (2 * (q : ℝ)) = (1 / (q : ℝ)) / 2 := by ring
  rw [he₁] at h
  rw [he₂]
  have hl := (abs_le.mp h).1
  linarith

end MinUncutGames.Foundations.PCP.LazySmoothing

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_GraphGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.CloudRounding

open scoped BigOperators

theorem dart_rejection_count_le
    {E V A : Type*} [Fintype E] [DecidableEq A]
    (tail : E → V) (reverse : E ≃ E) (accepts : E → A → A → Bool)
    (ell : E → A) (rounded : V → A) :
    (Finset.univ.filter (fun e =>
      accepts e (rounded (tail e)) (rounded (tail (reverse e))) = false)).card ≤
    (Finset.univ.filter (fun e => accepts e (ell e) (ell (reverse e)) = false)).card +
      2 * (Finset.univ.filter (fun e => ell e ≠ rounded (tail e))).card := by
  classical
  let R : Finset E := Finset.univ.filter (fun e =>
    accepts e (rounded (tail e)) (rounded (tail (reverse e))) = false)
  let B : Finset E := Finset.univ.filter (fun e =>
    accepts e (ell e) (ell (reverse e)) = false)
  let M : Finset E := Finset.univ.filter (fun e => ell e ≠ rounded (tail e))
  let MR : Finset E := Finset.univ.filter (fun e =>
    ell (reverse e) ≠ rounded (tail (reverse e)))
  have hrev : MR.card = M.card := by
    have hsets : MR = M.map reverse.symm.toEmbedding := by
      ext e
      constructor
      · intro he
        apply Finset.mem_map.mpr
        refine ⟨reverse e, ?_, reverse.symm_apply_apply e⟩
        simpa [MR, M] using he
      · intro he
        obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp he
        simpa [MR, M] using hd
    rw [hsets, Finset.card_map]
  have hsub : R ⊆ (B ∪ M) ∪ MR := by
    intro e he
    by_cases hl : ell e = rounded (tail e)
    · by_cases hr : ell (reverse e) = rounded (tail (reverse e))
      · have hb : e ∈ B := by simpa [B, R, hl, hr] using he
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
      · exact Finset.mem_union_right _ (by simp [MR, hr])
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [M, hl]))
  change R.card ≤ B.card + 2 * M.card
  calc
    R.card ≤ ((B ∪ M) ∪ MR).card := Finset.card_le_card hsub
    _ ≤ (B ∪ M).card + MR.card := Finset.card_union_le _ _
    _ ≤ (B.card + M.card) + MR.card :=
      Nat.add_le_add_right (Finset.card_union_le B M) _
    _ = B.card + 2 * M.card := by rw [hrev]; omega

section CloudCounts

variable {X A D : Type*} [Fintype X] [Fintype A] [Fintype D]
variable [DecidableEq X] [DecidableEq A]

def colorSet (ell : X → A) (a : A) : Finset X :=
  Finset.univ.filter (fun x => ell x = a)

def minoritySet (ell : X → A) (m : A) : Finset X :=
  Finset.univ.filter (fun x => ell x ≠ m)

def directedCut (next : X × D → X) (S : Finset X) : Finset (X × D) :=
  Finset.univ.filter (fun xd => xd.1 ∈ S ∧ next xd ∉ S)

def disagreementSet (ell : X → A) (next : X × D → X) : Finset (X × D) :=
  Finset.univ.filter (fun xd => ell xd.1 ≠ ell (next xd))

abbrev Nonmajor (m : A) := {a : A // a ≠ m}

omit [DecidableEq X] in
theorem exists_max_color (ell : X → A) [Nonempty A] :
    ∃ m : A, ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ
    (fun a : A => (colorSet ell a).card) Finset.univ_nonempty
  exact ⟨m, fun a => hm a (Finset.mem_univ a)⟩

noncomputable def majority (ell : X → A) [Nonempty A] : A :=
  Classical.choose (exists_max_color ell)

omit [DecidableEq X] in
theorem majority_maximal (ell : X → A) [Nonempty A] (a : A) :
    (colorSet ell a).card ≤ (colorSet ell (majority ell)).card :=
  Classical.choose_spec (exists_max_color ell) a

omit [Fintype A] in
theorem nonchosen_color_twice_le (ell : X → A) (m : A)
    (maximal : ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card)
    (a : A) (ha : a ≠ m) :
    2 * (colorSet ell a).card ≤ Fintype.card X := by
  have hd : Disjoint (colorSet ell a) (colorSet ell m) := by
    apply Finset.disjoint_left.mpr
    intro x hx hm
    have hxa : ell x = a := by simpa [colorSet] using hx
    have hxm : ell x = m := by simpa [colorSet] using hm
    exact ha (hxa.symm.trans hxm)
  have hu : (colorSet ell a).card + (colorSet ell m).card ≤ Fintype.card X := by
    calc
      _ = (colorSet ell a ∪ colorSet ell m).card :=
        (Finset.card_union_of_disjoint hd).symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card X := Finset.card_univ
  have hm := maximal a
  omega

def minorityEquiv (ell : X → A) (m : A) :
    (Σ a : Nonmajor m, ↥(colorSet ell a.val)) ≃ ↥(minoritySet ell m) where
  toFun t := ⟨t.2.val, by
    have hc : ell t.2.val = t.1.val := (Finset.mem_filter.mp t.2.property).2
    have hn : ell t.2.val ≠ m := fun h => t.1.property (hc.symm.trans h)
    simpa [minoritySet] using hn⟩
  invFun x :=
    ⟨⟨ell x.val, by simpa [minoritySet] using x.property⟩,
      ⟨x.val, by simp [colorSet]⟩⟩
  left_inv t := by
    rcases t with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    have hxa : ell x = a := by simpa [colorSet] using hx
    cases hxa
    rfl
  right_inv x := by apply Subtype.ext; rfl

omit [DecidableEq X] in
theorem minority_card_eq_sum (ell : X → A) (m : A) :
    (minoritySet ell m).card = ∑ a : Nonmajor m, (colorSet ell a.val).card := by
  have h := Fintype.card_congr (minorityEquiv ell m)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

def minorityCutEmbedding (ell : X → A) (next : X × D → X) (m : A) :
    (Σ a : Nonmajor m, ↥(directedCut next (colorSet ell a.val))) ↪
      ↥(disagreementSet ell next) where
  toFun t := ⟨t.2.val, by
    have hc : ell t.2.val.1 = t.1.val ∧ ell (next t.2.val) ≠ t.1.val := by
      simpa [directedCut, colorSet] using t.2.property
    have hn : ell t.2.val.1 ≠ ell (next t.2.val) :=
      fun h => hc.2 (h.symm.trans hc.1)
    simpa [disagreementSet] using hn⟩
  inj' p q h := by
    rcases p with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    rcases q with ⟨⟨b, hb⟩, ⟨y, hy⟩⟩
    have hxy : x = y := congrArg Subtype.val h
    cases hxy
    have hxa : ell x.1 = a := by
      have hc : ell x.1 = a ∧ ell (next x) ≠ a := by
        simpa [directedCut, colorSet] using hx
      exact hc.1
    have hxb : ell x.1 = b := by
      have hc : ell x.1 = b ∧ ell (next x) ≠ b := by
        simpa [directedCut, colorSet] using hy
      exact hc.1
    have hab : a = b := hxa.symm.trans hxb
    cases hab
    rfl

theorem minority_cut_sum_le (ell : X → A) (next : X × D → X) (m : A) :
    (∑ a : Nonmajor m, (directedCut next (colorSet ell a.val)).card) ≤
      (disagreementSet ell next).card := by
  have h := Fintype.card_le_of_injective
    (minorityCutEmbedding ell next m) (minorityCutEmbedding ell next m).injective
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h

theorem minority_expansion_bound (ell : X → A) (next : X × D → X) (m : A)
    (h : ℚ)
    (maximal : ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card)
    (expansion : ∀ S : Finset X, S.card ≤ Fintype.card X / 2 →
      h * (S.card : ℚ) ≤ ((directedCut next S).card : ℚ)) :
    h * ((minoritySet ell m).card : ℚ) ≤ ((disagreementSet ell next).card : ℚ) := by
  have each (a : Nonmajor m) :
      h * ((colorSet ell a.val).card : ℚ) ≤
        ((directedCut next (colorSet ell a.val)).card : ℚ) := by
    apply expansion
    have ha := nonchosen_color_twice_le ell m maximal a.val a.property
    omega
  calc
    h * ((minoritySet ell m).card : ℚ) =
        ∑ a : Nonmajor m, h * ((colorSet ell a.val).card : ℚ) := by
      rw [minority_card_eq_sum, Nat.cast_sum, Finset.mul_sum]
    _ ≤ ∑ a : Nonmajor m, ((directedCut next (colorSet ell a.val)).card : ℚ) :=
      Finset.sum_le_sum (fun a _ => each a)
    _ ≤ ((disagreementSet ell next).card : ℚ) := by
      exact_mod_cast minority_cut_sum_le ell next m

end CloudCounts

end MinUncutGames.Foundations.PCP.CloudRounding

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SpectralCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncutGames.Foundations.PCP.SpectralCut

open scoped BigOperators
open SpectralReturn

section Indicators
variable {V : Type*} [Fintype V] [DecidableEq V]

def indicator (S : Finset V) (v : V) : ℝ := if v ∈ S then 1 else 0

omit [Fintype V] in
theorem indicator_nonnegative (S : Finset V) (v : V) : 0 ≤ indicator S v := by
  unfold indicator
  split_ifs <;> norm_num
end Indicators

end MinUncutGames.Foundations.PCP.SpectralCut


end
namespace MinUncutGames.Foundations.PCP.LazySpectral

open SpectralReturn

noncomputable section

variable {V D : Type*}

theorem half_sum_sq_le (a b : ℝ) : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]

end

end MinUncutGames.Foundations.PCP.LazySpectral

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingTableSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringDecoding

open scoped BigOperators

variable {Ω A : Type*} [Fintype Ω] [Nonempty Ω] [Fintype A] [Nonempty A]

noncomputable def mass (opinion : Ω → A) (a : A) : ℝ := by
  classical
  exact Finset.univ.expect (fun ω => if opinion ω = a then 1 else 0)

omit [Nonempty A] in
theorem mass_sum (opinion : Ω → A) : (∑ a, mass opinion a) = 1 := by
  classical
  calc
    (∑ a, mass opinion a) =
        (Finset.univ : Finset Ω).expect
          (fun ω => ∑ a : A, if opinion ω = a then (1 : ℝ) else 0) :=
      (Finset.expect_sum_comm (Finset.univ : Finset Ω) (Finset.univ : Finset A)
        (fun ω a => if opinion ω = a then (1 : ℝ) else 0)).symm
    _ = (Finset.univ : Finset Ω).expect (fun _ => (1 : ℝ)) := by
      apply Finset.expect_congr rfl
      intro ω _
      simp
    _ = 1 := Finset.expect_const Finset.univ_nonempty 1

omit [Nonempty Ω] in
theorem exists_mode (opinion : Ω → A) :
    ∃ a : A, ∀ b : A, mass opinion b ≤ mass opinion a := by
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset A)
    (mass opinion) Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

noncomputable def mode (opinion : Ω → A) : A := Classical.choose (exists_mode opinion)

omit [Nonempty Ω] in
theorem mode_max (opinion : Ω → A) (b : A) :
    mass opinion b ≤ mass opinion (mode opinion) :=
  Classical.choose_spec (exists_mode opinion) b

theorem mode_mass_lower (opinion : Ω → A) :
    1 / (Fintype.card A : ℝ) ≤ mass opinion (mode opinion) := by
  have hk : 0 < (Fintype.card A : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : (1 : ℝ) ≤ mass opinion (mode opinion) * (Fintype.card A : ℝ) := by
    calc
      (1 : ℝ) = ∑ a : A, mass opinion a := (mass_sum opinion).symm
      _ ≤ ∑ _a : A, mass opinion (mode opinion) :=
        Finset.sum_le_sum (fun a _ => mode_max opinion a)
      _ = mass opinion (mode opinion) * (Fintype.card A : ℝ) := by simp [mul_comm]
  exact (div_le_iff₀ hk).2 hsum

end MinUncutGames.Foundations.PCP.PoweringDecoding

end
section
noncomputable section

namespace MinUncutGames.Foundations.PCP.PoweringMoment

open scoped BigOperators

def bit (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

def hits {I Ω : Type*} [Fintype I] (E : I → Ω → Prop) (ω : Ω) : ℝ :=
  ∑ i, bit (E i ω)

def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ := Finset.univ.expect f

theorem bit_nonneg (p : Prop) : 0 ≤ bit p := by
  classical
  by_cases hp : p <;> simp [bit, hp]

theorem bit_sq (p : Prop) : bit p ^ 2 = bit p := by
  classical
  by_cases hp : p <;> simp [bit, hp]

theorem bit_mul (p q : Prop) : bit p * bit q = bit (p ∧ q) := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [bit, hp, hq]

theorem bit_mono {p q : Prop} (hpq : p → q) : bit p ≤ bit q := by
  classical
  by_cases hp : p
  · simp [bit, hp, hpq hp]
  · have hz : bit p = 0 := by simp [bit, hp]
    rw [hz]
    exact bit_nonneg q

theorem hits_nonneg {I Ω : Type*} [Fintype I] (E : I → Ω → Prop) (ω : Ω) :
    0 ≤ hits E ω := Finset.sum_nonneg (fun i _ => bit_nonneg (E i ω))

theorem mean_nonneg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ mean f := Finset.expect_nonneg (fun ω _ => hf ω)

theorem mean_hits {I Ω : Type*} [Fintype I] [Fintype Ω] (E : I → Ω → Prop) :
    mean (hits E) = ∑ i, mean (fun ω => bit (E i ω)) := by
  exact Finset.expect_sum_comm _ _ _

theorem second_moment_eq {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E : I → Ω → Prop) :
    mean (fun ω => hits E ω ^ 2) =
      ∑ i, ∑ j, mean (fun ω => bit (E i ω ∧ E j ω)) := by
  simp only [hits, pow_two, Finset.sum_mul, Finset.mul_sum, bit_mul,
    mean, Finset.expect_sum_comm]
  exact Finset.sum_comm

theorem mean_witness_sq_le {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E W : I → Ω → Prop) (reject : Ω → Prop)
    (hWE : ∀ i ω, W i ω → E i ω)
    (hWR : ∀ i ω, W i ω → reject ω) :
    mean (hits W) ^ 2 ≤
      mean (fun ω => bit (reject ω)) * mean (fun ω => hits E ω ^ 2) := by
  classical
  have hNH (ω : Ω) : hits W ω ≤ hits E ω :=
    Finset.sum_le_sum (fun i _ => bit_mono (hWE i ω))
  have hzero (ω : Ω) (hr : ¬ reject ω) : hits W ω = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hw : ¬ W i ω := fun h => hr (hWR i ω h)
    simp [bit, hw]
  have hsupport (ω : Ω) : bit (reject ω) * hits W ω = hits W ω := by
    by_cases hr : reject ω
    · simp [bit, hr]
    · rw [hzero ω hr]
      simp
  have hCS := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun ω => bit (reject ω)) (hits W)
  have hsquares : mean (fun ω => hits W ω ^ 2) ≤ mean (fun ω => hits E ω ^ 2) := by
    apply Finset.expect_le_expect
    intro ω _
    simpa only [pow_two] using
      (mul_le_mul (hNH ω) (hNH ω) (hits_nonneg W ω) (hits_nonneg E ω))
  calc
    _ ≤ mean (fun ω => bit (reject ω)) * mean (fun ω => hits W ω ^ 2) := by
      simpa only [mean, hsupport, bit_sq] using hCS
    _ ≤ _ := mul_le_mul_of_nonneg_left hsquares
      (mean_nonneg _ (fun ω => bit_nonneg (reject ω)))

theorem rejection_lower_bound {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E W : I → Ω → Prop) (reject : Ω → Prop)
    (hWE : ∀ i ω, W i ω → E i ω)
    (hWR : ∀ i ω, W i ω → reject ω)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hfirst : a ≤ mean (hits W))
    (hsecond : mean (fun ω => hits E ω ^ 2) ≤ b) :
    a ^ 2 / b ≤ mean (fun ω => bit (reject ω)) := by
  have hN : 0 ≤ mean (hits W) := mean_nonneg _ (hits_nonneg W)
  have hρ : 0 ≤ mean (fun ω => bit (reject ω)) :=
    mean_nonneg _ (fun ω => bit_nonneg (reject ω))
  have haSq : a ^ 2 ≤ mean (hits W) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hfirst hfirst ha.le hN
  have hCS := mean_witness_sq_le E W reject hWE hWR
  apply (div_le_iff₀ hb).2
  exact haSq.trans (hCS.trans (mul_le_mul_of_nonneg_left hsecond hρ))

end MinUncutGames.Foundations.PCP.PoweringMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringReturn

open SpectralReturn
open PoweringMoment (bit)

variable {V D : Type*}

def portConsEquiv (D : Type*) (n : Nat) :
    (D × (Fin n → D)) ≃ (Fin (n + 1) → D) where
  toFun z := Fin.cases z.1 z.2
  invFun r := (r 0, fun j => r j.succ)
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext j
      rfl
  right_inv r := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

theorem bit_bool (b : Bool) : bit (b = true) = (if b then 1 else 0 : ℝ) := by
  cases b <;> simp [bit]

end MinUncutGames.Foundations.PCP.PoweringReturn

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringTableSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open MinUncutGames.Foundations.Hastad

def disagreement (a b : Bool) : ℝ := if a = b then 0 else 1

@[simp] theorem disagreement_self (a : Bool) : disagreement a a = 0 := by
  simp [disagreement]

theorem disagreement_nonnegative (a b : Bool) : 0 ≤ disagreement a b := by
  cases a <;> cases b <;> norm_num [disagreement]

theorem disagreement_comm (a b : Bool) : disagreement a b = disagreement b a := by
  simp [disagreement, eq_comm]

theorem disagreement_triangle (a b c : Bool) :
    disagreement a c ≤ disagreement a b + disagreement b c := by
  cases a <;> cases b <;> cases c <;> norm_num [disagreement]

def relativeDistance {X : Type*} [Fintype X] (f g : X → Bool) : ℝ :=
  𝔼 x, disagreement (f x) (g x)

@[simp] theorem relativeDistance_self {X : Type*} [Fintype X] (f : X → Bool) :
    relativeDistance f f = 0 := by
  simp [relativeDistance]

theorem relativeDistance_nonnegative {X : Type*} [Fintype X] (f g : X → Bool) :
    0 ≤ relativeDistance f g :=
  Finset.expect_nonneg (fun _ _ => disagreement_nonnegative _ _)

theorem relativeDistance_comm {X : Type*} [Fintype X] (f g : X → Bool) :
    relativeDistance f g = relativeDistance g f := by
  simp only [relativeDistance, disagreement_comm]

theorem relativeDistance_triangle {X : Type*} [Fintype X] (f g h : X → Bool) :
    relativeDistance f h ≤ relativeDistance f g + relativeDistance g h := by
  rw [relativeDistance, relativeDistance, relativeDistance,
    ← Finset.expect_add_distrib]
  exact Finset.expect_le_expect (fun _ _ => disagreement_triangle _ _ _)

end MinUncutGames.Foundations.PCP.CodeComposition

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_AlphabetGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.PCP.AlphabetGraph

open MinUncutGames.Foundations.Hastad
open scoped BigOperators

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem expect_prod {I J : Type*} [Fintype I] [Fintype J] (f : I × J → ℝ) :
    (𝔼 z : I × J, f z) = 𝔼 i : I, 𝔼 j : J, f (i, j) := by
  simpa only [Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset I) (Finset.univ : Finset J) f

end MinUncutGames.Foundations.PCP.AlphabetGraph

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RuntimeModel2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.CompareLoop

open _root_.Turing
open MinUncutGames.Foundations.Complexity

variable {q : Nat} {Λ : Type}

def comparisonTime (tailName headName : Nat) : Nat :=
  2 * (tailName + 2) + 2 * (headName + 2) + max (tailName + 1) (headName + 1) + 2

theorem comparisonTime_le_of_lt (tailName headName N : Nat)
    (hTail : tailName < N) (hHead : headName < N) :
    comparisonTime tailName headName ≤ 5 * N + 6 := by
  have hm : max (tailName + 1) (headName + 1) ≤ N := max_le (by omega) (by omega)
  unfold comparisonTime
  omega

end MinUncutGames.Foundations.PCP.AlphabetTable.CompareLoop

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Addresses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.AlphabetTable.Addresses

open MinUncutGames.Foundations.Hastad

def values (n m edge tail head : Nat) : Fin 5 → Nat := ![n, m, edge, tail, head]

end MinUncutGames.Foundations.PCP.AlphabetTable.Addresses

namespace MinUncutGames.Foundations.PCP.AlphabetTable.EmitRows

open _root_.Turing
open MinUncutGames.Foundations.Complexity

theorem vector_list_ofFn {α : Type} {n : Nat} (vector : Vector α n) :
    List.ofFn (fun index : Fin n => vector[index]) = vector.toList := by
  have equality := congrArg Vector.toList (Vector.ofFn_getElem (xs := vector))
  simpa only [Vector.toList_ofFn, Fin.getElem_fin] using equality

theorem flatMap_length_le {α β : Type} (items : List α) (f : α → List β)
    (bound : Nat) (bounded : ∀ item ∈ items, (f item).length ≤ bound) :
    (items.flatMap f).length ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item items ih =>
    have hh := bounded item (by simp)
    have ht := ih (fun x hx => bounded x (by simp [hx]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

end MinUncutGames.Foundations.PCP.AlphabetTable.EmitRows

namespace MinUncutGames.Foundations.PCP.AlphabetTable.Cleanup

open _root_.Turing
open Complexity
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

def clearTapes : {n : Nat} → (Fin n → K) → (K → List Bool) → K → List Bool
  | 0, _, base => base
  | n + 1, selected, base =>
      clearTapes (fun i : Fin n => selected i.succ) (Function.update base (selected 0) [])

def actualCost : {n : Nat} → (Fin n → K) → (K → List Bool) → Nat
  | 0, _, _ => 1
  | n + 1, selected, base =>
      actualCost (fun i : Fin n => selected i.succ) (Function.update base (selected 0) []) +
        ((base (selected 0)).length + 1)

theorem clearTapes_apply {n : Nat} (selected : Fin n → K) (base : K → List Bool) (k : K) :
    clearTapes selected base k = if ∃ i, selected i = k then [] else base k := by
  induction n generalizing base with
  | zero => simp [clearTapes]
  | succ n ih =>
      rw [clearTapes, ih]
      by_cases first : selected 0 = k
      · subst k
        simp [Function.update]
      · have notFirst : k ≠ selected 0 := Ne.symm first
        by_cases later : ∃ i : Fin n, selected i.succ = k <;>
          simp [Fin.exists_fin_succ, first, later, Function.update, notFirst]

theorem actualCost_le {n : Nat} (selected : Fin n → K) (base : K → List Bool) :
    actualCost selected base ≤ (∑ i, (base (selected i)).length) + n + 1 := by
  induction n generalizing base with
  | zero => simp [actualCost]
  | succ n ih =>
      have tailBound := ih (fun i : Fin n => selected i.succ)
        (Function.update base (selected 0) [])
      have sumBound :
          (∑ i : Fin n, ((Function.update base (selected 0) []) (selected i.succ)).length) ≤
            ∑ i : Fin n, (base (selected i.succ)).length := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : selected i.succ = selected 0 <;> simp [h]
      rw [actualCost, Fin.sum_univ_succ]
      omega

end MinUncutGames.Foundations.PCP.AlphabetTable.Cleanup

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Driver
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.AlphabetTable.Initialization

open _root_.Turing
open MinUncutGames.Foundations.Complexity

variable {q : Nat}

def time (N : Nat) : Nat := (6 * N + 11) + (7 * (3 * (N + 1) + 3) + 1)

end MinUncutGames.Foundations.PCP.AlphabetTable.Initialization

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineFiniteAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineUnaryEqualityBit

open _root_.Turing

variable {K Λ A : Type} [DecidableEq K]

def copySteps (n : Nat) : Nat := 2 * (n + 1) + 1
def compareSteps (a b : Nat) : Nat := max (a + 1) (b + 1) + 1
def steps (a b : Nat) : Nat := copySteps a + copySteps b + compareSteps a b + 1

theorem steps_le (a b : Nat) : steps a b ≤ 3 * (a + b) + 9 := by
  unfold steps copySteps compareSteps
  omega

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.Complexity.MachineUnaryEqualityBit

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingPaddingOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingPaddingOffsets

open scoped BigOperators

theorem sigma_length {A : Type*} (sizes : A → Nat) (xs : List A) :
    (xs.sigma (fun x => List.finRange (sizes x))).length = (xs.map sizes).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.sigma_cons, ih]

end MinUncutGames.Foundations.PCP.PreprocessingPaddingOffsets

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCloudPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineCloudPrefix

open _root_.Turing
open MinUncutGames.Foundations.PCP
open scoped BigOperators

variable {σ : Type}

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

end MinUncutGames.Foundations.Complexity.MachineCloudPrefix

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PoweringMachineRow

open _root_.Turing
open MinUncutGames.Foundations.PCP

def encodeBit (b : Bool) : List Bool := if b then [true, false] else [false]

def encodeBits : List Bool → List Bool
  | [] => []
  | b :: bits => encodeBit b ++ encodeBits bits

@[simp] theorem encodeBits_append (xs ys : List Bool) :
    encodeBits (xs ++ ys) = encodeBits xs ++ encodeBits ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [encodeBits, ih, List.append_assoc]

end MinUncutGames.Foundations.Complexity.PoweringMachineRow

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineCloudRank

open _root_.Turing

variable {σ : Type}

theorem idxOf_filter_prefix {α : Type*} [BEq α] [LawfulBEq α]
    (p : α → Bool) (a : α) (hp : p a = true) :
    ∀ xs : List α, a ∈ xs →
      (xs.filter p).idxOf a = ((xs.take (xs.idxOf a)).filter p).length := by
  classical
  intro xs
  induction xs with
  | nil => intro ha; simp at ha
  | cons b xs ih =>
      intro ha
      by_cases hba : b = a
      · subst b
        simp [hp]
      · have ha' : a ∈ xs := by simpa [hba, Ne.symm hba] using ha
        cases hb : p b <;>
          simp [hba, hb, ih ha']

open MinUncutGames.Foundations.PCP

end MinUncutGames.Foundations.Complexity.MachineCloudRank

end
section
namespace MinUncutGames.Foundations.Complexity.MachineRegularOriginalRow

open _root_.Turing
open PCP

section Execution

variable {Λ σ : Type}

theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end Execution

end MinUncutGames.Foundations.Complexity.MachineRegularOriginalRow

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularMetadata

open _root_.Turing
open MinUncutGames.Foundations.PCP


variable {σ : Type}

theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

def overhead (N x v : Nat) : Nat :=
  (2*x + 5*N + 6) + 2 + (N+1) + 2*(x+2) + 2*(v+2) + 1 +
    (5*N + 3*(v+x+2) + 6) + (v+x+3) + (N+1) + 2 + (v+2) + 2

theorem overhead_le (N x v : Nat) (hx : x ≤ N) (hv : v ≤ N) :
    overhead N x v ≤ 40*(N+1) := by
  unfold overhead
  omega

end MinUncutGames.Foundations.Complexity.MachineRegularMetadata

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_SelectorMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularInternalRow
open _root_.Turing
open PCP
variable {K Λ σ : Type} [DecidableEq K]

def coreTimeBound (q graphLength rotorLength x v i k o m outputLength : Nat) : Nat :=
  (5 * q + 32) * rotorLength + 10 * graphLength + 2 * i + 13 * v + 5 * k +
    (5 * q + 10) * (m + o) + 4 * x + 2 * outputLength + 8 * q + 41066

end MinUncutGames.Foundations.Complexity.MachineRegularInternalRow

end
section
namespace MinUncutGames.Foundations.Complexity.MachineRegularOriginalClean

open _root_.Turing PCP

theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

def timeBound (q inputLength outputLength : Nat) : Nat :=
  (5 * q + 20) * inputLength + 2 * outputLength + 5 * q + 40995

end MinUncutGames.Foundations.Complexity.MachineRegularOriginalClean

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineDummyRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachinePaddingRows

open _root_.Turing

inductive Control
  | initialize_ | guard | bump
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.initialize_, .guard, .bump]

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance instFintypeControl : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 6 ⊕ Unit
abbrev State := (Unit × Option Bool) × Unit

end MinUncutGames.Foundations.Complexity.MachinePaddingRows

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularVertexBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularVertexBlock

open _root_.Turing PCP MachineRegularInternalRow

variable {σ Λ : Type}

def rowSizeBound (q vertices : Nat) : Nat := vertices + vertices * (q + 1) + 8192

def portTimeBound (q graphLength rotorLength x v i k o m outputLength vertices : Nat) : Nat :=
  q * coreTimeBound q graphLength rotorLength x v i k o m
    (outputLength + q * rowSizeBound q vertices)

def originalTimeBound (q graphLength rotorLength x v i k o m outputLength vertices : Nat) : Nat :=
  portTimeBound q graphLength rotorLength x v i k o m outputLength vertices +
    MachineRegularOriginalClean.timeBound q graphLength
      (outputLength + q * rowSizeBound q vertices)

end MinUncutGames.Foundations.Complexity.MachineRegularVertexBlock

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularOriginalBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineRegularOriginalBody

open _root_.Turing PCP

theorem joinTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.Complexity.MachineRegularOriginalBody

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingRegularLoopWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingRegularLoopWords

def blocksSuffix {n : Nat} (f : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn f).drop k).flatten

@[simp] theorem blocksSuffix_zero {n : Nat} (f : Fin n → List Bool) :
    blocksSuffix f 0 = (List.ofFn f).flatten := by
  simp only [blocksSuffix, List.drop_zero]

@[simp] theorem blocksSuffix_all {n : Nat} (f : Fin n → List Bool) :
    blocksSuffix f n = [] := by
  have h : (List.ofFn f).drop n = [] := by
    simpa only [List.length_ofFn] using (List.drop_length (l := List.ofFn f))
  exact congrArg List.flatten h

end MinUncutGames.Foundations.PCP.PreprocessingRegularLoopWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Basic2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularTable

open _root_.Turing
open MinUncutGames.Foundations.PCP


namespace Header

variable {σ : Type}

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

end Header

end MinUncutGames.Foundations.Complexity.MachineRegularTable
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachinePortReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachinePortReindex

open _root_.Turing

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive Label (d : Nat)
  | copySeed | copyScan | copyRestore | initialize_ | divide
  | emit (r : Fin d)
  | affineScan | affineRestore | drainQuotient | finish
  deriving DecidableEq, Fintype

def steps (d j : Nat) : Nat := 3 * j + 3 * (j / d) + 11

def value (d c b j : Nat) : Nat := c * (j / d) + (j % d) + b

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem lazy_value (d j : Nat) : value d (2 * d) d j =
    2 * d * (j / d) + d + (j % d) := by
  unfold value
  omega

end MinUncutGames.Foundations.Complexity.MachinePortReindex

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingLazyWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingLazyWords

open MinUncutGames.Foundations.Complexity

variable {n d : Nat}

def reverseMap (d j : Nat) : Nat := 2 * d * (j / d) + d + j % d

end MinUncutGames.Foundations.PCP.PreprocessingLazyWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineLazyRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineLazyRows

open _root_.Turing
open PCP.PreprocessingLazyWords (reverseMap )

variable {K Λ A : Type} [DecidableEq K]

def addressIndex : Fin 5 → Fin 9 := ![1, 3, 4, 5, 6]

theorem addressIndex_injective : Function.Injective addressIndex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [addressIndex]

def fields (tape : Fin 9 → K) : Fin 3 → K := ![tape 0, tape 6, tape 2]

def bodyIndex (i : Fin 9) : Fin 10 := i.castSucc

theorem bodyIndex_injective : Function.Injective bodyIndex := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 10 => k.val) h

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def valueBound (c b m : Nat) : Nat := c * m + m + b
def rowSizeBound (c b n m : Nat) : Nat := n + valueBound c b m + 8194
def rowCostBound (c b n m : Nat) : Nat :=
  2 * n + 8 * m + valueBound c b m + 4 * rowSizeBound c b n m + 8224

end MinUncutGames.Foundations.Complexity.MachineLazyRows

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingOverlayWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingOverlayWords

open Complexity

variable {n d e : Nat}

def oldReverseMap (d e j : Nat) : Nat := (d + e) * (j / d) + j % d
def expanderReverseMap (d e j : Nat) : Nat := (d + e) * (j / e) + d + j % e

end MinUncutGames.Foundations.PCP.PreprocessingOverlayWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineOverlayRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineOverlayRows

open _root_.Turing
open PCP.PreprocessingOverlayWords

variable {K Λ A : Type} [DecidableEq K]
variable {e : Nat}

def bodyIndex (i : Fin 9) : Fin 10 := i.castSucc

theorem bodyIndex_injective : Function.Injective bodyIndex := by
  intro i j h
  exact Fin.castSucc_injective 9 h

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def valueBound (d e B : Nat) : Nat := (d + e) * B + B + d

theorem value_le (d e j B : Nat) (hj : j ≤ B) :
    MachinePortReindex.value e (d + e) d j ≤ valueBound d e B := by
  have hdiv := (Nat.div_le_self j e).trans hj
  have hmod := (Nat.mod_le j e).trans hj
  have hmul := Nat.mul_le_mul_left (d + e) hdiv
  unfold MachinePortReindex.value valueBound
  omega

end MinUncutGames.Foundations.Complexity.MachineOverlayRows

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_InputData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularTable
open _root_.Turing
open MinUncutGames.Foundations.PCP
namespace Top

theorem joinTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end Top

end MinUncutGames.Foundations.Complexity.MachineRegularTable

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularTableTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineRegularTable.Top

open _root_.Turing
open MinUncutGames.Foundations.PCP

theorem joinCompleteTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

theorem normalizeEmptyAppend {A : Type*} (output : List Bool → A)
    (bits : List Bool) : output ([] ++ bits) = output bits :=
  congrArg output (List.nil_append bits)

end MinUncutGames.Foundations.Complexity.MachineRegularTable.Top

namespace MinUncutGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

open _root_.Turing PCP
open MachineRegularOriginalBody

theorem originalTimeBound_le (q L R x v i k o m O V W R' : Nat)
    (hL : L ≤ W) (hR : R ≤ R') (hx : x ≤ W) (hv : v ≤ W)
    (hi : i ≤ W) (hk : k ≤ W) (ho : o ≤ W) (hm : m ≤ W)
    (hO : O ≤ W) (hV : V ≤ W) :
    MachineRegularVertexBlock.originalTimeBound q L R x v i k o m O V ≤
      MachineRegularVertexBlock.originalTimeBound q W R' W W W W W W W W := by
  unfold MachineRegularVertexBlock.originalTimeBound MachineRegularVertexBlock.portTimeBound
    MachineRegularInternalRow.coreTimeBound MachineRegularOriginalClean.timeBound
    MachineRegularVertexBlock.rowSizeBound
  gcongr

end MinUncutGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularTableRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineTableSplit

open _root_.Turing


abbrev State (σ : Type) := σ × Option Bool

inductive Label
  | copyFirst | copySecond | startVertices | readVertices | startDarts | readDarts
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyFirst, .copySecond, .startVertices,
  .readVertices, .startDarts, .readDarts]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 6

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 4 * length + 6 := by simp [timePolynomial]

end MinUncutGames.Foundations.Complexity.MachineTableSplit

end
section
namespace MinUncutGames.Foundations.Complexity.MachinePaddingBounds

def rowBound (d v e count : Nat) : Nat := v + count + e + (count + 1) * d + 8194

theorem rowBound_next (d v e count : Nat) :
    rowBound d (v + 1) (e + d) count = rowBound d v e (count + 1) := by
  simp only [rowBound, Nat.add_mul, Nat.one_mul]
  omega

theorem blockRow_le_rowBound (d v e count : Nat) :
    v + e + d + 8194 ≤ rowBound d v e (count + 1) := by
  simp only [rowBound, Nat.add_mul, Nat.one_mul]
  omega

def rowCap (d size : Nat) : Nat := size + (size + 1) * d + 8194

noncomputable def rowPolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.X + (Polynomial.X + 1) * Polynomial.C d + Polynomial.C 8194

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.X * (Polynomial.C d *
    (Polynomial.C 4 * rowPolynomial d +
      Polynomial.C 2 * (Polynomial.X + Polynomial.X * Polynomial.C d * rowPolynomial d) +
      Polynomial.C 10) + Polynomial.C 2) + 1

end MinUncutGames.Foundations.Complexity.MachinePaddingBounds

end
section
namespace MinUncutGames.Foundations.Complexity.MachinePaddingCertificate

open MachinePaddingRows

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  MachinePaddingBounds.timePolynomial d + 1

end MinUncutGames.Foundations.Complexity.MachinePaddingCertificate

end
section
namespace MinUncutGames.Foundations.Complexity.MachineVertexPadding

open _root_.Turing
open MinUncutGames.Foundations.PCP
open MachineCloudPadding


inductive Tape
  | original | output | vertex | edge | power | level | fuel | relation
  | scratch | work | saved | product | rowWork | rowSpare
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.original, .output, .vertex, .edge, .power, .level,
  .fuel, .relation, .scratch, .work, .saved, .product, .rowWork, .rowSpare]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def memory (input output vertex edge power level fuel relation : List Bool) : Tape → List Bool
  | .original => input
  | .output => output
  | .vertex => vertex
  | .edge => edge
  | .power => power
  | .level => level
  | .fuel => fuel
  | .relation => relation
  | _ => []

@[simp] theorem update_output (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .output x = memory a x c d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_vertex (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .vertex x = memory a b x d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_edge (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .edge x = memory a b c x e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_power (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .power x = memory a b c d x f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_fuel (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .fuel x = memory a b c d e f x h := by
  funext k; cases k <;> rfl
@[simp] theorem update_relation (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .relation x = memory a b c d e f g x := by
  funext k; cases k <;> rfl

def rowTape : MachinePaddingRows.Tape → Tape
  | .inl k => (![.vertex, .edge, .relation, .rowWork, .output, .rowSpare] : Fin 6 → Tape) k
  | .inr _ => .fuel
def rowView : Tape → Option MachinePaddingRows.Tape
  | .vertex => some (.inl 0)
  | .edge => some (.inl 1)
  | .relation => some (.inl 2)
  | .rowWork => some (.inl 3)
  | .output => some (.inl 4)
  | .rowSpare => some (.inl 5)
  | .fuel => some (.inr ())
  | _ => none

theorem rowView_left (k : MachinePaddingRows.Tape) : rowView (rowTape k) = some k := by
  rcases k with k | k
  · fin_cases k <;> rfl
  · cases k; rfl
theorem rowView_right (j : Tape) (k : MachinePaddingRows.Tape)
    (h : rowView j = some k) : rowTape k = j := by
  rcases k with k | k
  · cases j <;> fin_cases k <;> simp_all [rowView, rowTape]
  · cases k; cases j <;> simp_all [rowView, rowTape]

def rowStateEquiv (σ : Type) : (MachinePaddingRows.State × (σ × Bool)) ≃ State σ where
  toFun x := (x.2, x.1.1.2)
  invFun x := ((((), x.2), ()), x.1)
  left_inv := by rintro ⟨⟨⟨⟨⟩, r⟩, ⟨⟩⟩, a⟩; rfl
  right_inv := by rintro ⟨a, r⟩; rfl

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

def cleanupTime (d m : Nat) : Nat := 2 * m + m * d + 8201

end MinUncutGames.Foundations.Complexity.MachineVertexPadding

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineOverlayTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineOverlayTable

open _root_.Turing
open PCP PCP.PreprocessingOverlayWords
open MachineCloudPadding


variable {A : Type} {d e : Nat}

abbrev Tape := Fin 5 ⊕ Fin 12

def graphArchive : Tape := .inl 0
def graphStream : Tape := .inl 1
def scratch : Tape := .inl 2
def vertexCount : Tape := .inl 3
def dartCount : Tape := .inl 4
def expanderArchive : Tape := .inr 0
def expanderStream : Tape := .inr 1
def fuel : Tape := .inr 2
def vertex : Tape := .inr 3
def tail : Tape := .inr 4
def oldReverse : Tape := .inr 5
def relation : Tape := .inr 6
def dividedCopy : Tape := .inr 7
def quotient : Tape := .inr 8
def newReverse : Tape := .inr 9
def rowBuffer : Tape := .inr 10
def output : Tape := .inr 11

def oldTapes : Fin 10 → Tape :=
  ![tail, oldReverse, relation, scratch, dividedCopy, quotient, newReverse,
    output, rowBuffer, graphStream]

def expanderTapes : Fin 10 → Tape :=
  ![tail, oldReverse, relation, scratch, dividedCopy, quotient, newReverse,
    output, rowBuffer, expanderStream]

theorem oldTapes_injective : Function.Injective oldTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [oldTapes, tail, oldReverse, relation, scratch, dividedCopy, quotient,
      newReverse, output, rowBuffer, graphStream]

theorem expanderTapes_injective : Function.Injective expanderTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [expanderTapes, tail, oldReverse, relation, scratch, dividedCopy, quotient,
      newReverse, output, rowBuffer, expanderStream]

def extraTapes (rawH : List Bool) : Fin 12 → List Bool :=
  fun i => if i = 0 then rawH else []

def splitView : Tape → Option (Fin 5)
  | .inl i => some i
  | .inr _ => none

def combine (left : Fin 5 → List Bool) (rawH : List Bool) : Tape → List Bool
  | .inl i => left i
  | .inr i => extraTapes rawH i

def memory (g h gs hs n m f v t out : List Bool) : Tape → List Bool
  | .inl i => ![g, gs, [], n, m] i
  | .inr i => ![h, hs, f, v, t, [], [], [], [], [], [], out] i

@[simp] theorem memory_graphArchive (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out graphArchive = g := rfl
@[simp] theorem memory_graphStream (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out graphStream = gs := rfl
@[simp] theorem memory_scratch (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out scratch = [] := rfl
@[simp] theorem memory_vertexCount (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out vertexCount = n := rfl
@[simp] theorem memory_dartCount (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out dartCount = m := rfl
@[simp] theorem memory_expanderArchive (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out expanderArchive = h := rfl
@[simp] theorem memory_expanderStream (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out expanderStream = hs := rfl
@[simp] theorem memory_fuel (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out fuel = f := rfl
@[simp] theorem memory_vertex (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out vertex = v := rfl
@[simp] theorem memory_tail (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out tail = t := rfl
@[simp] theorem memory_oldReverse (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out oldReverse = [] := rfl
@[simp] theorem memory_relation (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out relation = [] := rfl
@[simp] theorem memory_dividedCopy (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out dividedCopy = [] := rfl
@[simp] theorem memory_quotient (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out quotient = [] := rfl
@[simp] theorem memory_newReverse (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out newReverse = [] := rfl
@[simp] theorem memory_rowBuffer (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out rowBuffer = [] := rfl
@[simp] theorem memory_output (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out output = out := rfl

@[simp] theorem update_output (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) output x = memory g h gs hs n m f v t x := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_expanderStream (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) expanderStream x =
      memory g h gs x n m f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_graphStream (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) graphStream x =
      memory g h x hs n m f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_fuel (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) fuel x = memory g h gs hs n m x v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_vertex (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) vertex x = memory g h gs hs n m f x t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_tail (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) tail x = memory g h gs hs n m f v x out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_vertexCount (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) vertexCount x = memory g h gs hs x m f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_dartCount (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) dartCount x = memory g h gs hs n x f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def preparationSteps (n : Nat) (h : List Bool) : Nat := 2 * (h.length + 1) + 6 * (n + 1) + 4

def remaining {n : Nat} (block : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn block).drop k).flatten
def emittedPrefix {n : Nat} (block : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn block).take k).flatten

theorem remaining_step {n : Nat} (block : Fin n → List Bool) (v : Fin n) :
    remaining block v.val = block v ++ remaining block (v.val + 1) := by
  have hs := List.getElem_cons_drop (as := List.ofFn block) (i := v.val)
    (by simpa only [List.length_ofFn] using v.isLt)
  unfold remaining
  rw [← hs]
  simp only [List.flatten_cons, List.getElem_ofFn, Fin.eta]

theorem prefix_step {n : Nat} (block : Fin n → List Bool) (v : Fin n) :
    emittedPrefix block (v.val + 1) = emittedPrefix block v.val ++ block v := by
  unfold emittedPrefix
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using v.isLt)]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.getElem_ofFn, Fin.eta]

@[simp] theorem remaining_zero {n : Nat} (block : Fin n → List Bool) :
    remaining block 0 = (List.ofFn block).flatten := by simp [remaining]
@[simp] theorem remaining_end {n : Nat} (block : Fin n → List Bool) :
    remaining block n = [] := by
  unfold remaining
  rw [List.drop_eq_nil_iff.mpr (by simpa only [List.length_ofFn] using (Nat.le_refl n)), List.flatten_nil]
@[simp] theorem prefix_zero {n : Nat} (block : Fin n → List Bool) : emittedPrefix block 0 = [] := by
  simp [emittedPrefix]
@[simp] theorem prefix_end {n : Nat} (block : Fin n → List Bool) :
    emittedPrefix block n = (List.ofFn block).flatten := by
  unfold emittedPrefix
  have ht : (List.ofFn block).take n = List.ofFn block :=
    List.take_of_length_le (by simpa only [List.length_ofFn] using (Nat.le_refl n))
  rw [ht]

def cleanupSteps (n m : Nat) : Nat := 2 * n + m + 8

theorem flatMap_length_le {α : Type*} (items : List α) (f : α → List Bool)
    (B : Nat) (bounded : ∀ x ∈ items, (f x).length ≤ B) :
    (items.flatMap f).length ≤ items.length * B := by
  induction items with
  | nil => simp
  | cons x xs ih =>
      have hx := bounded x (by simp)
      have ht := ih (fun y hy => bounded y (by simp [hy]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem flatten_length_le (items : List (List Bool)) (B : Nat)
    (bounded : ∀ x ∈ items, x.length ≤ B) : items.flatten.length ≤ items.length * B := by
  simpa only [List.flatMap_id] using flatMap_length_le items id B bounded

def oldSize (d e n : Nat) : Nat := MachineLazyRows.rowSizeBound (d + e) 0 n (n * d)

end MinUncutGames.Foundations.Complexity.MachineOverlayTable

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineLazyTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineLazyTable

open _root_.Turing PCP


inductive Tape
  | input | output | source | vertices | darts | fuel | vertex | reverse
  | tail | old | relation | scratch | divided | quotient | newReverse | rowBuffer
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .output, .source, .vertices, .darts, .fuel,
  .vertex, .reverse, .tail, .old, .relation, .scratch, .divided, .quotient, .newReverse,
  .rowBuffer]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

def splitRoles : Fin 5 → Tape := ![.input, .source, .scratch, .vertices, .darts]
def splitView : Tape → Option (Fin 5)
  | .input => some 0 | .source => some 1 | .scratch => some 2
  | .vertices => some 3 | .darts => some 4 | _ => none

def dummyRoles : Fin 6 → Tape := ![.tail, .reverse, .relation, .rowBuffer, .output, .scratch]
def dummyView : Tape → Option (Fin 6)
  | .tail => some 0 | .reverse => some 1 | .relation => some 2
  | .rowBuffer => some 3 | .output => some 4 | .scratch => some 5 | _ => none

def oldRoles : Fin 10 → Tape :=
  ![.tail, .old, .relation, .scratch, .divided, .quotient, .newReverse,
    .output, .rowBuffer, .source]

theorem splitRoles_left (i : Fin 5) : splitView (splitRoles i) = some i := by
  fin_cases i <;> rfl

theorem splitRoles_right (t : Tape) (i : Fin 5) (h : splitView t = some i) : splitRoles i = t := by
  cases t <;> fin_cases i <;> simp_all [splitView, splitRoles]

theorem dummyRoles_left (i : Fin 6) : dummyView (dummyRoles i) = some i := by
  fin_cases i <;> rfl

theorem dummyRoles_right (t : Tape) (i : Fin 6) (h : dummyView t = some i) : dummyRoles i = t := by
  cases t <;> fin_cases i <;> simp_all [dummyView, dummyRoles]

theorem oldRoles_injective : Function.Injective oldRoles := by decide

def frame (input source output vertices darts fuel vertex reverse : List Bool) : Tape → List Bool
  | .input => input | .source => source | .output => output
  | .vertices => vertices | .darts => darts | .fuel => fuel
  | .vertex => vertex | .reverse => reverse | _ => []

def initialTapes (input : List Bool) : Tape → List Bool := frame input [] [] [] [] [] [] []

def finalTapes (input output : List Bool) : Tape → List Bool := frame input [] output [] [] [] [] []

theorem joinTrace {X : Type} {f : X → X} {a b c : X} {s t : Nat}
    (first : f^[s] a = b) (second : f^[t] b = c) : f^[s + t] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem frame_old_empty (input source output vertices darts fuel vertex reverse : List Bool)
    (i : Fin 10) (h7 : i ≠ 7) (h9 : i ≠ 9) :
    frame input source output vertices darts fuel vertex reverse (oldRoles i) = [] := by
  fin_cases i <;> simp_all [frame, oldRoles]

def finishSteps (d n m v : Nat) : Nat := n + m + v + 2 * d * v + 11

def remaining (n r : Nat) : List (Fin n) := (List.finRange n).drop r

@[simp] theorem remaining_zero (n : Nat) : remaining n 0 = List.finRange n := by simp [remaining]
@[simp] theorem remaining_done (n : Nat) : remaining n n = [] := by simp [remaining]

theorem remaining_cons (n r : Nat) (h : r < n) :
    remaining n r = ⟨r, h⟩ :: remaining n (r + 1) := by
  unfold remaining
  rw [List.drop_eq_getElem_cons (l := List.finRange n) (i := r) (by simpa using h)]
  simp

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (1000000 * (d + 1) ^ 3 + 100) * (Polynomial.X + 1) ^ 3

@[simp] theorem timePolynomial_eval (d L : Nat) :
    (timePolynomial d).eval L = (1000000 * (d + 1) ^ 3 + 100) * (L + 1) ^ 3 := by
  simp [timePolynomial]

@[simp] theorem finalTapes_input (input output : List Bool) : finalTapes input output .input = input := rfl
@[simp] theorem finalTapes_output (input output : List Bool) : finalTapes input output .output = output := rfl

end MinUncutGames.Foundations.Complexity.MachineLazyTable

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineLazyTableRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineLazyTableRuntime

open _root_.Turing PCP
open MachineLazyTable (Tape )


def cleanupTapes : List Tape :=
  [.input, .source, .vertices, .darts, .fuel, .vertex, .reverse,
    .tail, .old, .relation, .scratch, .divided, .quotient, .newReverse, .rowBuffer]

end MinUncutGames.Foundations.Complexity.MachineLazyTableRuntime

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_RawInitialTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.AmplificationIteration

theorem min_double_min (u cap : ℝ) (hc : 0 ≤ cap) :
    min (2 * min u cap) cap = min (2 * u) cap := by
  by_cases hu : u ≤ cap
  · rw [min_eq_left hu]
  · have hcu : cap ≤ u := le_of_not_ge hu
    rw [min_eq_right hcu, min_eq_right (by linarith : cap ≤ 2 * cap),
      min_eq_right (by linarith : cap ≤ 2 * u)]

end MinUncutGames.Foundations.PCP.AmplificationIteration

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_GraphTableComplexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringMomentBound

open scoped BigOperators
open SpectralReturn PoweringReturn
open PoweringMoment (bit hits)

theorem symmetric_gap_matrix_sum (ε : ℝ) (r : Nat → ℝ) :
    ∀ (m : Nat) (f : Fin m → Fin m → ℝ),
      (∀ i j, f i j = f j i) → (∀ i, f i i = ε) →
      (∀ i j, i.val < j.val → f i j = r (j.val - i.val - 1)) →
      (∑ i, ∑ j, f i j) = (m : ℝ) * ε +
        2 * ∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, r gap := by
  intro m
  induction m with
  | zero => intro f _hSym _hDiag _hUpper; simp
  | succ m ih =>
    intro f hSym hDiag hUpper
    have hOld : (∑ i : Fin m, ∑ j : Fin m, f i.castSucc j.castSucc) =
        (m : ℝ) * ε + 2 * ∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, r gap := by
      apply ih (fun i j => f i.castSucc j.castSucc)
      · intro i j; exact hSym i.castSucc j.castSucc
      · intro i; exact hDiag i.castSucc
      · intro i j hij; exact hUpper i.castSucc j.castSucc hij
    have hLast : (∑ i : Fin m, f i.castSucc (Fin.last m)) =
        ∑ gap ∈ Finset.range m, r gap := by
      calc
        _ = ∑ i : Fin m, r (m - 1 - i.val) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hUpper i.castSucc (Fin.last m) i.isLt]
          simp only [Fin.val_last, Fin.val_castSucc]
          congr 1
          omega
        _ = ∑ i ∈ Finset.range m, r (m - 1 - i) :=
          Fin.sum_univ_eq_sum_range (fun i => r (m - 1 - i)) m
        _ = _ := Finset.sum_range_reflect r m
    have hLastRow : (∑ j : Fin m, f (Fin.last m) j.castSucc) =
        ∑ gap ∈ Finset.range m, r gap := by
      calc
        _ = ∑ j : Fin m, f j.castSucc (Fin.last m) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hSym (Fin.last m) j.castSucc
        _ = _ := hLast
    calc
      (∑ i, ∑ j, f i j) =
          (∑ i : Fin m, ∑ j : Fin m, f i.castSucc j.castSucc) +
            (∑ i : Fin m, f i.castSucc (Fin.last m)) +
            (∑ j : Fin m, f (Fin.last m) j.castSucc) + f (Fin.last m) (Fin.last m) := by
        simp only [Fin.sum_univ_castSucc, Finset.sum_add_distrib]
        ring
      _ = (m : ℝ) * ε +
          2 * (∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, r gap) +
          (∑ gap ∈ Finset.range m, r gap) + (∑ gap ∈ Finset.range m, r gap) + ε := by
        rw [hOld, hLast, hLastRow, hDiag]
      _ = ((m + 1 : Nat) : ℝ) * ε +
          2 * ∑ j ∈ Finset.range (m + 1), ∑ gap ∈ Finset.range j, r gap := by
        rw [Finset.sum_range_succ]
        simp only [Nat.cast_add, Nat.cast_one]
        ring

def windowIndex (n start m : Nat) (h : start + m ≤ n + 1) (i : Fin m) : Fin (n + 1) :=
  ⟨start + i.val, (Nat.add_lt_add_left i.isLt start).trans_le h⟩

end MinUncutGames.Foundations.PCP.PoweringMomentBound

end
section
namespace MinUncutGames.Foundations.PCP.PoweringNumeric

theorem min_density_ratio (ε C k t : ℝ)
    (hε : 0 < ε) (hC : 0 < C) (hk : 0 ≤ k)
    (ht : 0 < t) (hkt : k ≤ t) :
    min ε (1 / t) / (C + 1) ≤ ε / (C + k * ε) := by
  have hx : 0 ≤ min ε (1 / t) :=
    le_min hε.le (one_div_nonneg.mpr ht.le)
  have hxt : min ε (1 / t) * t ≤ 1 :=
    (le_div_iff₀ ht).mp (min_le_right ε (1 / t))
  have hkx : k * min ε (1 / t) ≤ 1 := by
    calc
      k * min ε (1 / t) ≤ t * min ε (1 / t) :=
        mul_le_mul_of_nonneg_right hkt hx
      _ ≤ 1 := by simpa only [mul_comm] using hxt
  have hC1 : 0 < C + 1 := by positivity
  have hden : 0 < C + k * ε :=
    add_pos_of_pos_of_nonneg hC (mul_nonneg hk hε.le)
  apply (div_le_div_iff₀ hC1 hden).2
  calc
    min ε (1 / t) * (C + k * ε) =
        C * min ε (1 / t) + ε * (k * min ε (1 / t)) := by ring
    _ ≤ C * ε + ε * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (min_le_left ε (1 / t)) hC.le)
        (mul_le_mul_of_nonneg_left hkx hε.le)
    _ = ε * (C + 1) := by ring

theorem count_moment_ratio_lower (α ε C t : ℝ) (m : ℕ)
    (hm : 0 < m) (hε : 0 < ε) (hC : 0 < C) (ht : 0 < t)
    (hmt : (m : ℝ) - 1 ≤ t) :
    (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / t) ≤
      (α ^ 2 * (m : ℝ) * ε) ^ 2 /
        ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hk : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr hm1
  have hden : 0 < C + ((m : ℝ) - 1) * ε :=
    add_pos_of_pos_of_nonneg hC (mul_nonneg hk hε.le)
  have hαm : 0 ≤ α ^ 4 * (m : ℝ) := by positivity
  have hratio := min_density_ratio ε C ((m : ℝ) - 1) t hε hC hk ht hmt
  calc
    (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / t) =
        (α ^ 4 * (m : ℝ)) * (min ε (1 / t) / (C + 1)) := by ring
    _ ≤ (α ^ 4 * (m : ℝ)) * (ε / (C + ((m : ℝ) - 1) * ε)) :=
      mul_le_mul_of_nonneg_left hratio hαm
    _ = (α ^ 2 * (m : ℝ) * ε) ^ 2 /
        ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε)) := by
      field_simp [ne_of_gt hm0, ne_of_gt hε, ne_of_gt hden]

end MinUncutGames.Foundations.PCP.PoweringNumeric

end
section
noncomputable section

namespace MinUncutGames.Foundations.PCP.PoweringSoundness

open scoped BigOperators
open SpectralReturn PoweringMomentBound
open PoweringMoment (bit hits)

variable {V D A : Type*}

def center (q M : Nat) : Nat := (4 * q * M) ^ 2

theorem le_center (q M : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M) : M ≤ center q M := by
  have hfour : 1 ≤ 4 * q := by omega
  have hx : M ≤ 4 * q * M := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right M hfour
  have hone : 1 ≤ 4 * q * M := hM.trans hx
  have hsquare : 4 * q * M ≤ (4 * q * M) * (4 * q * M) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 * q * M) hone
  exact hx.trans (by simpa only [center, pow_two] using hsquare)

def gain (q M : Nat) (lambda : ℝ) : ℝ :=
  (1 / (2 * (q : ℝ))) ^ 4 * ((2 * M + 1 : Nat) : ℝ) /
    ((1 + 2 / (1 - lambda)) + 1)

end MinUncutGames.Foundations.PCP.PoweringSoundness

end
end
section
namespace MinUncutGames.Foundations.PCP.PoweringGap

open SpectralReturn PoweringSoundness

variable {V D A : Type*}

theorem gain_nonneg (q M : Nat) (lambda : ℝ) (hlambda : lambda < 1) :
    0 ≤ gain q M lambda := by
  have hden : 0 < 1 - lambda := sub_pos.mpr hlambda
  unfold gain
  positivity

end MinUncutGames.Foundations.PCP.PoweringGap

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringFinalConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringFinalConstants

abbrev Alphabet := Fin 6 → Bool

@[simp] theorem card_alphabet : Fintype.card Alphabet = 64 := by
  norm_num [Alphabet, Fintype.card_fun]

theorem spectral_denominator_eq :
    (1 + 2 / (1 - (31 / 32 : ℝ))) + 1 = 66 := by
  norm_num

end MinUncutGames.Foundations.PCP.PoweringFinalConstants

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_TableIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncutGames.Foundations.PCP.PoweringPortReindex
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

def wordEquiv (ports : D ≃ E) (n : Nat) : (Fin n → D) ≃ (Fin n → E) where
  toFun p := fun i => ports (p i)
  invFun p := fun i => ports.symm (p i)
  left_inv p := by funext i; exact ports.symm_apply_apply (p i)
  right_inv p := by funext i; exact ports.apply_symm_apply (p i)

end MinUncutGames.Foundations.PCP.PoweringPortReindex

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PortTableLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PortTableLookup

theorem flatMap_word {α β : Type*} (f : α → List β)
    (width j : Nat) (hj : j < width) :
    ∀ (rows : List α), (∀ a ∈ rows, (f a).length = width) →
      ∀ (i : Nat) (row : α), rows[i]? = some row →
        (rows.flatMap f)[width * i + j]? = (f row)[j]? := by
  intro rows
  induction rows with
  | nil =>
      intro _ i row selected
      simp at selected
  | cons a rows ih =>
      intro hwidth i row selected
      have ha : (f a).length = width := hwidth a (by simp)
      cases i with
      | zero =>
          have heq : a = row := by simpa using selected
          subst row
          simp only [Nat.mul_zero, Nat.zero_add, List.flatMap_cons]
          exact List.getElem?_append_left (by omega)
      | succ i =>
          have selected' : rows[i]? = some row := by simpa using selected
          have hskip : (f a).length ≤ width * (i + 1) + j := by
            rw [ha, Nat.mul_add, Nat.mul_one]
            omega
          have hoff : width * (i + 1) + j - (f a).length = width * i + j := by
            rw [ha, Nat.mul_add, Nat.mul_one]
            omega
          rw [List.flatMap_cons, List.getElem?_append_right hskip, hoff]
          exact ih (fun b hb => hwidth b (by simp [hb])) i row selected'

end MinUncutGames.Foundations.PCP.PortTableLookup

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineRotor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineRotor

open _root_.Turing
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

def reverseAddress (vertex : Fin n) (port : Fin d) : Nat :=
  (4098 * d) * vertex.val + (4098 * port.val + 3)

end MinUncutGames.Foundations.Complexity.PoweringMachineRotor

namespace MinUncutGames.Foundations.Complexity.PoweringMachineInitialize

open _root_.Turing

def castTapes {K : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (tapes : ∀ k, List (Γ k)) : ∀ k, List (Δ k) := h ▸ tapes

def castConfiguration {K Λ σ : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Δ Λ σ := h ▸ c

theorem castTapes_apply {K : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (tapes : ∀ k, List (Γ k)) (k : K) :
    castTapes h tapes k = cast (congrArg (fun alphabet => List (alphabet k)) h) (tapes k) := by
  cases h
  rfl

theorem castConfiguration_mk {K Λ σ : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (label : Option Λ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    castConfiguration h ⟨label, state, tapes⟩ = ⟨label, state, castTapes h tapes⟩ := by
  cases h
  rfl

end MinUncutGames.Foundations.Complexity.PoweringMachineInitialize

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineRelation

open _root_.Turing
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

def address (vertex : Fin n) (port : Fin d) (position : Fin 4096) : Nat :=
  (4098 * d) * vertex.val + (4098 * port.val + 4 + position.val)

end MinUncutGames.Foundations.Complexity.PoweringMachineRelation

namespace MinUncutGames.Foundations.Complexity.PoweringMachineEqualityField

open _root_.Turing
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {max l r n d : Nat}

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {u v : Nat}
    (first : f^[u] a = b) (second : f^[v] b = c) : f^[u + v] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.Complexity.PoweringMachineEqualityField

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_PoweringPlanBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PoweringPlanBudget

open _root_.Turing PCP

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}


def fieldBudget (max inputLength : Nat) : Nat :=
  (28 * max + 10) * inputLength + 24 * max + 15

end MinUncutGames.Foundations.Complexity.PoweringPlanBudget

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringTableLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringTableLayout

open MinUncutGames.Foundations.Complexity

theorem vector_toList_ofFn {α : Type*} {m : Nat} (rows : Vector α m) :
    rows.toList = List.ofFn (fun i : Fin m => rows[i]) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp

theorem vector_blocks {α : Type*} {m vertices width : Nat}
    (sameCount : m = vertices * width) (rows : Vector α m) :
    rows.toList = (List.finRange vertices).flatMap (fun v =>
      List.ofFn (fun j : Fin width =>
        rows[Fin.cast sameCount.symm (finProdFinEquiv (v, j))])) := by
  have atIndex (v : Fin vertices) (j : Fin width)
      (h : v.val * width + j.val < vertices * width) :
      (⟨v.val * width + j.val, h⟩ : Fin (vertices * width)) =
        finProdFinEquiv (v, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  rw [vector_toList_ofFn rows,
    List.ofFn_congr sameCount (fun i : Fin m => rows[i]), List.ofFn_mul]
  simp only [atIndex, List.finRange, List.flatMap_def, List.map_ofFn]
  rfl

end MinUncutGames.Foundations.PCP.PoweringTableLayout

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineFinish

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

def copySteps (n m : Nat) : Nat := (2 * (m + 1) + 1) + (2 * (n + 1) + 1)

theorem copySteps_eq (n m : Nat) : copySteps n m = 2 * (n + m) + 6 := by
  unfold copySteps
  omega

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MinUncutGames.Foundations.Complexity.PoweringMachineFinish

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_PoweringInitializeFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringGlobalConfiguration

open _root_.Turing

@[simp] theorem boolList_mpr_eq (h : List Bool = List Bool) (bits : List Bool) :
    h.mpr bits = bits := rfl

end MinUncutGames.Foundations.Complexity.PoweringGlobalConfiguration

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Bridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.SourceBridge
attribute [local instance] Classical.propDecidable

lemma sum_list_count {A : Type*} (xs : List A) (f : A → Bool) :
    (∑ i : Fin xs.length, if f xs[i] then (1:ℝ) else 0)=(xs.countP f:ℝ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons] at *
    rw [Fin.sum_univ_succ]
    change (if f x then (1:ℝ) else 0)+(∑ i : Fin xs.length, if f xs[i] then (1:ℝ) else 0)=_
    rw [ih,List.countP_cons]
    cases f x <;> simp [add_comm]

end MinUncut.SourceBridge

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ExpressionEffectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Syntax
open Turing.ToPartrec

def bin (op a b : Code) : Code := .comp op (.cons a (.cons b .nil))
def branch (e a b : Code) : Code := .comp (.case a (.comp b .tail)) (.cons e .id)
end MinUncut.Preprocess.Syntax

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
open scoped BigOperators
variable {P X : Type} [Primcodable P] [Primcodable X] [AddCommMonoid X]

lemma c_rangeSum {f : P → ℕ → X} (hf : Computable₂ f)
    (hadd : Computable₂ (fun x y : X=>x+y)) :
    Computable₂ (fun p n=>((List.range n).map (f p)).sum) := by
  have hh := Computable.nat_rec (α:=P × ℕ) (σ:=X) Computable.snd
    (Computable.const 0)
    (hadd.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))).to₂
  exact hh.of_eq (by
    intro p
    induction p.2 with
    | zero => rfl
    | succ n ih => simp only [List.range_succ,List.map_append,List.map_singleton,List.sum_append,
        List.sum_singleton,ih])

end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_UniformFind
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
namespace UEncoding
variable {P : Type} [Primcodable P] {A B Γ : P → Type}

def optionEquiv (X : Type) : Option X ≃ X ⊕ Unit where
  toFun x := match x with | some a => .inl a | none => .inr ()
  invFun x := match x with | .inl a => some a | .inr _ => none
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x with | inl a => rfl | inr a => cases a; rfl

end UEncoding
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Preprocess.Source
open MinUncutGames.Foundations
open PCP Hastad
open UEncoding

abbrev Par := ℕ × ℕ
end MinUncut.Preprocess.Source

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_UniformAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Alphabet
open UEncoding
open scoped BigOperators
variable {P : Type} [Primcodable P]
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
def slotGood (p : P) (x : Fin (t p) × Fin 3) : Bool := !h p x.1 || decide (x.2=0)
end MinUncut.Preprocess.Alphabet

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
open scoped BigOperators
variable {P X : Type} [Primcodable P] [Primcodable X] [CommMonoid X]
lemma c_rangeProd {f : P → ℕ → X} (hf : Computable₂ f)
    (hmul : Computable₂ (fun x y : X=>x*y)) :
    Computable₂ (fun p n=>((List.range n).map (f p)).prod) := by
  have hh := Computable.nat_rec (α:=P × ℕ) (σ:=X) Computable.snd
    (Computable.const 1)
    (hmul.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))).to₂
  exact hh.of_eq (by
    intro p
    induction p.2 with
    | zero => rfl
    | succ n ih => simp only [List.range_succ,List.map_append,List.map_singleton,List.prod_append,
        List.prod_singleton,ih])

end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_LocalBodyEffectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess
open UEncoding
lemma c_replicate {X : Type} [Primcodable X] : Computable₂ (fun n (x : X)=>List.replicate n x) := by
  have hf : Computable₂ (fun (x : X) (_ : ℕ)=>x) := Computable.fst
  have hh : Computable (fun p : ℕ × X=>(List.range p.1).map (fun _=>p.2)) :=
    (c_rangeMap hf).comp Computable.snd Computable.fst
  change Computable (fun p : ℕ × X=>List.replicate p.1 p.2)
  simpa using hh
end MinUncut.Preprocess

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_UniformFiniteSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess

variable {α β : Type} [Primcodable α] [Primcodable β]

noncomputable def searchWith (e : Encodable β) {p : α → β → Prop} [DecidableRel p]
    (h : ∀a,∃b,p a b) (a : α) : β := @Encodable.choose β (p a) e _ (h a)

end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_ArithmeticTactic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

set_option maxHeartbeats 1000000
section
namespace MinUncut.Preprocess

def gridTail (n : ℕ) : ℕ := n.unpair.2
def gridField (n : ℕ) : ℕ := (n.unpair.1-1).unpair.2

@[fun_prop] lemma c_gridTail : Computable gridTail := Computable.snd.comp Computable.unpair
end MinUncut.Preprocess

end

end OAI
end


