-- Prove2me | Definitions.Def_OAIQ035K006
-- name    : OAIQ035K006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:53:31.64156+00:00
-- url     : https://prove2.me/theorems/134f0e52-e9dc-4bf4-98e9-a23c720a0eae
-- title:
--   Definitions bundle OAIQ035K006 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 87 declarations of OpenAI's Lean: 45 definitions, 6 inductive types or structures, 1 instance and 35 theorems. The definitions and types are `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.Raw`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.dummy`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.Input`, `OAI.MetricKMedian.FixedBatch.RationalParameters.candidateGood`, `OAI.MetricKMedian.MarginalRounding.fractional`, `OAI.MetricKMedian.MaskProgram.pullback`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.QRow`, `OAI.MetricKMedian.RationalBatchData.ProposalProgram.Input`, `OAI.MetricKMedian.RationalGrid.At`, `OAI.MetricKMedian.RationalSignedStep.Active`, `OAI.MetricKMedian.RationalSignedStep.endpoint`, `OAI.MetricKMedian.RationalSignedStep.pair`, `OAI.MetricKMedian.RationalSignedStep.pairs`, `OAI.MetricKMedian.RationalSignedStep.probability`, `OAI.MetricKMedian.RationalWeightedStep.down`, `OAI.MetricKMedian.RationalWeightedStep.endpoint`, `OAI.MetricKMedian.RationalWeightedStep.fractional`, `OAI.MetricKMedian.RationalWeightedStep.move`, `OAI.MetricKMedian.RationalWeightedStep.pair`, `OAI.MetricKMedian.RationalWeightedStep.point`, `OAI.MetricKMedian.RationalWeightedStep.probability`, `OAI.MetricKMedian.RationalWeightedStep.realPoint`, `OAI.MetricKMedian.RationalWeightedStep.up`, `OAI.MetricKMedian.RoundingProgram.Input`, `OAI.MetricKMedian.RoundingProgram.coordinateBound`, `OAI.MetricKMedian.SparseBernoulli.Program.Input`, `OAI.MetricKMedian.SparseCardinalRounding.Program.Input`, `OAI.MetricKMedian.SparseCardinalRounding.selected`, `OAI.MetricKMedian.SparseEnumeratedGraph.lift`, `OAI.MetricKMedian.SparseGraph.Graph`, `OAI.MetricKMedian.SparseGraph.Program.QInput`, `OAI.MetricKMedian.SparseGraph.Program.QInput.raw`, `OAI.MetricKMedian.SparseGraph.edge`, `OAI.MetricKMedian.SparseGraph.edgeCode`, `OAI.MetricKMedian.SparseGraph.features`, `OAI.MetricKMedian.SparseGraph.next`, `OAI.MetricKMedian.SparsePhysicalBatch.balanced`, `OAI.MetricKMedian.SparsePhysicalBatch.unbalanced`, `OAI.MetricKMedian.SparseWeightedPartial.features`, `OAI.MetricKMedian.Taper.breakpoints` and 11 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Compression_AffineElimination`, `KMedian_Geometry_BoundFreeCompression`, `KMedian_Optimization_GradientDenominator`, `KMedian_Preparation_PreparedScanProgram`, `KMedian_Preparation_RationalPreparedScan`, `KMedian_Preparation_SupplierListOperations`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Process_BatchProposalProgram`, `KMedian_Process_RoundCountsProgram`, `KMedian_Process_RoundingRunProgram`, `KMedian_Process_TaperGraphProgram`, `KMedian_Process_TaperReindex`, `KMedian_Programs_CardinalRoundProgram`, `KMedian_Programs_GraphLawProgram`, `KMedian_Programs_OriginalMaskProgram`, `KMedian_Rounding_MarginalRounding`, `KMedian_Rounding_RationalSignedStep`, `KMedian_Rounding_RationalTaperAffine`, `KMedian_Rounding_RationalTaperData`, `KMedian_Rounding_RationalTaperZero`, `KMedian_Rounding_RationalWeightedStep`, `KMedian_Rounding_WeightedGridInvariant`, `KMedian_Rounding_WeightedRounding`, `KMedian_Sparse_SparseCardinalRounding`, `KMedian_Sparse_SparseEnumeratedGraph`, `KMedian_Sparse_SparseGraphFeatures`, `KMedian_Sparse_SparsePhysicalBatch`, `KMedian_Sparse_SparseWeightedPartial`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K018`, `OAIQ035K019`, `OAIQ035K020`, `OAIQ035K021`, `OAIQ035K022`, `OAIQ035K024`, `OAIQ035K025`, `OAIQ035K026`, `OAIQ035K044`, `OAIQ035K058` and `OAIQ035K062`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_AffineElimination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
open Finset

namespace IntegerLaw
variable {Ω I : Type} [Fintype Ω] [Fintype I]

theorem positive_entry {z : Ω → ℤ} (hsum : ∑ i, z i=0) (hz : ∃ i, z i ≠ 0) :
    ∃ i, 0 < z i := by
  by_contra hn
  push Not at hn
  have he : ∀ i, z i=0 := by
    intro i
    have hsingle : z i ≤ 0 := hn i
    have hsum' : (∑ j, -z j)=0 := by rw [sum_neg_distrib,hsum,neg_zero]
    have hm : -z i ≤ 0 := by
      rw [← hsum']
      exact single_le_sum (fun j _ => neg_nonneg.mpr (hn j)) (mem_univ i)
    omega
  obtain ⟨i,hi⟩ := hz
  exact hi (he i)

end IntegerLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_BoundFreeCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

theorem exists_feature_bound {n d : ℕ} (v : Fin n → Fin d → ℤ) :
    ∃ L : ℕ, ∀ i j, |v i j| ≤ (2:ℤ)^L := by
  let L := ∑ i, ∑ j, (v i j).natAbs
  refine ⟨L,?_⟩
  intro i j
  have h1 : (v i j).natAbs ≤ ∑ j, (v i j).natAbs :=
    single_le_sum (f:=fun (j : Fin d) => (v i j).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ j)
  have h2 : (∑ j, (v i j).natAbs) ≤ L :=
    single_le_sum (f:=fun (i : Fin n) => ∑ j, (v i j).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)
  have hn : (v i j).natAbs ≤ L := h1.trans h2
  have hh := hn.trans (Nat.lt_two_pow_self (n:=L)).le
  have hh' : ((v i j).natAbs:ℤ) ≤ (2:ℤ)^L := by exact_mod_cast hh
  simpa only [Int.natCast_natAbs] using hh'

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_GradientDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalGrid
open Finset

def At (D : ℤ) (q : ℚ) : Prop := ∃ a : ℤ, q=(a:ℚ)/(D:ℚ)

theorem zero (D : ℤ) : At D 0 := ⟨0,by simp⟩

theorem integer (D a : ℤ) (hD : D ≠ 0) : At D (a:ℚ) := by
  refine ⟨a*D,?_⟩
  rw [Int.cast_mul,mul_div_cancel_right₀ _ (by exact_mod_cast hD)]

theorem sub {D : ℤ} {a b : ℚ} (ha : At D a) (hb : At D b) : At D (a-b) := by
  obtain ⟨A,rfl⟩ := ha
  obtain ⟨B,rfl⟩ := hb
  exact ⟨A-B,by rw [Int.cast_sub,sub_div]⟩

end MetricKMedian.RationalGrid

end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_MarginalRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.MarginalRounding

variable {I : Type*} [Fintype I]

noncomputable def fractional (p : I → ℝ) : Finset I :=
  Finset.univ.filter (fun i => 0 < p i ∧ p i < 1)

@[simp] theorem mem_fractional (p : I → ℝ) (i : I) :
    i ∈ fractional p ↔ 0 < p i ∧ p i < 1 := by simp [fractional]

end MetricKMedian.MarginalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparsePhysicalBatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparsePhysicalBatch
open Finset
variable {n : ℕ}

def balanced (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n)) (ω : Fin n → Bool) : Finset (Fin n) :=
  (univ.filter (fun e => ω e=true ∧ ∀ f∈C e, ω f=false)) ∩ Z

def unbalanced (Z : Finset (Fin n)) (ω : Fin n → Bool) : Finset (Fin n) :=
  univ.filter (fun e => ω e=true ∧ e∉Z)

end MetricKMedian.SparsePhysicalBatch

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalTaperAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset

variable {I : Type*} [Fintype I]

def upper (d : I → ℚ) : ℚ := 1+∑ i, (d i)⁻¹

def breakpoints (P : ℚ) (d : I → ℚ) : Finset ℚ :=
  insert 0 (insert (upper d) ((univ.image (fun i => (1-P)/d i)) ∪ (univ.image (fun i => 1/d i))))

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalTaperZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I] [LinearOrder I]

def extend (own Z : Finset I) (Δ : ℕ) : Finset I :=
  own ∪ (((Z \ own).sort (· ≤ ·)).take (Δ-own.card)).toFinset

def zeroSources (d : I → ℚ) : Finset I := univ.filter (fun i => d i=0)

def zeroSelection (d : I → ℚ) (own : Finset I) (Δ : ℕ) : Finset I :=
  extend own (zeroSources d) Δ

def zeroMarginal (d : I → ℚ) (own : Finset I) (Δ : ℕ) (i : I) : ℚ :=
  if i ∈ zeroSelection d own Δ then 1 else 0

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalTaperData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I] [LinearOrder I]

def rationalColocatedMass (g : ℚ) (d : I → ℚ) : ℚ :=
  ∑ i, if d i=0 then g else 0

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_WeightedRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.WeightedRounding

variable {I : Type*} [Fintype I] [DecidableEq I]
open MarginalRounding

noncomputable def sign (i j : I) (r : ℝ) (k : I) : ℝ :=
  (if k=i then 1 else 0)-(if k=j then r else 0)
noncomputable def move (p : I → ℝ) (i j : I) (r t : ℝ) : I → ℝ :=
  fun k => p k+t*sign i j r k
noncomputable def up (p : I → ℝ) (i j : I) (r : ℝ) := min (1-p i) (p j/r)
noncomputable def down (p : I → ℝ) (i j : I) (r : ℝ) := min (p i) ((1-p j)/r)

end MetricKMedian.WeightedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalWeightedStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalWeightedStep
open Finset
variable {n : ℕ}

abbrev point (p : Vector ℚ n) (i : Fin n) : ℚ := p[i.val]
def realPoint (p : Vector ℚ n) (i : Fin n) : ℝ := (point p i:ℝ)
def fractional (p : Vector ℚ n) : Finset (Fin n) :=
  univ.filter (fun i => 0 < point p i ∧ point p i < 1)

def pair (p : Vector ℚ n) (h : 1 < (fractional p).card) :
    {a : Fin n × Fin n // a.1 ∈ fractional p ∧ a.2 ∈ fractional p ∧ a.1 ≠ a.2} :=
  let F := fractional p
  have hFc : 1 < F.card := h
  have hF : F.Nonempty := card_pos.mp (by omega)
  let i := F.min' hF
  have hi : i ∈ F := min'_mem _ _
  have hE : (F.erase i).Nonempty := by
    rw [← card_pos,card_erase_of_mem hi]
    omega
  let j := (F.erase i).min' hE
  have hj : j ∈ F.erase i := min'_mem _ _
  ⟨(i,j),hi,(mem_erase.mp hj).2,(mem_erase.mp hj).1.symm⟩

def move (p : Vector ℚ n) (i j : Fin n) (r t : ℚ) : Vector ℚ n :=
  Vector.ofFn (fun k => point p k+t*((if k=i then 1 else 0)-(if k=j then r else 0)))

def up (p : Vector ℚ n) (i j : Fin n) (r : ℚ) : ℚ := min (1-point p i) (point p j/r)
def down (p : Vector ℚ n) (i j : Fin n) (r : ℚ) : ℚ := min (point p i) ((1-point p j)/r)

@[simp] theorem real_move (p : Vector ℚ n) (i j : Fin n) (r t : ℚ) :
    realPoint (move p i j r t)=WeightedRounding.move (realPoint p) i j (r:ℝ) (t:ℝ) := by
  funext k
  simp only [realPoint,point,move,Vector.getElem_ofFn,Fin.eta,WeightedRounding.move,
    WeightedRounding.sign,Rat.cast_add,Rat.cast_mul,Rat.cast_sub]
  split_ifs <;> simp only [Rat.cast_one,Rat.cast_zero]

@[simp] theorem real_up (p : Vector ℚ n) (i j : Fin n) (r : ℚ) :
    (up p i j r:ℝ)=WeightedRounding.up (realPoint p) i j (r:ℝ) := by
  simp only [up,WeightedRounding.up,realPoint,Rat.cast_min,Rat.cast_sub,Rat.cast_one,Rat.cast_div]

@[simp] theorem real_down (p : Vector ℚ n) (i j : Fin n) (r : ℚ) :
    (down p i j r:ℝ)=WeightedRounding.down (realPoint p) i j (r:ℝ) := by
  simp only [down,WeightedRounding.down,realPoint,Rat.cast_min,Rat.cast_sub,Rat.cast_one,Rat.cast_div]

@[simp] theorem real_fractional (p : Vector ℚ n) :
    MarginalRounding.fractional (realPoint p)=fractional p := by
  ext i
  simp only [fractional,mem_filter,mem_univ,true_and,MarginalRounding.mem_fractional,
    realPoint]
  constructor <;> rintro ⟨h0,h1⟩ <;> exact ⟨by exact_mod_cast h0,by exact_mod_cast h1⟩

theorem up_pos (p : Vector ℚ n) (i j : Fin n) (r : ℚ) (hr : 0 < r)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) : 0 < up p i j r := by
  exact lt_min (sub_pos.mpr (mem_filter.mp hi).2.2)
    (div_pos (mem_filter.mp hj).2.1 hr)

theorem down_pos (p : Vector ℚ n) (i j : Fin n) (r : ℚ) (hr : 0 < r)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) : 0 < down p i j r := by
  exact lt_min (mem_filter.mp hi).2.1
    (div_pos (sub_pos.mpr (mem_filter.mp hj).2.2) hr)

def probability (β : Fin n → ℚ) (p : Vector ℚ n) : ℚ :=
  if h : 1 < (fractional p).card then
    let a := pair p h
    let r := β a.val.1/β a.val.2
    down p a.val.1 a.val.2 r/(up p a.val.1 a.val.2 r+down p a.val.1 a.val.2 r)
  else 0

def endpoint (β : Fin n → ℚ) (p : Vector ℚ n) (b : Fin 2) : Vector ℚ n :=
  if h : 1 < (fractional p).card then
    let a := pair p h
    let r := β a.val.1/β a.val.2
    move p a.val.1 a.val.2 r (if b=0 then up p a.val.1 a.val.2 r else -down p a.val.1 a.val.2 r)
  else p

theorem probability_unit (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i) (p : Vector ℚ n) :
    0 ≤ probability β p ∧ probability β p ≤ 1 := by
  unfold probability
  split_ifs with h
  · let a := pair p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := div_pos (hβ _) (hβ _)
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    exact ⟨(div_pos hd (add_pos hu hd)).le,(div_le_one (add_pos hu hd)).mpr (by linarith)⟩
  · exact ⟨le_rfl,by norm_num⟩

end MetricKMedian.RationalWeightedStep
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseWeightedPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedPartial
open Finset RationalWeightedStep
variable {n : ℕ}

def features (p : Vector ℚ n) (a : Fin (n+n*n)) : ℚ :=
  Sum.elim (point p) (fun ij : Fin (n*n) =>
    point p (finProdFinEquiv.symm ij).1*point p (finProdFinEquiv.symm ij).2)
    (finSumFinEquiv.symm a)

@[simp] theorem features_single (p : Vector ℚ n) (i : Fin n) :
    features p (finSumFinEquiv (Sum.inl i))=point p i := by
  simp only [features,Equiv.symm_apply_apply,Sum.elim_inl]

@[simp] theorem features_pair (p : Vector ℚ n) (i j : Fin n) :
    features p (finSumFinEquiv (Sum.inr (finProdFinEquiv (i,j))))=point p i*point p j := by
  simp only [features,Equiv.symm_apply_apply,Sum.elim_inr]

end MetricKMedian.SparseWeightedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCardinalRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCardinalRounding
open Finset RationalWeightedStep
variable {n : ℕ}

def selected (q : Vector ℚ n) : Finset (Fin n) := univ.filter (fun i => point q i=1)

end MetricKMedian.SparseCardinalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGraphFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

abbrev Graph (n m : ℕ) := Fin m → Finset (Fin n)

def edge (G : Graph n m) (h : Fin n) (i : Fin m) : ℚ := if h ∈ G i then 1 else 0

def edgeCode (G : Graph n m) (a : Fin (n*m)) : ℚ :=
  edge G (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2

def features (G : Graph n m) (a : Fin (n*m+(n*m)*(n*m))) : ℚ :=
  Sum.elim (edgeCode G) (fun ij : Fin ((n*m)*(n*m)) =>
    edgeCode G (finProdFinEquiv.symm ij).1*edgeCode G (finProdFinEquiv.symm ij).2)
    (finSumFinEquiv.symm a)

@[simp] theorem features_single (G : Graph n m) (h : Fin n) (i : Fin m) :
    features G (finSumFinEquiv (Sum.inl (finProdFinEquiv (h,i))))=edge G h i := by
  simp only [features,edgeCode,Equiv.symm_apply_apply,Sum.elim_inl]

@[simp] theorem features_pair (G : Graph n m) (h k : Fin n) (i j : Fin m) :
    features G (finSumFinEquiv (Sum.inr (finProdFinEquiv
      (finProdFinEquiv (h,i),finProdFinEquiv (k,j)))))=edge G h i*edge G k j := by
  simp only [features,edgeCode,Equiv.symm_apply_apply,Sum.elim_inr]

def next (G : Graph n m) (S : Finset (Fin n)) (i : Fin m) : Graph n m :=
  Function.update G i S

@[simp] theorem edge_next (G : Graph n m) (S : Finset (Fin n)) (h : Fin n) (i j : Fin m) :
    edge (next G S i) h j=if j=i then (if h∈S then 1 else 0) else edge G h j := by
  by_cases hji : j=i <;> simp [edge,next,hji]

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseEnumeratedGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedGraph
open Finset
variable {I : Type} [DecidableEq I] {n : ℕ}

def lift (enum : Fin n ≃ I) (G : SparseGraph.Graph n n) : I → Finset I :=
  fun i => (G (enum.symm i)).map enum.toEmbedding

omit [DecidableEq I] in
@[simp] theorem mem_lift (enum : Fin n ≃ I) (G : SparseGraph.Graph n n) (h i : I) :
    h∈lift enum G i ↔ enum.symm h∈G (enum.symm i) := by
  simp only [lift,mem_map,Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨a,ha,he⟩
    simpa only [← he,Equiv.symm_apply_apply] using ha
  · intro ha
    exact ⟨enum.symm h,ha,enum.apply_symm_apply h⟩

end MetricKMedian.SparseEnumeratedGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RationalPreparedScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset
variable {τ : ℝ}
variable {F H X : Type} [LinearOrder F] [Fintype F] [DecidableEq H]
  [PseudoMetricSpace X] {j : ℕ}

def candidateGood (B : ℚ) (O : Finset H) : Bool := decide (O.Nonempty ∧ (O.card:ℚ) ≤ B)

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalSignedStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalSignedStep
open Finset RationalWeightedStep
variable {n : ℕ}

def pairs (u : Fin n → ℚ) (p : Vector ℚ n) : Finset (Fin (n*n)) :=
  univ.filter (fun z => let a := finProdFinEquiv.symm z;
    a.1∈fractional p ∧ a.2∈fractional p ∧ a.1≠a.2 ∧ 0<u a.1*u a.2)

def Active (u : Fin n → ℚ) (p : Vector ℚ n) : Prop := (pairs u p).Nonempty
instance instDecidableActive (u : Fin n → ℚ) (p : Vector ℚ n) : Decidable (Active u p) :=
  inferInstanceAs (Decidable (pairs u p).Nonempty)

def pair (u : Fin n → ℚ) (p : Vector ℚ n) (h : Active u p) :
    {a : Fin n × Fin n // a.1∈fractional p ∧ a.2∈fractional p ∧
      a.1≠a.2 ∧ 0<u a.1*u a.2} :=
  ⟨finProdFinEquiv.symm ((pairs u p).min' h), by
    have hh := min'_mem (pairs u p) h
    exact (mem_filter.mp hh).2⟩

theorem pair_ratio_pos (u : Fin n → ℚ) (p : Vector ℚ n) (h : Active u p) :
    0<u (pair u p h).val.1/u (pair u p h).val.2 := by
  rcases mul_pos_iff.mp (pair u p h).property.2.2.2 with h | h
  · exact div_pos h.1 h.2
  · exact div_pos_of_neg_of_neg h.1 h.2

theorem pair_right_ne (u : Fin n → ℚ) (p : Vector ℚ n) (h : Active u p) :
    u (pair u p h).val.2≠0 := by
  intro hz
  have hh := (pair u p h).property.2.2.2
  rw [hz,mul_zero] at hh
  exact lt_irrefl _ hh

def probability (β : Fin n → ℚ) (p : Vector ℚ n) : ℚ :=
  if h : Active β p then
    let a := pair β p h
    let r := β a.val.1/β a.val.2
    down p a.val.1 a.val.2 r/(up p a.val.1 a.val.2 r+down p a.val.1 a.val.2 r)
  else 0

def endpoint (β : Fin n → ℚ) (p : Vector ℚ n) (b : Fin 2) : Vector ℚ n :=
  if h : Active β p then
    let a := pair β p h
    let r := β a.val.1/β a.val.2
    move p a.val.1 a.val.2 r (if b=0 then up p a.val.1 a.val.2 r else -down p a.val.1 a.val.2 r)
  else p

theorem probability_unit (β : Fin n → ℚ) (p : Vector ℚ n) :
    0 ≤ probability β p ∧ probability β p ≤ 1 := by
  unfold probability
  split_ifs with h
  · let a := pair β p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := pair_ratio_pos β p h
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    exact ⟨(div_pos hd (add_pos hu hd)).le,(div_le_one (add_pos hu hd)).mpr (by linarith)⟩
  · exact ⟨le_rfl,by norm_num⟩

end MetricKMedian.RationalSignedStep
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBernoulli.Program
open Function

structure Input where
  n : ℕ
  p : Fin n → ℚ
  feasible : ∀ i, 0 ≤ p i ∧ p i ≤ 1

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_WeightedGridInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RationalGrid

theorem add {D : ℤ} {a b : ℚ} (ha : At D a) (hb : At D b) : At D (a+b) := by
  obtain ⟨A,rfl⟩ := ha
  obtain ⟨B,rfl⟩ := hb
  exact ⟨A+B,by rw [Int.cast_add,add_div]⟩

end MetricKMedian.RationalGrid

namespace MetricKMedian.RationalWeightedStep
open Finset RationalGrid
variable {n : ℕ}

theorem point_move_self (p : Vector ℚ n) (i j : Fin n) (hij : i≠j) (r t : ℚ) :
    point (move p i j r t) i=point p i+t := by
  simp [point,move,hij]
theorem point_move_other (p : Vector ℚ n) (i j : Fin n) (hij : i≠j) (r t : ℚ) :
    point (move p i j r t) j=point p j-t*r := by
  simp [point,move,Ne.symm hij,sub_eq_add_neg]
theorem point_move_rest (p : Vector ℚ n) (i j k : Fin n) (hki : k≠i) (hkj : k≠j) (r t : ℚ) :
    point (move p i j r t) k=point p k := by
  simp [point,move,hki,hkj]

theorem move_pair_weighted (β : Fin n → ℚ) (p : Vector ℚ n) (i j : Fin n)
    (hij : i≠j) (hj : β j ≠ 0) (t : ℚ) :
    β i*point (move p i j (β i/β j) t) i+
      β j*point (move p i j (β i/β j) t) j=β i*point p i+β j*point p j := by
  rw [point_move_self _ _ _ hij,point_move_other _ _ _ hij]
  field_simp
  ring

theorem down_integral (p : Vector ℚ n) (i j : Fin n) (hij : i≠j) (r : ℚ) (hr : r≠0) :
    point (move p i j r (-down p i j r)) i=0 ∨ point (move p i j r (-down p i j r)) j=1 := by
  rw [point_move_self _ _ _ hij,point_move_other _ _ _ hij]
  unfold down
  rcases le_total (point p i) ((1-point p j)/r) with h | h
  · left; rw [min_eq_left h]; ring
  · right; rw [min_eq_right h,neg_mul,div_mul_cancel₀ _ hr]; ring

end MetricKMedian.RationalWeightedStep
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Function Polynomial

structure Input (signed : Bool) where
  n : ℕ
  β : Fin n → ℚ
  p : Vector ℚ n
  positive : signed=false → ∀ i, 0<β i
  feasible : ∀ i, 0 ≤ RationalWeightedStep.point p i ∧ RationalWeightedStep.point p i ≤ 1

def coordinateBound (L : ℕ) := 2*L*L+L

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_CardinalRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseCardinalRounding.Program
open Function
abbrev Input := SparseBernoulli.Program.Input
end MetricKMedian.SparseCardinalRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_GraphLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Function

structure QInput where
  n : ℕ
  m : ℕ
  q : Fin n → Fin m → ℚ
  feasible : ∀ h i, 0≤q h i ∧ q h i≤1

def QInput.raw (x : QInput) : List Unit × List (List ℚ) :=
  (List.replicate x.n (),List.ofFn fun i => List.ofFn fun h => x.q h i)
end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_TaperGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.TaperGraphProgram

structure Input where
  n : ℕ
  d : Fin n → Fin n → ℚ
  own : Fin n → Finset (Fin n)
  g : ℚ
  P : ℚ
  Δ : ℕ
  positive : 0<P

end MetricKMedian.TaperGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_TaperReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section
namespace MetricKMedian.Taper
open Finset
variable {I J : Type} [Fintype I] [Fintype J]

 theorem image_univ_reindex [DecidableEq ℚ] (e : I ≃ J) (f : J → ℚ) :
    univ.image (fun i => f (e i))=univ.image f := by
  ext q
  simp only [mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩; exact ⟨e i,rfl⟩
  · rintro ⟨j,rfl⟩; exact ⟨e.symm j,by rw [e.apply_symm_apply]⟩
 theorem upper_reindex (e : I ≃ J) (d : J → ℚ) : upper (fun i => d (e i))=upper d := by
  exact congrArg (fun q : ℚ => 1+q) (e.sum_comp (fun j => (d j)⁻¹))
 theorem breaks_reindex (e : I ≃ J) (P : ℚ) (d : J → ℚ) :
    breakpoints P (fun i => d (e i))=breakpoints P d := by
  unfold breakpoints
  rw [upper_reindex,image_univ_reindex e (fun j => (1-P)/d j),image_univ_reindex e (fun j => 1/d j)]
 theorem colocated_reindex (e : I ≃ J) (g : ℚ) (d : J → ℚ) :
    rationalColocatedMass g (fun i => d (e i))=rationalColocatedMass g d :=
  e.sum_comp (fun j => if d j=0 then g else 0)

variable [LinearOrder I] [LinearOrder J]
omit [LinearOrder I] [LinearOrder J] in
 theorem zeros_reindex (e : I ≃ J) (d : J → ℚ) :
    (zeroSources (fun i => d (e i))).map e.toEmbedding=zeroSources d := by
  ext j
  simp only [mem_map_equiv,zeroSources,mem_filter,mem_univ,true_and,e.apply_symm_apply]
omit [Fintype I] [Fintype J] in
 theorem extend_reindex (e : I ≃o J) (own Z : Finset I) (Δ : ℕ) :
    extend (own.map e.toEquiv.toEmbedding) (Z.map e.toEquiv.toEmbedding) Δ=
      (extend own Z Δ).map e.toEquiv.toEmbedding := by
  have hs : ((Z\own).map e.toEquiv.toEmbedding).sort=
      ((Z\own).sort).map e := by
    exact (Finset.map_sort e.toEquiv.toEmbedding (Z\own) (·≤·) (·≤·)
      (fun _ _ _ _ => e.le_iff_le.symm)).symm
  have hm (xs : List I) : (xs.map e).toFinset=xs.toFinset.map e.toEquiv.toEmbedding := by
    ext j; simp only [List.mem_toFinset,List.mem_map,mem_map,Equiv.toEmbedding_apply]
    rfl
  simp only [extend,← Finset.map_sdiff,card_map,hs,← List.map_take,hm,Finset.map_union]
 theorem zeroMarginal_reindex (e : I ≃o J) (d : J → ℚ) (own : Finset I) (Δ : ℕ) (i : I) :
    zeroMarginal d (own.map e.toEquiv.toEmbedding) Δ (e i)=
      zeroMarginal (fun j => d (e j)) own Δ i := by
  rw [zeroMarginal,zeroSelection,← zeros_reindex e.toEquiv,extend_reindex]
  simp only [mem_map_equiv,zeroMarginal,zeroSelection]
  change (if e.toEquiv.symm (e.toEquiv i)∈extend own (zeroSources (fun j => d (e j))) Δ then (1:ℚ) else 0)=_
  rw [e.toEquiv.symm_apply_apply]
  rfl
end MetricKMedian.Taper
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchProposalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalBatchData.ProposalProgram
open Finset FixedBatch
variable {C : Type} (I : C → Type) [∀ c, LinearOrder (I c)] [∀ c, Fintype (I c)]

structure Input where
  ctx : C
  n : ℕ
  enum : Fin n ≃o I ctx
  G : I ctx → Finset (I ctx)
  Δ : ℕ
  g : ℚ
  b : ℚ
  p : ℚ
  φ : ℚ
  hp : 0≤p
  hφ : 0≤φ
  hupper : (1+φ)*p≤1
end MetricKMedian.RationalBatchData.ProposalProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundCountsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
open Finset
variable {τ : ℝ}

structure Input where
  f : ℕ
  j : ℕ
  d₀ : Fin f → Fin f → ℚ
  d : Fin j → Fin f → ℚ
  n : Fin f → ℕ
end MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_OriginalMaskProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.MaskProgram
open Finset

def pullback (x : List ℚ × List ℕ) : List ℚ := x.2.map (fun i => x.1[i]?.getD 0)
end MetricKMedian.MaskProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparedScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
open Finset
variable {τ : ℝ}
abbrev Raw := (List Unit × List ℕ) × ((List (List ℚ) × List (List ℚ)) × (List (List ℕ) × ℚ))

def dummy : RoundCountsProgram.Input := ⟨0,0,Fin.elim0,Fin.elim0,Fin.elim0⟩
end MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset
abbrev QRow := List ℚ
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end


