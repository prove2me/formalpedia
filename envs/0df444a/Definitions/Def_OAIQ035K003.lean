-- Prove2me | Definitions.Def_OAIQ035K003
-- name    : OAIQ035K003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:53:09.044706+00:00
-- url     : https://prove2.me/theorems/9f88f094-b37a-48c9-95c4-e6e614c1df9f
-- title:
--   Definitions bundle OAIQ035K003 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 50 declarations of OpenAI's Lean: 27 definitions, 3 inductive types or structures and 20 theorems. The definitions and types are `OAI.MetricKMedian.Completion.Rational.MaskOperations.instLinearOrderCopyFin`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.Cut`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.Input`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.Input.start`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.Input.state`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.State`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.State.step`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.advance`, `OAI.MetricKMedian.Completion.Rational.Program.Input`, `OAI.MetricKMedian.Completion.Rational.Program.Input.packing`, `OAI.MetricKMedian.Completion.Rational.instLinearOrderCopy`, `OAI.MetricKMedian.Completion.Rational.output`, `OAI.MetricKMedian.Completion.Rational.packing`, `OAI.MetricKMedian.Completion.Rational.pick`, `OAI.MetricKMedian.Completion.Rational.uncovered`, `OAI.MetricKMedian.Compression.extendVector`, `OAI.MetricKMedian.CopyState.Copy`, `OAI.MetricKMedian.CopyState.activeSlots`, `OAI.MetricKMedian.CopyState.embedSlots`, `OAI.MetricKMedian.CopyState.integral`, `OAI.MetricKMedian.CopyState.localSet`, `OAI.MetricKMedian.CopyState.own`, `OAI.MetricKMedian.CopyState.resets`, `OAI.MetricKMedian.CopyState.slots`, `OAI.MetricKMedian.FiniteComparison.H`, `OAI.MetricKMedian.FiniteComparison.kZero`, `OAI.MetricKMedian.PhysicalPotential.mass`, `OAI.MetricKMedian.Preparation.firstNearest`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyList.rank`, `OAI.MetricKMedian.RationalPhysicalKernel.copyOrder`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Analysis_FiniteAverages`, `KMedian_Compression_FinsetVectorExtension`, `KMedian_Compression_GaussianListOperations`, `KMedian_Compression_GramBounds`, `KMedian_Compression_IntegerCoefficientBounds`, `KMedian_Optimization_ComputedNearest`, `KMedian_Optimization_LPMinimumSelection`, `KMedian_Preparation_AssignmentCopies`, `KMedian_Process_CopyGraphProgram`, `KMedian_Process_CopyListEncoding`, `KMedian_Process_CopyRound`, `KMedian_Process_CopyState`, `KMedian_Process_CopyTransport`, `KMedian_Process_PhysicalPotential`, `KMedian_Process_RoundingListOperations`, `KMedian_Programs_GreedyPackingProgram`, `KMedian_Reduction_CompletionMaskProgram`, `KMedian_Reduction_CompletionProgram`, `KMedian_Reduction_RationalGreedyCompletion`, `KMedian_Rounding_RationalPhysicalKernel`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K015`, `OAIQ035K016`, `OAIQ035K017`, `OAIQ035K018`, `OAIQ035K019`, `OAIQ035K020`, `OAIQ035K021`, `OAIQ035K023`, `OAIQ035K024`, `OAIQ035K025`, `OAIQ035K036`, `OAIQ035K044` and `OAIQ035K062`; the statement `OAI.MetricKMedian.Certificates.k_envelope`; the proof of `OAI.MetricKMedian.Certificates.k_envelope`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_FiniteAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteComparison

noncomputable def kZero (p : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - p)) / (1 + Real.sqrt (1 - p))

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

noncomputable def H (h : ℝ) (s : Bool) : ℝ := if s then 1 / 4 else h

end MetricKMedian.FiniteComparison


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_FinsetVectorExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Compression
open Finset

def extendVector {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ) (i : Fin n) : ℤ :=
  if h : i ∈ s then z ((s.orderIsoOfFin rfl).symm ⟨i,h⟩) else 0

end MetricKMedian.Compression

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Gaussian.ListOperation
open Finset
universe uα uβ
variable {α : Type uα} {β : Type uβ}

 theorem zip_ofFn {n : ℕ} (f : Fin n → α) (g : Fin n → β) :
    (List.ofFn f).zip (List.ofFn g)=List.ofFn (fun i => (f i,g i)) := by
  apply List.ext_getElem (by simp only [List.length_zip,List.length_ofFn,min_self])
  intro i hi hj
  simp only [List.getElem_zip,List.getElem_ofFn]

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GramBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix
variable {R C : Type} [Fintype R] [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
                                                                      
theorem gram_entry_bound (A : Matrix R C ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) (c d : C) :
    |(A.transpose*A) c d| ≤ (Fintype.card R:ℤ)*M^2 := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ r, |A r c*A r d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : R, M^2 := sum_le_sum (fun r _ => by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hA r c) (hA r d) (abs_nonneg _) hM)
    _ = _ := by simp

omit [Fintype C] [DecidableEq C] in
theorem gram_rhs_bound (A : Matrix R C ℤ) (w : R → ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) (hw : ∀ r, |w r| ≤ M) (c : C) :
    |(A.transpose*ᵥw) c| ≤ (Fintype.card R:ℤ)*M^2 := by
  change |∑ r, A r c*w r| ≤ _
  calc
    _ ≤ ∑ r, |A r c*w r| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : R, M^2 := sum_le_sum (fun r _ => by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hA r c) (hw r) (abs_nonneg _) hM)
    _ = _ := by simp

theorem gram_det_bound (A : Matrix R C ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) :
    |(A.transpose*A).det| ≤ (Nat.factorial (Fintype.card C):ℤ)*
      ((Fintype.card R:ℤ)*M^2)^(Fintype.card C) := by
  simpa only [AbsoluteValue.abs_apply,nsmul_eq_mul] using
    (Matrix.det_le (abv := AbsoluteValue.abs) (gram_entry_bound A M hM hA))

theorem gram_cramer_bound (A : Matrix R C ℤ) (w : R → ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) (hw : ∀ r, |w r| ≤ M) (c : C) :
    |((A.transpose*A).cramer (A.transpose*ᵥw)) c| ≤ (Nat.factorial (Fintype.card C):ℤ)*
      ((Fintype.card R:ℤ)*M^2)^(Fintype.card C) := by
  rw [Matrix.cramer_apply]
  have hentry : ∀ i j, |((A.transpose*A).updateCol c (A.transpose*ᵥw)) i j| ≤
      (Fintype.card R:ℤ)*M^2 := by
    intro i j
    by_cases hj : j=c
    · subst j
      simpa using gram_rhs_bound A w M hM hA hw i
    · simpa [Matrix.updateCol_apply,hj] using gram_entry_bound A M hM hA i j
  simpa only [AbsoluteValue.abs_apply,nsmul_eq_mul] using
    (Matrix.det_le (abv := AbsoluteValue.abs) hentry)

end MetricKMedian.Compression

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_IntegerCoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Compression

theorem gram_coefficient_bit_bound (r n L : ℕ) (hn : n ≤ r) :
    (n.factorial:ℤ)*((r:ℤ)*((2:ℤ)^L)^2)^n ≤ (2:ℤ)^(2*r*(r+L)) := by
  have hnr : n ≤ 2^r := hn.trans Nat.lt_two_pow_self.le
  have hf : n.factorial ≤ 2^(r*r) := by
    calc
      _ ≤ n^n := Nat.factorial_le_pow n
      _ ≤ (2^r)^n := Nat.pow_le_pow_left hnr n
      _ = 2^(r*n) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left r hn)
  have hfZ : (n.factorial:ℤ) ≤ 2^(r*r) := by exact_mod_cast hf
  have hrZ : (r:ℤ) ≤ 2^r := by exact_mod_cast (Nat.lt_two_pow_self (n:=r)).le
  have hb : (r:ℤ)*((2:ℤ)^L)^2 ≤ 2^(r+2*L) := by
    calc
      _ ≤ 2^r*((2:ℤ)^L)^2 := mul_le_mul_of_nonneg_right hrZ (sq_nonneg _)
      _ = _ := by rw [pow_add,Nat.mul_comm 2 L,pow_mul]
  have hbn : ((r:ℤ)*((2:ℤ)^L)^2)^n ≤ 2^((r+2*L)*r) := by
    calc
      _ ≤ ((2:ℤ)^(r+2*L))^n := pow_le_pow_left₀ (by positivity) hb n
      _ = 2^((r+2*L)*n) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hn)
  calc
    _ ≤ 2^(r*r)*(2:ℤ)^((r+2*L)*r) :=
      mul_le_mul hfZ hbn (by positivity) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; ring

end MetricKMedian.Compression

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ComputedNearest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {n : ℕ}

def firstNearest (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty) : Fin n :=
  let m := (U.image d).min' (hU.image _)
  let B := U.filter (fun i => d i=m)
  have hB : B.Nonempty := by
    obtain ⟨a,ha,he⟩ := mem_image.mp (min'_mem (U.image d) (hU.image _))
    exact ⟨a,mem_filter.mpr ⟨ha,he⟩⟩
  B.min' hB

theorem firstNearest_spec (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty) :
    firstNearest U d hU ∈ U ∧ ∀ i ∈ U, d (firstNearest U d hU) ≤ d i := by
  let B := U.filter (fun i => d i=(U.image d).min' (hU.image _))
  have hB : B.Nonempty := by
    obtain ⟨a,ha,he⟩ := mem_image.mp (min'_mem (U.image d) (hU.image _))
    exact ⟨a,mem_filter.mpr ⟨ha,he⟩⟩
  change B.min' hB ∈ U ∧ ∀ i ∈ U, d (B.min' hB) ≤ d i
  have hh := mem_filter.mp (min'_mem B hB)
  refine ⟨hh.1,?_⟩
  intro i hi
  rw [hh.2]
  exact min'_le _ _ (mem_image.mpr ⟨i,hi,rfl⟩)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPMinimumSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

 theorem firstNearest_value {n : ℕ} (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty) :
    d (Preparation.firstNearest U d hU)=(U.image d).min' (hU.image _) := by
  unfold Preparation.firstNearest
  exact (mem_filter.mp (min'_mem (U.filter (fun i => d i=(U.image d).min' (hU.image _))) _)).2

 theorem firstNearest_le {n : ℕ} (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty)
    (j : Fin n) (hj : j∈U) (hd : d j=d (Preparation.firstNearest U d hU)) :
    Preparation.firstNearest U d hU ≤ j := by
  unfold Preparation.firstNearest
  apply min'_le
  exact mem_filter.mpr ⟨hj,hd.trans (firstNearest_value U d hU)⟩

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

noncomputable def mass {I : Type*} (g : ℝ) (S : Finset I) : ℝ := g * S.card

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type*} [DecidableEq F]
variable (Δ : ℕ)

abbrev Copy := F × Fin Δ

def slots (f : F) : Finset (Copy (F := F) Δ) := univ.image (fun i => (f,i))

@[simp] theorem mem_slots (f : F) (i : Copy (F := F) Δ) : i ∈ slots Δ f ↔ i.1=f := by
  rw [slots, mem_image]
  constructor
  · rintro ⟨a,_,he⟩
    exact (congrArg Prod.fst he).symm
  · intro h
    exact ⟨i.2, mem_univ _, Prod.ext h.symm rfl⟩

@[simp] theorem card_slots (f : F) : (slots Δ f).card=Δ := by
  rw [slots, card_image_of_injective _ (fun i j h => (Prod.mk.inj h).2)]
  simp

def resets (O : Finset F) : Finset (Copy (F := F) Δ) := O.biUnion (slots Δ)

@[simp] theorem mem_resets (O : Finset F) (i : Copy (F := F) Δ) : i ∈ resets Δ O ↔ i.1 ∈ O := by
  simp [resets]

variable [Fintype F]

def integral (A : Finset (Copy (F := F) Δ)) : Finset F := univ.filter (fun f => slots Δ f ⊆ A)

@[simp] theorem mem_integral (A : Finset (Copy (F := F) Δ)) (f : F) :
    f ∈ integral Δ A ↔ slots Δ f ⊆ A := by simp [integral]

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_AssignmentCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type} [Fintype F] [DecidableEq F] {Δ : ℕ}

def embedSlots (n : F → ℕ) (hn : ∀ a, n a ≤ Δ) : (Σ a, Fin (n a)) → Copy (F := F) Δ :=
  fun a => (a.1,⟨a.2.val,lt_of_lt_of_le a.2.isLt (hn a.1)⟩)

def activeSlots (n : F → ℕ) (hn : ∀ a, n a ≤ Δ) : Finset (Copy (F := F) Δ) :=
  univ.image (embedSlots n hn)

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.RoundingList
open Finset

theorem range_finRange (n : ℕ) : List.range n=(List.finRange n).map Fin.val := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_range,List.getElem_map,List.getElem_finRange,Fin.val_cast]

end MetricKMedian.RoundingList
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset
variable {F : Type*} [DecidableEq F] [Fintype F] (Δ : ℕ)

noncomputable def own (A : Finset (Copy (F := F) Δ)) (i : A) : Finset A :=
  univ.filter (fun h => h.val.1=i.val.1)

omit [Fintype F] in
@[simp] theorem mem_own (A : Finset (Copy (F := F) Δ)) (i h : A) :
    h ∈ own Δ A i ↔ h.val.1=i.val.1 := by simp [own]

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset
variable {F : Type} [LinearOrder F] [Fintype F] {Δ : ℕ}

@[instance_reducible] def copyOrder : LinearOrder (CopyState.Copy (F := F) Δ) :=
  { LinearOrder.lift' (fun p : CopyState.Copy (F := F) Δ => toLex p) (fun _ _ h => h) with
    toDecidableEq := inferInstanceAs (DecidableEq (F × Fin Δ))
    compare := fun a b => if toLex a < toLex b then Ordering.lt else if a=b then Ordering.eq else Ordering.gt
    compare_eq_compareOfLessAndEq := by intros; rfl }

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyListEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.RationalPhysicalKernel.CopyList
open Finset
variable {f Δ : ℕ}

abbrev rank (a : CopyState.Copy (F:=Fin f) Δ) : Fin (f*Δ) := finProdFinEquiv a

 local instance instLinearOrderCopyFin_rcd6a93_1 : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
theorem rank_strictMono : @StrictMono _ _ (copyOrder (F:=Fin f) (Δ:=Δ)).toPreorder _ (rank (f:=f) (Δ:=Δ)) := by
  intro a b hab
  change Prod.Lex (fun a b : Fin f => a<b) (fun a b : Fin Δ => a<b) a b at hab
  change a.2.val+Δ*a.1.val<b.2.val+Δ*b.1.val
  rcases Prod.lex_def.mp hab with h | ⟨h,h'⟩
  · have h1 : a.1.val+1≤b.1.val := h
    have h2 := a.2.isLt
    nlinarith
  · rw [h]
    have h2 : a.2.val<b.2.val := h'
    omega

end MetricKMedian.RationalPhysicalKernel.CopyList
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
open Finset
open CopyList

 theorem rank_owner {f Δ : ℕ} (a : CopyState.Copy (F:=Fin f) Δ) :
    (rank a).val/Δ=a.1.val := by
  change (a.2.val+Δ*a.1.val)/Δ=a.1.val
  have hd : 0<Δ := Nat.zero_lt_of_lt a.2.isLt
  rw [Nat.add_comm,Nat.mul_add_div hd,Nat.div_eq_of_lt a.2.isLt,Nat.add_zero]

end MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type*} [DecidableEq F] {Δ : ℕ}

noncomputable def localSet (A S : Finset (Copy (F := F) Δ)) : Finset A :=
  univ.filter (fun i => i.val ∈ S)

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_RationalGreedyCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.Completion.Rational
open Finset PhysicalPotential CopyState Preparation
variable {j : ℕ} {I : Type*} [DecidableEq I]

def packing : ℕ → Finset (Fin j) → (Fin j → ℚ) → (Fin j → Finset I) → Finset (Fin j)
  | 0, _, _, _ => ∅
  | t+1, U, R, B => if h : U.Nonempty then
      let c := firstNearest U R h
      insert c (packing t (U.filter (fun i => Disjoint (B c) (B i))) R B)
    else ∅

variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}
local instance instLinearOrderCopy : LinearOrder (Copy (F := F) Δ) := RationalPhysicalKernel.copyOrder

def uncovered (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (A : Finset (Copy (F := F) Δ)) : Finset (Fin j) :=
  univ.filter (fun c => ¬ ∃ f ∈ integral Δ A, d c f ≤ 5*R c)

def pick (B : Fin j → Finset (Copy (F := F) Δ))
    (hB : ∀ c, (B c).Nonempty) (c : Fin j) : Copy (F := F) Δ := (B c).min' (hB c)

def output (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (A : Finset (Copy (F := F) Δ)) (B : Fin j → Finset (Copy (F := F) Δ))
    (hB : ∀ c, (B c).Nonempty) : Finset F :=
  integral Δ A ∪ (packing j (uncovered d R A) R B).image (fun c => (pick B hB c).1)

end MetricKMedian.Completion.Rational
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_GreedyPackingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Completion.Rational.PackingProgram
open Finset Polynomial

structure Input where
  n : ℕ
  m : ℕ
  R : Fin n → ℚ
  B : Fin n → Finset (Fin m)
  U : Finset (Fin n)
abbrev Cut (x : Input) := Finset (Fin x.n) × Finset (Fin x.n)
def advance (x : Input) (s : Cut x) : Cut x :=
  if h : s.1.Nonempty then
    let c := Preparation.firstNearest s.1 x.R h
    (s.1.filter (fun i => Disjoint (x.B c) (x.B i)),insert c s.2)
  else s
structure State where
  input : Input
  cut : Cut input
def State.step (s : State) : State := ⟨s.input,advance s.input s.cut⟩
def Input.state (x : Input) (t : ℕ) : State := ⟨x,(advance x)^[t] (x.U,∅)⟩
def Input.start (x : Input) := x.state 0

 theorem state_iterate (x : Input) (t : ℕ) : State.step^[t] x.start=x.state t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih]
    change (⟨x,advance x ((advance x)^[t] (x.U,∅))⟩ : State)=_
    simp only [Input.state,Function.iterate_succ_apply']

 theorem packing_empty {n m : ℕ} (t : ℕ) (R : Fin n → ℚ) (B : Fin n → Finset (Fin m)) : packing t ∅ R B=∅ := by
  cases t <;> simp [packing,Finset.not_nonempty_empty]
end MetricKMedian.Completion.Rational.PackingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_CompletionMaskProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Completion.Rational.MaskOperations
open Finset CopyState
open RationalPhysicalKernel.CopyList
local instance instLinearOrderCopyFin {f Δ : ℕ} : LinearOrder (Copy (F:=Fin f) Δ) := RationalPhysicalKernel.copyOrder

 theorem packing_map {j : ℕ} {I K : Type} [DecidableEq I] [DecidableEq K]
    (e : I ↪ K) (t : ℕ) (U : Finset (Fin j)) (R : Fin j → ℚ) (B : Fin j → Finset I) :
    packing t U R (fun c => (B c).map e)=packing t U R B := by
  induction t generalizing U with
  | zero => rfl
  | succ t ih =>
    unfold packing
    split_ifs with h
    · simp only [Finset.disjoint_map,ih]
    · rfl
end MetricKMedian.Completion.Rational.MaskOperations
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_CompletionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Completion.Rational.Program
open Finset CopyState
open MaskOperations RationalPhysicalKernel.CopyList

structure Input (Δ : ℕ) where
  f : ℕ
  j : ℕ
  d : Fin j → Fin f → ℚ
  R : Fin j → ℚ
  A : Finset (Copy (F:=Fin f) Δ)
  B : Fin j → Finset (Copy (F:=Fin f) Δ)
  hB : ∀ c, (B c).Nonempty
def Input.packing {Δ : ℕ} (x : Input Δ) : PackingProgram.Input :=
  ⟨x.j,x.f*Δ,x.R,(fun c => (x.B c).map finProdFinEquiv.toEmbedding),uncovered x.d x.R x.A⟩
end MetricKMedian.Completion.Rational.Program
end

end OAI
end


