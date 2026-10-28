-- Prove2me | Definitions.Def_OAIQ035K035
-- name    : OAIQ035K035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:01:07.172529+00:00
-- url     : https://prove2.me/theorems/129bc891-f732-4e8e-804f-ea7c4e475e95
-- title:
--   Definitions bundle OAIQ035K035 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 10 definitions and 19 theorems. The definitions and types are `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.Input.rep`, `OAI.MetricKMedian.RoundingProgram.Terminal.bernoulliInput`, `OAI.MetricKMedian.ScalarTransfer.N`, `OAI.MetricKMedian.SparseOuterLaw.deficit`, `OAI.MetricKMedian.SparseOuterLaw.nominalMass`, `OAI.MetricKMedian.SparseSignedPreparation.BudgetSpec`, `OAI.MetricKMedian.SparseSignedPreparation.nominalCount`, `OAI.MetricKMedian.SparseSignedPreparation.outside`, `OAI.MetricKMedian.SparseSignedPreparation.raw`, `OAI.MetricKMedian.SparseTargetSubset.Program.Input.weighted`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Analysis_ScalarTransfer`, `KMedian_Preparation_PreparationStars`, `KMedian_Preparation_RationalSupplierScan`, `KMedian_Preparation_RepresentativeProgram`, `KMedian_Programs_UnitRepresentativeProgram`, `KMedian_Rounding_ExceptionalStar`, `KMedian_Rounding_MarginalRounding`, `KMedian_Rounding_RationalLastFraction`, `KMedian_Rounding_SignedTerminalProgram`, `KMedian_Rounding_TargetSubsetProgram`, `KMedian_Sparse_SparseAffineMoments`, `KMedian_Sparse_SparseMap`, `KMedian_Sparse_SparseMarginalTools`, `KMedian_Sparse_SparseMomentAlgebra`, `KMedian_Sparse_SparseOuterLaw`, `KMedian_Sparse_SparseOuterMoments`, `KMedian_Sparse_SparseOuterReal`, `KMedian_Sparse_SparseSignedBudget`, `KMedian_Sparse_SparseTargetSubset`.
--
--   **Imports.** It imports the bundles `OAIQ035K016`, `OAIQ035K017`, `OAIQ035K022`, `OAIQ035K023`, `OAIQ035K024` and `OAIQ035K025` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K043`, `OAIQ035K044` and `OAIQ035K045`; the proof of `OAI.MetricKMedian.WeightedRounding.exact_law`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K017
import Definitions.Def_OAIQ035K022
import Definitions.Def_OAIQ035K023
import Definitions.Def_OAIQ035K024
import Definitions.Def_OAIQ035K025

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_ScalarTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

noncomputable def N (p k : ℝ) (s : Bool) : ℝ := c p s-(1-bit s)*k

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparationStars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation.SupplierStars
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

theorem raw_identity (y : I → ℝ) (P A : T → Finset I) (c : T → ℝ) (γ : ℝ)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hc : ∀ t, ∑ i ∈ A t, y i=c t)
    (hunit : ∀ t, (∑ i ∈ P t, y i)+c t=1) :
    (Fintype.card T:ℝ)+(∑ e, (flag e-((targets A e).card:ℝ))*weight y P A c γ e)=
      (∑ i, y i)-γ*∑ t, c t := by
  simp_rw [sub_mul]
  rw [sum_sub_distrib,flagged_weight,target_card_sum]
  simp_rw [targeted_weight y P A c γ hP hc]
  rw [← mul_sum]
  have hp := mass_partition y P hP univ
  simp only [univ_inter] at hp
  have hu := congrArg (fun f : T → ℝ => ∑ t, f t) (funext hunit)
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,card_univ] at hu
  linarith only [hu,hp]

end MetricKMedian.Preparation.SupplierStars
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

theorem second_fractional {p : I → ℝ} {K : ℕ} (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (hsum : ∑ i, p i = K) {i : I} (hi : i ∈ fractional p) :
    ∃ j ∈ fractional p, j ≠ i := by
  classical
  by_contra h
  push Not at h
  have hother : ∀ j, j ≠ i → j ∉ fractional p := by
    intro j hji hj
    exact hji (h j hj)
  have hi0 := (mem_fractional p i).mp hi
  have hpoint : ∀ j, p j = (if p j=1 then (1:ℝ) else 0)+(if j=i then p i else 0) := by
    intro j
    by_cases hji : j=i
    · subst j
      rw [ite_eq_right (ne_of_lt hi0.2), ite_eq_left rfl, zero_add]
    · rw [ite_eq_right hji, add_zero]
      rcases nonfractional_integral hp hp1 (hother j hji) with hj | hj <;> simp [hj]
  let S := Finset.univ.filter (fun j => p j=1)
  have hid : (∑ j, p j) = (S.card:ℝ)+p i := by
    conv_lhs => arg 2; ext j; rw [hpoint j]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    congr 1
    rw [← Finset.sum_filter]
    simp only [S, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hlow : S.card < K := by
    have hh : (S.card:ℝ) < K := by linarith only [hi0.1, hid, hsum]
    exact_mod_cast hh
  have hhigh : K < S.card+1 := by
    have hh : (K:ℝ) < (S.card+1:ℕ) := by push_cast; linarith only [hi0.2, hid, hsum]
    exact_mod_cast hh
  omega

end MetricKMedian.MarginalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMarginalTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

 theorem moment_mono (μ : SparseIntegerLaw α) (f g : α → ℚ)
    (h : ∀ i : Fin μ.length, f μ.states[i.val] ≤ g μ.states[i.val]) :
    μ.moment f ≤ μ.moment g := by
  apply sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (h i) (μ.law.rational.nonneg i)

 theorem moment_const (μ : SparseIntegerLaw α) (c : ℚ) : μ.moment (fun _ => c)=c := by
  unfold moment
  rw [← sum_mul,μ.law.rational.total,one_mul]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMomentAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem moment_add (μ : SparseIntegerLaw α) (f g : α → ℚ) :
    μ.moment (fun a => f a+g a)=μ.moment f+μ.moment g := by
  simp only [moment,mul_add,sum_add_distrib]

theorem moment_mul_right (μ : SparseIntegerLaw α) (f : α → ℚ) (c : ℚ) :
    μ.moment (fun a => f a*c)=μ.moment f*c := by
  simp only [moment,← mul_assoc,sum_mul]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
variable {α β : Type}

theorem map_moment (μ : SparseIntegerLaw α) (f : α → β) (v : β → ℚ) :
    (μ.map f).moment v=μ.moment (fun a => v (f a)) := by
  unfold moment map
  simp only [Vector.getElem_map]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalLastFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalLastFraction
open Finset RationalWeightedStep
variable {n : ℕ}

theorem endpoint_mean (p : Vector ℚ n) (k : Fin n) :
    probability p*point (endpoint p 0) k+
      (1-probability p)*point (endpoint p 1) k=point p k := by
  by_cases h : (fractional p).Nonempty
  · simp only [probability,endpoint,dite_eq_left h,point,Vector.getElem_ofFn,Fin.eta]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    by_cases hi : k=pick p h
    · subst k; simp only [ite_true]; ring
    · simp only [ite_eq_right hi]; ring
  · simp only [probability,endpoint,dite_eq_right h]; ring

theorem endpoint_integral (p : Vector ℚ n)
    (hp : ∀ k, 0 ≤ point p k ∧ point p k ≤ 1)
    (hsmall : (fractional p).card ≤ 1) (b : Fin 2) (k : Fin n) :
    point (endpoint p b) k=0 ∨ point (endpoint p b) k=1 := by
  by_cases h : (fractional p).Nonempty
  · simp only [endpoint,dite_eq_left h,point,Vector.getElem_ofFn,Fin.eta]
    by_cases hk : k=pick p h
    · simp only [ite_eq_left hk]; split_ifs <;> simp
    · simp only [ite_eq_right hk]
      apply nonfractional p hp k
      intro hm
      exact hk (card_le_one.mp hsmall k hm (pick p h) (pick_mem p h))
  · simp only [endpoint,dite_eq_right h]
    apply nonfractional p hp
    exact fun hm => h ⟨k,hm⟩

theorem endpoint_noise (p : Vector ℚ n) (β : Fin n → ℚ) {M : ℚ}
    (hβ0 : ∀ k, 0 ≤ β k) (hβM : ∀ k, β k ≤ M) (hM : 0 ≤ M) (b : Fin 2) :
    |(∑ k, β k*point (endpoint p b) k)-(∑ k, β k*point p k)| ≤ M := by
  by_cases h : (fractional p).Nonempty
  · simp only [endpoint,dite_eq_left h]
    let i := pick p h
    have hi := (mem_filter.mp (pick_mem p h)).2
    rw [← sum_sub_distrib]
    have hid : (∑ k, (β k*point (Vector.ofFn
        (fun k => if k=pick p h then (if b=0 then 1 else 0) else point p k)) k-β k*point p k))=
        β i*((if b=0 then 1 else 0)-point p i) := by
      rw [sum_eq_single i]
      · simp only [point,Vector.getElem_ofFn,Fin.eta,i,ite_true]
        ring
      · intro k _ hki
        simp only [point,Vector.getElem_ofFn,Fin.eta,show k ≠ pick p h from hki,ite_false,sub_self]
      · intro hh; exact False.elim (hh (mem_univ i))
    rw [hid,abs_mul,abs_of_nonneg (hβ0 i)]
    have herr : |(if b=0 then (1:ℚ) else 0)-point p i| ≤ 1 := by
      apply abs_le.mpr
      split_ifs <;> constructor <;> dsimp only [i] <;> linarith only [hi.1,hi.2]
    exact (mul_le_mul_of_nonneg_left herr (hβ0 i)).trans (by simpa only [mul_one] using hβM i)
  · simpa only [endpoint,dite_eq_right h,sub_self,abs_zero] using hM

end MetricKMedian.RationalLastFraction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_ExceptionalStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset MarginalRounding
variable {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

omit [DecidableEq E] [Fintype T] [DecidableEq T] in

theorem exceptional_raw_error (D : E → Finset T) (q a : E → ℝ) (S : E → Finset T)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (_ha0 : ∀ e, 0 ≤ a e) (ha1 : ∀ e, a e ≤ 1)
    (hsmall : (fractional q).card ≤ 1)
    (hS : ∀ e, |((S e).card:ℝ)-((D e).card:ℝ)*q e| ≤ 1 ∧
      (q e=0 → S e=∅) ∧ (q e=1 → S e=D e)) :
    (∑ e, (a e*(upperBit (q e)-q e)+((D e).card:ℝ)*q e-((S e).card:ℝ))) ≤ 2 := by
  let v : E → ℝ := fun e => a e*(upperBit (q e)-q e)+((D e).card:ℝ)*q e-((S e).card:ℝ)
  have hv0 : ∀ e, e ∉ fractional q → v e=0 := by
    intro e he
    rcases nonfractional_integral hq0 hq1 he with h | h
    · simp only [v, h, upperBit, lt_self_iff_false, ite_false, sub_self, mul_zero, zero_add,
        (hS e).2.1 h, card_empty, Nat.cast_zero]
    · simp only [v, h, upperBit, zero_lt_one, ite_true, sub_self, mul_zero, mul_one,
        zero_add, (hS e).2.2 h, sub_self]
  have hv : ∀ e, v e ≤ 2 := by
    intro e
    have hu := upperBit_bounds (hq0 e) (hq1 e)
    have hprod := mul_le_mul (ha1 e)
      (show upperBit (q e)-q e ≤ 1 by linarith only [hu.2, hq0 e])
      (sub_nonneg.mpr hu.1) (by norm_num : (0:ℝ) ≤ 1)
    have herr := (abs_le.mp (hS e).1).1
    dsimp only [v]
    nlinarith only [hprod, herr]
  have heq : (∑ e, v e)=∑ e ∈ fractional q, v e := by
    apply (sum_subset (subset_univ _) (fun e _ he => hv0 e he)).symm
  change (∑ e, v e) ≤ 2
  rw [heq]
  calc
    _ ≤ ∑ _e ∈ fractional q, (2:ℝ) := sum_le_sum (fun e _ => hv e)
    _ = ((fractional q).card:ℝ)*2 := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ 2 := by exact_mod_cast (by omega : (fractional q).card*2 ≤ 2)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseAffineMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
variable {α : Type}

theorem moment_sub (μ : SparseIntegerLaw α) (f g : α → ℚ) :
    μ.moment (fun a => f a-g a)=μ.moment f-μ.moment g := by
  simp only [moment,mul_sub,Finset.sum_sub_distrib]

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseTargetSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseTargetSubset
open Finset RationalWeightedStep
variable {n : ℕ}

theorem initial_unit (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1) :
    ∀ i, 0 ≤ point (initial D q) i ∧ point (initial D q) i ≤ 1 := by
  intro i
  rw [point_initial]
  split_ifs
  · exact hq
  · exact ⟨le_rfl,zero_le_one⟩

end MetricKMedian.SparseTargetSubset
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSignedBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPreparation
open Finset
open RationalWeightedStep (point fractional)
variable {n m : ℕ}

def outside (b : Fin m → ℕ) (z : State n m) (e : Fin m) : ℚ :=
  (b e:ℚ)+SparseStarActivation.upper (point z.1 e)

def nominalCount (b : Fin m → ℕ) (z : State n m) (e : Fin m) : ℚ :=
  (b e:ℚ)+SparseBernoulli.flag z.2.2 e

def raw (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (b : Fin m → ℕ) (z : State n m) : ℚ :=
  ∑ e, (c e*outside b z e-(((D e).card:ℚ)*(b e:ℚ)+(z.2.1 e).card))

def BudgetSpec (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (b : Fin m → ℕ)
    (t : ℚ) (z : State n m) : Prop :=
  (∀ e, z.2.1 e ⊆ D e) ∧
  (∀ e, outside b z e=(b e:ℚ) ∨ outside b z e=(b e:ℚ)+1) ∧
  (∀ e, nominalCount b z e=(b e:ℚ) ∨ nominalCount b z e=(b e:ℚ)+1) ∧
  (∀ e, nominalCount b z e ≤ outside b z e) ∧
  (∀ e i, (b e:ℚ)+(if i∈z.2.1 e then 1 else 0) ≤ outside b z e) ∧
  raw D c b z ≤ t

end MetricKMedian.SparseSignedPreparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseOuterLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem fraction_identity (q : Fin m → ℚ) (e : Fin m) :
    (base q e:ℚ)+point (fraction q) e=q e := by
  simp only [point,fraction,Vector.getElem_ofFn,add_sub_cancel]

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseOuterReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

noncomputable def nominalMass (q : Fin m → ℚ) (g : ℝ) (z : State n m) (e : Fin m) : ℝ :=
  g * (SparseSignedPreparation.nominalCount (base q) z e : ℝ)

theorem nominalMass_nonneg (q : Fin m → ℚ) {g : ℝ} (hg : 0 ≤ g)
    (z : State n m) (e : Fin m) : 0 ≤ nominalMass q g z e := by
  apply mul_nonneg hg
  dsimp only [SparseSignedPreparation.nominalCount, SparseBernoulli.flag]
  split_ifs <;> positivity

end MetricKMedian.SparseOuterLaw
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseOuterMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open SparseGridRounding (base)
open SparseSignedPreparation (State)
variable {n m : ℕ}

def deficit (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (g : ℚ)
    (z : State n m) (i : Fin n) : ℚ := g*∑ e, activation D q z e i

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RationalSupplierScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars

namespace FixedParameters
theorem grid {τ : ℝ} (qR : FixedBatch.RationalParameters τ) : qR.g*(qR.Δ:ℚ)=1 := by exact_mod_cast qR.unit
end FixedParameters

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RepresentativeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalRepresentatives.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram

 theorem select_empty {n : ℕ} (t : ℕ) (R : Fin n → ℚ) (d : Fin n → Fin n → ℚ) (M : ℚ) : select d R M t ∅=∅ := by
  cases t <;> simp [select,Finset.not_nonempty_empty]
 theorem advance_result (x : Input) (t : ℕ) (s : Cut x) :
    ((advance x)^[t] s).2=s.2 ∪ select x.d x.R x.M t s.1 := by
  induction t generalizing s with
  | zero => simp only [Function.iterate_zero,Function.id_def,select,union_empty]
  | succ t ih =>
    rw [Function.iterate_succ_apply,ih]
    by_cases h : s.1.Nonempty
    · simp only [advance,dite_eq_left h,select]
      ext i
      simp only [mem_union,mem_insert]
      tauto
    · have he : s.1=∅ := not_nonempty_iff_eq_empty.mp h
      simp [advance,he,select_empty]

end MetricKMedian.Preparation.RationalRepresentatives.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_UnitRepresentativeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Preparation.RationalUnitInput.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram

def Input.rep (M : ℚ) (x : Input) : RationalRepresentatives.Program.Input :=
  ⟨x.j,x.U.V,x.U.dd,M,univ⟩

end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedTerminalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open Binary.Automatic Binary.Automatic.Poly
namespace Terminal

 theorem point_toList {n : ℕ} (p : Vector ℚ n) : p.toList=List.ofFn (RationalWeightedStep.point p) := by
  apply List.ext_getElem <;> intros <;> simp [RationalWeightedStep.point]

def bernoulliInput (x : Input true) : BInput := ⟨x.n,RationalWeightedStep.point x.p,x.feasible⟩

end Terminal
end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_TargetSubsetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseTargetSubset.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)

def Input.weighted (x : Input) : RoundingProgram.Input false :=
  ⟨x.n,fun _ => 1,initial x.D x.q,fun _ _ => by norm_num,initial_unit x.D x.feasible⟩
end MetricKMedian.SparseTargetSubset.Program
end

end OAI
end


