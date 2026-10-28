-- Prove2me | Definitions.Def_OAIQ035K051
-- name    : OAIQ035K051
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:07:30.92436+00:00
-- url     : https://prove2.me/theorems/02535c46-77b3-4913-92f8-4cd65756e629
-- title:
--   Definitions bundle OAIQ035K051 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 35 declarations of OpenAI's Lean: 7 definitions and 28 theorems. The definitions and types are `OAI.MetricKMedian.SparseBernoulli.Program.Input.start`, `OAI.MetricKMedian.Taper.ListOperation.AllRaw`, `OAI.MetricKMedian.Taper.ListOperation.colocated`, `OAI.MetricKMedian.Taper.ListOperation.extras`, `OAI.MetricKMedian.Taper.ListOperation.sourceRow`, `OAI.MetricKMedian.Taper.ListOperation.zeroRow`, `OAI.MetricKMedian.TaperGraphProgram.rawQ`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Compression_IntegerRationalCompression`, `KMedian_Geometry_BoundFreeCompression`, `KMedian_Probability_BernoulliRunProgram`, `KMedian_Process_RoundingCoordinateHeight`, `KMedian_Process_RoundingRunHeight`, `KMedian_Process_TaperAllProgram`, `KMedian_Process_TaperGraphProgram`, `KMedian_Process_TaperListProgram`, `KMedian_Rounding_SignedGridInvariant`, `KMedian_Sparse_SparseAlgorithm`, `KMedian_Sparse_SparseBindProgram`, `KMedian_Sparse_SparseIterationHeight`, `KMedian_Sparse_SparseProductProgram`, `KMedian_Sparse_SparseSignedPartial`.
--
--   **Imports.** It imports the bundles `OAIQ035K046` and `OAIQ035K047` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K054`, `OAIQ035K055`, `OAIQ035K056`, `OAIQ035K057`, `OAIQ035K058` and `OAIQ035K062`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K046
import Definitions.Def_OAIQ035K047

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_IntegerRationalCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

theorem compressRational_spec {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℚ) (L : ℕ)
    (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) :
    let ν := μ.compressRational v L hnum hden
    ν.denominator ≤ μ.denominator*(2:ℤ)^(((2*(d+1)*(d+1+L*(n+1)))*(n+1))*n) ∧
      ν.support ⊆ μ.support ∧ ν.support.card ≤ d+1 ∧
      ∀ j, (∑ i, ν.rational.weight i*v i j)=∑ i, μ.rational.weight i*v i j := by
  have hh := μ.computedCompress_spec (RationalLaw.scaledFeatures v) (L*(n+1))
    (RationalLaw.scaledFeatures_bound v L hnum hden)
  refine ⟨hh.1,hh.2.1,hh.2.2.1,?_⟩
  intro j
  let D := RationalScaling.denominator (fun i => v i j)
  have hD : (D:ℚ) ≠ 0 := by
    exact_mod_cast (RationalScaling.denominator_pos (fun i => v i j)).ne'
  have hcast : ∀ i, (RationalLaw.scaledFeatures v i j:ℚ)=v i j*(D:ℚ) := by
    intro i
    rw [RationalLaw.scaledFeatures_eq]
    exact RationalScaling.numerator_cast _ i
  have hm := hh.2.2.2 j
  simp only [hcast,← mul_assoc,← sum_mul] at hm
  exact mul_right_cancel₀ hD hm

end MetricKMedian.IntegerLaw

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

theorem compressAuto_spec {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℚ) (L : ℕ)
    (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) :
    let ν := μ.compressAuto v
    ν.denominator ≤ μ.denominator*(2:ℤ)^(((2*(d+1)*(d+1+L*(n+1)))*(n+1))*n) ∧
      ν.support ⊆ μ.support ∧ ν.support.card ≤ d+1 ∧
      ∀ j, (∑ i, ν.rational.weight i*v i j)=∑ i, μ.rational.weight i*v i j := by
  rw [compressAuto_eq μ v L hnum hden]
  exact compressRational_spec μ v L hnum hden

theorem compressAuto_correct {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℚ) :
    let ν := μ.compressAuto v
    ν.support ⊆ μ.support ∧ ν.support.card ≤ d+1 ∧
      ∀ j, (∑ i, ν.rational.weight i*v i j)=∑ i, μ.rational.weight i*v i j := by
  obtain ⟨L,hnum,hden⟩ := exists_rational_feature_bound v
  exact (compressAuto_spec μ v L hnum hden).2

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem compressAuto_correct {d : ℕ} (μ : SparseIntegerLaw α) (v : α → Fin d → ℚ) :
    let ν := μ.compressAuto v
    ν.length ≤ d+1 ∧
      (∀ i : Fin ν.length, ∃ j : Fin μ.length, ν.states[i.val]=μ.states[j.val]) ∧
      ∀ j, ν.moment (fun a => v a j)=μ.moment (fun a => v a j) := by
  let ξ : SparseIntegerLaw α := ⟨μ.length,μ.states,
    μ.law.compressAuto (fun i => v μ.states[i.val])⟩
  have hh := μ.law.compressAuto_correct (fun i => v μ.states[i.val])
  refine ⟨hh.2.1,?_,?_⟩
  · intro i
    refine ⟨ξ.law.support.orderEmbOfFin rfl i,?_⟩
    change (Vector.ofFn (fun k => μ.states[(ξ.law.support.orderEmbOfFin rfl k).val]))[i.val] = _
    simp only [Vector.getElem_ofFn]
    congr 2
  · intro j
    change ξ.trim.moment (fun a => v a j)=_
    rw [trim_moment]
    exact hh.2.2 j

theorem compressAuto_denominator {d : ℕ} (μ : SparseIntegerLaw α)
    (v : α → Fin d → ℚ) (L : ℕ)
    (hnum : ∀ i : Fin μ.length, ∀ j, |(v μ.states[i.val] j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i : Fin μ.length, ∀ j, ((v μ.states[i.val] j).den:ℤ) ≤ (2:ℤ)^L) :
    (μ.compressAuto v).law.denominator ≤ μ.law.denominator *
      (2:ℤ)^(((2*(d+1)*(d+1+L*(μ.length+1)))*(μ.length+1))*μ.length) :=
  (μ.law.compressAuto_spec (fun i => v μ.states[i.val]) L hnum hden).1

theorem step_property {d : ℕ} (v : α → Fin d → ℚ) (μ : SparseIntegerLaw α)
    (p : α → ℚ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (next : α → Fin 2 → α)
    (P : α → Prop) (hP : ∀ i : Fin μ.length, ∀ b, P (next μ.states[i.val] b)) :
    ∀ i : Fin (step v μ p hp next).length, P (step v μ p hp next).states[i.val] := by
  intro i
  obtain ⟨j,hj⟩ := ((μ.branch p hp next).compressAuto_correct v).2.1 i
  change P ((μ.branch p hp next).compressAuto v).states[i.val]
  rw [hj]
  change P ((Vector.ofFn (fun k => next
    μ.states[(finProdFinEquiv.symm k).1.val] (finProdFinEquiv.symm k).2))[j.val])
  simp only [Vector.getElem_ofFn]
  exact hP _ _

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseIterationHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MetricKMedian.SparseIntegerLaw
open Binary
variable {α : Type} {d : ℕ}

theorem step_denominator_height (μ : SparseIntegerLaw α) (v : α → Fin d → ℚ)
    (p : α → ℚ) (hp : ∀ a, 0≤p a ∧ p a≤1) (next : α → Fin 2 → α)
    (N P F : ℕ) (hN : μ.length≤N)
    (hP : ∀ i : Fin μ.length, HasHeight (p μ.states[i.val]) P)
    (hF : ∀ i : Fin μ.length, ∀ b j, HasHeight (v (next μ.states[i.val] b) j) F) :
    (μ.step v p hp next).law.denominator≤μ.law.denominator*(2:ℤ)^(stepHeight N d P F) := by
  have hf : ∀ i : Fin (μ.branch p hp next).length, ∀ j,
      HasHeight (v (μ.branch p hp next).states[i.val] j) F := by
    intro i j
    change HasHeight (v ((Vector.ofFn _)[i.val]) j) F
    simp only [Vector.getElem_ofFn]
    exact hF _ _ j
  have hc := (μ.branch p hp next).compressAuto_denominator v F
    (fun i j => (hf i j).1) (fun i j => (hf i j).2)
  have hb : (μ.branch p hp next).law.denominator≤μ.law.denominator*(2:ℤ)^(P*μ.length) :=
    IntegerBranching.branch_denominator μ.law (fun i => p μ.states[i.val]) (fun i => hp μ.states[i.val]) P (fun i => (hP i).2)
  apply hc.trans
  calc
    _ ≤ (μ.law.denominator*(2:ℤ)^(P*μ.length)) *
        (2:ℤ)^(((2*(d+1)*(d+1+F*((μ.branch p hp next).length+1)))*((μ.branch p hp next).length+1))*(μ.branch p hp next).length) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = μ.law.denominator*(2:ℤ)^(stepHeight μ.length d P F) := by
      simp only [branch,stepHeight,← mul_assoc,Nat.mul_comm 2 μ.length]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ μ.law.denominator_pos.le
      apply pow_le_pow_right₀ (by norm_num)
      unfold stepHeight
      gcongr

end MetricKMedian.SparseIntegerLaw
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram
open SparseIntegerLaw.BinarySparse (el ed)

def Input.start (x : Input) : State := ⟨⟨x,0⟩,.dirac (fun _ => false)⟩

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSignedPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPartial
open Finset RationalSignedStep
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features features_single features_pair)
variable {n : ℕ}

 theorem run_length (β : Fin n → ℚ) 
    (p : Vector ℚ n) (t : ℕ) : (run β p t).length ≤ n+n*n+1 := by
  cases t with
  | zero => change 1 ≤ _; omega
  | succ t => exact ((run β p t).branch (probability β)
      (probability_unit β) (endpoint β)).compressAuto_correct features |>.1

theorem run_invariants (β : Fin n → ℚ)
    (p : Vector ℚ n) (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (t : ℕ) :
    ∀ a : Fin (run β p t).length,
      let q := (run β p t).states[a.val]
      (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧
      (∑ i, β i*point q i)=∑ i, β i*point p i ∧
      ((fractional q).card ≤ n-t ∨ ¬Active β q) := by
  induction t with
  | zero =>
    intro a
    have he : (run β p 0).states[a.val]=p := SparseIntegerLaw.dirac_states p a
    dsimp only
    rw [he]
    refine ⟨hp,rfl,Or.inl ?_⟩
    have hh := card_le_card (filter_subset (fun i : Fin n => 0 < point p i ∧ point p i < 1) univ)
    simpa only [fractional,card_univ,Fintype.card_fin,Nat.sub_zero] using hh
  | succ t ih =>
    apply (run β p t).step_property features (probability β)
      (probability_unit β) (endpoint β)
      (fun q => (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧
        (∑ i, β i*point q i)=∑ i, β i*point p i ∧
        ((fractional q).card ≤ n-(t+1) ∨ ¬Active β q))
    intro a b
    obtain ⟨ha0,ha1,ha2⟩ := ih a
    refine ⟨endpoint_feasible β _ ha0 b,(endpoint_weighted β _ b).trans ha1,?_⟩
    by_cases h : Active β (run β p t).states[a.val]
    · have hh := endpoint_smaller β _ h b
      rcases ha2 with ha2 | ha2
      · exact Or.inl (by omega)
      · exact False.elim (ha2 h)
    · simp only [endpoint,dite_eq_right h]
      exact Or.inr h

end MetricKMedian.SparseSignedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedGridInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.SparseSignedPartial
open RationalSignedStep RationalGrid
open RationalWeightedStep (point)
variable {n : ℕ}

theorem run_grid (β : Fin n → ℚ) (p : Vector ℚ n)
    (D : ℤ) (hb : ∀ i, At D (β i)) (hp : ∀ i, At D (β i*point p i)) (t : ℕ) :
    ∀ a : Fin (run β p t).length, ∀ i, At D (β i*point (run β p t).states[a.val] i) := by
  induction t with
  | zero =>
    intro a
    have he : (run β p 0).states[a.val]=p := SparseIntegerLaw.dirac_states p a
    rw [he]
    exact hp
  | succ t ih =>
    apply (run β p t).step_property SparseWeightedPartial.features (probability β) (probability_unit β)
      (endpoint β) (fun q => ∀ i, At D (β i*point q i))
    intro a b
    exact endpoint_grid β D hb _ (ih a) b

theorem run_zero_weight (β : Fin n → ℚ) (p : Vector ℚ n) (t : ℕ) :
    ∀ a : Fin (run β p t).length, ∀ i, β i=0 → point (run β p t).states[a.val] i=point p i := by
  induction t with
  | zero =>
    intro a
    have he : (run β p 0).states[a.val]=p := SparseIntegerLaw.dirac_states p a
    rw [he]
    exact fun _ _ => rfl
  | succ t ih =>
    apply (run β p t).step_property SparseWeightedPartial.features (probability β) (probability_unit β)
      (endpoint β) (fun q => ∀ i, β i=0 → point q i=point p i)
    intro a b i hi
    exact (endpoint_zero_weight β _ b i hi).trans (ih a i hi)
end MetricKMedian.SparseSignedPartial
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingCoordinateHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section

namespace MetricKMedian.RoundingHeight
open RationalGrid RationalWeightedStep Binary
variable {n : ℕ}

theorem signed_run (β : Fin n → ℚ) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) (a : Fin (SparseSignedPartial.run β p t).length)
    (i : Fin n) : HasHeight (point (SparseSignedPartial.run β p t).states[a.val] i) (2*n*L+L) := by
  apply coordinate_height β p _ L hb hp
  · exact SparseSignedPartial.run_grid β p _ (initial_grid β p).1 (initial_grid β p).2 t a
  · exact SparseSignedPartial.run_zero_weight β p t a
  · exact (SparseSignedPartial.run_invariants β p hu t a).1

end MetricKMedian.RoundingHeight
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingRunHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.RoundingHeight
open RationalWeightedStep Binary
variable {n : ℕ}

theorem signed_endpoint (β : Fin n → ℚ) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) (a : Fin (SparseSignedPartial.run β p t).length)
    (b : Fin 2) (i : Fin n) :
    HasHeight (point (RationalSignedStep.endpoint β (SparseSignedPartial.run β p t).states[a.val] b) i) (2*n*L+L) := by
  apply coordinate_height β p _ L hb hp
  · exact RationalSignedStep.endpoint_grid β _ (initial_grid β p).1 _
      (SparseSignedPartial.run_grid β p _ (initial_grid β p).1 (initial_grid β p).2 t a) b
  · intro j hj
    exact (RationalSignedStep.endpoint_zero_weight β _ b j hj).trans
      (SparseSignedPartial.run_zero_weight β p t a j hj)
  · exact RationalSignedStep.endpoint_feasible β _ (SparseSignedPartial.run_invariants β p hu t a).1 b

end MetricKMedian.RoundingHeight
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_TaperListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Taper.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly Finset

@[fun_prop] theorem upper_poly : Poly upper := by
  unfold upper
  have h : Poly (fun ds : Row => ds.map (fun q => 1/q)) := by apply list_map <;> fun_prop
  fun_prop
@[fun_prop] theorem breaks_poly : Poly breaks := by
  unfold breaks
  have h : Poly (fun x : ℚ × Row => x.2.map (fun q => (1-x.1)/q)) := by apply list_map <;> fun_prop
  have h' : Poly (fun x : ℚ × Row => x.2.map (fun q => 1/q)) := by apply list_map <;> fun_prop
  fun_prop
@[fun_prop] theorem aSum_poly : Poly aSum := by
  unfold aSum
  apply comp rat_sum
  apply list_map
  · unfold aCoef; fun_prop
  · fun_prop
@[fun_prop] theorem bSum_poly : Poly bSum := by
  unfold bSum
  apply comp rat_sum
  apply list_map
  · unfold bCoef; fun_prop
  · fun_prop
@[fun_prop] theorem candidateList_poly : Poly candidateList := by
  unfold candidateList
  dsimp only
  apply comp (f:=fun x : Row × Row => x.1++x.2) (g:=fun x : Raw => (breaks (x.1.2,x.2), (breaks (x.1.2,x.2)).flatMap (fun a => (breaks (x.1.2,x.2)).map (fun b => (aSum ((x.1.2,x.2),(a+b)/2)-1/x.1.1)/bSum ((x.1.2,x.2),(a+b)/2))))) list_append
  apply pair
  · fun_prop
  · apply list_flatMap
    · apply list_map <;> fun_prop
    · fun_prop
@[fun_prop] theorem mass_poly : Poly mass := by
  unfold mass
  apply comp rat_sum
  apply list_map
  · unfold rationalMarginal; fun_prop
  · fun_prop
@[fun_prop] theorem roots_poly : Poly roots := by
  unfold roots
  apply list_filter <;> fun_prop
@[fun_prop] theorem radius_poly : Poly radius := by
  exact comp (f:=fun x : Row × ℚ => x.1.foldl max x.2) (g:=fun x : Raw => (roots x,0))
    (of_program LPBinary.Program.maxFold) (pair roots_poly (const 0))

end MetricKMedian.Taper.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_TaperAllProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Taper.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly Finset
abbrev AllRaw := (Raw × List Bool) × ℕ

def colocated (x : ℚ × Row) : ℚ := (x.2.map (fun q => if q=0 then x.1 else 0)).sum
def extras (x : (Row × List Bool) × ℕ) : List ℕ :=
  ((RoundingList.indices x.1.1).filter (fun i => decide (x.1.1[i]?.getD 0=0) && !(x.1.2[i]?.getD false))).take (x.2-(x.1.2.filter id).length)
def zeroRow (x : (Row × List Bool) × ℕ) : Row :=
  (RoundingList.indices x.1.1).map (fun i => if x.1.2[i]?.getD false || natMember (extras x,i) then 1 else 0)
def sourceRow (x : AllRaw) : Row :=
  if 1 ≤ colocated (x.1.1.1.1,x.1.1.2) then zeroRow ((x.1.1.2,x.1.2),x.2)
  else x.1.1.2.map (fun d => rationalMarginal x.1.1.1.2 d (radius x.1.1))

@[fun_prop] theorem colocated_poly : Poly colocated := by
  unfold colocated
  apply comp rat_sum
  apply list_map <;> fun_prop
@[fun_prop] theorem extras_poly : Poly extras := by
  unfold extras
  have hf : Poly (fun x : (Row × List Bool) × ℕ =>
      (RoundingList.indices x.1.1).filter (fun i => decide (x.1.1[i]?.getD 0=0) && !(x.1.2[i]?.getD false))) := by
    apply list_filter <;> fun_prop
  have hc : Poly (fun x : (Row × List Bool) × ℕ => x.1.2.filter id) := by
    apply list_filter <;> fun_prop
  exact comp (f:=fun x : List ℕ × ℕ => x.1.take x.2)
    (g:=fun x : (Row × List Bool) × ℕ => (((RoundingList.indices x.1.1).filter (fun i => decide (x.1.1[i]?.getD 0=0) && !(x.1.2[i]?.getD false))),x.2-(x.1.2.filter id).length))
    list_take (pair hf (by fun_prop))
@[fun_prop] theorem zeroRow_poly : Poly zeroRow := by
  unfold zeroRow
  apply list_map <;> fun_prop
@[fun_prop] theorem sourceRow_poly : Poly sourceRow := by
  unfold sourceRow
  have hm : Poly (fun x : AllRaw => x.1.1.2.map (fun d => rationalMarginal x.1.1.1.2 d (radius x.1.1))) := by
    apply list_map
    · unfold rationalMarginal; fun_prop
    · fun_prop
  fun_prop

end MetricKMedian.Taper.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseProductProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section

namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.Automatic Binary.Automatic.Poly
variable {α β A B : Type}

@[fun_prop] theorem prodData_poly [Coding A] [Coding B] [Inhabited A] [Inhabited B] :
    Poly (prodData (A:=A) (B:=B)) := by
  unfold prodData
  apply pair
  · apply pair
    · fun_prop
    · apply list_flatMap
      · apply list_map <;> fun_prop
      · fun_prop
  · apply list_flatMap
    · apply list_map <;> fun_prop
    · fun_prop
end MetricKMedian.SparseIntegerLaw.BinarySparse
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
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse
def rawQ (x : Raw) : List Unit × List Row :=
  (x.2.map (fun _ => ()),x.2.map (fun col => Taper.ListOperation.sourceRow (((x.1.1,col.1),col.2),x.1.2)))
end MetricKMedian.TaperGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBindProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.Automatic Binary.Automatic.Poly Finset

variable {α β A : Type}

@[fun_prop] theorem weights_poly : Poly weights := by
  unfold weights
  apply list_map <;> fun_prop

@[fun_prop] theorem jointWeights_poly [Coding A] [Inhabited A] : Poly (jointWeights (A:=A)) := by
  unfold jointWeights
  apply list_flatMap
  · apply list_map <;> fun_prop
  · fun_prop

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end


