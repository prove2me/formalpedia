-- Prove2me | Definitions.Def_OAIQ035K042
-- name    : OAIQ035K042
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:03:43.035062+00:00
-- url     : https://prove2.me/theorems/70e1be48-df30-4b84-8145-9b150a4241ba
-- title:
--   Definitions bundle OAIQ035K042 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 8 definitions, 1 instance and 16 theorems. The definitions and types are `OAI.MetricKMedian.Instance.facilityDistance`, `OAI.MetricKMedian.LPBinary.Repair.assignments`, `OAI.MetricKMedian.LPBinary.Repair.nearestRows`, `OAI.MetricKMedian.LPBinary.start`, `OAI.MetricKMedian.Preparation.FractionalRefinement.realization`, `OAI.MetricKMedian.Preparation.FractionalRefinement.unitInput`, `OAI.MetricKMedian.Preparation.RationalUnitInput.suppliers`, `OAI.MetricKMedian.RationalBatchData.ProposalProgram.Input.batch`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Geometry_IntegerBranching`, `KMedian_Geometry_RationalFractionalInput`, `KMedian_Geometry_RationalUnitScan`, `KMedian_Optimization_ApproximateLPSelection`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_IndexedInstanceLP`, `KMedian_Optimization_IntegralFractionalComparison`, `KMedian_Optimization_LPBinaryStart`, `KMedian_Optimization_ZeroCostBranch`, `KMedian_Process_BatchProposalProgram`, `KMedian_Programs_InstanceFractionalRound`, `KMedian_Sparse_SparseAlgorithm`, `KMedian_Sparse_SparseBind`, `KMedian_Sparse_SparseMarginalTools`, `KMedian_Sparse_SparseProduct`, `KMedian_Sparse_SparseSupport`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K029`, `OAIQ035K030`, `OAIQ035K032`, `OAIQ035K033` and `OAIQ035K034` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K048` and `OAIQ035K049`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K029
import Definitions.Def_OAIQ035K030
import Definitions.Def_OAIQ035K032
import Definitions.Def_OAIQ035K033
import Definitions.Def_OAIQ035K034

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_IntegerBranching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerBranching
open Finset
variable {n : ℕ}

theorem branch_moment (μ : IntegerLaw (Fin n)) (p : Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (f : Fin n → Fin 2 → ℚ) :
    (∑ a, (branch μ p hp).rational.weight a*f a.1 a.2)=
      ∑ i, μ.rational.weight i*(p i*f i 0+(1-p i)*f i 1) := by
  have hD : (RationalScaling.denominator p:ℚ) ≠ 0 := by
    exact_mod_cast (RationalScaling.denominator_pos p).ne'
  have hM : (μ.denominator:ℚ) ≠ 0 := by exact_mod_cast μ.denominator_pos.ne'
  simp only [IntegerLaw.rational,branch,Vector.getElem_ofFn,Fin.eta]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two,branchNumerator]
  norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
  simp only [Int.cast_mul,Int.cast_sub,RationalScaling.numerator_cast]
  apply sum_congr rfl
  intro i _
  field_simp

end MetricKMedian.IntegerBranching

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_IntegralFractionalComparison
attribute [-instance] _root_.OAI.MetricKMedian.TruncatedLP.instDecidableValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset ProjectedSubgradient
variable {n m : ℕ} [NeZero n] [NeZero m]

theorem approximation_integral (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hSk : S.card ≤ k)
    (a : Fin m → Fin n) (ha : ∀ j, a j ∈ S)
    (hc0 : 1/2 ≤ ∑ j, d j (a j)) (hc1 : (∑ j, d j (a j)) ≤ 1) :
    let out := approximation d r k hr hk hd
    (∀ i : Fin n, 0 ≤ out.opening[i.val] ∧ out.opening[i.val] ≤ 1) ∧
    (∀ (j : Fin m) (i : Fin n), 0 ≤ out.assignment[j.val][i.val] ∧
      out.assignment[j.val][i.val] ≤ out.opening[i.val]) ∧
    (∀ j : Fin m, ∑ i : Fin n, out.assignment[j.val][i.val]=1) ∧
    (∑ i : Fin n, out.opening[i.val]) ≤ (k:ℚ)+1 ∧
    (∑ j : Fin m, ∑ i : Fin n, out.assignment[j.val][i.val]*d j i) ≤
      (1+3/(r:ℚ))*(∑ j, d j (a j)) := by
  obtain ⟨z,hz,hzc⟩ := integral_comparison d k hd S hS hSk a ha hc1 (penalty r k)
  exact approximation_spec d r k hr hk hd _ hc0 hc1 z hz hzc

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ApproximateLPSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset
variable {n m : ℕ} [NeZero n] [NeZero m]

theorem candidate_success (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hSk : S.card ≤ k)
    (a : Fin m → Fin n) (ha : ∀ j, a j ∈ S)
    (hc : 0 < ∑ j, d j (a j)) :
    ∃ B ∈ feasibleScales d r k hr hk hd,
      (scaledCandidate d r k hr hk hd B).value d ≤ (1+3/(r:ℚ))*(∑ j, d j (a j)) := by
  obtain ⟨B,hBg,hB,hc0,hc1⟩ := Normalization.matrixGoodGuess d hd a hc
  have hh := approximation_integral (fun j i => d j i/B) r k hr hk
    (fun j i => div_nonneg (hd j i) hB.le) S hS hSk a ha
    (by simpa only [sum_div] using hc0) (by simpa only [sum_div] using hc1)
  have hv : (scaledCandidate d r k hr hk hd B).Valid k := by
    simp only [scaledCandidate,dite_eq_left hB,FractionalData.Valid]
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
  have hcand : (scaledCandidate d r k hr hk hd B).value (fun j i => d j i/B) ≤
      (1+3/(r:ℚ))*(∑ j, d j (a j)/B) := by
    simpa only [scaledCandidate,dite_eq_left hB,FractionalData.value] using hh.2.2.2.2
  refine ⟨B,mem_filter.mpr ⟨hBg,hv⟩,?_⟩
  rw [value_div,← sum_div,← mul_div_assoc] at hcand
  exact (div_le_div_iff_of_pos_right hB).mp hcand

theorem selectFractional_spec (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hSk : S.card ≤ k)
    (a : Fin m → Fin n) (ha : ∀ j, a j ∈ S)
    (hc : 0 < ∑ j, d j (a j)) :
    let out := selectFractional d r k hr hk hd
    out.Valid k ∧ out.value d ≤ (1+3/(r:ℚ))*(∑ j, d j (a j)) := by
  obtain ⟨B,hB,hBc⟩ := candidate_success d r k hr hk hd S hS hSk a ha hc
  obtain ⟨hmem,hmin⟩ := rationalArgmin_spec (feasibleScales d r k hr hk hd)
    (fun B => (scaledCandidate d r k hr hk hd B).value d) ⟨B,hB⟩
  exact ⟨(mem_filter.mp hmem).2,(hmin B hB).trans hBc⟩

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalFractionalInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Preparation
open Finset
variable {f j : ℕ}

namespace FractionalRefinement

variable (a : TruncatedLP.FractionalData f j) (k : ℕ) (ha : a.Valid k) (hj : 0<j)

 theorem x_spec (dc : Fin j → Fin f → ℚ) :
    (∀ c i, 0≤x a k ha hj dc c i ∧ x a k ha hj dc c i≤y a i) ∧
    (∀ c, ∑ i, x a k ha hj dc c i=1) ∧
    (∀ c b b', 0<x a k ha hj dc c b → x a k ha hj dc c b'<y a b' → dc c b≤dc c b') ∧
    (∑ c, ∑ i, x a k ha hj dc c i*dc c i)≤a.value dc := by
  have hs := fun c => computedNearest_spec (y a) (dc c) (fun b => (ha.1 b).1) (mass_one a k ha hj) 0
  refine ⟨fun c => (hs c).1,fun c => (hs c).2.1,?_,?_⟩
  · intro c b b' hb hb'
    exact computedNearest_ordered (y a) (dc c) (fun b => (ha.1 b).1) (mass_one a k ha hj) b b' hb hb'
  · apply sum_le_sum
    intro c _
    change (∑ i : Fin f, (computedNearest (y a) (dc c) _ _)[i.val]*dc c i)≤_
    rw [(hs c).2.2]
    exact FractionalDual.value_le_assignment (dc c) (y a) (fun i => a.assignment[c.val][i.val]) 0
      (ha.2.1 c) (ha.2.2.1 c)

def unitInput (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hdc : ∀ c i, 0≤dc c i) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c) :
    RationalUnitInput (count a k ha hj dc) j :=
  let hs := x_spec a k ha hj dc
  RationalSplitting.input (y a) (x a k ha hj dc) dc dd df (fun i => (ha.1 i).1) (fun i => (ha.1 i).2)
    (fun c i => (hs.1 c i).1) (fun c i => (hs.1 c i).2) hs.2.1 hdc hdd hds hs.2.2.1

 def realization {X : Type} [PseudoMetricSpace X]
    (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hdc : ∀ c i, 0≤dc c i) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c)
    (i : Fin f → X) (c : Fin j → X)
    (hdf : ∀ b b', dist (i b) (i b')=(df b b':ℝ))
    (hc : ∀ c' b, dist (c c') (i b)=(dc c' b:ℝ))
    (hcc : ∀ c' c'', dist (c c') (c c'')=(dd c' c'':ℝ)) :
    (unitInput a k ha hj dc dd df hdc hdd hds).Realization X where
  i := fun b => i (original a k ha hj dc b)
  c := c
  hdf := fun first second => hdf (original a k ha hj dc first) (original a k ha hj dc second)
  hdc := fun client piece => hc client (original a k ha hj dc piece)
  hdd := hcc

end FractionalRefinement
end MetricKMedian.Preparation
end

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

theorem branch_moment (μ : SparseIntegerLaw α) (p : α → ℚ)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (next : α → Fin 2 → α) (f : α → ℚ) :
    (μ.branch p hp next).moment f=
      μ.moment (fun a => p a*f (next a 0)+(1-p a)*f (next a 1)) := by
  let ρ := IntegerBranching.branch μ.law (fun i => p μ.states[i.val])
    (fun i => hp μ.states[i.val])
  have h := ρ.reindex_moment finProdFinEquiv
    (fun a => f (next μ.states[a.1.val] a.2))
  have h' := IntegerBranching.branch_moment μ.law (fun i => p μ.states[i.val])
    (fun i => hp μ.states[i.val]) (fun i b => f (next μ.states[i.val] b))
  unfold moment branch
  simp only [Vector.getElem_ofFn]
  convert h.trans h' using 1
  all_goals try with_reducible_and_instances rfl

end MetricKMedian.SparseIntegerLaw

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

 theorem dirac_moment (a : α) (f : α → ℚ) : (dirac a).moment f=f a := by
  change (∑ _i : Fin 1, ((1:ℤ):ℚ)/1*f a)=f a
  simp

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBind
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.RationalLaw
open Finset
variable {α : Type} {β : α → Type} [Fintype α] [∀ a, Fintype (β a)]

theorem sigma_moment (μ : RationalLaw α) (κ : ∀ a, RationalLaw (β a)) (f : Sigma β → ℚ) :
    (∑ z, (μ.sigma κ).weight z*f z)=
      ∑ a, μ.weight a*∑ b, (κ a).weight b*f ⟨a,b⟩ := by
  rw [Fintype.sum_sigma]
  simp only [sigma,mul_sum,mul_assoc]

end MetricKMedian.RationalLaw
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem bindIndexed_moment (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (f : β → ℚ) :
    (μ.bindIndexed κ).moment f=∑ a, μ.law.rational.weight a*(κ a).moment f := by
  let ρ := μ.law.rational.sigma (fun a => (κ a).law.rational)
  have h := ρ.integer.reindex_moment finSigmaFinEquiv
    (fun z => f (κ z.1).states[z.2.val])
  have h' := μ.law.rational.sigma_moment (fun a => (κ a).law.rational)
    (fun z => f (κ z.1).states[z.2.val])
  simp only [RationalLaw.integer_weight] at h
  unfold moment bindIndexed
  simp only [Vector.getElem_ofFn]
  convert h.trans h' using 1
  all_goals try with_reducible_and_instances rfl

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.IntegerLaw
open Finset
variable {α β : Type} [Fintype α] [Fintype β]

theorem prod_moment (μ : IntegerLaw α) (ν : IntegerLaw β) (f : α → β → ℚ) :
    (∑ ab, (μ.prod ν).rational.weight ab*f ab.1 ab.2)=
      ∑ a, μ.rational.weight a*(∑ b, ν.rational.weight b*f a b) := by
  rw [Fintype.sum_prod_type]
  simp only [prod_weight,mul_sum,mul_assoc]

end MetricKMedian.IntegerLaw
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β γ : Type}

theorem prod_moment (μ : SparseIntegerLaw α) (ν : SparseIntegerLaw β)
    (f : α → β → γ) (v : γ → ℚ) :
    (μ.prod ν f).moment v=μ.moment (fun a => ν.moment (fun b => v (f a b))) := by
  have h := (μ.law.prod ν.law).reindex_moment (finProdFinEquiv (m := μ.length) (n := ν.length))
    (fun a => v (f μ.states[a.1.val] ν.states[a.2.val]))
  have h' := μ.law.prod_moment ν.law (fun a b => v (f μ.states[a.val] ν.states[b.val]))
  unfold moment prod
  simp only [Vector.getElem_ofFn]
  convert h.trans h' using 1
  all_goals try with_reducible_and_instances rfl

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem trim_positive (μ : SparseIntegerLaw α) (a : Fin μ.trim.length) :
    0 < μ.trim.law.rational.weight a := by
  change Fin μ.law.support.card at a
  change 0 < μ.law.trim.rational.weight a
  rw [IntegerLaw.trim_weight]
  unfold IntegerLaw.rational
  apply div_pos
  · have hh := (μ.law.mem_support _).mp (orderEmbOfFin_mem μ.law.support rfl a)
    exact_mod_cast lt_of_le_of_ne (μ.law.numerator_nonneg _) (Ne.symm hh)
  · exact_mod_cast μ.law.denominator_pos

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalUnitScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Preparation.RationalUnitInput
open Finset
variable {f j : ℕ} {X : Type} [PseudoMetricSpace X]
variable (U : RationalUnitInput f j) (R : U.Realization X) {η τ : ℝ} (p : RationalAllParameters η τ)

def suppliers : RationalSuppliers.Data f (U.representatives p.M).card :=
  RationalBundles.suppliers (fun t => U.F (U.ridx p.M t)) U.y
    (fun t => R.c (U.ridx p.M t)) R.i
    (fun t u => U.dd (U.ridx p.M t) (U.ridx p.M u))
    (fun t a => U.dc (U.ridx p.M t) a) (fun t => U.V (U.ridx p.M t)) p.M p.δ p.γ
    (fun t u => R.hdd (U.ridx p.M t) (U.ridx p.M u))
    (fun t a => R.hdc (U.ridx p.M t) a) U.hy p.hM p.hδ (by linarith only [p.hδ1])
    p.hθ p.hγ p.hγ1 (fun t => U.hu (U.ridx p.M t)) (fun _ => rfl)
    (U.representative_separation p.M p.hM.le)

end MetricKMedian.Preparation.RationalUnitInput
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPBinaryStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function
def start (r : ℕ) (I : Input) : State := (rawContext r I.raw,rawInitial I.raw)
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ApproximationListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Repair
def assignments (ds xs : Rows) : Rows := (ds.zip xs).map (fun p => assignment p.1 p.2)
def nearestRows (ds : Rows) (ys : Row) : Rows := ds.map (Nearest.filling ys)
end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_IndexedInstanceLP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset
namespace Instance

theorem computedFractional_spec (I : Instance) (r : ℕ) (hr : 0 < r)
    (hJ : I.clients.Nonempty) (S : Finset (Fin I.n))
    (hSF : S ⊆ I.facilities) (hS : S.Nonempty) (hSk : S.card ≤ I.k)
    (hc : 0 < rationalCost I S) :
    let out := I.computedFractional r hr hJ
    out.Valid I.k ∧ out.value I.indexedDistance ≤ (1+3/(r:ℚ))*rationalCost I S := by
  let : NeZero I.facilities.card := ⟨(card_pos.mpr I.facilities_nonempty).ne'⟩
  let : NeZero I.clients.card := ⟨(card_pos.mpr hJ).ne'⟩
  obtain ⟨T,hT,hTc,a,ha,hac⟩ := I.indexed_integral S hSF hS
  have hh := TruncatedLP.selectFractional_spec I.indexedDistance r I.k hr I.k_pos
    I.indexedDistance_nonneg T hT (by rwa [hTc]) a ha (by rwa [hac])
  rwa [hac] at hh

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ZeroCostBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset
namespace Instance

instance instDecidableZeroTest (I : Instance) : Decidable I.zeroTest := by unfold zeroTest; infer_instance

theorem zeroTest_iff (I : Instance) : I.zeroTest ↔ optimum I=0 :=
  I.optimum_eq_zero_iff.symm

theorem nonzero_clients (I : Instance) (h : ¬I.zeroTest) : I.clients.Nonempty := by
  by_contra hn
  apply h
  have hj : I.clients=∅ := not_nonempty_iff_eq_empty.mp hn
  simp only [zeroTest,hj,empty_subset,card_empty,Nat.zero_le,and_self]

theorem nonzero_optimum (I : Instance) (h : ¬I.zeroTest) : 0 < optimum I :=
  lt_of_le_of_ne I.optimum_nonneg (fun he => h (I.zeroTest_iff.mpr he.symm))

end Instance
end MetricKMedian
end
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
open Finset FixedBatch Binary Binary.PolyProgram
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
variable {C : Type} (I : C → Type) [∀ c, LinearOrder (I c)] [∀ c, Fintype (I c)]

variable {I}

def Input.batch (x : Input I) : SparsePhysicalBatch.Program.Input where
  n := Fintype.card (HeavyAction (graph x.G) (heavySet (graphMass x.G x.g) x.b))
  Z := (balanced (heavy (graph x.G) (heavySet (graphMass x.G x.g) x.b)) x.Δ).map x.enumActions.symm.toEmbedding
  C := fun i => (conflicts (heavy (graph x.G) (heavySet (graphMass x.G x.g) x.b)) x.Δ (x.enumActions i)).map x.enumActions.symm.toEmbedding
  p := x.p
  q := fun i => bias (graphMass x.G x.g) x.p x.φ (heavyParent (graph x.G) _ (x.enumActions i))
  hp := ⟨x.hp,by have h := mul_nonneg x.hp x.hφ; nlinarith only [h,x.hupper]⟩
  hq := fun _ => bias_probability (graphMass x.G x.g) x.hp x.hφ x.hupper _
end MetricKMedian.RationalBatchData.ProposalProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_InstanceFractionalRound
attribute [-instance] _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Instance
open Finset Preparation

 def facilityDistance (I : Instance) (b b' : Fin I.facilities.card) : ℚ :=
  I.distance (I.facilities.orderEmbOfFin rfl b) (I.facilities.orderEmbOfFin rfl b')

end MetricKMedian.Instance
end

end OAI
end


