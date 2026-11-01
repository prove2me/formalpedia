-- Prove2me | Definitions.Def_OAIQ053K041
-- name    : OAIQ053K041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:04:11.495514+00:00
-- url     : https://prove2.me/theorems/fe5885fd-0767-4246-a4b2-a59d4f3a26b8
-- title:
--   Definitions bundle OAIQ053K041 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 50 declarations of OpenAI's Lean: 27 definitions, 1 instance and 22 theorems. The definitions and types are `OAI.MetricKMedian.Instance.clientDistance`, `OAI.MetricKMedian.Instance.computedFractional`, `OAI.MetricKMedian.Instance.facilityDistance`, `OAI.MetricKMedian.Instance.zeroOutput`, `OAI.MetricKMedian.Instance.zeroTest`, `OAI.MetricKMedian.InstanceProgram.Nonzero`, `OAI.MetricKMedian.InstanceProgram.lpInput`, `OAI.MetricKMedian.LPBinary.Program.edual`, `OAI.MetricKMedian.LPBinary.Program.enext`, `OAI.MetricKMedian.LPBinary.Program.epoint`, `OAI.MetricKMedian.LPBinary.Program.ethreshold`, `OAI.MetricKMedian.LPBinary.Program.etrunc`, `OAI.MetricKMedian.LPBinary.Repair.eo`, `OAI.MetricKMedian.LPBinary.ec`, `OAI.MetricKMedian.LPBinary.ei`, `OAI.MetricKMedian.LPBinary.ers`, `OAI.MetricKMedian.LPBinary.es`, `OAI.MetricKMedian.SparseGraph.Program.State.product`, `OAI.MetricKMedian.SparseGraph.Program.column`, `OAI.MetricKMedian.SparseGraph.Program.columnsProgram`, `OAI.MetricKMedian.SparseGraph.Program.update`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.Bundle.branch`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.Bundle.compressionInput`, `OAI.MetricKMedian.TruncatedLP.approximation`, `OAI.MetricKMedian.TruncatedLP.feasibleScales`, `OAI.MetricKMedian.TruncatedLP.scaledCandidate`, `OAI.MetricKMedian.TruncatedLP.selectFractional`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Compression_RationalKernelHeightSupport`, `KMedian_Instance`, `KMedian_Optimization_ApproximateFractional`, `KMedian_Optimization_ApproximateLPSelection`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_DualListCompiler`, `KMedian_Optimization_IndexedInstanceLP`, `KMedian_Optimization_LPBinaryStart`, `KMedian_Optimization_LPListFacts`, `KMedian_Optimization_SimplexListProgram`, `KMedian_Optimization_TruncatedListCompiler`, `KMedian_Optimization_ZeroCostBranch`, `KMedian_Probability_BernoulliRunProgram`, `KMedian_Process_RoundingStateCompiler`, `KMedian_Programs_DependentSparseProgram`, `KMedian_Programs_GraphLawProgram`, `KMedian_Programs_GraphStepProgram`, `KMedian_Programs_InstanceDataProgram`, `KMedian_Programs_InstanceFractionalRound`, `KMedian_Programs_ScaleListProgram`, `KMedian_Sparse_SparseBindProgram`, `KMedian_Sparse_SparseListTrim`, `KMedian_Sparse_SparseProduct`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K029`, `OAIQ053K030`, `OAIQ053K031`, `OAIQ053K032`, `OAIQ053K033` and `OAIQ053K034` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K046` and `OAIQ053K047`; the proofs of `OAI.MetricKMedian.Reduction.reductionOutputs_success_s53` and `OAI.MetricKMedian.threshold`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K029
import Definitions.Def_OAIQ053K030
import Definitions.Def_OAIQ053K031
import Definitions.Def_OAIQ053K032
import Definitions.Def_OAIQ053K033
import Definitions.Def_OAIQ053K034

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_RationalKernelHeightSupport
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                   
section
namespace MetricKMedian.Gaussian
open Finset

theorem rational_input_kernel_bounds (r n L : ℕ) (A : Fin r → Fin n → ℚ)
    (hn : r < n) (hnum : ∀ i j, |(A i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((A i j).den:ℤ) ≤ (2:ℤ)^L) :
    let z := kernel r n A
    ∀ j, |(z j).num| ≤ (2:ℤ)^(2*r*(r+L*(n+1))) ∧
      ((z j).den:ℤ) ≤ (2:ℤ)^(2*r*(r+L*(n+1))) := by
  dsimp only
  let V : Fin r → Fin n → ℤ := fun i => RationalScaling.numerator (A i)
  let D : Fin r → ℚ := fun i => RationalScaling.denominator (A i)
  have hD : ∀ i, D i ≠ 0 := by
    intro i
    apply ne_of_gt
    dsimp only [D]
    exact_mod_cast RationalScaling.denominator_pos (A i)
  have hV : ∀ i j, (V i j:ℚ)=A i j*D i := fun i j =>
    RationalScaling.numerator_cast (A i) j
  have hVb : ∀ i j, |V i j| ≤ (2:ℤ)^(L*(n+1)) := by
    intro i j
    simpa only [Fintype.card_fin] using
      RationalScaling.numerator_bound (A i) L (hnum i) (hden i) j
  have hki : ∀ z : Fin n → ℚ,
      (∀ i, ∑ j, (V i j:ℚ)*z j=0) ↔ (∀ i, ∑ j, A i j*z j=0) := by
    intro z
    simp only [hV]
    exact row_scaling_kernel_iff A D hD z
  obtain ⟨⟨w,hw⟩,hc⟩ := kernel_circuit r n A hn
  have hk := (kernel_spec r n A hn).2
  have hcV : IsCircuit (fun i j => (V i j:ℚ)) (kernel r n A) := by
    intro v hv hkV
    exact hc v hv ((hki v).mp hkV)
  obtain ⟨U,hUw,hU,hz⟩ := circuit_integer_ratio V _ (L*(n+1)) hVb
    ((hki _).mpr hk) hcV w hw
  intro j
  rw [hz j]
  exact ratio_num_den_bound (U j) (U w) hUw _ (hU j) (hU w)

end MetricKMedian.Gaussian
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Instance
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.Input.distance_client_facility _root_.OAI.MetricKMedian.Instance.restrict_cost
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

theorem optimum_nonneg (I : Instance) : 0 ≤ optimum I := by
  obtain ⟨S,_,_,_,he⟩ := I.optimum_attained
  rw [← he]
  exact I.cost_nonneg S

theorem optimum_le (I : Instance) {S : Finset (Fin I.n)}
    (hS : S ⊆ I.facilities) (hne : S.Nonempty) (hk : S.card ≤ I.k) : optimum I ≤ cost I S := by
  rw [optimum,dite_eq_left I.feasible_nonempty]
  exact min'_le _ _ (mem_image_of_mem _ ((I.mem_feasible S).mpr ⟨hS,hne,hk⟩))

theorem optimum_eq_zero_iff (I : Instance) :
    optimum I=0 ↔ I.clients ⊆ I.facilities ∧ I.clients.card ≤ I.k := by
  constructor
  · intro hz
    obtain ⟨S,hSF,hne,hSk,hcost⟩ := I.optimum_attained
    have hJS := (I.cost_eq_zero_iff S hne).mp (hcost.trans hz)
    exact ⟨hJS.trans hSF,(card_le_card hJS).trans hSk⟩
  · rintro ⟨hJF,hJk⟩
    by_cases hJ : I.clients.Nonempty
    · apply le_antisymm _ I.optimum_nonneg
      exact (I.optimum_le hJF hJ hJk).trans_eq ((I.cost_eq_zero_iff I.clients hJ).mpr Subset.rfl)
    · have he := not_nonempty_iff_eq_empty.mp hJ
      obtain ⟨S,hSF,hne,hSk,_⟩ := I.optimum_attained
      apply le_antisymm _ I.optimum_nonneg
      exact (I.optimum_le hSF hne hSk).trans_eq (by simp [cost,he])

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximateFractional
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.TruncatedLP.instDecidableValid
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

def approximation (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i) : FractionalData n m :=
  let H := penalty r k
  let y := point (optimize d r k H hr hk (penalty_pos r k hr))
  have hy : feasible (k:ℚ) y := (optimize_spec d r k H hr hk (penalty_pos r k hr) hd
    (point (initial (k:ℚ))) (initial_feasible _ (by positivity))).1
  have hym : 1 ≤ ∑ i, y i := by rw [hy.2]; exact_mod_cast hk
  let x := fun j => point (Preparation.computedNearest y (truncated d H j) hy.1 hym)
  ⟨Vector.ofFn (repairedOpening y (loss r k)),
    Vector.ofFn (fun j => Vector.ofFn (repairedAssignment d x j))⟩

theorem approximation_spec (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i)
    (s : ℚ) (hs : 1/2 ≤ s) (hs1 : s ≤ 1)
    (z : Fin n → ℚ) (hz : feasible (k:ℚ) z)
    (hzc : objective d z (penalty r k) ≤ s) :
    let a := approximation d r k hr hk hd
    (∀ i : Fin n, 0 ≤ a.opening[i.val] ∧ a.opening[i.val] ≤ 1) ∧
    (∀ (j : Fin m) (i : Fin n), 0 ≤ a.assignment[j.val][i.val] ∧
      a.assignment[j.val][i.val] ≤ a.opening[i.val]) ∧
    (∀ j : Fin m, ∑ i : Fin n, a.assignment[j.val][i.val]=1) ∧
    (∑ i : Fin n, a.opening[i.val]) ≤ (k:ℚ)+1 ∧
    (∑ j : Fin m, ∑ i : Fin n, a.assignment[j.val][i.val]*d j i) ≤ (1+3/(r:ℚ))*s := by
  let H := penalty r k
  let y := point (optimize d r k H hr hk (penalty_pos r k hr))
  have hyc := optimize_spec d r k H hr hk (penalty_pos r k hr) hd z hz
  have hy : feasible (k:ℚ) y := hyc.1
  have hym : 1 ≤ ∑ i, y i := by rw [hy.2]; exact_mod_cast hk
  let x := fun j => point (Preparation.computedNearest y (truncated d H j) hy.1 hym)
  have hx := fun j => Preparation.computedNearest_spec y (truncated d H j) hy.1 hym H
  have hxe : (∑ j, ∑ i, x j i*truncated d H j i)=objective d y H := by
    exact sum_congr rfl (fun j _ => (hx j).2.2)
  have hc : (∑ j, ∑ i, x j i*truncated d H j i) ≤ s+1/(r:ℚ) := by
    rw [hxe]
    exact hyc.2.trans (by dsimp [H] at *; linarith)
  have hcost : (∑ j, ∑ i, x j i*truncated d H j i) ≤ loss r k*(H:ℚ) := by
    have he : loss r k*(H:ℚ)=1+1/(r:ℚ) := by
      unfold loss
      exact div_mul_cancel₀ _ (by exact_mod_cast (penalty_pos r k hr).ne')
    rw [he]
    exact hc.trans (by linarith)
  obtain ⟨_,_,hρ,hkρ⟩ := loss_bounds r k hr hk
  obtain ⟨h1,h2,h3,h4,h5⟩ := repaired_spec d x y H (loss r k) k
    (penalty_one r k hr) hρ hkρ hd hy.1 (fun j => (hx j).1)
    (fun j => (hx j).2.1) hy.2.le hcost
  have hfinal := h5.trans ((div_le_div_of_nonneg_right hc (sub_pos.mpr hρ).le).trans
    (repair_error r k hr hk s hs))
  simpa only [approximation,Vector.getElem_ofFn] using And.intro h1 (And.intro h2
    (And.intro h3 (And.intro h4 hfinal)))

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximateLPSelection
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

def scaledCandidate (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i) (B : ℚ) : FractionalData n m :=
  if hB : 0 < B then
    approximation (fun j i => d j i/B) r k hr hk (fun j i => div_nonneg (hd j i) hB.le)
  else ⟨Vector.replicate n 0,Vector.replicate m (Vector.replicate n 0)⟩

def feasibleScales (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i) : Finset ℚ :=
  (Normalization.matrixGuesses d).filter
    (fun B => (scaledCandidate d r k hr hk hd B).Valid k)

def selectFractional (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i) : FractionalData n m :=
  scaledCandidate d r k hr hk hd
    (rationalArgmin (feasibleScales d r k hr hk hd)
      (fun B => (scaledCandidate d r k hr hk hd B).value d))

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPListFacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.LPBinary
open Finset
abbrev ers := Binary.encodeList er

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_SimplexListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

namespace Program
open Binary Binary.PolyProgram
abbrev ethreshold := encodePair (encodePair er Ratio.encode) Ratio.encode
end Program
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_DualListCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.LPBinary.Program
open Binary Binary.PolyProgram Function
abbrev epoint := encodePair er er
abbrev edual := encodePair epoint Ratio.encode

end MetricKMedian.LPBinary.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_TruncatedListCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.LPBinary.Program
open Binary Binary.PolyProgram Function
abbrev etrunc := encodePair (encodePair ers er) Ratio.encode
abbrev enext := encodePair etrunc (encodePair Ratio.encode Ratio.encode)

end MetricKMedian.LPBinary.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPBinaryStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function
abbrev ec := encodePair ers (encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode))
abbrev es := encodePair ec er
abbrev ei := encodePair ers Nat.bits

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximationListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Repair
abbrev eo := encodePair er ers

end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_IndexedInstanceLP
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

def computedFractional (I : Instance) (r : ℕ) (hr : 0 < r)
    (hJ : I.clients.Nonempty) : TruncatedLP.FractionalData I.facilities.card I.clients.card :=
  letI : NeZero I.facilities.card := ⟨(card_pos.mpr I.facilities_nonempty).ne'⟩
  letI : NeZero I.clients.card := ⟨(card_pos.mpr hJ).ne'⟩
  TruncatedLP.selectFractional I.indexedDistance r I.k hr I.k_pos I.indexedDistance_nonneg

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ZeroCostBranch
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

def zeroTest (I : Instance) : Prop := I.clients ⊆ I.facilities ∧ I.clients.card ≤ I.k

instance instDecidableZeroTest (I : Instance) : Decidable I.zeroTest := by unfold zeroTest; infer_instance

def zeroOutput (I : Instance) : Finset (Fin I.n) :=
  if I.clients.Nonempty then I.clients else {I.facilities.min' I.facilities_nonempty}

theorem zeroOutput_spec (I : Instance) (h : I.zeroTest) :
    I.zeroOutput ⊆ I.facilities ∧ I.zeroOutput.Nonempty ∧ I.zeroOutput.card ≤ I.k ∧
      cost I I.zeroOutput=0 := by
  by_cases hJ : I.clients.Nonempty
  · simp only [zeroOutput,ite_eq_left hJ]
    exact ⟨h.1,hJ,h.2,(I.cost_eq_zero_iff I.clients hJ).mpr Subset.rfl⟩
  · simp only [zeroOutput,ite_eq_right hJ]
    refine ⟨singleton_subset_iff.mpr (min'_mem _ _),singleton_nonempty _,?_,?_⟩
    · simpa only [card_singleton] using I.k_pos
    · have hj : I.clients=∅ := not_nonempty_iff_eq_empty.mp hJ
      simp only [cost,hj,sum_empty]

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
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseListTrim
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function Finset
variable {α : Type}

theorem activeEntries_raw (μ : SparseIntegerLaw α) : activeEntries (raw μ)=
    List.ofFn (fun j : Fin μ.law.support.card => let i := μ.law.support.orderEmbOfFin rfl j;
      (μ.law.numerator i,μ.states[i.val])) := by
  rw [activeEntries,raw,states_list,Gaussian.ListOperation.zip_ofFn,List.ofFn_eq_map,List.filter_map]
  exact EncodingLists.map_filter_enum _ (fun i => μ.law.numerator i≠0)

theorem trimData_raw (μ : SparseIntegerLaw α) : trimData (raw μ)=raw μ.trim := by
  unfold trimData
  rw [activeEntries_raw]
  simp only [raw,trim,Vector.toList_ofFn,List.map_ofFn,Function.comp_def,IntegerLaw.trim_denominator]
  congr 2
  exact congrArg List.ofFn (funext (IntegerLaw.trim_numerator μ.law)).symm

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingStateCompiler
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse

theorem trim_encode_raw {n : ℕ} (μ : SparseIntegerLaw (Vector ℚ n)) :
    trimData ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map Vector.toList)=
      (((μ.trim).law.denominator,List.ofFn (μ.trim).law.numerator),μ.trim.states.toList.map Vector.toList) := by
  change trimData ((raw μ).1,(raw μ).2.map Vector.toList)=_
  rw [trimData_map,trimData_raw]
  rfl

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_DependentSparseProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.SparseIntegerLaw.DependentProgram
open Binary Binary.PolyProgram Function BinarySparse
variable {C A : Type} (T : C → Type)

variable {T} (ec : C → List Bool) (ea : A → List Bool) (view : ∀ c, T c → A)

def Bundle.branch (p : ∀ c, T c → ℚ) (hp : ∀ c a, 0 ≤ p c a ∧ p c a ≤ 1)
    (next : ∀ c, T c → Fin 2 → T c) (x : Bundle T) : Bundle T :=
  ⟨x.ctx,x.law.branch (p x.ctx) (hp x.ctx) (next x.ctx)⟩
def Bundle.compressionInput (d : C → ℕ) (v : ∀ c, T c → Fin (d c) → ℚ) (x : Bundle T) :
    IntegerLaw.BinaryCompression.RationalInput :=
  ⟨x.law.length,d x.ctx,x.law.law,fun i => v x.ctx x.law.states[i.val]⟩

 theorem trim_view (c : C) (μ : SparseIntegerLaw (T c)) :
    trimData ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map (view c))=
      (((μ.trim).law.denominator,List.ofFn (μ.trim).law.numerator),μ.trim.states.toList.map (view c)) := by
  change trimData ((raw μ).1,(raw μ).2.map (view c))=_
  rw [RoundingProgram.trimData_map,trimData_raw]
  rfl

 theorem raw_branch (p : ∀ c, T c → ℚ) (hp : ∀ c a, 0 ≤ p c a ∧ p c a ≤ 1)
    (next : ∀ c, T c → Fin 2 → T c)
    (P : C × A → ℚ) (E0 E1 : C × A → A)
    (hP : ∀ c a, P (c,view c a)=p c a)
    (hE0 : ∀ c a, E0 (c,view c a)=view c (next c a 0))
    (hE1 : ∀ c a, E1 (c,view c a)=view c (next c a 1)) (x : Bundle T) :
    (x.ctx,(branchLawData ((x.raw view).2.1,(x.raw view).2.2.map (fun a => P (x.ctx,a))),
      (x.raw view).2.2.flatMap (fun a => [E0 (x.ctx,a),E1 (x.ctx,a)])))=
       (x.branch p hp next).raw view := by
  simp only [Bundle.raw,Bundle.branch,states_list,List.map_ofFn,Function.comp_def,hP]
  rw [branchLaw_ofFn x.law.law _ (fun i => hp x.ctx x.law.states[i.val])]
  congr 2
  simp only [SparseIntegerLaw.branch,Vector.getElem_ofFn,List.flatMap_def,List.map_ofFn,
    Function.comp_def,hE0,hE1]
  exact (two_expand (fun i b => view x.ctx (next x.ctx x.law.states[i.val] b))).symm

end MetricKMedian.SparseIntegerLaw.DependentProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram

 theorem input_bounds (x : Input) : x.n ≤ x.encode.length ∧ ∀ i, HasHeight (x.p i) x.encode.length := by
  refine ⟨?_,?_⟩
  · simpa only [List.length_ofFn] using (EncodedList.length_le Ratio.encode (List.ofFn x.p))
  · intro i
    exact (Ratio.height_length _).mono (EncodedList.member_length _ _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩))

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseProduct
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
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
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphStepProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table er et)

def column (c : Context) : SparseIntegerLaw (Finset (Fin c.input.n)) :=
  if h : c.t < c.input.m then c.input.columns ⟨c.t,h⟩ else .dirac ∅
def update (c : Context) (G : T c) (S : Finset (Fin c.input.n)) : T c :=
  fun i => if i.val=c.t then S else G i

def State.product (x : State) : State := ⟨x.ctx,x.law.prod (column x.ctx) (update x.ctx)⟩
end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseIntegerLaw.DependentProgram

noncomputable def columnsProgram : PolyProgram QInput.encode (encodeList SparseBernoulli.Program.Input.encode) QInput.columns :=
  (snd (encodeList (fun _ : Unit => [])) qt).recode QInput.raw (fun _ => rfl) (fun x => by
    change qt (List.ofFn (fun i => List.ofFn (x.column i).p))=
      encodeList SparseBernoulli.Program.Input.encode (List.ofFn x.column)
    rw [show List.ofFn (fun i => List.ofFn (x.column i).p)=
      (List.ofFn x.column).map (fun c => List.ofFn c.p) by rw [List.map_ofFn]; rfl]
    exact RoundingProgram.encodeList_map qr (fun c : SparseBernoulli.Program.Input => List.ofFn c.p) _)

end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_ScaleListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Input

theorem scale_rows (I : Input) (B : ℚ) :
    (I.scale B).rows=I.rows.map (fun ds => ds.map (fun d => d/B)) := by
  simp only [rows,scale,List.map_ofFn,Function.comp_def]

end Input
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceFractionalRound
attribute [-instance] _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Instance
open Finset Preparation

 def clientDistance (I : Instance) (c c' : Fin I.clients.card) : ℚ :=
  I.distance (I.clients.orderEmbOfFin rfl c) (I.clients.orderEmbOfFin rfl c')

 def facilityDistance (I : Instance) (b b' : Fin I.facilities.card) : ℚ :=
  I.distance (I.facilities.orderEmbOfFin rfl b) (I.facilities.orderEmbOfFin rfl b')

 theorem clientDistance_self (I : Instance) (c : Fin I.clients.card) : I.clientDistance c c=0 :=
  (I.distance_eq_zero _ _).mpr rfl

 theorem clientDistance_comm (I : Instance) (c c' : Fin I.clients.card) :
    I.clientDistance c c'=I.clientDistance c' c := I.distance_symm _ _

end MetricKMedian.Instance
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceDataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.InstanceProgram
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram
abbrev Nonzero := {I : Instance // ¬I.zeroTest}
def lpInput (I : Nonzero) : LPBinary.Input :=
  ⟨I.val.facilities.card,I.val.clients.card,I.val.k,card_pos.mpr I.val.facilities_nonempty,
    card_pos.mpr (I.val.nonzero_clients I.property),I.val.k_pos,I.val.k_le,I.val.indexedDistance⟩
end MetricKMedian.InstanceProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBindProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.Automatic Binary.Automatic.Poly Finset

variable {α β A : Type}

 theorem jointWeights_raw (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (view : β → A) :
    jointWeights ((raw μ).1,List.ofFn (fun i => ((raw (κ i)).1,(κ i).states.toList.map view)))=
      List.ofFn (fun j => let z := (finSigmaFinEquiv (n:=fun i => (κ i).length)).symm j;
        μ.law.rational.weight z.1*(κ z.1).law.rational.weight z.2) := by
  simp only [jointWeights,raw,weights_law,Gaussian.ListOperation.zip_ofFn,List.flatMap_def,
    List.map_ofFn,Function.comp_def,weights_law]
  exact ListSigma.ofFn_sigma _

 theorem bindData_raw (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (view : β → A) :
    bindData ((raw μ).1,List.ofFn (fun i => ((raw (κ i)).1,(κ i).states.toList.map view)))=
      ((raw (μ.bindIndexed κ)).1,(μ.bindIndexed κ).states.toList.map view) := by
  unfold bindData
  rw [jointWeights_raw,IntegerList.denominator_ofFn,IntegerList.numerators_ofFn]
  let w := (μ.law.rational.sigma (fun i => (κ i).law.rational)).weight
  change ((RationalScaling.denominator (fun j => w (finSigmaFinEquiv.symm j)),
    List.ofFn (RationalScaling.numerator (fun j => w (finSigmaFinEquiv.symm j)))),_) = _
  rw [scaling_denominator_equiv finSigmaFinEquiv w]
  rw [show RationalScaling.numerator (fun j => w (finSigmaFinEquiv.symm j)) =
    (fun j => RationalScaling.numerator w (finSigmaFinEquiv.symm j)) from
      funext (scaling_numerator_equiv finSigmaFinEquiv w)]
  have hs : (List.ofFn fun i => ((raw (κ i)).1,(κ i).states.toList.map view)).flatMap Prod.snd=
      (μ.bindIndexed κ).states.toList.map view := by
    simp only [List.flatMap_def,List.map_ofFn,Function.comp_def,states_list,List.map_ofFn]
    rw [ListSigma.ofFn_sigma]
    simp only [bindIndexed,Vector.getElem_ofFn]
  rw [hs]
  rfl

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end


