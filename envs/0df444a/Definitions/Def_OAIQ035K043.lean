-- Prove2me | Definitions.Def_OAIQ035K043
-- name    : OAIQ035K043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:06:21.532847+00:00
-- url     : https://prove2.me/theorems/d8f92189-f422-45bb-a94f-adc6e65ec7c9
-- title:
--   Definitions bundle OAIQ035K043 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 45 declarations of OpenAI's Lean: 21 definitions, 3 inductive types or structures and 21 theorems. The definitions and types are `OAI.MetricKMedian.Instance.zeroOutput`, `OAI.MetricKMedian.LPBinary.Input.encode`, `OAI.MetricKMedian.LPBinary.Program.candidatesProgram`, `OAI.MetricKMedian.LPBinary.Program.edual`, `OAI.MetricKMedian.LPBinary.Program.enext`, `OAI.MetricKMedian.LPBinary.Program.epoint`, `OAI.MetricKMedian.LPBinary.Program.ethreshold`, `OAI.MetricKMedian.LPBinary.Program.etrunc`, `OAI.MetricKMedian.LPBinary.Program.inputRaw`, `OAI.MetricKMedian.LPBinary.Repair.eo`, `OAI.MetricKMedian.LPBinary.ec`, `OAI.MetricKMedian.LPBinary.ei`, `OAI.MetricKMedian.LPBinary.ers`, `OAI.MetricKMedian.LPBinary.es`, `OAI.MetricKMedian.Preparation.CoupledLaw.castWeights`, `OAI.MetricKMedian.Reduction.Program.Branch`, `OAI.MetricKMedian.RoundingProgram.Terminal.ber`, `OAI.MetricKMedian.SparseCounts.Program.Context`, `OAI.MetricKMedian.SparseCounts.Program.Input`, `OAI.MetricKMedian.SparseCounts.Program.T`, `OAI.MetricKMedian.SparseCounts.Program.column`, `OAI.MetricKMedian.SparseCounts.Program.update`, `OAI.MetricKMedian.SparsePrepared.opening`, `OAI.MetricKMedian.SparseSignedPreparation.Program.Input.signed`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_DualListCompiler`, `KMedian_Optimization_FractionalListChecks`, `KMedian_Optimization_LPBinaryInput`, `KMedian_Optimization_LPBinaryStart`, `KMedian_Optimization_LPBinaryTrajectory`, `KMedian_Optimization_LPListFacts`, `KMedian_Optimization_SimplexListProgram`, `KMedian_Optimization_SubgradientTrajectoryHeight`, `KMedian_Optimization_TruncatedListCompiler`, `KMedian_Optimization_ZeroCostBranch`, `KMedian_Preparation_CoupledWeights`, `KMedian_Process_CountStepProgram`, `KMedian_Programs_BranchProgram`, `KMedian_Programs_NearestListProgram`, `KMedian_Rounding_SignedPreparationProgram`, `KMedian_Rounding_SignedTerminalProgram`, `KMedian_Sparse_SparseBind`, `KMedian_Sparse_SparseCoupledPreparation`, `KMedian_Sparse_SparseOuterCounts`, `KMedian_Sparse_SparsePreparedBudget`, `KMedian_Sparse_SparseProduct`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K027`, `OAIQ035K028`, `OAIQ035K029`, `OAIQ035K030`, `OAIQ035K032`, `OAIQ035K033`, `OAIQ035K034` and `OAIQ035K035` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K048` and `OAIQ035K049`; the proofs of `OAI.MetricKMedian.RationalPhysicalKernel.histories_drift`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_mass`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival` and `OAI.MetricKMedian.RationalPhysicalKernel.histories_valid`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K027
import Definitions.Def_OAIQ035K028
import Definitions.Def_OAIQ035K029
import Definitions.Def_OAIQ035K030
import Definitions.Def_OAIQ035K032
import Definitions.Def_OAIQ035K033
import Definitions.Def_OAIQ035K034
import Definitions.Def_OAIQ035K035

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPListFacts
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
-- module Solutions.OAIQ035_KM.KMedian_Optimization_SubgradientTrajectoryHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                   
section
namespace MetricKMedian.TruncatedLP
open Finset ProjectedSubgradient Binary
variable {n m : ℕ} [NeZero n] [NeZero m]

theorem trajectory_height (d : Fin m → Fin n → ℚ) (r k H : ℕ)
    (hr : 0 < r) (hk : 0<k) (hH : 0<H)
    (R : ℤ) (hR : 0<R) (hd : ∀ j i, RationalGrid.At R (d j i))
    (L : ℕ) (hbase : rateDen (n:=n) (m:=m) r H*R*(n:ℤ) ≤ 2^L)
    (hkL : (k:ℤ) ≤ 2^L) (t : ℕ) (i : Fin n) :
    HasHeight (point (trajectory (k:ℚ) (rate (n:=n) (m:=m) r H)
      (fun y => gradient d y H) (initial (k:ℚ)) t) i) (L*(t+1)) := by
  let b := rateDen (n:=n) (m:=m) r H
  have hb : 0<b := rateDen_pos r H hr hH
  obtain ⟨Q,hQ,hBQ,hv⟩ := trajectory_denominator (n:=n) (k:ℤ) b R hb hR
    (fun y => gradient d y H) (fun y j => by
      exact_mod_cast gradient_grid d y R (H:ℤ) hR.ne' hd j) t
  let q := point (trajectory (k:ℚ) (rate (n:=n) (m:=m) r H)
      (fun y => gradient d y H) (initial (k:ℚ)) t) i
  have hqgrid : RationalGrid.At Q q := by
    dsimp only [q]
    rw [rate_eq]
    exact hv i
  have hkq : (0:ℚ)<k := by exact_mod_cast hk
  have hf := trajectory_feasible (k:ℚ) (rate (n:=n) (m:=m) r H)
    (fun y => gradient d y H) (initial (k:ℚ)) hkq (initial_feasible _ hkq.le) t
  have hq0 : 0≤q := hf.1 i
  have hqk : q≤(k:ℚ) := (single_le_sum (fun j _ => hf.1 j) (mem_univ i)).trans_eq hf.2
  obtain ⟨A,hA⟩ := hqgrid
  change q=(A:ℚ)/(Q:ℚ) at hA
  have hQq : (0:ℚ)<Q := by exact_mod_cast hQ
  have hA0 : (0:ℤ)≤A := by
    have hh : (0:ℚ)≤A := by
      have hmul := mul_nonneg (hA ▸ hq0) hQq.le
      rwa [div_mul_cancel₀ _ hQq.ne'] at hmul
    exact_mod_cast hh
  have hAk : A≤(k:ℤ)*Q := by
    have hh := (div_le_iff₀ hQq).mp (hA ▸ hqk)
    exact_mod_cast hh
  have hQP : Q≤(2:ℤ)^(L*t) := by
    apply hBQ.trans
    rw [pow_mul]
    apply pow_le_pow_left₀ (le_of_lt (mul_pos (mul_pos hb hR) (by exact_mod_cast NeZero.pos n))) hbase
  have hAP : |A|≤(2:ℤ)^(L*(t+1)) := by
    rw [abs_of_nonneg hA0]
    calc
      _ ≤ (k:ℤ)*Q := hAk
      _ ≤ (2:ℤ)^L*(2:ℤ)^(L*t) := mul_le_mul hkL hQP hQ.le (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; ring
  have hQP' : |Q|≤(2:ℤ)^(L*(t+1)) := by
    rw [abs_of_pos hQ]
    exact hQP.trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left L (Nat.le_succ _)))
  change HasHeight q _
  rw [hA]
  exact Gaussian.ratio_num_den_bound A Q hQ.ne' _ hAP hQP'
end MetricKMedian.TruncatedLP
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPBinaryInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Polynomial Finset

namespace Input
abbrev encode (I : Input) := encodePair ers Nat.bits I.raw

 theorem bounds (I : Input) : I.n ≤ I.encode.length ∧ I.m ≤ I.encode.length ∧ I.k ≤ I.encode.length ∧
    ∀ j i, HasHeight (I.distance j i) I.encode.length := by
  let L := I.encode.length
  have henc : L=2*(ers I.rows).length+1+I.k.bits.length := by
    simp only [L,raw,encodePair_length]
  have hm := EncodedList.length_le er I.rows
  change I.rows.length ≤ (ers I.rows).length at hm
  simp only [rows,List.length_ofFn] at hm
  change I.m ≤ (ers I.rows).length at hm
  have hrow (j : Fin I.m) : (er (List.ofFn (I.distance j))).length  ≤  (ers I.rows).length :=
    EncodedList.member_length er I.rows _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
  have hn := EncodedList.length_le Ratio.encode (List.ofFn (I.distance ⟨0,I.mpos⟩))
  change (List.ofFn (I.distance ⟨0,I.mpos⟩)).length ≤ (er (List.ofFn (I.distance ⟨0,I.mpos⟩))).length at hn
  simp only [List.length_ofFn] at hn
  have hnL : I.n ≤ L := by have hh := hrow ⟨0,I.mpos⟩; omega
  refine ⟨hnL,by omega,I.kle.trans hnL,?_⟩
  intro j i
  have hh := EncodedList.member_length Ratio.encode (List.ofFn (I.distance j)) _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  change (Ratio.encode (I.distance j i)).length ≤ (er (List.ofFn (I.distance j))).length at hh
  have hrow := hrow j
  exact (Ratio.height_length _).mono (by omega)

end Input

 theorem penalty_bound (I : Input) (r : ℕ) : TruncatedLP.penalty r I.k  ≤  4*r*(I.encode.length+1) := by
  unfold TruncatedLP.penalty
  gcongr
  exact I.bounds.2.2.1
 theorem grad_bound (I : Input) (r : ℕ) :
    TruncatedLP.gradSize (n:=I.n) (m:=I.m) (TruncatedLP.penalty r I.k)  ≤  gradientBound r I.encode.length := by
  unfold TruncatedLP.gradSize gradientBound
  gcongr
  · exact I.bounds.1
  · exact I.bounds.2.1
  · exact penalty_bound I r
 theorem steps_bound (I : Input) (r : ℕ) :
    TruncatedLP.steps (n:=I.n) (m:=I.m) r I.k (TruncatedLP.penalty r I.k)  ≤  stepsBound r I.encode.length := by
  unfold TruncatedLP.steps stepsBound
  gcongr
  · exact grad_bound I r
  · exact I.bounds.2.2.1

 theorem iterate_height (I : Input) (r : ℕ) (hr : 0 < r) (t : ℕ)
    (ht : t ≤ TruncatedLP.steps (n:=I.n) (m:=I.m) r I.k (TruncatedLP.penalty r I.k)) (i : Fin I.n) :
    HasHeight (ProjectedSubgradient.point (I.vector r t) i) (heightBound r I.encode.length) := by
  let L := I.encode.length
  let q := fun p : Fin I.m × Fin I.n => I.distance p.1 p.2
  let R := RationalScaling.denominator q
  have hR : 0 < R := RationalScaling.denominator_pos q
  have hd : ∀ j i, RationalGrid.At R (I.distance j i) := by
    intro j i
    refine ⟨RationalScaling.numerator q (j,i),?_⟩
    rw [RationalScaling.numerator_cast,mul_div_cancel_right₀]
    exact_mod_cast hR.ne'
  have hRbound : R ≤ (2:ℤ)^(L*(L*L)) := by
    have hh := RationalScaling.denominator_bound q L (fun p => (I.bounds.2.2.2 p.1 p.2).2)
    simp only [Fintype.card_prod,Fintype.card_fin] at hh
    apply hh.trans
    apply pow_le_pow_right₀ (by norm_num)
    gcongr
    · exact I.bounds.2.1
    · exact I.bounds.1
  have hbn : TruncatedLP.rateDen (n:=I.n) (m:=I.m) r (TruncatedLP.penalty r I.k)*(I.n:ℤ) ≤ baseBound r L := by
    unfold TruncatedLP.rateDen
    have hg := grad_bound I r
    have hn := I.bounds.1
    dsimp only [baseBound]
    exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul_left (2*r) hg) hn
  have hnat : (baseBound r L:ℤ) ≤ (2:ℤ)^(baseBound r L) := by exact_mod_cast (Nat.lt_two_pow_self (n:=baseBound r L)).le
  have hbase : TruncatedLP.rateDen (n:=I.n) (m:=I.m) r (TruncatedLP.penalty r I.k)*R*(I.n:ℤ) ≤ (2:ℤ)^(exponentBound r L) := by
    calc
      _ = (TruncatedLP.rateDen (n:=I.n) (m:=I.m) r (TruncatedLP.penalty r I.k)*(I.n:ℤ))*R := by ring
      _  ≤  (2:ℤ)^(baseBound r L)*(2:ℤ)^(L*(L*L)) := mul_le_mul (hbn.trans hnat) hRbound hR.le (by positivity)
      _ = (2:ℤ)^(baseBound r L+L*(L*L)) := (pow_add ..).symm
      _  ≤  _ := pow_le_pow_right₀ (by norm_num) (by unfold exponentBound; omega)
  have hk : (I.k:ℤ) ≤ (2:ℤ)^(exponentBound r L) := by
    have hkL : (I.k:ℤ) ≤ L := by exact_mod_cast I.bounds.2.2.1
    have hL : (L:ℤ) ≤ (2:ℤ)^L := by exact_mod_cast (Nat.lt_two_pow_self (n:=L)).le
    exact (hkL.trans hL).trans (pow_le_pow_right₀ (by norm_num) (by unfold exponentBound; omega))
  have hh := TruncatedLP.trajectory_height I.distance r I.k (TruncatedLP.penalty r I.k) hr I.kpos
    (TruncatedLP.penalty_pos r I.k hr) R hR hd (exponentBound r L) hbase hk t i
  apply hh.mono
  unfold heightBound
  exact Nat.mul_le_mul_left _ (Nat.succ_le_succ (ht.trans (steps_bound I r)))

 theorem iterate_size (I : Input) (r : ℕ) (hr : 0 < r) (t : ℕ)
    (ht : t ≤ TruncatedLP.steps (n:=I.n) (m:=I.m) r I.k (TruncatedLP.penalty r I.k)) :
    (er (I.iterate r t)).length  ≤  I.encode.length*(2*(3*heightBound r I.encode.length+10)+1) := by
  have hh := EncodedList.length_bound Ratio.encode (I.iterate r t) (3*heightBound r I.encode.length+10) (by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact Ratio.length_height (iterate_height I r hr t ht i))
  simp only [Input.iterate,List.length_ofFn] at hh
  exact hh.trans (Nat.mul_le_mul_right _ I.bounds.1)

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_SimplexListProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Optimization_DualListCompiler
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

noncomputable def candidatesProgram : PolyProgram (encodePair er Ratio.encode) er (fun x : Row × ℚ => Dual.candidates x.1 x.2) := by
  let consH := (exchange er Ratio.encode).comp (listCons Ratio.encode)
  exact (((constant (encodePair er Ratio.encode) Ratio.encode 0).fanout consH).comp (listCons Ratio.encode)).congr _ (fun _ => rfl)

end MetricKMedian.LPBinary.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_TruncatedListCompiler
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
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPBinaryStart
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

namespace Program
noncomputable def inputRaw : PolyProgram Input.encode ei Input.raw :=
  (identity ei).recode Input.raw (fun _ => rfl) (fun _ => rfl)
end Program

theorem rawGrad_eq (r : ℕ) (I : Input) : rawGrad r I.raw=TruncatedLP.gradSize (n:=I.n) (m:=I.m) (TruncatedLP.penalty r I.k) := by
  simp only [rawGrad,Input.raw,Input.rows,head_ofFn,List.length_ofFn,rawPenalty,TruncatedLP.gradSize,TruncatedLP.penalty]
theorem rawSteps_eq (r : ℕ) (I : Input) : rawSteps r I.raw=TruncatedLP.steps (n:=I.n) (m:=I.m) r I.k (TruncatedLP.penalty r I.k) := by
  unfold rawSteps
  rw [rawGrad_eq]
  rfl
theorem rawRate_eq (r : ℕ) (I : Input) : rawRate r I.raw=TruncatedLP.rate (n:=I.n) (m:=I.m) r (TruncatedLP.penalty r I.k) := by
  simp only [rawRate,rawGrad_eq,TruncatedLP.rate]

theorem update_eq (r : ℕ) (I : Input) (t : ℕ) :
    update (rawContext r I.raw,I.iterate r t)=(rawContext r I.raw,I.iterate r (t+1)) := by
  unfold update
  congr 1
  change Truncated.next I.rows (I.iterate r t) (TruncatedLP.penalty r I.k) I.k (rawRate r I.raw)=I.iterate r (t+1)
  rw [rawRate_eq]
  unfold Input.rows Input.iterate
  rw [Truncated.next_ofFn]
  have he : Vector.ofFn (ProjectedSubgradient.point (I.vector r t))=I.vector r t := by ext index hindex; simp
  rw [he]
  rfl

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPBinaryTrajectory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Polynomial Function

 theorem value_eq (r : ℕ) (I : Input) (t : ℕ) :
    value (rawContext r I.raw,I.iterate r t)=
      TruncatedLP.objective I.distance (ProjectedSubgradient.point (I.vector r t)) (TruncatedLP.penalty r I.k) := by
  unfold value
  change Truncated.objective I.rows (I.iterate r t) (TruncatedLP.penalty r I.k)=_
  exact Truncated.objective_ofFn _ _ _

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_NearestListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset

namespace Nearest

theorem filling_ofFn {n : ℕ} (y d : Fin n → ℚ) (hy : ∀ i, 0 ≤ y i) (hm : 1 ≤ ∑ i, y i) :
    filling (List.ofFn y) (List.ofFn d)=List.ofFn (ProjectedSubgradient.point (Preparation.computedNearest y d hy hm)) := by
  simp only [filling,entries_ofFn,List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply,amount,prior_ofFn,ProjectedSubgradient.point,Preparation.computedNearest_formula]

end Nearest
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
abbrev eo := encodePair er ers

end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalListChecks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.LPBinary.Repair
open Binary Binary.PolyProgram Function Finset

theorem valid_encodeData {n m : ℕ} (a : TruncatedLP.FractionalData n m) (k : ℕ) :
    valid (encodeData a) k=decide (a.Valid k) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [valid,encodeData,Bool.and_eq_true,all_ofFn,bounded,dominated,Gaussian.ListOperation.zip_ofFn,
    decide_eq_true_eq,List.sum_ofFn,TruncatedLP.FractionalData.Valid,ProjectedSubgradient.point]
  tauto

theorem value_encodeData {n m : ℕ} (a : TruncatedLP.FractionalData n m) (d : Fin m → Fin n → ℚ) :
    value (encodeData a) (List.ofFn (fun j => List.ofFn (d j)))=a.value d := by
  simp only [value,encodeData,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,Function.comp_def,dot,List.sum_ofFn,
    TruncatedLP.FractionalData.value,ProjectedSubgradient.point]

end MetricKMedian.LPBinary.Repair
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

end Instance
end MetricKMedian
end
end

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
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β γ : Type}

theorem prod_property (μ : SparseIntegerLaw α) (ν : SparseIntegerLaw β)
    (f : α → β → γ) (P : γ → Prop)
    (hP : ∀ a : Fin μ.length, ∀ b : Fin ν.length, P (f μ.states[a.val] ν.states[b.val])) :
    ∀ a : Fin (μ.prod ν f).length, P (μ.prod ν f).states[a.val] := by
  intro a
  change P ((Vector.ofFn (fun i => f μ.states[((finProdFinEquiv (m := μ.length) (n := ν.length)).symm i).1.val]
    ν.states[((finProdFinEquiv (m := μ.length) (n := ν.length)).symm i).2.val]))[a.val])
  simp only [Vector.getElem_ofFn]
  exact hP _ _

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBind
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem bindIndexed_property (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (P : β → Prop) (hP : ∀ a, ∀ b : Fin (κ a).length, P (κ a).states[b.val]) :
    ∀ i : Fin (μ.bindIndexed κ).length, P (μ.bindIndexed κ).states[i.val] := by
  intro i
  change P ((Vector.ofFn (fun j => let z := finSigmaFinEquiv.symm j;
    (κ z.1).states[z.2.val]))[i.val])
  simp only [Vector.getElem_ofFn]
  exact hP _ _

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseOuterCounts
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

theorem outsideCount_cast (q : Fin m → ℚ) (z : State n m) (e : Fin m) :
    (outsideCount q z e:ℚ)=SparseSignedPreparation.outside (base q) z e := by
  simp only [outsideCount,SparseSignedPreparation.outside,SparseStarActivation.upper]
  split_ifs <;> simp

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparsePreparedBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw SparseGridRounding
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem raw_counts (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (z : State n m) :
    SparseSignedPreparation.raw D c (base q) z=
      (∑ e,c e*(outsideCount q z e:ℚ))-(∑ j,∑ e,(activationCount D q z e j:ℚ)) := by
  rw [sum_comm]
  simp only [SparseSignedPreparation.raw,sum_sub_distrib,← Nat.cast_sum,activation_sum,
    Nat.cast_add,Nat.cast_mul,outsideCount_cast]

def opening (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) : ℚ :=
  (∑ e,c e*(outsideCount q z e:ℚ))+(∑ j,(total D q Δ z j:ℚ))

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCoupledPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m f : ℕ}

theorem opening_cast (D : Fin m → Finset (Fin n)) (a q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (g : ℝ) :
    g * (opening D a q Δ z : ℝ) =
      (∑ e, (a e : ℝ) * (g * (outsideCount q z e : ℝ))) +
      (∑ j, g * (total D q Δ z j : ℝ)) := by
  simp only [opening, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast,
    mul_add, mul_sum]
  congr 1
  exact sum_congr rfl (fun _ _ => by ring)

end MetricKMedian.SparsePrepared
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_CoupledWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Preparation
open Finset
attribute [local instance] CoupledLaw.finite
variable {E T I : Type} [Fintype E] [DecidableEq E]
  [Fintype T] [DecidableEq T] [Fintype I] [DecidableEq I]

noncomputable def CoupledLaw.castWeights {D : E → Finset T} {a a' w w' : E → ℝ}
    {P : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw D a w P y p c g γ B Δ) (ha : a=a') (hw : w=w') :
    CoupledLaw D a' w' P y p c g γ B Δ where
  Ω := L.Ω
  ν := L.ν
  κ := L.κ
  O := L.O
  N := L.N
  R := L.R
  K := L.K
  C := L.C
  open_cap := by rw [← hw]; exact L.open_cap
  open_zero := by rw [← hw]; exact L.open_zero
  nominal_nonneg := L.nominal_nonneg
  nominal_cap := L.nominal_cap
  nominal_mean := by rw [← hw]; exact L.nominal_mean
  nominal_variance := by rw [← hw]; exact L.nominal_variance
  nominal_pair := by rw [← hw]; exact L.nominal_pair
  request_cap := L.request_cap
  request_target := L.request_target
  request_mean := by rw [← hw]; exact L.request_mean
  exact_total := L.exact_total
  half := L.half
  total_cap := L.total_cap
  total_deviation := L.total_deviation
  pieces := L.pieces
  piece_mean := L.piece_mean
  piece_pair := L.piece_pair
  piece_variance := L.piece_variance
  budget := by rw [← ha]; exact L.budget

end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.SparseCounts.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse
open ListOperation (Row Table er et)

structure Input where
  n : ℕ
  m : ℕ
  columns : Fin m → SparseIntegerLaw ((Fin n → ℕ))
structure Context where
  input : Input
  t : ℕ
abbrev T (c : Context) := SparseCounts.Table c.input.n c.input.m

def column (c : Context) : SparseIntegerLaw (Fin c.input.n → ℕ) :=
  if h : c.t < c.input.m then c.input.columns ⟨c.t,h⟩ else .dirac (fun _ => 0)
def update (c : Context) (G : T c) (S : (Fin c.input.n → ℕ)) : T c :=
  fun i => if i.val=c.t then S else G i

end MetricKMedian.SparseCounts.Program
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

abbrev ber := SparseBernoulli.Program.er

end Terminal
end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedPreparationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparseSignedPreparation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)

def Input.signed (x : Input) : RoundingProgram.Input true :=
  ⟨x.m,SparseSignedPreparation.signed x.D x.c,x.p,by simp,x.feasible⟩

end MetricKMedian.SparseSignedPreparation.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_BranchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open Enumeration
structure Branch where
  original : Instance
  facilities : Finset (Fin original.n)
end MetricKMedian.Reduction.Program
end

end OAI
end


