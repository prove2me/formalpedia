-- Prove2me | Definitions.Def_OAIQ035K041
-- name    : OAIQ035K041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:03:32.650072+00:00
-- url     : https://prove2.me/theorems/efc5a71c-1e09-45b6-bafa-05160b75d8d7
-- title:
--   Definitions bundle OAIQ035K041 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 23 definitions and 25 theorems. The definitions and types are `OAI.MetricKMedian.Gaussian.IntegerProgram.Input.encode`, `OAI.MetricKMedian.Gaussian.IntegerProgram.ed`, `OAI.MetricKMedian.Gaussian.IntegerProgram.em`, `OAI.MetricKMedian.Gaussian.IntegerProgram.er`, `OAI.MetricKMedian.Gaussian.ListOperation.startProgram`, `OAI.MetricKMedian.InstanceProgram.Nonzero`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.compressed`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.nextLaw`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.step`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.RationalInput.compressed`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.er`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.lawStep`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.scaledRows`, `OAI.MetricKMedian.IntegerLaw.ListOperation.Input.encode`, `OAI.MetricKMedian.IntegerLaw.ListOperation.activeData`, `OAI.MetricKMedian.IntegerLaw.ListOperation.activeRows`, `OAI.MetricKMedian.IntegerLaw.ListOperation.ed`, `OAI.MetricKMedian.IntegerLaw.ListOperation.ee`, `OAI.MetricKMedian.IntegerLaw.ListOperation.ees`, `OAI.MetricKMedian.IntegerLaw.ListOperation.em`, `OAI.MetricKMedian.IntegerLaw.ListOperation.er`, `OAI.MetricKMedian.IntegerLaw.ListPivot.ees`, `OAI.MetricKMedian.SparseBernoulli.Program.Context.encode`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Compression_AffineListOperations`, `KMedian_Compression_CompressionBinaryProgram`, `KMedian_Compression_CompressionBounds`, `KMedian_Compression_CompressionListStep`, `KMedian_Compression_GaussianBinaryProgram`, `KMedian_Compression_GaussianInputBounds`, `KMedian_Compression_GaussianListRun`, `KMedian_Compression_GaussianListSize`, `KMedian_Compression_GaussianResidualHeight`, `KMedian_Compression_GaussianStates`, `KMedian_Compression_IntegerKernelProgram`, `KMedian_Compression_RationalKernelHeightSupport`, `KMedian_Geometry_IntegerBranching`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Programs_InstanceDataProgram`, `KMedian_Programs_PivotListProgram`, `KMedian_Programs_RationalFeatureProgram`, `KMedian_Sparse_SparseBranchProgram`, `KMedian_Sparse_SparseIntegerLaw`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K027`, `OAIQ035K028`, `OAIQ035K029`, `OAIQ035K030`, `OAIQ035K031` and `OAIQ035K032` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K047`, `OAIQ035K048` and `OAIQ035K062`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K027
import Definitions.Def_OAIQ035K028
import Definitions.Def_OAIQ035K029
import Definitions.Def_OAIQ035K030
import Definitions.Def_OAIQ035K031
import Definitions.Def_OAIQ035K032

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_RationalKernelHeightSupport
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianResidualHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Gaussian
open Finset

 theorem rational_circuit_ratio (r n L : ℕ) (A : Fin r → Fin n → ℚ)
    (hnum : ∀ i j, |(A i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((A i j).den:ℤ) ≤ (2:ℤ)^L)
    (z : Fin n → ℚ) (hc : IsCircuit A z) (hk : ∀ i, ∑ j, A i j*z j=0)
    (w : Fin n) (hw : z w=1) :
    ∃ U : Fin n → ℤ, U w ≠ 0 ∧
      (∀ j, |U j| ≤ (2:ℤ)^(2*r*(r+L*(n+1)))) ∧
      ∀ j, z j=(U j:ℚ)/(U w:ℚ) := by
  let V : Fin r → Fin n → ℤ := fun i => RationalScaling.numerator (A i)
  let D : Fin r → ℚ := fun i => RationalScaling.denominator (A i)
  have hD : ∀ i, D i ≠ 0 := by
    intro i
    apply ne_of_gt
    dsimp only [D]
    exact_mod_cast RationalScaling.denominator_pos (A i)
  have hV : ∀ i j, (V i j:ℚ)=A i j*D i := fun i j => RationalScaling.numerator_cast (A i) j
  have hVb : ∀ i j, |V i j| ≤ (2:ℤ)^(L*(n+1)) := by
    intro i j
    simpa only [Fintype.card_fin] using RationalScaling.numerator_bound (A i) L (hnum i) (hden i) j
  have hki : ∀ v : Fin n → ℚ,
      (∀ i, ∑ j, (V i j:ℚ)*v j=0) ↔ (∀ i, ∑ j, A i j*v j=0) := by
    intro v
    simp only [hV]
    exact row_scaling_kernel_iff A D hD v
  have hcV : IsCircuit (fun i j => (V i j:ℚ)) z := by
    intro v hv hkv
    exact hc v hv ((hki v).mp hkv)
  exact circuit_integer_ratio V z (L*(n+1)) hVb ((hki z).mpr hk) hcV w hw

namespace ResidualCertificate
variable {R N r n : ℕ} {A : Fin R → Fin N → ℚ} {B : Fin r → Fin n → ℚ}

 theorem entry_height (P : ResidualCertificate A B) (L : ℕ)
    (hnum : ∀ i j, |(A i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((A i j).den:ℤ) ≤ (2:ℤ)^L) (i : Fin r) (j : Fin n) :
    |(B i j).num| ≤ (2:ℤ)^(residualHeight R N L) ∧
      ((B i j).den:ℤ) ≤ (2:ℤ)^(residualHeight R N L) := by
  obtain ⟨U,hUw,hU,hz⟩ := rational_circuit_ratio P.pivotCols.card R L
    (fun c t => A t (P.pivotCols.orderEmbOfFin rfl c))
    (fun c t => hnum t _) (fun c t => hden t _)
    (P.coefficient i) (P.circuit i)
    (fun c => P.annihilates i _ (P.pivotCols.orderEmbOfFin_mem rfl c)) (P.row i) (P.normalized i)
  have hc : P.pivotCols.card ≤ N := (card_le_card (subset_univ P.pivotCols)).trans_eq (card_fin N)
  have hpow : 2*P.pivotCols.card*(P.pivotCols.card+L*(R+1)) ≤ 2*N*(N+L*(R+1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hc) (Nat.add_le_add_right hc _)
  have hUb : ∀ t, |U t| ≤ (2:ℤ)^(2*N*(N+L*(R+1))) := fun t =>
    (hU t).trans (pow_le_pow_right₀ (by norm_num) hpow)
  rw [P.represents]
  exact combination_height R (2*N*(N+L*(R+1))) L (fun t => A t (P.col j))
    (P.coefficient i) U (P.row i) hUw hUb hz (fun t => hnum t _) (fun t => hden t _)

end ResidualCertificate
end MetricKMedian.Gaussian
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Gaussian
open Finset

 theorem kernelStates_entry_height (R N L : ℕ) (A : RatMatrix R N)
    (hnum : ∀ i j, |(values A i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((values A i j).den:ℤ) ≤ (2:ℤ)^L)
    (B : MatrixState) (hB : B ∈ kernelStates R N A) (i : Fin B.rows) (j : Fin B.cols) :
    |(values B.data i j).num| ≤ (2:ℤ)^(residualHeight R N L) ∧
      ((values B.data i j).den:ℤ) ≤ (2:ℤ)^(residualHeight R N L) := by
  obtain ⟨P⟩ := kernelStates_certificate (values A) R N A (ResidualCertificate.initial _) B hB
  exact P.entry_height L hnum hden i j

 theorem kernelStates_return_height (R N L : ℕ) (A : RatMatrix R N) (hRN : R<N)
    (hnum : ∀ i j, |(values A i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((values A i j).den:ℤ) ≤ (2:ℤ)^L)
    (B : MatrixState) (hB : B ∈ kernelStates R N A) (j : Fin B.cols) :
    |((kernelVector B.rows B.cols B.data)[j.val]).num| ≤ (2:ℤ)^(returnHeight R N L) ∧
      (((kernelVector B.rows B.cols B.data)[j.val]).den:ℤ) ≤ (2:ℤ)^(returnHeight R N L) := by
  obtain ⟨P⟩ := kernelStates_certificate (values A) R N A (ResidualCertificate.initial _) B hB
  have hrow : B.rows ≤ R := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective P.row P.row_injective
  have hcol : B.cols ≤ N := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective P.col P.col_injective
  have hentry := kernelStates_entry_height R N L A hnum hden B hB
  have hb := rational_input_kernel_bounds B.rows B.cols (residualHeight R N L) (values B.data)
    (kernelStates_underdetermined R N A hRN B hB) (fun i j => (hentry i j).1) (fun i j => (hentry i j).2) j
  have hp : 2*B.rows*(B.rows+residualHeight R N L*(B.cols+1)) ≤ returnHeight R N L := by
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hrow)
      (Nat.add_le_add hrow (Nat.mul_le_mul_left _ (Nat.add_le_add_right hcol 1)))
  have he := congrFun (kernelVector_eq B.rows B.cols B.data) j
  rw [he]
  exact ⟨hb.1.trans (pow_le_pow_right₀ (by norm_num) hp),hb.2.trans (pow_le_pow_right₀ (by norm_num) hp)⟩

end MetricKMedian.Gaussian
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianListSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function

 theorem row_size (row : Row) (N H : ℕ) (hn : row.length ≤ N) (hh : ∀ q∈row, HasHeight q H) :
    (er row).length ≤ rowBound N H := by
  exact (EncodedList.length_bound Ratio.encode row (3*H+10) (fun q hq => Ratio.length_height (hh q hq))).trans
    (Nat.mul_le_mul_right _ hn)

 theorem frame_size (N H : ℕ) (f : Frame) (h : FrameValid N H f) :
    (ef f).length ≤ frameBound N H := by
  have hp := NatBinary.length_le_height (h.1.trans (Nat.lt_two_pow_self (n:=N)).le)
  have hr := row_size f.2 N H h.2.1 h.2.2
  simp only [ef,encodePair_length,frameBound]
  omega

 theorem frames_size (R N H : ℕ) (fs : Frames) (hR : fs.length ≤ R) (h : FramesValid N H fs) :
    (efs fs).length ≤ framesBound R N H :=
  (EncodedList.length_bound ef fs (frameBound N H) (fun f hf => frame_size N H f (h f hf))).trans
    (Nat.mul_le_mul_right _ hR)

 theorem matrix_size {r n : ℕ} (A : Fin r → Fin n → ℚ) (R N H : ℕ)
    (hr : r ≤ R) (hn : n ≤ N) (hh : ∀ i j,HasHeight (A i j) H) :
    (ers (matrix A)).length ≤ matrixBound R N H := by
  apply (EncodedList.length_bound er (matrix A) (rowBound N H) ?_).trans
  · simpa only [matrix,List.length_ofFn,matrixBound] using Nat.mul_le_mul_right (2*rowBound N H+1) hr
  · intro row hrow
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
    apply row_size _ N H (by simpa only [List.length_ofFn] using hn)
    intro q hq
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
    exact hh i j

 theorem desc_size {r n : ℕ} (A : Fin r → Fin n → ℚ) (fs : Frames) (R N H K : ℕ)
    (hr : r ≤ R) (hn : n ≤ N) (hh : ∀ i j,HasHeight (A i j) H)
    (hf : fs.length ≤ R) (hv : FramesValid N H fs) :
    (eState (.inl ((List.replicate n (),matrix A),fs))).length ≤ stateBound R N H K := by
  have ha := matrix_size A R N H hr hn hh
  have hf := frames_size R N H fs hf hv
  simp only [eState,encodeLoop,List.length_cons,ed,edata,encodePair_length,slots_size,stateBound]
  omega

 theorem up_size {n : ℕ} (z : Fin n → ℚ) (fs : Frames) (R N H K : ℕ)
    (hn : n ≤ N) (hz : ∀ j,HasHeight (z j) K)
    (hf : fs.length ≤ R) (hv : FramesValid N H fs) :
    (eState (.inr (List.ofFn z,fs))).length ≤ stateBound R N H K := by
  have hf := frames_size R N H fs hf hv
  have hz := row_size (List.ofFn z) N K (by simpa only [List.length_ofFn] using hn)
    (fun q hq => by obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq; exact hz j)
  simp only [eState,encodeLoop,List.length_cons,eUp,encodePair_length,stateBound]
  omega

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianInputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Finset Polynomial

 theorem input_bounds (I : Input) :
    I.rows ≤ I.encode.length ∧ I.cols ≤ I.encode.length ∧
      ∀ i j,HasHeight (values I.data i j) I.encode.length := by
  let L := I.encode.length
  have henc : L=2*I.cols+1+(ers (matrix (values I.data))).length := by
    simp only [L,Input.raw,encodePair_length,slots_size]
  have hr := EncodedList.length_le er (matrix (values I.data))
  simp only [matrix,List.length_ofFn] at hr
  change I.rows ≤ (ers (matrix (values I.data))).length at hr
  refine ⟨by omega,by omega,?_⟩
  intro i j
  have hrow : List.ofFn (values I.data i)∈matrix (values I.data) := List.mem_ofFn.mpr ⟨i,rfl⟩
  have hq : values I.data i j∈List.ofFn (values I.data i) := List.mem_ofFn.mpr ⟨j,rfl⟩
  have h₁ := EncodedList.member_length Ratio.encode (List.ofFn (values I.data i)) _ hq
  have h₂ := EncodedList.member_length er (matrix (values I.data)) _ hrow
  change (Ratio.encode (values I.data i j)).length ≤ (er (List.ofFn (values I.data i))).length at h₁
  change (er (List.ofFn (values I.data i))).length ≤ (ers (matrix (values I.data))).length at h₂
  exact (Ratio.height_length _).mono (by omega)

 theorem input_audit (I : Input) :
    Audit I.encode.length I.encode.length (residualHeight I.encode.length I.encode.length I.encode.length)
      (returnHeight I.encode.length I.encode.length I.encode.length) I.rows I.cols I.data := by
  let L := I.encode.length
  obtain ⟨hr,hn,hh⟩ := input_bounds I
  intro B hB
  obtain ⟨P⟩ := kernelStates_certificate (values I.data) I.rows I.cols I.data (ResidualCertificate.initial _) B hB
  have hrB : B.rows ≤ I.rows := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective P.row P.row_injective
  have hnB : B.cols ≤ I.cols := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective P.col P.col_injective
  refine ⟨hrB.trans hr,hnB.trans hn,?_,?_⟩
  · intro i j
    have hb := kernelStates_entry_height I.rows I.cols L I.data (fun i j => (hh i j).1) (fun i j => (hh i j).2) B hB i j
    exact HasHeight.mono hb (residualHeight_mono hr hn le_rfl)
  · intro j
    have hb := kernelStates_return_height I.rows I.cols L I.data I.underdetermined
      (fun i j => (hh i j).1) (fun i j => (hh i j).2) B hB j
    exact HasHeight.mono hb (returnHeight_mono hr hn le_rfl)

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianListRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Finset

 theorem descend_run (R N H K r n : ℕ) (A : RatMatrix r n) (hn : r<n)
    (ha : Audit R N H K r n A) (fs : Frames) (hfs : fs.length+r ≤ R)
    (hv : FramesValid N H fs) (u : ℕ) (out : Row)
    (hu : BoundedRun eState body (stateBound R N H K) u (returned r n A fs) out) :
    ∃ t ≤ 2*r+1, BoundedRun eState body (stateBound R N H K) (t+u) (desc r n A fs) out := by
  induction r generalizing n fs u with
  | zero =>
      obtain ⟨hr,hN,hh,hk⟩ := audit_head ha
      refine ⟨1,by omega,?_⟩
      have hs := desc_size (values A) fs R N H K hr hN hh (by omega) hv
      rw [Nat.add_comm 1 u]
      exact BoundedRun.step hs (down_base n A fs) hu
  | succ r ih =>
      cases n with
      | zero => omega
      | succ n =>
          obtain ⟨hr,hN,hh,hk⟩ := audit_head ha
          have hs := desc_size (values A) fs R N H K hr hN hh (by omega) hv
          by_cases hp : (univ.filter (fun j => values A 0 j ≠ 0)).Nonempty
          · let p := (univ.filter (fun j => values A 0 j ≠ 0)).min' hp
            let B := tabulate (Gaussian.residual (values A) p)
            let frame : Frame := (p.val,List.ofFn (values A 0))
            have hframe : FrameValid N H frame := by
              refine ⟨p.isLt.le.trans hN,by simpa only [frame,List.length_ofFn] using hN,?_⟩
              intro q hq
              obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
              exact hh 0 j
            have hvalid : FramesValid N H (frame::fs) := by
              intro f hf
              rcases List.mem_cons.mp hf with rfl|hf
              · exact hframe
              · exact hv f hf
            have hlen : (frame::fs).length+r ≤ R := by simp only [List.length_cons]; omega
            have hB := audit_pivot ha hp
            obtain ⟨hrB,hNB,hhB,hkB⟩ := audit_head hB
            have hrise : BoundedRun eState body (stateBound R N H K) (u+1)
                (returned r n B (frame::fs)) out := by
              apply BoundedRun.step
              · exact up_size (fun j : Fin n => (kernelVector r n B)[j.val]) (frame::fs) R N H K hNB hkB (by omega) hvalid
              · exact return_pivot A fs hp
              · exact hu
            obtain ⟨t,ht,htRun⟩ := ih n B (by omega) hB (frame::fs) hlen hvalid (u+1) hrise
            refine ⟨t+2,by omega,?_⟩
            have hstep := BoundedRun.step hs (down_pivot A fs hp) htRun
            rw [show (t+2)+u=(t+(u+1))+1 by omega]
            exact hstep
          · have hB := audit_skip ha hp
            have hcont : BoundedRun eState body (stateBound R N H K) u
                (returned r (n+1) (tabulate (fun i j => values A i.succ j)) fs) out := by
              rw [return_skip A fs hp]
              exact hu
            obtain ⟨t,ht,htRun⟩ := ih (n+1) (tabulate (fun i j => values A i.succ j)) (by omega) hB fs (by omega) hv u hcont
            refine ⟨t+1,by omega,?_⟩
            have hstep := BoundedRun.step hs (down_skip A fs hp) htRun
            rw [show (t+1)+u=(t+u)+1 by omega]
            exact hstep

 theorem full_run (R N H K r n : ℕ) (A : RatMatrix r n) (hn : r<n)
    (ha : Audit R N H K r n A) :
    ∃ t ≤ 2*r+2, BoundedRun eState body (stateBound R N H K) t (desc r n A []) (kernelList r n A) := by
  obtain ⟨hr,hN,hh,hk⟩ := audit_head ha
  have hv : FramesValid N H [] := by intro f hf; cases hf
  have hend : BoundedRun eState body (stateBound R N H K) 1 (returned r n A []) (kernelList r n A) := by
    apply BoundedRun.stop
    · exact up_size (fun j : Fin n => (kernelVector r n A)[j.val]) [] R N H K hN hk (by simp) hv
    · exact finish r n A
  obtain ⟨t,ht,hrun⟩ := descend_run R N H K r n A hn ha [] (by simpa) hv 1 _ hend
  exact ⟨t+1,by omega,hrun⟩
end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianBinaryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Polynomial

noncomputable def startProgram : PolyProgram Input.encode eState (fun I : Input => desc I.rows I.cols I.data []) := by
  let raw : PolyProgram Input.encode edata Input.raw := (identity edata).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  exact ((raw.fanout (constant Input.encode efs [])).comp (injectLeft eUp ed)).congr _ (fun _ => rfl)

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_IntegerKernelProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Gaussian.IntegerProgram
open Binary Binary.PolyProgram
abbrev er := IntegerList.er
abbrev em := IntegerList.em
abbrev ed := encodePair ListOperation.eslots em

abbrev Input.encode (I : Input) := ed I.raw

end MetricKMedian.Gaussian.IntegerProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_AffineListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.IntegerLaw.ListOperation
open Binary Gaussian
open Finset
abbrev er := Binary.IntegerList.er
abbrev em := Binary.IntegerList.em
abbrev ed := encodePair es (encodePair er em)
abbrev ee := encodePair Nat.bits (encodePair Signed.encode er)
abbrev ees := encodeList ee

def activeRows (x : Data) : Gaussian.IntegerProgram.Rows :=
  (active x).map (fun _ => 1) :: (List.range x.1.length).map (fun j => (active x).map (fun e => e.2.2[j]?.getD 0))
def activeData (x : Data) : List Unit × Rows :=
  ((active x).map (fun _ => ()),activeRows x)

abbrev Input.encode (I : Input) := ed I.raw

theorem active_raw (I : Input) : active I.raw=List.ofFn (fun j : Fin I.μ.support.card =>
    let i := ((I.μ.support.orderIsoOfFin rfl) j).val
    (i.val,(I.μ.numerator i,List.ofFn (I.v i)))) := by
  rw [active,entries_raw,List.ofFn_eq_map,List.filter_map]
  exact EncodingLists.map_filter_enum _ (fun i => I.μ.numerator i≠0)

theorem activeRows_raw (I : Input) : activeRows I.raw=
    List.ofFn (fun j => List.ofFn (activeMatrix I.μ I.v j)) := by
  rw [activeRows,active_raw]
  simp only [Input.raw,List.length_replicate,List.map_ofFn,Function.comp_def]
  rw [indices_ofFn,List.map_ofFn,List.ofFn_succ]
  congr 1
  congr 1
  funext j
  simp only [Function.comp_apply,Gaussian.ListOperation.get_ofFn]
  rfl

theorem activeData_raw (I : Input) : activeData I.raw=I.kernel.raw := by
  simp only [activeData,activeRows_raw,active_raw,List.map_ofFn,Function.comp_def,List.ofFn_const,
    Input.kernel,Gaussian.IntegerProgram.Input.raw]

theorem full_raw (I : Input) :
    full I.raw (List.ofFn (Gaussian.computedIntegerKernel (I.d+1) I.μ.support.card (activeMatrix I.μ I.v)))=
      List.ofFn (computedAffineKernel I.μ I.v) := by
  rw [full,active_raw]
  simp only [List.map_ofFn,Function.comp_def,Gaussian.ListOperation.zip_ofFn]
  simp only [Input.raw,List.length_ofFn,indices_ofFn,List.map_ofFn,Function.comp_def,extend_ofFn,
    computedAffineKernel,Vector.getElem_ofFn]

end MetricKMedian.IntegerLaw.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_PivotListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.IntegerLaw.ListPivot
open Binary Binary.PolyProgram Function Finset
abbrev ees := encodeList ee

theorem update_ofFn {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) (hzsum : ∑ i, z i=0) :
    update (μ.denominator,List.ofFn μ.numerator) (List.ofFn z)=
      let ν := eliminateAt μ z (computedPivot μ z h) (computedPivot_spec μ z h).1 (computedPivot_spec μ z h).2 hzsum
      (ν.denominator,List.ofFn ν.numerator) := by
  simp only [update,Gaussian.ListOperation.zip_ofFn,pivot_ofFn μ z h,Gaussian.ListOperation.get_ofFn,List.map_ofFn,
    Function.comp_def,eliminateAt,Vector.getElem_ofFn]

end MetricKMedian.IntegerLaw.ListPivot
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_CompressionListStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset
abbrev er := Binary.IntegerList.er
def Input.nextLaw (I : Input) : IntegerLaw (Fin I.n) :=
  if h : I.large then compressionStepAuto I.μ I.v h else I.μ

def Input.step (I : Input) : Input := {I with μ := I.nextLaw}

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_CompressionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset Polynomial

def lawStep {n d : ℕ} (v : Fin n → Fin d → ℤ) (μ : IntegerLaw (Fin n)) : IntegerLaw (Fin n) :=
  if h : d+1 < μ.support.card then compressionStepAuto μ v h else μ

theorem input_iterate (I : Input) (t : ℕ) :
    Input.step^[t] I=⟨I.n,I.d,(lawStep I.v)^[t] I.μ,I.v⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']
      rfl

theorem compressSteps_eq_iterate {n d : ℕ} (v : Fin n → Fin d → ℤ) (t : ℕ) (μ : IntegerLaw (Fin n)) :
    compressStepsAuto v t μ=(lawStep v)^[t] μ := by
  induction t generalizing μ with
  | zero => rfl
  | succ t ih =>
      rw [compressStepsAuto,Function.iterate_succ_apply]
      split_ifs with h
      · rw [show lawStep v μ=compressionStepAuto μ v h from dite_eq_left h,ih]
      · have he : lawStep v μ=μ := dite_eq_right h
        rw [he,Function.iterate_fixed he]

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_RationalFeatureProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function

def scaledRows (x : QData) : Rows :=
  let columns := MatrixList.transpose (0:ℚ) (x.1,x.2.2)
  let is := columns.map IntegerList.numerators
  MatrixList.transpose (0:ℤ) (x.2.1.2,is)

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_CompressionBinaryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Polynomial

def Input.compressed (I : Input) : LawData :=
  let ν := compressStepsAuto I.v I.n I.μ
  (ν.denominator,List.ofFn ν.numerator)

def RationalInput.compressed (I : RationalInput) : LawData :=
  ( (I.μ.compressAuto I.v).denominator, List.ofFn (I.μ.compressAuto I.v).numerator)

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

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

theorem branch_denominator (μ : IntegerLaw (Fin n)) (p : Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (L : ℕ)
    (hden : ∀ i, ((p i).den:ℤ) ≤ (2:ℤ)^L) :
    (branch μ p hp).denominator ≤ μ.denominator*(2:ℤ)^(L*n) := by
  apply mul_le_mul_of_nonneg_left _ μ.denominator_pos.le
  simpa only [Fintype.card_fin] using RationalScaling.denominator_bound p L hden

end MetricKMedian.IntegerBranching

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseIntegerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
open Finset

namespace SparseIntegerLaw
variable {α : Type}

theorem trim_moment (μ : SparseIntegerLaw α) (f : α → ℚ) :
    μ.trim.moment f=μ.moment f := by
  unfold moment
  change (∑ i : Fin μ.law.support.card,
    μ.law.trim.rational.weight i * f ((Vector.ofFn (fun k =>
      μ.states[(μ.law.support.orderEmbOfFin rfl k).val]))[i.val])) = _
  simp only [Vector.getElem_ofFn]
  convert μ.law.trim_moment (fun i => f μ.states[i.val]) using 1
  all_goals try with_reducible_and_instances rfl

end SparseIntegerLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBranchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function
variable {α γ : Type}

theorem branchLaw_ofFn {n : ℕ} (μ : IntegerLaw (Fin n)) (p : Fin n → ℚ)
    (hp : ∀ i, 0≤p i ∧ p i≤1) :
    branchLawData ((μ.denominator,List.ofFn μ.numerator),List.ofFn p)=
      ((IntegerBranching.branch μ p hp).denominator,
        List.ofFn ((IntegerBranching.branch μ p hp).reindex finProdFinEquiv).numerator) := by
  simp only [branchLawData,IntegerList.denominator_ofFn,IntegerList.numerators_ofFn,
    Gaussian.ListOperation.zip_ofFn,List.flatMap_def,List.map_ofFn,Function.comp_def]
  congr 1
  rw [show ((IntegerBranching.branch μ p hp).reindex finProdFinEquiv).numerator=
    (fun i => μ.numerator (finProdFinEquiv.symm i).1 *
      IntegerBranching.branchNumerator p (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) from by
      funext i; simp only [IntegerLaw.reindex,IntegerBranching.branch,Vector.getElem_ofFn]]
  rw [two_expand (fun i b => μ.numerator i * IntegerBranching.branchNumerator p i b)]
  simp only [IntegerBranching.branchNumerator,show (1:Fin 2)≠0 from by decide,ite_true,ite_false]

end MetricKMedian.SparseIntegerLaw.BinarySparse
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
open Binary Binary.PolyProgram Function
abbrev Context.encode (c : Context) := encodePair qr Nat.bits c.raw

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_InstanceDataProgram
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
end MetricKMedian.InstanceProgram
end

end OAI
end


