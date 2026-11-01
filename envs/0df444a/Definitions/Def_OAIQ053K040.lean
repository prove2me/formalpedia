-- Prove2me | Definitions.Def_OAIQ053K040
-- name    : OAIQ053K040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:02:52.523959+00:00
-- url     : https://prove2.me/theorems/28638dda-8c94-4d90-b2f9-4aabaabca98f
-- title:
--   Definitions bundle OAIQ053K040 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 27 definitions and 21 theorems. The definitions and types are `OAI.MetricKMedian.Coverage.Raw.bitsProgram`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.Input.ctx`, `OAI.MetricKMedian.Gaussian.IntegerProgram.Input.encode`, `OAI.MetricKMedian.Gaussian.IntegerProgram.ed`, `OAI.MetricKMedian.Gaussian.IntegerProgram.em`, `OAI.MetricKMedian.Gaussian.IntegerProgram.er`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.RationalInput.features`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.RationalInput.integer`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.RationalInput.lawData`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.RationalInput.raw`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.scaledRows`, `OAI.MetricKMedian.IntegerLaw.ListOperation.Input.encode`, `OAI.MetricKMedian.IntegerLaw.ListOperation.ed`, `OAI.MetricKMedian.IntegerLaw.ListOperation.ee`, `OAI.MetricKMedian.IntegerLaw.ListOperation.ees`, `OAI.MetricKMedian.IntegerLaw.ListOperation.em`, `OAI.MetricKMedian.IntegerLaw.ListOperation.er`, `OAI.MetricKMedian.LPBinary.Input.raw`, `OAI.MetricKMedian.Preparation.RationalBundles.suppliers`, `OAI.MetricKMedian.Preparation.RationalUnitInput.suppliers`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.Input.taper`, `OAI.MetricKMedian.RoundingProgram.State.compressionInput`, `OAI.MetricKMedian.SparseBernoulli.Program.Context.encode`, `OAI.MetricKMedian.SparseBernoulli.Program.Input.start`, `OAI.MetricKMedian.SparseBernoulli.Program.State`, `OAI.MetricKMedian.SparseGraph.Program.Input.start`, `OAI.MetricKMedian.SparseGraph.Program.State.increment`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Compression_AffineListOperations`, `KMedian_Compression_GaussianInputBounds`, `KMedian_Compression_GaussianListRun`, `KMedian_Compression_GaussianListSize`, `KMedian_Compression_GaussianResidualHeight`, `KMedian_Compression_GaussianStates`, `KMedian_Compression_IntegerKernelProgram`, `KMedian_Geometry_RationalGeometryScan`, `KMedian_Geometry_RationalParameterizedHistory`, `KMedian_Geometry_RationalUnitInput`, `KMedian_Geometry_RationalUnitScan`, `KMedian_Hardness_Encoding`, `KMedian_Optimization_LPBinaryInput`, `KMedian_Probability_BernoulliRunProgram`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Process_CopyGraphProgram`, `KMedian_Process_CopyListEncoding`, `KMedian_Process_RoundingUniformStep`, `KMedian_Programs_GraphRunProgram`, `KMedian_Programs_GraphStepProgram`, `KMedian_Programs_HistorySelectionProgram`, `KMedian_Programs_RationalFeatureProgram`, `KMedian_Sparse_SparseMapBind`, `KMedian_Sparse_SparseSupport`.
--
--   **Imports.** It imports the bundles `OAIQ053K029`, `OAIQ053K030`, `OAIQ053K031`, `OAIQ053K032` and `OAIQ053K033` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K045`, `OAIQ053K046` and `OAIQ053K047`; the proofs of `OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation_s53` and `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K029
import Definitions.Def_OAIQ053K030
import Definitions.Def_OAIQ053K031
import Definitions.Def_OAIQ053K032
import Definitions.Def_OAIQ053K033

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianResidualHeight
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianStates
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

end MetricKMedian.Gaussian
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListSize
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianInputBounds
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

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListRun
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_IntegerKernelProgram
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_AffineListOperations
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

abbrev Input.encode (I : Input) := ed I.raw

end MetricKMedian.IntegerLaw.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSupport
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
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
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalParameterizedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                    
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)

theorem taperAt_pos (t : ℕ) : 0 < (q.taperAt t:ℝ) := by
  unfold taperAt
  split_ifs with ht
  · exact q.taper_pos _
  · norm_num

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalGeometryScan
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalBundles
open Finset SupplierStars RationalSuppliers
variable {f n j : ℕ} {X : Type} [PseudoMetricSpace X]

 theorem valid (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ)
    (s : Fin n → X) (i : Fin f → X)
    (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ) (V : Fin n → ℚ) (M δ : ℚ)
    (hd : ∀ t u, dist (s t) (s u)=(d t u:ℝ))
    (hdi : ∀ t a, dist (s t) (i a)=(di t a:ℝ))
    (hy : ∀ a, 0 < y a) (hM : 0 < M) (hδ : 0 < δ) (hδ1 : (δ:ℝ) < 1/2)
    (hθ : 1/((M:ℝ)*(δ:ℝ)) ≤ 1/8)
    (hu : ∀ t, ∑ a ∈ F t, y a=1)
    (hv : ∀ t, ∑ a ∈ F t, y a*di t a=V t)
    (hs : ∀ t u, t ≠ u → M*max (V t) (V u) < d t u) :
    let P := bundle d di F δ;
    let A := missing d di F δ;
    (∀ t, 0 < mass y P t) ∧ Pairwise (fun t u => Disjoint (P t) (P u)) ∧
    (∀ t, 0 ≤ mass y A t) ∧ (∀ t, mass y A t ≤ 1/8) ∧
    (∀ t, mass y P t+mass y A t=1) := by
  intro P A
  let G := geometry F y s i d di V M δ hd hdi hy hM hδ hδ1 hu hv hs
  have hc : ∀ t, (mass y A t:ℝ) ≤ 1/8 := fun t => (G.small t).trans hθ
  have hu' : ∀ t, (mass y P t:ℝ)+(mass y A t:ℝ)=1 := G.unit
  refine ⟨?_,G.disjoint,?_,?_,?_⟩
  · intro t
    have h := hc t
    have h' := hu' t
    have hp : (0:ℝ) < mass y P t := by linarith only [h,h']
    exact_mod_cast hp
  · intro t
    have h := G.nonneg t
    change (0:ℝ) ≤ (mass y A t:ℝ) at h
    exact_mod_cast h
  · intro t
    apply (Rat.cast_le (K:=ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hc t
  · intro t
    exact_mod_cast hu' t

def suppliers (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ)
    (s : Fin n → X) (i : Fin f → X)
    (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ) (V : Fin n → ℚ) (M δ γ : ℚ)
    (hd : ∀ t u, dist (s t) (s u)=(d t u:ℝ))
    (hdi : ∀ t a, dist (s t) (i a)=(di t a:ℝ))
    (hy : ∀ a, 0 < y a) (hM : 0 < M) (hδ : 0 < δ) (hδ1 : (δ:ℝ) < 1/2)
    (hθ : 1/((M:ℝ)*(δ:ℝ)) ≤ 1/8) (hγ : 0<γ) (hγ1 : γ≤1)
    (hu : ∀ t, ∑ a ∈ F t, y a=1)
    (hv : ∀ t, ∑ a ∈ F t, y a*di t a=V t)
    (hs : ∀ t u, t ≠ u → M*max (V t) (V u) < d t u) : RationalSuppliers.Data f n :=
  let h := valid F y s i d di V M δ hd hdi hy hM hδ hδ1 hθ hu hv hs
  {y:=y, P:=bundle d di F δ, A:=missing d di F δ,
   p:=mass y (bundle d di F δ), c:=mass y (missing d di F δ), γ:=γ,
   hy:=fun a => (hy a).le, hp:=h.1, hP:=h.2.1, hm:=fun _ => rfl, hc:=fun _ => rfl,
   hc0:=h.2.2.1, hc1:=h.2.2.2.1, hunit:=h.2.2.2.2,hγ:=hγ,hγ1:=hγ1}

end MetricKMedian.Preparation.RationalBundles
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalUnitInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Preparation
open Finset

namespace RationalUnitInput
variable {f j : ℕ} (U : RationalUnitInput f j)

theorem representative_separation (M : ℚ) (hM : 0≤M) :
    ∀ t u, t≠u → M*max (U.V (U.ridx M t)) (U.V (U.ridx M u)) <
      U.dd (U.ridx M t) (U.ridx M u) := by
  intro t u htu
  have hh := (RationalRepresentatives.representatives_spec U.dd U.V M U.hdd U.hsymm hM U.V_nonneg).1
  exact hh ((U.representatives M).orderEmbOfFin_mem rfl t)
    ((U.representatives M).orderEmbOfFin_mem rfl u)
    (fun h => htu ((U.representatives M).orderEmbOfFin rfl |>.injective h))

end RationalUnitInput
end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalUnitScan
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
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Encoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Binary Binary.Automatic Binary.Automatic.Poly

namespace Raw

noncomputable def bitsProgram : PolyProgram Nat.bits (Binary.encodeList Binary.encodeBool) Nat.bits :=
  BooleanLists.packProgram.recode Nat.bits (fun _ => rfl) (fun _ => rfl)

end Raw

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPBinaryInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Polynomial Finset

namespace Input
def raw (I : Input) : Rows × ℕ := (I.rows,I.k)
end Input

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_RationalFeatureProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function

def RationalInput.lawData (I : RationalInput) : LawData := (I.μ.denominator,List.ofFn I.μ.numerator)
def RationalInput.features (I : RationalInput) : QRows := List.ofFn (fun i => List.ofFn (I.v i))
def RationalInput.raw (I : RationalInput) : QData := (List.replicate I.d (),(I.lawData,I.features))

def scaledRows (x : QData) : Rows :=
  let columns := MatrixList.transpose (0:ℚ) (x.1,x.2.2)
  let is := columns.map IntegerList.numerators
  MatrixList.transpose (0:ℤ) (x.2.1.2,is)

theorem scaledRows_raw (I : RationalInput) : scaledRows I.raw=
    List.ofFn (fun i => List.ofFn (RationalLaw.scaledFeatures I.v i)) := by
  unfold scaledRows RationalInput.raw RationalInput.features RationalInput.lawData
  rw [MatrixList.transpose_ofFn _ _ (List.length_replicate ..)]
  simp only [List.map_ofFn,Function.comp_def,IntegerList.numerators_ofFn]
  rw [MatrixList.transpose_ofFn _ _ (List.length_ofFn ..)]
  congr 1
  funext i
  congr 1
  funext j
  exact (RationalLaw.scaledFeatures_eq I.v i j).symm

def RationalInput.integer (I : RationalInput) : Input := ⟨I.n,I.d,I.μ,RationalLaw.scaledFeatures I.v⟩

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingUniformStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse

def State.compressionInput {s : Bool} (x : State s) : IntegerLaw.BinaryCompression.RationalInput :=
  ⟨x.μ.length,x.n+x.n*x.n,x.μ.law,fun i => SparseWeightedPartial.features x.μ.states[i.val]⟩

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram
abbrev Context.encode (c : Context) := encodePair qr Nat.bits c.raw
abbrev State := Bundle T

end MetricKMedian.SparseBernoulli.Program
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
def Input.start (x : Input) : State := ⟨⟨x,0⟩,.dirac (fun _ => false)⟩

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyListEncoding
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.RationalPhysicalKernel.CopyList
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
variable {f Δ : ℕ}
 local instance instLinearOrderCopyFin_r345b78_1 : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
theorem enum_rank_strictMono (A : Finset (CopyState.Copy (F:=Fin f) Δ)) :
    StrictMono (fun i => (rank (enumeration A i).val).val) := by
  intro i j hij
  apply rank_strictMono
  exact @OrderIso.strictMono _ _ _ (activeOrder A).toPreorder
    (@Fintype.orderIsoFinOfCardEq A (activeOrder A) _ _ (Fintype.card_coe A)) i j hij
 theorem ordinal_enum (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : (ordinal A).toEquiv=enumeration A := rfl

end MetricKMedian.RationalPhysicalKernel.CopyList
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphStepProgram
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

def State.increment (x : State) : State := ⟨⟨x.ctx.input,x.ctx.t+1⟩,x.law⟩
end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table et)
def Input.start (x : Input) : State := ⟨⟨x,0⟩,.dirac (fun _ => ∅)⟩

end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyGraphProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open CopyList

local instance instLinearOrderCopyFin_r345b78_2 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.instLinearOrderSubtypeCopyFinMemFinset
def Input.taper (x : Input) : TaperGraphProgram.Input where
  n := x.A.card
  d := fun i h => x.d (enumeration x.A i).val.1 (enumeration x.A h).val.1
  own := fun i => (own x.A (enumeration x.A i)).map (enumeration x.A).symm.toEmbedding
  g := x.g
  P := x.P
  Δ := x.Δ
  positive := x.positive

 theorem taper_q (x : Input) : x.taper.qInput.q =
    (fun h i => Taper.sourceMarginals x.g x.P (fun a : x.A => x.d (enumeration x.A i).val.1 a.val.1)
      (own x.A (enumeration x.A i)) x.Δ (enumeration x.A h)) := by
  funext h i
  let e := ordinal x.A
  have hm : ((own x.A (enumeration x.A i)).map (enumeration x.A).symm.toEmbedding).map e.toEquiv.toEmbedding =
      own x.A (enumeration x.A i) := by
    rw [ordinal_enum]
    ext a
    simp only [mem_map_equiv,Equiv.symm_symm,Equiv.apply_symm_apply]
  have hh := Taper.source_reindex e x.g x.P (fun a : x.A => x.d (enumeration x.A i).val.1 a.val.1)
    ((own x.A (enumeration x.A i)).map (enumeration x.A).symm.toEmbedding) x.Δ h
  rw [hm] at hh
  exact hh.symm

end MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseMapBind
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.SparseIntegerLaw
variable {α β γ : Type}
 theorem map_bindIndexed (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β) (f : β → γ) :
    (μ.bindIndexed κ).map f=μ.bindIndexed (fun i => (κ i).map f) := by
  unfold map bindIndexed
  congr 1
  ext i hi
  simp only [Vector.getElem_map,Vector.getElem_ofFn]
end MetricKMedian.SparseIntegerLaw
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_HistorySelectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open RationalPhysicalKernel
variable {τ : ℝ} (q : RationalParameters τ)

def Input.ctx (x : Input q) : UpdateProgram.Context where
  f := x.f
  Δ := q.Δ
  d := x.d₀
  g := q.g
  P := 1
  positive := by norm_num
  A := x.A
  β := q.β
  p := q.probabilityQ
  φ := q.φ
  hp := q.probabilityQ_pos.le
  hφ := by exact_mod_cast q.φpos.le
  hupper := q.probabilityQ_le

end MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
end

end OAI
end


