-- Prove2me | Definitions.Def_OAIQ035K015
-- name    : OAIQ035K015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:55:11.827997+00:00
-- url     : https://prove2.me/theorems/05f8cba1-5712-4b1f-a41c-8f62a87b7f61
-- title:
--   Definitions bundle OAIQ035K015 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 45 declarations of OpenAI's Lean: 25 definitions, 1 instance and 19 theorems. The definitions and types are `OAI.MetricKMedian.Binary.BooleanLists.pack`, `OAI.MetricKMedian.Binary.BooleanLists.unpack`, `OAI.MetricKMedian.Binary.PolyProgram.boolOr`, `OAI.MetricKMedian.Binary.PolyProgram.stock`, `OAI.MetricKMedian.Binary.Repeat.enc`, `OAI.MetricKMedian.Binary.WordTransducer.listBits`, `OAI.MetricKMedian.CopyState.State`, `OAI.MetricKMedian.CopyState.Valid`, `OAI.MetricKMedian.CopyState.forcedAlive`, `OAI.MetricKMedian.CopyState.forcedGroups`, `OAI.MetricKMedian.CopyState.next`, `OAI.MetricKMedian.CopyState.roundErased`, `OAI.MetricKMedian.FiniteComparison.G`, `OAI.MetricKMedian.FiniteComparison.L`, `OAI.MetricKMedian.FiniteComparison.M`, `OAI.MetricKMedian.FiniteComparison.k`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Rows`, `OAI.MetricKMedian.RoundingList.down`, `OAI.MetricKMedian.RoundingList.endpoint`, `OAI.MetricKMedian.RoundingList.move`, `OAI.MetricKMedian.RoundingList.probability`, `OAI.MetricKMedian.RoundingList.ratio`, `OAI.MetricKMedian.RoundingList.second`, `OAI.MetricKMedian.RoundingList.up`, `OAI.MetricKMedian.Taper.ListOperation.radius`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Analysis_FiniteAverages`, `KMedian_Binary_BinaryBooleanLists`, `KMedian_Binary_BinaryDyadicPowers`, `KMedian_Binary_BinaryFloor`, `KMedian_Binary_BinaryListExtras`, `KMedian_Binary_BinaryRepeat`, `KMedian_Binary_BooleanFinite`, `KMedian_Binary_BooleanMachine`, `KMedian_Binary_BooleanPolynomial`, `KMedian_Compression_CompressionListStep`, `KMedian_Compression_DependentIntegerKernel`, `KMedian_Compression_FinsetVectorExtension`, `KMedian_Compression_RationalOperationHeight`, `KMedian_Process_CopyRound`, `KMedian_Process_CopyState`, `KMedian_Process_CopyTransport`, `KMedian_Process_PhysicalRound`, `KMedian_Process_PhysicalState`, `KMedian_Process_RoundingListOperations`, `KMedian_Process_StateInvariants`, `KMedian_Process_TaperListProgram`, `KMedian_Programs_GreedyPackingProgram`, `KMedian_Sparse_SparseIterationHeight`.
--
--   **Imports.** It imports the bundles `OAIQ035K000`, `OAIQ035K001`, `OAIQ035K002`, `OAIQ035K003` and `OAIQ035K004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K028`, `OAIQ035K029`, `OAIQ035K030`, `OAIQ035K031`, `OAIQ035K032` and `OAIQ035K038`; the statements `OAI.MetricKMedian.CopyState.round_backup`, `OAI.MetricKMedian.CopyState.round_cap`, `OAI.MetricKMedian.CopyState.unbalanced_count_change`, `OAI.MetricKMedian.CopyState.unbalanced_small_change` and `OAI_MetricKMedian_SparseBernoulli_count_variance`; the proofs of `OAI.MetricKMedian.Completion.Rational.output_potential`, `OAI.MetricKMedian.CopyState.round_backup`, `OAI.MetricKMedian.CopyState.round_cap`, `OAI.MetricKMedian.CopyState.unbalanced_count_change` and `OAI.MetricKMedian.CopyState.unbalanced_small_change`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K001
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K003
import Definitions.Def_OAIQ035K004

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

noncomputable def k (p : ℝ) (s : Bool) : ℝ := if s then 0 else kZero p
noncomputable def L (p m z : ℝ) (b : Bool → ℝ) (s : Bool) (r : ℝ) : ℝ :=
  (C p s - m - b s) * r + (2 / 5) * z
noncomputable def M (p a : ℝ) (s : Bool) (r : ℝ) : ℝ :=
  (1 - r) * a + C p s * p * r
noncomputable def G (p m a z : ℝ) (b : Bool → ℝ) (s : Bool) (r : ℝ) : ℝ :=
  M p a s r - L p m z b s r

end MetricKMedian.FiniteComparison


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Turing StateTransition Function Finset

attribute [instance] Machine.decK Machine.finK Machine.finLabel Machine.finState

namespace Machine

instance allWorkFinite (M : Machine) (k : M.tm.K) : Fintype (M.tm.Γ k) :=
  inferInstanceAs (Fintype Bool)

end Machine

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Turing Polynomial

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
variable {f : α → β} {g : β → γ}

def stock (P : PolyProgram ea eb f) : TM2ComputableInPolyTime ea eb f where
  tm := P.machine.tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := P.time
  outputsFun a := by
    have h := P.outputs a
    dsimp only [Machine.tm,Equiv.refl] at h ⊢
    simpa only [List.map_id] using h

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryBooleanLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Binary
namespace BooleanLists
def pack : Transducer where
  Q := Unit
  initial := ()
  next := fun _ b => ((),[true,b,false])
  finish := fun _ => []
def unpack : Transducer where
  Q := Phase
  initial := .start
  next := fun q b => match q with
    | .start => (.value,[])
    | .value => (.stop,[b])
    | .stop => (.start,[])
  finish := fun _ => []
end BooleanLists
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Finset

namespace PolyProgram

noncomputable def boolOr : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => x.1 || x.2) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_DependentIntegerKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix

theorem small_integer_dependence_of_dependent {R Ω : Type} [Fintype R] [Fintype Ω]
    (V : Matrix R Ω ℤ) (L : ℕ) (hV : ∀ r i, |V r i| ≤ (2:ℤ)^L)
    (hdep : ¬ LinearIndependent ℚ (fun i r => (V r i:ℚ))) :
    ∃ (K : Type) (inst : Fintype K), letI := inst;
      ∃ (a : K → Ω) (z : K → ℤ), Function.Injective a ∧
        Fintype.card K ≤ Fintype.card R+1 ∧ (∃ k, z k ≠ 0) ∧
        (∀ k, |z k| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L))) ∧
        ∀ r, ∑ k, z k*V r (a k)=0 := by
  classical
  let v : Ω → R → ℚ := fun i r => V r i
  obtain ⟨κ,a,ha,hspan,hi⟩ := exists_linearIndependent' ℚ v
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ ≤ Fintype.card R := by
    simpa using hi.fintype_card_le_finrank
  have hns : ¬ Function.Surjective a := by
    intro hs
    apply hdep
    let e := Equiv.ofBijective a ⟨ha,hs⟩
    have hh := hi.comp e.symm e.symm.injective
    have he : (v ∘ a) ∘ e.symm=v := by
      funext i
      change v (e (e.symm i))=v i
      rw [e.apply_symm_apply]
    rw [he] at hh
    exact hh
  simp only [Function.Surjective,not_forall,not_exists] at hns
  obtain ⟨w,hw⟩ := hns
  let A : Matrix R κ ℤ := fun r c => V r (a c)
  let wv : R → ℤ := fun r => V r w
  let B := A.transpose*A
  let D := B.det
  let b := B.cramer (A.transpose*ᵥwv)
  have hAi : LinearIndependent ℚ (fun c r => (A r c:ℚ)) := hi
  have hwm : (fun r => (wv r:ℚ)) ∈ Submodule.span ℚ (Set.range (fun c r => (A r c:ℚ))) := by
    change v w ∈ Submodule.span ℚ (Set.range (v ∘ a))
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self w)
  have hD : D ≠ 0 := gram_det_ne_zero A hAi
  have heq : ∀ r, (A*ᵥb) r=D*wv r := gram_span_relation A wv hAi hwm
  have hbnd := gram_coefficient_bit_bound (Fintype.card R) (Fintype.card κ) L hcard
  have hAb : ∀ r c, |A r c| ≤ (2:ℤ)^L := fun r c => hV r (a c)
  have hwv : ∀ r, |wv r| ≤ (2:ℤ)^L := fun r => hV r w
  have hDb : |D| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L)) :=
    (gram_det_bound A _ (by positivity) hAb).trans hbnd
  have hbb : ∀ c, |b c| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L)) :=
    fun c => (gram_cramer_bound A wv _ (by positivity) hAb hwv c).trans hbnd
  let a' : Option κ → Ω := fun k => k.elim w a
  let z : Option κ → ℤ := fun k => k.elim D (fun c => -b c)
  refine ⟨Option κ,inferInstance,a',z,?_,?_,⟨none,hD⟩,?_,?_⟩
  · intro c d he
    cases c with
    | none =>
      cases d with
      | none => rfl
      | some d => exact False.elim (hw d he.symm)
    | some c =>
      cases d with
      | none => exact False.elim (hw c he)
      | some d => exact congrArg some (ha he)
  · simp only [Fintype.card_option]
    omega
  · intro k
    cases k with
    | none => exact hDb
    | some c => simpa only [z,Option.elim_some,abs_neg] using hbb c
  · intro r
    rw [Fintype.sum_option]
    change D*wv r+(∑ c, (-b c)*A r c)=0
    have hh := heq r
    change (∑ c, A r c*b c)=D*wv r at hh
    simp only [neg_mul,sum_neg_distrib,mul_comm (b _) (A _ _)]
    rw [hh]
    ring

theorem full_integer_kernel_of_dependent {R Ω : Type} [Fintype R] [Fintype Ω]
    (V : Matrix R Ω ℤ) (L : ℕ) (hV : ∀ r i, |V r i| ≤ (2:ℤ)^L)
    (hdep : ¬ LinearIndependent ℚ (fun i r => (V r i:ℚ))) :
    ∃ z : Ω → ℤ, (∃ i, z i ≠ 0) ∧
      (∀ i, |z i| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L))) ∧
      ∀ r, ∑ i, z i*V r i=0 := by
  classical
  obtain ⟨K,inst,a,z,ha,_,hne,hbound,hker⟩ := small_integer_dependence_of_dependent V L hV hdep
  let zz : Ω → ℤ := fun i => ∑ k, if a k=i then z k else 0
  have hzval : ∀ k, zz (a k)=z k := by
    intro k
    simp only [zz,ha.eq_iff]
    simpa only [mem_univ,ite_true] using sum_ite_eq' univ k z
  have hzout : ∀ i, (¬∃ k, a k=i) → zz i=0 := by
    intro i hi
    apply sum_eq_zero
    intro k _
    exact ite_eq_right (fun hk => hi ⟨k,hk⟩)
  refine ⟨zz,?_,?_,?_⟩
  · obtain ⟨k,hk⟩ := hne
    exact ⟨a k,by rwa [hzval]⟩
  · intro i
    by_cases hi : ∃ k, a k=i
    · obtain ⟨k,rfl⟩ := hi
      rw [hzval]
      exact hbound k
    · rw [hzout i hi,abs_zero]
      positivity
  · intro r
    change (∑ i, (∑ k, if a k=i then z k else 0)*V r i)=0
    simp only [sum_mul,ite_mul,zero_mul]
    rw [sum_comm]
    simpa using hker r

end MetricKMedian.Compression

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_RationalOperationHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Binary
open Finset

namespace HasHeight
variable {q r : ℚ} {L M : ℕ}

 theorem zero (L : ℕ) : HasHeight 0 L := by
  constructor
  · simp
  · simp only [Rat.den_zero,Int.natCast_one]
    exact one_le_pow₀ (by norm_num)

 theorem one (L : ℕ) : HasHeight 1 L := by
  constructor <;> simp only [Rat.num_one,Rat.den_one,abs_one,Int.natCast_one] <;>
    exact one_le_pow₀ (by norm_num)

 theorem neg (h : HasHeight q L) : HasHeight (-q) L := by
  simpa only [HasHeight,Rat.num_neg_eq_neg_num,Rat.den_neg_eq_den,abs_neg] using h

 theorem inv (hq : HasHeight q L) : HasHeight q⁻¹ L := by
  by_cases hq0 : q=0
  · rw [hq0,inv_zero]
    exact zero L
  have hqn : q.num ≠ 0 := by
    intro h
    apply hq0
    rw [← Rat.num_div_den q,h,Int.cast_zero,zero_div]
  have hh := Gaussian.ratio_num_den_bound (q.den:ℤ) q.num hqn ((2:ℤ)^L)
    (by simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using hq.2) hq.1
  have he : ((q.den:ℤ):ℚ)/(q.num:ℚ)=q⁻¹ := by
    conv_rhs => rw [← Rat.num_div_den q]
    simp only [inv_div,Int.cast_natCast]
  rwa [he] at hh

 theorem div (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q/r) (L+M) := by
  simpa only [div_eq_mul_inv] using hq.mul hr.inv

 theorem add (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q+r) (L+M+1) := by
  have hdq : (q.den:ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hdr : (r.den:ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hterm₁ : |q.num*(r.den:ℤ)| ≤ (2:ℤ)^(L+M) := by
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),pow_add]
    exact mul_le_mul hq.1 hr.2 (by positivity) (by positivity)
  have hterm₂ : |r.num*(q.den:ℤ)| ≤ (2:ℤ)^(L+M) := by
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),Nat.add_comm L M,pow_add]
    exact mul_le_mul hr.1 hq.2 (by positivity) (by positivity)
  have hh := Gaussian.ratio_num_den_bound (q.num*r.den+r.num*q.den) ((q.den:ℤ)*r.den)
    (mul_ne_zero hdq hdr) ((2:ℤ)^(L+M+1)) (by
      have hab := abs_add_le (q.num*(r.den:ℤ)) (r.num*(q.den:ℤ))
      rw [pow_succ]
      linarith) (by
      rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),abs_of_nonneg (Int.natCast_nonneg _)]
      have hb : (q.den:ℤ)*r.den ≤ (2:ℤ)^(L+M) := by
        rw [pow_add]
        exact mul_le_mul hq.2 hr.2 (by positivity) (by positivity)
      exact hb.trans (pow_le_pow_right₀ (by norm_num) (by omega)))
  have he : ((q.num*r.den+r.num*q.den:ℤ):ℚ)/(((q.den:ℤ)*r.den:ℤ):ℚ)=q+r := by
    push_cast
    rw [add_div, mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr r.den_ne_zero),
      mul_comm (r.num:ℚ) (q.den:ℚ),mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr q.den_ne_zero),
      Rat.num_div_den,Rat.num_div_den]
  rwa [he] at hh

 theorem sub (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q-r) (L+M+1) := by
  simpa only [sub_eq_add_neg] using hq.add hr.neg

end HasHeight
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace WordTransducer

def listBits : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((),[true,b,false])
  finish _ := []
end WordTransducer
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryDyadicPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Binary
open Function Polynomial PolyProgram
namespace Dyadic

theorem height_pow (i : ℕ) : HasHeight ((2:ℚ)^i) i := by
  induction i with
  | zero => simpa using HasHeight.one 0
  | succ i ih =>
      rw [pow_succ]
      exact ih.mul (by norm_num [HasHeight])
end Dyadic
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryFloor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.Binary.Automatic.Poly
 theorem natFloor_eq (q : ℚ) : ⌊q⌋₊=if q<0 then 0 else q.num.natAbs/q.den := by
  by_cases h : q<0
  · simp only [ite_eq_left h,Nat.floor_of_nonpos h.le]
  · rw [ite_eq_right h]
    have hn : 0≤q.num := Rat.num_nonneg.mpr (le_of_not_gt h)
    have he : ((q.num.natAbs:ℕ):ℚ)/(q.den:ℚ)=q := by
      rw [← Int.cast_natCast,Int.natCast_natAbs,abs_of_nonneg hn,Rat.num_div_den]
    calc
      ⌊q⌋₊=⌊((q.num.natAbs:ℕ):ℚ)/(q.den:ℚ)⌋₊ := congrArg Nat.floor he.symm
      _ = _ := Rat.natFloor_natCast_div_natCast _ _
end MetricKMedian.Binary.Automatic.Poly
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryRepeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace Repeat
variable {α : Type}
abbrev enc (ea : α → List Bool) := encodePair Nat.bits ea

theorem run (ea : α → List Bool) (f : α → α) (N A n : ℕ) (a : α)
    (hn : n≤N) (ha : ∀ i≤n, (ea (f^[i] a)).length≤A) :
    BoundedRun (enc ea) (body f) (2*(N+1)+1+A) (n+1) (n,a) (f^[n] a) := by
  induction n generalizing a with
  | zero =>
      have has : (ea a).length≤A := by simpa using ha 0 (Nat.zero_le _)
      have hsize : (enc ea (0,a)).length ≤ 2*(N+1)+1+A := by
        simp only [enc,encodePair_length,Nat.zero_bits,List.length_nil]; omega
      exact BoundedRun.stop hsize (by simp [body])
  | succ n ih =>
      have hnl : (n+1).bits.length≤N+1 := (NatBinary.length_le_height (Nat.lt_two_pow_self.le)).trans (by omega)
      have has : (ea a).length≤A := by simpa using ha 0 (Nat.zero_le _)
      have hsize : (enc ea (n+1,a)).length ≤ 2*(N+1)+1+A := by
        simp only [enc,encodePair_length]; omega
      have hh := ih (f a) (by omega) (fun i hi => by
        simpa only [Function.iterate_succ_apply] using ha (i+1) (by omega))
      simpa only [Function.iterate_succ_apply] using
        (BoundedRun.step hsize (by simp [body]) hh)
end Repeat

end MetricKMedian.Binary
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

theorem extendVector_at {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ)
    (i : Fin s.card) : extendVector s z ((s.orderIsoOfFin rfl) i).val=z i := by
  have hi := ((s.orderIsoOfFin rfl) i).property
  simp only [extendVector,dite_eq_left hi]
  congr 1
  exact (s.orderIsoOfFin rfl).symm_apply_apply i

theorem extendVector_zero {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ)
    (i : Fin n) (hi : i ∉ s) : extendVector s z i=0 := dite_eq_right hi

theorem extendVector_sum {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ)
    (g : Fin n → ℤ) :
    (∑ i, extendVector s z i*g i)=∑ j, z j*g ((s.orderIsoOfFin rfl) j).val := by
  let e := (s.orderIsoOfFin rfl).toEquiv
  calc
    _ = ∑ i ∈ s, extendVector s z i*g i := by
      symm
      apply sum_subset (subset_univ _)
      intro i _ hi
      rw [extendVector_zero s z i hi,zero_mul]
    _ = ∑ i : s, extendVector s z i.val*g i.val := by
      exact (sum_coe_sort s (fun i => extendVector s z i*g i)).symm
    _ = ∑ j, extendVector s z (e j).val*g (e j).val := (e.sum_comp _).symm
    _ = _ := by
      apply sum_congr rfl
      intro j _
      rw [show extendVector s z (e j).val=z j from extendVector_at s z j]
      rfl

theorem extendVector_bound {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ)
    (H : ℤ) (hH : 0 ≤ H) (hz : ∀ j, |z j| ≤ H) (i : Fin n) :
    |extendVector s z i| ≤ H := by
  by_cases hi : i ∈ s
  · simp only [extendVector,dite_eq_left hi]; exact hz _
  · rw [extendVector_zero s z i hi,abs_zero]; exact hH

end MetricKMedian.Compression

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
abbrev Rows := Binary.IntegerList.Rows

end MetricKMedian.IntegerLaw.BinaryCompression
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

variable [Fintype F]

def next (A erased : Finset (Copy (F := F) Δ)) (O : Finset F) := (A \ erased) ∪ resets Δ O

end MetricKMedian.CopyState
end
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
open Finset FixedBatch
variable {F : Type*} [DecidableEq F] [Fintype F] (Δ : ℕ)

variable {Δ}

noncomputable def roundErased (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) : Finset (Copy (F := F) Δ) :=
  (Z.biUnion (heavyActions (graphActions G) H).erase).image Subtype.val

end MetricKMedian.CopyState
end
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

@[simp] theorem mem_localSet (A S : Finset (Copy (F := F) Δ)) (i : A) :
    i ∈ localSet A S ↔ i.val ∈ S := by simp [localSet]

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F : Type*} [DecidableEq F] [Fintype F] {Δ : ℕ}

noncomputable def forcedGroups (A : Finset (Copy (F := F) Δ)) (H : Finset A) : Finset F :=
  H.image (fun i => i.val.1)

noncomputable def forcedAlive (A S : Finset (Copy (F := F) Δ)) (H : Finset A) : Finset A :=
  (localSet A S).filter (fun i => i.val.1 ∈ forcedGroups A H)

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch Analytic
variable {F J X : Type*} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J]
variable [PseudoMetricSpace X] {Δ : ℕ}

abbrev State (F J : Type*) (Δ : ℕ) := Finset (Copy (F := F) Δ) × (J → Finset (Copy (F := F) Δ))

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
open Binary Binary.Automatic Binary.Automatic.Poly Finset
def second (p : Row) : ℕ := (indices p).findIdx (fun i => frac (p[i]?.getD 0) && decide (i≠first p))
def ratio (β p : Row) : ℚ := β[first p]?.getD 0 / β[second p]?.getD 0

def up (p : Row) (i j : ℕ) (r : ℚ) := min (1-p[i]?.getD 0) (p[j]?.getD 0/r)
def down (p : Row) (i j : ℕ) (r : ℚ) := min (p[i]?.getD 0) ((1-p[j]?.getD 0)/r)
def move (p : Row) (i j : ℕ) (r t : ℚ) : Row :=
  (indices p).map (fun k => p[k]?.getD 0+t*((if k=i then 1 else 0)-(if k=j then r else 0)))
def probability (β p : Row) : ℚ :=
  if active p then
    down p (first p) (second p) (ratio β p) /
      (up p (first p) (second p) (ratio β p)+down p (first p) (second p) (ratio β p))
  else 0

def endpoint (β p : Row) (b : Bool) : Row :=
  if active p then move p (first p) (second p) (ratio β p)
    (if b then -down p (first p) (second p) (ratio β p) else up p (first p) (second p) (ratio β p))
  else p

end MetricKMedian.RoundingList
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_StateInvariants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F J X : Type*} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J]
variable [PseudoMetricSpace X] {Δ : ℕ}

def Valid (g : ℝ) (location : F → X) (client : J → X) (R : J → ℝ)
    (S₀ : J → Finset (Copy (F := F) Δ)) (s : State F J Δ) : Prop :=
  1 ≤ mass g s.1 ∧
    (∀ j, s.2 j ⊆ s.1) ∧ (∀ j, s.2 j ⊆ S₀ j) ∧
    ∀ j, (¬∃ f ∈ integral Δ s.1, dist (client j) (location f) ≤ 5*R j) → S₀ j ⊆ s.1

end MetricKMedian.CopyState
end
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
def radius (x : Raw) : ℚ := (roots x).foldl max 0

end MetricKMedian.Taper.ListOperation
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
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
open SparseGraph.ListOperation (Row Table setView indices)
 theorem advance_result (x : Input) (t : ℕ) (s : Cut x) :
    ((advance x)^[t] s).2=s.2 ∪ packing t s.1 x.R x.B := by
  induction t generalizing s with
  | zero => simp only [Function.iterate_zero,Function.id_def,packing,union_empty]
  | succ t ih =>
    rw [Function.iterate_succ_apply,ih]
    by_cases h : s.1.Nonempty
    · simp only [advance,dite_eq_left h,packing]
      ext i
      simp only [mem_union,mem_insert]
      tauto
    · have he : s.1=∅ := not_nonempty_iff_eq_empty.mp h
      simp [advance,he,packing_empty]

end MetricKMedian.Completion.Rational.PackingProgram
end

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
namespace MetricKMedian.Binary.HasHeight
variable {q r : ℚ} {L : ℕ}
theorem min (hq : HasHeight q L) (hr : HasHeight r L) : HasHeight (min q r) L := by
  rcases le_total q r with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]
end MetricKMedian.Binary.HasHeight

end

end OAI
end


