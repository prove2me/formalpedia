-- Prove2me | Definitions.Def_OAIQ035K055
-- name    : OAIQ035K055
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:11:20.229393+00:00
-- url     : https://prove2.me/theorems/38e6b364-af5b-47d0-86f7-9c9e42c51faa
-- title:
--   Definitions bundle OAIQ035K055 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 56 declarations of OpenAI's Lean: 33 definitions and 23 theorems. The definitions and types are `OAI.MetricKMedian.Gaussian.IntegerProgram.kernelProgram`, `OAI.MetricKMedian.IntegerLaw.ListOperation.extendProgram`, `OAI.MetricKMedian.MaskProgram.imageRaw`, `OAI.MetricKMedian.MaskProgram.pullbackMatrix`, `OAI.MetricKMedian.RationalBatchData.Ordinal.graphView`, `OAI.MetricKMedian.RationalBatchData.Ordinal.sets`, `OAI.MetricKMedian.RationalBatchData.ProposalProgram.Input.raw`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.Input.result`, `OAI.MetricKMedian.RoundingProgram.Input.encode`, `OAI.MetricKMedian.RoundingProgram.Input.raw`, `OAI.MetricKMedian.RoundingProgram.State.raw`, `OAI.MetricKMedian.RoundingProgram.branchProgram`, `OAI.MetricKMedian.RoundingProgram.branchRawProgram`, `OAI.MetricKMedian.RoundingProgram.countProgram`, `OAI.MetricKMedian.RoundingProgram.endpoint`, `OAI.MetricKMedian.RoundingProgram.endpointProgram`, `OAI.MetricKMedian.RoundingProgram.probability`, `OAI.MetricKMedian.RoundingProgram.probabilityProgram`, `OAI.MetricKMedian.RoundingProgram.startProgram`, `OAI.MetricKMedian.RoundingProgram.vectorData`, `OAI.MetricKMedian.SparseGraph.Program.Context.encode`, `OAI.MetricKMedian.SparseGraph.Program.Context.raw`, `OAI.MetricKMedian.SparseGraph.Program.Input.encode`, `OAI.MetricKMedian.SparseGraph.Program.Input.raw`, `OAI.MetricKMedian.SparseGraph.Program.InputRaw`, `OAI.MetricKMedian.SparseGraph.Program.QInput.result`, `OAI.MetricKMedian.SparseGraph.Program.State.encode`, `OAI.MetricKMedian.SparseGraph.Program.columnRaw`, `OAI.MetricKMedian.SparseGraph.Program.ei`, `OAI.MetricKMedian.SparseGraph.Program.view`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.branchLawProgram`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.mixData`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.table`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Compression_AffineListCompiler`, `KMedian_Compression_IntegerKernelProgram`, `KMedian_Process_BatchOrdinalArrays`, `KMedian_Process_BatchOrdinalCodes`, `KMedian_Process_BatchProposalProgram`, `KMedian_Process_CopyGraphProgram`, `KMedian_Process_RoundingCoordinateHeight`, `KMedian_Process_RoundingRunHeight`, `KMedian_Process_RoundingRunProgram`, `KMedian_Process_RoundingStateCompiler`, `KMedian_Process_RoundingUniformStep`, `KMedian_Programs_GraphLawProgram`, `KMedian_Programs_GraphStepProgram`, `KMedian_Programs_OriginalMaskProgram`, `KMedian_Rounding_SignedGridInvariant`, `KMedian_Sparse_SparseBindProgram`, `KMedian_Sparse_SparseBranchProgram`, `KMedian_Sparse_SparseMixProgram`, `KMedian_Sparse_SparseTable`, `KMedian_Sparse_SparseWeightedPartial`.
--
--   **Imports.** It imports the bundles `OAIQ035K050`, `OAIQ035K051` and `OAIQ035K052` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K059`, `OAIQ035K060`, `OAIQ035K061`, `OAIQ035K062`, `OAIQ035K063` and `OAIQ035K064`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K050
import Definitions.Def_OAIQ035K051
import Definitions.Def_OAIQ035K052

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

noncomputable def kernelProgram : PolyProgram Input.encode er Input.result :=
  ((rationalProgram.comp ListOperation.kernelProgram).comp IntegerList.numeratorsProgram).congr _ (fun I => by
    simp only [Function.comp_apply,ListOperation.Input.result,ListOperation.kernelList,IntegerList.numerators_ofFn]
    unfold Input.result computedIntegerKernel
    simp only [Vector.getElem_ofFn]
    rfl)
end MetricKMedian.Gaussian.IntegerProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_AffineListCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.IntegerLaw.ListOperation
open Binary Binary.PolyProgram Function

noncomputable def extendProgram : PolyProgram (encodePair (encodeList ez) Nat.bits) Signed.encode
    (fun x : List (ℕ × ℤ) × ℕ => extend x.1 x.2) := by
  let a := fst Nat.bits ez
  let b := (snd Nat.bits ez).comp (fst Nat.bits Signed.encode)
  let test := (b.fanout a).comp natEQ
  let filtered := (exchange (encodeList ez) Nat.bits).comp (test.listFilterWith (0,0) 0)
  exact ((filtered.comp ((snd Nat.bits Signed.encode).listMap (0,0))).comp IntegerList.sumProgram).congr _ (fun _ => rfl)

end MetricKMedian.IntegerLaw.ListOperation
end

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

noncomputable def branchLawProgram :
    PolyProgram (encodePair el (encodeList Ratio.encode)) el branchLawData := by
  let en := encodePair el (encodeList Ratio.encode)
  let law := fst el (encodeList Ratio.encode)
  let probs := snd el (encodeList Ratio.encode)
  let D := probs.comp IntegerList.denominatorProgram
  let nums := law.comp (snd Signed.encode er)
  let zs := probs.comp IntegerList.numeratorsProgram
  let triples := D.fanout ((nums.fanout zs).comp (listZip Signed.encode Signed.encode 0 0))
  let ez := encodePair Signed.encode Signed.encode
  let z := snd Signed.encode ez
  let w := z.comp (fst Signed.encode Signed.encode)
  let a := z.comp (snd Signed.encode Signed.encode)
  let d := fst Signed.encode ez
  let p0 := (w.fanout a).comp intMul
  let p1 := (w.fanout ((d.fanout a).comp intSub)).comp intMul
  let entries := (p0.fanout p1).comp pairList
  let outputnums := triples.comp (entries.listFlatMapWith (0,0) 0)
  let den := ((law.comp (fst Signed.encode er)).fanout D).comp intMul
  exact (den.fanout outputnums).congr _ (fun _ => rfl)

end MetricKMedian.SparseIntegerLaw.BinarySparse
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

 theorem run_length (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (t : ℕ) : (run β hβ p t).length ≤ n+n*n+1 := by
  cases t with
  | zero => change 1 ≤ _; omega
  | succ t => exact ((run β hβ p t).branch (probability β)
      (probability_unit β hβ) (endpoint β)).compressAuto_correct features |>.1

 theorem run_invariants (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (t : ℕ) :
    ∀ a : Fin (run β hβ p t).length,
      let q := (run β hβ p t).states[a.val]
      (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧
      (∑ i, β i*point q i)=∑ i, β i*point p i ∧
      (fractional q).card ≤ max (n-t) 1 := by
  induction t with
  | zero =>
    intro a
    have he : (run β hβ p 0).states[a.val]=p := SparseIntegerLaw.dirac_states p a
    dsimp only
    rw [he]
    refine ⟨hp,rfl,?_⟩
    have hh := card_le_card (filter_subset (fun i : Fin n => 0 < point p i ∧ point p i < 1) univ)
    simp only [card_univ,Fintype.card_fin] at hh
    exact hh.trans (le_max_left _ _)
  | succ t ih =>
    apply (run β hβ p t).step_property features (probability β)
      (probability_unit β hβ) (endpoint β)
      (fun q => (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧
        (∑ i, β i*point q i)=∑ i, β i*point p i ∧
        (fractional q).card ≤ max (n-(t+1)) 1)
    intro a b
    obtain ⟨ha0,ha1,ha2⟩ := ih a
    refine ⟨endpoint_feasible β hβ _ ha0 b,(endpoint_weighted β hβ _ b).trans ha1,?_⟩
    by_cases h : 1 < (fractional (run β hβ p t).states[a.val]).card
    · have hh := endpoint_smaller β hβ _ h b
      omega
    · simp only [endpoint,dite_eq_right h]
      omega

end MetricKMedian.SparseWeightedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingUniformStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse
def State.raw {s : Bool} (x : State s) : Row × Data Row :=
  (List.ofFn x.β,((x.μ.law.denominator,List.ofFn x.μ.law.numerator),x.μ.states.toList.map Vector.toList))

theorem State.encode_raw {s : Bool} (x : State s) :
    encodePair erow (ed erow) x.raw=x.encode := by
  simp only [State.raw,State.encode,SparseIntegerLaw.BinarySparse.encode,
    SparseIntegerLaw.BinarySparse.raw,ed,encodePair,encodeList_map]

def probability (s : Bool) : Row × Row → ℚ :=
  if s then fun x => RoundingList.Signed.probability x.1 x.2 else fun x => RoundingList.probability x.1 x.2
def endpoint (s b : Bool) : Row × Row → Row :=
  if s then fun x => RoundingList.Signed.endpoint x.1 x.2 b else fun x => RoundingList.endpoint x.1 x.2 b

noncomputable def probabilityProgram (s : Bool) : PolyProgram (encodePair erow erow) Ratio.encode (probability s) := by
  cases s
  · exact RoundingList.probability_poly.program
  · exact RoundingList.Signed.probability_poly.program
noncomputable def endpointProgram (s b : Bool) : PolyProgram (encodePair erow erow) erow (endpoint s b) := by
  cases s
  · exact (RoundingList.endpoint_poly b).program
  · exact (RoundingList.Signed.endpoint_poly b).program

noncomputable def branchRawProgram (s : Bool) :
    PolyProgram (encodePair erow (ed erow)) (encodePair erow (ed erow)) (fun x =>
      (x.1,(branchLawData (x.2.1,x.2.2.map (fun p => probability s (x.1,p))),
        x.2.2.flatMap (fun p => [endpoint s false (x.1,p),endpoint s true (x.1,p)])))) := by
  let β := fst erow (ed erow)
  let law := (snd erow (ed erow)).comp (fst el (encodeList erow))
  let states := (snd erow (ed erow)).comp (snd el (encodeList erow))
  let probs := (β.fanout states).comp ((probabilityProgram s).listMapWith [] 0)
  let laws := (law.fanout probs).comp branchLawProgram
  let endpoints := ((endpointProgram s false).fanout (endpointProgram s true)).comp pairList
  let ps := (β.fanout states).comp (endpoints.listFlatMapWith [] [])
  exact (β.fanout (laws.fanout ps)).congr _ (fun _ => rfl)

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchOrdinalCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.RationalBatchData.Ordinal
open Finset FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)
variable {I : Type} [LinearOrder I] {n : ℕ}
variable (r : Fin n ≃o I) (D : Actions I I) (H : Finset I)

def sets (S : Finset I) : Row := setView (S.map r.symm.toEquiv.toEmbedding)

 theorem sets_eq (S : Finset I) : sets r S=List.ofFn (fun i => decide (r i∈S)) := by
  simp only [sets,setView,mem_map_equiv]
  rfl
 theorem sets_length (S : Finset I) : (sets r S).length=n := by rw [sets_eq,List.length_ofFn]
end MetricKMedian.RationalBatchData.Ordinal
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchOrdinalArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RationalBatchData.Ordinal
open Finset FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)
variable {I : Type} [LinearOrder I] [Fintype I] {n : ℕ}
variable (r : Fin n ≃o I) (D : Actions I I) (H : Finset I)

 def graphView (G : I → Finset I) : Table := List.ofFn (fun i => sets r (G (r i)))
end MetricKMedian.RationalBatchData.Ordinal
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingStateCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse

def vectorData {n : ℕ} (μ : SparseIntegerLaw (Vector ℚ n)) : Data Row :=
  ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map Vector.toList)

theorem vectorData_branch {n : ℕ} (μ : SparseIntegerLaw (Vector ℚ n))
    (p : Vector ℚ n → ℚ) (hp : ∀ q, 0≤p q ∧ p q≤1) (next : Vector ℚ n → Fin 2 → Vector ℚ n)
    (P : Row → ℚ) (E0 E1 : Row → Row)
    (hP : ∀ q, P q.toList=p q) (hE0 : ∀ q, E0 q.toList=(next q 0).toList)
    (hE1 : ∀ q, E1 q.toList=(next q 1).toList) :
    (branchLawData ((vectorData μ).1,(vectorData μ).2.map P),
      (vectorData μ).2.flatMap (fun q => [E0 q,E1 q]))=vectorData (μ.branch p hp next) := by
  simp only [vectorData,states_list,List.map_ofFn,Function.comp_def,hP]
  rw [branchLaw_ofFn μ.law _ (fun i => hp μ.states[i.val])]
  congr 1
  simp only [SparseIntegerLaw.branch,Vector.getElem_ofFn,List.flatMap_def,List.map_ofFn,Function.comp_def,hE0,hE1]
  exact (two_expand (fun i b => (next μ.states[i.val] b).toList)).symm

theorem branch_raw (s : Bool) (x : State s) :
    (x.raw.1,(branchLawData (x.raw.2.1,x.raw.2.2.map (fun p => probability s (x.raw.1,p))),
      x.raw.2.2.flatMap (fun p => [endpoint s false (x.raw.1,p),endpoint s true (x.raw.1,p)])))=
       x.branch.raw := by
  cases s
  · change (List.ofFn x.β,_)=(List.ofFn x.β,vectorData
      (x.μ.branch (RationalWeightedStep.probability x.β)
        (RationalWeightedStep.probability_unit x.β (x.positive rfl)) (RationalWeightedStep.endpoint x.β)))
    apply congrArg (fun d => (List.ofFn x.β,d))
    exact vectorData_branch x.μ _ _ _ (RoundingList.probability (List.ofFn x.β))
      (fun p => RoundingList.endpoint (List.ofFn x.β) p false)
      (fun p => RoundingList.endpoint (List.ofFn x.β) p true)
      (RoundingList.probability_list x.β)
      (fun p => RoundingList.endpoint_list x.β p 0) (fun p => RoundingList.endpoint_list x.β p 1)
  · change (List.ofFn x.β,_)=(List.ofFn x.β,vectorData
      (x.μ.branch (RationalSignedStep.probability x.β)
        (RationalSignedStep.probability_unit x.β) (RationalSignedStep.endpoint x.β)))
    apply congrArg (fun d => (List.ofFn x.β,d))
    exact vectorData_branch x.μ _ _ _ (RoundingList.Signed.probability (List.ofFn x.β))
      (fun p => RoundingList.Signed.endpoint (List.ofFn x.β) p false)
      (fun p => RoundingList.Signed.endpoint (List.ofFn x.β) p true)
      (RoundingList.Signed.probability_list x.β)
      (fun p => RoundingList.Signed.endpoint_list x.β p 0) (fun p => RoundingList.Signed.endpoint_list x.β p 1)

noncomputable def branchProgram (s : Bool) : PolyProgram State.encode State.encode (@State.branch s) :=
  (branchRawProgram s).recode State.raw State.encode_raw (fun x => by
    rw [branch_raw,State.encode_raw])

end MetricKMedian.RoundingProgram
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

@[fun_prop] theorem bindData_poly [Coding A] [Inhabited A] : Poly (bindData (A:=A)) := by
  have hd : Poly IntegerList.denominator := ⟨IntegerList.denominatorProgram⟩
  have hn : Poly IntegerList.numerators := ⟨IntegerList.numeratorsProgram⟩
  have hs : Poly (fun x : LawData × List (Data A) => x.2.flatMap Prod.snd) := by
    apply list_flatMap <;> fun_prop
  exact pair (pair (comp hd jointWeights_poly) (comp hn jointWeights_poly)) hs

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.Automatic Binary.Automatic.Poly
variable {α A : Type}

def mixData (x : Data A × Data A) : Data A := bindData ((2,[1,1]),[x.1,x.2])

@[fun_prop] theorem mixData_poly [Coding A] [Inhabited A] : Poly (mixData (A:=A)) := by
  unfold mixData
  fun_prop
end MetricKMedian.SparseIntegerLaw.BinarySparse
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

def Input.raw (x : Input I) : GraphData.Raw :=
  (((x.g,x.b),(x.Δ,(x.p,x.φ))),Ordinal.graphView x.enum x.G)
end MetricKMedian.RationalBatchData.ProposalProgram
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

namespace MetricKMedian.SparseWeightedPartial
open RationalWeightedStep RationalGrid
variable {n : ℕ}

theorem run_grid (β : Fin n → ℚ) (hβ : ∀ i, 0<β i) (p : Vector ℚ n)
    (D : ℤ) (hb : ∀ i, At D (β i)) (hp : ∀ i, At D (β i*point p i)) (t : ℕ) :
    ∀ a : Fin (run β hβ p t).length, ∀ i, At D (β i*point (run β hβ p t).states[a.val] i) := by
  induction t with
  | zero =>
    intro a
    have he : (run β hβ p 0).states[a.val]=p := SparseIntegerLaw.dirac_states p a
    rw [he]
    exact hp
  | succ t ih =>
    apply (run β hβ p t).step_property features (probability β) (probability_unit β hβ)
      (endpoint β) (fun q => ∀ i, At D (β i*point q i))
    intro a b
    exact endpoint_grid β hβ D hb _ (ih a) b
end MetricKMedian.SparseWeightedPartial

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

theorem weighted_run (β : Fin n → ℚ) (hβ : ∀ i, 0<β i) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) (a : Fin (SparseWeightedPartial.run β hβ p t).length)
    (i : Fin n) : HasHeight (point (SparseWeightedPartial.run β hβ p t).states[a.val] i) (2*n*L+L) := by
  apply coordinate_height β p _ L hb hp
  · exact SparseWeightedPartial.run_grid β hβ p _ (initial_grid β p).1 (initial_grid β p).2 t a
  · intro j hj; exact False.elim ((hβ j).ne' hj)
  · exact (SparseWeightedPartial.run_invariants β hβ p hu t a).1

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

theorem weighted_endpoint (β : Fin n → ℚ) (hβ : ∀ i, 0<β i) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) (a : Fin (SparseWeightedPartial.run β hβ p t).length)
    (b : Fin 2) (i : Fin n) :
    HasHeight (point (endpoint β (SparseWeightedPartial.run β hβ p t).states[a.val] b) i) (2*n*L+L) := by
  apply coordinate_height β p _ L hb hp
  · exact endpoint_grid β hβ _ (initial_grid β p).1 _
      (SparseWeightedPartial.run_grid β hβ p _ (initial_grid β p).1 (initial_grid β p).2 t a) b
  · intro j hj; exact False.elim ((hβ j).ne' hj)
  · exact endpoint_feasible β hβ _ (SparseWeightedPartial.run_invariants β hβ p hu t a).1 b

theorem weighted_denominator (β : Fin n → ℚ) (hβ : ∀ i, 0<β i) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) :
    (SparseWeightedPartial.run β hβ p t).law.denominator≤(2:ℤ)^(stepHeight n L*t) := by
  induction t with
  | zero => simp only [SparseWeightedPartial.run,SparseIntegerLaw.dirac,mul_zero,pow_zero,le_refl]
  | succ t ih =>
    apply (SparseIntegerLaw.step_denominator_height _ _ _ _ _ (n+n*n+1)
      (3*(2*n*L+L+2*L+1)+1) (2*(2*n*L+L)) (SparseWeightedPartial.run_length β hβ p t)
      (fun a => probability_height β _ _ L hb (weighted_run β hβ p L t hb hp hu a))
      (fun a b i => SparseWeightedPartial.features_height _ _ (weighted_endpoint β hβ p L t hb hp hu a b) i)).trans
    calc
      _ ≤ (2:ℤ)^(stepHeight n L*t)*(2:ℤ)^(stepHeight n L) := mul_le_mul_of_nonneg_right ih (by positivity)
      _ = _ := by rw [← pow_add,Nat.mul_succ]

theorem signed_denominator (β : Fin n → ℚ) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) :
    (SparseSignedPartial.run β p t).law.denominator≤(2:ℤ)^(stepHeight n L*t) := by
  induction t with
  | zero => simp only [SparseSignedPartial.run,SparseIntegerLaw.dirac,mul_zero,pow_zero,le_refl]
  | succ t ih =>
    apply (SparseIntegerLaw.step_denominator_height _ _ _ _ _ (n+n*n+1)
      (3*(2*n*L+L+2*L+1)+1) (2*(2*n*L+L)) (SparseSignedPartial.run_length β p t)
      (fun a => RationalSignedStep.probability_height β _ _ L hb (signed_run β p L t hb hp hu a))
      (fun a b i => SparseWeightedPartial.features_height _ _ (signed_endpoint β p L t hb hp hu a b) i)).trans
    calc
      _ ≤ (2:ℤ)^(stepHeight n L*t)*(2:ℤ)^(stepHeight n L) := mul_le_mul_of_nonneg_right ih (by positivity)
      _ = _ := by rw [← pow_add,Nat.mul_succ]

end MetricKMedian.RoundingHeight
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
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.BinarySparse

def Input.raw {s : Bool} (x : Input s) : Row × Row := (List.ofFn x.β,x.p.toList)
abbrev Input.encode {s : Bool} (x : Input s) := encodePair erow erow x.raw

noncomputable def startProgram (s : Bool) : PolyProgram Input.encode State.encode (@Input.start s) := by
  let β := fst erow erow
  let p := snd erow erow
  let law := constant (encodePair erow erow) el ((1:ℤ),[(1:ℤ)])
  let ps := (p.fanout (constant (encodePair erow erow) (encodeList erow) [])).comp (listCons erow)
  let work := β.fanout (law.fanout ps)
  exact work.recode Input.raw (fun _ => rfl) (fun x => by
    change encodePair erow (ed erow) (List.ofFn x.β,((1,[1]),[x.p.toList]))=_
    rw [← State.encode_raw]
    rfl)

noncomputable def countProgram (s : Bool) : PolyProgram Input.encode Nat.bits (@Input.n s) :=
  ((fst erow erow).comp (listLength Ratio.encode 0)).recode Input.raw (fun _ => rfl)
    (fun x => by simp only [Function.comp_def,Input.raw,List.length_ofFn])

theorem input_bounds {s : Bool} (x : Input s) :
    x.n ≤ x.encode.length ∧ (erow (List.ofFn x.β)).length ≤ x.encode.length ∧
      (∀ i, HasHeight (x.β i) x.encode.length) ∧
      ∀ i, HasHeight (RationalWeightedStep.point x.p i) x.encode.length := by
  have he : x.encode.length=2*(erow (List.ofFn x.β)).length+1+(erow x.p.toList).length := by
    simp only [Input.encode,Input.raw,encodePair_length]
  have hn := EncodedList.length_le Ratio.encode (List.ofFn x.β)
  change (List.ofFn x.β).length ≤ (erow (List.ofFn x.β)).length at hn
  simp only [List.length_ofFn] at hn
  refine ⟨by omega,by omega,?_,?_⟩
  · intro i
    exact (Ratio.height_length _).mono ((EncodedList.member_length Ratio.encode _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩)).trans (by change (erow (List.ofFn x.β)).length ≤ x.encode.length; omega))
  · intro i
    have hm : RationalWeightedStep.point x.p i∈x.p.toList := by
      exact List.mem_iff_getElem.mpr ⟨i.val,by simp,by simp [RationalWeightedStep.point]⟩
    exact (Ratio.height_length _).mono ((EncodedList.member_length Ratio.encode _ _ hm).trans (by change (erow x.p.toList).length ≤ x.encode.length; omega))

 theorem run_size {s : Bool} (x : Input s) (t : ℕ) (ht : t ≤ x.n) :
    (State.encode (x.run t)).length ≤ statePolynomial.eval x.encode.length := by
  let L := x.encode.length
  obtain ⟨hn,hβ,hb,hp⟩ := input_bounds x
  have hH : RoundingHeight.stepHeight x.n L*t ≤ heightBound L := by
    unfold heightBound RoundingHeight.stepHeight SparseIntegerLaw.stepHeight
    gcongr
    exact ht.trans hn
  have hC : 2*x.n*L+L ≤ coordinateBound L := by unfold coordinateBound; gcongr
  have hN : x.n+x.n*x.n+1 ≤ supportBound L := by unfold supportBound; gcongr
  have hrow (p : Vector ℚ x.n) (hp : ∀ i, HasHeight (RationalWeightedStep.point p i) (2*x.n*L+L)) :
      (erow p.toList).length  ≤  L*(2*(3*coordinateBound L+10)+1) := by
    apply (EncodedList.length_bound Ratio.encode p.toList (3*coordinateBound L+10) ?_).trans
    · simpa only [Vector.length_toList] using Nat.mul_le_mul_right (2*(3*coordinateBound L+10)+1) hn
    · intro q hq
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hq
      have hh := hp ⟨i,by simpa only [Vector.length_toList] using hi⟩
      exact Ratio.length_height (hh.mono hC)
  have hsize : (SparseIntegerLaw.BinarySparse.encode (fun p => erow p.toList) (x.run t).μ).length ≤ 
      2*(2*(heightBound L+4)+1+supportBound L*(2*(heightBound L+4)+1))+1+
      supportBound L*(2*(L*(2*(3*coordinateBound L+10)+1))+1) := by
    cases s
    · apply SparseIntegerLaw.encode_length_bound _ _ (supportBound L) (heightBound L) _
      · exact (SparseWeightedPartial.run_length x.β (x.positive rfl) x.p t).trans hN
      · exact (RoundingHeight.weighted_denominator x.β (x.positive rfl) x.p L t hb hp x.feasible).trans
          (pow_le_pow_right₀ (by norm_num) hH)
      · intro i; exact hrow _ (RoundingHeight.weighted_run x.β (x.positive rfl) x.p L t hb hp x.feasible i)
    · apply SparseIntegerLaw.encode_length_bound _ _ (supportBound L) (heightBound L) _
      · exact (SparseSignedPartial.run_length x.β x.p t).trans hN
      · exact (RoundingHeight.signed_denominator x.β x.p L t hb hp x.feasible).trans
          (pow_le_pow_right₀ (by norm_num) hH)
      · intro i; exact hrow _ (RoundingHeight.signed_run x.β x.p L t hb hp x.feasible i)
  rw [statePolynomial_eval]
  have he : (State.encode (x.run t)).length = 2*(erow (List.ofFn x.β)).length+1+
      (SparseIntegerLaw.BinarySparse.encode (fun p => erow p.toList) (x.run t).μ).length := by
    exact encodePair_length _ _ _
  rw [he]
  change 2*(erow (List.ofFn x.β)).length+1+
    (SparseIntegerLaw.BinarySparse.encode (fun p => erow p.toList) (x.run t).μ).length ≤ stateBound L
  unfold stateBound
  omega

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_GraphStepProgram
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
abbrev InputRaw := List Unit × List (Data Row)
abbrev ei : InputRaw → List Bool := Binary.Automatic.enc

def columnRaw {n : ℕ} (μ : SparseIntegerLaw (Finset (Fin n))) : Data Row :=
  ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map ListOperation.setView)
def Input.raw (x : Input) : InputRaw := (List.replicate x.n (),List.ofFn fun i => columnRaw (x.columns i))
abbrev Input.encode (x : Input) := ei x.raw
def Context.raw (c : Context) : InputRaw × ℕ := (c.input.raw,c.t)
abbrev Context.encode (c : Context) := encodePair ei Nat.bits c.raw
abbrev view (c : Context) (G : T c) := ListOperation.view G
abbrev State.encode := Bundle.encode Context.encode et view

end MetricKMedian.SparseGraph.Program
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
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseIntegerLaw.DependentProgram
def QInput.result (x : QInput) : Data ListOperation.Table :=
  (((SparseGraph.law x.q).law.denominator,List.ofFn (SparseGraph.law x.q).law.numerator),
    (SparseGraph.law x.q).states.toList.map ListOperation.view)

end MetricKMedian.SparseGraph.Program
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
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open CopyList

attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.instLinearOrderSubtypeCopyFinMemFinset
def Input.result (x : Input) : Data Table :=
  ((x.law.law.denominator,List.ofFn x.law.law.numerator),
    x.law.states.toList.map (RationalBatchData.Ordinal.graphView (ordinal x.A)))

end MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
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
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row setView indices)

def imageRaw (x : (List Unit × List ℕ) × Row) : Row :=
  (indices x.1.1).map (fun h => ((indices x.1.2).map (fun i =>
    get x.2 i && decide (x.1.2[i]?.getD 0=h))).any id)
@[fun_prop] theorem imageRaw_poly : Poly imageRaw := by
  unfold imageRaw
  apply list_map
  · apply comp bool_any
    apply list_map <;> fun_prop
  · fun_prop
 theorem imageRaw_view {f h : ℕ} (orig : Fin f → Fin h) (O : Finset (Fin f)) :
    imageRaw ((List.replicate h (),List.ofFn (fun i => (orig i).val)),setView O)=setView (O.image orig) := by
  simp only [imageRaw,indices,List.length_replicate,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  unfold setView
  apply congrArg List.ofFn
  funext a
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,List.mem_ofFn,id_eq,get,List.getElem?_ofFn,
    dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,decide_eq_true_eq,mem_image]
  constructor
  · rintro ⟨b,⟨i,rfl⟩,hi⟩
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hi
    exact ⟨i,hi.1,Fin.ext hi.2⟩
  · rintro ⟨i,hi,he⟩
    refine ⟨_,⟨i,rfl⟩,?_⟩
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨hi,congrArg Fin.val he⟩

@[fun_prop] theorem pullback_poly : Poly pullback := by unfold pullback; apply list_map <;> fun_prop
 theorem pullback_view {f h : ℕ} (orig : Fin f → Fin h) (d : Fin h → ℚ) :
    pullback (List.ofFn d,List.ofFn (fun i => (orig i).val))=List.ofFn (fun i => d (orig i)) := by
  simp only [pullback,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]

def pullbackMatrix (x : List (List ℚ) × List ℕ) : List (List ℚ) :=
  x.2.map (fun i => pullback (x.1[i]?.getD [],x.2))
@[fun_prop] theorem pullbackMatrix_poly : Poly pullbackMatrix := by unfold pullbackMatrix; apply list_map <;> fun_prop
 theorem pullbackMatrix_view {f h : ℕ} (orig : Fin f → Fin h) (d : Fin h → Fin h → ℚ) :
    pullbackMatrix (List.ofFn (fun i => List.ofFn (d i)),List.ofFn (fun i => (orig i).val))=
      List.ofFn (fun i => List.ofFn (fun k => d (orig i) (orig k))) := by
  simp only [pullbackMatrix,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,pullback_view]
end MetricKMedian.MaskProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section

namespace MetricKMedian.SparseIntegerLaw.BinarySparse
variable {α β A : Type}
def table (μ : SparseIntegerLaw α) (v : α → A) : Data A := ((raw μ).1,μ.states.toList.map v)
 theorem table_map (μ : SparseIntegerLaw α) (f : α → β) (v : β → A) :
    table (μ.map f) v=table μ (v ∘ f) := by
  simp only [table,raw,map,Vector.toList_map,List.map_map]

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end


