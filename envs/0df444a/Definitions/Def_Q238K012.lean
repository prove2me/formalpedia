-- Prove2me | Definitions.Def_Q238K012
-- name    : Q238K012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:13:46.808284+00:00
-- url     : https://prove2.me/theorems/aa16343f-9d53-4f09-9c14-a719bcb6272a
-- title:
--   Definitions bundle Q238K012 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 129 declarations of OpenAI's Lean: 127 definitions and 2 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.colorTensor`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.colors`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.labelTensor`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.labels`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape.layout`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape.raw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape.tensors`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.advance`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.finish`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.same`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.input`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.G`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.H`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.T`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.U`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.bf`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.key`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.leafKey`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.qbits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.sf`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.spare`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.cf`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.flipped`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.leftData`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.leftNode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.mixed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.mixedCommon`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.rightData`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.rightNode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.successNode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.taggedPair`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.threeQ`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.threeQOne`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.chainInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.crossCtx`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.firstNode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.nextQ`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.data`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.atPrice`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.bf` and 87 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_BlueDPValue`, `KMedianRecovery_Branching_BluePlan`, `KMedianRecovery_Branching_BranchSeedLayout`, `KMedianRecovery_Branching_CategoricalOutput`, `KMedianRecovery_Branching_CategoricalResources`, `KMedianRecovery_Encoding_CoupledEncode`, `KMedianRecovery_Encoding_LengthEncode`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Machines_CoupledPrimitives`, `KMedianRecovery_Machines_FiniteMachine`, `KMedianRecovery_Machines_LengthQuery`, `KMedianRecovery_Machines_LoopMachine`, `KMedianRecovery_Machines_MatchFold`, `KMedianRecovery_Machines_MatchSize`, `KMedianRecovery_Machines_RefineMachine`, `KMedianRecovery_Machines_ResolveMachine`, `KMedianRecovery_Machines_ScanMachine`, `KMedianRecovery_Machines_SensitiveMachine`, `KMedianRecovery_Machines_SliceFold`, `KMedianRecovery_Machines_StartResources`, `KMedianRecovery_Machines_StepMachine`, `KMedianRecovery_Machines_SuffixMachine`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_CrossEdge`, `KMedianRecovery_Recovery_FinishPhase`, `KMedianRecovery_Recovery_FirstPresent`, `KMedianRecovery_Recovery_LengthCandidates`, `KMedianRecovery_Recovery_Min`, `KMedianRecovery_Recovery_OrientedSearch`, `KMedianRecovery_Recovery_PlanResult`, `KMedianRecovery_Recovery_RefineMath`, `KMedianRecovery_Recovery_RegularChain`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K000`, `Q238K001`, `Q238K002` and `Q238K003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K020` and `Q238K021`; the proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_rows_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryBranchRows_run_pack_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K000
import Definitions.Def_Q238K001
import Definitions.Def_Q238K002
import Definitions.Def_Q238K003

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueDPValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {A L : Type*}

variable [LinearOrder L]
lemma enumBlocks_set (U : Finset L) : (enumBlocks U).toFinset=BlueSubsetDP.blocks U := by
  ext V
  simp only [enumBlocks,List.mem_toFinset,List.mem_filter,List.mem_map,List.mem_sublists,decide_eq_true_eq,BlueSubsetDP.mem_blocks]
  constructor
  · rintro ⟨⟨xs,hxs,rfl⟩,hx⟩
    refine ⟨Finset.nonempty_iff_ne_empty.mpr hx,?_⟩
    intro l hl
    exact (Finset.mem_sort (·≤·)).mp (hxs.subset (List.mem_toFinset.mp hl))
  · intro h
    refine ⟨⟨(U.sort (·≤·)).filter (fun l=>l∈V),List.filter_sublist,?_⟩,h.1.ne_empty⟩
    ext l
    simp only [List.mem_toFinset,List.mem_filter,Finset.mem_sort,decide_eq_true_eq]
    exact ⟨And.right,fun hv=>⟨h.2 hv,hv⟩⟩

end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Min
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic WordList
namespace BinaryPhaseAdvance
open EffectiveOpenability RationalPhase BinaryOpeningPayment

def paramV (x : List Bool) : ℚ := BinaryRational.decode (sf 2 x)
def paramZ (x : List Bool) : ℚ := BinaryRational.decode (sf 3 x)
def phase (x : List Bool) : ℚ := (1+paramV x*paramV x)*paramZ x
def query (x : List Bool) : List Bool := pairBits (extractPrefix (extractPrefix x),discardPrefix x)
noncomputable def context (x : List Bool) : List Bool := encode [sf 0 x,sf 1 x,sf 2 x,BinaryRational.encode (phase x),
  sf 4 x,sf 5 x,sf 6 x,sf 7 x,sf 8 x]
end BinaryPhaseAdvance
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinishPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseCount
open BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryOpeningPayment
attribute [local irreducible] WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run 
noncomputable def powerInput (x : List Bool) : List Bool := pairBits
  (encode [[],[],x,BinaryRational.encode 1,BinaryRational.encode 0,BinaryRational.encode 0,[],[],[]],[])
end MetricKMedianRecovery.BitMachine.BinaryPhaseCount

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FiniteMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteMachine
open WordList RationalLeaves
open BinaryOpeningPayment (field )

noncomputable def data : List Bool → List Bool := discardPrefix ∘ discardPrefix
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryOpeningPayment (field )
def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
def jf (n : ℕ) : List Bool → List Bool := field n ∘ discardPrefix
noncomputable def tagIs (n : ℕ) (x : List Bool) : Bool := decide (value (jf 0 x)=n)

end MetricKMedianRecovery.BitMachine.BinaryJump

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BluePlan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]
def pick (r0 : R) (y0 : Y) (xs : List (Atom L R Y)) (l : L) : Atom L R Y :=
  (xs.find? (fun a=>a.1=l)).getD (l,r0,y0)
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical.Explicit
open FiniteSampling

lemma steps_upper (a : ℕ) : steps a ≤ 4096*(a+2)^2 := by
  have hh := pow_size_bound (a+1)
  have hs:=Nat.pow_le_pow_left hh 2
  unfold steps exponent
  rw [pow_add,show 2*(a+1).size=(a+1).size*2 by omega,pow_mul]
  norm_num
  nlinarith
attribute [local irreducible] steps exponent

attribute [local irreducible] samples
end MetricKMedianRecovery.Categorical.Explicit

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape
open BinarySeed
variable (q a b L : ℕ)

def tensors : (Categorical.BinaryOracleIndex (Fin q) a b L→Bool)≃
    Tensor [2^b,q,L,a] b × Tensor [a] b where
  toFun bits := (fun t e l j i=>bits (.inl (t,e,l,j),i),fun j i=>bits (.inr j,i))
  invFun s := fun idx=>match idx.1 with
    | .inl (t,e,l,j)=>s.1 t e l j idx.2
    | .inr j=>s.2 j idx.2
  left_inv bits := by
    funext idx
    rcases idx with ⟨idx,i⟩
    rcases idx with ⟨t,e,l,j⟩ | j <;> rfl
  right_inv s := by rfl

def layout : (Fin (M q a b L+K a b)→Bool)≃(Categorical.BinaryOracleIndex (Fin q) a b L→Bool) :=
  (tensorPair q a b L).trans (tensors q a b L).symm

def raw (bits : Categorical.BinaryOracleIndex (Fin q) a b L→Bool) : List Bool :=
  BinarySeed.raw ((tensors q a b L bits).1)++BinarySeed.raw ((tensors q a b L bits).2)
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchSeedLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape
open BinarySeed
def colors (n : ℕ) : (Fin (colorCount n)→Bool)≃(Fin n→Fin 4) :=
  (tensorEquiv [n] 2).trans (Equiv.arrowCongr (Equiv.refl (Fin n)) (Categorical.uniformBits 2))
def labels (n b : ℕ) : (Fin (labelCount n b)→Bool)≃(Fin n→Fin (ColorLabel.labelRange b)) :=
  (tensorEquiv [n] (Nat.clog 2 b)).trans (Equiv.arrowCongr (Equiv.refl (Fin n)) (Categorical.uniformBits (Nat.clog 2 b)))
def colorTensor {n : ℕ} (s : Fin n→Fin 4) : Tensor [n] 2 := fun i=>(Categorical.uniformBits 2).symm (s i)
def labelTensor {n b : ℕ} (s : Fin n→Fin (ColorLabel.labelRange b)) : Tensor [n] (Nat.clog 2 b) :=
  fun i=>(Categorical.uniformBits (Nat.clog 2 b)).symm (s i)
end MetricKMedianRecovery.BitMachine.BinaryBranchTape

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_CoupledEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
noncomputable def finish (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 2 x++field 3 x]
noncomputable def same (x : List Bool) : List Bool := encode [field 0 x,field 2 x,[],field 1 x,field 1 x,field 3 x,field 4 x]
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LengthEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordList RationalLeaves CanonicalLengthView BinaryArithmetic
open BinaryOpeningPayment (field )
def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
def pf (n : ℕ) : List Bool → List Bool := field n ∘ discardPrefix
noncomputable def isFree (x : List Bool) : Bool := decide (value (pf 0 x)=0)
noncomputable def source (x : List Bool) : List Bool :=
  if isFree x then cf 2 x else pf 3 x++cons (pf 1 x) (pf 4 x)
noncomputable def target (x : List Bool) : List Bool :=
  if isFree x then cf 2 x++cons (pf 2 x) [] else pf 3 x++pf 4 x
end MetricKMedianRecovery.BitMachine.BinaryLength

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CoupledPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
noncomputable def advance (x : List Bool) : List Bool :=
  encode [field 0 (field 0 x),field 1 (field 0 x)++cons (field 1 x) [],field 2 (field 0 x),
    field 3 (field 0 x),field 4 (field 0 x),field 2 x,field 3 x]
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SliceFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Slices
open BinaryOpeningPayment (field )

def sf (n : ℕ) (x : List Bool) : List Bool := field n (discardPrefix (discardPrefix x))
def item (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
noncomputable def front (x : List Bool) : List Bool := sf 0 x++cons (item x) []
noncomputable def rest (x : List Bool) : List Bool := tail (sf 1 x)
noncomputable def cut (x : List Bool) : List Bool := encode [sf 0 x,item x,rest x]
noncomputable def output (x : List Bool) : List Bool := sf 2 x++cons (cut x) []
noncomputable def step (x : List Bool) : List Bool := encode [front x,rest x,output x]
noncomputable def initial (x : List Bool) : List Bool := Fold.pack x [] (encode [[],x,[]])
end MetricKMedianRecovery.BitMachine.WordList.Slices

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SuffixMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySuffix
open WordList RationalLeaves
open BinaryOpeningPayment (field )
noncomputable def pruneOp (x : List Bool) : List Bool := extractPrefix x++field 2 (discardPrefix x)
noncomputable def growOp (x : List Bool) : List Bool :=
  extractPrefix (extractPrefix x)++cons (field 1 (discardPrefix x)) (field 2 (discardPrefix x))++
    cons (discardPrefix (extractPrefix x)) []
end MetricKMedianRecovery.BitMachine.BinarySuffix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordList RationalLeaves BinaryArithmetic
open BinaryOpeningPayment (field )

def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
end MetricKMedianRecovery.BitMachine.BinaryCross

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def addOp (x : List Bool) : List Bool := encode [(0:ℕ).bits,[],[],[],discardPrefix x]
noncomputable def replaceOp (x : List Bool) : List Bool := encode [(2:ℕ).bits,jf 0 x,jf 2 x,[],jf 1 x]
noncomputable def adds (x : List Bool) : List Bool := mapWith addOp (pairBits (x,field 1 x))
end MetricKMedianRecovery.BitMachine.BinaryJump

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_OrientedSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryOrientedSearch
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def isReversed (query : List Bool→List Bool) (x : List Bool) : Bool :=
  decide (value (query (pairBits (field 1 x,BinaryRational.encode 0)))<value (field 2 x))
end MetricKMedianRecovery.BitMachine.BinaryOrientedSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LengthQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLengthQuery
open WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field )
def cf (n : ℕ) : List Bool→List Bool := field n ∘ extractPrefix
noncomputable def isZero (x : List Bool) : Bool := decide (BinaryRational.decode (discardPrefix x)=0)
noncomputable def isUpper (x : List Bool) : Bool := decide (BinaryRational.decode (discardPrefix x)=BinaryRational.decode (cf 5 x))
end MetricKMedianRecovery.BitMachine.BinaryLengthQuery

namespace MetricKMedianRecovery.BitMachine.BinaryLengthSearch
open WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field )
def lower : List Bool→List Bool := extractPrefix ∘ discardPrefix
def upper : List Bool→List Bool := discardPrefix ∘ discardPrefix
def context : List Bool→List Bool := field 1 ∘ extractPrefix
def boundK : List Bool→List Bool := field 2 ∘ extractPrefix
def leftInput (x : List Bool) : List Bool := pairBits (context x,lower x)
def rightInput (x : List Bool) : List Bool := pairBits (context x,upper x)
end MetricKMedianRecovery.BitMachine.BinaryLengthSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SensitiveMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySensitive
open WordList BinaryArithmetic RationalLeaves CanonicalLengthView
open BinaryOpeningPayment (field )
def jf (n : ℕ) : List Bool→List Bool := field n ∘ field 10
noncomputable def isFree (x : List Bool) : Bool := decide (value (jf 0 x)=0)
noncomputable def common (x : List Bool) : List Bool := if isFree x then field 7 x else jf 3 x++jf 4 x
end MetricKMedianRecovery.BitMachine.BinarySensitive

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordList RationalLeaves BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def leftNode : List Bool → List Bool := extractPrefix ∘ discardPrefix
noncomputable def rightNode : List Bool → List Bool := discardPrefix ∘ discardPrefix
noncomputable def leftData (x : List Bool) : List Bool := pairBits (extractPrefix x,leftNode x)
noncomputable def rightData (x : List Bool) : List Bool := pairBits (extractPrefix x,rightNode x)

noncomputable def mixed (x : List Bool) : List Bool := pairBits (extractPrefix (rightNode x),discardPrefix (leftNode x))
noncomputable def successNode (x : List Bool) : List Bool := encode [(0:ℕ).bits,x,[]]
noncomputable def taggedPair (tag : ℕ) (x : List Bool) : List Bool := encode [tag.bits,extractPrefix x,discardPrefix x]
noncomputable def mixedCommon (x : List Bool) : List Bool := taggedPair 1 (pairBits (mixed x,discardPrefix (rightNode x)))

noncomputable def flipped (x : List Bool) : List Bool := pairBits (extractPrefix x,pairBits (rightNode x,leftNode x))
end MetricKMedianRecovery.BitMachine.BinaryCross

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordList RationalLeaves CanonicalLengthView BinaryArithmetic CanonicalMergeRefinement
open BinaryOpeningPayment (field )
attribute [local irreducible] WordList.mapWith
noncomputable def freeOp (x : List Bool) : List Bool := encode [(0:ℕ).bits,extractPrefix x,discardPrefix x,[],[]]
noncomputable def paidOp (x : List Bool) : List Bool := encode [(1:ℕ).bits,pf 1 x,[],pf 0 x,pf 2 x]
end MetricKMedianRecovery.BitMachine.BinaryLength

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PlanResult
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPlanResult
open WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field )

def sf (n : ℕ) : List Bool→List Bool := field n ∘ field 0
def rf (n : ℕ) : List Bool→List Bool := field n ∘ field 3
noncomputable def success (x : List Bool) : Bool := decide (value (rf 0 x)=0)
noncomputable def rightHeight (x : List Bool) : List Bool := if success x then rf 1 x else rf 2 x
noncomputable def price : List Bool→List Bool := field 7 ∘ sf 0
noncomputable def root : List Bool→List Bool := field 1 ∘ sf 10
noncomputable def common : List Bool→List Bool := BinarySensitive.common ∘ field 0
noncomputable def leafInput (x : List Bool) : List Bool := encode [field 1 x,field 2 x,price x,sf 3 x,root x,common x,rf 1 x,rightHeight x,rf 3 x,rf 4 x]
end MetricKMedianRecovery.BitMachine.BinaryPlanResult

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field )
noncomputable def threeQ (x : List Bool) : List Bool := (3*value (field 2 x)).bits
noncomputable def threeQOne (x : List Bool) : List Bool := (value (threeQ x)+1).bits
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ResolveMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryResolve
open WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field )
def rf (n : ℕ) : List Bool→List Bool := field n ∘ field 9
def bf (n : ℕ) : List Bool→List Bool := field n ∘ field 0
def H : List Bool→List Bool := extractPrefix ∘ rf 1
def T : List Bool→List Bool := discardPrefix ∘ rf 1
def G : List Bool→List Bool := extractPrefix ∘ rf 2
def U : List Bool→List Bool := discardPrefix ∘ rf 2
noncomputable def prefixH (x : List Bool) : List Bool := field 8 x++cons (H x) []
noncomputable def finishInput (x : List Bool) : List Bool := encode [field 7 x,bf 7 x,prefixH x,T x]
noncomputable def sameInput (x : List Bool) : List Bool := encode [field 7 x,bf 7 x,prefixH x,T x,rf 2 x]
noncomputable def fallbackInput (x : List Bool) : List Bool := encode [field 7 x,bf 7 x,field 8 x,[]]
noncomputable def viewInput (x : List Bool) : List Bool := encode [bf 2 x,bf 2 x,H x,G x,pairBits (bf 0 x,bf 1 x)]
end MetricKMedianRecovery.BitMachine.BinaryResolve

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMatch
open WordList RationalLeaves CanonicalMatch
open BinaryOpeningPayment (field )

def cf (n : ℕ) (x : List Bool) : List Bool := field n (extractPrefix x)
def sf (n : ℕ) (x : List Bool) : List Bool := field n (discardPrefix (discardPrefix x))
def item (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
noncomputable def front (x : List Bool) : List Bool := sf 0 x++WordList.cons (item x) []
end MetricKMedianRecovery.BitMachine.BinaryMatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegular
open WordList RationalLeaves
open BinaryOpeningPayment (field )

noncomputable def poolInput (x : List Bool) : List Bool := pairBits (field 1 x,field 2 (field 0 x))
noncomputable def state0 (x : List Bool) : List Bool := encode [[],field 3 x,[]]
end MetricKMedianRecovery.BitMachine.BinaryRegular

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RefineMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordList RationalLeaves CanonicalMergeRefinement
open BinaryOpeningPayment (field )
noncomputable def ct (x : List Bool) : List Bool := jf 1 x++jf 2 x
noncomputable def edgeG (x : List Bool) : List Bool := field 4 (field 0 x)
noncomputable def edgeData (x : List Bool) : List Bool := encode [field 1 x,edgeG x]
end MetricKMedianRecovery.BitMachine.BinaryJump

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RefineMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRefine
open WordList RationalLeaves CanonicalMergeRefinement
open BinaryOpeningPayment (field )
noncomputable def cutTail (x : List Bool) : List Bool := field 2 (discardPrefix x)
noncomputable def source (x : List Bool) : List Bool := field 1 (discardPrefix x)
noncomputable def target : List Bool → List Bool := head ∘ cutTail
noncomputable def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
noncomputable def jumpContext (x : List Bool) : List Bool := encode [cf 0 x,cf 1 x,cf 2 x,source x,target x]
noncomputable def edgeInput (x : List Bool) : List Bool := encode [jumpContext x,cf 3 x]
end MetricKMedianRecovery.BitMachine.BinaryRefine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RegularChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegularChain
open WordList RationalLeaves
open BinaryOpeningPayment (field )
noncomputable def regularInput (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 5 x,field 4 x]
noncomputable def context (x : List Bool) : List Bool := encode [field 2 (field 0 x),field 3 x,field 1 x,field 2 x]
end MetricKMedianRecovery.BitMachine.BinaryRegularChain

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FirstPresent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.FirstPresent
open CanonicalMergeCrossing
noncomputable def present (x : List Bool) : Bool := !decide (discardPrefix x=[])
end MetricKMedianRecovery.BitMachine.WordList.FirstPresent

namespace MetricKMedianRecovery.BitMachine.BinaryNodeScan
open WordList RationalLeaves CanonicalMergeRefinement CanonicalMergeCrossing
open BinaryOpeningPayment (field )
noncomputable def suffix (x : List Bool) : List Bool := field 2 (discardPrefix x)
noncomputable def current (x : List Bool) : List Bool := field 1 (discardPrefix x)
noncomputable def transitionInput (x : List Bool) : List Bool :=
  pairBits (extractPrefix x,pairBits (current x,head (suffix x)))
noncomputable def lastNode : List Bool → List Bool := head ∘ WordList.reverse ∘ field 2
noncomputable def fallback (x : List Bool) : List Bool := encode [(1:ℕ).bits,lastNode x,field 1 x]
end MetricKMedianRecovery.BitMachine.BinaryNodeScan

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ScanMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryScan
open WordList RationalLeaves CanonicalMergeCrossing
open BinaryOpeningPayment (field )
noncomputable def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
noncomputable def mapCtx (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 2 x]
end MetricKMedianRecovery.BitMachine.BinaryScan

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteCross
open WordList RationalLeaves
open BinaryOpeningPayment (field )
noncomputable def chainInput (x : List Bool) : List Bool :=
  encode [field 0 x,field 1 x,field 2 x,field 2 (field 0 x),field 6 x,field 7 x]
noncomputable def crossCtx (x : List Bool) : List Bool := encode [field 2 (field 0 x),field 3 (field 0 x),field 3 x]
noncomputable def nextQ (x : List Bool) : List Bool := true::field 5 x
noncomputable def firstNode (x : List Bool) : List Bool := pairBits (field 6 x,field 8 x)
end MetricKMedianRecovery.BitMachine.BinaryFiniteCross

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_StepMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledStep
open WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
def sf (i : ℕ) : List Bool→List Bool := field i ∘ field 6
def bf (i : ℕ) : List Bool→List Bool := field i ∘ field 0
noncomputable def H (x : List Bool) : List Bool := WordList.head (sf 5 x)
noncomputable def T (x : List Bool) : List Bool := WordList.tail (sf 5 x)
noncomputable def G (x : List Bool) : List Bool := WordList.head (sf 6 x)
noncomputable def U (x : List Bool) : List Bool := WordList.tail (sf 6 x)
noncomputable def qbits (x : List Bool) : List Bool := (field 2 x).length.bits
noncomputable def key (x : List Bool) : List Bool := (3*value (qbits x)).bits
noncomputable def spare (x : List Bool) : List Bool := (value (key x)+1).bits
noncomputable def leafKey (x : List Bool) : List Bool := (value (key x)+2).bits
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
noncomputable def input (x : List Bool) : List Bool := encode [field 0 x,(field 1 x).tail,field 2 x,
  field 3 x,field 4 x,field 5 x,discardPrefix (field 6 x)]
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_StartResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialQuery
open WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
def bf (j : ℕ) : List Bool→List Bool := field j ∘ discardPrefix ∘ extractPrefix
noncomputable def atPrice (x : List Bool) : List Bool :=
  encode [bf 0 x,bf 1 x,bf 2 x,bf 3 x,bf 4 x,bf 5 x,bf 6 x,discardPrefix x]
end MetricKMedianRecovery.BitMachine.BinaryInitialQuery

end OAI
end


