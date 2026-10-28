-- Prove2me | Definitions.Def_OAIQ076M002
-- name    : OAIQ076M002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:00:03.82046+00:00
-- url     : https://prove2.me/theorems/916b82cb-04ef-4a52-8bc7-6859f508f3ca
-- title:
--   Definitions bundle OAIQ076M002 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 964 declarations of OpenAI's Lean: 543 definitions, 51 inductive types or structures, 16 instances and 354 theorems. The definitions and types are `OAI.MinUncut.Costed.Arena.Init.parseWithKey`, `OAI.MinUncut.Costed.Arena.unboundedControllerInput`, `OAI.MinUncut.Costed.Arena.unboundedControllerState`, `OAI.MinUncut.Costed.FiberPrefix.args`, `OAI.MinUncut.Costed.FiberPrefix.init`, `OAI.MinUncut.Costed.FiberPrefix.state`, `OAI.MinUncut.Costed.FiberPrefix.step`, `OAI.MinUncut.Costed.FiberPrefix.transition`, `OAI.MinUncut.Costed.FiniteControl.program`, `OAI.MinUncut.Costed.FiniteControl.project`, `OAI.MinUncut.Costed.FiniteControl.stmt`, `OAI.MinUncut.Costed.FrameDecode.Mode`, `OAI.MinUncut.Costed.FrameDecode.Mode.enumList`, `OAI.MinUncut.Costed.FrameDecode.emit`, `OAI.MinUncut.Costed.FrameDecode.machine`, `OAI.MinUncut.Costed.FrameDecode.next`, `OAI.MinUncut.Costed.FrameDecode.outputs`, `OAI.MinUncut.Costed.FrameDecode.symbol`, `OAI.MinUncut.Costed.Framed.Alphabet`, `OAI.MinUncut.Costed.Framed.Label`, `OAI.MinUncut.Costed.Framed.State`, `OAI.MinUncut.Costed.Framed.Tape`, `OAI.MinUncut.Costed.Framed.extra`, `OAI.MinUncut.Costed.Framed.machine`, `OAI.MinUncut.Costed.Framed.program`, `OAI.MinUncut.Costed.Framed.readCfg`, `OAI.MinUncut.Costed.Framed.readTapes`, `OAI.MinUncut.Costed.GraphCodec.Mode`, `OAI.MinUncut.Costed.GraphCodec.Mode.enumList`, `OAI.MinUncut.Costed.GraphCodec.bitSymbol`, `OAI.MinUncut.Costed.GraphCodec.emit`, `OAI.MinUncut.Costed.GraphCodec.machine`, `OAI.MinUncut.Costed.GraphCodec.next`, `OAI.MinUncut.Costed.GraphRegisters.RenderState`, `OAI.MinUncut.Costed.GraphRegisters.RenderState.encode`, `OAI.MinUncut.Costed.GraphRegisters.canonicalTable`, `OAI.MinUncut.Costed.GraphRegisters.endpoint`, `OAI.MinUncut.Costed.GraphRegisters.initRender`, `OAI.MinUncut.Costed.GraphRegisters.localAdj`, `OAI.MinUncut.Costed.GraphRegisters.packDemand` and 554 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_GaussianSmallBall`, `MinUncut_Encoding_BinaryCoordinates`, `MinUncut_Encoding_GameEncoding`, `MinUncut_Encoding_RawGraphEncoding`, `MinUncut_Estimates_CountedWordParser`, `MinUncut_Estimates_FiberPrefix`, `MinUncut_Estimates_LiteralLocalTemplates`, `MinUncut_Estimates_PolynomialRecursor`, `MinUncut_Estimates_TM2Costed`, `MinUncut_Games_FinalCNFHeader`, `MinUncut_Games_FinalCNFPattern`, `MinUncut_Games_PoweringGlobalEnumeration`, `MinUncut_Graphs_CanonicalPathGraph`, `MinUncut_Graphs_CanonicalSamplerGraph`, `MinUncut_Graphs_DemandOrder`, `MinUncut_Graphs_GraphWordCodec`, `MinUncut_Graphs_SignedGraph`, `MinUncut_Machines_Addresses`, `MinUncut_Machines_AlphabetGraph`, `MinUncut_Machines_AlphabetReduction`, `MinUncut_Machines_AlphabetRetraction`, `MinUncut_Machines_CodeFiniteMachine`, `MinUncut_Machines_FramedWordDecoder`, `MinUncut_Machines_GraphCoreMachine`, `MinUncut_Machines_Input`, `MinUncut_Machines_Machine`, `MinUncut_Machines_MachineBinaryFormula`, `MinUncut_Machines_MachineCloudCount`, `MinUncut_Machines_MachineCloudPadding`, `MinUncut_Machines_MachineCloudPrefix`, `MinUncut_Machines_MachineCompare`, `MinUncut_Machines_MachineDrain`, `MinUncut_Machines_MachineExpanderFamilyCycle`, `MinUncut_Machines_MachineExpanderTableProgram`, `MinUncut_Machines_MachineFiniteAlphabet`, `MinUncut_Machines_MachineFiniteSequence`, `MinUncut_Machines_MachineFixedDivMod`, `MinUncut_Machines_MachineInitialHeaders`, `MinUncut_Machines_MachineLookup`, `MinUncut_Machines_MachinePreservingLookup`, `MinUncut_Machines_MachineRegularMetadata`, `MinUncut_Machines_MachineRegularOriginalBody`, `MinUncut_Machines_MachineSubroutine`, `MinUncut_Machines_MachineSubstitution`, `MinUncut_Machines_MachineTransducer`, `MinUncut_Machines_MachineTupleOdometer`, `MinUncut_Machines_MachineUnaryAdd`, `MinUncut_Machines_MachineUnaryCounter`, `MinUncut_Machines_PoweringMachineField`, `MinUncut_Machines_PoweringMachineRelation`, `MinUncut_Machines_PoweringMachineRotor`, `MinUncut_Machines_PoweringMachineRow`, `MinUncut_Machines_PoweringMachineRowHeaders`, `MinUncut_Machines_PoweringMachineVertex`, `MinUncut_Machines_RawInitialMachineFinish`, `MinUncut_Machines_Relations`, `MinUncut_Machines_Runtime`, `MinUncut_Machines_RuntimeModel`, `MinUncut_Machines_RuntimeModel2`, `MinUncut_PCP_CayleySampling`, `MinUncut_PCP_CayleySpectral`, `MinUncut_PCP_ContextPrepare`, `MinUncut_PCP_DegreeReplacement`, `MinUncut_PCP_ExpanderFamily`, `MinUncut_PCP_ExpanderRowControl`, `MinUncut_PCP_ExpanderTableEnumeration`, `MinUncut_PCP_FinalBooleanVerifier`, `MinUncut_PCP_Gap`, `MinUncut_PCP_Generator`, `MinUncut_PCP_GraphGap`, `MinUncut_PCP_GraphTables`, `MinUncut_PCP_InitialGraph`, `MinUncut_PCP_LoopOrder`, `MinUncut_PCP_PoweringOpinionTables`, `MinUncut_PCP_PoweringRowData`, `MinUncut_PCP_PoweringRowHeaderSemantics`, `MinUncut_PCP_PoweringTableLayout`, `MinUncut_PCP_PoweringTableSemantics`, `MinUncut_PCP_PreprocessingPaddingOffsets`, `MinUncut_PCP_PreprocessingRegularTables`, `MinUncut_PCP_PreprocessingTableSpectral`, `MinUncut_PCP_RawInitialPredicate`, `MinUncut_PCP_RawInitialTables`, `MinUncut_PCP_UniformRestriction`, `MinUncut_Search_RawRationalArithmetic`.
--
--   **Imports.** It imports the published bundle `Def_MinUncut`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M006`, `OAIQ076M007`, `OAIQ076M008`, `OAIQ076M010`, `OAIQ076M011`, `OAIQ076M012` and `OAIQ076M013`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_MinUncut

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RawRationalArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Preprocess
abbrev RawRat := ℕ × ℕ × ℕ
end MinUncut.Preprocess

section
attribute [fun_prop] Computable ComputablePred

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianSmallBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

open scoped BigOperators Topology
open MeasureTheory Set
namespace MinUncut.FiniteGaussian

open scoped BigOperators
open MeasureTheory

def endpoint (T : ℚ) (L i : ℕ) : ℚ := -T+2*T*i/L

open scoped BigOperators
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
attribute [local instance] Classical.propDecidable

open scoped BigOperators RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set
attribute [local instance] Classical.propDecidable

end MinUncut.FiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_BinaryCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Integration.BinaryCoordinates

abbrev Coordinates (n : Nat) := Fin n → Bool

def pack : {n : Nat} → Coordinates n → BitVec n
  | 0, _ => 0
  | _ + 1, f => BitVec.concat (pack (fun i => f i.succ)) (f 0)

def unpack {n : Nat} (v : BitVec n) : Coordinates n :=
  fun i => v.getLsbD i.val

theorem pack_get {n : Nat} (f : Coordinates n) (i : Fin n) :
    (pack f).getLsbD i.val = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact BitVec.getLsbD_concat_zero
    · exact (BitVec.getLsbD_concat_succ).trans (ih (fun j => f j.succ) j)

theorem unpack_pack {n : Nat} (f : Coordinates n) : unpack (pack f) = f := by
  funext i
  exact pack_get f i

theorem pack_unpack {n : Nat} (v : BitVec n) : pack (unpack v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact pack_get (unpack v) ⟨i, hi⟩

end MinUncutGames.Integration.BinaryCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_GameEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity

def parseLabel (alphabet value : Nat) : Option (Fin alphabet) :=
  if bounded : value < alphabet then some ⟨value, bounded⟩ else none

@[simp] theorem parseLabel_value {q : Nat} (label : Fin q) :
    parseLabel q label.val = some label := by simp [parseLabel, label.isLt]

@[simp] theorem parseLabels_values {q : Nat} (labels : List (Fin q)) :
    (labels.map Fin.val).mapM (parseLabel q) = some labels := by
  induction labels with
  | nil => rfl
  | cons label labels ih => simp [ih]

end MinUncutGames.Foundations.Complexity

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_PolynomialRecursor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Costed.PolyProgram
open Turing.ToPartrec Polynomial

def scalarRec (f g : List ℕ → List ℕ) (v : List ℕ) : ℕ → ℕ
  | 0 => (f v).headI
  | i+1 => (g (i::scalarRec f g v i::v)).headI

end MinUncut.Costed.PolyProgram

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_SignedGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.PathRealization
attribute [local instance] Classical.propDecidable

structure Demand (V : Type*) where
  left : V
  right : V
  equal : Bool

variable {V D : Type*}
abbrev Vertex (V D : Type*) := V ⊕ (D × Fin 3)

abbrev EdgeIndex (e : D → Demand V) := {p : D×Fin 4 // p.2.val < if (e p.1).equal then 4 else 3}

def ends (e : D → Demand V) (p : D×Fin 4) : Vertex V D × Vertex V D :=
  match p.2.val with
  | 0 => (.inl (e p.1).left,.inr (p.1,0))
  | 1 => (.inr (p.1,0),.inr (p.1,1))
  | 2 => if (e p.1).equal then (.inr (p.1,1),.inr (p.1,2))
      else (.inr (p.1,1),.inl (e p.1).right)
  | _ => (.inr (p.1,2),.inl (e p.1).right)

lemma ends_ne (e : D → Demand V) (p : EdgeIndex e) :
    (ends e p.val).1 ≠ (ends e p.val).2 := by
  obtain ⟨⟨d,i⟩,hi⟩ := p
  fin_cases i <;> simp only [ends] <;> (try split_ifs) <;> simp

end MinUncut.PathRealization

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_CanonicalPathGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace MinUncut.PathRealization

def number (N M : ℕ) : Vertex (Fin N) (Fin M) ≃ Fin (N+M*3) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

lemma number_left (N M : ℕ) (v : Fin N) : (number N M (.inl v)).val=v.val := rfl
lemma number_right (N M : ℕ) (d : Fin M) (i : Fin 3) :
    (number N M (.inr (d,i))).val=N+i.val+3*d.val := by
  simp [number,finProdFinEquiv,finSumFinEquiv,Nat.add_assoc]

def canonicalAdjacent {N M : ℕ} (e : Fin M → Demand (Fin N))
    (u v : Fin (N+M*3)) : Bool :=
  decide (∃ d : Fin M, ∃ j : Fin 4,
    j.val < (if (e d).equal then 4 else 3) ∧
      ((u=number N M (ends e (d,j)).1 ∧ v=number N M (ends e (d,j)).2) ∨
       (v=number N M (ends e (d,j)).1 ∧ u=number N M (ends e (d,j)).2)))

lemma canonicalAdjacent_symmetric {N M : ℕ} (e : Fin M → Demand (Fin N))
    (u v : Fin (N+M*3)) : canonicalAdjacent e u v=canonicalAdjacent e v u := by
  simp only [canonicalAdjacent,decide_eq_decide]
  apply exists_congr
  intro d
  apply exists_congr
  intro j
  exact and_congr_right (fun _ => or_comm)

lemma canonicalAdjacent_loopless {N M : ℕ} (e : Fin M → Demand (Fin N))
    (u : Fin (N+M*3)) : canonicalAdjacent e u u=false := by
  simp only [canonicalAdjacent,decide_eq_false_iff_not]
  rintro ⟨d,j,hj,h|h⟩ <;>
    exact ends_ne e ⟨(d,j),hj⟩ ((number N M).injective (h.1.symm.trans h.2))

def canonicalOutput {N M : ℕ} (e : Fin M → Demand (Fin N)) (k : ℕ) (hk : 1≤k) : Output where
  vertices := N+M*3
  adjacent := canonicalAdjacent e
  symmetric := canonicalAdjacent_symmetric e
  loopless := canonicalAdjacent_loopless e
  threshold := k
  threshold_pos := hk

end MinUncut.PathRealization

end
namespace MinUncut.Costed.GraphRegisters

open PolyProgram Polynomial

open PolyProgram Polynomial

structure RenderState where
  N : ℕ
  M : ℕ
  threshold : ℕ
  V : ℕ
  row : ℕ
  col : ℕ
  q : ℕ
  tape : List ℕ

def RenderState.encode (s : RenderState) : List ℕ :=
  s.N::s.M::s.threshold::s.V::s.row::s.col::s.q::s.tape

def parseState (v : List ℕ) : RenderState :=
  ⟨v.headI,(v.drop 1).headI,(v.drop 2).headI,(v.drop 3).headI,
    (v.drop 4).headI,(v.drop 5).headI,(v.drop 6).headI,v.drop 7⟩

@[simp] lemma parse_encode (s : RenderState) : parseState s.encode=s := by
  cases s; rfl

open MinUncut.PathRealization
open PolyProgram

def queryState (N M k V u v : ℕ) (acc data : List ℕ) : RenderState :=
  ⟨N,M,k,V,u,v,acc.length,acc++2::k::data⟩

def endpoint (u v a b : ℕ) : Prop := (u=a ∧ v=b) ∨ (u=b ∧ v=a)
instance instDecidableEndpoint (u v a b : ℕ) : Decidable (endpoint u v a b) := inferInstanceAs (Decidable (_∨_))

def localAdj (N d l r e u v : ℕ) : Prop :=
  endpoint u v l (N+3*d) ∨ endpoint u v (N+3*d) (N+3*d+1) ∨
    if e=0 then endpoint u v (N+3*d+1) r
    else endpoint u v (N+3*d+1) (N+3*d+2) ∨ endpoint u v (N+3*d+2) r
instance instDecidableLocalAdj (N d l r e u v : ℕ) : Decidable (localAdj N d l r e u v) := by
  unfold localAdj; infer_instance

def rawLocal (N d : ℕ) (data : List ℕ) (u v : ℕ) : Prop :=
  localAdj N d (data.drop (3*d)).headI (data.drop (3*d+1)).headI
    (data.drop (3*d+2)).headI u v
instance instDecidableRawLocal (N d : ℕ) (data : List ℕ) (u v : ℕ) : Decidable (rawLocal N d data u v) :=
  inferInstanceAs (Decidable (localAdj ..))

lemma data_address (N M k V u v d a j : ℕ) (acc data : List ℕ) :
    ((d::a::(queryState N M k V u v acc data).encode).drop
      (11+acc.length+3*d+j)).headI=(data.drop (3*d+j)).headI := by
  have he : 11+acc.length+3*d+j=9+(acc.length+(2+(3*d+j))) := by omega
  rw [he,← List.drop_drop]
  change ((acc++2::k::data).drop (acc.length+(2+(3*d+j)))).headI=_
  rw [← List.drop_drop,List.drop_left]
  rw [Nat.add_comm 2 _]
  rfl

lemma bit_or (P Q : Prop) [Decidable P] [Decidable Q] :
    (if (if P then 1 else 0 : ℕ)=0 then (if Q then 1 else 0) else 1)=
      if P∨Q then 1 else 0 := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp,hq]

def rawCell (N M : ℕ) (data : List ℕ) (u v : ℕ) : ℕ :=
  if ∃ d<M, rawLocal N d data u v then 1 else 0

end MinUncut.Costed.GraphRegisters

open scoped BigOperators

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_RawGraphEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Costed.GraphRegisters
open MinUncut.PathRealization

def packDemand {N : ℕ} (d : Demand (Fin N)) : List ℕ :=
  [d.left.val,d.right.val,d.equal.toNat]
def packDemands {N : ℕ} (ds : List (Demand (Fin N))) : List ℕ := ds.flatMap packDemand

lemma canonicalLocal_iff {N M : ℕ} (e : Fin M → Demand (Fin N)) (d : Fin M)
    (u v : Fin (N+M*3)) :
    (∃j:Fin 4, j.val<(if (e d).equal then 4 else 3) ∧
      ((u=number N M (ends e (d,j)).1 ∧ v=number N M (ends e (d,j)).2) ∨
       (v=number N M (ends e (d,j)).1 ∧ u=number N M (ends e (d,j)).2))) ↔
    localAdj N d.val (e d).left.val (e d).right.val (e d).equal.toNat u.val v.val := by
  simp only [show (4:ℕ)=3+1 from rfl,Fin.exists_fin_succ]
  simp only [Fin.val_zero,Fin.val_succ]
  cases h : (e d).equal <;>
    simp [h,ends,localAdj,endpoint,Fin.ext_iff,number_left,number_right,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,and_comm,or_assoc,or_comm,or_left_comm]

end MinUncut.Costed.GraphRegisters

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Runtime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineEmbedding

open Turing.TM2

variable {K E Λ Λextra σ τ : Type} {Γ : K → Type} {Δ : E → Type}

abbrev Alphabet (Γ : K → Type) (Δ : E → Type) : K ⊕ E → Type
  | .inl k => Γ k
  | .inr e => Δ e

def tapes (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e)) :
    ∀ j, List (Alphabet Γ Δ j)
  | .inl k => source k
  | .inr e => extra e

@[simp] theorem tapes_inl (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (k : K) : tapes source extra (.inl k) = source k := rfl

@[simp] theorem tapes_inr (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (e : E) : tapes source extra (.inr e) = extra e := rfl

def label (haltTarget : Option (Λ ⊕ Λextra)) : Option Λ → Option (Λ ⊕ Λextra)
  | none => haltTarget
  | some l => some (.inl l)

def configuration (haltTarget : Option (Λ ⊕ Λextra)) (extraState : τ)
    (extraTapes : ∀ e, List (Δ e)) (c : Cfg Γ Λ σ) :
    Cfg (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ) where
  l := label haltTarget c.l
  var := (c.var, extraState)
  stk := tapes c.stk extraTapes

def statement (haltTarget : Option (Λ ⊕ Λextra)) :
    Stmt Γ Λ σ → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)
  | .push k f next => .push (.inl k) (fun st => f st.1) (statement haltTarget next)
  | .peek k f next => .peek (.inl k) (fun st v => (f st.1 v, st.2))
      (statement haltTarget next)
  | .pop k f next => .pop (.inl k) (fun st v => (f st.1 v, st.2))
      (statement haltTarget next)
  | .load f next => .load (fun st => (f st.1, st.2)) (statement haltTarget next)
  | .branch f yes no => .branch (fun st => f st.1)
      (statement haltTarget yes) (statement haltTarget no)
  | .goto f => .goto (fun st => .inl (f st.1))
  | .halt => match haltTarget with
      | none => .halt
      | some l => .goto (fun _ => l)

variable [DecidableEq K] [DecidableEq E]

theorem tapes_update (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (k : K) (value : List (Γ k)) :
    tapes (Function.update source k value) extra =
      Function.update (tapes source extra) (.inl k) value := by
  funext j
  cases j with
  | inl j =>
    by_cases h : j = k
    · subst j
      simp [Function.update]
    · simp [Function.update, h]
  | inr e => simp [Function.update]

theorem stepAux_simulation (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (q : Stmt Γ Λ σ) (state : σ) (source : ∀ k, List (Γ k)) :
    stepAux (statement haltTarget q) (state, extraState) (tapes source extraTapes) =
      configuration haltTarget extraState extraTapes (stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
    simp only [statement, stepAux, tapes_inl]
    rw [← tapes_update]
    exact ih state (Function.update source k (f state :: source k))
  | peek k f next ih =>
    simpa only [statement, stepAux, tapes_inl] using
      ih (f state (source k).head?) source
  | pop k f next ih =>
    simp only [statement, stepAux, tapes_inl]
    rw [← tapes_update]
    exact ih (f state (source k).head?) (Function.update source k (source k).tail)
  | load f next ih =>
    simpa only [statement, stepAux] using ih (f state) source
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [statement, stepAux, h, Bool.cond_false] using ihNo state source
    | true => simpa only [statement, stepAux, h, Bool.cond_true] using ihYes state source
  | goto f => rfl
  | halt => cases haltTarget <;> rfl

def program (haltTarget : Option (Λ ⊕ Λextra)) (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)) :
    Λ ⊕ Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)
  | .inl l => statement haltTarget (source l)
  | .inr l => extra l

theorem step_running (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ))
    (l : Λ) (state : σ) (sourceTapes : ∀ k, List (Γ k)) :
    step (program haltTarget source extra)
      (configuration haltTarget extraState extraTapes ⟨some l, state, sourceTapes⟩) =
      some (configuration haltTarget extraState extraTapes
        (stepAux (source l) state sourceTapes)) := by
  change some (stepAux (statement haltTarget (source l)) (state, extraState)
    (tapes sourceTapes extraTapes)) = _
  rw [stepAux_simulation]

theorem step_simulation (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ))
    (a b : Cfg Γ Λ σ) (h : step source a = some b) :
    step (program haltTarget source extra)
      (configuration haltTarget extraState extraTapes a) =
      some (configuration haltTarget extraState extraTapes b) := by
  cases a with
  | mk l state sourceTapes =>
    cases l with
    | none => simp [step] at h
    | some l =>
      have hb : stepAux (source l) state sourceTapes = b := Option.some.inj h
      rw [← hb]
      exact step_running haltTarget extraState extraTapes source extra l state sourceTapes

end MinUncutGames.Foundations.Complexity.MachineEmbedding

namespace MinUncutGames.Reduction.MachineTransfer

open _root_.Turing

variable {α β : Type} [Fintype α] [Fintype β]

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

def exitAt (dst : K) (exit : Option Λ) : TM2.Stmt Γ Λ (σ × Option (Γ dst)) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def loopAt (src dst : K) (f : Γ src → Γ dst) (fallback : Γ dst)
    (loopLabel : Λ) (exit : Option Λ) : TM2.Stmt Γ Λ (σ × Option (Γ dst)) :=
  .pop src (fun state head => (state.1, head.map f))
    (.branch (fun state => state.2.isSome)
      (.push dst (fun state => state.2.getD fallback) (.goto fun _ => loopLabel))
      (exitAt dst exit))

def nextAt (dst : K) (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (configuration : Option (TM2.Cfg Γ Λ (σ × Option (Γ dst)))) :
    Option (TM2.Cfg Γ Λ (σ × Option (Γ dst))) :=
  configuration.bind (TM2.step program)

end MinUncutGames.Reduction.MachineTransfer

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineDrain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineDrain

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def drain (source : K) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun _ => again)
      (.load (fun state => (state.1, none)) (Reduction.MachineTransfer.exitAt source exit)))

end MinUncutGames.Foundations.Complexity.MachineDrain

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineFiniteSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineFiniteSequence

open _root_.Turing

variable {Command : Type} (LocalLabel : Command → Type)

def Label : List Command → Type
  | [] => Empty
  | command :: commands => LocalLabel command ⊕ Label commands

variable (main : ∀ command, LocalLabel command)
variable {K Λ σ : Type} {Γ : K → Type}

def entry : (commands : List Command) → (Label LocalLabel commands → Λ) → Option Λ → Option Λ
  | [], _, exit => exit
  | command :: _, labels, _ => some (labels (.inl (main command)))

variable (localInstruction : ∀ command, (LocalLabel command → Λ) → Option Λ →
  LocalLabel command → TM2.Stmt Γ Λ σ)

def instruction : (commands : List Command) → (Label LocalLabel commands → Λ) → Option Λ →
    Label LocalLabel commands → TM2.Stmt Γ Λ σ
  | [], _, _, label => nomatch label
  | command :: commands, labels, exit, .inl label =>
      localInstruction command (fun l => labels (.inl l))
        (entry LocalLabel main commands (fun l => labels (.inr l)) exit) label
  | _ :: commands, labels, exit, .inr label =>
      instruction commands (fun l => labels (.inr l)) exit label

variable {Data : Type} (result : Command → Data → Data) (cost : Command → Data → Nat)

def resultOf : List Command → Data → Data
  | [], data => data
  | command :: commands, data => resultOf commands (result command data)

def steps : List Command → Data → Nat
  | [], _ => 0
  | command :: commands, data => cost command data + steps commands (result command data)

end MinUncutGames.Foundations.Complexity.MachineFiniteSequence

namespace MinUncutGames.Foundations.Complexity.MachineDrainMany

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev Tapes (K : Type) := K → List Bool
abbrev LocalLabel (_ : K) := Unit
abbrev Label (chosen : List K) := MachineFiniteSequence.Label (LocalLabel (K := K)) chosen
abbrev Data (K : Type) := Tapes K × Option Bool

def entry (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel (K := K)) (fun _ => ()) chosen labels exit

def localInstruction (source : K) (labels : Unit → Λ) (exit : Option Λ) (_ : Unit) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineDrain.drain source (labels ()) exit

def instruction (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ) :
    Label chosen → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineFiniteSequence.instruction (LocalLabel (K := K)) (fun _ => ())
    localInstruction chosen labels exit

def result (source : K) (data : Data K) : Data K :=
  (Function.update data.1 source [], none)

def cost (source : K) (data : Data K) : Nat := (data.1 source).length + 1

def finalTapes : List K → Tapes K → Tapes K
  | [], base => base
  | source :: chosen, base => finalTapes chosen (Function.update base source [])

def finalRegister : List K → Option Bool → Option Bool
  | [], register => register
  | _ :: _, _ => none

omit [DecidableEq K] in
@[simp] theorem finalRegister_none (chosen : List K) : finalRegister chosen none = none := by
  cases chosen <;> rfl

def steps : List K → Tapes K → Nat
  | [], _ => 0
  | source :: chosen, base => (base source).length + 1 +
      steps chosen (Function.update base source [])

@[simp] theorem sequence_result (chosen : List K) (base : Tapes K) (register : Option Bool) :
    MachineFiniteSequence.resultOf result chosen (base, register) =
      (finalTapes chosen base, finalRegister chosen register) := by
  induction chosen generalizing base register with
  | nil => rfl
  | cons source chosen ih =>
      change MachineFiniteSequence.resultOf result chosen (Function.update base source [], none) =
        (finalTapes chosen (Function.update base source []), none)
      rw [ih, finalRegister_none]

@[simp] theorem sequence_steps (chosen : List K) (base : Tapes K) (register : Option Bool) :
    MachineFiniteSequence.steps result cost chosen (base, register) = steps chosen base := by
  induction chosen generalizing base register with
  | nil => rfl
  | cons source chosen ih =>
      simp only [MachineFiniteSequence.steps, result, cost, steps, ih]

theorem finalTapes_apply (chosen : List K) (base : Tapes K) (k : K) :
    finalTapes chosen base k = if k ∈ chosen then [] else base k := by
  induction chosen generalizing base with
  | nil => simp [finalTapes]
  | cons source chosen ih =>
      rw [finalTapes, ih]
      by_cases h : k = source
      · subst k
        simp
      · simp [List.mem_cons, h]

def workTapes {N : Nat} (enumeration : Fin N ≃ K) (output : K) : List K :=
  (List.ofFn (fun i => enumeration i)).filter (fun k => decide (k ≠ output))

@[simp] theorem mem_workTapes {N : Nat} (enumeration : Fin N ≃ K) (output k : K) :
    k ∈ workTapes enumeration output ↔ k ≠ output := by
  have hmem : k ∈ List.ofFn (fun i => enumeration i) := by
    apply List.mem_ofFn.mpr
    exact ⟨enumeration.symm k, enumeration.apply_symm_apply k⟩
  simp [workTapes, hmem]

end MinUncutGames.Foundations.Complexity.MachineDrainMany

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineSubroutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineSubroutine

open _root_.Turing

variable {K Λ Λ' σ : Type} {Γ : K → Type}

def label (labels : Λ → Λ') (exit : Option Λ') : Option Λ → Option Λ'
  | none => exit
  | some l => some (labels l)

def statement (labels : Λ → Λ') (exit : Option Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f next => .push k f (statement labels exit next)
  | .peek k f next => .peek k f (statement labels exit next)
  | .pop k f next => .pop k f (statement labels exit next)
  | .load f next => .load f (statement labels exit next)
  | .branch f yes no => .branch f (statement labels exit yes) (statement labels exit no)
  | .goto f => .goto (fun s => labels (f s))
  | .halt => match exit with
      | none => .halt
      | some l => .goto (fun _ => l)

end MinUncutGames.Foundations.Complexity.MachineSubroutine

namespace MinUncutGames.Foundations.Complexity.MachineStateFrame

open _root_.Turing

variable {K Λ Λ' σ τ : Type} {Γ : K → Type}

def frameStatement : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ (σ × τ)
  | .push k f next => .push k (fun state => f state.1) (frameStatement next)
  | .peek k f next => .peek k (fun state bit => (f state.1 bit, state.2))
      (frameStatement next)
  | .pop k f next => .pop k (fun state bit => (f state.1 bit, state.2))
      (frameStatement next)
  | .load f next => .load (fun state => (f state.1, state.2)) (frameStatement next)
  | .branch f yes no => .branch (fun state => f state.1)
      (frameStatement yes) (frameStatement no)
  | .goto f => .goto (fun state => f state.1)
  | .halt => .halt

def frameConfiguration (ambient : τ) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ (σ × τ) :=
  ⟨c.l, (c.var, ambient), c.stk⟩

def frameProgram (source : Λ → TM2.Stmt Γ Λ σ) : Λ → TM2.Stmt Γ Λ (σ × τ) :=
  fun label => frameStatement (source label)

@[simp] theorem frameConfiguration_state (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).var.1 = c.var := rfl

@[simp] theorem frameConfiguration_metadata (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).var.2 = ambient := rfl

@[simp] theorem frameConfiguration_tapes (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).stk = c.stk := rfl

variable [DecidableEq K]

theorem frame_stepAux (q : TM2.Stmt Γ Λ σ) (state : σ) (ambient : τ)
    (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (frameStatement q) (state, ambient) tapes =
      frameConfiguration ambient (TM2.stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using
      ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using
      ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => simpa only [frameStatement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [frameStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
    | true => simpa only [frameStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => rfl

theorem frame_step (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (c : TM2.Cfg Γ Λ σ) :
    TM2.step (frameProgram source) (frameConfiguration ambient c) =
      (TM2.step source c).map (frameConfiguration ambient) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => rfl
  | some label =>
    change some (TM2.stepAux (frameStatement (source label)) (state, ambient) tapes) = _
    rw [frame_stepAux]
    rfl

end MinUncutGames.Foundations.Complexity.MachineStateFrame

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Machine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceMachine

open _root_.Turing
open MinUncutGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def fieldLoop (source destination : K) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push destination (fun _ => true) (.goto fun _ => loopLabel))
      (.load (fun state => (state.1, none))
        (Reduction.MachineTransfer.exitAt destination exit)))

def fieldStart (destination : K) (loopLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .push destination (fun _ => false) (.goto fun _ => loopLabel)

def fieldTapes (source destination : K) (base : K → List Bool)
    (input output : List Bool) : K → List Bool :=
  Function.update (Function.update base source input) destination output

@[simp] theorem fieldTapes_source (source destination : K) (hne : source ≠ destination)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output source = input := by
  simp [fieldTapes, hne]

@[simp] theorem fieldTapes_destination (source destination : K)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output destination = output := by
  simp [fieldTapes]

@[simp] theorem fieldTapes_self (source destination : K) (base : K → List Bool) :
    fieldTapes source destination base (base source) (base destination) = base := by
  simp [fieldTapes]

end MinUncutGames.Foundations.Hastad.SourceMachine

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineUnaryCounter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineUnaryCounter

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def guard (counter : K) (bodyLabel exitLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek counter (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.pop counter (fun state _ => (state.1, none)) (.goto fun _ => bodyLabel))
      (.load (fun state => (state.1, none)) (.goto fun _ => exitLabel)))

end MinUncutGames.Foundations.Complexity.MachineUnaryCounter

namespace MinUncutGames.Foundations.Complexity.MachineLookup

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def discard (source : K) (loopLabel returnLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.goto fun _ => loopLabel)
      (.load (fun state => (state.1, none)) (.goto fun _ => returnLabel)))

def select (source destination : K) (copyLabel rejected : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (Hastad.SourceMachine.fieldStart destination copyLabel)
      (.load (fun state => (state.1, none)) (.goto fun _ => rejected)))

inductive Label
  | guard | skip | select | copy | accepted | rejected
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.guard, .skip, .select, .copy, .accepted,
  .rejected]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def program (index source destination : K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .guard => MachineUnaryCounter.guard index .skip .select
  | .skip => discard source .skip .guard
  | .select => select source destination .copy .rejected
  | .copy => Hastad.SourceMachine.fieldLoop source destination .copy (some .accepted)
  | .accepted => .halt
  | .rejected => .halt

def tapes (index source destination : K) (base : K → List Bool)
    (counter input output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base index counter) source input)
    destination output

@[simp] theorem tapes_index (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output index = counter := by
  simp [tapes, his, hid]

@[simp] theorem tapes_source (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter input output : List Bool) :
    tapes index source destination base counter input output source = input := by
  simp [tapes, hsd]

@[simp] theorem tapes_destination (index source destination : K)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output destination = output := by
  simp [tapes]

open _root_.Turing

end MinUncutGames.Foundations.Complexity.MachineLookup

namespace MinUncutGames.Foundations.Complexity.MachineCopy

open _root_.Turing

variable {K Λ σ β : Type} [DecidableEq K]

abbrev Alphabet (β : Type) (_ : K) := β

def forkLoop (source left right : K) (fallback : β) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push left (fun state => state.2.getD fallback)
        (.push right (fun state => state.2.getD fallback) (.goto fun _ => loopLabel)))
      (Reduction.MachineTransfer.exitAt right exit))

def forkTapes (source left right : K) (base : K → List β)
    (input leftOutput rightOutput : List β) : K → List β :=
  Function.update (Function.update (Function.update base source input) left leftOutput)
    right rightOutput

@[simp] theorem forkTapes_source (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right)
    (base : K → List β) (input leftOutput rightOutput : List β) :
    forkTapes source left right base input leftOutput rightOutput source = input := by
  simp [forkTapes, sourceLeft, sourceRight]

@[simp] theorem forkTapes_left (source left right : K) (leftRight : left ≠ right)
    (base : K → List β) (input leftOutput rightOutput : List β) :
    forkTapes source left right base input leftOutput rightOutput left = leftOutput := by
  simp [forkTapes, leftRight]

@[simp] theorem forkTapes_right (source left right : K)
    (base : K → List β) (input leftOutput rightOutput : List β) :
    forkTapes source left right base input leftOutput rightOutput right = rightOutput := by
  simp [forkTapes]

@[simp] theorem forkTapes_self (source left right : K) (base : K → List β) :
    forkTapes source left right base (base source) (base left) (base right) = base := by
  simp [forkTapes]

end MinUncutGames.Foundations.Complexity.MachineCopy

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineControl

open Turing.TM2

variable {K Λ Λ' σ σ' : Type} {Γ : K → Type}

def configuration (labels : Λ → Λ') (states : σ ≃ σ') (c : Cfg Γ Λ σ) :
    Cfg Γ Λ' σ' where
  l := c.l.map labels
  var := states c.var
  stk := c.stk

def statement (labels : Λ → Λ') (states : σ ≃ σ') : Stmt Γ Λ σ → Stmt Γ Λ' σ'
  | .push k f next => .push k (fun st => f (states.symm st)) (statement labels states next)
  | .peek k f next => .peek k (fun st v => states (f (states.symm st) v))
      (statement labels states next)
  | .pop k f next => .pop k (fun st v => states (f (states.symm st) v))
      (statement labels states next)
  | .load f next => .load (fun st => states (f (states.symm st)))
      (statement labels states next)
  | .branch f yes no => .branch (fun st => f (states.symm st))
      (statement labels states yes) (statement labels states no)
  | .goto f => .goto (fun st => labels (f (states.symm st)))
  | .halt => .halt

variable [DecidableEq K]

theorem stepAux_simulation (labels : Λ → Λ') (states : σ ≃ σ')
    (q : Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    stepAux (statement labels states q) (states state) tapes =
      configuration labels states (stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false =>
      simpa only [statement, stepAux, Equiv.symm_apply_apply, h, Bool.cond_false] using
        ihNo state tapes
    | true =>
      simpa only [statement, stepAux, Equiv.symm_apply_apply, h, Bool.cond_true] using
        ihYes state tapes
  | goto f => simp [statement, stepAux, configuration]
  | halt => rfl

end MinUncutGames.Foundations.Complexity.MachineControl

namespace MinUncutGames.Foundations.Complexity.MachineFieldProfile

open _root_.Turing

abbrev Profile (q : Nat) := Fin q → Fin q → Bool

def equalityProfile {q : Nat} (words : Fin q → List Bool) : Profile q :=
  fun i j => decide (words i = words j)

abbrev Tape (q : Nat) := Fin q ⊕ Fin 3

end MinUncutGames.Foundations.Complexity.MachineFieldProfile

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ContextPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceContextPrepare

open _root_.Turing MinUncutGames.Foundations.Complexity
abbrev LoadState := Unit × Option Bool

end MinUncutGames.Foundations.Hastad.SourceContextPrepare

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineSubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Reduction.MachineSubstitution

open _root_.Turing

open MinUncutGames.Foundations.Complexity

section PushWord

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

def pushWord (dst : K) : List (Γ dst) → TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ σ
  | [], continuation => continuation
  | symbol :: word, continuation =>
      .push dst (fun _ => symbol) (pushWord dst word continuation)

end PushWord

end MinUncutGames.Reduction.MachineSubstitution

end
section
namespace MinUncutGames.Foundations.Complexity.MachineStackSwap

open Turing.TM2

variable {A B C Λ σ : Type}
  {ΓA : A → Type} {ΓB : B → Type} {ΓC : C → Type}

abbrev Alphabet (ΓA : A → Type) (ΓB : B → Type) (ΓC : C → Type) :=
  MachineEmbedding.Alphabet ΓA (MachineEmbedding.Alphabet ΓB ΓC)

def tapes (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) :
    ∀ j, List (Alphabet ΓB ΓA ΓC j)
  | .inl b => source (.inr (.inl b))
  | .inr (.inl a) => source (.inl a)
  | .inr (.inr c) => source (.inr (.inr c))

@[simp] theorem tapes_first (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (a : A) :
    tapes source (.inr (.inl a)) = source (.inl a) := rfl
@[simp] theorem tapes_second (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (b : B) :
    tapes source (.inl b) = source (.inr (.inl b)) := rfl
@[simp] theorem tapes_third (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (c : C) :
    tapes source (.inr (.inr c)) = source (.inr (.inr c)) := rfl

def configuration (c : Cfg (Alphabet ΓA ΓB ΓC) Λ σ) :
    Cfg (Alphabet ΓB ΓA ΓC) Λ σ where
  l := c.l
  var := c.var
  stk := tapes c.stk

def statement : Stmt (Alphabet ΓA ΓB ΓC) Λ σ → Stmt (Alphabet ΓB ΓA ΓC) Λ σ
  | .push (.inl a) f next => .push (.inr (.inl a)) f (statement next)
  | .push (.inr (.inl b)) f next => .push (.inl b) f (statement next)
  | .push (.inr (.inr c)) f next => .push (.inr (.inr c)) f (statement next)
  | .peek (.inl a) f next => .peek (.inr (.inl a)) f (statement next)
  | .peek (.inr (.inl b)) f next => .peek (.inl b) f (statement next)
  | .peek (.inr (.inr c)) f next => .peek (.inr (.inr c)) f (statement next)
  | .pop (.inl a) f next => .pop (.inr (.inl a)) f (statement next)
  | .pop (.inr (.inl b)) f next => .pop (.inl b) f (statement next)
  | .pop (.inr (.inr c)) f next => .pop (.inr (.inr c)) f (statement next)
  | .load f next => .load f (statement next)
  | .branch f yes no => .branch f (statement yes) (statement no)
  | .goto f => .goto f
  | .halt => .halt

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem tapes_update_first (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (a : A) (value : List (ΓA a)) :
    tapes (Function.update source (.inl a) value) =
      Function.update (tapes source) (.inr (.inl a)) value := by
  funext j
  rcases j with b | a' | c
  · simp [Function.update]
  · by_cases h : a' = a
    · subst a'; simp [Function.update]
    · simp [Function.update, h]
  · simp [Function.update]

theorem tapes_update_second (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (b : B) (value : List (ΓB b)) :
    tapes (Function.update source (.inr (.inl b)) value) =
      Function.update (tapes source) (.inl b) value := by
  funext j
  rcases j with b' | a | c
  · by_cases h : b' = b
    · subst b'; simp [Function.update]
    · simp [Function.update, h]
  · simp [Function.update]
  · simp [Function.update]

theorem tapes_update_third (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (c : C) (value : List (ΓC c)) :
    tapes (Function.update source (.inr (.inr c)) value) =
      Function.update (tapes source) (.inr (.inr c)) value := by
  funext j
  rcases j with b | a | c'
  · simp [Function.update]
  · simp [Function.update]
  · by_cases h : c' = c
    · subst c'; simp [Function.update]
    · simp [Function.update, h]

theorem stepAux_simulation (q : Stmt (Alphabet ΓA ΓB ΓC) Λ σ)
    (state : σ) (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) :
    stepAux (statement q) state (tapes source) =
      configuration (stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
    rcases k with a | b | c
    · simp only [statement, stepAux, tapes_first]
      rw [← tapes_update_first]
      exact ih state (Function.update source (.inl a) (f state :: source (.inl a)))
    · simp only [statement, stepAux, tapes_second]
      rw [← tapes_update_second]
      exact ih state (Function.update source (.inr (.inl b))
        (f state :: source (.inr (.inl b))))
    · simp only [statement, stepAux, tapes_third]
      rw [← tapes_update_third]
      exact ih state (Function.update source (.inr (.inr c))
        (f state :: source (.inr (.inr c))))
  | peek k f next ih =>
    rcases k with a | b | c
    · simpa only [statement, stepAux, tapes_first] using
        ih (f state (source (.inl a)).head?) source
    · simpa only [statement, stepAux, tapes_second] using
        ih (f state (source (.inr (.inl b))).head?) source
    · simpa only [statement, stepAux, tapes_third] using
        ih (f state (source (.inr (.inr c))).head?) source
  | pop k f next ih =>
    rcases k with a | b | c
    · simp only [statement, stepAux, tapes_first]
      rw [← tapes_update_first]
      exact ih (f state (source (.inl a)).head?)
        (Function.update source (.inl a) (source (.inl a)).tail)
    · simp only [statement, stepAux, tapes_second]
      rw [← tapes_update_second]
      exact ih (f state (source (.inr (.inl b))).head?)
        (Function.update source (.inr (.inl b)) (source (.inr (.inl b))).tail)
    · simp only [statement, stepAux, tapes_third]
      rw [← tapes_update_third]
      exact ih (f state (source (.inr (.inr c))).head?)
        (Function.update source (.inr (.inr c)) (source (.inr (.inr c))).tail)
  | load f next ih => simpa only [statement, stepAux] using ih (f state) source
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [statement, stepAux, h, Bool.cond_false] using ihNo state source
    | true => simpa only [statement, stepAux, h, Bool.cond_true] using ihYes state source
  | goto f => rfl
  | halt => rfl

end MinUncutGames.Foundations.Complexity.MachineStackSwap

end
section
namespace MinUncutGames.Foundations.Complexity.MachineSequential

open _root_.Turing

abbrev Tape (first second : FinTM2) := first.K ⊕ (second.K ⊕ Unit)
abbrev Symbols (first second : FinTM2) : Tape first second → Type :=
  MachineEmbedding.Alphabet first.Γ
    (MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
abbrev Label (first second : FinTM2) := first.Λ ⊕ (Bool ⊕ second.Λ)
abbrev Register (second : FinTM2) := Option (second.Γ second.k₀)
abbrev State (first second : FinTM2) := (first.σ × second.σ) × Register second

def firstStates (first second : FinTM2) :
    first.σ × (second.σ × Register second) ≃ State first second where
  toFun st := ((st.1, st.2.1), st.2.2)
  invFun st := (st.1.1, (st.1.2, st.2))
  left_inv _ := rfl
  right_inv _ := rfl

def secondStates (first second : FinTM2) :
    second.σ × (first.σ × Register second) ≃ State first second where
  toFun st := ((st.2.1, st.1), st.2.2)
  invFun st := (st.1.2, (st.1.1, st.2))
  left_inv _ := rfl
  right_inv _ := rfl

def secondLabels (first second : FinTM2) :
    second.Λ ⊕ (Bool ⊕ first.Λ) → Label first second
  | .inl label => .inr (.inr label)
  | .inr (.inl bit) => .inr (.inl bit)
  | .inr (.inr label) => .inl label

def bridgeLabel (first second : FinTM2) (bit : Bool) : Label first second :=
  .inr (.inl bit)

def firstStatement (first second : FinTM2) (q : first.Stmt) :
    TM2.Stmt (Symbols first second) (Label first second) (State first second) :=
  MachineControl.statement id (firstStates first second)
    (MachineEmbedding.statement (some (bridgeLabel first second false)) q)

def secondStatement (first second : FinTM2) (q : second.Stmt) :
    TM2.Stmt (Symbols first second) (Label first second) (State first second) :=
  MachineControl.statement (secondLabels first second) (secondStates first second)
    (MachineStackSwap.statement
      (MachineEmbedding.statement
        (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
        (Λextra := Bool ⊕ first.Λ) none q))

def program (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) :
    Label first second → TM2.Stmt (Symbols first second) (Label first second)
      (State first second)
  | .inl label => firstStatement first second (first.m label)
  | .inr (.inr label) => secondStatement first second (second.m label)
  | .inr (.inl false) =>
      Reduction.MachineTransfer.loopAt (Γ := Symbols first second)
        (.inl first.k₁) (.inr (.inr ())) relabel fallback
        (bridgeLabel first second false) (some (bridgeLabel first second true))
  | .inr (.inl true) =>
      Reduction.MachineTransfer.loopAt (Γ := Symbols first second)
        (.inr (.inr ())) (.inr (.inl second.k₀)) id fallback
        (bridgeLabel first second true) (some (.inr (.inr second.main)))

def machine (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) : FinTM2 where
  K := Tape first second
  kFin := by
    letI := first.kFin
    letI := second.kFin
    exact inferInstanceAs (Fintype (first.K ⊕ (second.K ⊕ Unit)))
  k₀ := .inl first.k₀
  k₁ := .inr (.inl second.k₁)
  Γ := Symbols first second
  Λ := Label first second
  ΛFin := by
    letI := first.ΛFin
    letI := second.ΛFin
    exact inferInstanceAs (Fintype (first.Λ ⊕ (Bool ⊕ second.Λ)))
  main := .inl first.main
  σ := State first second
  σFin := by
    letI := first.σFin
    letI := second.σFin
    letI := second.Γk₀Fin
    exact inferInstanceAs (Fintype ((first.σ × second.σ) × Option (second.Γ second.k₀)))
  initialState := ((first.initialState, second.initialState), none)
  Γk₀Fin := first.Γk₀Fin
  m := program first second relabel fallback

def firstConfiguration (first second : FinTM2) (c : first.Cfg) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  MachineControl.configuration id (firstStates first second)
    (MachineEmbedding.configuration (some (bridgeLabel first second false))
      (second.initialState, (none : Register second)) (fun _ => []) c)

def secondConfiguration (first second : FinTM2) (c : second.Cfg) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  MachineControl.configuration (secondLabels first second) (secondStates first second)
    (MachineStackSwap.configuration
      (MachineEmbedding.configuration
        (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
        (Λextra := Bool ⊕ first.Λ) none
        (first.initialState, (none : Register second)) (fun _ => []) c))

theorem firstStep (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (a b : first.Cfg)
    (transition : first.step a = some b) :
    (machine first second relabel fallback).step (firstConfiguration first second a) =
      some (firstConfiguration first second b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => cases transition
    | some label =>
      have hb := Option.some.inj transition
      subst b
      change some (TM2.stepAux
        (MachineControl.statement id (firstStates first second)
          (MachineEmbedding.statement (some (bridgeLabel first second false)) (first.m label)))
        ((firstStates first second) (state, (second.initialState, none)))
        (MachineEmbedding.tapes tapes (fun _ => []))) = _
      have controlled := MachineControl.stepAux_simulation id (firstStates first second)
        (MachineEmbedding.statement
          (Δ := MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
          (some (bridgeLabel first second false)) (first.m label))
        (state, (second.initialState, none)) (MachineEmbedding.tapes tapes (fun _ => []))
      have embedded := MachineEmbedding.stepAux_simulation
        (Δ := MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
        (some (bridgeLabel first second false)) (second.initialState, (none : Register second))
        (fun _ => []) (first.m label) state tapes
      exact congrArg some (controlled.trans
        (congrArg (MachineControl.configuration id (firstStates first second)) embedded))

theorem secondStep (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (a b : second.Cfg)
    (transition : second.step a = some b) :
    (machine first second relabel fallback).step (secondConfiguration first second a) =
      some (secondConfiguration first second b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => cases transition
    | some label =>
      have hb := Option.some.inj transition
      subst b
      change some (TM2.stepAux
        (MachineControl.statement (secondLabels first second) (secondStates first second)
          (MachineStackSwap.statement
            (MachineEmbedding.statement
              (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
              (Λextra := Bool ⊕ first.Λ) none (second.m label))))
        ((secondStates first second) (state, (first.initialState, none)))
        (MachineStackSwap.tapes (MachineEmbedding.tapes tapes (fun _ => [])))) = _
      rw [MachineControl.stepAux_simulation, MachineStackSwap.stepAux_simulation,
        MachineEmbedding.stepAux_simulation]
      rfl

theorem firstConfiguration_init (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (input : List (first.Γ first.k₀)) :
    firstConfiguration first second (initList first input) =
      initList (machine first second relabel fallback) input := by
  unfold firstConfiguration MachineControl.configuration MachineEmbedding.configuration initList
  congr 1
  funext k
  rcases k with k | k | k
  · by_cases h : k = first.k₀
    · subst k
      simp [machine, MachineEmbedding.tapes]
      rfl
    · simp [machine, MachineEmbedding.tapes, h]
  · simp [machine, MachineEmbedding.tapes]
  · simp [machine, MachineEmbedding.tapes]

theorem secondConfiguration_halt (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (output : List (second.Γ second.k₁)) :
    secondConfiguration first second (haltList second output) =
      haltList (machine first second relabel fallback) output := by
  unfold secondConfiguration MachineControl.configuration MachineStackSwap.configuration
    MachineEmbedding.configuration haltList
  congr 1
  funext k
  rcases k with k | k | k
  · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]
  · by_cases h : k = second.k₁
    · subst k
      simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]
      rfl
    · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes, h]
  · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]

def temporaryTapes (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    ∀ k, List (Symbols first second k)
  | .inl _ => []
  | .inr (.inl _) => []
  | .inr (.inr _) => word

def temporaryConfiguration (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  ⟨some (bridgeLabel first second true),
    ((first.initialState, second.initialState), none), temporaryTapes first second word⟩

end MinUncutGames.Foundations.Complexity.MachineSequential

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineTransducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineTransducerCopy

open _root_.Turing
open Reduction.MachineSubstitution (pushWord )

variable {K Λ σ Q : Type} [DecidableEq K]

abbrev Alphabet (K : Type) (_ : K) := Bool
abbrev State (σ Q : Type) := (σ × Q) × Option Bool

def scanLoop (source scratch : K) (initial : Q)
    (emitterLabel : Q → Bool → Λ) (restoreLabel : Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ Q) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push scratch (fun state => state.2.getD false)
        (.goto fun state => emitterLabel state.1.2 (state.2.getD false)))
      (.load (fun state => ((state.1.1, initial), none)) (.goto fun _ => restoreLabel)))

def emitter (destination : K) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (scanLabel : Λ) (control : Q) (symbol : Bool) :
    TM2.Stmt (Alphabet K) Λ (State σ Q) :=
  .load (fun state => ((state.1.1, transition control symbol), state.2))
    (pushWord destination (emit control symbol) (.goto fun _ => scanLabel))

end MinUncutGames.Foundations.Complexity.MachineTransducerCopy

end
section
namespace MinUncutGames.Foundations.Complexity.MachineUnaryMultiply

open _root_.Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

abbrev State (σ : Type) := (σ × Unit) × Option Bool

end MinUncutGames.Foundations.Complexity.MachineUnaryMultiply

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineUnaryAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineRadixStep

open _root_.Turing

variable {K Λ σ : Type}

abbrev State (σ : Type) := MachineUnaryMultiply.State σ

end MinUncutGames.Foundations.Complexity.MachineRadixStep

namespace MinUncutGames.Foundations.Complexity.MachineHorner

open _root_.Turing

variable {K Λ σ : Type} {width : Nat}

abbrev State (σ : Type) := MachineRadixStep.State σ

open scoped BigOperators

end MinUncutGames.Foundations.Complexity.MachineHorner

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RuntimeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceRuntimeModel

open _root_.Turing Complexity

inductive BodyWork (Extra : Type)
  | leftBlock | dummy | bitCount | occurrenceCount
  | zero | rank | rightBase | leftBase
  | accA | accB | counter | arithScratch | coefficient
  | queryTemporary | queryScratch | accumulator
  | extra (value : Extra)
  deriving DecidableEq, Fintype

abbrev ArithmeticState := MachineHorner.State Unit

end MinUncutGames.Foundations.Hastad.SourceRuntimeModel

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineTupleOdometer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineTupleOdometer

open _root_.Turing
open Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

section Order

omit [DecidableEq K]

open scoped BigOperators

def tupleOrder (n q : ℕ) : List (Fin q → Fin n) :=
  List.ofFn (finFunctionFinEquiv (m := n) (n := q)).symm

end Order

section Nested

open scoped BigOperators

abbrev Configuration (K Λ σ : Type) :=
  TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool)

end Nested

end MinUncutGames.Foundations.Complexity.MachineTupleOdometer

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_LoopOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceTupleTape

open _root_.Turing Complexity SourceRuntimeModel

structure Snapshot where
  rank : List Bool := []
  rightBase : List Bool := []
  leftBase : List Bool := []
  zero : List Bool := []
  emitted : List Bool := []
  deriving DecidableEq, Inhabited

end MinUncutGames.Foundations.Hastad.SourceTupleTape

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Gap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceOdometerSchedule

open _root_.Turing Complexity MachineTupleOdometer
open Reduction.MachineTransfer

variable {u m : ℕ} {Extra Λ σ : Type} [DecidableEq Extra]

def allBits {q : ℕ} (bits : (Fin q → Fin m) → List Bool) : List Bool :=
  (tupleOrder m q).flatMap bits

end MinUncutGames.Foundations.Hastad.SourceOdometerSchedule

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP

structure ConstraintGraph (V E A : Type*) where
  reverse : E ≃ E
  reverse_involutive : Function.Involutive reverse
  tail : E → V
  accepts : E → A → A → Bool
  reverse_accepts : ∀ e a b, accepts (reverse e) b a = accepts e a b

namespace ConstraintGraph

variable {V E A : Type*}

def head (G : ConstraintGraph V E A) (e : E) : V := G.tail (G.reverse e)

@[simp] theorem head_reverse (G : ConstraintGraph V E A) (e : E) :
    G.head (G.reverse e) = G.tail e := by
  simp only [head, G.reverse_involutive e]

def edgeSatisfied (G : ConstraintGraph V E A) (labeling : V → A) (e : E) : Bool :=
  G.accepts e (labeling (G.tail e)) (labeling (G.head e))

@[simp] theorem edgeSatisfied_reverse (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    G.edgeSatisfied labeling (G.reverse e) = G.edgeSatisfied labeling e := by
  simpa only [edgeSatisfied, head, G.reverse_involutive e] using
    G.reverse_accepts e (labeling (G.tail e)) (labeling (G.tail (G.reverse e)))

def rejectedDarts [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) :
    Finset E := Finset.univ.filter (fun e => G.edgeSatisfied labeling e = false)

def rejectionCount [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) : Nat :=
  (G.rejectedDarts labeling).card

end ConstraintGraph

end MinUncutGames.Foundations.PCP

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_GraphTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.GraphTables

open MinUncutGames.Foundations.Complexity

abbrev Label := Fin 64
abbrev RelationTable := Vector Bool 4096

def relationIndex : Label × Label ≃ Fin 4096 := finProdFinEquiv

def relationAt (table : RelationTable) (a b : Label) : Bool :=
  table[relationIndex (a, b)]

def relationOf (predicate : Label → Label → Bool) : RelationTable :=
  Vector.ofFn (fun i => predicate (relationIndex.symm i).1 (relationIndex.symm i).2)

@[simp] theorem relationAt_relationOf (predicate : Label → Label → Bool) (a b : Label) :
    relationAt (relationOf predicate) a b = predicate a b := by
  simp [relationAt, relationOf]

structure DartRow (vertices darts : Nat) where
  tail : Fin vertices
  reverseIndex : Fin darts
  relation : RelationTable

abbrev Rows (vertices darts : Nat) := Vector (DartRow vertices darts) darts

def reverseAt {n m : Nat} (rows : Rows n m) (e : Fin m) : Fin m :=
  rows[e].reverseIndex

def acceptsAt {n m : Nat} (rows : Rows n m) (e : Fin m) (a b : Label) : Bool :=
  relationAt rows[e].relation a b

def Valid {n m : Nat} (rows : Rows n m) : Prop :=
  (∀ e, reverseAt rows (reverseAt rows e) = e) ∧
  (∀ e a b, acceptsAt rows (reverseAt rows e) b a = acceptsAt rows e a b)

instance instDecidableValid {n m : Nat} (rows : Rows n m) : Decidable (Valid rows) := by
  unfold Valid
  infer_instance

structure Table where
  vertices : Nat
  darts : Nat
  rows : Rows vertices darts
  valid : Valid rows

def rowList (table : Table) : List (DartRow table.vertices table.darts) := table.rows.toList

@[simp] theorem rowList_length (table : Table) : (rowList table).length = table.darts := by
  simp [rowList]

def semantics (table : Table) : ConstraintGraph (Fin table.vertices) (Fin table.darts) Label where
  reverse :=
    { toFun := reverseAt table.rows
      invFun := reverseAt table.rows
      left_inv := table.valid.1
      right_inv := table.valid.1 }
  reverse_involutive := table.valid.1
  tail e := table.rows[e].tail
  accepts := acceptsAt table.rows
  reverse_accepts := table.valid.2

@[simp] theorem semantics_reverse (table : Table) (e : Fin table.darts) :
    (semantics table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem semantics_tail (table : Table) (e : Fin table.darts) :
    (semantics table).tail e = table.rows[e].tail := rfl

@[simp] theorem semantics_accepts (table : Table) (e : Fin table.darts) (a b : Label) :
    (semantics table).accepts e a b = relationAt table.rows[e].relation a b := rfl

def graphRows {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) : Rows n m :=
  Vector.ofFn (fun e => ⟨G.tail e, G.reverse e, relationOf (G.accepts e)⟩)

@[simp] theorem reverseAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    reverseAt (graphRows G) e = G.reverse e := by
  simp [reverseAt, graphRows]

@[simp] theorem acceptsAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) (a b : Label) :
    acceptsAt (graphRows G) e a b = G.accepts e a b := by
  simp [acceptsAt, graphRows]

theorem graphRows_valid {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) :
    Valid (graphRows G) := by
  constructor
  · intro e
    simpa using G.reverse_involutive e
  · intro e a b
    simpa using G.reverse_accepts e a b

def ofGraph {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) : Table :=
  ⟨n, m, graphRows G, graphRows_valid G⟩

@[simp] theorem semantics_ofGraph_reverse {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    (semantics (ofGraph G)).reverse e = G.reverse e := by
  exact reverseAt_graphRows G e

@[simp] theorem semantics_ofGraph_tail {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    (semantics (ofGraph G)).tail e = G.tail e := by
  change (graphRows G)[e.val].tail = G.tail e
  simp only [graphRows, Vector.getElem_ofFn]

@[simp] theorem semantics_ofGraph_accepts {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) (a b : Label) :
    (semantics (ofGraph G)).accepts e a b = G.accepts e a b := by
  exact acceptsAt_graphRows G e a b

@[simp] theorem semantics_ofGraph_edgeSatisfied {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (labeling : Fin n → Label) (e : Fin m) :
    (semantics (ofGraph G)).edgeSatisfied labeling e = G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head]

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hr : ∀ e, G.reverse e = H.reverse e) (ht : G.tail = H.tail)
    (hp : G.accepts = H.accepts) : G = H := by
  cases G with
  | mk reverse hinv tail accepts htranspose =>
    cases H with
    | mk reverse' hinv' tail' accepts' htranspose' =>
      dsimp only at hr ht hp
      have he : reverse = reverse' := Equiv.ext hr
      cases he
      cases ht
      cases hp
      rfl

@[simp] theorem semantics_ofGraph {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) : semantics (ofGraph G) = G := by
  apply constraintGraph_ext
  · exact semantics_ofGraph_reverse G
  · funext e
    exact semantics_ofGraph_tail G e
  · funext e a b
    exact semantics_ofGraph_accepts G e a b

@[simp] theorem semantics_ofGraph_rejectionCount {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (labeling : Fin n → Label) :
    (semantics (ofGraph G)).rejectionCount labeling = G.rejectionCount labeling := by
  rw [semantics_ofGraph]
  rfl

def enumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ Label) :
    ConstraintGraph (Fin n) (Fin m) Label where
  reverse := (dartOrder.symm.trans G.reverse).trans dartOrder
  reverse_involutive e := by
    change dartOrder (G.reverse (dartOrder.symm
      (dartOrder (G.reverse (dartOrder.symm e))))) = e
    rw [dartOrder.symm_apply_apply, G.reverse_involutive, dartOrder.apply_symm_apply]
  tail e := vertexOrder (G.tail (dartOrder.symm e))
  accepts e a b := G.accepts (dartOrder.symm e) (labelOrder.symm a) (labelOrder.symm b)
  reverse_accepts e a b := by
    change G.accepts (dartOrder.symm (dartOrder (G.reverse (dartOrder.symm e))))
      (labelOrder.symm b) (labelOrder.symm a) = _
    rw [dartOrder.symm_apply_apply]
    exact G.reverse_accepts _ _ _

def ofEnumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ Label) : Table :=
  ofGraph (enumeratedGraph G vertexOrder dartOrder labelOrder)

def bitWord (b : Bool) : Nat := if b then 1 else 0

def parseBit : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

@[simp] theorem parseBit_bitWord (b : Bool) : parseBit (bitWord b) = some b := by
  cases b <;> rfl

@[simp] theorem parseBits_bitWords (bits : List Bool) :
    (bits.map bitWord).mapM parseBit = some bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [ih]

def relationWords (relation : RelationTable) : List Nat := relation.toList.map bitWord

@[simp] theorem relationWords_length (relation : RelationTable) :
    (relationWords relation).length = 4096 := by simp [relationWords]

def parseRelation (words : List Nat) : Option RelationTable := do
  let bits ← words.mapM parseBit
  if length_ok : bits.length = 4096 then
    some ⟨bits.toArray, by simpa using length_ok⟩
  else none

@[simp] theorem parseRelation_encoded (relation : RelationTable) :
    parseRelation (relationWords relation) = some relation := by
  unfold parseRelation relationWords
  rw [parseBits_bitWords]
  simp
  exact Vector.toArray_toList

def rowWords {n m : Nat} (row : DartRow n m) : List Nat :=
  [row.tail.val, row.reverseIndex.val] ++ relationWords row.relation

def parseRow (vertices darts : Nat) : List Nat → Option (DartRow vertices darts × List Nat)
  | tail :: reverseIndex :: words => do
      let tail ← parseLabel vertices tail
      let reverseIndex ← parseLabel darts reverseIndex
      let relation ← parseRelation (words.take 4096)
      return (⟨tail, reverseIndex, relation⟩, words.drop 4096)
  | _ => none

@[simp] theorem parseRow_encoded {n m : Nat} (row : DartRow n m) (rest : List Nat) :
    parseRow n m (rowWords row ++ rest) = some (row, rest) := by
  cases row with
  | mk tail reverseIndex relation =>
      have taken := List.take_left' (l₂ := rest) (relationWords_length relation)
      have dropped := List.drop_left' (l₂ := rest) (relationWords_length relation)
      simp [rowWords, parseRow, taken, dropped]

def parseRows (vertices darts : Nat) :
    Nat → List Nat → Option (List (DartRow vertices darts) × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (row, words) ← parseRow vertices darts words
      let (rows, words) ← parseRows vertices darts count words
      return (row :: rows, words)

@[simp] theorem parseRows_encoded {n m : Nat} (rows : List (DartRow n m)) (rest : List Nat) :
    parseRows n m rows.length (rows.flatMap rowWords ++ rest) = some (rows, rest) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [parseRows, List.append_assoc, ih]

def tableWords (table : Table) : List Nat :=
  [table.vertices, table.darts] ++ (rowList table).flatMap rowWords

def decodeTableWords : List Nat → Option Table
  | vertices :: darts :: words => do
      let (parsed, trailing) ← parseRows vertices darts darts words
      if trailing = [] then
        if length_ok : parsed.length = darts then
          let rows : Rows vertices darts := ⟨parsed.toArray, by simpa using length_ok⟩
          if valid : Valid rows then some ⟨vertices, darts, rows, valid⟩ else none
        else none
      else none
  | _ => none

@[simp] theorem decodeTableWords_encoded (table : Table) :
    decodeTableWords (tableWords table) = some table := by
  cases table with
  | mk vertices darts rows valid =>
      have parsed := parseRows_encoded rows.toList []
      simp only [Vector.length_toList, List.append_nil] at parsed
      simp [tableWords, rowList, decodeTableWords, parsed, valid, Vector.toArray_toList]

@[simp] theorem rowWords_length {n m : Nat} (row : DartRow n m) :
    (rowWords row).length = 4098 := by simp [rowWords]

theorem rowsWords_length {n m : Nat} (rows : List (DartRow n m)) :
    (rows.flatMap rowWords).length = 4098 * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [ih, Nat.mul_add, Nat.add_comm]

end MinUncutGames.Foundations.PCP.GraphTables

end
section
namespace MinUncutGames.Foundations.PCP.PoweringWalks

structure PortGraph (V D : Type*) where
  rot : (V × D) ≃ (V × D)
  rot_involutive : Function.Involutive rot

abbrev Edge (V D : Type*) := V × D
abbrev Walk (V D : Type*) (t : Nat) := V × (Fin t → D)

variable {V D : Type*}

def next (G : PortGraph V D) (v : V) (d : D) : V := (G.rot (v, d)).1

@[simp] theorem rot_rot (G : PortGraph V D) (e : Edge V D) :
    G.rot (G.rot e) = e := G.rot_involutive e

def walkEnd (G : PortGraph V D) : V → List D → V
  | v, [] => v
  | v, d :: ds => walkEnd G (next G v d) ds

@[simp] theorem walkEnd_nil (G : PortGraph V D) (v : V) : walkEnd G v [] = v := rfl

@[simp] theorem walkEnd_cons (G : PortGraph V D) (v : V) (d : D) (ds : List D) :
    walkEnd G v (d :: ds) = walkEnd G (next G v d) ds := rfl

theorem walkEnd_append (G : PortGraph V D) (v : V) (as bs : List D) :
    walkEnd G v (as ++ bs) = walkEnd G (walkEnd G v as) bs := by
  induction as generalizing v with
  | nil => rfl
  | cons d ds ih => exact ih (next G v d)

def splitHead (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ ((V × D) × (Fin n → D)) where
  toFun w := ((w.1, w.2 0), fun j => w.2 j.succ)
  invFun z := (z.1.1, Fin.cases z.1.2 z.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def rotateHead (G : PortGraph V D) (n : Nat) : Walk V D (n + 1) ≃ Walk V D (n + 1) :=
  (splitHead V D n).trans
    ((Equiv.prodCongr G.rot (Equiv.refl (Fin n → D))).trans (splitHead V D n).symm)

@[simp] theorem rotateHead_vertex (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).1 = next G w.1 (w.2 0) := rfl

@[simp] theorem rotateHead_zero (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).2 0 = (G.rot (w.1, w.2 0)).2 := rfl

@[simp] theorem rotateHead_succ (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (j : Fin n) :
    (rotateHead G n w).2 j.succ = w.2 j.succ := rfl

def wordEnd (G : PortGraph V D) : (n : Nat) → V → (Fin n → D) → V
  | 0, v, _ => v
  | n + 1, v, p => wordEnd G n (next G v (p 0)) (fun j => p j.succ)

def endpoint (G : PortGraph V D) {n : Nat} (w : Walk V D n) : V :=
  wordEnd G n w.1 w.2

def advanceTail {n : Nat} (G : PortGraph V D) (w : Walk V D (n + 1)) : Walk V D n :=
  ((G.rot (w.1, w.2 0)).1, fun j => w.2 j.succ)

def edgeAt (G : PortGraph V D) :
    (n : Nat) → Walk V D (n + 1) → Fin (n + 1) → Edge V D
  | 0, w, _ => (w.1, w.2 0)
  | n + 1, w, k => Fin.cases (w.1, w.2 0)
      (fun j => edgeAt G n (advanceTail G w) j) k

end MinUncutGames.Foundations.PCP.PoweringWalks

end
section
namespace MinUncutGames.Foundations.PCP.PortTables

open PoweringWalks

abbrev Label := GraphTables.Label

def rowIndex (vertices ports : Nat) :
    Fin vertices × Fin ports ≃ Fin (vertices * ports) := finProdFinEquiv

@[simp] theorem rowIndex_val (n d : Nat) (e : Fin n × Fin d) :
    (rowIndex n d e).val = e.2.val + d * e.1.val := rfl

structure Table (vertices ports : Nat) where
  reverseIndex : Vector (Fin (vertices * ports)) (vertices * ports)
  relations : Vector GraphTables.RelationTable (vertices * ports)
  involutive : Function.Involutive
    (fun i : Fin (vertices * ports) => reverseIndex[i])
  transpose : ∀ (i : Fin (vertices * ports)) (a b : Label),
    GraphTables.relationAt relations[reverseIndex[i]] b a =
      GraphTables.relationAt relations[i] a b

variable {n d : Nat}

def rotation (table : Table n d) (e : Fin n × Fin d) : Fin n × Fin d :=
  (rowIndex n d).symm table.reverseIndex[rowIndex n d e]

def accepts (table : Table n d) (e : Fin n × Fin d) (a b : Label) : Bool :=
  GraphTables.relationAt table.relations[rowIndex n d e] a b

@[simp] theorem rowIndex_rotation (table : Table n d) (e : Fin n × Fin d) :
    rowIndex n d (rotation table e) = table.reverseIndex[rowIndex n d e] := by
  exact (rowIndex n d).apply_symm_apply _

theorem rotation_involutive (table : Table n d) : Function.Involutive (rotation table) := by
  intro e
  simp only [rotation, Equiv.apply_symm_apply]
  exact (congrArg (rowIndex n d).symm (table.involutive (rowIndex n d e))).trans
    ((rowIndex n d).symm_apply_apply e)

theorem accepts_rotation (table : Table n d) (e : Fin n × Fin d) (a b : Label) :
    accepts table (rotation table e) b a = accepts table e a b := by
  simpa only [accepts, rowIndex_rotation] using table.transpose (rowIndex n d e) a b

def portGraph (table : Table n d) : PortGraph (Fin n) (Fin d) where
  rot :=
    { toFun := rotation table
      invFun := rotation table
      left_inv := rotation_involutive table
      right_inv := rotation_involutive table }
  rot_involutive := rotation_involutive table

@[simp] theorem portGraph_rot (table : Table n d) (e : Fin n × Fin d) :
    (portGraph table).rot e = rotation table e := rfl

def baseGraph (table : Table n d) : ConstraintGraph (Fin n) (Fin n × Fin d) Label where
  reverse := (portGraph table).rot
  reverse_involutive := rotation_involutive table
  tail := Prod.fst
  accepts := accepts table
  reverse_accepts := accepts_rotation table

@[simp] theorem baseGraph_reverse (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).reverse e = rotation table e := rfl

@[simp] theorem baseGraph_tail (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).tail e = e.1 := rfl

@[simp] theorem baseGraph_head (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).head e = (rotation table e).1 := rfl

@[simp] theorem baseGraph_accepts (table : Table n d) (e : Fin n × Fin d) (a b : Label) :
    (baseGraph table).accepts e a b = accepts table e a b := rfl

def ofPortGraph (G : PortGraph (Fin n) (Fin d))
    (predicate : (Fin n × Fin d) → Label → Label → Bool)
    (htranspose : ∀ e a b, predicate (G.rot e) b a = predicate e a b) : Table n d where
  reverseIndex := Vector.ofFn (fun i => rowIndex n d (G.rot ((rowIndex n d).symm i)))
  relations := Vector.ofFn (fun i => GraphTables.relationOf (predicate ((rowIndex n d).symm i)))
  involutive := by
    intro i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
      Equiv.symm_apply_apply]
    exact (congrArg (rowIndex n d) (G.rot_involutive ((rowIndex n d).symm i))).trans
      ((rowIndex n d).apply_symm_apply i)
  transpose := by
    intro i a b
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
      Equiv.symm_apply_apply, GraphTables.relationAt_relationOf]
    exact htranspose ((rowIndex n d).symm i) a b

@[simp] theorem rotation_ofPortGraph (G : PortGraph (Fin n) (Fin d))
    (predicate : (Fin n × Fin d) → Label → Label → Bool)
    (htranspose : ∀ e a b, predicate (G.rot e) b a = predicate e a b)
    (e : Fin n × Fin d) : rotation (ofPortGraph G predicate htranspose) e = G.rot e := by
  simp only [rotation, ofPortGraph, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    Equiv.symm_apply_apply]

@[simp] theorem accepts_ofPortGraph (G : PortGraph (Fin n) (Fin d))
    (predicate : (Fin n × Fin d) → Label → Label → Bool)
    (htranspose : ∀ e a b, predicate (G.rot e) b a = predicate e a b)
    (e : Fin n × Fin d) (a b : Label) :
    accepts (ofPortGraph G predicate htranspose) e a b = predicate e a b := by
  simp only [accepts, ofPortGraph, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    Equiv.symm_apply_apply, GraphTables.relationAt_relationOf]

def flatRows (table : Table n d) : GraphTables.Rows n (n * d) :=
  Vector.ofFn (fun i =>
    ⟨((rowIndex n d).symm i).1, table.reverseIndex[i], table.relations[i]⟩)

@[simp] theorem reverseAt_flatRows (table : Table n d) (i : Fin (n * d)) :
    GraphTables.reverseAt (flatRows table) i = table.reverseIndex[i] := by
  simp [GraphTables.reverseAt, flatRows]

@[simp] theorem acceptsAt_flatRows (table : Table n d) (i : Fin (n * d)) (a b : Label) :
    GraphTables.acceptsAt (flatRows table) i a b = GraphTables.relationAt table.relations[i] a b := by
  simp [GraphTables.acceptsAt, flatRows]

theorem flatRows_valid (table : Table n d) : GraphTables.Valid (flatRows table) := by
  constructor
  · intro i
    simpa only [reverseAt_flatRows] using table.involutive i
  · intro i a b
    simpa only [reverseAt_flatRows, acceptsAt_flatRows] using table.transpose i a b

end MinUncutGames.Foundations.PCP.PortTables

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_DegreeReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators

namespace MinUncutGames.Foundations.PCP.DegreeReplacement

open PoweringWalks

variable {V E A D : Type*}

abbrev Cloud (G : ConstraintGraph V E A) (v : V) := {e : E // G.tail e = v}

def cloudIndexEquiv (G : ConstraintGraph V E A) :
    (E × D) ≃ (Σ v : V, Cloud G v × D) where
  toFun p := ⟨G.tail p.1, (⟨p.1, rfl⟩, p.2)⟩
  invFun p := (p.2.1.val, p.2.2)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨⟨e, he⟩, d⟩⟩
    cases he
    rfl

def cloudRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    (Σ v : V, Cloud G v × D) ≃ (Σ v : V, Cloud G v × D) :=
  Equiv.sigmaCongrRight (fun v => (H v).rot)

theorem cloudRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (cloudRotation G H) := by
  rintro ⟨v, p⟩
  change (⟨v, (H v).rot ((H v).rot p)⟩ : Σ v : V, Cloud G v × D) = ⟨v, p⟩
  rw [(H v).rot_involutive p]

def innerRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : (E × D) ≃ (E × D) :=
  ((cloudIndexEquiv G).trans (cloudRotation G H)).trans (cloudIndexEquiv G).symm

theorem innerRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (innerRotation G H) := by
  intro p
  apply (cloudIndexEquiv G).injective
  simp only [innerRotation, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact cloudRotation_involutive G H _

theorem innerRotation_tail (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (e : E) (d : D) :
    G.tail (innerRotation G H (e, d)).1 = G.tail e := by
  change G.tail (((H (G.tail e)).rot (⟨e, rfl⟩, d)).1.val) = G.tail e
  exact ((H (G.tail e)).rot (⟨e, rfl⟩, d)).1.property

def replacementStep (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : E × (D ⊕ Unit) → E × (D ⊕ Unit)
  | (e, Sum.inl d) =>
      let p := innerRotation G H (e, d)
      (p.1, Sum.inl p.2)
  | (e, Sum.inr u) => (G.reverse e, Sum.inr u)

theorem replacementStep_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (replacementStep G H) := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · change ((innerRotation G H (innerRotation G H (e, d))).1,
        (Sum.inl ((innerRotation G H (innerRotation G H (e, d))).2) : D ⊕ Unit)) =
      (e, Sum.inl d)
    rw [innerRotation_involutive G H (e, d)]
  · change (G.reverse (G.reverse e), (Sum.inr u : D ⊕ Unit)) = (e, Sum.inr u)
    rw [G.reverse_involutive e]

def replacementPortGraph (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : PortGraph E (D ⊕ Unit) where
  rot :=
    { toFun := replacementStep G H
      invFun := replacementStep G H
      left_inv := replacementStep_involutive G H
      right_inv := replacementStep_involutive G H }
  rot_involutive := replacementStep_involutive G H

def replacementGraph [DecidableEq A] (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    ConstraintGraph E (E × (D ⊕ Unit)) A where
  reverse := (replacementPortGraph G H).rot
  reverse_involutive := (replacementPortGraph G H).rot_involutive
  tail := Prod.fst
  accepts p a b := match p.2 with
    | Sum.inl _ => decide (a = b)
    | Sum.inr _ => G.accepts p.1 a b
  reverse_accepts := by
    rintro ⟨e, p⟩ a b
    rcases p with d | u
    · change decide (b = a) = decide (a = b)
      simp [eq_comm]
    · exact G.reverse_accepts e a b

def liftLabel (G : ConstraintGraph V E A) (labeling : V → A) : E → A :=
  fun e => labeling (G.tail e)

@[simp] theorem replacement_satisfied_inl [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (d : D) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inl d) =
      true := by
  change decide (labeling (G.tail e) =
    labeling (G.tail (innerRotation G H (e, d)).1)) = true
  rw [innerRotation_tail G H e d]
  simp

@[simp] theorem replacement_satisfied_inr [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inr u) =
      G.edgeSatisfied labeling e := rfl

abbrev PaddedDart (_G : ConstraintGraph V E A) (dummy : V → Type*) :=
  E ⊕ (Σ v : V, dummy v)

def paddedOwner (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy → V
  | Sum.inl e => G.tail e
  | Sum.inr z => z.1

def paddedReverse (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy ≃ PaddedDart G dummy :=
  Equiv.sumCongr G.reverse (Equiv.refl (Σ v : V, dummy v))

theorem paddedReverse_involutive (G : ConstraintGraph V E A) (dummy : V → Type*) :
    Function.Involutive (paddedReverse G dummy) := by
  intro z
  cases z with
  | inl e =>
    change (Sum.inl (G.reverse (G.reverse e)) : PaddedDart G dummy) = Sum.inl e
    rw [G.reverse_involutive e]
  | inr z => rfl

def paddedGraph (G : ConstraintGraph V E A) (dummy : V → Type*) :
    ConstraintGraph V (PaddedDart G dummy) A where
  reverse := paddedReverse G dummy
  reverse_involutive := paddedReverse_involutive G dummy
  tail := paddedOwner G dummy
  accepts e a b := match e with
    | Sum.inl e => G.accepts e a b
    | Sum.inr _ => true
  reverse_accepts := by
    intro e a b
    cases e with
    | inl e => exact G.reverse_accepts e a b
    | inr z => rfl

@[simp] theorem padded_satisfied_inl (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (e : E) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inl e) =
      G.edgeSatisfied labeling e := rfl

@[simp] theorem padded_satisfied_inr (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (z : Σ v : V, dummy v) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inr z) = true := rfl

def paddedReplacementPortGraph (G : ConstraintGraph V E A) (dummy : V → Type*)
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) :
    PortGraph (PaddedDart G dummy) (D ⊕ Unit) :=
  replacementPortGraph (paddedGraph G dummy) H

def paddedReplacementGraph [DecidableEq A]
    (G : ConstraintGraph V E A) (dummy : V → Type*)
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) :
    ConstraintGraph (PaddedDart G dummy) (PaddedDart G dummy × (D ⊕ Unit)) A :=
  replacementGraph (paddedGraph G dummy) H

end MinUncutGames.Foundations.PCP.DegreeReplacement

end
section
noncomputable section

namespace MinUncutGames.Foundations.PCP.AssignmentTester

open MinUncutGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

variable {K : Type*} [Fintype K] [Nonempty K]

def eventAccepts (kind : Fin 4) (b : Fin 6 → Bool) : Bool :=
  if kind = 0 then decide ((b 0 ^^ b 1) = b 2)
  else if kind = 1 then decide ((b 0 ^^ b 1) = ((b 2 ^^ b 3) && (b 4 ^^ b 5)))
  else if kind = 2 then (b 0 ^^ b 1)
  else decide (b 0 = (b 1 ^^ b 2))

end MinUncutGames.Foundations.PCP.AssignmentTester

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_CayleySampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

def averagingOperator {V D : Type*} [Fintype D] (G : PortGraph V D)
    (f : V → ℝ) (v : V) : ℝ := Finset.univ.expect (fun d => f (G.rot (v, d)).1)

end

end MinUncutGames.Foundations.PCP.SpectralReturn

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_CayleySpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


namespace MinUncutGames.Foundations.PCP.Expanders

open scoped BigOperators
open MinUncutGames.Foundations.Hastad
def initialDegree : Nat := 2 ^ 16
def initialQuarterDegree : Nat := 2 ^ 14
def basePower : Nat := 7

abbrev BasePort := Fin basePower → Fin (4 * initialQuarterDegree)
def baseDegree : Nat := initialDegree ^ basePower

end MinUncutGames.Foundations.PCP.Expanders

end

namespace MinUncutGames.Foundations.PCP.ZigzagGraphs

open PoweringWalks

variable {V D E : Type*}

def involutionEquiv {A : Type*} (f : A → A) (hf : Function.Involutive f) : A ≃ A where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf

theorem palindrome_involutive {A : Type*} (B P : A ≃ A)
    (hB : Function.Involutive B) (hP : Function.Involutive P) :
    Function.Involutive (B.trans (P.trans B)) := by
  intro x
  change B (P (B (B (P (B x))))) = x
  rw [hB, hP, hB]

def squareSwap (s : V × (D × D)) : V × (D × D) := (s.1, (s.2.2, s.2.1))

theorem squareSwap_involutive : Function.Involutive (squareSwap (V := V) (D := D)) := by
  rintro ⟨v, d₁, d₂⟩
  rfl

end MinUncutGames.Foundations.PCP.ZigzagGraphs

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ExpanderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

abbrev Port := BasePort × BasePort
abbrev CloudPort := Port × Port
def growth : Nat := baseDegree ^ 4

theorem growth_gt_one : 1 < growth := by
  norm_num [growth, baseDegree, initialDegree, basePower]

def Vertex : Nat → Type
  | 0 => Unit
  | n + 1 => Vertex n × CloudPort

end MinUncutGames.Foundations.PCP.ExpanderFamily

namespace MinUncutGames.Foundations.PCP.CloudPadding

open scoped BigOperators
open DegreeReplacement

variable {V E A : Type*}

def paddedCloudEquiv (G : ConstraintGraph V E A) (dummy : V → Type*) (v : V) :
    Cloud (paddedGraph G dummy) v ≃ Cloud G v ⊕ dummy v where
  toFun := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · exact Sum.inl ⟨e, he⟩
    · change w = v at he
      cases he
      exact Sum.inr d
  invFun := fun z => match z with
    | Sum.inl e => ⟨Sum.inl e.val, e.property⟩
    | Sum.inr d => ⟨Sum.inr ⟨v, d⟩, rfl⟩
  left_inv := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · rfl
    · change w = v at he
      cases he
      rfl
  right_inv := by
    intro z
    cases z <;> rfl

end MinUncutGames.Foundations.PCP.CloudPadding

namespace MinUncutGames.Foundations.PCP.PreprocessingCloudIndex

open scoped BigOperators
open GraphTables DegreeReplacement

def listEquiv {α : Type*} [BEq α] [LawfulBEq α] (xs : List α)
    (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs) : α ≃ Fin xs.length where
  toFun a := ⟨xs.idxOf a, List.idxOf_lt_length_of_mem (complete a)⟩
  invFun i := xs.get i
  left_inv a := List.idxOf_get _
  right_inv i := by
    apply Fin.ext
    exact List.get_idxOf nodup i

@[simp] theorem listEquiv_val {α : Type*} [BEq α] [LawfulBEq α]
    (xs : List α) (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs) (a : α) :
    (listEquiv xs nodup complete a).val = xs.idxOf a := rfl

@[simp] theorem listEquiv_symm_apply {α : Type*} [BEq α] [LawfulBEq α]
    (xs : List α) (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs)
    (i : Fin xs.length) : (listEquiv xs nodup complete).symm i = xs.get i := rfl

end MinUncutGames.Foundations.PCP.PreprocessingCloudIndex

namespace MinUncutGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

def rowIndex (v d : Nat) : Fin v × Fin d ≃ Fin (v * d) := finProdFinEquiv

theorem rowIndex_val (v d : Nat) (x : Fin v × Fin d) :
    (rowIndex v d x).val = x.2.val + d * x.1.val := rfl

structure Table (v d : Nat) where
  rows : Vector (Fin (v * d)) (v * d)
  involutive : Function.Involutive (fun i : Fin (v * d) => rows[i])

def reverseIndex {v d : Nat} (table : Table v d) (i : Fin (v * d)) : Fin (v * d) :=
  table.rows[i]

def lookup {v d : Nat} (table : Table v d) (x : Fin v × Fin d) : Fin v × Fin d :=
  (rowIndex v d).symm (reverseIndex table (rowIndex v d x))

theorem lookup_involutive {v d : Nat} (table : Table v d) :
    Function.Involutive (lookup table) := by
  intro x
  simp only [lookup, Equiv.apply_symm_apply]
  exact (congrArg (rowIndex v d).symm (table.involutive (rowIndex v d x))).trans
    ((rowIndex v d).symm_apply_apply x)

def vertexIndex (v q : Nat) : Fin v × (Fin q × Fin q) ≃ Fin (v * (q * q)) :=
  (Equiv.prodCongr (Equiv.refl _) (rowIndex q q)).trans (rowIndex v (q * q))

def vertexCount (q : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => vertexCount q n * (q * q)

end MinUncutGames.Foundations.PCP.ExpanderTables

namespace MinUncutGames.Foundations.PCP.PreprocessingLevels

def levelLoop (g k : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, e, s => (e, s)
  | fuel + 1, e, s =>
      if k ≤ s then (e, s)
      else levelLoop g k fuel (e + 1) (s * g)

def searchResult (k : Nat) : Nat × Nat :=
  levelLoop ExpanderFamily.growth k k 0 1

def boundedLevel (k : Nat) : Nat := (searchResult k).1

def paddedSize (k : Nat) : Nat := (searchResult k).2

@[simp] theorem boundedLevel_zero : boundedLevel 0 = 0 := rfl

@[simp] theorem paddedSize_zero : paddedSize 0 = 1 := rfl

end MinUncutGames.Foundations.PCP.PreprocessingLevels

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCloudCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineCloudCount

open _root_.Turing

inductive Tape
  | original | work | target | scratch | count | spare
  deriving DecidableEq

def memory (original work target scratch count spare : List Bool) : Tape → List Bool
  | .original => original
  | .work => work
  | .target => target
  | .scratch => scratch
  | .count => count
  | .spare => spare

@[simp] theorem memory_original (a b c d e f : List Bool) :
    memory a b c d e f .original = a := rfl
@[simp] theorem memory_work (a b c d e f : List Bool) :
    memory a b c d e f .work = b := rfl
@[simp] theorem memory_target (a b c d e f : List Bool) :
    memory a b c d e f .target = c := rfl
@[simp] theorem memory_scratch (a b c d e f : List Bool) :
    memory a b c d e f .scratch = d := rfl
@[simp] theorem memory_count (a b c d e f : List Bool) :
    memory a b c d e f .count = e := rfl
@[simp] theorem memory_spare (a b c d e f : List Bool) :
    memory a b c d e f .spare = f := rfl

@[simp] theorem update_memory_work (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .work x = memory a x c d e f := by
  funext k
  cases k <;> rfl
@[simp] theorem update_memory_target (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .target x = memory a b x d e f := by
  funext k
  cases k <;> rfl
@[simp] theorem update_memory_scratch (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .scratch x = memory a b c x e f := by
  funext k
  cases k <;> rfl
@[simp] theorem update_memory_count (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .count x = memory a b c d x f := by
  funext k
  cases k <;> rfl

open MinUncutGames.Foundations.PCP

end MinUncutGames.Foundations.Complexity.MachineCloudCount

end
section
namespace MinUncutGames.Foundations.Complexity.MachineCeilingPower

open _root_.Turing
open MinUncutGames.Foundations.PCP

inductive Tape
  | input | work | power | saved | level | fuel | spare | product
  deriving DecidableEq

inductive Label
  | init | fuelFirst | fuelSecond | guard | copyFirst | copySecond
  | compare | restore | decide | scale | transfer | cleanup
  deriving DecidableEq

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def memory (input work power saved level fuel spare product : List Bool) : Tape → List Bool
  | .input => input
  | .work => work
  | .power => power
  | .saved => saved
  | .level => level
  | .fuel => fuel
  | .spare => spare
  | .product => product

@[simp] theorem update_work (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .work x = memory a x c d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_power (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .power x = memory a b x d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_saved (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .saved x = memory a b c x e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_level (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .level x = memory a b c d x f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_fuel (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .fuel x = memory a b c d e x g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_product (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .product x = memory a b c d e f g x := by
  funext k; cases k <;> rfl

variable {σ : Type}

def compareLoop : TM2.Stmt Alphabet Label (State σ) :=
  .pop .work (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.peek .power (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.pop .power (fun state _ => (state.1, none))
            (.push .saved (fun _ => true) (.goto fun _ => .compare)))
          (.load (fun state => ((state.1.1, true), none)) (.goto fun _ => .compare))))
      (.load (fun state => (state.1, none)) (.goto fun _ => .restore)))

def scaleLoop (g : Nat) : TM2.Stmt Alphabet Label (State σ) :=
  .pop .power (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (Reduction.MachineSubstitution.pushWord .product (List.replicate g true)
        (.goto fun _ => .scale))
      (.push .power (fun _ => false)
        (.push .level (fun _ => true)
          (.load (fun state => (state.1, none)) (.goto fun _ => .transfer)))))

def program (g : Nat) : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push .power (fun _ => false) (.push .power (fun _ => true)
      (.push .level (fun _ => false) (.goto fun _ => .fuelFirst)))
  | .fuelFirst => Reduction.MachineTransfer.loopAt
      .input .spare id false .fuelFirst (some .fuelSecond)
  | .fuelSecond => MachineCopy.forkLoop
      .spare .input .fuel false .fuelSecond (some .guard)
  | .guard => MachineUnaryCounter.guard .fuel .copyFirst .cleanup
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .input .spare id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      .spare .input .work false .copySecond (some .compare)
  | .compare => compareLoop
  | .restore => Reduction.MachineTransfer.loopAt
      .saved .power id false .restore (some .decide)
  | .decide => .branch (fun state => state.1.2)
      (.load (fun state => ((state.1.1, false), none)) (.goto fun _ => .scale))
      (.load (fun state => ((state.1.1, false), none)) (.goto fun _ => .cleanup))
  | .scale => scaleLoop g
  | .transfer => Reduction.MachineTransfer.loopAt
      .product .power id false .transfer (some .guard)
  | .cleanup => MachineDrain.drain .fuel .cleanup none

end MinUncutGames.Foundations.Complexity.MachineCeilingPower

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCloudPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineCloudPadding

open _root_.Turing
open MinUncutGames.Foundations.PCP

namespace Placement

variable {K K' Λ Λ' σ : Type}

def tapes (view : K' → Option K) (source : K → List Bool)
    (extra : K' → List Bool) : K' → List Bool :=
  fun j => match view j with
    | some k => source k
    | none => extra j

def statement (tape : K → K') (labels : Λ → Λ') (exit : Option Λ') :
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K' => Bool) Λ' σ
  | .push k f next => .push (tape k) f (statement tape labels exit next)
  | .peek k f next => .peek (tape k) f (statement tape labels exit next)
  | .pop k f next => .pop (tape k) f (statement tape labels exit next)
  | .load f next => .load f (statement tape labels exit next)
  | .branch f yes no => .branch f (statement tape labels exit yes) (statement tape labels exit no)
  | .goto f => .goto (fun state => labels (f state))
  | .halt => match exit with
    | some l => .goto (fun _ => l)
    | none => .halt

end Placement

inductive Tape
  | table | query | count | work | scratch | spare | power | level | fuel | product
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.table, .query, .count, .work, .scratch, .spare,
  .power, .level, .fuel, .product]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

def memory (table query count work scratch spare power level fuel product : List Bool) :
    Tape → List Bool
  | .table => table
  | .query => query
  | .count => count
  | .work => work
  | .scratch => scratch
  | .spare => spare
  | .power => power
  | .level => level
  | .fuel => fuel
  | .product => product

@[simp] theorem update_count (a b c d e f g h i j x : List Bool) :
    Function.update (memory a b c d e f g h i j) .count x = memory a b x d e f g h i j := by
  funext k; cases k <;> rfl
@[simp] theorem update_scratch (a b c d e f g h i j x : List Bool) :
    Function.update (memory a b c d e f g h i j) .scratch x = memory a b c d x f g h i j := by
  funext k; cases k <;> rfl
@[simp] theorem update_power (a b c d e f g h i j x : List Bool) :
    Function.update (memory a b c d e f g h i j) .power x = memory a b c d e f x h i j := by
  funext k; cases k <;> rfl

@[simp] theorem update_level (a b c d e f g h i j x : List Bool) :
    Function.update (memory a b c d e f g h i j) .level x = memory a b c d e f g x i j := by
  funext k; cases k <;> rfl

def countView : Tape → Option MachineCloudCount.Tape
  | .table => some .original
  | .query => some .target
  | .count => some .count
  | .work => some .work
  | .scratch => some .scratch
  | .spare => some .spare
  | _ => none

def powerView : Tape → Option MachineCeilingPower.Tape
  | .count => some .input
  | .work => some .work
  | .power => some .power
  | .scratch => some .saved
  | .level => some .level
  | .fuel => some .fuel
  | .spare => some .spare
  | .product => some .product
  | _ => none

@[simp] theorem countMemory (a b c d e f g h i j : List Bool) :
    Placement.tapes countView (MachineCloudCount.memory a d b e c f)
      (memory a b c d e f g h i j) = memory a b c d e f g h i j := by
  funext k; cases k <;> rfl

@[simp] theorem powerMemory (a b c d e f g h i j : List Bool) :
    Placement.tapes powerView (MachineCeilingPower.memory c d g e h i f j)
      (memory a b c d e f g h i j) = memory a b c d e f g h i j := by
  funext k; cases k <;> rfl

end MinUncutGames.Foundations.Complexity.MachineCloudPadding

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_GraphGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

def overlayPorts (d e : Nat) : (Fin d ⊕ Fin e) ≃ Fin (d + e) := finSumFinEquiv

@[simp] theorem overlayPorts_inl_val (d e : Nat) (i : Fin d) :
    (overlayPorts d e (Sum.inl i)).val = i.val := rfl

@[simp] theorem overlayPorts_inr_val (d e : Nat) (i : Fin e) :
    (overlayPorts d e (Sum.inr i)).val = d + i.val := rfl

def lazyPorts (d : Nat) : (Bool × Fin d) ≃ Fin (2 * d) :=
  (Equiv.prodCongr finTwoEquiv.symm (Equiv.refl (Fin d))).trans finProdFinEquiv

@[simp] theorem lazyPorts_false_val (d : Nat) (i : Fin d) :
    (lazyPorts d (false, i)).val = i.val := by
  simp [lazyPorts, finTwoEquiv, finProdFinEquiv]

@[simp] theorem lazyPorts_true_val (d : Nat) (i : Fin d) :
    (lazyPorts d (true, i)).val = i.val + d := by
  simp [lazyPorts, finTwoEquiv, finProdFinEquiv]

end MinUncutGames.Foundations.PCP.PreprocessingOverlayTables

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingRegularTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

def paddingList {n : Nat} (padding : Fin n → Nat) :
    List (Σ v : Fin n, Fin (padding v)) :=
  (List.finRange n).sigma (fun v => List.finRange (padding v))

theorem paddingList_nodup {n : Nat} (padding : Fin n → Nat) :
    (paddingList padding).Nodup :=
  (List.nodup_finRange n).sigma (fun v => List.nodup_finRange (padding v))

theorem mem_paddingList {n : Nat} (padding : Fin n → Nat)
    (z : Σ v : Fin n, Fin (padding v)) : z ∈ paddingList padding := by
  rcases z with ⟨v, k⟩
  simp only [paddingList, List.mem_sigma, List.mem_finRange, and_self]

def paddingListOrder {n : Nat} (padding : Fin n → Nat) :
    (Σ v : Fin n, Fin (padding v)) ≃ Fin (paddingList padding).length :=
  PreprocessingCloudIndex.listEquiv (paddingList padding)
    (paddingList_nodup padding) (mem_paddingList padding)

theorem paddingList_length {n : Nat} (padding : Fin n → Nat) :
    (paddingList padding).length = ∑ v, padding v := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    (Fintype.card_congr (paddingListOrder padding)).symm

def paddingOrder {n : Nat} (padding : Fin n → Nat) :
    (Σ v : Fin n, Fin (padding v)) ≃ Fin (∑ v, padding v) :=
  (paddingListOrder padding).trans (finCongr (paddingList_length padding))

def unitOrder : Unit ≃ Fin 1 where
  toFun _ := ⟨0, Nat.zero_lt_one⟩
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv k := Subsingleton.elim _ _

def portOrder (q : Nat) : (Fin q ⊕ Unit) ≃ Fin (q + 1) :=
  (Equiv.sumCongr (Equiv.refl _) unitOrder).trans finSumFinEquiv

@[simp] theorem portOrder_internal (q : Nat) (p : Fin q) :
    (portOrder q (Sum.inl p)).val = p.val := rfl

@[simp] theorem portOrder_inherited (q : Nat) :
    (portOrder q (Sum.inr ())).val = q := rfl

end MinUncutGames.Foundations.PCP.PreprocessingRegularTables

namespace MinUncutGames.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

def vertexEquiv (h : n ≤ m) : Fin n ⊕ Fin (m - n) ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

@[simp] theorem vertexEquiv_inl (h : n ≤ m) (v : Fin n) :
    vertexEquiv h (Sum.inl v) = v.castLE h := rfl

@[simp] theorem vertexEquiv_inr_val (h : n ≤ m) (v : Fin (m - n)) :
    (vertexEquiv h (Sum.inr v)).val = n + v.val := rfl

@[simp] theorem vertexEquiv_symm_old (h : n ≤ m) (v : Fin n) :
    (vertexEquiv h).symm (v.castLE h) = Sum.inl v :=
  (vertexEquiv h).symm_apply_apply (Sum.inl v)

def dartEquiv (h : n ≤ m) :
    (Fin n ⊕ Fin (m - n)) × Fin d ≃ Fin m × Fin d :=
  Equiv.prodCongr (vertexEquiv h) (Equiv.refl _)

@[simp] theorem dartEquiv_apply (h : n ≤ m)
    (v : Fin n ⊕ Fin (m - n)) (p : Fin d) :
    dartEquiv h (v, p) = (vertexEquiv h v, p) := rfl

end MinUncutGames.Foundations.PCP.PreprocessingPaddingTables

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingTableSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

abbrev PortWords (D : Type*) (t : Nat) := (n : Fin (t + 1)) × (Fin n.val → D)

def scanWitness {A : Type*} (p : A → Prop) [DecidablePred p] :
    (xs : List A) → (∃ a ∈ xs, p a) → {a // p a}
  | [], h => False.elim (by simp at h)
  | a :: xs, h =>
    if ha : p a then ⟨a, ha⟩ else
      scanWitness p xs (by
        obtain ⟨b, hb, hp⟩ := h
        rcases List.mem_cons.mp hb with he | hm
        · exact False.elim (ha (he ▸ hp))
        · exact ⟨b, hm, hp⟩)

abbrev PaddedLabel (D : Type*) (t : Nat) (A : Type*) := PortWords D t → A

end MinUncutGames.Foundations.PCP.PoweringLabels

end
section
namespace MinUncutGames.Foundations.PCP.PoweringAddresses

open PoweringWalks PoweringLabels
open scoped BigOperators

variable {V : Type*}

def allWords (d : Nat) : (n : Nat) → List (Fin n → Fin d)
  | 0 => [Fin.elim0]
  | n + 1 => (List.finRange d).flatMap fun a =>
      (allWords d n).map fun p => Fin.cases a p

theorem mem_allWords (d : Nat) :
    ∀ n (p : Fin n → Fin d), p ∈ allWords d n := by
  intro n
  induction n with
  | zero =>
    intro p
    simp only [allWords, List.mem_singleton]
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro p
    simp only [allWords, List.mem_flatMap, List.mem_map]
    refine ⟨p 0, List.mem_finRange (p 0), (fun j => p j.succ), ih _, ?_⟩
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

def allAddresses (d t : Nat) : List (PortWords (Fin d) t) :=
  (List.finRange (t + 1)).flatMap fun n =>
    (allWords d n.val).map fun p => Sigma.mk n p

theorem mem_allAddresses (d t : Nat) (w : PortWords (Fin d) t) :
    w ∈ allAddresses d t := by
  rcases w with ⟨n, p⟩
  unfold allAddresses
  apply List.mem_flatMap.mpr
  refine ⟨n, List.mem_finRange n, ?_⟩
  exact List.mem_map.mpr ⟨p, mem_allWords d n.val p, rfl⟩

end MinUncutGames.Foundations.PCP.PoweringAddresses

end
section
namespace MinUncutGames.Foundations.PCP.PoweringEnumeration

open PoweringLabels
open scoped BigOperators

def addressCount (d t : Nat) : Nat := ∑ i : Fin (t + 1), d ^ i.val

def reverseWordEquiv (d n : Nat) : (Fin n → Fin d) ≃ (Fin n → Fin d) where
  toFun p i := p i.rev
  invFun p i := p i.rev
  left_inv p := by funext i; simp only [Fin.rev_rev]
  right_inv p := by funext i; simp only [Fin.rev_rev]

def wordEquiv (d n : Nat) : (Fin n → Fin d) ≃ Fin (d ^ n) :=
  (reverseWordEquiv d n).trans finFunctionFinEquiv

def addressEquiv (d t : Nat) : PortWords (Fin d) t ≃ Fin (addressCount d t) :=
  (Equiv.sigmaCongrRight (fun i : Fin (t + 1) => wordEquiv d i.val)).trans
    finSigmaFinEquiv

def paddedLabelEquiv (d t q : Nat) :
    PaddedLabel (Fin d) t (Fin q) ≃ Fin (q ^ addressCount d t) :=
  ((addressEquiv d t).arrowCongr (Equiv.refl (Fin q))).trans
    (wordEquiv q (addressCount d t))

def orientationEquiv : Bool ≃ Fin 2 := finTwoEquiv.symm

@[simp] theorem orientationEquiv_false : orientationEquiv false = 0 := rfl
@[simp] theorem orientationEquiv_true : orientationEquiv true = 1 := rfl

def dartBlockEquiv (d n : Nat) :
    ((Fin (n + 1) → Fin d) × Bool) ≃ Fin (2 * d ^ (n + 1)) :=
  ((wordEquiv d (n + 1)).prodCongr orientationEquiv).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm (d ^ (n + 1)) 2)))

def dartVertexEquiv (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) ≃
      (Fin vertices × ((Fin (n + 1) → Fin d) × Bool)) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv x := by rcases x with ⟨b, v, p⟩; rfl
  right_inv x := by rcases x with ⟨v, p, b⟩; rfl

def dartEquiv (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) ≃
      Fin (2 * vertices * d ^ (n + 1)) :=
  (dartVertexEquiv vertices d n).trans
    (((Equiv.refl (Fin vertices)).prodCongr (dartBlockEquiv d n)).trans
      (finProdFinEquiv.trans
        (finCongr (show vertices * (2 * d ^ (n + 1)) =
          2 * vertices * d ^ (n + 1) by ac_rfl))))

def encodeLabel (d t q : Nat) :
    PaddedLabel (Fin d) t (Fin q) → Fin (q ^ addressCount d t) := paddedLabelEquiv d t q

def decodeLabel (d t q : Nat) :
    Fin (q ^ addressCount d t) → PaddedLabel (Fin d) t (Fin q) :=
  (paddedLabelEquiv d t q).symm

@[simp] theorem decodeLabel_encodeLabel (d t q : Nat) (a : PaddedLabel (Fin d) t (Fin q)) :
    decodeLabel d t q (encodeLabel d t q a) = a := (paddedLabelEquiv d t q).symm_apply_apply a

@[simp] theorem encodeLabel_decodeLabel (d t q : Nat) (i : Fin (q ^ addressCount d t)) :
    encodeLabel d t q (decodeLabel d t q i) = i := (paddedLabelEquiv d t q).apply_symm_apply i

end MinUncutGames.Foundations.PCP.PoweringEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringOpinionTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringOpinionTables

open PoweringWalks PoweringLabels PoweringAddresses
open scoped BigOperators

variable {X A : Type*}

theorem match_in_tail (p : X → Prop) {a : X} {xs : List X}
    (h : ∃ b ∈ a :: xs, p b) (ha : ¬p a) : ∃ b ∈ xs, p b := by
  obtain ⟨b, hb, hp⟩ := h
  rcases List.mem_cons.mp hb with he | hm
  · exact False.elim (ha (he ▸ hp))
  · exact ⟨b, hm, hp⟩

def firstIndex (p : X → Prop) [DecidablePred p] :
    (xs : List X) → (∃ a ∈ xs, p a) → Fin xs.length
  | [], h => False.elim (by simp at h)
  | a :: xs, h =>
    if ha : p a then ⟨0, Nat.zero_lt_succ xs.length⟩ else
      (firstIndex p xs (match_in_tail p h ha)).succ

theorem get_firstIndex (p : X → Prop) [DecidablePred p] :
    ∀ (xs : List X) (h : ∃ a ∈ xs, p a),
      xs.get (firstIndex p xs h) = (scanWitness p xs h).val := by
  intro xs
  induction xs with
  | nil => intro h; simp at h
  | cons a xs ih =>
    intro h
    by_cases ha : p a
    · simp [firstIndex, scanWitness, ha]
    · simpa only [firstIndex, scanWitness, ha, dite_false, List.get_cons_succ'] using
        ih (match_in_tail p h ha)

abbrev AddressIndex (d t : Nat) := Fin (allAddresses d t).length

variable {vertices d : Nat}

abbrev LabelTable (d t : Nat) (A : Type*) := Vector A (allAddresses d t).length

end MinUncutGames.Foundations.PCP.PoweringOpinionTables

end
section
namespace MinUncutGames.Foundations.PCP.GenericGraphTables

open MinUncutGames.Foundations.Complexity

abbrev Label (q : Nat) := Fin q
abbrev RelationTable (q : Nat) := Vector Bool (q * q)

variable {q : Nat}

def relationIndex (q : Nat) : (Label q) × (Label q) ≃ Fin (q * q) := finProdFinEquiv

def relationAt (table : (RelationTable q)) (a b : (Label q)) : Bool :=
  table[(relationIndex q) (a, b)]

def relationOf (predicate : (Label q) → (Label q) → Bool) : (RelationTable q) :=
  Vector.ofFn (fun i => predicate ((relationIndex q).symm i).1 ((relationIndex q).symm i).2)

@[simp] theorem relationAt_relationOf (predicate : (Label q) → (Label q) → Bool) (a b : (Label q)) :
    relationAt (relationOf predicate) a b = predicate a b := by
  simp [relationAt, relationOf]

structure DartRow (q vertices darts : Nat) where
  tail : Fin vertices
  reverseIndex : Fin darts
  relation : (RelationTable q)

abbrev Rows (q vertices darts : Nat) := Vector (DartRow q vertices darts) darts

def reverseAt {n m : Nat} (rows : Rows q n m) (e : Fin m) : Fin m :=
  rows[e].reverseIndex

def acceptsAt {n m : Nat} (rows : Rows q n m) (e : Fin m) (a b : (Label q)) : Bool :=
  relationAt rows[e].relation a b

def Valid {n m : Nat} (rows : Rows q n m) : Prop :=
  (∀ e, reverseAt rows (reverseAt rows e) = e) ∧
  (∀ e a b, acceptsAt rows (reverseAt rows e) b a = acceptsAt rows e a b)

structure Table (q : Nat) where
  vertices : Nat
  darts : Nat
  rows : Rows q vertices darts
  valid : Valid rows

def rowList (table : (Table q)) : List (DartRow q table.vertices table.darts) := table.rows.toList

@[simp] theorem rowList_length (table : (Table q)) : (rowList table).length = table.darts := by
  simp [rowList]

def bitWord (b : Bool) : Nat := if b then 1 else 0

def relationWords (relation : (RelationTable q)) : List Nat := relation.toList.map bitWord

@[simp] theorem relationWords_length (relation : (RelationTable q)) :
    (relationWords relation).length = (q * q) := by simp [relationWords]

end MinUncutGames.Foundations.PCP.GenericGraphTables

end
section
namespace MinUncutGames.Foundations.PCP.PoweringTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration

def labelCount (d n : Nat) : Nat := 64 ^ addressCount d (n + 1)

def dartCount (vertices d n : Nat) : Nat := 2 * vertices * d ^ (n + 1)

end MinUncutGames.Foundations.PCP.PoweringTables

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringTableSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.QueryIncidence

structure Verifier (E X : Type*) (q : Nat) where
  query : E → Fin q → X
  accepts : E → (Fin q → Bool) → Bool

abbrev Label (q : Nat) := Fin q → Bool
abbrev Vertex (E X : Type*) := E ⊕ X
abbrev Dart (E : Type*) (q : Nat) := (E × Fin q) × Bool

variable {E X : Type*} {q : Nat}

def zeroSlot (positive : 0 < q) : Fin q := ⟨0, positive⟩

def decodeRight (positive : 0 < q) (label : Label q) : Bool := label (zeroSlot positive)

def encodeRight (bit : Bool) : Label q := fun _ => bit

@[simp] theorem decode_encodeRight (positive : 0 < q) (bit : Bool) :
    decodeRight positive (encodeRight bit) = bit := rfl

def canonicalSlot [DecidableEq X] (T : Verifier E X q) (event : E) (i : Fin q) : Fin q :=
  Fin.find (fun j => T.query event j = T.query event i) ⟨i, rfl⟩

def RepeatedConsistent (T : Verifier E X q) (event : E) (label : Label q) : Prop :=
  ∀ i j, T.query event i = T.query event j → label i = label j

instance repeatedConsistentDecidable [DecidableEq X]
    (T : Verifier E X q) (event : E) (label : Label q) :
    Decidable (RepeatedConsistent T event label) := by
  unfold RepeatedConsistent
  infer_instance

def LeftValid (T : Verifier E X q) (event : E) (label : Label q) : Prop :=
  T.accepts event label = true ∧ RepeatedConsistent T event label

instance leftValidDecidable [DecidableEq X]
    (T : Verifier E X q) (event : E) (label : Label q) :
    Decidable (LeftValid T event label) := by
  unfold LeftValid
  infer_instance

def incidenceAccept [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (event : E) (slot : Fin q) (left right : Label q) : Bool :=
  decide (LeftValid T event left) &&
    decide (left (canonicalSlot T event slot) = decodeRight positive right)

def reverse : Dart E q → Dart E q := fun d => (d.1, !d.2)

theorem reverse_involutive : Function.Involutive (reverse : Dart E q → Dart E q) := by
  rintro ⟨⟨event, slot⟩, orientation⟩
  cases orientation <;> rfl

def reverseEquiv : Dart E q ≃ Dart E q where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_involutive
  right_inv := reverse_involutive

def tail (T : Verifier E X q) : Dart E q → Vertex E X
  | ((event, _), false) => .inl event
  | ((event, slot), true) => .inr (T.query event slot)

def predicate [DecidableEq X] (T : Verifier E X q) (positive : 0 < q) :
    Dart E q → Label q → Label q → Bool
  | ((event, slot), false), a, b => incidenceAccept T positive event slot a b
  | ((event, slot), true), a, b => incidenceAccept T positive event slot b a

@[simp] theorem card_label (q : Nat) : Fintype.card (Label q) = 2 ^ q := by
  simp [Label]

@[simp] theorem card_vertex [Fintype E] [Fintype X] :
    Fintype.card (Vertex E X) = Fintype.card E + Fintype.card X := by
  simp [Vertex, Fintype.card_sum]

@[simp] theorem card_dart [Fintype E] :
    Fintype.card (Dart E q) = 2 * q * Fintype.card E := by
  simp [Dart, Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

end MinUncutGames.Foundations.PCP.QueryIncidence

noncomputable section

namespace MinUncutGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open MinUncutGames.Foundations.Hastad

def pairWord {X : Type*} (left right : X → Bool) : Bool × X → Bool :=
  fun p => if p.1 then right p.2 else left p.2

end MinUncutGames.Foundations.PCP.CodeComposition

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_AlphabetReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.PCP.AlphabetReduction

open MinUncutGames.Foundations.Hastad
open CodeComposition

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev LegalPair (accepts : A → A → Bool) :=
  {p : A × A // accepts p.1 p.2 = true}

end MinUncutGames.Foundations.PCP.AlphabetReduction

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_UniformRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.UniformRestriction

open scoped BigOperators

variable {B : Type*} (p : B → Prop)

def restrict (f : B → Bool) : {b // p b} → Bool := fun b => f b.1

variable [DecidablePred p]

def extend (g : {b // p b} → Bool) : B → Bool :=
  fun b => if hb : p b then g ⟨b, hb⟩ else false

omit [DecidablePred p] in
@[simp] theorem restrict_apply (f : B → Bool) (b : {b // p b}) :
    restrict p f b = f b.1 := rfl

@[simp] theorem extend_apply_of_mem (g : {b // p b} → Bool) (b : B) (hb : p b) :
    extend p g b = g ⟨b, hb⟩ := by
  simp [extend, hb]

@[simp] theorem extend_apply_of_not_mem (g : {b // p b} → Bool) (b : B)
    (hb : ¬ p b) : extend p g b = false := by
  simp [extend, hb]

@[simp] theorem restrict_extend (g : {b // p b} → Bool) :
    restrict p (extend p g) = g := by
  funext b
  simp [restrict, extend, b.property]

end MinUncutGames.Foundations.PCP.UniformRestriction

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_AlphabetGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.AlphabetTable.Enumeration

open MinUncutGames.Foundations.Hastad
open scoped BigOperators

def bitValue (bit : Bool) : Nat := if bit then 1 else 0

def boolEquiv : Bool ≃ Fin 2 := finTwoEquiv.symm

@[simp] theorem boolEquiv_val (bit : Bool) : (boolEquiv bit).val = bitValue bit := by
  cases bit <;> rfl

def productEquiv {A B : Type*} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A × B ≃ Fin (a * b) :=
  (Equiv.prodCongr left right).trans finProdFinEquiv

@[simp] theorem productEquiv_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (x : A) (y : B) :
    (productEquiv left right (x, y)).val = (left x).val * b + (right y).val := by
  change (right y).val + b * (left x).val = _
  simp [Nat.mul_comm, Nat.add_comm]

def sumEquiv {A B : Type*} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A ⊕ B ≃ Fin (a + b) :=
  (Equiv.sumCongr left right).trans finSumFinEquiv

@[simp] theorem sumEquiv_inl_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (x : A) :
    (sumEquiv left right (.inl x)).val = (left x).val := rfl

@[simp] theorem sumEquiv_inr_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (y : B) :
    (sumEquiv left right (.inr y)).val = a + (right y).val := rfl

def tapeCount (q : Nat) : Nat := 2 ^ q
def pairTapeCount (q : Nat) : Nat := 2 ^ (q * q)
def fiveTapeCount (q : Nat) : Nat := pairTapeCount q ^ 5
def localCount (q : Nat) : Nat := 4 * (2 * tapeCount q) * fiveTapeCount q
def eventCount (m q : Nat) : Nat := m * localCount q
def addressCount (n m q : Nat) : Nat := n * tapeCount q + m * pairTapeCount q
def vertexCount (n m q : Nat) : Nat := eventCount m q + addressCount n m q
def dartCount (m q : Nat) : Nat := eventCount m q * 12

def pairIndex (q : Nat) : Fin q × Fin q ≃ Fin (q * q) := finProdFinEquiv

def ordered {A : Type*} {count : Nat} (order : A ≃ Fin count) : List A :=
  List.ofFn order.symm

@[simp] theorem ordered_length {A : Type*} {count : Nat} (order : A ≃ Fin count) :
    (ordered order).length = count := by simp [ordered]

@[simp] theorem ordered_refl (n : Nat) : ordered (Equiv.refl (Fin n)) = List.finRange n := rfl

@[simp] theorem ordered_bool : ordered boolEquiv = [false, true] := rfl

end MinUncutGames.Foundations.PCP.AlphabetTable.Enumeration

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Relations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.AlphabetTable.Relations

open Hastad

variable {q : Nat}

def oldPredicate (old : Vector Bool (q * q)) (a b : Fin q) : Bool :=
  old[(finProdFinEquiv (a, b) : Fin (q * q))]

end MinUncutGames.Foundations.PCP.AlphabetTable.Relations

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RuntimeModel2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.RuntimeModel

open _root_.Turing
open MinUncutGames.Foundations.Complexity

inductive Tape
  | original | cursor | scan | vertices | darts | counter | edge
  | tail | reverseIndex | head | scratch | indexScan
  | compareLeft | compareRight | reversed | output
  deriving DecidableEq

abbrev Alphabet (_ : Tape) := Bool

abbrev Flags := Bool × Bool × Option Bool
abbrev Ambient (q : Nat) := Flags × GenericGraphTables.RelationTable q
abbrev State (q : Nat) := Ambient q × Option Bool

def normal {q : Nat} (relation : GenericGraphTables.RelationTable q) (selfLoop : Bool) : State q :=
  (((selfLoop, false, none), relation), none)

def initial (q : Nat) : State q := normal (Vector.replicate (q * q) false) false

def context {q : Nat} (ambient : Ambient q) : GenericGraphTables.RelationTable q × Bool :=
  (ambient.2, ambient.1.1)

def setupPorts : Fin 7 → Tape :=
  ![.original, .cursor, .vertices, .darts, .counter, .scratch, .edge]

def rowSources : Fin 5 → Tape := ![.vertices, .darts, .edge, .tail, .head]
def headerSources : Fin 2 → Tape := ![.vertices, .darts]
def fieldPorts : Fin 3 → Tape := ![.tail, .reverseIndex, .head]

def cleanupPorts : Fin 15 → Tape :=
  ![.original, .cursor, .scan, .vertices, .darts, .counter, .edge,
    .tail, .reverseIndex, .head, .scratch, .indexScan, .compareLeft, .compareRight, .reversed]

end MinUncutGames.Foundations.PCP.AlphabetTable.RuntimeModel

end
section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.CompareLoop

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open RuntimeModel

inductive Label
  | leftFirst | leftSecond | rightFirst | rightSecond | compare
  | equalStore | differentStore
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.leftFirst, .leftSecond, .rightFirst,
  .rightSecond, .compare, .equalStore, .differentStore]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

end MinUncutGames.Foundations.PCP.AlphabetTable.CompareLoop

end
section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Emitter

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open Reduction.MachineSubstitution (pushWord )

inductive Command (h : Nat) (σ : Type) (bound : Nat)
  | literal (word : List Bool)
  | bit (value : σ → Bool)
  | bounded (value : σ → Fin bound)
  | scaled (source : Fin h) (coefficient : Nat)
  | scaledIf (source : Fin h) (coefficient : Nat) (active : σ → Bool)

inductive Phase (bound : Nat)
  | entry | emit (symbol : Bool) | restore | offset (value : Fin bound)
  | scanIf (active : Bool) | emitIf (active symbol : Bool)
  deriving DecidableEq, Fintype

variable {K : Type}

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Unit) × Option Bool

def transition (_ : Unit) (_ : Bool) : Unit := ()
def payload (coefficient : Nat) (_ : Unit) (symbol : Bool) : List Bool :=
  if symbol then List.replicate coefficient true else []

variable {Λ σ : Type} {h bound : Nat} [DecidableEq K]

def commandStatement (sources : Fin h → K) (scratch output : K)
    (labels : Phase bound → Λ) (next : Λ) (command : Command h σ bound) :
    Phase bound → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .entry => match command with
    | .literal word => pushWord output word
        (.load (fun state => (state.1, none)) (.goto fun _ => next))
    | .bit value => .branch (fun state => value state.1.1)
        (pushWord output [true, false]
          (.load (fun state => (state.1, none)) (.goto fun _ => next)))
        (pushWord output [false]
          (.load (fun state => (state.1, none)) (.goto fun _ => next)))
    | .bounded value => .goto fun state => labels (.offset (value state.1.1))
    | .scaled source _ => MachineTransducerCopy.scanLoop (sources source) scratch ()
        (fun _ symbol => labels (.emit symbol)) (labels .restore)
    | .scaledIf _ _ active => .goto fun state => labels (.scanIf (active state.1.1))
  | .emit symbol => match command with
    | .scaled _ coefficient => MachineTransducerCopy.emitter output transition
        (payload coefficient) (labels .entry) () symbol
    | _ => .goto fun _ => next
  | .restore => match command with
    | .scaled source _ | .scaledIf source _ _ => Reduction.MachineTransfer.loopAt scratch (sources source)
        id false (labels .restore) (some next)
    | _ => .goto fun _ => next
  | .offset value => pushWord output (List.replicate value.val true)
      (.load (fun state => (state.1, none)) (.goto fun _ => next))
  | .scanIf active => match command with
    | .scaledIf source _ _ => MachineTransducerCopy.scanLoop (sources source) scratch ()
        (fun _ symbol => labels (.emitIf active symbol)) (labels .restore)
    | _ => .goto fun _ => next
  | .emitIf active symbol => match command with
    | .scaledIf _ coefficient _ => MachineTransducerCopy.emitter output transition
        (payload (if active then coefficient else 0)) (labels (.scanIf active)) () symbol
    | _ => .goto fun _ => next

abbrev Label (count bound : Nat) := Fin (count + 1) × Phase bound

def labelAt (count bound r : Nat) (phase : Phase bound) : Label count bound :=
  (⟨min r count, by omega⟩, phase)

def commandAt {count : Nat} (commands : Fin count → Command h σ bound) (r : Nat) :
    Command h σ bound :=
  if hr : r < count then commands ⟨r, hr⟩ else .literal []

def statement {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (labels : Label count bound → Λ) (exit : Option Λ) (label : Label count bound) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  if label.1.val < count then
    commandStatement sources scratch output (fun phase => labels (labelAt count bound label.1.val phase))
      (labels (labelAt count bound (label.1.val + 1) .entry))
      (commandAt commands label.1.val) label.2
  else Reduction.MachineTransfer.exitAt output exit

def listCommands (commands : List (Command h σ bound)) :
    Fin commands.length → Command h σ bound := fun i => commands[i]

def affineCommands (terms : List (Fin h × Nat)) (offset : σ → Fin bound) :
    List (Command h σ bound) :=
  terms.map (fun term => .scaled term.1 term.2) ++ [.bounded offset, .literal [false]]

@[simp] theorem affineCommands_length (terms : List (Fin h × Nat)) (offset : σ → Fin bound) :
    (affineCommands terms offset).length = terms.length + 2 := by
  simp [affineCommands]

def bitCommands (bits : List (σ → Bool)) : List (Command h σ bound) := bits.map .bit

end MinUncutGames.Foundations.PCP.AlphabetTable.Emitter

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Addresses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.AlphabetTable.Addresses

open MinUncutGames.Foundations.Hastad
open Enumeration

abbrev Terms := List (Fin 5 × Nat)

structure Field (bound : Nat) where
  terms : Terms
  offset : Fin bound

end MinUncutGames.Foundations.PCP.AlphabetTable.Addresses

namespace MinUncutGames.Foundations.PCP.AlphabetTable.EmitRows

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open Emitter

abbrev Context (q : Nat) := Vector Bool (q * q) × Bool

end MinUncutGames.Foundations.PCP.AlphabetTable.EmitRows

namespace MinUncutGames.Foundations.PCP.AlphabetTable.Cleanup

open _root_.Turing
open Complexity
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (initial : σ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun _ => (initial, none))
    (match exit with | none => .halt | some label => .goto fun _ => label)

def instruction {n : Nat} (selected : Fin n → K) (labels : Fin (n + 1) → Λ)
    (initial : σ) (exit : Option Λ) (phase : Fin (n + 1)) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  if h : phase.val < n then
    MachineDrain.drain (selected ⟨phase.val, h⟩) (labels phase)
      (some (labels ⟨phase.val + 1, Nat.succ_lt_succ h⟩))
  else finish initial exit

omit [DecidableEq K] in
@[simp] theorem instruction_drain {n : Nat} (selected : Fin n → K)
    (labels : Fin (n + 1) → Λ) (initial : σ) (exit : Option Λ) (i : Fin n) :
    instruction selected labels initial exit i.castSucc =
      MachineDrain.drain (selected i) (labels i.castSucc) (some (labels i.succ)) := by
  simp [instruction, i.isLt]
  rfl

omit [DecidableEq K] in
@[simp] theorem instruction_finish {n : Nat} (selected : Fin n → K)
    (labels : Fin (n + 1) → Λ) (initial : σ) (exit : Option Λ) :
    instruction selected labels initial exit (Fin.last n) = finish initial exit := by
  simp [instruction]

end MinUncutGames.Foundations.PCP.AlphabetTable.Cleanup

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Input
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Setup

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MinUncutGames.Foundations.Hastad

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

abbrev Ports (K : Type) := Fin 7 → K

inductive Label
  | copyFirst | copySecond | verticesStart | verticesLoop
  | dartsStart | dartsLoop | counterFirst | counterSecond | initialize_
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyFirst, .copySecond, .verticesStart,
  .verticesLoop, .dartsStart, .dartsLoop, .counterFirst, .counterSecond, .initialize_]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def statement (ports : Ports K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .copyFirst => Reduction.MachineTransfer.loopAt (ports 0) (ports 5) id false
      (labels .copyFirst) (some (labels .copySecond))
  | .copySecond => MachineCopy.forkLoop (ports 5) (ports 0) (ports 1) false
      (labels .copySecond) (some (labels .verticesStart))
  | .verticesStart => SourceMachine.fieldStart (ports 2) (labels .verticesLoop)
  | .verticesLoop => SourceMachine.fieldLoop (ports 1) (ports 2)
      (labels .verticesLoop) (some (labels .dartsStart))
  | .dartsStart => SourceMachine.fieldStart (ports 3) (labels .dartsLoop)
  | .dartsLoop => SourceMachine.fieldLoop (ports 1) (ports 3)
      (labels .dartsLoop) (some (labels .counterFirst))
  | .counterFirst => Reduction.MachineTransfer.loopAt (ports 3) (ports 5) id false
      (labels .counterFirst) (some (labels .counterSecond))
  | .counterSecond => MachineCopy.forkLoop (ports 5) (ports 3) (ports 4) false
      (labels .counterSecond) (some (labels .initialize_))
  | .initialize_ => .push (ports 6) (fun _ => false)
      (.load (fun state => (state.1, none)) (Reduction.MachineTransfer.exitAt (ports 6) exit))

end MinUncutGames.Foundations.PCP.AlphabetTable.Setup

end
section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.ReadRelation

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K] {q : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) (q : Nat) := (σ × RelationTable q) × Option Bool

def relationEquiv (q : Nat) : RelationTable q ≃ (Fin (q * q) → Bool) where
  toFun relation i := relation[i.val]
  invFun := Vector.ofFn
  left_inv relation := Vector.ofFn_getElem
  right_inv bits := by funext i; simp

@[instance_reducible] def relationFintype (q : Nat) : Fintype (RelationTable q) :=
  Fintype.ofEquiv (Fin (q * q) → Bool) (relationEquiv q).symm

@[instance_reducible] def stateFintype (σ : Type) (q : Nat) [Fintype σ] :
    Fintype (State σ q) := by
  letI := relationFintype q
  exact inferInstance

def readSlot (source : K) (i : Fin (q * q))
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  .pop source
    (fun state head =>
      ((state.1.1, state.1.2.set i.val (head.getD false) i.isLt), head))
    (.branch (fun state => state.2.getD false)
      (.pop source (fun state _ => (state.1, none)) next)
      (.load (fun state => (state.1, none)) next))

def readSlots (source : K) : List (Fin (q * q)) →
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) →
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q)
  | [], next => .load (fun state => (state.1, none)) next
  | i :: indices, next => readSlot source i (readSlots source indices next)

def readRelation (source : K)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  readSlots source (List.finRange (q * q)) next

def parser (source : K) (exitLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  readRelation source (.goto fun _ => exitLabel)

end MinUncutGames.Foundations.PCP.AlphabetTable.ReadRelation

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineFixedBlockMap

open _root_.Turing

abbrev Buffer (N : Nat) := Fin N → Bool

def emptyBuffer (N : Nat) : Buffer N := fun _ => false

section Chains

variable {K Λ σ : Type} {N : Nat}

def fill (slots : List (Fin N)) (bits buffer : Buffer N) : Buffer N :=
  slots.foldl (fun buffer i => Function.update buffer i (bits i)) buffer

theorem fill_apply (slots : List (Fin N)) (bits buffer : Buffer N) (i : Fin N) :
    fill slots bits buffer i = if i ∈ slots then bits i else buffer i := by
  induction slots generalizing buffer with
  | nil => simp [fill]
  | cons j slots ih =>
      change fill slots bits (Function.update buffer j (bits j)) i = _
      rw [ih]
      by_cases hm : i ∈ slots
      · simp [hm]
      · by_cases he : i = j <;> simp [hm, he]

@[simp] theorem fill_all (bits buffer : Buffer N) :
    fill (List.ofFn id) bits buffer = bits := by
  funext i
  simp [fill_apply, List.mem_ofFn]

end Chains

section Block

variable {K Λ σ : Type} {N M : Nat}

def finishAt (exit : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

end Block

end MinUncutGames.Foundations.Complexity.MachineFixedBlockMap

end
section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Lookup

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def skipBits (source : K) : Nat →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | 0, next => .load (fun state => (state.1, none)) next
  | count + 1, next =>
      let rest := skipBits source count next
      .pop source (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.pop source (fun state _ => (state.1, none)) rest)
          (.load (fun state => (state.1, none)) rest))

inductive Label
  | guard | skipTail | skipReverse | skipPredicate | select | copy
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.guard, .skipTail, .skipReverse, .skipPredicate,
  .select, .copy]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def statement (q : Nat) (counter source destination : K) (labels : Label → Λ)
    (exit : Option Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .guard => MachineUnaryCounter.guard counter (labels .skipTail) (labels .select)
  | .skipTail => MachineLookup.discard source (labels .skipTail) (labels .skipReverse)
  | .skipReverse => MachineLookup.discard source (labels .skipReverse) (labels .skipPredicate)
  | .skipPredicate => skipBits source (q * q) (.goto fun _ => labels .guard)
  | .select => Hastad.SourceMachine.fieldStart destination (labels .copy)
  | .copy => Hastad.SourceMachine.fieldLoop source destination (labels .copy) exit

abbrev HeadTapes (K : Type) := Fin 6 → K

end MinUncutGames.Foundations.PCP.AlphabetTable.Lookup

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineFiniteAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineFiniteAlphabet

open _root_.Turing

def FiniteAlphabet (M : FinTM2) : Prop := ∀ k, Finite (M.Γ k)

end MinUncutGames.Foundations.Complexity.MachineFiniteAlphabet

end
section
namespace MinUncutGames.Foundations.Complexity.MachineStateEquiv

open Turing.TM2

variable {K Λ σ τ : Type} {Γ : K → Type}

abbrev statement (e : σ ≃ τ) : Stmt Γ Λ σ → Stmt Γ Λ τ :=
  MachineControl.statement (id : Λ → Λ) e

@[simp] theorem statement_symm_statement (e : σ ≃ τ) (q : Stmt Γ Λ σ) :
    statement e.symm (statement e q) = q := by
  induction q <;>
    simp_all only [statement, MachineControl.statement, Equiv.symm_symm,
      Equiv.symm_apply_apply, id_eq]

def configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) : Cfg Γ Λ τ :=
  ⟨c.l, e c.var, c.stk⟩

@[simp] theorem configuration_label (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).l = c.l := rfl

@[simp] theorem configuration_state (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).var = e c.var := rfl

@[simp] theorem configuration_tapes (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).stk = c.stk := rfl

@[simp] theorem configuration_symm_configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    configuration e.symm (configuration e c) = c := by
  cases c
  simp only [configuration, Equiv.symm_apply_apply]

@[simp] theorem configuration_configuration_symm (e : σ ≃ τ) (c : Cfg Γ Λ τ) :
    configuration e (configuration e.symm c) = c := by
  cases c
  simp only [configuration, Equiv.apply_symm_apply]

def configurationEquiv (e : σ ≃ τ) : Cfg Γ Λ σ ≃ Cfg Γ Λ τ where
  toFun := configuration e
  invFun := configuration e.symm
  left_inv := configuration_symm_configuration e
  right_inv := configuration_configuration_symm e

@[simp] theorem configurationEquiv_apply (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    configurationEquiv e c = configuration e c := rfl

@[simp] theorem control_configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    MachineControl.configuration (id : Λ → Λ) e c = configuration e c := by
  cases c
  simp [MachineControl.configuration, configuration]

def program (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) : Λ → Stmt Γ Λ τ :=
  fun l => statement e (source l)

@[simp] theorem program_symm_program (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) :
    program e.symm (program e source) = source := by
  funext l
  exact statement_symm_statement e (source l)

variable [DecidableEq K]

theorem stepAux_transport (e : σ ≃ τ) (q : Stmt Γ Λ σ) (state : σ)
    (tapes : ∀ k, List (Γ k)) :
    stepAux (statement e q) (e state) tapes =
      configuration e (stepAux q state tapes) := by
  simpa only [statement, control_configuration] using
    MachineControl.stepAux_simulation (id : Λ → Λ) e q state tapes

theorem step_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) :
    step (program e source) (configuration e c) =
      (step source c).map (configuration e) := by
  cases c with
  | mk l state tapes =>
      cases l with
      | none => rfl
      | some l =>
          change some (stepAux (statement e (source l)) (e state) tapes) = _
          rw [stepAux_transport]
          rfl

end MinUncutGames.Foundations.Complexity.MachineStateEquiv

end
section
namespace MinUncutGames.Foundations.Complexity.MachineUnaryAffineAt

open _root_.Turing
open Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (restoreLabel : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun s => (s.1,none)) (.goto (fun _ => restoreLabel))

def scan (source scratch destination : K) (coefficient : Nat) (scanLabel restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun s head => (s.1,head))
    (.branch (fun s => s.2.getD false)
      (.push scratch (fun _ => true)
        (pushWord destination (List.replicate coefficient true) (.goto (fun _ => scanLabel))))
      (.branch (fun s => s.2.isSome)
        (.push source (fun _ => false) (finish restoreLabel))
        (finish restoreLabel)))

inductive Label
  | seed | scan | restore
  deriving DecidableEq

end MinUncutGames.Foundations.Complexity.MachineUnaryAffineAt

end
section
namespace MinUncutGames.Foundations.Complexity.MachineUnaryEqualityBit

open _root_.Turing

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Bool × Option Bool) × Option Bool

def clean (ambient : A) : State A := ((ambient, false, none), none)

inductive Label
  | seedLeft | scanLeft | restoreLeft
  | seedRight | scanRight | restoreRight
  | compare | equal | different
  deriving DecidableEq

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def emit (destination : K) (bit : Bool) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .push destination (fun _ => false)
    (if bit then .push destination (fun _ => true) (exitAt exit) else exitAt exit)

end MinUncutGames.Foundations.Complexity.MachineUnaryEqualityBit

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachinePreservingLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachinePreservingLookup

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive Label
  | copyFirst | copySecond | lookup (l : MachineLookup.Label)
  deriving DecidableEq, Fintype

def program (tape : Fin 5 → K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .copyFirst => Reduction.MachineTransfer.loopAt (tape 0) (tape 4) id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop (tape 4) (tape 0) (tape 2) false .copySecond (some (.lookup .guard))
  | .lookup l => MachineSubroutine.statement Label.lookup none
      (MachineLookup.program (tape 1) (tape 2) (tape 3) l)

end MinUncutGames.Foundations.Complexity.MachinePreservingLookup

namespace MinUncutGames.Foundations.Complexity.MachineAffineLookup

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive Label
  | seed | scan | restore | copyFirst | copySecond
  | lookup (l : MachineLookup.Label)
  deriving DecidableEq, Fintype

end MinUncutGames.Foundations.Complexity.MachineAffineLookup

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingPaddingOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingPaddingOffsets

open PreprocessingRegularTables
open scoped BigOperators

theorem idxOf_map_injective {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (xs : List A) (a : A) :
    (xs.map f).idxOf (f a) = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x = a
    · subst x; simp
    · simp [List.idxOf_cons_ne, h, hf.ne h, ih]

theorem sigma_idxOf {A : Type*} [DecidableEq A] (sizes : A → Nat)
    (xs : List A) (a : A) (ha : a ∈ xs) (j : Fin (sizes a)) :
    (xs.sigma (fun x => List.finRange (sizes x))).idxOf ⟨a, j⟩ =
      ((xs.take (xs.idxOf a)).map sizes).sum + j.val := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.sigma_cons]
    by_cases h : x = a
    · subst x
      have hm : (⟨a, j⟩ : Σ x, Fin (sizes x)) ∈
          (List.finRange (sizes a)).map (Sigma.mk a) := by
        exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
      rw [List.idxOf_append_of_mem hm,
        idxOf_map_injective (Sigma.mk a) (fun x y h => by cases h; rfl),
        List.idxOf_finRange]
      simp
    · have hm : (⟨a, j⟩ : Σ x, Fin (sizes x)) ∉
          (List.finRange (sizes x)).map (Sigma.mk x) := by
        intro hm
        rcases List.mem_map.mp hm with ⟨k, _, hk⟩
        exact h (congrArg Sigma.fst hk)
      rw [List.idxOf_append_of_notMem hm, List.length_map, List.length_finRange,
        ih (List.mem_of_ne_of_mem (Ne.symm h) ha), List.idxOf_cons_ne xs h]
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

def offset {n : Nat} (padding : Fin n → Nat) (k : Nat) : Nat :=
  (((List.finRange n).take k).map padding).sum

@[simp] theorem offset_zero {n : Nat} (padding : Fin n → Nat) : offset padding 0 = 0 := by
  simp [offset]

end MinUncutGames.Foundations.PCP.PreprocessingPaddingOffsets

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCloudPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineCloudPrefix

open _root_.Turing
open MinUncutGames.Foundations.PCP
open scoped BigOperators

inductive Tape
  | inner (k : MachineCloudPadding.Tape)
  | bound | remaining | total
  deriving DecidableEq, Fintype

def memory (inner : MachineCloudPadding.Tape → List Bool) (bound remaining total : List Bool) :
    Tape → List Bool
  | .inner k => inner k
  | .bound => bound
  | .remaining => remaining
  | .total => total

def frame (table query count power level bound remaining total : List Bool) : Tape → List Bool :=
  memory (MachineCloudPadding.memory table query count [] [] [] power level [] []) bound remaining total

@[simp] theorem frame_query (a b c d e f g h : List Bool) :
    frame a b c d e f g h (.inner .query) = b := rfl
@[simp] theorem frame_count (a b c d e f g h : List Bool) :
    frame a b c d e f g h (.inner .count) = c := rfl
@[simp] theorem frame_power (a b c d e f g h : List Bool) :
    frame a b c d e f g h (.inner .power) = d := rfl
@[simp] theorem frame_level (a b c d e f g h : List Bool) :
    frame a b c d e f g h (.inner .level) = e := rfl
@[simp] theorem frame_bound (a b c d e f g h : List Bool) :
    frame a b c d e f g h .bound = f := rfl
@[simp] theorem frame_remaining (a b c d e f g h : List Bool) :
    frame a b c d e f g h .remaining = g := rfl
@[simp] theorem frame_total (a b c d e f g h : List Bool) :
    frame a b c d e f g h .total = h := rfl

@[simp] theorem update_frame_query (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) (.inner .query) x =
      frame a x c d e f g h := by
  funext k; cases k with
  | inner k => cases k <;> rfl
  | bound => rfl
  | remaining => rfl
  | total => rfl
@[simp] theorem update_frame_count (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) (.inner .count) x =
      frame a b x d e f g h := by
  funext k; cases k with
  | inner k => cases k <;> rfl
  | bound => rfl
  | remaining => rfl
  | total => rfl
@[simp] theorem update_frame_power (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) (.inner .power) x =
      frame a b c x e f g h := by
  funext k; cases k with
  | inner k => cases k <;> rfl
  | bound => rfl
  | remaining => rfl
  | total => rfl
@[simp] theorem update_frame_level (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) (.inner .level) x =
      frame a b c d x f g h := by
  funext k; cases k with
  | inner k => cases k <;> rfl
  | bound => rfl
  | remaining => rfl
  | total => rfl

end MinUncutGames.Foundations.Complexity.MachineCloudPrefix

namespace MinUncutGames.Foundations.Complexity.MachinePreservingLookupClean

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive Label
  | run (label : MachinePreservingLookup.Label)
  | cleanup
  deriving DecidableEq, Fintype

def statement (tape : Fin 5 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .run label => MachineSubroutine.statement (fun label => labels (.run label))
      (some (labels .cleanup)) (MachinePreservingLookup.program tape label)
  | .cleanup => MachineDrain.drain (tape 2) (labels .cleanup) exit

end MinUncutGames.Foundations.Complexity.MachinePreservingLookupClean

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ExpanderRowControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.ExpanderRowControl

open ExpanderTables

abbrev degree (d : Nat) : Nat := d * d
abbrev cloudSize (d : Nat) : Nat := degree d * degree d
abbrev rowFactor (d : Nat) : Nat := cloudSize d * degree d

structure Control (d : Nat) where
  firstH : Fin (cloudSize d) × Fin d
  lastInput : Fin d
  firstG : Fin (degree d)
  secondG : Fin (degree d)
  lastH : Fin (cloudSize d) × Fin d
  deriving DecidableEq, Fintype

def squarePorts {d : Nat} (s : Control d) : Fin (degree d) × Fin (degree d) :=
  (rowIndex (degree d) (degree d)).symm s.firstH.1

def receiveFirst {d : Nat} (s : Control d) (returnedPort : Fin (degree d)) : Control d :=
  { s with firstG := returnedPort }

def firstOffset {d : Nat} (s : Control d) : Fin (degree d) := (squarePorts s).1
def secondOffset {d : Nat} (s : Control d) : Fin (degree d) := (squarePorts s).2

def outputPort {d : Nat} (s : Control d) : Fin (degree d) :=
  rowIndex d d (s.lastH.2,s.firstH.2)

def outputOffset {d : Nat} (s : Control d) : Fin (rowFactor d) :=
  rowIndex (cloudSize d) (degree d) (s.lastH.1,outputPort s)

def firstAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  degree d * vertex + (firstOffset s).val

def secondAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  degree d * vertex + (secondOffset s).val

def outputAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  rowFactor d * vertex + (outputOffset s).val

@[simp] theorem firstOffset_receiveFirst {d : Nat} (s : Control d) (r : Fin (degree d)) :
    firstOffset (receiveFirst s r) = firstOffset s := rfl

@[simp] theorem secondOffset_receiveFirst {d : Nat} (s : Control d) (r : Fin (degree d)) :
    secondOffset (receiveFirst s r) = secondOffset s := rfl

@[simp] theorem receiveFirst_port {d : Nat} (s : Control d) (r : Fin (degree d)) :
    (receiveFirst s r).firstG = r := rfl

end MinUncutGames.Foundations.PCP.ExpanderRowControl

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineFixedDivMod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineFixedDivMod

open _root_.Turing
open Reduction.MachineSubstitution (pushWord )

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) (d : Nat) := (σ × Fin d) × Option Bool

def residue (d : Nat) (positive : 0 < d) (n : Nat) : Fin d :=
  ⟨n % d, Nat.mod_lt n positive⟩

def nextResidue (d : Nat) (positive : 0 < d) (r : Fin d) : Fin d :=
  residue d positive (r.val + 1)

def scanLoop (d : Nat) (positive : 0 < d) (source quotient : K)
    (scanLabel : Λ) (emitterLabel : Fin d → Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ d) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.branch (fun state => decide ((nextResidue d positive state.1.2).val = 0))
        (.push quotient (fun _ => true)
          (.load (fun state => ((state.1.1, nextResidue d positive state.1.2), state.2))
            (.goto fun _ => scanLabel)))
        (.load (fun state => ((state.1.1, nextResidue d positive state.1.2), state.2))
          (.goto fun _ => scanLabel)))
      (.push source (fun _ => false) (.goto fun state => emitterLabel state.1.2)))

abbrev tapes (source quotient remainder : K) (base : K → List Bool)
    (input quotientWord remainderWord : List Bool) : K → List Bool :=
  MachineCopy.forkTapes source quotient remainder base input quotientWord remainderWord

def emitterWithFinish [Fintype σ] (d : Nat) (positive : 0 < d) (remainder : K)
    (exit : Option Λ) (finish : σ → Fin d → σ) (r : Fin d) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ d) :=
  pushWord remainder (List.replicate r.val true)
    (.load (fun state => ((finish state.1.1 r, residue d positive 0), none))
      (Reduction.MachineTransfer.exitAt remainder exit))

end MinUncutGames.Foundations.Complexity.MachineFixedDivMod

namespace MinUncutGames.Foundations.Complexity.MachineExpanderRow

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

inductive Tape
  | inputVertex | table | output
  | emitScratch | queryReverse | queryIndex
  | lookupOutput | lookupWork | lookupRestore
  | quotientFirst | quotientSecond | remainderFirst | remainderSecond
  deriving DecidableEq

def lookupTape : Fin 5 → Tape
  | ⟨0, _⟩ => .table
  | ⟨1, _⟩ => .queryIndex
  | ⟨2, _⟩ => .lookupWork
  | ⟨3, _⟩ => .lookupOutput
  | _ => .lookupRestore

def dirtyTape : Fin 6 → Tape
  | ⟨0, _⟩ => .queryIndex
  | ⟨1, _⟩ => .lookupOutput
  | ⟨2, _⟩ => .quotientFirst
  | ⟨3, _⟩ => .quotientSecond
  | ⟨4, _⟩ => .remainderFirst
  | _ => .remainderSecond

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

end MinUncutGames.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PoweringMachineRow

open _root_.Turing
open MachineFixedBlockMap
open MinUncutGames.Foundations.PCP

def inputSize (t S : Nat) : Nat := t * (4096 + (S + S))

def firstMatch {S : Nat} (mask : Fin S → Bool) : Option (Fin S) :=
  (List.ofFn id).find? mask

end MinUncutGames.Foundations.Complexity.PoweringMachineRow

end
section
namespace MinUncutGames.Foundations.Complexity.PoweringMachineLoop

open _root_.Turing

inductive HeaderTape
  | source | counter | vertices | darts
  deriving DecidableEq

inductive HeaderLabel
  | initialize_ | scan
  deriving DecidableEq

abbrev HeaderAlphabet (_ : HeaderTape) := Bool
abbrev HeaderState (σ : Type) := σ × Option Bool

def pushTrue {K Λ σ : Type} (destination : K) : Nat →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | 0, next => next
  | count + 1, next => pushTrue destination count (.push destination (fun _ => true) next)

def headerProgram {σ : Type} (B : Nat) :
    HeaderLabel → TM2.Stmt HeaderAlphabet HeaderLabel (HeaderState σ)
  | .initialize_ =>
      .push .counter (fun _ => false)
        (.push .vertices (fun _ => false)
          (.push .darts (fun _ => false)
            (.load (fun state => (state.1, none)) (.goto fun _ => .scan))))
  | .scan =>
      .pop .source (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.push .counter (fun _ => true)
            (.push .vertices (fun _ => true)
              (pushTrue .darts B
                (.load (fun state => (state.1, none)) (.goto fun _ => .scan)))))
          (.load (fun state => (state.1, none)) .halt))

end MinUncutGames.Foundations.Complexity.PoweringMachineLoop

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularMetadata

open _root_.Turing
open MinUncutGames.Foundations.PCP


inductive Extra
  | padding | level
  deriving DecidableEq

abbrev Tape := Fin 27 ⊕ Extra

variable {σ : Type}

def cloudView : Tape → Option MachineCloudPadding.Tape
  | .inl i => match i.val with
    | 0 => some .table
    | 2 => some .query
    | 4 => some .count
    | 9 => some .work
    | 10 => some .scratch
    | 11 => some .spare
    | 12 => some .fuel
    | 13 => some .product
    | _ => none
  | .inr .padding => some .power
  | .inr .level => some .level

structure Data where
  table : List Bool
  globalIndex : List Bool
  owner : List Bool
  localRank : List Bool
  count : List Bool
  offset : List Bool
  darts : List Bool
  rotor : List Bool
  output : List Bool
  padding : List Bool
  level : List Bool

def frame (data : Data) : Tape → List Bool
  | .inl i => match i.val with
    | 0 => data.table
    | 1 => data.globalIndex
    | 2 => data.owner
    | 3 => data.localRank
    | 4 => data.count
    | 5 => data.offset
    | 6 => data.darts
    | 7 => data.rotor
    | 8 => data.output
    | _ => []
  | .inr .padding => data.padding
  | .inr .level => data.level

@[simp] theorem frame_index (data : Data) :
    frame data (.inl 1) = data.globalIndex := rfl

@[simp] theorem frame_query_empty (data : Data) :
    frame data (.inl 9) = [] := rfl

end MinUncutGames.Foundations.Complexity.MachineRegularMetadata

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineExpanderTable

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

inductive ExtraTape
  | vertexCount | result
  deriving DecidableEq

inductive OuterLabel
  | initialize_ | vertexGuard | prepareRow | afterRow | reverseOutput | done
  deriving DecidableEq

abbrev Position (d : Nat) := Fin (rowFactor d)

end MinUncutGames.Foundations.Complexity.MachineExpanderTable

namespace MinUncutGames.Foundations.Complexity.MachineAlphabetTransport

open Turing.TM2

variable {K Λ σ : Type} {Γ Δ : K → Type}

def tapes (h : Γ = Δ) (source : ∀ k, List (Γ k)) : ∀ k, List (Δ k) := h ▸ source

def statement (h : Γ = Δ) (source : Stmt Γ Λ σ) : Stmt Δ Λ σ := h ▸ source

def configuration (h : Γ = Δ) (source : Cfg Γ Λ σ) : Cfg Δ Λ σ := h ▸ source

def program (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) : Λ → Stmt Δ Λ σ :=
  fun label => statement h (source label)

@[simp] theorem tapes_rfl (source : ∀ k, List (Γ k)) : tapes rfl source = source := rfl
@[simp] theorem statement_rfl (source : Stmt Γ Λ σ) : statement rfl source = source := rfl
@[simp] theorem configuration_rfl (source : Cfg Γ Λ σ) : configuration rfl source = source := rfl
@[simp] theorem program_rfl (source : Λ → Stmt Γ Λ σ) : program rfl source = source := rfl

@[simp] theorem program_apply (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) (label : Λ) :
    program h source label = statement h (source label) := rfl

@[simp] theorem statement_roundtrip (h : Γ = Δ) (source : Stmt Δ Λ σ) :
    statement h (statement h.symm source) = source := by cases h; rfl

@[simp] theorem statement_symm_roundtrip (h : Γ = Δ) (source : Stmt Γ Λ σ) :
    statement h.symm (statement h source) = source := by cases h; rfl

@[simp] theorem configuration_roundtrip (h : Γ = Δ) (source : Cfg Δ Λ σ) :
    configuration h (configuration h.symm source) = source := by cases h; rfl

@[simp] theorem configuration_symm_roundtrip (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    configuration h.symm (configuration h source) = source := by cases h; rfl

@[simp] theorem program_roundtrip (h : Γ = Δ) (source : Λ → Stmt Δ Λ σ) :
    program h (program h.symm source) = source := by cases h; rfl

@[simp] theorem program_symm_roundtrip (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) :
    program h.symm (program h source) = source := by cases h; rfl

@[simp] theorem tapes_roundtrip (h : Γ = Δ) (source : ∀ k, List (Δ k)) :
    tapes h (tapes h.symm source) = source := by cases h; rfl

@[simp] theorem tapes_symm_roundtrip (h : Γ = Δ) (source : ∀ k, List (Γ k)) :
    tapes h.symm (tapes h source) = source := by cases h; rfl

@[simp] theorem configuration_label (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    (configuration h source).l = source.l := by cases h; rfl

@[simp] theorem configuration_state (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    (configuration h source).var = source.var := by cases h; rfl

@[simp] theorem configuration_tapes (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    (configuration h source).stk = tapes h source.stk := by cases h; rfl

@[simp] theorem configuration_mk (h : Γ = Δ) (label : Option Λ) (state : σ)
    (source : ∀ k, List (Γ k)) :
    configuration h ⟨label, state, source⟩ = ⟨label, state, tapes h source⟩ := by cases h; rfl

@[simp] theorem map_configuration_rfl (source : Option (Cfg Γ Λ σ)) :
    source.map (configuration (rfl : Γ = Γ)) = source := by cases source <;> rfl

variable [DecidableEq K]

def executionInTime (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start finish budget) :
    StateTransition.EvalsToInTime (step (program h source)) (configuration h start)
      (finish.map (configuration h)) budget where
  steps := execution.steps
  evals_in_steps := by
    cases h
    simpa only [program_rfl, configuration_rfl, map_configuration_rfl]
      using execution.evals_in_steps
  steps_le_m := execution.steps_le_m

@[simp] theorem executionInTime_steps (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start finish budget) :
    (executionInTime h source execution).steps = execution.steps := rfl

def successfulExecutionInTime (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start finish : Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start (some finish) budget) :
    StateTransition.EvalsToInTime (step (program h source)) (configuration h start)
      (some (configuration h finish)) budget := executionInTime h source execution

@[simp] theorem successfulExecutionInTime_steps (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start finish : Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start (some finish) budget) :
    (successfulExecutionInTime h source execution).steps = execution.steps := rfl

end MinUncutGames.Foundations.Complexity.MachineAlphabetTransport

namespace MinUncutGames.Foundations.Complexity.MachineExpanderFamily

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

inductive ExtraTape
  | remainingLevel | currentSize | unaryScratch | tableReverse
  deriving DecidableEq

inductive AffinePhase
  | copyCount | multiplySize
  deriving DecidableEq

protected abbrev AffinePhase.enumList : List AffinePhase := [.copyCount, .multiplySize]

protected theorem AffinePhase.enumList_nodup : AffinePhase.enumList.Nodup := by decide

instance instFintypeAffinePhase : Fintype AffinePhase where
  elems := ⟨AffinePhase.enumList, AffinePhase.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive AffineLabel
  | seed | scan | restore
  deriving DecidableEq

protected abbrev AffineLabel.enumList : List AffineLabel := [.seed, .scan, .restore]

protected theorem AffineLabel.enumList_nodup : AffineLabel.enumList.Nodup := by decide

instance instFintypeAffineLabel : Fintype AffineLabel where
  elems := ⟨AffineLabel.enumList, AffineLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive OuterLabel
  | initialize_
  | levelGuard
  | affine (phase : AffinePhase) (label : AffineLabel)
  | clearOldTable | reverseResult | reverseTable | clearCurrentSize
  | drainInputVertex | drainVertexCount | done
  deriving DecidableEq, Fintype

open _root_.Turing

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

end MinUncutGames.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ExpanderTableEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.ExpanderTableEnumeration

open ExpanderTables ExpanderRowControl
open MinUncutGames.Foundations.Complexity

variable {v d : Nat}

theorem ofFn_cast {α : Type*} {n m : Nat} (h : n = m) (f : Fin m → α) :
    List.ofFn (fun i : Fin n => f (Fin.cast h i)) = List.ofFn f := by
  cases h
  rfl

end MinUncutGames.Foundations.PCP.ExpanderTableEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderFamilyCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachinePaddedExpanderFamily

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

abbrev fixedDegree := PCP.Expanders.baseDegree

open _root_.Turing
open MachineCloudPadding
open PCP.ExpanderTables PCP.ExpanderRowControl

end MinUncutGames.Foundations.Complexity.MachinePaddedExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularOriginalBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineRegularOwnerCleanup

open _root_.Turing

variable {LabelType : Type}

def sumDecidableEq {A B : Type} (left : DecidableEq A) (right : DecidableEq B) :
    DecidableEq (A ⊕ B)
  | .inl a, .inl b => match left a b with
      | .isTrue h => .isTrue (congrArg (Sum.inl : A → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inl.inj e))
  | .inr a, .inr b => match right a b with
      | .isTrue h => .isTrue (congrArg (Sum.inr : B → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inr.inj e))
  | .inl _, .inr _ => .isFalse (by intro h; cases h)
  | .inr _, .inl _ => .isFalse (by intro h; cases h)

end MinUncutGames.Foundations.Complexity.MachineRegularOwnerCleanup

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_InitialGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.InitialGraph

abbrev Label := Bool × Bool × Bool
@[simp] theorem card_label : Fintype.card Label = 8 := by
  simp [Label, Fintype.card_prod]

def variableValid (label : Label) : Bool :=
  decide (label.2.1 = false ∧ label.2.2 = false)

end MinUncutGames.Foundations.PCP.InitialGraph

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_AlphabetRetraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.AlphabetRetraction

variable {V E A B : Type*}

abbrev Label64 := QueryIncidence.Label 6

def decode64 (label : Label64) : InitialGraph.Label := (label 0, label 1, label 2)

def encode64 (label : InitialGraph.Label) : Label64 :=
  fun i => if i = 0 then label.1 else if i = 1 then label.2.1 else label.2.2

@[simp] theorem decode_encode64 (label : InitialGraph.Label) :
    decode64 (encode64 label) = label := by
  rcases label with ⟨a, b, c⟩
  rfl

end MinUncutGames.Foundations.PCP.AlphabetRetraction

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_RawInitialTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.RawInitialTables

open GraphTables

def unitOrder : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := by fin_cases i; rfl

def binaryOrder (n : Nat) : (Fin n → Bool) ≃ Fin (2 ^ n) where
  toFun bits := (MinUncutGames.Integration.BinaryCoordinates.pack bits).toFin
  invFun index := MinUncutGames.Integration.BinaryCoordinates.unpack (BitVec.ofFin index)
  left_inv bits := MinUncutGames.Integration.BinaryCoordinates.unpack_pack bits
  right_inv index := by
    change (MinUncutGames.Integration.BinaryCoordinates.pack
      (MinUncutGames.Integration.BinaryCoordinates.unpack (BitVec.ofFin index))).toFin = index
    rw [MinUncutGames.Integration.BinaryCoordinates.pack_unpack]

end MinUncutGames.Foundations.PCP.RawInitialTables

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_FinalBooleanVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.FinalBooleanVerifier

abbrev Label := Fin 6 → Bool

variable {V E : Type*} {n m : Nat}

def bitIndex (vertices : V ≃ Fin n) (v : V) (j : Fin 6) : Fin (n * 6) :=
  finProdFinEquiv (vertices v, j)

def labelsOfBits (vertices : V ≃ Fin n) (assignment : Fin (n * 6) → Bool) : V → Label :=
  fun v j => assignment (bitIndex vertices v j)

def bitsOfLabels (vertices : V ≃ Fin n) (labeling : V → Label) : Fin (n * 6) → Bool :=
  fun k =>
    let pair : Fin n × Fin 6 := finProdFinEquiv.symm k
    labeling (vertices.symm pair.1) pair.2

@[simp] theorem labelsOfBits_bitsOfLabels (vertices : V ≃ Fin n) (labeling : V → Label) :
    labelsOfBits vertices (bitsOfLabels vertices labeling) = labeling := by
  funext v j
  simp only [labelsOfBits, bitsOfLabels, bitIndex, Equiv.symm_apply_apply]

end MinUncutGames.Foundations.PCP.FinalBooleanVerifier

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_FinalCNFPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.FinalCNFPattern

open PCP
open scoped BigOperators

abbrev Label := FinalBooleanVerifier.Label

end MinUncutGames.Foundations.Complexity.FinalCNFPattern

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_RawInitialPredicate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.RawInitialRows

open GraphTables RawInitialTables

abbrev Signs := Bool × Bool × Bool
abbrev Names := Nat × Nat × Nat

end MinUncutGames.Foundations.PCP.RawInitialRows

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineInitialHeaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.RawInitialMachineModel

open _root_.Turing Complexity Hastad

inductive Tape
  | input | «variables» | counter | index | field (slot : Fin 6)
  | scratch | reversed | output
  deriving DecidableEq, Fintype

def nameField (slot : Fin 3) : Fin 6 := ⟨2 * slot.val, by omega⟩

end MinUncutGames.Foundations.PCP.RawInitialMachineModel

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RawInitialMachineFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.FinalCNFMachine

open _root_.Turing
open PCP

namespace Program

open PCP.AlphabetTable

inductive Tape
  | input | output | accumulator | scratch | vertices | darts | tail | head | rowIndex
  | archive | reverseIndex | scanWork | indexWork
  deriving DecidableEq

def values (vertices darts tail head row : Nat) : Fin 5 → Nat :=
  Fin.cases vertices (Fin.cases darts (Fin.cases tail (Fin.cases head (fun _ => row))))

def headRoles : Fin 6 → Tape :=
  Fin.cases .archive (Fin.cases .reverseIndex (Fin.cases .scanWork
    (Fin.cases .indexWork (Fin.cases .head (fun _ => .scratch)))))

end Program

end MinUncutGames.Foundations.Complexity.FinalCNFMachine

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_FinalCNFHeader
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.FinalCNFMachine.Program

open _root_.Turing
open PCP.AlphabetTable

def headerFrame (input archive vertices darts rowIndex tail head accumulator : List Bool) :
    Tape → List Bool
  | .input => input
  | .archive => archive
  | .vertices => vertices
  | .darts => darts
  | .rowIndex => rowIndex
  | .tail => tail
  | .head => head
  | .accumulator => accumulator
  | _ => []

open _root_.Turing PCP PCP.AlphabetTable

end MinUncutGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineRotor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineRotor

open _root_.Turing
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool

def reverseRole (i : Fin 5) : Fin 7 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else 6

def endpointRole (i : Fin 5) : Fin 7 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 5 else 6

def reverseTapes (tape : Fin 7 → K) : Fin 5 → K := tape ∘ reverseRole
def endpointTapes (tape : Fin 7 → K) : Fin 5 → K := tape ∘ endpointRole

inductive Label
  | reverse (l : MachineAffineLookup.Label)
  | endpoint (l : MachineAffineLookup.Label)
  deriving DecidableEq, Fintype

end MinUncutGames.Foundations.Complexity.PoweringMachineRotor

namespace MinUncutGames.Foundations.Complexity.PoweringMachineWord

open _root_.Turing
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev Tape (t : Nat) := Fin 6 ⊕ Fin (t + 1)

def first (t : Nat) : Fin (t + 1) := ⟨0, by omega⟩

def shift (t : Nat) : Tape t → Tape (t + 1) := Sum.map id Fin.succ

def rotorRole (t : Nat) (i : Fin 7) : Tape (t + 1) :=
  if i = 0 then .inl 0 else if i = 1 then .inr (first (t + 1)) else
  if i = 2 then .inl 1 else if i = 3 then .inl 2 else
  if i = 4 then .inl 3 else if i = 5 then .inr (first t).succ else .inl 4

def Label : Nat → Type
  | 0 => MachineUnaryAffineAt.Label
  | t + 1 => PoweringMachineRotor.Label ⊕ Label t

def entry : (t : Nat) → Label t
  | 0 => .seed
  | _ + 1 => .inl (.reverse .seed)

end MinUncutGames.Foundations.Complexity.PoweringMachineWord

namespace MinUncutGames.Foundations.Complexity.PoweringMachineTapes

abbrev Tape (max : Nat) := Fin 11 ⊕ Fin max

def table (max : Nat) : Tape max := .inl 0
def start (max : Nat) : Tape max := .inl 1
def query (max : Nat) : Tape max := .inl 2
def scan (max : Nat) : Tape max := .inl 3
def reverse (max : Nat) : Tape max := .inl 4
def scratch (max : Nat) : Tape max := .inl 5
def leftEndpoint (max : Nat) : Tape max := .inl 6
def rightEndpoint (max : Nat) : Tape max := .inl 7
def leftCopy (max : Nat) : Tape max := .inl 8
def rightCopy (max : Nat) : Tape max := .inl 9
def rowOutput (max : Nat) : Tape max := .inl 10

def endpoint (max : Nat) (target : Bool) : Tape max :=
  if target then rightEndpoint max else leftEndpoint max

@[simp] theorem endpoint_false (max : Nat) : endpoint max false = leftEndpoint max := rfl
@[simp] theorem endpoint_true (max : Nat) : endpoint max true = rightEndpoint max := rfl

def wordSharedRole (target : Bool) (i : Fin 6) : Fin 11 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else
  if i = 3 then 4 else if i = 4 then 5 else if target then 7 else 6

def trajectoryPlacement {t max : Nat} (h : t ≤ max) : Fin (t + 1) → Tape max :=
  Fin.cases (start max) (fun i => .inr (Fin.castLE h i))

def wordPlacement {t max : Nat} (h : t ≤ max) (target : Bool) :
    PoweringMachineWord.Tape t → Tape max
  | .inl i => .inl (wordSharedRole target i)
  | .inr i => trajectoryPlacement h i

@[simp] theorem wordPlacement_inl_zero {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 0) = table max := rfl
@[simp] theorem wordPlacement_inl_one {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 1) = query max := rfl
@[simp] theorem wordPlacement_inl_two {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 2) = scan max := rfl
@[simp] theorem wordPlacement_inl_three {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 3) = reverse max := rfl
@[simp] theorem wordPlacement_inl_four {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 4) = scratch max := rfl
@[simp] theorem wordPlacement_inl_five {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 5) = endpoint max target := by cases target <;> rfl
@[simp] theorem wordPlacement_first {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inr (PoweringMachineWord.first t)) = start max := rfl
@[simp] theorem wordPlacement_succ {t max : Nat} (h : t ≤ max) (target : Bool) (i : Fin t) :
    wordPlacement h target (.inr i.succ) = .inr (Fin.castLE h i) := rfl

def relationPlacement (max : Nat) (i : Fin 6) : Tape max :=
  .inl (if i = 0 then 6 else if i = 1 then 0 else if i = 2 then 2 else
    if i = 3 then 3 else if i = 4 then 10 else 5)

@[simp] theorem relationPlacement_zero (max : Nat) : relationPlacement max 0 = leftEndpoint max := rfl
@[simp] theorem relationPlacement_one (max : Nat) : relationPlacement max 1 = table max := rfl
@[simp] theorem relationPlacement_two (max : Nat) : relationPlacement max 2 = query max := rfl
@[simp] theorem relationPlacement_three (max : Nat) : relationPlacement max 3 = scan max := rfl
@[simp] theorem relationPlacement_four (max : Nat) : relationPlacement max 4 = rowOutput max := rfl
@[simp] theorem relationPlacement_five (max : Nat) : relationPlacement max 5 = scratch max := rfl

def equalityPlacement (max : Nat) (i : Fin 6) : Tape max :=
  .inl (if i = 0 then 6 else if i = 1 then 7 else if i = 2 then 8 else
    if i = 3 then 9 else if i = 4 then 5 else 10)

@[simp] theorem equalityPlacement_zero (max : Nat) : equalityPlacement max 0 = leftEndpoint max := rfl
@[simp] theorem equalityPlacement_one (max : Nat) : equalityPlacement max 1 = rightEndpoint max := rfl
@[simp] theorem equalityPlacement_two (max : Nat) : equalityPlacement max 2 = leftCopy max := rfl
@[simp] theorem equalityPlacement_three (max : Nat) : equalityPlacement max 3 = rightCopy max := rfl
@[simp] theorem equalityPlacement_four (max : Nat) : equalityPlacement max 4 = scratch max := rfl
@[simp] theorem equalityPlacement_five (max : Nat) : equalityPlacement max 5 = rowOutput max := rfl

end MinUncutGames.Foundations.Complexity.PoweringMachineTapes

namespace MinUncutGames.Foundations.Complexity.PoweringMachineInitialize

open _root_.Turing
open PoweringMachineLoop

abbrev ExtraTape (max : Nat) := PoweringMachineTapes.Tape max ⊕ Unit
abbrev GlobalTape (max : Nat) := HeaderTape ⊕ ExtraTape max
abbrev Label := HeaderLabel ⊕ MachineUnaryAffineAt.Label

def finalOutput (max : Nat) : GlobalTape max := .inr (.inr ())

def commonPlacement (max : Nat) (tape : PoweringMachineTapes.Tape max) : GlobalTape max :=
  if tape = PoweringMachineTapes.start max then .inl .counter else .inr (.inl tape)

@[simp] theorem commonPlacement_start (max : Nat) :
    commonPlacement max (PoweringMachineTapes.start max) = .inl .counter := by
  simp [commonPlacement]

@[simp] theorem commonPlacement_table (max : Nat) :
    commonPlacement max (PoweringMachineTapes.table max) =
      .inr (.inl (PoweringMachineTapes.table max)) := by
  simp [commonPlacement, PoweringMachineTapes.table, PoweringMachineTapes.start]

@[simp] theorem commonPlacement_scratch (max : Nat) :
    commonPlacement max (PoweringMachineTapes.scratch max) =
      .inr (.inl (PoweringMachineTapes.scratch max)) := by
  simp [commonPlacement, PoweringMachineTapes.scratch, PoweringMachineTapes.start]

@[simp] theorem commonPlacement_rowOutput (max : Nat) :
    commonPlacement max (PoweringMachineTapes.rowOutput max) =
      .inr (.inl (PoweringMachineTapes.rowOutput max)) := by
  simp [commonPlacement, PoweringMachineTapes.rowOutput, PoweringMachineTapes.start]

def castStatement {K Λ σ : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (q : TM2.Stmt Γ Λ σ) : TM2.Stmt Δ Λ σ := h ▸ q

theorem boolAlphabet_eq (max : Nat) :
    MachineEmbedding.Alphabet HeaderAlphabet (fun _ : ExtraTape max => Bool) =
      (fun _ : GlobalTape max => Bool) := by
  funext tape
  cases tape <;> rfl

def mergeTapes {max : Nat} (header : HeaderTape → List Bool)
    (extra : ExtraTape max → List Bool) : GlobalTape max → List Bool
  | .inl k => header k
  | .inr e => extra e

end MinUncutGames.Foundations.Complexity.PoweringMachineInitialize

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_PoweringGlobalEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PoweringGlobalEnumeration

open PoweringMachineLoop PoweringMachineInitialize

def unitTapeEquiv : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv i := (Fin.eq_zero i).symm

def sharedTapeEquiv (max : Nat) : PoweringMachineTapes.Tape max ≃ Fin (11 + max) :=
  finSumFinEquiv

end MinUncutGames.Foundations.Complexity.PoweringGlobalEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineRelation

open _root_.Turing
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool

end MinUncutGames.Foundations.Complexity.PoweringMachineRelation

namespace MinUncutGames.Foundations.Complexity.PoweringMachineRelationField

open _root_.Turing
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {n d max : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev Label (path : List (Fin d)) := PoweringMachineWord.Label path.length ⊕ MachineAffineLookup.Label

def lookupTapes (placement : PoweringMachineTapes.Tape max → K) (i : Fin 5) : K :=
  placement (PoweringMachineTapes.relationPlacement max i.succ)

end MinUncutGames.Foundations.Complexity.PoweringMachineRelationField

namespace MinUncutGames.Foundations.Complexity.PoweringMachineEqualityField

open _root_.Turing
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {max l r n d : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev Tape := PoweringMachineTapes.Tape
abbrev Label (l r : Nat) :=
  PoweringMachineWord.Label l ⊕ PoweringMachineWord.Label r ⊕ MachineUnaryEqualityBit.Label

def entry (l r : Nat) : Label l r := .inl (PoweringMachineWord.entry l)

end MinUncutGames.Foundations.Complexity.PoweringMachineEqualityField

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringRowData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringFieldPlan

open PoweringWalks PoweringLabels PoweringAddresses
open MinUncutGames.Foundations.Complexity PoweringMachineRow

variable {V D : Type*}

def tailPorts : (n : Nat) → (Fin (n + 1) → D) → Fin (n + 1) → List D
  | 0, _, _ => []
  | n + 1, p, k => Fin.cases [] (fun j => p 0 :: tailPorts n (fun i => p i.succ) j) k

theorem tailPorts_length : ∀ (n : Nat) (p : Fin (n + 1) → D) (k : Fin (n + 1)),
    (tailPorts n p k).length = k.val := by
  intro n
  induction n with
  | zero => intro p k; have hk := Fin.eq_zero k; subst k; rfl
  | succ n ih =>
      intro p k
      refine Fin.cases rfl (fun j => ?_) k
      simp only [tailPorts, Fin.cases_succ, List.length_cons, ih, Fin.val_succ]

def headPorts (n : Nat) (p : Fin (n + 1) → D) (k : Fin (n + 1)) : List D :=
  tailPorts n p k ++ [p k]

inductive Instruction (d : Nat) where
  | relation (ports : List (Fin d)) (port : Fin d) (left right : Fin 64)
  | equal (left right : List (Fin d))

def Instruction.radius {d : Nat} : Instruction d → Nat
  | .relation ports _ _ _ => ports.length
  | .equal left right => max left.length right.length

end MinUncutGames.Foundations.PCP.PoweringFieldPlan

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineField

open _root_.Turing PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

abbrev Tape := PoweringMachineTapes.Tape

def Label : Instruction d → Type
  | .relation path _ _ _ => PoweringMachineRelationField.Label path
  | .equal left right => PoweringMachineEqualityField.Label left.length right.length

def entry : (op : Instruction d) → Label op
  | .relation path _ _ _ => .inl (PoweringMachineWord.entry path.length)
  | .equal left right => PoweringMachineEqualityField.entry left.length right.length

end MinUncutGames.Foundations.Complexity.PoweringMachineField

namespace MinUncutGames.Foundations.Complexity.PoweringMachinePlan

open _root_.Turing PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

abbrev Command (d max : Nat) := {op : Instruction d // op.radius ≤ max}
abbrev LocalLabel (op : Command d max) := PoweringMachineField.Label op.val
abbrev Label (commands : List (Command d max)) := MachineFiniteSequence.Label LocalLabel commands

end MinUncutGames.Foundations.Complexity.PoweringMachinePlan

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringRowHeaderSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringRowHeaderSemantics

open PoweringWalks PoweringEnumeration
open MinUncutGames.Foundations.Complexity

variable {vertices d : Nat}

def blockSize (d n : Nat) : Nat := 2 * d ^ (n + 1)

def reverseOffset (d n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  2 * (wordEquiv d (n + 1) ports).val + (if direction then 0 else 1)

end MinUncutGames.Foundations.PCP.PoweringRowHeaderSemantics

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineRowHeaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineRowHeaders

open _root_.Turing
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

def headerPlacement {t max : Nat} (h : t ≤ max) : PoweringMachineWord.Tape t → Tape max :=
  (Equiv.swap (leftEndpoint max) (rowOutput max)) ∘ wordPlacement h false

@[simp] theorem headerPlacement_table {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 0) = table max := by
  simp [headerPlacement, table, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_query {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 1) = query max := by
  simp [headerPlacement, query, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_scan {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 2) = scan max := by
  simp [headerPlacement, scan, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_reverse {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 3) = reverse max := by
  simp [headerPlacement, reverse, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_scratch {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 4) = scratch max := by
  simp [headerPlacement, scratch, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_output {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 5) = rowOutput max := by
  simp [headerPlacement]

abbrev Label (n : Nat) := MachineUnaryAffineAt.Label ⊕
  (MachineUnaryAffineAt.Label ⊕ PoweringMachineWord.Label (n + 1))

def entry (n : Nat) : Label n := .inl .seed

def tailEntry (n : Nat) (direction : Bool) : Label n :=
  if direction then .inr (.inr (PoweringMachineWord.entry (n + 1))) else .inr (.inl .seed)

end MinUncutGames.Foundations.Complexity.PoweringMachineRowHeaders

namespace MinUncutGames.Foundations.Complexity.PoweringMachineRowBody

open _root_.Turing PCP
open MachineFixedBlockMap

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

abbrev capacity (n : Nat) := 2 * (n + 1)

end MinUncutGames.Foundations.Complexity.PoweringMachineRowBody

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringTableLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringTableLayout

open MinUncutGames.Foundations.Complexity
open PoweringTables PoweringEnumeration

def blockSize (d n : Nat) : Nat := 2 * d ^ (n + 1)

end MinUncutGames.Foundations.PCP.PoweringTableLayout

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineFinish

open _root_.Turing

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

abbrev Alphabet (_ : K) := Bool

abbrev Label (enumeration : Fin N ≃ K) (output : K) :=
  MachineUnaryAffineAt.Label ⊕ (MachineUnaryAffineAt.Label ⊕
    MachineDrainMany.Label (MachineDrainMany.workTapes enumeration output))

end MinUncutGames.Foundations.Complexity.PoweringMachineFinish

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_LiteralLocalTemplates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed
lemma drop_head_append {α : Type} [Inhabited α] (xs ys : List α) (i : ℕ) (hi : i<xs.length) :
    ((xs++ys).drop i).headI=(xs.drop i).headI := by
  rw [List.drop_append_of_le_length hi.le,List.drop_eq_getElem_cons hi]
  rfl

end MinUncut.Costed

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_CanonicalSamplerGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace MinUncut.PathRealization

def listOutput {N : ℕ} (ds : List (Demand (Fin N))) (k : ℕ) (hk : 1≤k) : Output :=
  canonicalOutput (fun i : Fin ds.length => ds[i]) k hk

end MinUncut.PathRealization

end
namespace MinUncut.Costed.GraphRegisters
open MinUncut.PathRealization

lemma finRange_vals (V : ℕ) : (List.finRange V).map Fin.val=List.range V := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

def canonicalTable {N : ℕ} (ds : List (Demand (Fin N))) : List Bool :=
  (List.finRange (N+ds.length*3)).flatMap fun u=>
    (List.finRange (N+ds.length*3)).map fun v=>canonicalAdjacent (fun d:Fin ds.length=>ds[d]) u v

lemma listOutput_bits {N : ℕ} (ds : List (Demand (Fin N))) (k : ℕ) (hk : 1≤k) :
    (listOutput ds k hk).bits=MinUncutGames.BinaryEncoding.nameBits (N+ds.length*3)++
      canonicalTable ds++MinUncutGames.BinaryEncoding.nameBits k := rfl

end MinUncut.Costed.GraphRegisters

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_FiberPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Costed.FiberPrefix
open Turing.ToPartrec Polynomial
lemma scalar_code {f : ℕ → ℕ} (hf : Computable f) :
    ∃c : Code,∀K,[f K]∈c.eval [K] := by
  obtain ⟨c,hc⟩:=Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf)
  refine ⟨c,fun K=>?_⟩
  have h:=hc ⟨[K],rfl⟩
  rw [h]
  change [f K]∈Part.some [f K]
  exact Part.mem_some _
lemma scalar₂_code {f : ℕ → ℕ → ℕ} (hf : Computable₂ f) :
    ∃c : Code,∀K i,[f K i]∈c.eval [K,i] := by
  obtain ⟨c,hc⟩:=Code.exists_code (Nat.Partrec'.part_iff₂.mpr hf.partrec₂)
  refine ⟨c,fun K i=>?_⟩
  have h:=hc ⟨[K,i],rfl⟩
  rw [h]
  change [f K i]∈Part.some [f K i]
  exact Part.mem_some _

def args : Code := .cons (.comp .head .tail) .head

def step (cell : Code) : Code :=
  .cons .succ (.cons (.comp .head .tail) (.cons (.comp cell args) (.comp .tail .tail)))

def state (f : ℕ → List ℕ) (K i : ℕ) (v : List ℕ) : List ℕ :=
  i::K::((f K).reverse.take i).reverse++v
lemma state_step (f : ℕ → List ℕ) (K i : ℕ) (v : List ℕ) (hi : i<(f K).length) :
    state f K (i+1) v=(i+1)::K::((f K).reverse[i]?.getD 0)::((f K).reverse.take i).reverse++v := by
  have hlen:i<(f K).reverse.length:=by simpa using hi
  simp only [state,List.take_succ_eq_append_getElem hlen,List.reverse_append,List.reverse_singleton,
    List.singleton_append,List.getElem?_eq_getElem hlen,Option.getD_some]

def init (len : Code) : Code :=
  .cons (.comp len .head) (.cons .zero (.cons .head .id))
def transition (f : ℕ → List ℕ) (v : List ℕ) : List ℕ :=
  (v.headI+1)::(v.tail.headI)::((f v.tail.headI).reverse[v.headI]?.getD 0)::v.drop 2
lemma iterate_state (f : ℕ → List ℕ) (K i : ℕ) (v : List ℕ) (hi : i≤(f K).length) :
    (transition f)^[i] (0::K::v)=state f K i v := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply',ih (by omega),state_step f K i v (by omega)]
    rfl
end MinUncut.Costed.FiberPrefix

end

namespace MinUncut.Costed.UnaryWords
open Turing.ToPartrec Polynomial

def symbol (v : List ℕ) : ℕ := (v.drop (3+(v.drop 2).headI+v.headI)).headI

def step (v : List ℕ) : List ℕ :=
  if symbol v=1 then
    (v.headI+1)::0::((v.drop 2).headI+1)::(v.drop 1).headI::v.drop 3
  else (v.headI+1)::((v.drop 1).headI+1)::(v.drop 2).headI::v.drop 3

def finish (v : List ℕ) : List ℕ := (v.drop 2).headI::v.drop 3

def state (i c : ℕ) (acc input : List ℕ) : List ℕ := i::c::acc.length::acc++input

lemma symbol_state (i c : ℕ) (acc input : List ℕ) :
    symbol (state i c acc input)=(input.drop i).headI := by
  simp only [symbol,state,List.cons_append,List.drop_succ_cons,List.drop_zero,List.headI_cons]
  rw [show 3+acc.length+i=(acc.length+i)+3 by omega]
  simp only [List.drop_succ_cons]
  rw [show acc.length+i=acc.length+i from rfl,←List.drop_drop,List.drop_left]
lemma step_state (i c : ℕ) (acc input : List ℕ) :
    step (state i c acc input)=if (input.drop i).headI=1 then state (i+1) 0 (c::acc) input
      else state (i+1) (c+1) acc input := by
  unfold step
  rw [symbol_state]
  split_ifs <;> rfl

def count : List ℕ → ℕ
  | [] => 0
  | a::as => if a=0 then 0 else count as+1

def decodeAux (c : ℕ) (acc : List ℕ) : List ℕ → List ℕ
  | [] => acc
  | a::as => if a=0 then acc else if a=1 then decodeAux 0 (c::acc) as else decodeAux (c+1) acc as

def lastCounter (c : ℕ) : List ℕ → ℕ
  | [] => c
  | a::as => if a=0 then c else if a=1 then lastCounter 0 as else lastCounter (c+1) as

lemma count_le (v : List ℕ) : count v≤v.length := by
  induction v with
  | nil => rfl
  | cons a as ih => simp only [count,List.length_cons]; split_ifs <;> omega

lemma count_drop_head (v : List ℕ) : (v.drop (count v)).headI=0 := by
  induction v with
  | nil => rfl
  | cons a as ih =>
    simp only [count]
    split_ifs with h
    · simpa only [List.drop_zero,List.headI_cons] using h
    · simpa only [List.drop_succ_cons] using ih

lemma count_drop_ne (v : List ℕ) (i : ℕ) (hi : i < count v) : (v.drop i).headI≠0 := by
  induction v generalizing i with
  | nil => simp only [count] at hi; omega
  | cons a as ih =>
    simp only [count] at hi
    by_cases h : a=0
    · simp only [h,ite_true] at hi; omega
    · simp only [h,ite_false] at hi
      cases i with
      | zero => simpa only [List.drop_zero,List.headI_cons] using h
      | succ i => exact ih i (by omega)

lemma iterate_shape (input : List ℕ) (i : ℕ) :
    ∃ c acc,step^[i] (state 0 0 [] input)=state i c acc input := by
  induction i with
  | zero => exact ⟨0,[],rfl⟩
  | succ i ih =>
    obtain ⟨c,acc,he⟩:=ih
    rw [Function.iterate_succ_apply',he,step_state]
    split_ifs
    · exact ⟨0,c::acc,rfl⟩
    · exact ⟨c+1,acc,rfl⟩

lemma symbol_iterate (input : List ℕ) (i : ℕ) :
    symbol (step^[i] (state 0 0 [] input))=(input.drop i).headI := by
  obtain ⟨c,acc,he⟩:=iterate_shape input i
  rw [he,symbol_state]

def parsed (v : List ℕ) : List ℕ := (decodeAux 0 [] v).length::decodeAux 0 [] v++v

noncomputable def parseSize : Polynomial ℕ := C 20*(X+1)^2
end MinUncut.Costed.UnaryWords

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_TM2Costed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Costed

open Function

def Steps {α : Type*} (f : α → Option α) (n : ℕ) (a b : α) : Prop :=
  (fun x : Option α => x.bind f)^[n] (some a) = some b

@[simp] theorem steps_zero {α : Type*} (f : α → Option α) (a b : α) :
    Steps f 0 a b ↔ a = b := by
  simp [Steps]

theorem steps_one {α : Type*} {f : α → Option α} {a b : α}
    (h : f a = some b) : Steps f 1 a b := h

theorem steps_head {α : Type*} {f : α → Option α} {n : ℕ} {a b c : α}
    (h : f a = some b) (h' : Steps f n b c) : Steps f (n + 1) a c := by
  simpa only [Steps, Function.iterate_succ_apply, Option.bind_some, h] using h'

theorem steps_trans {α : Type*} {f : α → Option α} {m n : ℕ} {a b c : α}
    (h : Steps f m a b) (h' : Steps f n b c) : Steps f (m + n) a c := by
  dsimp [Steps] at *
  rw [Nat.add_comm m n, Function.iterate_add_apply, h, h']

def steps_timed {α : Type*} {f : α → Option α} {n m : ℕ} {a b : α}
    (h : Steps f n a b) (hn : n ≤ m) : StateTransition.EvalsToInTime f a (some b) m :=
  ⟨⟨n, h⟩, hn⟩

def Within {α : Type*} (f : α → Option α) (n : ℕ) (a b : α) : Prop :=
  ∃ t, t ≤ n ∧ Steps f t a b

theorem Steps.within {α : Type*} {f : α → Option α} {n : ℕ} {a b : α}
    (h : Steps f n a b) : Within f n a b := ⟨n, le_rfl, h⟩

theorem Within.mono {α : Type*} {f : α → Option α} {m n : ℕ} {a b : α}
    (h : Within f m a b) (hmn : m ≤ n) : Within f n a b := by
  obtain ⟨t, ht, he⟩ := h
  exact ⟨t, ht.trans hmn, he⟩

theorem Within.trans {α : Type*} {f : α → Option α} {m n : ℕ} {a b c : α}
    (h : Within f m a b) (h' : Within f n b c) : Within f (m + n) a c := by
  obtain ⟨t, ht, he⟩ := h
  obtain ⟨t', ht', he'⟩ := h'
  exact ⟨t+t', Nat.add_le_add ht ht', steps_trans he he'⟩

theorem Within.head {α : Type*} {f : α → Option α} {n : ℕ} {a b c : α}
    (h : f a = some b) (h' : Within f n b c) : Within f (n + 1) a c := by
  obtain ⟨t, ht, he⟩ := h'
  exact ⟨t+1, Nat.add_le_add_right ht 1, steps_head h he⟩

theorem within_one {α : Type*} {f : α → Option α} {a b : α}
    (h : f a = some b) : Within f 1 a b := (steps_one h).within

end MinUncut.Costed

namespace Turing.PartrecToTM2
open scoped _root_.Turing _root_.Turing.PartrecToTM2
open Function
open MinUncut.Costed
open _root_.Turing.PartrecToTM2.K'

theorem move_steps {p k₁ k₂ q s L₁ o L₂} {S : _root_.Turing.PartrecToTM2.K' → List _root_.Turing.PartrecToTM2.Γ'} (h₁ : k₁ ≠ k₂)
    (e : _root_.Turing.PartrecToTM2.splitAtPred p (S k₁) = (L₁, o, L₂)) :
    Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (L₁.length + 1) ⟨some (_root_.Turing.PartrecToTM2.Λ'.move p k₁ k₂ q), s, S⟩
      ⟨some q, o, update (update S k₁ L₂) k₂ (L₁.reverseAux (S k₂))⟩ := by
  induction L₁ generalizing S s with
  | nil =>
    rw [(_ : [].reverseAux _ = _), Function.update_eq_self]
    swap
    · rw [Function.update_of_ne h₁.symm, List.reverseAux_nil]
    apply steps_one
    simp only [_root_.Turing.TM2.step, _root_.Turing.PartrecToTM2.tr_move, _root_.Turing.PartrecToTM2.pop', _root_.Turing.TM2.stepAux, Option.elim]
    grind [_root_.Turing.PartrecToTM2.splitAtPred.eq_def]
  | cons a L₁ IH =>
    refine steps_head rfl ?_
    rw [_root_.Turing.PartrecToTM2.tr]; simp only [_root_.Turing.PartrecToTM2.pop', Option.elim, _root_.Turing.TM2.stepAux, _root_.Turing.PartrecToTM2.push']
    rcases e₁ : S k₁ with - | ⟨a', Sk⟩ <;> rw [e₁, _root_.Turing.PartrecToTM2.splitAtPred] at e
    · cases e
    cases e₂ : p a' <;> simp only [e₂, cond] at e
    swap
    · cases e
    rcases e₃ : _root_.Turing.PartrecToTM2.splitAtPred p Sk with ⟨_, _, _⟩
    rw [e₃] at e
    cases e
    simp only [List.head?_cons, e₂, List.tail_cons, Bool.cond_false]
    convert! @IH _ (update (update S k₁ Sk) k₂ (a :: S k₂)) _ using 2 <;>
      simp [Function.update_of_ne, h₁, h₁.symm, e₃, List.reverseAux]
    simp [Function.update_comm h₁.symm]

theorem clear_steps {p k q s L₁ o L₂} {S : _root_.Turing.PartrecToTM2.K' → List _root_.Turing.PartrecToTM2.Γ'}
    (e : _root_.Turing.PartrecToTM2.splitAtPred p (S k) = (L₁, o, L₂)) :
    Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (L₁.length + 1) ⟨some (_root_.Turing.PartrecToTM2.Λ'.clear p k q), s, S⟩
      ⟨some q, o, update S k L₂⟩ := by
  induction L₁ generalizing S s with
  | nil =>
    apply steps_one
    simp only [_root_.Turing.TM2.step, _root_.Turing.PartrecToTM2.tr_clear, _root_.Turing.PartrecToTM2.pop', _root_.Turing.TM2.stepAux]
    grind [_root_.Turing.PartrecToTM2.splitAtPred.eq_def]
  | cons a L₁ IH =>
    refine steps_head rfl ?_
    rw [_root_.Turing.PartrecToTM2.tr]; simp only [_root_.Turing.PartrecToTM2.pop', _root_.Turing.TM2.stepAux, Option.elim]
    rcases e₁ : S k with - | ⟨a', Sk⟩ <;> rw [e₁, _root_.Turing.PartrecToTM2.splitAtPred] at e
    · cases e
    cases e₂ : p a' <;> simp only [e₂, cond] at e
    swap
    · cases e
    rcases e₃ : _root_.Turing.PartrecToTM2.splitAtPred p Sk with ⟨_, _, _⟩
    rw [e₃] at e
    cases e
    simp only [List.head?_cons, e₂, List.tail_cons, Bool.cond_false]
    convert! @IH _ (update S k Sk) _ using 2 <;> simp [e₃]

theorem unrev_steps {q s} {S : _root_.Turing.PartrecToTM2.K' → List _root_.Turing.PartrecToTM2.Γ'} :
    Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) ((S rev).length + 1) ⟨some (_root_.Turing.PartrecToTM2.unrev q), s, S⟩
      ⟨some q, none, update (update S rev []) main (List.reverseAux (S rev) (S main))⟩ :=
  move_steps (by decide) (_root_.Turing.PartrecToTM2.splitAtPred_false _)

theorem copy_steps (q s a b c d) :
    Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (b.length + 1) ⟨some (_root_.Turing.PartrecToTM2.Λ'.copy q), s, _root_.Turing.PartrecToTM2.K'.elim a b c d⟩
      ⟨some q, none, _root_.Turing.PartrecToTM2.K'.elim (List.reverseAux b a) [] c (List.reverseAux b d)⟩ := by
  induction b generalizing a d s with
  | nil =>
    apply steps_one
    simp [_root_.Turing.TM2.step, _root_.Turing.PartrecToTM2.tr, _root_.Turing.PartrecToTM2.pop', _root_.Turing.TM2.stepAux]
  | cons x b IH =>
    refine steps_head rfl ?_
    rw [_root_.Turing.PartrecToTM2.tr]
    simp only [_root_.Turing.TM2.stepAux, elim_rev, List.head?_cons, Option.isSome_some,
      List.tail_cons, elim_update_rev, elim_main, elim_update_main,
      elim_stack, elim_update_stack, Bool.cond_true, List.reverseAux_cons, _root_.Turing.PartrecToTM2.pop', _root_.Turing.PartrecToTM2.push']
    exact IH _ _ _

theorem move₂_steps {p k₁ k₂ q s L₁ o L₂} {S : _root_.Turing.PartrecToTM2.K' → List _root_.Turing.PartrecToTM2.Γ'}
    (h₁ : k₁ ≠ rev ∧ k₂ ≠ rev ∧ k₁ ≠ k₂) (h₂ : S rev = [])
    (e : _root_.Turing.PartrecToTM2.splitAtPred p (S k₁) = (L₁, o, L₂)) :
    Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (2 * L₁.length + 3) ⟨some (_root_.Turing.PartrecToTM2.move₂ p k₁ k₂ q), s, S⟩
      ⟨some q, none, update (update S k₁ (o.elim id List.cons L₂)) k₂ (L₁ ++ S k₂)⟩ := by
  have heq : 2 * L₁.length + 3 = (L₁.length + 1) + ((L₁.length + 1) + 1) := by omega
  rw [heq]
  refine steps_trans (move_steps h₁.1 e) (steps_head rfl ?_)
  cases o <;> rw [_root_.Turing.PartrecToTM2.tr]
    <;> simp only [id, _root_.Turing.TM2.stepAux, Option.isSome, Bool.cond_true, Bool.cond_false, Option.elim]
  · convert! move_steps h₁.2.1.symm (_root_.Turing.PartrecToTM2.splitAtPred_false _) using 2
    · simp [Function.update_self, List.reverseAux_eq, h₂]
    simp only [Function.update_comm h₁.1, Function.update_idem]
    rw [show update S rev [] = S by rw [← h₂, Function.update_eq_self]]
    simp only [Function.update_of_ne h₁.2.2.symm, Function.update_of_ne h₁.2.1,
      Function.update_of_ne h₁.1.symm, List.reverseAux_eq, h₂, Function.update_self,
      List.append_nil, List.reverse_reverse]
  · simp only [Option.getD_some]
    convert! move_steps h₁.2.1.symm (_root_.Turing.PartrecToTM2.splitAtPred_false _) using 2
    · simp [Function.update_self, Function.update_of_ne h₁.1.symm, List.reverseAux_eq, h₂]
    simp only [h₂, Function.update_comm h₁.1, List.reverseAux_eq, Function.update_self,
      List.append_nil, Function.update_idem]
    rw [show update S rev [] = S by rw [← h₂, Function.update_eq_self]]
    simp only [Function.update_of_ne h₁.1.symm, Function.update_of_ne h₁.2.2.symm,
      Function.update_of_ne h₁.2.1, Function.update_self, List.reverse_reverse]

theorem head_stack_time {q s L₁ L₂ L₃} :
    Within (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (2*(_root_.Turing.PartrecToTM2.trList L₂).length+6)
      ⟨some (_root_.Turing.PartrecToTM2.head stack q), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList L₁) [] [] (_root_.Turing.PartrecToTM2.trList L₂ ++ _root_.Turing.PartrecToTM2.Γ'.consₗ :: L₃)⟩
      ⟨some q, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList (L₂.headI :: L₁)) [] [] L₃⟩ := by
  rcases L₂ with - | ⟨a, L₂⟩
  · have h : Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (1+(2+1+1))
        ⟨some (_root_.Turing.PartrecToTM2.head stack q), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList L₁) [] [] (_root_.Turing.PartrecToTM2.trList [] ++ _root_.Turing.PartrecToTM2.Γ'.consₗ :: L₃)⟩
        ⟨some q, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList ([].headI :: L₁)) [] [] L₃⟩ := by
      refine steps_trans
        (move_steps (by decide)
          (_root_.Turing.PartrecToTM2.splitAtPred_eq _ _ [] (some _root_.Turing.PartrecToTM2.Γ'.consₗ) L₃ (by rintro _ ⟨⟩) ⟨rfl,rfl⟩))
        (steps_head rfl (steps_head rfl ?_))
      rw [_root_.Turing.PartrecToTM2.tr]
      simp only [_root_.Turing.TM2.stepAux, ite_true, id_eq, _root_.Turing.PartrecToTM2.trList, List.nil_append,
        elim_update_stack, elim_rev, List.reverseAux_nil, elim_update_rev,
        Function.update_self, List.headI_nil, _root_.Turing.PartrecToTM2.trNat_default]
      convert! unrev_steps using 2 <;> simp
    exact h.within.mono (by simp)
  · have h : Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr)
        (((_root_.Turing.PartrecToTM2.trNat a).length+1)+((((_root_.Turing.PartrecToTM2.trList L₂).length+1)+((_root_.Turing.PartrecToTM2.trNat a).length+2)+1)+1))
        ⟨some (_root_.Turing.PartrecToTM2.head stack q), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList L₁) [] [] (_root_.Turing.PartrecToTM2.trList (a::L₂) ++ _root_.Turing.PartrecToTM2.Γ'.consₗ :: L₃)⟩
        ⟨some q, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList ((a::L₂).headI :: L₁)) [] [] L₃⟩ := by
      refine steps_trans
        (move_steps (by decide)
          (_root_.Turing.PartrecToTM2.splitAtPred_eq _ _ (_root_.Turing.PartrecToTM2.trNat a) (some _root_.Turing.PartrecToTM2.Γ'.cons) (_root_.Turing.PartrecToTM2.trList L₂ ++ _root_.Turing.PartrecToTM2.Γ'.consₗ :: L₃)
            (_root_.Turing.PartrecToTM2.trNat_natEnd _) ⟨rfl, by simp⟩))
        (steps_head rfl (steps_head rfl ?_))
      simp only [_root_.Turing.PartrecToTM2.trList, List.append_assoc,
        List.cons_append, elim_update_stack, elim_rev, elim_update_rev,
        Function.update_self, List.headI_cons]
      refine steps_trans
        (clear_steps
          (_root_.Turing.PartrecToTM2.splitAtPred_eq _ _ (_root_.Turing.PartrecToTM2.trList L₂) (some _root_.Turing.PartrecToTM2.Γ'.consₗ) L₃
            (fun x h => Bool.decide_false (_root_.Turing.PartrecToTM2.trList_ne_consₗ _ _ h)) ⟨rfl, by simp⟩)) ?_
      simpa [List.reverseAux_eq] using
        (unrev_steps (q := q) (s := some _root_.Turing.PartrecToTM2.Γ'.consₗ) (S := _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList L₁) (_root_.Turing.PartrecToTM2.Γ'.cons :: (_root_.Turing.PartrecToTM2.trNat a).reverse) [] L₃))
    exact h.within.mono (by simp only [_root_.Turing.PartrecToTM2.trList, List.length_append, List.length_cons]; omega)

theorem succ_time {q s n} {c d : List _root_.Turing.PartrecToTM2.Γ'} :
    Within (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (2*(_root_.Turing.PartrecToTM2.trNat n).length+2)
      ⟨some (_root_.Turing.PartrecToTM2.Λ'.succ q), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList [n]) [] c d⟩
      ⟨some q, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList [n.succ]) [] c d⟩ := by
  simp only [_root_.Turing.PartrecToTM2.trList, _root_.Turing.PartrecToTM2.trNat.eq_1, Nat.cast_succ, Num.add_one]
  rcases (n : Num) with - | a
  · have h : Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (1+1)
        ⟨some (_root_.Turing.PartrecToTM2.Λ'.succ q), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trNum Num.zero ++ _root_.Turing.PartrecToTM2.Γ'.cons :: _root_.Turing.PartrecToTM2.trList []) [] c d⟩
        ⟨some q, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trNum (Num.succ Num.zero) ++ _root_.Turing.PartrecToTM2.Γ'.cons :: _root_.Turing.PartrecToTM2.trList []) [] c d⟩ := by
      refine steps_head rfl ?_
      convert! (unrev_steps (q := q) (s := some _root_.Turing.PartrecToTM2.Γ'.cons) (S := _root_.Turing.PartrecToTM2.K'.elim [_root_.Turing.PartrecToTM2.Γ'.bit1, _root_.Turing.PartrecToTM2.Γ'.cons] [] c d)) using 1 <;> simp <;> rfl
    exact h.within
  simp only [_root_.Turing.PartrecToTM2.trNum, Num.succ, Num.succ']
  have hpref : ∀ l₁, ∃ l₁' l₂' s' t,
      List.reverseAux l₁ (_root_.Turing.PartrecToTM2.trPosNum a.succ) = List.reverseAux l₁' l₂' ∧
      Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) t ⟨some q.succ, s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trPosNum a ++ [_root_.Turing.PartrecToTM2.Γ'.cons]) l₁ c d⟩
        ⟨some (_root_.Turing.PartrecToTM2.unrev q), s', _root_.Turing.PartrecToTM2.K'.elim (l₂' ++ [_root_.Turing.PartrecToTM2.Γ'.cons]) l₁' c d⟩ ∧
      t ≤ (_root_.Turing.PartrecToTM2.trPosNum a).length+1 ∧ l₁'.length ≤ l₁.length+(_root_.Turing.PartrecToTM2.trPosNum a).length := by
    induction a generalizing s with intro l₁
    | one =>
      refine ⟨_root_.Turing.PartrecToTM2.Γ'.bit0::l₁, [_root_.Turing.PartrecToTM2.Γ'.bit1], some _root_.Turing.PartrecToTM2.Γ'.cons, 2, rfl,
        steps_head rfl (steps_one ?_), by simp [_root_.Turing.PartrecToTM2.trPosNum], by simp [_root_.Turing.PartrecToTM2.trPosNum]⟩
      simp [_root_.Turing.TM2.step, _root_.Turing.PartrecToTM2.trPosNum]
    | bit1 m IH =>
      obtain ⟨l₁',l₂',s',t,e,h,ht,hl⟩ := IH (_root_.Turing.PartrecToTM2.Γ'.bit0::l₁)
      refine ⟨l₁',l₂',s',t+1,e,steps_head ?_ h,?_,?_⟩
      · simp [_root_.Turing.TM2.step, _root_.Turing.PartrecToTM2.trPosNum]
        rfl
      · simp only [_root_.Turing.PartrecToTM2.trPosNum,List.length_cons]; omega
      · simp only [_root_.Turing.PartrecToTM2.trPosNum,List.length_cons] at *; omega
    | bit0 m _ =>
      refine ⟨l₁, _, some _root_.Turing.PartrecToTM2.Γ'.bit0, 1, rfl, steps_one ?_, by simp [_root_.Turing.PartrecToTM2.trPosNum], by simp [_root_.Turing.PartrecToTM2.trPosNum]⟩
      simp only [_root_.Turing.TM2.step]; rw [_root_.Turing.PartrecToTM2.tr]
      simp only [_root_.Turing.TM2.stepAux, _root_.Turing.PartrecToTM2.pop', elim_main, elim_update_main,
        elim_rev, elim_update_rev, Function.update_self]
      rfl
  obtain ⟨l₁',l₂',s',t,e,h,ht,hl⟩ := hpref []
  simp only [List.reverseAux_nil] at e
  have hu : Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (l₁'.length+1)
      ⟨some (_root_.Turing.PartrecToTM2.unrev q), s', _root_.Turing.PartrecToTM2.K'.elim (l₂' ++ [_root_.Turing.PartrecToTM2.Γ'.cons]) l₁' c d⟩
      ⟨some q, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trPosNum a.succ ++ [_root_.Turing.PartrecToTM2.Γ'.cons]) [] c d⟩ := by
    convert! unrev_steps using 2 <;> simp [e,List.reverseAux_eq]
  exact (steps_trans h hu).within.mono (by simp only [List.length_nil, zero_add] at hl; omega)

theorem pred_time (q₁ q₂ s v) (c d : List _root_.Turing.PartrecToTM2.Γ') : ∃ s',
    Within (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (2*(_root_.Turing.PartrecToTM2.trList v).length+3)
      ⟨some (_root_.Turing.PartrecToTM2.Λ'.pred q₁ q₂), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList v) [] c d⟩
      (v.headI.rec ⟨some q₁, s', _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList v.tail) [] c d⟩ fun n _ =>
        ⟨some q₂, s', _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList (n::v.tail)) [] c d⟩) := by
  rcases v with (_ | ⟨_ | n, v⟩)
  · refine ⟨none, (within_one ?_).mono (by simp)⟩
    simp [_root_.Turing.TM2.step]
  · refine ⟨some _root_.Turing.PartrecToTM2.Γ'.cons, (within_one ?_).mono (by simp)⟩
    simp [_root_.Turing.TM2.step]
  refine ⟨none, ?_⟩
  simp only [_root_.Turing.PartrecToTM2.trList, _root_.Turing.PartrecToTM2.trNat.eq_1, _root_.Turing.PartrecToTM2.trNum, Nat.cast_succ, Num.add_one, Num.succ,
    List.tail_cons, List.headI_cons]
  rcases (n : Num) with - | a
  · simp only [_root_.Turing.PartrecToTM2.trPosNum, Num.succ', List.singleton_append, List.nil_append]
    have h : Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (1+1)
        ⟨some (_root_.Turing.PartrecToTM2.Λ'.pred q₁ q₂), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.Γ'.bit1::_root_.Turing.PartrecToTM2.Γ'.cons::_root_.Turing.PartrecToTM2.trList v) [] c d⟩
        ⟨some q₂, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.Γ'.cons::_root_.Turing.PartrecToTM2.trList v) [] c d⟩ := by
      refine steps_head rfl ?_
      rw [_root_.Turing.PartrecToTM2.tr]; simp only [_root_.Turing.PartrecToTM2.pop', _root_.Turing.TM2.stepAux]
      convert! unrev_steps using 2 <;> simp
    exact h.within.mono (by simp)
  simp only [Num.succ']
  have hpref : ∀ l₁, ∃ l₁' l₂' s' t,
      List.reverseAux l₁ (_root_.Turing.PartrecToTM2.trPosNum a) = List.reverseAux l₁' l₂' ∧
      Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) t
        ⟨some (q₁.pred q₂), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trPosNum a.succ ++ _root_.Turing.PartrecToTM2.Γ'.cons :: _root_.Turing.PartrecToTM2.trList v) l₁ c d⟩
        ⟨some (_root_.Turing.PartrecToTM2.unrev q₂), s', _root_.Turing.PartrecToTM2.K'.elim (l₂' ++ _root_.Turing.PartrecToTM2.Γ'.cons :: _root_.Turing.PartrecToTM2.trList v) l₁' c d⟩ ∧
      t ≤ (_root_.Turing.PartrecToTM2.trPosNum a.succ).length+1 ∧ l₁'.length ≤ l₁.length+(_root_.Turing.PartrecToTM2.trPosNum a.succ).length := by
    induction a generalizing s with intro l₁
    | one =>
      refine ⟨_root_.Turing.PartrecToTM2.Γ'.bit1::l₁, [], some _root_.Turing.PartrecToTM2.Γ'.cons, 2, rfl,
        steps_head rfl (steps_one ?_), by simp [_root_.Turing.PartrecToTM2.trPosNum,PosNum.succ], by simp [_root_.Turing.PartrecToTM2.trPosNum,PosNum.succ]⟩
      simp [_root_.Turing.TM2.step, _root_.Turing.PartrecToTM2.trPosNum, show PosNum.one.succ = PosNum.one.bit0 from rfl]
    | bit1 m IH =>
      obtain ⟨l₁',l₂',s',t,e,h,ht,hl⟩ := IH (some _root_.Turing.PartrecToTM2.Γ'.bit0) (_root_.Turing.PartrecToTM2.Γ'.bit1::l₁)
      refine ⟨l₁',l₂',s',t+1,e,steps_head ?_ h,?_,?_⟩
      · simp [_root_.Turing.TM2.step]
        rfl
      · simp only [PosNum.succ,_root_.Turing.PartrecToTM2.trPosNum,List.length_cons]; omega
      · simp only [PosNum.succ,_root_.Turing.PartrecToTM2.trPosNum,List.length_cons] at *; omega
    | bit0 m _ =>
      obtain ⟨a,l,e,h⟩ : ∃ a l, _root_.Turing.PartrecToTM2.trPosNum m=a::l ∧ _root_.Turing.PartrecToTM2.natEnd a=false := by
        cases m <;> refine ⟨_,_,rfl,rfl⟩
      refine ⟨_root_.Turing.PartrecToTM2.Γ'.bit0::l₁, _, some a, 1, rfl, steps_one ?_,
        by simp [PosNum.succ,_root_.Turing.PartrecToTM2.trPosNum], by simp [PosNum.succ,_root_.Turing.PartrecToTM2.trPosNum]⟩
      simp [_root_.Turing.TM2.step,_root_.Turing.PartrecToTM2.trPosNum,PosNum.succ,e,h,show some _root_.Turing.PartrecToTM2.Γ'.bit1 ≠ some _root_.Turing.PartrecToTM2.Γ'.bit0 by decide,
        Option.getD,-_root_.Turing.PartrecToTM2.natEnd]
      simp [_root_.Turing.PartrecToTM2.natEnd]
  obtain ⟨l₁',l₂',s',t,e,h,ht,hl⟩ := hpref []
  simp only [List.reverseAux_nil] at e
  have hu : Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (l₁'.length+1)
      ⟨some (_root_.Turing.PartrecToTM2.unrev q₂), s', _root_.Turing.PartrecToTM2.K'.elim (l₂' ++ _root_.Turing.PartrecToTM2.Γ'.cons :: _root_.Turing.PartrecToTM2.trList v) l₁' c d⟩
      ⟨some q₂, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trPosNum a ++ _root_.Turing.PartrecToTM2.Γ'.cons :: _root_.Turing.PartrecToTM2.trList v) [] c d⟩ := by
    convert! unrev_steps using 2 <;> simp [e,List.reverseAux_eq]
  exact (steps_trans h hu).within.mono (by
    simp only [List.length_nil,zero_add] at hl
    simp only [List.length_append,List.length_cons]; omega)

end Turing.PartrecToTM2

end

namespace MinUncut.Costed.WordTransducer
open _root_.Turing Function

inductive Tape | input | work | output deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .work, .output]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

def Alphabet (A B : Type) : Tape → Type
  | .input => A
  | .work | .output => B

def tapes {A B : Type} (input : List A) (work output : List B) :
    ∀ k,List (Alphabet A B k)
  | .input => input
  | .work => work
  | .output => output

@[simp] lemma update_input {A B : Type} (i i' : List A) (w o : List B) :
    update (tapes i w o) .input i'=tapes i' w o := by
  funext k
  cases k <;> simp only [tapes] <;> rfl
@[simp] lemma update_work {A B : Type} (i : List A) (w w' o : List B) :
    update (tapes i w o) .work w'=tapes i w' o := by
  funext k; cases k <;> rfl
@[simp] lemma update_output {A B : Type} (i : List A) (w o o' : List B) :
    update (tapes i w o) .output o'=tapes i w o' := by
  funext k; cases k <;> rfl

def pushWord {K Λ σ : Type} {Γ : K → Type} (dst : K) :
    List (Γ dst) → TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ σ
  | [], q => q
  | a::w, q => .push dst (fun _ => a) (pushWord dst w q)

lemma pushWord_aux {K Λ σ : Type} {Γ : K → Type} [DecidableEq K] (dst : K)
    (w : List (Γ dst)) (q : TM2.Stmt Γ Λ σ) (s : σ) (st : ∀ k,List (Γ k)) :
    TM2.stepAux (pushWord dst w q) s st=
      TM2.stepAux q s (update st dst (w.reverse++st dst)) := by
  induction w generalizing st with
  | nil => simp [pushWord]
  | cons a w ih =>
    simp only [pushWord,TM2.stepAux,ih,update_self,update_idem,
      List.reverse_cons,List.append_assoc,List.singleton_append]

variable {A B Q : Type}
inductive Label (Q A : Type) | read | emit (q : Q) (a : A) | reverse
  deriving DecidableEq, Fintype
abbrev State (Q A B : Type) := Q × Option A × Option B

def output (next : Q → A → Q) (emit : Q → A → List B) : Q → List A → List B
  | _, [] => []
  | q,a::v => emit q a ++ output next emit (next q a) v

def program [Inhabited A] [Inhabited B] (initial : Q)
    (next : Q → A → Q) (emit : Q → A → List B) :
    Label Q A → TM2.Stmt (Alphabet A B) (Label Q A) (State Q A B)
  | .read => .pop .input (fun s a => (s.1,a,s.2.2))
      (.branch (fun s => s.2.1.isSome)
        (.goto fun s => .emit s.1 (s.2.1.getD default))
        (.load (fun _ => (initial,none,none)) (.goto fun _ => .reverse)))
  | .emit q a => .load (fun _ => (next q a,none,none))
      (pushWord .work (emit q a) (.goto fun _ => .read))
  | .reverse => .pop .work (fun s b => (s.1,s.2.1,b))
      (.branch (fun s => s.2.2.isSome)
        (.push .output (fun s => s.2.2.getD default) (.goto fun _ => .reverse))
        (.load (fun _ => (initial,none,none)) .halt))

def machine [Fintype A] [Fintype B] [Fintype Q] [Inhabited A] [Inhabited B]
    (initial : Q) (next : Q → A → Q) (emit : Q → A → List B) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet A B
  Γk₀Fin := inferInstanceAs (Fintype A)
  Λ := Label Q A
  main := .read
  σ := State Q A B
  initialState := (initial,none,none)
  m := program initial next emit

lemma finiteAlphabet [Fintype A] [Fintype B] [Fintype Q] [Inhabited A] [Inhabited B]
    (initial : Q) (next : Q → A → Q) (emit : Q → A → List B)
    (k : (machine initial next emit).K) : Finite ((machine initial next emit).Γ k) := by
  cases k <;> dsimp [machine,Alphabet] <;> infer_instance

variable [Inhabited A] [Inhabited B]

lemma reverse_steps (initial : Q) (next : Q → A → Q) (emit : Q → A → List B)
    (w o : List B) (s : State Q A B) :
    Steps (TM2.step (program initial next emit)) (w.length+1)
      ⟨some .reverse,s,tapes [] w o⟩
      ⟨none,(initial,none,none),tapes [] [] (w.reverse++o)⟩ := by
  induction w generalizing s o with
  | nil =>
    apply steps_one
    simp only [TM2.step, program]
    exact congrArg (fun st => (some ⟨none, (initial, none, none), st⟩ :
      Option (TM2.Cfg (Alphabet A B) (Label Q A) (State Q A B))))
      (update_work (A := A) [] [] [] o)
  | cons b w ih =>
    have h : TM2.step (program initial next emit)
        ⟨some .reverse,s,tapes [] (b::w) o⟩=
        some ⟨some .reverse,(s.1,s.2.1,some b),tapes [] w (b::o)⟩ := by
      have hwork := update_work (A := A) [] (b :: w) w o
      have hout := update_output (A := A) [] w o (b :: o)
      have ht := (congrArg (fun st => update st Tape.output (b :: o)) hwork).trans hout
      exact congrArg (fun st => (some ⟨some .reverse, (s.1, s.2.1, some b), st⟩ :
        Option (TM2.Cfg (Alphabet A B) (Label Q A) (State Q A B)))) ht
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
      using steps_head h (ih (b::o) (s.1,s.2.1,some b))

lemma emit_steps (initial q : Q) (next : Q → A → Q) (emit : Q → A → List B)
    (a : A) (v : List A) (w : List B) :
    Steps (TM2.step (program initial next emit)) 2
      ⟨some .read,(q,none,none),tapes (a::v) w []⟩
      ⟨some .read,(next q a,none,none),tapes v ((emit q a).reverse++w) []⟩ := by
  apply steps_head (b := ⟨some (.emit q a),(q,some a,none),tapes v w []⟩)
  · exact congrArg (fun st => (some ⟨some (.emit q a), (q, some a, none), st⟩ :
      Option (TM2.Cfg (Alphabet A B) (Label Q A) (State Q A B))))
      (update_input (a :: v) v w [])
  · apply steps_one
    have hp := pushWord_aux (Γ := Alphabet A B) (Λ := Label Q A) (σ := State Q A B)
      Tape.work (emit q a) (.goto fun _ => .read) (next q a, none, none) (tapes v w [])
    exact (congrArg some hp).trans
      (congrArg (fun st => (some ⟨some .read, (next q a, none, none), st⟩ :
        Option (TM2.Cfg (Alphabet A B) (Label Q A) (State Q A B))))
        (update_work v w ((emit q a).reverse ++ w) []))

lemma read_steps (initial q : Q) (next : Q → A → Q) (emit : Q → A → List B)
    (v : List A) (w : List B) :
    Steps (TM2.step (program initial next emit)) (2*v.length+1)
      ⟨some .read,(q,none,none),tapes v w []⟩
      ⟨some .reverse,(initial,none,none),tapes [] ((output next emit q v).reverse++w) []⟩ := by
  induction v generalizing q w with
  | nil =>
    apply steps_one
    exact congrArg (fun st => (some ⟨some .reverse, (initial, none, none), st⟩ :
      Option (TM2.Cfg (Alphabet A B) (Label Q A) (State Q A B))))
      (update_input (A := A) [] [] w [])
  | cons a v ih =>
    have ht := steps_trans (emit_steps initial q next emit a v w)
      (ih (next q a) ((emit q a).reverse++w))
    convert ht using 1 <;> simp [output,List.reverse_append,List.append_assoc]
    omega

variable [Fintype A] [Fintype B] [Fintype Q]

def outputsInTime (initial : Q) (next : Q → A → Q) (emit : Q → A → List B) (v : List A) :
    TM2OutputsInTime (machine initial next emit) v (some (output next emit initial v))
      (2*v.length+(output next emit initial v).length+2) := by
  have h₁ := read_steps initial initial next emit v []
  simp only [List.append_nil] at h₁
  have h := steps_trans h₁
    (reverse_steps initial next emit ((output next emit initial v).reverse) [] (initial,none,none))
  have hi : initList (machine initial next emit) v=
      ⟨some .read,(initial,none,none),tapes v [] []⟩ := by
    change TM2.Cfg.mk _ _ _=TM2.Cfg.mk _ _ _
    congr 1
    funext k; cases k <;> rfl
  have ho : haltList (machine initial next emit) (output next emit initial v)=
      ⟨none,(initial,none,none),tapes [] [] (output next emit initial v)⟩ := by
    change TM2.Cfg.mk _ _ _=TM2.Cfg.mk _ _ _
    congr 1
    funext k; cases k <;> rfl
  apply steps_timed (n := (2*v.length+1)+((output next emit initial v).reverse.length+1))
  · change Steps (TM2.step (program initial next emit)) _ _ _
    simp only [hi,ho,List.append_nil,List.reverse_reverse] at h ⊢
    exact h
  · simp only [List.length_reverse]; omega

end MinUncut.Costed.WordTransducer

namespace MinUncut.Costed
open _root_.Turing _root_.Turing.ToPartrec _root_.Turing.PartrecToTM2
  _root_.OAI.Turing.PartrecToTM2 Function
open _root_.Turing.PartrecToTM2.K'

theorem fix_done_steps (f : Code) (k : Cont') (v : List ℕ) (s : Option Γ') (S : List Γ')
    (hv : v.headI=0) :
    Steps (TM2.step tr) 1
      ⟨some (Λ'.ret (.fix f k)),s,K'.elim (trList v) [] [] S⟩
      ⟨some (Λ'.ret k),(trList v).head?,K'.elim (trList v.tail) [] [] S⟩ := by
  apply steps_one
  cases v with
  | nil => simp [TM2.step]
  | cons a v =>
    simp only [List.headI_cons] at hv
    subst a
    simp [TM2.step]

theorem fix_more_steps (f : Code) (k : Cont') (a : ℕ) (v : List ℕ) (s : Option Γ') (S : List Γ') :
    Steps (TM2.step tr) ((trNat (a+1)).length+1)
      ⟨some (Λ'.ret (.fix f k)),s,K'.elim (trList ((a+1)::v)) [] [] S⟩
      ⟨some (trNormal f (.fix f k)),some Γ'.cons,K'.elim (trList v) [] [] S⟩ := by
  have htt : natEnd ((trList ((a+1)::v)).head?.getD default)=false ∧
      (trList ((a+1)::v)).tail=(trNat (a+1)).tail ++ Γ'.cons::trList v := by
    simp only [trList,trNat.eq_1,Nat.cast_succ,Num.add_one,Num.succ]
    cases (a : Num).succ' <;> exact ⟨rfl,rfl⟩
  have hn : (trNat (a+1)).length=(trNat (a+1)).tail.length+1 := by
    simp only [trNat.eq_1,Nat.cast_succ,Num.add_one,Num.succ]
    cases (a : Num).succ' <;> simp [trNum,trPosNum]
  rw [hn]
  refine steps_head rfl ?_
  rw [tr]; simp only [TM2.stepAux,pop',elim_main,htt.1]
  convert! (clear_steps (q := trNormal f (.fix f k))
    (s := (trList ((a+1)::v)).head?) (k := main)
    (S := K'.elim (trList ((a+1)::v)).tail [] [] S)
    (splitAtPred_eq _ _ (trNat (a+1)).tail (some Γ'.cons) (trList v)
      (fun x h => trNat_natEnd _ _ (List.tail_subset _ h)) ⟨rfl,htt.2⟩)) using 2 <;> simp

open _root_.Turing
namespace FiniteControl
variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

noncomputable def stmt (S : Finset Λ) :
    (q : TM2.Stmt Γ Λ σ) → TM2.SupportsStmt S q → TM2.Stmt Γ S σ
  | .push k f q, h => .push k f (stmt S q h)
  | .peek k f q, h => .peek k f (stmt S q h)
  | .pop k f q, h => .pop k f (stmt S q h)
  | .load f q, h => .load f (stmt S q h)
  | .branch f q r, h => .branch f (stmt S q h.1) (stmt S r h.2)
  | .goto f, h => .goto (fun s => ⟨f s,h s⟩)
  | .halt, _ => .halt

def project (S : Finset Λ) (c : TM2.Cfg Γ S σ) : TM2.Cfg Γ Λ σ :=
  ⟨c.l.map Subtype.val,c.var,c.stk⟩

omit [DecidableEq K] in
lemma project_injective (S : Finset Λ) : Function.Injective (project (Γ:=Γ) (σ:=σ) S) := by
  intro a b h
  cases a with | mk a v A =>
    cases b with | mk b w B =>
      simp only [project,TM2.Cfg.mk.injEq] at h
      rcases h with ⟨h,hv,hB⟩
      have hab : a=b := Option.map_injective Subtype.val_injective h
      cases hab; cases hv; cases hB; rfl

lemma project_aux (S : Finset Λ) (q : TM2.Stmt Γ Λ σ) (h : TM2.SupportsStmt S q)
    (s : σ) (st : ∀ k,List (Γ k)) :
    project S (TM2.stepAux (stmt S q h) s st)=TM2.stepAux q s st := by
  induction q generalizing s st with
  | push k f q ih => exact ih h _ _
  | peek k f q ih => exact ih h _ _
  | pop k f q ih => exact ih h _ _
  | load f q ih => exact ih h _ _
  | branch f q r ih ih' =>
    cases he : f s <;> simp only [stmt,TM2.stepAux,he,
      Bool.cond_false,Bool.cond_true] <;> first | exact ih h.1 _ _ | exact ih' h.2 _ _
  | goto f => rfl
  | halt => rfl

noncomputable def program (S : Finset Λ) (m : Λ → TM2.Stmt Γ Λ σ)
    (h : ∀q∈S,TM2.SupportsStmt S (m q)) : S → TM2.Stmt Γ S σ :=
  fun q => stmt S (m q.val) (h q q.property)

lemma project_step (S : Finset Λ) (m : Λ → TM2.Stmt Γ Λ σ)
    (h : ∀q∈S,TM2.SupportsStmt S (m q)) (c : TM2.Cfg Γ S σ) :
    (TM2.step (program S m h) c).map (project S)=TM2.step m (project S c) := by
  rcases c with ⟨l,s,st⟩
  cases l with
  | none => rfl
  | some q => exact congrArg some (project_aux S (m q) (h q q.property) s st)

lemma projected_iterate {α β : Type} (f : α → Option α) (g : β → Option β)
    (p : α → β) (h : ∀a,(f a).map p=g (p a)) (n : ℕ) (a : Option α) :
    ((fun x => x.bind f)^[n] a).map p=(fun x => x.bind g)^[n] (a.map p) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply,ih]
    congr 1
    cases a with
    | none => rfl
    | some a => exact h a

end FiniteControl
end MinUncut.Costed

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_GraphWordCodec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MinUncut.Costed.GraphCodec
open _root_.Turing _root_.OAI.Turing _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2
open MinUncutGames.BinaryEncoding

inductive Mode | header | cell | one | zeroBit | marker | threshold | done
  deriving DecidableEq

protected abbrev Mode.enumList : List Mode := [.header, .cell, .one, .zeroBit, .marker,
  .threshold, .done]

protected theorem Mode.enumList_nodup : Mode.enumList.Nodup := by decide

instance instFintypeMode : Fintype Mode where
  elems := ⟨Mode.enumList, Mode.enumList_nodup⟩
  complete x := by cases x <;> decide

def bitSymbol (b : Bool) : Γ' := if b then .bit1 else .bit0

def next : Mode → Γ' → Mode
  | .header,.cons => .cell
  | .threshold,.cons => .done
  | .header,_ => .header
  | .threshold,_ => .threshold
  | .done,_ => .done
  | .cell,.bit1 => .one
  | .cell,.bit0 => .zeroBit
  | .cell,_ => .cell
  | .one,_ => .cell
  | .zeroBit,.bit1 => .marker
  | .zeroBit,_ => .cell
  | .marker,.cons => .threshold
  | .marker,_ => .marker

def emit : Mode → Γ' → List Bool
  | .header,.bit0 | .threshold,.bit0 => [true,false]
  | .header,.bit1 | .threshold,.bit1 => [true,true]
  | .header,.cons | .threshold,.cons | .cell,.cons => [false]
  | .one,.cons => [true]
  | _,_ => []

def machine : FinTM2 := WordTransducer.machine .header next emit

lemma trPosNum_bits (n : PosNum) : trPosNum n=(n:ℕ).bits.map bitSymbol := by
  induction n with
  | one => simp [trPosNum,Nat.one_bits,bitSymbol]
  | bit0 n ih =>
    have hn : (n:ℕ)≠0 := ne_of_gt n.to_nat_pos
    simpa [trPosNum,PosNum.cast_bit0,← two_mul,Nat.bit0_bits _ hn,bitSymbol] using
      congrArg (List.cons Γ'.bit0) ih
  | bit1 n ih =>
    simpa [trPosNum,PosNum.cast_bit1,← two_mul,Nat.bit1_bits,bitSymbol] using
      congrArg (List.cons Γ'.bit1) ih

lemma trNat_bits (n : ℕ) : trNat n=n.bits.map bitSymbol := by
  have hh (a : Num) : trNum a=(a:ℕ).bits.map bitSymbol := by
    cases a with
    | zero => simp [trNum,Nat.zero_bits]
    | pos a => exact trPosNum_bits a
  simpa only [trNat,Num.to_of_nat] using hh (n:Num)

lemma done_output (v : List Γ') : WordTransducer.output next emit .done v=[] := by
  induction v with
  | nil => rfl
  | cons a v ih => cases a <;> simpa [WordTransducer.output,next,emit] using ih

lemma header_output (v : List Bool) (rest : List Γ') :
    WordTransducer.output next emit .header (v.map bitSymbol++Γ'.cons::rest)=
      frame v++WordTransducer.output next emit .cell rest := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    cases b <;> simp [WordTransducer.output,next,emit,bitSymbol,frame,ih]

lemma threshold_output (v : List Bool) (rest : List Γ') :
    WordTransducer.output next emit .threshold (v.map bitSymbol++Γ'.cons::rest)=frame v := by
  induction v with
  | nil => simp [WordTransducer.output,next,emit,frame,done_output]
  | cons b v ih =>
    cases b <;> simp [WordTransducer.output,next,emit,bitSymbol,frame,ih]

lemma cells_output (v : List Bool) (k : ℕ) (rest : List ℕ) :
    WordTransducer.output next emit .cell (trList (v.map Bool.toNat++2::k::rest))=
      v++nameBits k := by
  induction v with
  | nil =>
    change WordTransducer.output next emit .cell
      ([.bit0,.bit1,.cons]++(trNat k++Γ'.cons::trList rest))=nameBits k
    simp only [List.cons_append,List.nil_append,WordTransducer.output,next,emit]
    rw [trNat_bits,threshold_output]
    rfl
  | cons b v ih =>
    cases b with
    | false =>
      change false::WordTransducer.output next emit .cell
        (trList (v.map Bool.toNat++2::k::rest))=false::(v++nameBits k)
      exact congrArg (List.cons false) ih
    | true =>
      change true::WordTransducer.output next emit .cell
        (trList (v.map Bool.toNat++2::k::rest))=true::(v++nameBits k)
      exact congrArg (List.cons true) ih

lemma output (n k : ℕ) (v : List Bool) (rest : List ℕ) :
    WordTransducer.output next emit .header (trList (n::(v.map Bool.toNat++2::k::rest)))=
      nameBits n++v++nameBits k := by
  rw [trList,trNat_bits,header_output,cells_output]
  simp only [nameBits,List.append_assoc]

lemma finiteAlphabet (k : machine.K) : Finite (machine.Γ k) :=
  WordTransducer.finiteAlphabet _ _ _ k

end MinUncut.Costed.GraphCodec

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_FramedWordDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Costed.FrameDecode
open _root_.Turing _root_.OAI.Turing _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 MinUncutGames.BinaryEncoding
inductive Mode
  | flag | payload | suffix
  deriving DecidableEq

protected abbrev Mode.enumList : List Mode := [.flag, .payload, .suffix]

protected theorem Mode.enumList_nodup : Mode.enumList.Nodup := by decide

instance instFintypeMode : Fintype Mode where
  elems := ⟨Mode.enumList, Mode.enumList_nodup⟩
  complete x := by cases x <;> decide

def next : Mode → Bool → Mode
  | .flag,true => .payload
  | .flag,false => .suffix
  | .payload,_ => .flag
  | .suffix,_ => .suffix

def symbol (b : Bool) : ℕ := b.toNat+1

def emit : Mode → Bool → List Γ'
  | .flag,true => []
  | .flag,false => [.cons]
  | .payload,b => [GraphCodec.bitSymbol b]
  | .suffix,b => trNat (symbol b)++[.cons]

def machine : FinTM2 := WordTransducer.machine .flag next emit
lemma finiteAlphabet (k : machine.K) : Finite (machine.Γ k) :=
  WordTransducer.finiteAlphabet .flag next emit k
lemma suffix_output (v : List Bool) :
    WordTransducer.output next emit .suffix v=trList (v.map symbol) := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    simp only [WordTransducer.output,next,emit,List.map_cons,trList,ih,List.append_assoc,List.singleton_append]
lemma frame_output (v w : List Bool) :
    WordTransducer.output next emit .flag (frame v++w)=
      v.map GraphCodec.bitSymbol++Γ'.cons::trList (w.map symbol) := by
  induction v with
  | nil => simpa only [frame,List.cons_append,List.nil_append,WordTransducer.output,next,emit,
      List.singleton_append,List.map_nil] using congrArg (List.cons Γ'.cons) (suffix_output w)
  | cons b v ih =>
    simp only [frame,List.cons_append,WordTransducer.output,next,emit,List.nil_append,
      List.map_cons,ih]
lemma output_spec (K : ℕ) (w : List Bool) :
    WordTransducer.output next emit .flag (nameBits K++w)=trList (K::w.map symbol) := by
  rw [nameBits,frame_output,←GraphCodec.trNat_bits]
  rfl
def outputs (K : ℕ) (w : List Bool) :
    TM2OutputsInTime machine (nameBits K++w) (some (trList (K::w.map symbol)))
      (2*(nameBits K++w).length+(trList (K::w.map symbol)).length+2) := by
  have h := WordTransducer.outputsInTime .flag next emit (nameBits K++w)
  erw [output_spec] at h
  exact h
lemma count_symbols (v : List Bool) : UnaryWords.count (v.map symbol)=v.length := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    simp only [List.map_cons,UnaryWords.count,symbol,show b.toNat+1≠0 by omega,ite_false,ih,List.length_cons]
end MinUncut.Costed.FrameDecode

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CountedWordParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.UnaryWords
open Turing.ToPartrec Polynomial
def finishCounted (v : List ℕ) : List ℕ := v.headI::finish v
def bodyCounted (v : List ℕ) : List ℕ := if symbol v=0 then 0::finishCounted v else 1::step v
def parsedCounted (v : List ℕ) : List ℕ := count v::parsed v

open MinUncutGames.Foundations.Complexity
end MinUncut.Costed.UnaryWords

noncomputable section
namespace MinUncut.Costed.Arena.Init
open Turing.ToPartrec Polynomial MinUncutGames.Foundations.Complexity

def parseWithKey (v : List ℕ) : List ℕ := v.headI::UnaryWords.parsedCounted v.tail
end MinUncut.Costed.Arena.Init

end
namespace MinUncut.Costed
open Turing.ToPartrec Polynomial
noncomputable section
variable {f e : List ℕ → List ℕ}

def untilStateBound (L M : ℕ) : Polynomial ℕ := C ((L+1)*(M+1))*(X+1)^2
lemma iterate_at_stop (hs : ∀v,(e v).headI=0 → f v=v) (v : List ℕ) (i j : ℕ)
    (hi : (e (f^[i] v)).headI=0) (hij : i≤j) : f^[j] v=f^[i] v := by
  have hf : ∀k,f^[k] (f^[i] v)=f^[i] v := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply',ih,hs _ hi]
  rw [show j=(j-i)+i by omega,Function.iterate_add_apply,hf]

end
end MinUncut.Costed

namespace MinUncut.Costed.Arena
open Turing.ToPartrec Polynomial

open Turing.ToPartrec Polynomial
noncomputable section

def unboundedControllerInput : Polynomial ℕ := 3*X+2
def unboundedControllerState : Polynomial ℕ := (untilStateBound 9 3).comp unboundedControllerInput
end
end MinUncut.Costed.Arena

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_DemandOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.GraphRegisters
open PolyProgram

def initRender (v : List ℕ) : List ℕ :=
  let V := v.headI+(v.drop 1).headI*3
  V^2::(queryState v.headI (v.drop 1).headI (v.drop 2).headI V (V-1) (V-1) [] (v.drop 3)).encode

open MinUncut.PathRealization

lemma length_packDemands {N : ℕ} (ds : List (Demand (Fin N))) :
    (packDemands ds).length=3*ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [packDemands,List.flatMap_cons,List.length_append,
      packDemand,List.length_cons,List.length_nil,List.length_cons] at ih ⊢; omega

lemma rawLocal_append (N d : ℕ) (data rest : List ℕ) (u v : ℕ) (h : 3*d+2<data.length) :
    rawLocal N d (data++rest) u v=rawLocal N d data u v := by
  simp only [rawLocal,drop_head_append data rest (3*d) (by omega),
    drop_head_append data rest (3*d+1) (by omega),drop_head_append data rest (3*d+2) h]

lemma rawCell_append (N M : ℕ) (data rest : List ℕ) (u v : ℕ) (h : 3*M≤data.length) :
    rawCell N M (data++rest) u v=rawCell N M data u v := by
  unfold rawCell
  congr 1
  apply propext
  constructor <;> rintro ⟨d,hd,he⟩ <;> refine ⟨d,hd,?_⟩
  · rwa [rawLocal_append N d data rest u v (by omega)] at he
  · rwa [rawLocal_append N d data rest u v (by omega)]

end MinUncut.Costed.GraphRegisters

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_CodeFiniteMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MinUncut.Costed
open _root_.Turing _root_.OAI.Turing _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 Turing.ToPartrec
noncomputable section

local instance instFintypeK'_solutions : Fintype K' := ⟨{.main,.rev,.aux,.stack}, by intro k; cases k <;> simp⟩

def codeMachine (c : Code) : FinTM2 where
  K := K'
  k₀ := .main
  k₁ := .main
  Γ _ := Γ'
  Λ := codeSupp c .halt
  main := ⟨trNormal c .halt,codeSupp_self c .halt (trStmts₁_self _)⟩
  σ := Option Γ'
  initialState := none
  m := FiniteControl.program (codeSupp c .halt) tr
    (fun _ h => codeSupp_supports (Finset.Subset.refl _) _ h)

lemma codeMachine_finiteAlphabet (c : Code) (k : (codeMachine c).K) :
    Finite ((codeMachine c).Γ k) := inferInstanceAs (Finite Γ')

lemma codeMachine_init (c : Code) (v : List ℕ) :
    FiniteControl.project (codeSupp c .halt) (initList (codeMachine c) (trList v))=
      ⟨some (trNormal c .halt),none,K'.elim (trList v) [] [] []⟩ := by
  change TM2.Cfg.mk _ _ _=TM2.Cfg.mk _ _ _
  congr 1
  funext k
  cases k <;> rfl

lemma codeMachine_halt (c : Code) (v : List ℕ) :
    FiniteControl.project (codeSupp c .halt) (haltList (codeMachine c) (trList v))=
      ⟨none,none,K'.elim (trList v) [] [] []⟩ := by
  change TM2.Cfg.mk _ _ _=TM2.Cfg.mk _ _ _
  congr 1
  funext k
  cases k <;> rfl

end
end MinUncut.Costed

end
section
namespace MinUncut.Costed
open _root_.Turing _root_.OAI.Turing _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 Turing.ToPartrec
open MinUncutGames.Foundations.Complexity
noncomputable section

lemma sequential_finiteAlphabet (a b : FinTM2) (r : a.Γ a.k₁→b.Γ b.k₀)
    (fallback : b.Γ b.k₀) (ha : ∀k,Finite (a.Γ k)) (hb : ∀k,Finite (b.Γ k))
    (k : (MachineSequential.machine a b r fallback).K) :
    Finite ((MachineSequential.machine a b r fallback).Γ k) := by
  rcases k with k | k
  · exact ha k
  · rcases k with k | k
    · exact hb k
    · exact hb b.k₀

end
end MinUncut.Costed

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineBinaryFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.BinaryEncoding

open BinaryFormula

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame, ih]; omega

@[simp] theorem nameBits_length (name : Nat) :
    (nameBits name).length = 2 * name.size + 1 := by
  simp [nameBits, Nat.size_eq_bits_len]

end MinUncutGames.BinaryEncoding

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_GraphCoreMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Costed.Framed
open _root_.Turing _root_.OAI.Turing MinUncutGames.Foundations.Complexity
variable (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool)
abbrev Tape := M.K ⊕ Unit
abbrev Alphabet : Tape M → Type := MachineEmbedding.Alphabet M.Γ (fun _ : Unit=>Bool)
abbrev Label := M.Λ ⊕ Option Bool
abbrev State := M.σ × Option Bool

def extra : Option Bool → TM2.Stmt (Alphabet M) (Label M) (State M)
  | none => .pop (.inl M.k₀) (fun s a=>(s.1,a.map ei))
      (.push (.inr ()) (fun s=>s.2.getD false)
        (.branch (fun s=>s.2.getD false)
          (.load (fun s=>(s.1,none)) (.goto fun _=>.inr (some false)))
          (.load (fun s=>(s.1,none)) (.goto fun _=>.inl M.main))))
  | some false => .pop (.inl M.k₀) (fun s a=>(s.1,a.map ei))
      (.push (.inr ()) (fun s=>s.2.getD false)
        (.load (fun s=>(s.1,none)) (.goto fun _=>.inr none)))
  | some true => .pop (.inr ()) (fun s a=>(s.1,a))
      (.branch (fun s=>s.2.isSome)
        (.push (.inl M.k₁) (fun s=>eo.symm (s.2.getD false))
          (.load (fun s=>(s.1,none)) (.goto fun _=>.inr (some true))))
        (.load (fun s=>(s.1,none)) .halt))
def program : Label M → TM2.Stmt (Alphabet M) (Label M) (State M) :=
  MachineEmbedding.program (some (.inr (some true))) M.m (extra M ei eo)
def machine : FinTM2 where
  K := Tape M
  kFin := by letI:=M.kFin; exact inferInstanceAs (Fintype (M.K ⊕ Unit))
  k₀ := .inl M.k₀
  k₁ := .inl M.k₁
  Γ := Alphabet M
  Γk₀Fin := M.Γk₀Fin
  Λ := Label M
  ΛFin := by letI:=M.ΛFin; exact inferInstanceAs (Fintype (M.Λ ⊕ Option Bool))
  main := .inr none
  σ := State M
  σFin := by letI:=M.σFin; exact inferInstanceAs (Fintype (M.σ × Option Bool))
  initialState := (M.initialState,none)
  m := program M ei eo
lemma finiteAlphabet (hm : MachineFiniteAlphabet.FiniteAlphabet M)
    (k : (machine M ei eo).K) : Finite ((machine M ei eo).Γ k) := by
  cases k with
  | inl k => exact hm k
  | inr k => exact inferInstanceAs (Finite Bool)

def readTapes (v acc : List Bool) : ∀k,List (Alphabet M k) :=
  MachineEmbedding.tapes (initList M (v.map ei.symm)).stk (fun _=>acc)
def readCfg (label : Option Bool) (v acc : List Bool) : (machine M ei eo).Cfg :=
  ⟨some (.inr label),(M.initialState,none),readTapes M ei v acc⟩
lemma read_input (v acc : List Bool) : (readTapes M ei v acc) (.inl M.k₀)=v.map ei.symm := by
  simp [readTapes,initList]
lemma payload_step (b : Bool) (v acc : List Bool) :
    (machine M ei eo).step (readCfg M ei eo (some false) (b::v) acc)=
      some (readCfg M ei eo none v (b::acc)) := by
  change some (TM2.stepAux (extra M ei eo (some false)) (M.initialState,none) (readTapes M ei (b::v) acc))=_
  simp only [extra,TM2.stepAux,read_input,List.map_cons,List.head?_cons,Option.map_some,
    Equiv.apply_symm_apply,Option.getD_some,List.tail_cons]
  congr 2
  funext k
  cases k with
  | inl k =>
    by_cases h:k=M.k₀
    · subst k; simp [readTapes,initList]
    · simp [readTapes,initList,Function.update,h]
  | inr k => cases k; simp [readTapes,Function.update]
open MinUncutGames.BinaryEncoding
lemma read_init (v : List Bool) :
    readCfg M ei eo none v []=initList (machine M ei eo) (v.map ei.symm) := by
  change TM2.Cfg.mk _ _ _=TM2.Cfg.mk _ _ _
  congr 1
  funext k
  cases k with
  | inl k =>
    by_cases h:k=M.k₀ <;> simp [readTapes,initList,h,machine]
    rfl
  | inr k => simp [readTapes,initList,machine]
end MinUncut.Costed.Framed

end
end

end OAI
end


