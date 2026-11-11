-- Prove2me | Definitions.Def_OAIQ222A002
-- name    : OAIQ222A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:06:08.228208+00:00
-- url     : https://prove2.me/theorems/617de864-cf04-4dbb-94ce-2edce4559cc6
-- title:
--   Definitions bundle OAIQ222A002 of the split of OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ExactQuantumFactoring.exact_quantum_factoring`, carved from OpenAI's openai/math development (OpenAI, *Exact quantum factoring over a fixed finite gate set (result family 279)*, OpenAI Math Release, September 25, 2026, result family 279, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 546 declarations of OpenAI's Lean: 390 definitions, 3 inductive types or structures and 153 theorems. The definitions and types are `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.addPackP`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.binaryPackP`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.compilePackP`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.declAtom`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.declAtomP`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.declGate`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.declGateP`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.declTag`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.declTagP`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.divPackP`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.faninPackP`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.graphInputCode`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.inputUltP`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.modPackP`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.mulPackP`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.nodePackP`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.padPackP`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.partialPackP`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.subPackP`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.binaryPack`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.compilePack`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.nodePack`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.padPack`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.partialPack`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.ultPack`, `OAI.ExactQuantumFactoring.BitArithmetic.CanonicalCyclic`, `OAI.ExactQuantumFactoring.BitArithmetic.ChildQueue.active`, `OAI.ExactQuantumFactoring.BitArithmetic.ChildQueue.kids`, `OAI.ExactQuantumFactoring.BitArithmetic.ChildQueue.liftWord`, `OAI.ExactQuantumFactoring.BitArithmetic.ChildQueue.predBits`, `OAI.ExactQuantumFactoring.BitArithmetic.ChildQueue.pushAll`, `OAI.ExactQuantumFactoring.BitArithmetic.ChildQueue.pushOne`, `OAI.ExactQuantumFactoring.BitArithmetic.ChildQueue.queue`, `OAI.ExactQuantumFactoring.BitArithmetic.ChildQueue.source`, `OAI.ExactQuantumFactoring.BitArithmetic.ChildQueue.wordMember`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top`, `OAI.ExactQuantumFactoring.BitArithmetic.binaryInputs`, `OAI.ExactQuantumFactoring.BitArithmetic.blockNet` and 353 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `QuantumFactoring_AIGBitArithmeticEmission`, `QuantumFactoring_AIGNetworkEmission`, `QuantumFactoring_AIGNetworkProcedure`, `QuantumFactoring_ArithmeticPredicates`, `QuantumFactoring_BitArithmetic`, `QuantumFactoring_BitArithmeticDivision`, `QuantumFactoring_BitStackAssociation`, `QuantumFactoring_BitStackBooleans`, `QuantumFactoring_BitStackListCode`, `QuantumFactoring_BitStackListOps`, `QuantumFactoring_BitStackOptions`, `QuantumFactoring_BitStackUnary`, `QuantumFactoring_BooleanFold`, `QuantumFactoring_BoundedStack`, `QuantumFactoring_ChildQueue`, `QuantumFactoring_CircuitEmissionModel`, `QuantumFactoring_CyclicCircuit`, `QuantumFactoring_CyclicPowerCircuit`, `QuantumFactoring_Emission`, `QuantumFactoring_EmissionFurther2`, `QuantumFactoring_ModularMultiply`, `QuantumFactoring_ModularPower`, `QuantumFactoring_NativeAIGAdd`, `QuantumFactoring_NativeAIGAddBounded`, `QuantumFactoring_NativeAIGAddProcedure`, `QuantumFactoring_NativeAIGAddWrapper`, `QuantumFactoring_NativeAIGBinaryInputs`, `QuantumFactoring_NativeAIGBoolean`, `QuantumFactoring_NativeAIGBounds`, `QuantumFactoring_NativeAIGCarry`, `QuantumFactoring_NativeAIGCarryProcedure`, `QuantumFactoring_NativeAIGDiv`, `QuantumFactoring_NativeAIGDivBounded`, `QuantumFactoring_NativeAIGDivOperations`, `QuantumFactoring_NativeAIGDivProcedure`, `QuantumFactoring_NativeAIGDivWrapper`, `QuantumFactoring_NativeAIGEqProcedure`, `QuantumFactoring_NativeAIGExtend`, `QuantumFactoring_NativeAIGFullAdder`, `QuantumFactoring_NativeAIGGateProcedure`, `QuantumFactoring_NativeAIGIf`, `QuantumFactoring_NativeAIGIfProcedure`, `QuantumFactoring_NativeAIGInputs`, `QuantumFactoring_NativeAIGKnownProcedure`, `QuantumFactoring_NativeAIGMod`, `QuantumFactoring_NativeAIGModWrapper`, `QuantumFactoring_NativeAIGModel`, `QuantumFactoring_NativeAIGMul`, `QuantumFactoring_NativeAIGMulBounded`, `QuantumFactoring_NativeAIGMulProcedure`, `QuantumFactoring_NativeAIGMulWrapper`, `QuantumFactoring_NativeAIGNot`, `QuantumFactoring_NativeAIGProcedures`, `QuantumFactoring_NativeAIGShift`, `QuantumFactoring_NativeAIGSub`, `QuantumFactoring_NativeAIGSubProcedure`, `QuantumFactoring_NativeAIGVectorBounds`, `QuantumFactoring_NativeAIGZipFold`, `QuantumFactoring_NativeAIGZipFoldProcedure`, `QuantumFactoring_NetworkEmissionBasic`, `QuantumFactoring_NetworkEmissionBounds`, `QuantumFactoring_NetworkEmissionPack`, `QuantumFactoring_NetworkEmissionPair`, `QuantumFactoring_NetworkEmissionProcedures`, `QuantumFactoring_NetworkEmissionRewire`, `QuantumFactoring_NetworkEmissionVector`, `QuantumFactoring_NodeControlCircuit`, `QuantumFactoring_WordBlocks`, `QuantumFactoring_WordNetworks`.
--
--   **Imports.** It imports the published bundle `Def_ExactQuantumFactoring`; the bundles `OAIQ222A000` and `OAIQ222A001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ222A004`.
-- source:
--   OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 279; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_ExactQuantumFactoring
import Definitions.Def_OAIQ222A000
import Definitions.Def_OAIQ222A001

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackBooleans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Procedure
variable {β : Type}

noncomputable def boolOr : Procedure (prodCode boolCode boolCode) boolCode
    (fun x=>x.1 || x.2) := ofBool₂ boolCode or
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackListCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

lemma code_le_of_mem (ea : α→List Bool) {a : α} {xs : List α} (h : a∈xs) :
    (ea a).length≤(listCode ea xs).length := by
  induction xs with
  | nil=>simp at h
  | cons b bs ih=>
    rw [List.mem_cons] at h
    rw [listCode_length_cons]
    rcases h with h|h
    · subst b;omega
    · have hh:=ih h;omega

end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackListOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

namespace Procedure
variable (ea : α→List Bool)

variable {ea} {eb : β→List Bool} {f : α→β}
noncomputable def listMap (d : α) (e : β) (p : Procedure ea eb f) :
    Procedure (listCode ea) (listCode eb) (List.map f) := by
  let step:=(listCons eb).comp ((p.comp (first ea (listCode eb))).pair (second ea (listCode eb)))
  let q:=Polynomial.X*(Polynomial.C 2*(Polynomial.X+p.bound)+Polynomial.C 2)+1+Polynomial.X
  let fold:=foldList d step q (by
    intro xs ys i
    change (listCode eb ((xs.take i).foldl (fun ys a=>f a::ys) ys)).length≤_
    rw [fold_map_cons_append]
    let L:=(listCode ea xs).length+(listCode eb ys).length
    have hh:=listCode_length_append eb ((xs.take i).map f).reverse ys
    rw [listCode_length_rev] at hh
    have hm:(listCode eb ((xs.take i).map f)).length≤(xs.take i).length*(2*(L+p.bound.eval L)+2)+1:=by
      apply listCode_length_map_bound
      intro a ha
      have hc:=(code_le_of_mem ea (List.mem_of_mem_take ha)).trans (Nat.le_add_right _ (listCode eb ys).length)
      have ho:=p.output_length_le a
      have hp:=eval_nat_mono p.bound hc
      dsimp only [L] at *
      omega
    have ht : (xs.take i).length≤L:=by
      have h1:=list_length_le_code ea xs
      simp only [List.length_take]
      dsimp [L];omega
    have hm':=(Nat.mul_le_mul_right (2*(L+p.bound.eval L)+2) ht)
    simp only [q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one]
    change (listCode eb (((xs.take i).map f).reverse++ys)).length≤L*(2*(L+p.bound.eval L)+2)+1+L
    dsimp only [L] at *
    omega)
  let start:=(identity (listCode ea)).pair (constant (listCode ea) (listCode eb) [])
  exact ((listReverse eb e).comp (fold.comp start)).congrFun (by
    intro xs
    change (xs.foldl (fun ys a=>f a::ys) []).reverse=xs.map f
    rw [fold_map_cons_append,List.append_nil,List.reverse_reverse])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

namespace Procedure

noncomputable def unaryMul : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x=>x.1*x.2) := by
  let step : Procedure (prodCode unaryCode unaryCode) (prodCode unaryCode unaryCode) addCounter:=
    ((first unaryCode unaryCode).pair unaryAdd).congrFun (by intro x;rfl)
  let rep:=step.iterate (Polynomial.X^2+Polynomial.X) (by
    intro n x i hi
    rw [addCounter_iterate]
    simp only [prodCode,pairBits_length,unaryCode,List.length_replicate,
      Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_X]
    have hm : x.1≤n+(2*x.1+1+x.2):=by omega
    have hii : i≤n+(2*x.1+1+x.2):=by omega
    have hh:=Nat.mul_le_mul hii hm
    nlinarith)
  let fst:=first unaryCode unaryCode
  let snd:=second unaryCode unaryCode
  let start:=fst.pair (snd.pair (constant (prodCode unaryCode unaryCode) unaryCode 0))
  exact ((second unaryCode unaryCode).comp (rep.comp start)).congrFun (by
    intro x
    change (addCounter^[x.1] (x.2,0)).2=x.1*x.2
    simp [addCounter_iterate])

noncomputable def unaryPred : Procedure unaryCode unaryCode (fun n=>n-1) :=
  (tail.precompose unaryCode).result (by intro n;simp [unaryCode])

noncomputable def unaryZero : Procedure unaryCode boolCode (fun n=>decide (n=0)) :=
  (isEmpty.precompose unaryCode).congrFun (by intro n;simp [unaryCode])

end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackOptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool}
noncomputable def optionSome (ea : α→List Bool) : Procedure ea (optionCode ea) some :=
  (prepend ea [true]).result (by intro a;rfl)
noncomputable def optionCases {f : Unit→β} {g : α→β}
    (p : Procedure emptyCode eb f) (q : Procedure ea eb g) :
    Procedure (optionCode ea) eb (fun x=>Sum.elim f g (optionView x)) :=
  ((casesSum p q).precompose optionView).congrEncoding
    (by intro x;cases x <;> rfl) (by intro x;rfl)
noncomputable def optionGet (ea : α→List Bool) (d : α) :
    Procedure (optionCode ea) ea (fun x=>x.getD d) :=
  (optionCases (constant emptyCode ea d) (identity ea)).congrFun
    (by intro x;cases x <;> rfl)
noncomputable def optionIsSome (ea : α→List Bool) :
    Procedure (optionCode ea) boolCode Option.isSome :=
  (optionCases (constant emptyCode boolCode false) (constant ea boolCode true)).congrFun
    (by intro x;cases x <;> rfl)
noncomputable def prodEq [DecidableEq α] [DecidableEq β]
    (pa : Procedure (prodCode ea ea) boolCode (fun x=>decide (x.1=x.2)))
    (pb : Procedure (prodCode eb eb) boolCode (fun x=>decide (x.1=x.2))) :
    Procedure (prodCode (prodCode ea eb) (prodCode ea eb)) boolCode
      (fun x=>decide (x.1=x.2)) := by
  let l:=first (prodCode ea eb) (prodCode ea eb)
  let r:=second (prodCode ea eb) (prodCode ea eb)
  let a:=pa.comp (((first ea eb).comp l).pair ((first ea eb).comp r))
  let b:=pb.comp (((second ea eb).comp l).pair ((second ea eb).comp r))
  exact (boolAnd.comp (a.pair b)).congrFun (by rintro ⟨⟨a,b⟩,⟨c,d⟩⟩;apply Bool.eq_iff_iff.mpr;simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,Prod.mk.injEq])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackAssociation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type} [DecidableEq α]
lemma assocFold_size (ea : α→List Bool) (eb : β→List Bool)
    (xs : List (α×β)) (s : α×Option β) :
    (prodCode ea (optionCode eb) (xs.foldl (fun s a=>assocStep (a,s)) s)).length≤
      (prodCode ea (optionCode eb) s).length+(listCode (prodCode ea eb) xs).length := by
  induction xs generalizing s with
  | nil=>simp
  | cons a as ih=>
    have hh:=ih (assocStep (a,s))
    have hb : (prodCode ea (optionCode eb) (assocStep (a,s))).length≤
        (prodCode ea (optionCode eb) s).length+2*(prodCode ea eb a).length+2:=by
      unfold assocStep
      split <;> simp only [prodCode,pairBits_length,optionCode,List.length_cons] <;> omega
    simp only [List.foldl_cons,listCode_length_cons]
    omega

namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool}
noncomputable def association (da : α) (db : β)
    (eqp : Procedure (prodCode ea ea) boolCode (fun x=>decide (x.1=x.2))) :
    Procedure (prodCode ea (listCode (prodCode ea eb))) (optionCode eb)
      (fun x=>assocLookup x.1 x.2) := by
  let ent:=prodCode ea eb
  let st:=prodCode ea (optionCode eb)
  let e:=first ent st
  let s:=second ent st
  let key:=(first ea (optionCode eb)).comp s
  let ky:=(first ea eb).comp e
  let value:=(second ea eb).comp e
  let upd:=conditional (eqp.comp (key.pair ky)) ((optionSome eb).comp value)
    ((second ea (optionCode eb)).comp s)
  let step : Procedure (prodCode ent st) st (assocStep (α:=α) (β:=β)):=
    (key.pair upd).congrFun (by intro x; simp only [assocStep,Function.comp_apply,decide_eq_true_eq])
  let fold:=foldList (da,db) step Polynomial.X (by
    intro xs s i
    have hh:=assocFold_size ea eb (xs.take i) s
    have ht:=listCode_length_take_le ent i xs
    simp only [Polynomial.eval_X]
    dsimp only [ent,st] at ht ⊢
    omega)
  let start:=((listReverse ent (da,db)).comp (second ea (listCode ent))).pair
    ((first ea (listCode ent)).pair (constant (prodCode ea (listCode ent)) (optionCode eb) none))
  exact ((second ea (optionCode eb)).comp (fold.comp start)).congrFun (by
    intro x
    change (x.2.reverse.foldl (fun s a=>assocStep (a,s)) (x.1,none)).2=assocLookup x.1 x.2
    rw [assocFold_reverse]
    cases assocLookup x.1 x.2 <;> rfl)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std Sat
def lookup (k : Key) : List (Key × ℕ) → Option ℕ
  | [] => none
  | (a,v)::as => if k=a then some v else lookup k as

def constant (r : Graph) (a : Ref) : Option Bool :=
  match r.decls[a.1]?.getD .zero with
  | .zero => some a.2
  | _ => none

def addGate (r : Graph) (a b : Ref) : Graph × Ref :=
  (⟨r.decls++[.gate a b],((a,b),r.decls.length)::r.cache⟩,(r.decls.length,false))
def go (r : Graph) (a b : Ref) : Graph × Ref :=
  match lookup (a,b) r.cache with
  | some i => (r,(i,false))
  | none =>
    match constant r a,constant r b with
    | some false,_ | _,some false => (r,(0,false))
    | some true,_ => (r,b)
    | _,some true => (r,a)
    | _,_ => if a.1=b.1 then
        if a.2=b.2 then (r,a) else (r,(0,false))
      else addGate r a b
def gate (r : Graph) (a b : Ref) : Graph × Ref :=
  if a.1<b.1 then go r a b else go r b a

end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGProcedures
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.countKnown_nil _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_cast _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_empty _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_get _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_length _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_push
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
abbrev keyCode := prodCode refCode refCode
abbrev entryCode := prodCode keyCode Nat.bits
def declView : Decl→Unit⊕(ℕ⊕Key)
  | .zero=>.inl ()
  | .atom i=>.inr (.inl i)
  | .gate a b=>.inr (.inr (a,b))
def declCode (d : Decl) := sumCode emptyCode (sumCode Nat.bits keyCode) (declView d)
def graphCode (g : Graph) := prodCode (listCode declCode) (listCode entryCode) (g.decls,g.cache)

namespace Emission
open Procedure
noncomputable def refEq : Procedure (prodCode refCode refCode) boolCode
    (fun x=>decide (x.1=x.2)) := prodEq binaryEq (ofBool₂ boolCode fun a b=>decide (a=b))
noncomputable def keyEq : Procedure (prodCode keyCode keyCode) boolCode
    (fun x=>decide (x.1=x.2)) := prodEq refEq refEq
noncomputable def lookupP : Procedure (prodCode keyCode (listCode entryCode)) (optionCode Nat.bits)
    (fun x=>lookup x.1 x.2) :=
  (association ((0,false),(0,false)) 0 keyEq).congrFun (by
    rintro ⟨k,es⟩
    induction es with
    | nil=>rfl
    | cons e es ih=>simp only [assocLookup,lookup,ih])
noncomputable def decls : Procedure graphCode (listCode declCode) Graph.decls :=
  ((first (listCode declCode) (listCode entryCode)).precompose (fun g : Graph=>(g.decls,g.cache)))
noncomputable def cache : Procedure graphCode (listCode entryCode) Graph.cache :=
  ((second (listCode declCode) (listCode entryCode)).precompose (fun g : Graph=>(g.decls,g.cache)))
noncomputable def packGraph : Procedure (prodCode (listCode declCode) (listCode entryCode)) graphCode
    (fun x=>Graph.mk x.1 x.2) := (identity _).result (by intro x;rfl)
noncomputable def atomDecl : Procedure Nat.bits declCode Decl.atom :=
  (prepend Nat.bits [true,false]).result (by intro x;rfl)
noncomputable def gateDecl : Procedure keyCode declCode (fun x=>Decl.gate x.1 x.2) :=
  (prepend keyCode [true,true]).result (by intro x;rfl)
noncomputable def zeroDecl : Procedure declCode boolCode (fun x=>decide (x=Decl.zero)) :=
  ((casesSum (Procedure.constant emptyCode boolCode true)
    (Procedure.constant (sumCode Nat.bits keyCode) boolCode false)).precompose declView).congrFun
      (by intro x;cases x <;> rfl)
noncomputable def singleton {α : Type} (ea : α→List Bool) : Procedure ea (listCode ea) (fun a=>[a]) :=
  ((listCons ea).comp ((identity ea).pair (Procedure.constant ea (listCode ea) [])))
noncomputable def addGateP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>addGate x.1 x.2.1 x.2.2) := by
  let r:=first graphCode keyCode
  let k:=second graphCode keyCode
  let ds:=decls.comp r
  let cs:=cache.comp r
  let sz:=(listLength declCode .zero).comp ds
  let nd:=(listAppend declCode .zero).comp (ds.pair ((singleton declCode).comp (gateDecl.comp k)))
  let nc:=(listCons entryCode).comp ((k.pair sz).pair cs)
  let nr:=sz.pair (Procedure.constant _ boolCode false)
  exact ((packGraph.comp (nd.pair nc)).pair nr).congrFun (by intro x;rfl)
noncomputable def constantP : Procedure (prodCode graphCode refCode) (optionCode boolCode)
    (fun x=>constant x.1 x.2) := by
  let r:=first graphCode refCode
  let a:=second graphCode refCode
  let idx:=(first Nat.bits boolCode).comp a
  let inv:=(second Nat.bits boolCode).comp a
  let d:=(listGet declCode .zero).comp (idx.pair (decls.comp r))
  exact (conditional (zeroDecl.comp d) ((optionSome boolCode).comp inv)
    (Procedure.constant _ (optionCode boolCode) none)).congrFun (by
      rintro ⟨g,⟨i,b⟩⟩
      simp only [Function.comp_apply,decide_eq_true_eq]
      have he : (g.decls.drop i).headD Decl.zero=g.decls[i]?.getD Decl.zero := by
        rw [List.headD_eq_head?_getD,List.head?_drop]
      rw [he]
      unfold constant
      cases g.decls[i]?.getD Decl.zero <;> simp)
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGGateProcedure
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.countKnown_nil _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_cast _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_empty _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_get _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_length _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_push
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG.Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def optionTrue : Procedure (optionCode boolCode) boolCode
    (fun x=>x=some true) :=
  (optionGet boolCode false).congrFun (by intro x;cases x with
    | none=>rfl
    | some b=>cases b <;> rfl)
noncomputable def optionFalse : Procedure (optionCode boolCode) boolCode
    (fun x=>x=some false) :=
  (optionCases (Procedure.constant emptyCode boolCode false) boolNot).congrFun
    (by intro x;cases x with
    | none=>rfl
    | some b=>cases b <;> rfl)
noncomputable def goP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>go x.1 x.2.1 x.2.2) := by
  let r:=first graphCode keyCode
  let k:=second graphCode keyCode
  let a:=(first refCode refCode).comp k
  let b:=(second refCode refCode).comp k
  let ca:=constantP.comp (r.pair a)
  let cb:=constantP.comp (r.pair b)
  let lk:=lookupP.comp (k.pair (cache.comp r))
  let z:=r.pair (Procedure.constant _ refCode (0,false))
  let ra:=r.pair a
  let rb:=r.pair b
  let cm:=(binaryEq.comp (((first Nat.bits boolCode).comp a).pair
    ((first Nat.bits boolCode).comp b)))
  let ci:=((ofBool₂ boolCode (fun a b=>decide (a=b))).comp
    (((second Nat.bits boolCode).comp a).pair ((second Nat.bits boolCode).comp b)))
  let twins:=conditional cm (conditional ci ra z) addGateP
  let rest:=conditional (boolOr.comp ((optionFalse.comp ca).pair (optionFalse.comp cb))) z
    (conditional (optionTrue.comp ca) rb (conditional (optionTrue.comp cb) ra twins))
  let hit:=r.pair (((optionGet Nat.bits 0).comp lk).pair (Procedure.constant _ boolCode false))
  exact (conditional ((optionIsSome Nat.bits).comp lk) hit rest).congrFun (by
    rintro ⟨g,⟨a,b⟩⟩
    simp only [Function.comp_apply]
    unfold go
    cases hl : lookup (a,b) g.cache with
    | some i=>simp
    | none=>
      simp only [Option.isSome_none,Bool.false_eq_true,↓reduceIte,Bool.or_eq_true,decide_eq_true_eq]
      cases ha : constant g a with
      | none=>
        cases hb : constant g b with
        | none=>simp
        | some bb=>cases bb <;> simp
      | some aa=>cases aa <;> cases hb : constant g b with
        | none=>simp
        | some bb=>cases bb <;> simp)
noncomputable def gateP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>gate x.1 x.2.1 x.2.2) := by
  let r:=first graphCode keyCode
  let k:=second graphCode keyCode
  let a:=(first refCode refCode).comp k
  let b:=(second refCode refCode).comp k
  let t:=binaryLt.comp (((first Nat.bits boolCode).comp a).pair ((first Nat.bits boolCode).comp b))
  exact (conditional t goP (goP.comp (r.pair (b.pair a)))).congrFun
    (by intro x;simp only [Function.comp_apply,decide_eq_true_eq,gate])
end ExactQuantumFactoring.NativeAIG.Emission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGBoolean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat
def orGate (r : Graph) (a b : Ref) : Graph×Ref :=
  let s:=gate r (notRef a) (notRef b)
  (s.1,notRef s.2)
def xorGate (r : Graph) (a b : Ref) : Graph×Ref :=
  let s:=gate r a b
  let t:=gate s.1 (notRef a) (notRef b)
  gate t.1 (notRef s.2) (notRef t.2)

namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def notRefP : Procedure refCode refCode notRef :=
  ((first Nat.bits boolCode).pair (boolNot.comp (second Nat.bits boolCode)))
noncomputable def orP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>orGate x.1 x.2.1 x.2.2) := by
  let r:=first graphCode keyCode
  let k:=second graphCode keyCode
  let a:=(first refCode refCode).comp k
  let b:=(second refCode refCode).comp k
  let s:=gateP.comp (r.pair ((notRefP.comp a).pair (notRefP.comp b)))
  exact (((first graphCode refCode).comp s).pair
    (notRefP.comp ((second graphCode refCode).comp s))).congrFun (by intro x;rfl)
noncomputable def xorP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>xorGate x.1 x.2.1 x.2.2) := by
  let k:=second graphCode keyCode
  let a:=(first refCode refCode).comp k
  let b:=(second refCode refCode).comp k
  let s:=gateP
  let t:=gateP.comp (((first graphCode refCode).comp s).pair
    ((notRefP.comp a).pair (notRefP.comp b)))
  exact (gateP.comp (((first graphCode refCode).comp t).pair
    ((notRefP.comp ((second graphCode refCode).comp s)).pair
      (notRefP.comp ((second graphCode refCode).comp t))))).congrFun (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGFullAdder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
abbrev Triple := Ref×Ref×Ref
def fullOut (r : Graph) (a b c : Ref) : Graph×Ref :=
  let s:=xorGate r a b
  xorGate s.1 s.2 c
def fullCarry (r : Graph) (a b c : Ref) : Graph×Ref :=
  let s:=xorGate r a b
  let t:=gate s.1 s.2 c
  let u:=gate t.1 a b
  orGate u.1 t.2 u.2
def full (r : Graph) (a b c : Ref) : Graph×(Ref×Ref) :=
  let o:=fullOut r a b c
  let k:=fullCarry o.1 a b c
  (k.1,(o.2,k.2))

end ExactQuantumFactoring.NativeAIG
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_Emission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

namespace Emission
open BitStackProgram BitStackProgram.Procedure
def tripleCode : Triple→List Bool:=prodCode refCode (prodCode refCode refCode)
noncomputable def fullOutP : Procedure (prodCode graphCode tripleCode) (prodCode graphCode refCode)
    (fun x=>fullOut x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let r:=first graphCode tripleCode
  let abc:=second graphCode tripleCode
  let a:=(first refCode keyCode).comp abc
  let bc:=(second refCode keyCode).comp abc
  let b:=(first refCode refCode).comp bc
  let c:=(second refCode refCode).comp bc
  let s:=xorP.comp (r.pair (a.pair b))
  exact (xorP.comp (((first graphCode refCode).comp s).pair
    (((second graphCode refCode).comp s).pair c))).congrFun (by intro x;rfl)
noncomputable def fullCarryP : Procedure (prodCode graphCode tripleCode) (prodCode graphCode refCode)
    (fun x=>fullCarry x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let r:=first graphCode tripleCode
  let abc:=second graphCode tripleCode
  let a:=(first refCode keyCode).comp abc
  let bc:=(second refCode keyCode).comp abc
  let b:=(first refCode refCode).comp bc
  let c:=(second refCode refCode).comp bc
  let s:=xorP.comp (r.pair (a.pair b))
  let t:=gateP.comp (((first graphCode refCode).comp s).pair
    (((second graphCode refCode).comp s).pair c))
  let u:=gateP.comp (((first graphCode refCode).comp t).pair (a.pair b))
  exact (orP.comp (((first graphCode refCode).comp u).pair
    (((second graphCode refCode).comp t).pair ((second graphCode refCode).comp u)))).congrFun (by intro x;rfl)
noncomputable def fullP : Procedure (prodCode graphCode tripleCode) (prodCode graphCode keyCode)
    (fun x=>full x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let o:=fullOutP
  let abc:=second graphCode tripleCode
  let k:=fullCarryP.comp (((first graphCode refCode).comp o).pair abc)
  exact (((first graphCode refCode).comp k).pair
    (((second graphCode refCode).comp o).pair ((second graphCode refCode).comp k))).congrFun (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
lemma countKnown_cons (r : Graph) (a : Ref) (as : List Ref) :
    countKnown r (a::as)=(if known r a then 1 else 0)+countKnown r as := by
  simp only [countKnown,List.filter_cons]
  split <;> simp_all [Nat.add_comm]

def addLoop : ℕ→Graph→List Ref→List Ref→ℕ→Ref→List Ref→Graph×List Ref
  | 0,r,_,_,_,_,out=>(r,out)
  | k+1,r,lhs,rhs,curr,cin,out=>
    let s:=full r ((lhs.drop curr).headD (0,false)) ((rhs.drop curr).headD (0,false)) cin
    addLoop k s.1 lhs rhs (curr+1) s.2.2 (out++[s.2.1])
def addBlast (r : Graph) (lhs rhs : List Ref) : Graph×List Ref :=
  addLoop lhs.length r lhs rhs 0 (0,false) []
def add (r : Graph) (lhs rhs : List Ref) : Graph×List Ref :=
  if countKnown r lhs < countKnown r rhs then addBlast r lhs rhs else addBlast r rhs lhs

end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGBounds
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.countKnown_nil _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_cast _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_empty _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_get _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_length _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_push
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def DeclBound (B : ℕ) : Decl→Prop
  | .zero=>True
  | .atom i=>i≤B
  | .gate a b=>a.1≤B ∧ b.1≤B
structure Bounded (B : ℕ) (r : Graph) : Prop where
  decl_length : r.decls.length≤B
  cache_length : r.cache.length≤B
  decls : ∀d∈r.decls,DeclBound B d
  cache : ∀e∈r.cache,e.1.1.1≤B ∧ e.1.2.1≤B ∧ e.2≤B
lemma DeclBound.mono {A B : ℕ} (h : A≤B) {d : Decl} (hd : DeclBound A d) : DeclBound B d := by
  cases d <;> simp only [DeclBound] at * <;> omega
lemma Bounded.mono {A B : ℕ} {r : Graph} (h : A≤B) (hr : Bounded A r) : Bounded B r :=
  ⟨hr.decl_length.trans h,hr.cache_length.trans h,fun d hd=>(hr.decls d hd).mono h,
    fun e he=>by have hh:=hr.cache e he;omega⟩
lemma lookup_bound {B : ℕ} {es : List (Key×ℕ)}
    (h : ∀e∈es,e.2≤B) (k : Key) {v : ℕ} (hv : lookup k es=some v) : v≤B := by
  induction es with
  | nil=>simp [lookup] at hv
  | cons e es ih=>
    simp only [lookup] at hv
    split_ifs at hv with he
    · cases hv;exact h e (by simp)
    · exact ih (fun a ha=>h a (by simp [ha])) hv
lemma addGate_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b : Ref)
    (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+1) (addGate r a b).1 ∧ (addGate r a b).2.1≤B+1 := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · simp only [addGate,List.length_append,List.length_cons,List.length_nil];have:=h.decl_length;omega
  · simp only [addGate,List.length_cons];have:=h.cache_length;omega
  · intro d hd
    simp only [addGate,List.mem_append,List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact (h.decls d hd).mono (by omega)
    · simp only [DeclBound];omega
  · intro e he
    simp only [addGate,List.mem_cons] at he
    rcases he with rfl | he
    · dsimp only;have:=h.decl_length;omega
    · have:=h.cache e he;omega
  · exact h.decl_length.trans (by omega)
lemma go_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b : Ref)
    (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+1) (go r a b).1 ∧ (go r a b).2.1≤B+1 := by
  have hg:=h.mono (Nat.le_add_right B 1)
  unfold go
  cases hl : lookup (a,b) r.cache with
  | some v=>
    dsimp only
    have hv:=lookup_bound (fun e he=>(h.cache e he).2.2) (a,b) hl
    exact ⟨hg,by omega⟩
  | none=>
    dsimp only
    cases hc : constant r a with
    | some a'=>
      cases a' <;> cases hd : constant r b with
      | none=>dsimp only;exact ⟨hg,by omega⟩
      | some b'=>cases b' <;> dsimp only <;> exact ⟨hg,by omega⟩
    | none=>
      cases hd : constant r b with
      | some b'=>cases b' <;> dsimp only <;> exact ⟨hg,by omega⟩
      | none=>
        dsimp only
        split_ifs
        · exact ⟨hg,ha.trans (by omega)⟩
        · exact ⟨hg,Nat.zero_le _⟩
        · exact addGate_bound h a b ha hb
lemma gate_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b : Ref)
    (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+1) (gate r a b).1 ∧ (gate r a b).2.1≤B+1 := by
  unfold gate;split <;> exact go_bound h _ _ (by omega) (by omega)
lemma orGate_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b : Ref)
    (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+1) (orGate r a b).1 ∧ (orGate r a b).2.1≤B+1 :=
  gate_bound h (notRef a) (notRef b) ha hb
lemma xorGate_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b : Ref)
    (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+3) (xorGate r a b).1 ∧ (xorGate r a b).2.1≤B+3 := by
  have hs:=gate_bound h a b ha hb
  have ht:=gate_bound hs.1 (notRef a) (notRef b) (by exact ha.trans (by omega)) (by exact hb.trans (by omega))
  have hh:=gate_bound ht.1 (notRef (gate r a b).2)
    (notRef (gate (gate r a b).1 (notRef a) (notRef b)).2) (by exact hs.2.trans (by omega)) ht.2
  exact hh
lemma fullOut_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b c : Ref)
    (ha : a.1≤B) (hb : b.1≤B) (hc : c.1≤B) :
    Bounded (B+6) (fullOut r a b c).1 ∧ (fullOut r a b c).2.1≤B+6 := by
  have hs:=xorGate_bound h a b ha hb
  exact xorGate_bound hs.1 _ c hs.2 (hc.trans (by omega))
lemma fullCarry_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b c : Ref)
    (ha : a.1≤B) (hb : b.1≤B) (hc : c.1≤B) :
    Bounded (B+6) (fullCarry r a b c).1 ∧ (fullCarry r a b c).2.1≤B+6 := by
  have hs:=xorGate_bound h a b ha hb
  have ht:=gate_bound hs.1 _ c hs.2 (hc.trans (by omega))
  have hu:=gate_bound ht.1 a b (ha.trans (by omega)) (hb.trans (by omega))
  exact orGate_bound hu.1 _ _ (ht.2.trans (by omega)) hu.2
lemma full_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b c : Ref)
    (ha : a.1≤B) (hb : b.1≤B) (hc : c.1≤B) :
    Bounded (B+12) (full r a b c).1 ∧
      (full r a b c).2.1.1≤B+12 ∧ (full r a b c).2.2.1≤B+12 := by
  have ho:=fullOut_bound h a b c ha hb hc
  have hk:=fullCarry_bound ho.1 a b c (ha.trans (by omega)) (hb.trans (by omega)) (hc.trans (by omega))
  exact ⟨hk.1,ho.2.trans (by omega),hk.2⟩
lemma refCode_length_bound {B : ℕ} (a : Ref) (ha : a.1≤B) : (refCode a).length≤2*B+2 := by
  have hn:=nat_bits_length_bound a.1
  simp only [refCode,prodCode,pairBits_length,boolCode,List.length_singleton]
  omega
lemma keyCode_length_bound {B : ℕ} (k : Key) (ha : k.1.1≤B) (hb : k.2.1≤B) :
    (keyCode k).length≤6*B+7 := by
  have h1:=refCode_length_bound k.1 ha
  have h2:=refCode_length_bound k.2 hb
  change (pairBits (refCode k.1) (refCode k.2)).length≤_
  rw [pairBits_length]
  omega
lemma declCode_length_bound {B : ℕ} (d : Decl) (hd : DeclBound B d) :
    (declCode d).length≤6*B+9 := by
  cases d with
  | zero=>simp [declCode,declView,sumCode,emptyCode]
  | atom i=>
    have hh:=nat_bits_length_bound i
    simp only [DeclBound] at hd
    simp only [declCode,declView,sumCode,List.length_cons];omega
  | gate a b=>
    have hh:=keyCode_length_bound (a,b) hd.1 hd.2
    simp only [declCode,declView,sumCode,List.length_cons];omega
lemma entryCode_length_bound {B : ℕ} (e : Key×ℕ) (h : e.1.1.1≤B ∧ e.1.2.1≤B ∧ e.2≤B) :
    (entryCode e).length≤13*B+15 := by
  have hk:=keyCode_length_bound e.1 h.1 h.2.1
  have hn:=nat_bits_length_bound e.2
  change (pairBits (keyCode e.1) e.2.bits).length≤_
  rw [pairBits_length]
  omega
lemma listCode_length_bound {α : Type} (e : α→List Bool) (xs : List α) (B : ℕ)
    (h : ∀x∈xs,(e x).length≤B) : (listCode e xs).length≤xs.length*(2*B+2)+1 := by
  simpa only [List.map_id] using listCode_length_map_bound e id xs B h
lemma graphCode_length_bound {B : ℕ} {r : Graph} (h : Bounded B r) :
    (graphCode r).length≤100*(B+1)^2 := by
  have hd:=listCode_length_bound declCode r.decls (6*B+9)
    (fun d hd=>declCode_length_bound d (h.decls d hd))
  have hc:=listCode_length_bound entryCode r.cache (13*B+15)
    (fun e he=>entryCode_length_bound e (h.cache e he))
  have hdm:=Nat.mul_le_mul_right (2*(6*B+9)+2) h.decl_length
  have hcm:=Nat.mul_le_mul_right (2*(13*B+15)+2) h.cache_length
  change (pairBits (listCode declCode r.decls) (listCode entryCode r.cache)).length≤_
  rw [pairBits_length]
  nlinarith
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGAddBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def RefsBound (B : ℕ) (xs : List Ref) : Prop := xs.length≤B ∧ ∀a∈xs,a.1≤B
lemma RefsBound.mono {A B : ℕ} {xs : List Ref} (h : A≤B) (hx : RefsBound A xs) : RefsBound B xs :=
  ⟨hx.1.trans h,fun a ha=>(hx.2 a ha).trans h⟩
lemma RefsBound.get {B : ℕ} {xs : List Ref} (hx : RefsBound B xs) (i : ℕ) :
    ((xs.drop i).headD (0,false)).1≤B := by
  cases he : (xs.drop i).head? with
  | none=>simp only [List.headD_eq_head?_getD,he,Option.getD_none];omega
  | some a=>
    rw [List.headD_eq_head?_getD,he,Option.getD_some]
    exact hx.2 a (List.mem_of_mem_drop (List.mem_of_head? he))
lemma RefsBound.push {B : ℕ} {xs : List Ref} (hx : RefsBound B xs) (a : Ref) (ha : a.1≤B+13) :
    RefsBound (B+13) (xs++[a]) := by
  refine ⟨?_,?_⟩
  · simp only [List.length_append,List.length_singleton];have:=hx.1;omega
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (hx.2 r hr).trans (by omega)
    · have he : r=a:=List.mem_singleton.mp hr
      simpa only [he] using ha
lemma refsCode_bound {B : ℕ} {xs : List Ref} (h : RefsBound B xs) :
    (listCode refCode xs).length≤10*(B+1)^2 := by
  have hh:=listCode_length_bound refCode xs (2*B+2) (fun a ha=>refCode_length_bound a (h.2 a ha))
  have hm : xs.length*(2*(2*B+2)+2)≤B*(2*(2*B+2)+2) := Nat.mul_le_mul_right _ h.1
  nlinarith
structure AddData where
  budget : ℕ
  graph : Graph
  lhs : List Ref
  rhs : List Ref
  curr : ℕ
  cin : Ref
  output : List Ref

def AddOK (s : AddData) : Prop :=
  Bounded s.budget s.graph ∧ RefsBound s.budget s.lhs ∧ RefsBound s.budget s.rhs ∧
  s.curr≤ s.budget ∧ s.cin.1≤ s.budget ∧ RefsBound s.budget s.output
abbrev AddState := {s : AddData // AddOK s}
def addStepData (s : AddData) : AddData :=
  let r:=full s.graph ((s.lhs.drop s.curr).headD (0,false)) ((s.rhs.drop s.curr).headD (0,false)) s.cin
  ⟨s.budget+13,r.1,s.lhs,s.rhs,s.curr+1,r.2.2,s.output++[r.2.1]⟩
lemma addStep_ok (s : AddState) : AddOK (addStepData s.val) := by
  obtain ⟨hg,hl,hr,hc,hci,ho⟩:=s.property
  have hh:=full_bound hg _ _ s.val.cin (hl.get s.val.curr) (hr.get s.val.curr) hci
  unfold AddOK
  dsimp only [addStepData]
  refine ⟨hh.1.mono (by omega),hl.mono (by omega),hr.mono (by omega),by omega,
    hh.2.2.trans (by omega),?_⟩
  exact ho.push _ (hh.2.1.trans (by omega))
def addStep (s : AddState) : AddState := ⟨addStepData s.val,addStep_ok s⟩
def addDataView (s : AddData) := (s.budget,(s.graph,(s.lhs,(s.rhs,(s.curr,(s.cin,s.output))))))
def addDataCode (s : AddData) : List Bool :=
  prodCode unaryCode (prodCode graphCode (prodCode (listCode refCode)
    (prodCode (listCode refCode) (prodCode Nat.bits (prodCode refCode (listCode refCode)))))) (addDataView s)
def addStateCode (s : AddState) : List Bool := addDataCode s.val
lemma addStateCode_bound (s : AddState) : (addStateCode s).length≤300*(s.val.budget+1)^2 := by
  obtain ⟨hg,hl,hr,hc,hci,ho⟩:=s.property
  have h1:=graphCode_length_bound hg
  have h2:=refsCode_bound hl
  have h3:=refsCode_bound hr
  have h4:=(nat_bits_length_bound s.val.curr).trans hc
  have h5:=refCode_length_bound s.val.cin hci
  have h6:=refsCode_bound ho
  simp only [refCode,prodCode,pairBits_length] at h5
  simp only [addStateCode,addDataCode,addDataView,prodCode,pairBits_length,unaryCode,List.length_replicate]
  nlinarith
lemma budget_le_code (s : AddState) : s.val.budget≤(addStateCode s).length := by
  simp only [addStateCode,addDataCode,addDataView,prodCode,pairBits_length,unaryCode,List.length_replicate]
  omega
lemma addStep_budget (s : AddState) : (addStep s).val.budget=s.val.budget+13 := rfl
lemma addStep_iterate_budget (s : AddState) (k : ℕ) :
    ((addStep^[k]) s).val.budget=s.val.budget+13*k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,addStep_budget];omega
lemma addStep_iterate_loop (s : AddState) (k : ℕ) :
    (((addStep^[k]) s).val.graph,((addStep^[k]) s).val.output)=
      addLoop k s.val.graph s.val.lhs s.val.rhs s.val.curr s.val.cin s.val.output := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>
    rw [Function.iterate_succ_apply,ih]
    rfl
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGAddProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
namespace Emission
abbrev addTail5 := prodCode refCode (listCode refCode)
abbrev addTail4 := prodCode Nat.bits addTail5
abbrev addTail3 := prodCode (listCode refCode) addTail4
abbrev addTail2 := prodCode (listCode refCode) addTail3
abbrev addTail1 := prodCode graphCode addTail2
abbrev addPayload := prodCode unaryCode addTail1
noncomputable def addViewP : Procedure addDataCode addPayload addDataView :=
  ((identity addPayload).precompose addDataView)
noncomputable def packAddP : Procedure addPayload addDataCode
    (fun x=>AddData.mk x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2) :=
  (identity addPayload).result (by intro x;rfl)
noncomputable def addGraphP : Procedure addDataCode graphCode AddData.graph :=
  (first graphCode addTail2).comp ((second unaryCode addTail1).comp addViewP)
noncomputable def addLhsP : Procedure addDataCode (listCode refCode) AddData.lhs :=
  (first (listCode refCode) addTail3).comp ((second graphCode addTail2).comp
    ((second unaryCode addTail1).comp addViewP))
noncomputable def addRhsP : Procedure addDataCode (listCode refCode) AddData.rhs :=
  (first (listCode refCode) addTail4).comp ((second (listCode refCode) addTail3).comp
    ((second graphCode addTail2).comp ((second unaryCode addTail1).comp addViewP)))
noncomputable def addCurrP : Procedure addDataCode Nat.bits AddData.curr :=
  (first Nat.bits addTail5).comp ((second (listCode refCode) addTail4).comp
    ((second (listCode refCode) addTail3).comp ((second graphCode addTail2).comp
      ((second unaryCode addTail1).comp addViewP))))
noncomputable def addCinP : Procedure addDataCode refCode AddData.cin :=
  (first refCode (listCode refCode)).comp ((second Nat.bits addTail5).comp
    ((second (listCode refCode) addTail4).comp ((second (listCode refCode) addTail3).comp
      ((second graphCode addTail2).comp ((second unaryCode addTail1).comp addViewP)))))
noncomputable def addOutputP : Procedure addDataCode (listCode refCode) AddData.output :=
  (second refCode (listCode refCode)).comp ((second Nat.bits addTail5).comp
    ((second (listCode refCode) addTail4).comp ((second (listCode refCode) addTail3).comp
      ((second graphCode addTail2).comp ((second unaryCode addTail1).comp addViewP)))))
noncomputable def addStepDataP : Procedure addDataCode addDataCode addStepData := by
  let budget:=(first unaryCode addTail1).comp addViewP
  let newBudget:=unaryAdd.comp (budget.pair (Procedure.constant _ unaryCode 13))
  let lhsBit:=(listGet refCode (0,false)).comp (addCurrP.pair addLhsP)
  let rhsBit:=(listGet refCode (0,false)).comp (addCurrP.pair addRhsP)
  let s:=fullP.comp (addGraphP.pair (lhsBit.pair (rhsBit.pair addCinP)))
  let g:=(first graphCode keyCode).comp s
  let refs:=(second graphCode keyCode).comp s
  let outBit:=(first refCode refCode).comp refs
  let cin:=(second refCode refCode).comp refs
  let out:=(listAppend refCode (0,false)).comp (addOutputP.pair ((singleton refCode).comp outBit))
  exact (packAddP.comp (newBudget.pair (g.pair (addLhsP.pair (addRhsP.pair
    ((successor.comp addCurrP).pair (cin.pair out))))))).congrFun (by intro s;rfl)
noncomputable def addStepP : Procedure addStateCode addStateCode addStep :=
  (addStepDataP.precompose Subtype.val).result (by intro s;rfl)
noncomputable def addIterationP : Procedure (prodCode unaryCode addStateCode) addStateCode
    (fun x=>(addStep^[x.1]) x.2) :=
  addStepP.iterate (Polynomial.C 50700*(Polynomial.X+1)^2) (by
    intro n s i hi
    have hh:=addStateCode_bound ((addStep^[i]) s)
    rw [addStep_iterate_budget] at hh
    have hb:=budget_le_code s
    have hb' : s.val.budget+13*i+1≤13*(n+(addStateCode s).length+1):=by omega
    have hs:=Nat.pow_le_pow_left hb' 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    nlinarith)
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGKnownProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
namespace Emission
noncomputable def knownP : Procedure (prodCode graphCode refCode) boolCode
    (fun x=>known x.1 x.2) := by
  let r:=first graphCode refCode
  let a:=second graphCode refCode
  let idx:=(first Nat.bits boolCode).comp a
  let d:=(listGet declCode .zero).comp (idx.pair (decls.comp r))
  exact (zeroDecl.comp d).congrFun (by
    rintro ⟨g,⟨i,b⟩⟩
    simp only [Function.comp_apply]
    have he : (g.decls.drop i).headD Decl.zero=g.decls[i]?.getD Decl.zero := by
      rw [List.headD_eq_head?_getD,List.head?_drop]
    simp only [he]
    unfold known
    cases g.decls[i]?.getD Decl.zero <;> rfl)
def knownStep (x : Ref×(Graph×ℕ)) : Graph×ℕ :=
  (x.2.1,x.2.2+(if known x.2.1 x.1 then 1 else 0))
lemma knownStep_fold (xs : List Ref) (g : Graph) (acc : ℕ) :
    xs.foldl (fun s a=>knownStep (a,s)) (g,acc)=(g,acc+countKnown g xs) := by
  induction xs generalizing acc with
  | nil=>simp
  | cons a as ih=>
    rw [List.foldl_cons]
    change as.foldl (fun s a=>knownStep (a,s)) (g,acc+(if known g a then 1 else 0))=_
    rw [ih,countKnown_cons,Nat.add_assoc]
noncomputable def knownStepP : Procedure (prodCode refCode (prodCode graphCode unaryCode))
    (prodCode graphCode unaryCode) knownStep := by
  let a:=first refCode (prodCode graphCode unaryCode)
  let rest:=second refCode (prodCode graphCode unaryCode)
  let g:=(first graphCode unaryCode).comp rest
  let acc:=(second graphCode unaryCode).comp rest
  let test:=knownP.comp (g.pair a)
  exact (conditional test (g.pair (unarySuccessor.comp acc)) rest).congrFun (by
    intro x
    unfold knownStep
    split <;> simp_all)
noncomputable def countKnownUnaryP : Procedure (prodCode graphCode (listCode refCode)) unaryCode
    (fun x=>countKnown x.1 x.2) := by
  let fold:=foldList (0,false) knownStepP (Polynomial.C 2*Polynomial.X) (by
    rintro xs ⟨g,acc⟩ i
    rw [knownStep_fold]
    have hh : countKnown g (xs.take i)≤xs.length :=
      (List.length_filter_le _ _).trans (by simp only [List.length_take];omega)
    have hc:=list_length_le_code refCode xs
    simp only [prodCode,pairBits_length,unaryCode,List.length_replicate,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega)
  let g:=first graphCode (listCode refCode)
  let xs:=second graphCode (listCode refCode)
  exact ((second graphCode unaryCode).comp (fold.comp (xs.pair
    (g.pair (Procedure.constant _ unaryCode 0))))).congrFun (by
      intro x
      change (x.2.foldl (fun s a=>knownStep (a,s)) (x.1,0)).2=countKnown x.1 x.2
      rw [knownStep_fold,Nat.zero_add])
noncomputable def countKnownP : Procedure (prodCode graphCode (listCode refCode)) Nat.bits
    (fun x=>countKnown x.1 x.2) := unaryToBits.comp countKnownUnaryP
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGAddWrapper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def initializeAddData (s : AddData) : AddData:=⟨s.budget,s.graph,s.lhs,s.rhs,0,(0,false),[]⟩
lemma initializeAdd_ok (s : AddState) : AddOK (initializeAddData s.val) := by
  exact ⟨s.property.1,s.property.2.1,s.property.2.2.1,Nat.zero_le _,Nat.zero_le _,
    ⟨Nat.zero_le _,by intro a ha;cases ha⟩⟩
def initializeAdd (s : AddState) : AddState:=⟨initializeAddData s.val,initializeAdd_ok s⟩
def swapAddData (s : AddData) : AddData:=⟨s.budget,s.graph,s.rhs,s.lhs,s.curr,s.cin,s.output⟩
def swapAdd (s : AddState) : AddState:=⟨swapAddData s.val,
  ⟨s.property.1,s.property.2.2.1,s.property.2.1,s.property.2.2.2⟩⟩
def addBlastState (s : AddState) : AddState:=(addStep^[s.val.lhs.length]) (initializeAdd s)
def addState (s : AddState) : AddState:=
  if countKnown s.val.graph s.val.lhs < countKnown s.val.graph s.val.rhs then
    addBlastState s else addBlastState (swapAdd s)
lemma addBlastState_value (s : AddState) :
    ((addBlastState s).val.graph,(addBlastState s).val.output)=addBlast s.val.graph s.val.lhs s.val.rhs :=
  addStep_iterate_loop (initializeAdd s) s.val.lhs.length
lemma addState_value (s : AddState) :
    ((addState s).val.graph,(addState s).val.output)=add s.val.graph s.val.lhs s.val.rhs := by
  unfold addState add
  split <;> exact addBlastState_value _
lemma addBlastState_budget (s : AddState) :
    (addBlastState s).val.budget=s.val.budget+13*s.val.lhs.length :=
  addStep_iterate_budget (initializeAdd s) s.val.lhs.length

namespace Emission
noncomputable def initializeAddDataP : Procedure addDataCode addDataCode initializeAddData := by
  let b:=(first unaryCode addTail1).comp addViewP
  exact (packAddP.comp (b.pair (addGraphP.pair (addLhsP.pair (addRhsP.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).congrFun (by intro x;rfl)
noncomputable def initializeAddP : Procedure addStateCode addStateCode initializeAdd :=
  (initializeAddDataP.precompose (fun s:AddState=>s.val)).result (by intro s;rfl)
noncomputable def swapAddDataP : Procedure addDataCode addDataCode swapAddData := by
  let b:=(first unaryCode addTail1).comp addViewP
  exact (packAddP.comp (b.pair (addGraphP.pair (addRhsP.pair
    (addLhsP.pair (addCurrP.pair (addCinP.pair addOutputP))))))).congrFun (by intro x;rfl)
noncomputable def swapAddP : Procedure addStateCode addStateCode swapAdd :=
  (swapAddDataP.precompose (fun s:AddState=>s.val)).result (by intro s;rfl)
noncomputable def addBlastStateP : Procedure addStateCode addStateCode addBlastState :=
  addIterationP.comp (((listUnaryLength refCode (0,false)).comp
    (addLhsP.precompose (fun s:AddState=>s.val))).pair initializeAddP)
noncomputable def addStateP : Procedure addStateCode addStateCode addState := by
  let g:=addGraphP.precompose (fun s:AddState=>s.val)
  let lhs:=addLhsP.precompose (fun s:AddState=>s.val)
  let rhs:=addRhsP.precompose (fun s:AddState=>s.val)
  let lk:=countKnownP.comp (g.pair lhs)
  let rk:=countKnownP.comp (g.pair rhs)
  let test:=binaryLt.comp (lk.pair rk)
  exact (conditional test addBlastStateP (addBlastStateP.comp swapAddP)).congrFun (by
    intro s;unfold addState
    split <;> simp_all)
noncomputable def addP : Procedure addStateCode (prodCode graphCode (listCode refCode))
    (fun s=>add s.val.graph s.val.lhs s.val.rhs) :=
  (((addGraphP.pair addOutputP).precompose (fun s:AddState=>s.val)).comp addStateP).congrFun addState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission

def pair (a b : Data) : Data:=
  let f:=pairIndex a.inputs (a.inputs+a.nodes.length)
  ⟨a.inputs,a.nodes++b.nodes.map (Node.map f),a.outputs++b.outputs.map f⟩
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionProcedures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

namespace Emission
noncomputable def nodeTagP : Procedure nodeCode Nat.bits (fun o=>(nodeView o).1):=
  (first Nat.bits _).comp nodeViewP
noncomputable def nodeRhsP : Procedure nodeCode Nat.bits (fun o=>(nodeView o).2.2.2):=
  (second Nat.bits Nat.bits).comp ((second boolCode _).comp ((second Nat.bits _).comp nodeViewP))
noncomputable def nodeConstP : Procedure boolCode nodeCode Node.constant:=
  ((Procedure.constant boolCode Nat.bits 0).pair ((identity boolCode).pair
    ((Procedure.constant boolCode Nat.bits 0).pair (Procedure.constant boolCode Nat.bits 0)))).result (by intro b;rfl)
noncomputable def nodeCopyP : Procedure Nat.bits nodeCode Node.copy:=
  ((Procedure.constant Nat.bits Nat.bits 1).pair ((Procedure.constant Nat.bits boolCode false).pair
    ((identity Nat.bits).pair (Procedure.constant Nat.bits Nat.bits 0)))).result (by intro i;rfl)
noncomputable def nodeNegP : Procedure Nat.bits nodeCode Node.neg:=
  ((Procedure.constant Nat.bits Nat.bits 2).pair ((Procedure.constant Nat.bits boolCode false).pair
    ((identity Nat.bits).pair (Procedure.constant Nat.bits Nat.bits 0)))).result (by intro i;rfl)
noncomputable def nodeConjP : Procedure (prodCode Nat.bits Nat.bits) nodeCode (fun x=>Node.conj x.1 x.2):=
  ((Procedure.constant _ Nat.bits 3).pair ((Procedure.constant _ boolCode false).pair (identity _))).result (by intro x;rfl)

noncomputable def nodeMapWith {α : Type} {ea : α→List Bool} {f : α→ℕ→ℕ}
    (p : Procedure (prodCode ea Nat.bits) Nat.bits (fun x=>f x.1 x.2)) :
    Procedure (prodCode ea nodeCode) nodeCode (fun x=>x.2.map (f x.1)) := by
  let a:=first ea nodeCode
  let o:=second ea nodeCode
  let tag:=nodeTagP.comp o
  let isTag:=(fun k=>binaryEq.comp (tag.pair (Procedure.constant _ Nat.bits k)))
  let lhs:=p.comp (a.pair (nodeLhsP.comp o))
  let rhs:=p.comp (a.pair (nodeRhsP.comp o))
  let b:=nodeConstP.comp (nodeBoolP.comp o)
  let c:=nodeCopyP.comp lhs
  let n:=nodeNegP.comp lhs
  let g:=nodeConjP.comp (lhs.pair rhs)
  exact (conditional (isTag 0) b (conditional (isTag 1) c (conditional (isTag 2) n g))).congrFun (by
    rintro ⟨a,o⟩;cases o <;> rfl)
noncomputable def compP : Procedure (prodCode dataCode dataCode) dataCode
    (fun x=>comp x.1 x.2) := by
  let a:=first dataCode dataCode
  let b:=second dataCode dataCode
  let env:=(dataWidthP.comp a).pair (dataOutputsP.comp a)
  let ns:=(listMapWith (f:=fun (e : ℕ×List ℕ) (o : Node)=>o.map (attachRawIndex e.1 e.2)) (Node.constant false) (Node.constant false) (nodeMapWith (f:=fun (e : ℕ×List ℕ) i=>attachRawIndex e.1 e.2 i) attachIndexP)).comp
    (env.pair (dataNodesP.comp b))
  let nodes:=(listAppend nodeCode (.constant false)).comp ((dataNodesP.comp a).pair ns)
  let outs:=(listMapWith (f:=fun (e : ℕ×List ℕ) i=>attachRawIndex e.1 e.2 i) 0 0 attachIndexP).comp (env.pair (dataOutputsP.comp b))
  exact (dataPackP.comp ((dataInputP.comp a).pair (nodes.pair outs))).congrFun (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

namespace Emission
noncomputable def nodeP : Procedure (prodCode Nat.bits nodeCode) dataCode (fun x=>node x.1 x.2):=by
  let n:=first Nat.bits nodeCode
  let o:=second Nat.bits nodeCode
  let ns:=(listCons nodeCode).comp (o.pair (Procedure.constant _ (listCode nodeCode) []))
  let os:=(listCons Nat.bits).comp (n.pair (Procedure.constant _ (listCode Nat.bits) []))
  exact (dataPackP.comp (n.pair (ns.pair os))).congrFun (by intro x;rfl)
noncomputable def pairIndexP : Procedure (prodCode (prodCode Nat.bits Nat.bits) Nat.bits) Nat.bits
    (fun x=>pairIndex x.1.1 x.1.2 x.2):=by
  let e:=first (prodCode Nat.bits Nat.bits) Nat.bits
  let n:=(first Nat.bits Nat.bits).comp e
  let w:=(second Nat.bits Nat.bits).comp e
  let i:=second (prodCode Nat.bits Nat.bits) Nat.bits
  exact (conditional (binaryLt.comp (i.pair n)) i (binaryAdd.comp (w.pair (binarySub.comp (i.pair n))))).congrFun (by
    intro x;unfold pairIndex;split <;> simp_all)
noncomputable def pairP : Procedure (prodCode dataCode dataCode) dataCode (fun x=>pair x.1 x.2):=by
  let a:=first dataCode dataCode
  let b:=second dataCode dataCode
  let env:=(dataInputP.comp a).pair (dataWidthP.comp a)
  let mp:=nodeMapWith (f:=fun (e : ℕ×ℕ) i=>pairIndex e.1 e.2 i) pairIndexP
  let ns:=(listMapWith (f:=fun (e : ℕ×ℕ) (o : Node)=>o.map (pairIndex e.1 e.2)) (.constant false) (.constant false) mp).comp
    (env.pair (dataNodesP.comp b))
  let os:=(listMapWith (f:=fun (e : ℕ×ℕ) i=>pairIndex e.1 e.2 i) 0 0 pairIndexP).comp
    (env.pair (dataOutputsP.comp b))
  let nn:=(listAppend nodeCode (.constant false)).comp ((dataNodesP.comp a).pair ns)
  let oo:=(listAppend Nat.bits 0).comp ((dataOutputsP.comp a).pair os)
  exact (dataPackP.comp ((dataInputP.comp a).pair (nn.pair oo))).congrFun (by intro x;rfl)
noncomputable def constantP : Procedure (prodCode Nat.bits boolCode) dataCode (fun x=>constant x.1 x.2):=
  (nodeP.comp ((first Nat.bits boolCode).pair (nodeConstP.comp (second Nat.bits boolCode)))).congrFun (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

lemma pair_valid {a b : Data} (ha : a.Valid) (hb : b.Valid) (he : a.inputs=b.inputs) : (pair a b).Valid:=by
  have hw : (pair a b).width=a.width+b.nodes.length:=by simp [Data.width,pair,Nat.add_assoc]
  have hf : ∀i,i≤b.width→pairIndex a.inputs a.width i≤(pair a b).width:=by
    intro i hi
    rw [hw]
    apply pairIndex_bound
    · exact Nat.le_add_right _ _
    · simpa only [Data.width,←he] using hi
  constructor
  · intro o ho
    simp only [pair,List.mem_append,List.mem_map] at ho
    rcases ho with ho|⟨p,hp,rfl⟩
    · exact (ha.1 _ ho).mono (by rw [hw];omega)
    · exact (hb.1 _ hp).map _ hf
  · intro i hi
    simp only [pair,List.mem_append,List.mem_map] at hi
    rcases hi with hi|⟨j,hj,rfl⟩
    · exact (ha.2 _ hi).trans (by rw [hw];omega)
    · exact hf _ (hb.2 _ hj)
lemma pair_mass (a b : Data) : (pair a b).mass≤a.mass+b.mass:=by
  simp only [Data.mass,Data.width,pair,List.length_append,List.length_map];omega
lemma listCode_length_bound {α : Type} (ea : α→List Bool) (xs : List α) (B : ℕ)
    (h : ∀a∈xs,(ea a).length≤B) : (listCode ea xs).length≤xs.length*(2*B+2)+1:=by
  induction xs with
  | nil=>simp [listCode]
  | cons a xs ih=>
    have ha:=h a (by simp)
    have hh:=ih (by intro b hb;exact h b (by simp [hb]))
    simp only [listCode_length_cons,List.length_cons]
    nlinarith
lemma nodeCode_bound {o : Node} {B : ℕ} (h : o.Bound B) : (nodeCode o).length≤8*B+30:=by
  have h0 : (Nat.bits 0).length=0:=rfl
  have h1 : (Nat.bits 1).length=1:=rfl
  have h2 : (Nat.bits 2).length=2:=rfl
  have h3 : (Nat.bits 3).length=2:=rfl
  cases o <;> simp only [Node.Bound] at h
  · simp only [nodeCode,nodePayload,nodeView,prodCode,pairBits_length,boolCode,List.length_singleton,h0]
    omega
  · rename_i i
    have hi:=(nat_bits_length_bound i).trans h
    simp only [nodeCode,nodePayload,nodeView,prodCode,pairBits_length,boolCode,List.length_singleton,h0,h1]
    omega
  · rename_i i
    have hi:=(nat_bits_length_bound i).trans h
    simp only [nodeCode,nodePayload,nodeView,prodCode,pairBits_length,boolCode,List.length_singleton,h0,h2]
    omega
  · rename_i i j
    have hi:=(nat_bits_length_bound i).trans h.1
    have hj:=(nat_bits_length_bound j).trans h.2
    simp only [nodeCode,nodePayload,nodeView,prodCode,pairBits_length,boolCode,List.length_singleton,h3]
    omega
lemma dataCode_bound {a : Data} {B : ℕ} (ha : a.Valid) (hm : a.mass≤B) :
    (dataCode a).length≤100*(B+1)^2:=by
  have hn : a.inputs≤B:=by dsimp [Data.mass,Data.width] at hm;omega
  have hw : a.width≤B:=by dsimp [Data.mass] at hm;omega
  have hnl : a.nodes.length≤B:=by dsimp [Data.mass,Data.width] at hm;omega
  have hol : a.outputs.length≤B:=by dsimp [Data.mass,Data.width] at hm;omega
  have hb:=(nat_bits_length_bound a.inputs).trans hn
  have hns:=listCode_length_bound nodeCode a.nodes (8*B+30) (fun o ho=>nodeCode_bound ((ha.1 _ ho).mono hw))
  have hos:=listCode_length_bound Nat.bits a.outputs B (fun i hi=>(nat_bits_length_bound i).trans ((ha.2 _ hi).trans hw))
  simp only [dataCode,dataPayload,dataView,prodCode,pairBits_length]
  have h1:=Nat.mul_le_mul_right (2*(8*B+30)+2) hnl
  have h2:=Nat.mul_le_mul_right (2*B+2) hol
  nlinarith
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionPack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
def pairPack (a b : Pack) : Pack:=
  ⟨⟨a.val.budget+b.val.budget,if a.val.value.inputs=b.val.value.inputs then pair a.val.value b.val.value else a.val.value⟩,by
    split
    · rename_i h
      exact ⟨pair_valid a.property.1 b.property.1 h,(pair_mass _ _).trans (Nat.add_le_add a.property.2 b.property.2)⟩
    · exact ⟨a.property.1,a.property.2.trans (Nat.le_add_right _ _)⟩⟩
lemma packCode_bound (s : Pack) : (packCode s).length≤104*(s.val.budget+1)^2:=by
  have hh:=dataCode_bound s.property.1 s.property.2
  simp only [packCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
  nlinarith [Nat.zero_le s.val.budget]
lemma packBudget_le_code (s : Pack) : s.val.budget≤(packCode s).length:=by
  simp only [packCode,prodCode,pairBits_length,unaryCode,List.length_replicate];omega
lemma packBudgets_le_code (xs : List Pack) : (xs.map (fun s=>s.val.budget)).sum≤(listCode packCode xs).length:=by
  induction xs with
  | nil=>simp
  | cons s xs ih=>
    have hh:=packBudget_le_code s
    simp only [List.map_cons,List.sum_cons,listCode_length_cons];omega
lemma fold_budget (f : Pack→Pack→Pack) (h : ∀a b,(f a b).val.budget=a.val.budget+b.val.budget)
    (xs : List Pack) (a : Pack) : (xs.foldl f a).val.budget=a.val.budget+(xs.map (fun s=>s.val.budget)).sum:=by
  induction xs generalizing a with
  | nil=>simp
  | cons s xs ih=>rw [List.foldl_cons,ih,h,List.map_cons,List.sum_cons];omega

def emptyPack : Pack:=selectPack 0 [] (by simp)
namespace Emission
noncomputable def packViewP : Procedure packCode (prodCode unaryCode dataCode)
    (fun s=>(s.val.budget,s.val.value)):=(identity _).precompose _
noncomputable def packBudgetP : Procedure packCode unaryCode (fun s=>s.val.budget):=
  (first unaryCode dataCode).comp packViewP
noncomputable def packValueP : Procedure packCode dataCode (fun s=>s.val.value):=
  (second unaryCode dataCode).comp packViewP
noncomputable def pairPackP : Procedure (prodCode packCode packCode) packCode (fun x=>pairPack x.1 x.2):=by
  let a:=first packCode packCode
  let b:=second packCode packCode
  let av:=packValueP.comp a
  let bv:=packValueP.comp b
  let test:=binaryEq.comp ((dataInputP.comp av).pair (dataInputP.comp bv))
  let val:=conditional test (pairP.comp (av.pair bv)) av
  let bud:=unaryAdd.comp ((packBudgetP.comp a).pair (packBudgetP.comp b))
  exact (bud.pair val).result (by intro x;unfold pairPack packCode;split <;> simp_all)
noncomputable def compPackP : Procedure (prodCode packCode packCode) packCode (fun x=>compPack x.1 x.2):=by
  let a:=first packCode packCode
  let b:=second packCode packCode
  let av:=packValueP.comp a
  let bv:=packValueP.comp b
  let len:=(listLength Nat.bits 0).comp (dataOutputsP.comp av)
  let test:=binaryEq.comp (len.pair (dataInputP.comp bv))
  let val:=conditional test (compP.comp (av.pair bv)) av
  let bud:=unaryAdd.comp ((packBudgetP.comp a).pair (packBudgetP.comp b))
  exact (bud.pair val).result (by intro x;unfold compPack packCode;split <;> simp_all)
noncomputable def foldPack {f : Pack→Pack→Pack}
    (h : ∀a b,(f a b).val.budget=a.val.budget+b.val.budget)
    (p : Procedure (prodCode packCode packCode) packCode (fun x=>f x.1 x.2)) :
    Procedure (prodCode (listCode packCode) packCode) packCode (fun x=>x.1.foldl f x.2):=
  foldList emptyPack (p.comp ((second packCode packCode).pair (first packCode packCode)))
    (Polynomial.C 104*(Polynomial.X+1)^2) (by
      intro xs a i
      have hh:=packCode_bound ((xs.take i).foldl f a)
      rw [fold_budget f h] at hh
      have hb:=packBudget_le_code a
      have hx:=(packBudgets_le_code (xs.take i)).trans (listCode_length_take_le packCode i xs)
      have hp:=Nat.pow_le_pow_left (by omega :
        a.val.budget+((xs.take i).map (fun s=>s.val.budget)).sum+1≤
          (listCode packCode xs).length+(packCode a).length+1) 2
      simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
        Polynomial.eval_X,Polynomial.eval_one]
      change (packCode ((xs.take i).foldl f a)).length≤104*((listCode packCode xs).length+(packCode a).length+1)^2
      exact hh.trans (Nat.mul_le_mul_left _ hp))
noncomputable def foldPairP : Procedure (prodCode (listCode packCode) packCode) packCode
    (fun x=>x.1.foldl pairPack x.2):=foldPack (by intros;rfl) pairPackP
noncomputable def foldCompP : Procedure (prodCode (listCode packCode) packCode) packCode
    (fun x=>x.1.foldl compPack x.2):=foldPack (by intros;rfl) compPackP
end Emission
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionRewire
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def rewireBy (a : Data) (is : List ℕ) : Data:=
  ⟨a.inputs,a.nodes,is.map (fun i=>(a.outputs.drop i).headD 0)⟩
lemma rewireBy_valid (a : Data) (ha : a.Valid) (is : List ℕ) : (rewireBy a is).Valid:=by
  refine ⟨ha.1,?_⟩
  intro i hi
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp hi
  exact headD_drop_bound ha.2 j
lemma rewireBy_mass (a : Data) (is : List ℕ) : (rewireBy a is).mass≤a.mass+is.length:=by
  simp only [rewireBy,Data.mass,Data.width,List.length_map];omega
def rewirePack (a : Pack) (is : List ℕ) : Pack:=
  ⟨⟨a.val.budget+is.length,rewireBy a.val.value is⟩,rewireBy_valid a.val.value a.property.1 is,
    (rewireBy_mass _ _).trans (Nat.add_le_add_right a.property.2 _)⟩
def identityPack (n : ℕ) : Pack:=selectPack n (List.range n) (by intro i hi;exact Nat.le_of_lt (List.mem_range.mp hi))

def assignPack (n i : ℕ) (v : Pack) : Pack:=
  rewirePack (pairPack (identityPack n) v) ((List.range n).map (fun j=>if j=i then n else j))
namespace Emission
noncomputable def rewireByP : Procedure (prodCode dataCode (listCode Nat.bits)) dataCode
    (fun x=>rewireBy x.1 x.2):=by
  let a:=first dataCode (listCode Nat.bits)
  let is:=second dataCode (listCode Nat.bits)
  let out:=dataOutputsP.comp a
  let get:=(listGet Nat.bits 0).comp ((second (listCode Nat.bits) Nat.bits).pair (first (listCode Nat.bits) Nat.bits))
  let outs:=(listMapWith (f:=fun (xs:List ℕ) i=>(xs.drop i).headD 0) 0 0 get).comp (out.pair is)
  exact (dataPackP.comp ((dataInputP.comp a).pair ((dataNodesP.comp a).pair outs))).congrFun (by intro x;rfl)
noncomputable def rewirePackP : Procedure (prodCode packCode (listCode Nat.bits)) packCode
    (fun x=>rewirePack x.1 x.2):=by
  let a:=first packCode (listCode Nat.bits)
  let is:=second packCode (listCode Nat.bits)
  let v:=rewireByP.comp ((packValueP.comp a).pair is)
  let b:=unaryAdd.comp ((packBudgetP.comp a).pair ((NativeAIG.Emission.listUnaryLength Nat.bits 0).comp is))
  exact (b.pair v).result (by intro x;rfl)
noncomputable def rangeP : Procedure unaryCode (listCode Nat.bits) List.range:=by
  let p:=unaryToBits.comp (first unaryCode emptyCode)
  exact ((tabulate (f:=fun (_:Unit) i=>i) 0 p).comp
    ((identity unaryCode).pair (Procedure.constant _ emptyCode ()))).congrFun (by intro n;exact List.map_id _)
noncomputable def identityPackP : Procedure unaryCode packCode identityPack:=by
  let v:=selectP.comp (unaryToBits.pair rangeP)
  let b:=unaryAdd.comp ((identity unaryCode).pair (identity unaryCode))
  exact (b.pair v).result (by intro n;change _=prodCode unaryCode dataCode (n+(List.range n).length,select n (List.range n));rw [List.length_range];rfl)
noncomputable def assignPackP : Procedure (prodCode unaryCode (prodCode Nat.bits packCode)) packCode
    (fun x=>assignPack x.1 x.2.1 x.2.2):=by
  let n:=first unaryCode (prodCode Nat.bits packCode)
  let i:=(first Nat.bits packCode).comp (second unaryCode (prodCode Nat.bits packCode))
  let v:=(second Nat.bits packCode).comp (second unaryCode (prodCode Nat.bits packCode))
  let env:=(unaryToBits.comp n).pair i
  let e:=first (prodCode Nat.bits Nat.bits) Nat.bits
  let j:=second (prodCode Nat.bits Nat.bits) Nat.bits
  let test:=binaryEq.comp (j.pair ((second Nat.bits Nat.bits).comp e))
  let choose:= (conditional test ((first Nat.bits Nat.bits).comp e) j).congrFun
    (show ∀ x : (ℕ×ℕ)×ℕ, _ = (if x.2=x.1.2 then x.1.1 else x.2) from by
      intro x;simp)
  let out:=(listMapWith (f:=fun (e:ℕ×ℕ) j=>if j=e.2 then e.1 else j) 0 0 choose).comp
    (env.pair (rangeP.comp n))
  exact rewirePackP.comp ((pairPackP.comp ((identityPackP.comp n).pair v)).pair out)
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def emptyAt (n : ℕ) : Pack:=selectPack n [] (by simp)
def bandPack (a b : Pack) : Pack:=compPack (pairPack a b) (nodePack 2 (.conj 0 1) (by simp [Node.Bound]))
def vectorPack (n : ℕ) (xs : List Pack) : Pack:=xs.foldl pairPack (emptyAt n)
namespace Emission
noncomputable def emptyAtP : Procedure unaryCode packCode emptyAt:=by
  let v:=selectP.comp (unaryToBits.pair (Procedure.constant _ (listCode Nat.bits) []))
  exact ((identity unaryCode).pair v).result (by intro n;rfl)
noncomputable def constantPackP : Procedure (prodCode unaryCode boolCode) packCode (fun x=>constantPack x.1 x.2):=by
  let n:=first unaryCode boolCode
  let v:=constantP.comp ((unaryToBits.comp n).pair (second unaryCode boolCode))
  let b:=unaryAdd.comp (n.pair (Procedure.constant _ unaryCode 2))
  exact (b.pair v).result (by intro x;rfl)
noncomputable def bnotPackP : Procedure packCode packCode bnotPack:=
  compPackP.comp ((identity packCode).pair (Procedure.constant _ packCode (nodePack 1 (.neg 0) (by simp [Node.Bound]))))
noncomputable def bandPackP : Procedure (prodCode packCode packCode) packCode (fun x=>bandPack x.1 x.2):=
  compPackP.comp (pairPackP.pair (Procedure.constant _ packCode (nodePack 2 (.conj 0 1) (by simp [Node.Bound]))))
noncomputable def vectorPackP : Procedure (prodCode unaryCode (listCode packCode)) packCode
    (fun x=>vectorPack x.1 x.2):=
  foldPairP.comp ((second unaryCode (listCode packCode)).pair (emptyAtP.comp (first unaryCode (listCode packCode))))
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGNetworkEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.AIGNetworkEmission
open Std.Sat BooleanNetwork
open NetworkEmission

def nodePack (n gs : ℕ) : NativeAIG.Decl→Pack
  | .zero=>constantPack (n+gs) false
  | .atom v=>bitPack (n+gs) v
  | .gate a b=>bandPack (faninPack n gs a) (faninPack n gs b)

def partialPack (n : ℕ) (ds : List NativeAIG.Decl) (k : ℕ) : Pack:=
  ((List.range k).map (fun i=>assignPack (n+ds.length) (n+i)
    (nodePack n ds.length ((ds.drop i).headD .zero)))).foldl compPack (identityPack (n+ds.length))

def padPack (n gs : ℕ) : Pack:=vectorPack n ((List.range (n+gs)).map
  (fun i=>if i<n then bitPack n i else constantPack n false))

def compilePack (n : ℕ) (ds : List NativeAIG.Decl) (refs : List NativeAIG.Ref) : Pack:=
  compPack (compPack (padPack n ds.length) (partialPack n ds ds.length))
    (vectorPack (n+ds.length) (refs.map (faninPack n ds.length)))
end ExactQuantumFactoring.AIGNetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGNetworkProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.AIGNetworkEmission
open BitStackProgram BitStackProgram.Procedure NetworkEmission
open NetworkEmission.Emission
namespace Emission
noncomputable def faninPackP : Procedure (prodCode dimsCode NativeAIG.refCode) packCode
    (fun x=>faninPack x.1.1 x.1.2 x.2):=by
  let e:=first dimsCode NativeAIG.refCode
  let n:=(first unaryCode unaryCode).comp e
  let gs:=(second unaryCode unaryCode).comp e
  let w:=unaryAdd.comp (n.pair gs)
  let ref:=second dimsCode NativeAIG.refCode
  let idx:=(first Nat.bits boolCode).comp ref
  let inv:=(second Nat.bits boolCode).comp ref
  let off:=binaryAdd.comp ((unaryToBits.comp n).pair idx)
  let v:=conditional (binaryLt.comp (idx.pair (unaryToBits.comp gs)))
    (bitPackP.comp (w.pair off)) (constantPackP.comp (w.pair (Procedure.constant _ boolCode false)))
  exact (conditional inv (bnotPackP.comp v) v).congrFun (by intro x;simp only [Function.comp_apply,id_eq,decide_eq_true_eq,faninPack])

def declTag : NativeAIG.Decl→ℕ | .zero=>0 | .atom _=>1 | .gate _ _=>2
def declAtom : NativeAIG.Decl→ℕ | .atom i=>i | _=>0
def declGate : NativeAIG.Decl→NativeAIG.Key | .gate a b=>(a,b) | _=>((0,false),(0,false))
noncomputable def declTagP : Procedure NativeAIG.declCode Nat.bits declTag:=
  ((casesSum (Procedure.constant emptyCode Nat.bits 0)
    (casesSum (Procedure.constant Nat.bits Nat.bits 1) (Procedure.constant NativeAIG.keyCode Nat.bits 2))).precompose
      NativeAIG.declView).congrFun (by intro d;cases d <;> rfl)
noncomputable def declAtomP : Procedure NativeAIG.declCode Nat.bits declAtom:=
  ((casesSum (Procedure.constant emptyCode Nat.bits 0)
    (casesSum (identity Nat.bits) (Procedure.constant NativeAIG.keyCode Nat.bits 0))).precompose
      NativeAIG.declView).congrFun (by intro d;cases d <;> rfl)
noncomputable def declGateP : Procedure NativeAIG.declCode NativeAIG.keyCode declGate:=
  ((casesSum (Procedure.constant emptyCode NativeAIG.keyCode ((0,false),(0,false)))
    (casesSum (Procedure.constant Nat.bits NativeAIG.keyCode ((0,false),(0,false))) (identity NativeAIG.keyCode))).precompose
      NativeAIG.declView).congrFun (by intro d;cases d <;> rfl)
noncomputable def nodePackP : Procedure (prodCode dimsCode NativeAIG.declCode) packCode
    (fun x=>nodePack x.1.1 x.1.2 x.2):=by
  let e:=first dimsCode NativeAIG.declCode
  let w:=unaryAdd.comp e
  let d:=second dimsCode NativeAIG.declCode
  let tag:=declTagP.comp d
  let z:=constantPackP.comp (w.pair (Procedure.constant _ boolCode false))
  let a:=bitPackP.comp (w.pair (declAtomP.comp d))
  let l:=(first NativeAIG.refCode NativeAIG.refCode).comp (declGateP.comp d)
  let r:=(second NativeAIG.refCode NativeAIG.refCode).comp (declGateP.comp d)
  let g:=bandPackP.comp ((faninPackP.comp (e.pair l)).pair (faninPackP.comp (e.pair r)))
  exact (conditional (binaryEq.comp (tag.pair (Procedure.constant _ Nat.bits 0))) z
    (conditional (binaryEq.comp (tag.pair (Procedure.constant _ Nat.bits 1))) a g)).congrFun (by
      rintro ⟨e,d⟩;cases d <;> rfl)

abbrev graphInputCode:=prodCode unaryCode (listCode NativeAIG.declCode)
noncomputable def partialPackP : Procedure (prodCode graphInputCode unaryCode) packCode
    (fun x=>partialPack x.1.1 x.1.2 x.2):=by
  let e:=second unaryCode graphInputCode
  let n:=(first unaryCode (listCode NativeAIG.declCode)).comp e
  let ds:=(second unaryCode (listCode NativeAIG.declCode)).comp e
  let gs:=(NativeAIG.Emission.listUnaryLength NativeAIG.declCode .zero).comp ds
  let w:=unaryAdd.comp (n.pair gs)
  let i:=first unaryCode graphInputCode
  let off:=binaryAdd.comp ((unaryToBits.comp n).pair (unaryToBits.comp i))
  let d:=(listGet NativeAIG.declCode .zero).comp ((unaryToBits.comp i).pair ds)
  let node:=nodePackP.comp ((n.pair gs).pair d)
  let step:=assignPackP.comp (w.pair (off.pair node))
  let input:=first graphInputCode unaryCode
  let num:=second graphInputCode unaryCode
  let parts:=(tabulate (f:=fun (x:ℕ×List NativeAIG.Decl) i=>assignPack (x.1+x.2.length) (x.1+i)
    (nodePack x.1 x.2.length ((x.2.drop i).headD .zero))) emptyPack step).comp (num.pair input)
  let nn:=(first unaryCode (listCode NativeAIG.declCode)).comp input
  let gg:=(NativeAIG.Emission.listUnaryLength NativeAIG.declCode .zero).comp ((second unaryCode (listCode NativeAIG.declCode)).comp input)
  exact foldCompP.comp (parts.pair (identityPackP.comp (unaryAdd.comp (nn.pair gg))))
noncomputable def padPackP : Procedure dimsCode packCode (fun x=>padPack x.1 x.2):=by
  let e:=second unaryCode dimsCode
  let n:=(first unaryCode unaryCode).comp e
  let i:=unaryToBits.comp (first unaryCode dimsCode)
  let v:=conditional (binaryLt.comp (i.pair (unaryToBits.comp n)))
    (bitPackP.comp (n.pair i)) (constantPackP.comp (n.pair (Procedure.constant _ boolCode false)))
  let parts:=(tabulate (f:=fun (x:ℕ×ℕ) i=>if i<x.1 then bitPack x.1 i else constantPack x.1 false)
    emptyPack (v.congrFun (by intro x;simp only [Function.comp_apply,id_eq,decide_eq_true_eq]))).comp (unaryAdd.pair (identity dimsCode))
  exact vectorPackP.comp ((first unaryCode unaryCode).pair parts)
noncomputable def compilePackP : Procedure (prodCode graphInputCode (listCode NativeAIG.refCode)) packCode
    (fun x=>compilePack x.1.1 x.1.2 x.2):=by
  let e:=first graphInputCode (listCode NativeAIG.refCode)
  let n:=(first unaryCode (listCode NativeAIG.declCode)).comp e
  let ds:=(second unaryCode (listCode NativeAIG.declCode)).comp e
  let gs:=(NativeAIG.Emission.listUnaryLength NativeAIG.declCode .zero).comp ds
  let dim:=n.pair gs
  let pad:=padPackP.comp dim
  let graph:=partialPackP.comp (e.pair gs)
  let refs:=second graphInputCode (listCode NativeAIG.refCode)
  let parts:=(listMapWith (f:=fun (x:ℕ×ℕ) f=>faninPack x.1 x.2 f) (0,false) emptyPack faninPackP).comp (dim.pair refs)
  let output:=vectorPackP.comp ((unaryAdd.comp dim).pair parts)
  exact compPackP.comp ((compPackP.comp (pad.pair graph)).pair output)
end Emission
end ExactQuantumFactoring.AIGNetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace BitArithmetic
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
open AIGCompiler BooleanNetwork

/-- The two actual little-endian input words of the bitblaster. -/
def binaryInputs (w : ℕ) : AIG.BinaryRefVec (inputs (w+w)).1 w :=
  ⟨refVector (fun i => (inputs (w+w)).2 (i.castAdd w)),
   refVector (fun i => (inputs (w+w)).2 (Fin.natAdd w i))⟩

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitArithmeticDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
open AIGCompiler BooleanNetwork

def sub (w : ℕ) : BooleanNetwork (w+w) w :=
  let res := blastSub (inputs (w+w)).1 (binaryInputs w)
  compileVec res.aig res.vec

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordNetworks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
namespace BitArithmetic
open BooleanNetwork

/-- A word of constants uses at most one Boolean node per output bit. -/
def wordConstant {n : ℕ} {w : ℕ} (v : BitVec w) : BooleanNetwork n w :=
  vector (fun i => constant (v.getLsbD i.val))

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ArithmeticPredicates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open Std.Sat Std.Tactic.BVDecide
open AIGCompiler BooleanNetwork

def ult (w : ℕ) : BooleanNetwork (w+w) 1 :=
  let r := BVPred.mkUlt (inputs (w+w)).1 (binaryInputs w)
  compile r.aig (fun _ => r.ref)

def wordLt {n w : ℕ} (a b : BooleanNetwork n w) : BooleanNetwork n 1 :=
  (a.pair b).comp (ult w)

def wordEq (w : ℕ) : BooleanNetwork (w+w) 1 :=
  ((ult w).bor (((select (Fin.addCases (Fin.natAdd w) (Fin.castAdd w))).comp (ult w)))).bnot

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGIf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat

def ifGate (r : Graph) (d a b : Ref) : Graph×Ref :=
  let s:=gate r d a
  let t:=gate s.1 (notRef d) b
  orGate t.1 s.2 t.2
lemma ifGate_bound {B : ℕ} {r : Graph} (h : Bounded B r) (d a b : Ref)
    (hd : d.1≤B) (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+3) (ifGate r d a b).1 ∧ (ifGate r d a b).2.1≤B+3 := by
  have hs:=gate_bound h d a hd ha
  have ht:=gate_bound hs.1 (notRef d) b (hd.trans (by omega)) (hb.trans (by omega))
  exact orGate_bound ht.1 _ _ (hs.2.trans (by omega)) ht.2

def ifLoop : ℕ→Graph→Ref→List Ref→List Ref→ℕ→List Ref→Graph×List Ref
  | 0,r,_,_,_,_,out=>(r,out)
  | k+1,r,d,lhs,rhs,curr,out=>
    let s:=ifGate r d ((lhs.drop curr).headD (0,false)) ((rhs.drop curr).headD (0,false))
    ifLoop k s.1 d lhs rhs (curr+1) (out++[s.2])
def ifVec (r : Graph) (d : Ref) (lhs rhs : List Ref) : Graph×List Ref :=
  ifLoop lhs.length r d lhs rhs 0 []

namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def ifP : Procedure (prodCode graphCode tripleCode) (prodCode graphCode refCode)
    (fun x=>ifGate x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let r:=first graphCode tripleCode
  let abc:=second graphCode tripleCode
  let d:=(first refCode keyCode).comp abc
  let bc:=(second refCode keyCode).comp abc
  let a:=(first refCode refCode).comp bc
  let b:=(second refCode refCode).comp bc
  let s:=gateP.comp (r.pair (d.pair a))
  let t:=gateP.comp (((first graphCode refCode).comp s).pair ((notRefP.comp d).pair b))
  exact (orP.comp (((first graphCode refCode).comp t).pair
    (((second graphCode refCode).comp s).pair ((second graphCode refCode).comp t)))).congrFun (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

def shiftBit (xs : List Ref) (d i : ℕ) : Ref:=
  if i<d then (0,false) else (xs.drop (i-d)).headD (0,false)
def shift (xs : List Ref) (d : ℕ) : List Ref:=
  (List.range xs.length).map (shiftBit xs d)

namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def shiftBitP : Procedure (prodCode unaryCode (prodCode (listCode refCode) Nat.bits)) refCode
    (fun x=>shiftBit x.2.1 x.2.2 x.1) := by
  let i:=unaryToBits.comp (first unaryCode (prodCode (listCode refCode) Nat.bits))
  let env:=second unaryCode (prodCode (listCode refCode) Nat.bits)
  let xs:=(first (listCode refCode) Nat.bits).comp env
  let d:=(second (listCode refCode) Nat.bits).comp env
  let idx:=binarySub.comp (i.pair d)
  let get:=(listGet refCode (0,false)).comp (idx.pair xs)
  exact (conditional (binaryLt.comp (i.pair d)) (Procedure.constant _ refCode (0,false)) get).congrFun (by
    intro x;unfold shiftBit;split <;> simp_all)
noncomputable def shiftP : Procedure (prodCode (listCode refCode) Nat.bits) (listCode refCode)
    (fun x=>shift x.1 x.2) :=
  (tabulate (f:=fun (x : List Ref×ℕ) i=>shiftBit x.1 x.2 i) (0,false) shiftBitP).comp
    (((listUnaryLength refCode (0,false)).comp (first (listCode refCode) Nat.bits)).pair (identity _))
end Emission
end ExactQuantumFactoring.NativeAIG

end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

def isZero (r : Graph) (a : Ref) : Bool:=constant r a==some false

def mulLoop : ℕ→Graph→List Ref→List Ref→ℕ→List Ref→Graph×List Ref
  | 0,r,_,_,_,acc=>(r,acc)
  | k+1,r,lhs,rhs,curr,acc=>
    if isZero r ((rhs.drop curr).headD (0,false)) then mulLoop k r lhs rhs (curr+1) acc else
      let added:=add r acc (shift lhs curr)
      let next:=ifVec added.1 ((rhs.drop curr).headD (0,false)) added.2 acc
      mulLoop k next.1 lhs rhs (curr+1) next.2
def mulBlast (r : Graph) (lhs rhs : List Ref) : Graph×List Ref:=
  if lhs.length=0 then (r,[]) else
    let first:=ifVec r (rhs.headD (0,false)) lhs (List.replicate lhs.length (0,false))
    mulLoop (lhs.length-1) first.1 lhs rhs 1 first.2
def mul (r : Graph) (lhs rhs : List Ref) : Graph×List Ref:=
  if countKnown r lhs < countKnown r rhs then mulBlast r lhs rhs else mulBlast r rhs lhs

end ExactQuantumFactoring.NativeAIG

end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGIfProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
lemma RefsBound.push_inc {B c : ℕ} {xs : List Ref} (hx : RefsBound B xs)
    (hc : 1 ≤ c) (a : Ref) (ha : a.1 ≤ B+c) : RefsBound (B+c) (xs++[a]) := by
  refine ⟨?_,?_⟩
  · simp only [List.length_append,List.length_singleton];have:=hx.1;omega
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (hx.2 r hr).trans (by omega)
    · have he : r=a:=List.mem_singleton.mp hr
      simpa only [he] using ha

def ifStepData (s : AddData) : AddData :=
  let r:=ifGate s.graph s.cin ((s.lhs.drop s.curr).headD (0,false)) ((s.rhs.drop s.curr).headD (0,false))
  ⟨s.budget+3,r.1,s.lhs,s.rhs,s.curr+1,s.cin,s.output++[r.2]⟩
lemma ifStep_ok (s : AddState) : AddOK (ifStepData s.val) := by
  obtain ⟨hg,hl,hr,hc,hci,ho⟩:=s.property
  have hh:=ifGate_bound hg s.val.cin _ _ hci (hl.get s.val.curr) (hr.get s.val.curr)
  unfold AddOK
  dsimp only [ifStepData]
  exact ⟨hh.1,hl.mono (by omega),hr.mono (by omega),by omega,by omega,
    ho.push_inc (by omega) _ hh.2⟩
def ifStep (s : AddState) : AddState:=⟨ifStepData s.val,ifStep_ok s⟩
lemma ifStep_budget (s : AddState) : (ifStep s).val.budget=s.val.budget+3 := rfl
lemma ifStep_iterate_budget (s : AddState) (k : ℕ) :
    ((ifStep^[k]) s).val.budget=s.val.budget+3*k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,ifStep_budget];omega
lemma ifStep_iterate_loop (s : AddState) (k : ℕ) :
    (((ifStep^[k]) s).val.graph,((ifStep^[k]) s).val.output)=
      ifLoop k s.val.graph s.val.cin s.val.lhs s.val.rhs s.val.curr s.val.output := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl

def initializeIfData (s : AddData) : AddData:=⟨s.budget,s.graph,s.lhs,s.rhs,0,s.cin,[]⟩
lemma initializeIf_ok (s : AddState) : AddOK (initializeIfData s.val) := by
  exact ⟨s.property.1,s.property.2.1,s.property.2.2.1,Nat.zero_le _,s.property.2.2.2.2.1,
    ⟨Nat.zero_le _,by intro a ha;cases ha⟩⟩
def initializeIf (s : AddState) : AddState:=⟨initializeIfData s.val,initializeIf_ok s⟩
def ifVecState (s : AddState) : AddState:=(ifStep^[s.val.lhs.length]) (initializeIf s)
lemma ifVecState_value (s : AddState) :
    ((ifVecState s).val.graph,(ifVecState s).val.output)=ifVec s.val.graph s.val.cin s.val.lhs s.val.rhs :=
  ifStep_iterate_loop (initializeIf s) s.val.lhs.length
lemma ifVecState_budget (s : AddState) :
    (ifVecState s).val.budget=s.val.budget+3*s.val.lhs.length :=
  ifStep_iterate_budget (initializeIf s) s.val.lhs.length
namespace Emission
noncomputable def ifStepDataP : Procedure addDataCode addDataCode ifStepData := by
  let budget:=(first unaryCode addTail1).comp addViewP
  let newBudget:=unaryAdd.comp (budget.pair (Procedure.constant _ unaryCode 3))
  let lhsBit:=(listGet refCode (0,false)).comp (addCurrP.pair addLhsP)
  let rhsBit:=(listGet refCode (0,false)).comp (addCurrP.pair addRhsP)
  let s:=ifP.comp (addGraphP.pair (addCinP.pair (lhsBit.pair rhsBit)))
  let g:=(first graphCode refCode).comp s
  let outBit:=(second graphCode refCode).comp s
  let out:=(listAppend refCode (0,false)).comp (addOutputP.pair ((singleton refCode).comp outBit))
  exact (packAddP.comp (newBudget.pair (g.pair (addLhsP.pair (addRhsP.pair
    ((successor.comp addCurrP).pair (addCinP.pair out))))))).congrFun (by intro s;rfl)
noncomputable def ifStepP : Procedure addStateCode addStateCode ifStep :=
  (ifStepDataP.precompose Subtype.val).result (by intro s;rfl)
noncomputable def ifIterationP : Procedure (prodCode unaryCode addStateCode) addStateCode
    (fun x=>(ifStep^[x.1]) x.2) :=
  ifStepP.iterate (Polynomial.C 2700*(Polynomial.X+1)^2) (by
    intro n s i hi
    have hh:=addStateCode_bound ((ifStep^[i]) s)
    rw [ifStep_iterate_budget] at hh
    have hb:=budget_le_code s
    have hb' : s.val.budget+3*i+1 ≤ 3*(n+(addStateCode s).length+1):=by omega
    have hs:=Nat.pow_le_pow_left hb' 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    nlinarith)
noncomputable def initializeIfDataP : Procedure addDataCode addDataCode initializeIfData := by
  let b:=(first unaryCode addTail1).comp addViewP
  exact (packAddP.comp (b.pair (addGraphP.pair (addLhsP.pair (addRhsP.pair
    ((Procedure.constant _ Nat.bits 0).pair (addCinP.pair
      (Procedure.constant _ (listCode refCode) [])))))))).congrFun (by intro x;rfl)
noncomputable def initializeIfP : Procedure addStateCode addStateCode initializeIf :=
  (initializeIfDataP.precompose (fun s:AddState=>s.val)).result (by intro s;rfl)
noncomputable def ifVecStateP : Procedure addStateCode addStateCode ifVecState :=
  ifIterationP.comp (((listUnaryLength refCode (0,false)).comp
    (addLhsP.precompose (fun s:AddState=>s.val))).pair initializeIfP)
noncomputable def ifVecP : Procedure addStateCode (prodCode graphCode (listCode refCode))
    (fun s=>ifVec s.val.graph s.val.cin s.val.lhs s.val.rhs) :=
  (((addGraphP.pair addOutputP).precompose (fun s:AddState=>s.val)).comp ifVecStateP).congrFun ifVecState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGVectorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
lemma shift_length (xs : List Ref) (d : ℕ) : (shift xs d).length=xs.length := by
  simp [shift]
lemma shift_refs {B : ℕ} {xs : List Ref} (h : RefsBound B xs) (d : ℕ) :
    RefsBound B (shift xs d) := by
  refine ⟨by simpa only [shift_length] using h.1,?_⟩
  intro a ha
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp ha
  unfold shiftBit
  split
  · exact Nat.zero_le _
  · exact h.get _
lemma addStep_length (s : AddState) : (addStep s).val.output.length=s.val.output.length+1 := by
  simp only [addStep,addStepData,List.length_append,List.length_singleton]
lemma addStep_iterate_length (s : AddState) (k : ℕ) :
    ((addStep^[k]) s).val.output.length=s.val.output.length+k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,addStep_length];omega
lemma addBlastState_length (s : AddState) : (addBlastState s).val.output.length=s.val.lhs.length := by
  rw [addBlastState,addStep_iterate_length]
  simp only [initializeAdd,initializeAddData,List.length_nil,Nat.zero_add]
lemma addState_length (s : AddState) (h : s.val.lhs.length=s.val.rhs.length) :
    (addState s).val.output.length=s.val.lhs.length := by
  unfold addState
  split
  · exact addBlastState_length s
  · rw [addBlastState_length];exact h.symm
lemma addState_budget_eq (s : AddState) (h : s.val.lhs.length=s.val.rhs.length) :
    (addState s).val.budget=s.val.budget+13*s.val.lhs.length := by
  unfold addState
  split
  · exact addBlastState_budget s
  · rw [addBlastState_budget];change s.val.budget+13*s.val.rhs.length=_;rw [h]
lemma ifStep_length (s : AddState) : (ifStep s).val.output.length=s.val.output.length+1 := by
  simp only [ifStep,ifStepData,List.length_append,List.length_singleton]
lemma ifStep_iterate_length (s : AddState) (k : ℕ) :
    ((ifStep^[k]) s).val.output.length=s.val.output.length+k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,ifStep_length];omega
lemma ifVecState_length (s : AddState) : (ifVecState s).val.output.length=s.val.lhs.length := by
  rw [ifVecState,ifStep_iterate_length]
  simp only [initializeIf,initializeIfData,List.length_nil,Nat.zero_add]
lemma add_bound {B : ℕ} {g : Graph} {lhs rhs : List Ref}
    (hg : Bounded B g) (hl : RefsBound B lhs) (hr : RefsBound B rhs)
    (he : lhs.length=rhs.length) :
    Bounded (B+13*lhs.length) (add g lhs rhs).1 ∧
    RefsBound (B+13*lhs.length) (add g lhs rhs).2 ∧ (add g lhs rhs).2.length=lhs.length := by
  let s : AddState:=⟨⟨B,g,lhs,rhs,0,(0,false),[]⟩,
    hg,hl,hr,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
  have hs : s.val.lhs.length=s.val.rhs.length:=he
  have hb:=addState_budget_eq s hs
  have ho:=(addState s).property
  have hv:=addState_value s
  have hn:=addState_length s hs
  rw [←hv]
  unfold AddOK at ho
  rw [hb] at ho
  exact ⟨ho.1,ho.2.2.2.2.2,hn⟩
lemma ifVec_bound {B : ℕ} {g : Graph} {lhs rhs : List Ref} {c : Ref}
    (hg : Bounded B g) (hl : RefsBound B lhs) (hr : RefsBound B rhs) (hc : c.1 ≤ B) :
    Bounded (B+3*lhs.length) (ifVec g c lhs rhs).1 ∧
    RefsBound (B+3*lhs.length) (ifVec g c lhs rhs).2 ∧ (ifVec g c lhs rhs).2.length=lhs.length := by
  let s : AddState:=⟨⟨B,g,lhs,rhs,0,c,[]⟩,
    hg,hl,hr,Nat.zero_le _,hc,Nat.zero_le _,by intro a ha;cases ha⟩
  have hb:=ifVecState_budget s
  have ho:=(ifVecState s).property
  have hv:=ifVecState_value s
  have hn:=ifVecState_length s
  rw [←hv]
  unfold AddOK at ho
  rw [hb] at ho
  exact ⟨ho.1,ho.2.2.2.2.2,hn⟩
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGMulBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def MulOK (s : AddData) : Prop:=AddOK s ∧ s.lhs.length=s.rhs.length ∧ s.output.length=s.lhs.length
abbrev MulState:={s : AddData // MulOK s}
def mulStateCode (s : MulState) : List Bool:=addDataCode s.val

def mulStepData (s : AddData) : AddData:=
  let next:=if isZero s.graph ((s.rhs.drop s.curr).headD (0,false)) then (s.graph,s.output) else
    let added:=add s.graph s.output (shift s.lhs s.curr)
    ifVec added.1 ((s.rhs.drop s.curr).headD (0,false)) added.2 s.output
  ⟨s.budget+16*s.lhs.length+1,next.1,s.lhs,s.rhs,s.curr+1,s.cin,next.2⟩
lemma mulStep_ok (s : MulState) : MulOK (mulStepData s.val) := by
  obtain ⟨⟨hg,hl,hr,hc,hci,ho⟩,he,ha⟩:=s.property
  have hb : s.val.budget ≤ s.val.budget+16*s.val.lhs.length+1:=by omega
  unfold MulOK AddOK mulStepData
  split
  · exact ⟨⟨hg.mono hb,hl.mono hb,hr.mono hb,by dsimp only;omega,hci.trans hb,ho.mono hb⟩,he,ha⟩
  · have had:=add_bound hg ho (shift_refs hl s.val.curr) (by rw [shift_length];exact ha)
    have hn : s.val.budget+13*s.val.output.length+3*(add s.val.graph s.val.output (shift s.val.lhs s.val.curr)).2.length ≤
        s.val.budget+16*s.val.lhs.length+1:=by rw [had.2.2,ha];omega
    have hh:=ifVec_bound had.1 had.2.1 (ho.mono (by omega)) ((hr.get s.val.curr).trans (by omega))
    exact ⟨⟨hh.1.mono hn,hl.mono hb,hr.mono hb,by dsimp only;omega,hci.trans hb,hh.2.1.mono hn⟩,
      he,hh.2.2.trans (had.2.2.trans ha)⟩
def mulStep (s : MulState) : MulState:=⟨mulStepData s.val,mulStep_ok s⟩
lemma mulStep_budget (s : MulState) : (mulStep s).val.budget=s.val.budget+16*s.val.lhs.length+1 := rfl
lemma mulStep_lhs (s : MulState) : (mulStep s).val.lhs=s.val.lhs := rfl
lemma mulStep_iterate_budget (s : MulState) (k : ℕ) :
    ((mulStep^[k]) s).val.budget=s.val.budget+(16*s.val.lhs.length+1)*k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,mulStep_budget,mulStep_lhs];ring
lemma mulStep_iterate_loop (s : MulState) (k : ℕ) :
    (((mulStep^[k]) s).val.graph,((mulStep^[k]) s).val.output)=
      mulLoop k s.val.graph s.val.lhs s.val.rhs s.val.curr s.val.output := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>
    rw [Function.iterate_succ_apply,ih,mulLoop]
    unfold mulStep mulStepData
    split <;> rfl
lemma mulStateCode_bound (s : MulState) : (mulStateCode s).length ≤ 300*(s.val.budget+1)^2 :=
  addStateCode_bound ⟨s.val,s.property.1⟩
lemma mulBudget_le_code (s : MulState) : s.val.budget ≤ (mulStateCode s).length :=
  budget_le_code ⟨s.val,s.property.1⟩
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGMulProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def mulAddInput (s : MulState) : AddState:=
  ⟨⟨s.val.budget,s.val.graph,s.val.output,shift s.val.lhs s.val.curr,0,(0,false),[]⟩,
   s.property.1.1,s.property.1.2.2.2.2.2,shift_refs s.property.1.2.1 _,Nat.zero_le _,Nat.zero_le _,
   Nat.zero_le _,by intro a ha;cases ha⟩
def mulAdded (s : MulState) : AddState:=addState (mulAddInput s)
lemma mulAdded_value (s : MulState) : ((mulAdded s).val.graph,(mulAdded s).val.output)=
    add s.val.graph s.val.output (shift s.val.lhs s.val.curr) :=addState_value _
lemma mulAdded_budget (s : MulState) : (mulAdded s).val.budget=s.val.budget+13*s.val.lhs.length := by
  have hh:=addState_budget_eq (mulAddInput s) (by
    change s.val.output.length=(shift s.val.lhs s.val.curr).length
    rw [shift_length];exact s.property.2.2)
  simpa only [mulAdded,mulAddInput,s.property.2.2] using hh

def mulIfInput (s : MulState) : AddState:=
  ⟨⟨(mulAdded s).val.budget,(mulAdded s).val.graph,(mulAdded s).val.output,s.val.output,0,
      (s.val.rhs.drop s.val.curr).headD (0,false),[]⟩,
    (mulAdded s).property.1,(mulAdded s).property.2.2.2.2.2,
    s.property.1.2.2.2.2.2.mono (by rw [mulAdded_budget];omega),Nat.zero_le _,
    (s.property.1.2.2.1.get _).trans (by rw [mulAdded_budget];omega),Nat.zero_le _,by intro a ha;cases ha⟩
lemma mulIfInput_value (s : MulState) :
    ifVec (mulIfInput s).val.graph (mulIfInput s).val.cin (mulIfInput s).val.lhs (mulIfInput s).val.rhs=
      ifVec (add s.val.graph s.val.output (shift s.val.lhs s.val.curr)).1
        ((s.val.rhs.drop s.val.curr).headD (0,false))
        (add s.val.graph s.val.output (shift s.val.lhs s.val.curr)).2 s.val.output := by
  have hh:=mulAdded_value s
  have h1:=congrArg Prod.fst hh
  have h2:=congrArg Prod.snd hh
  dsimp only [Prod.fst] at h1
  dsimp only [Prod.snd] at h2
  dsimp only [mulIfInput]
  rw [h1,h2]

namespace Emission
noncomputable def mulBudgetP : Procedure mulStateCode unaryCode (fun s=>s.val.budget):=
  ((first unaryCode addTail1).comp addViewP).precompose (fun s:MulState=>s.val)
noncomputable def mulGraphP : Procedure mulStateCode graphCode (fun s=>s.val.graph):=
  addGraphP.precompose (fun s:MulState=>s.val)
noncomputable def mulLhsP : Procedure mulStateCode (listCode refCode) (fun s=>s.val.lhs):=
  addLhsP.precompose (fun s:MulState=>s.val)
noncomputable def mulRhsP : Procedure mulStateCode (listCode refCode) (fun s=>s.val.rhs):=
  addRhsP.precompose (fun s:MulState=>s.val)
noncomputable def mulOutputP : Procedure mulStateCode (listCode refCode) (fun s=>s.val.output):=
  addOutputP.precompose (fun s:MulState=>s.val)
noncomputable def mulCurrP : Procedure mulStateCode Nat.bits (fun s=>s.val.curr):=
  addCurrP.precompose (fun s:MulState=>s.val)
noncomputable def mulCinP : Procedure mulStateCode refCode (fun s=>s.val.cin):=
  addCinP.precompose (fun s:MulState=>s.val)
noncomputable def mulAddInputP : Procedure mulStateCode addStateCode mulAddInput := by
  let sh:=shiftP.comp (mulLhsP.pair mulCurrP)
  exact (packAddP.comp (mulBudgetP.pair (mulGraphP.pair (mulOutputP.pair (sh.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
    (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def mulAddedP : Procedure mulStateCode addStateCode mulAdded :=addStateP.comp mulAddInputP
noncomputable def mulIfInputP : Procedure mulStateCode addStateCode mulIfInput := by
  let ad:=mulAddedP
  let budget:=(((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)).comp ad
  let g:=(addGraphP.precompose (fun s:AddState=>s.val)).comp ad
  let added:=(addOutputP.precompose (fun s:AddState=>s.val)).comp ad
  let c:=(listGet refCode (0,false)).comp (mulCurrP.pair mulRhsP)
  exact (packAddP.comp (budget.pair (g.pair (added.pair (mulOutputP.pair
    ((Procedure.constant _ Nat.bits 0).pair (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result
      (by intro s;rfl)
noncomputable def isZeroP : Procedure (prodCode graphCode refCode) boolCode (fun x=>isZero x.1 x.2):=by
  let inv := (second Nat.bits boolCode).comp (second graphCode refCode)
  exact (boolAnd.comp (knownP.pair (boolNot.comp inv))).congrFun (by
    rintro ⟨g,⟨i,b⟩⟩
    dsimp only [Function.comp_apply, Prod.fst, Prod.snd]
    unfold known isZero constant
    cases g.decls[i]?.getD Decl.zero <;> cases b <;> rfl)
noncomputable def mulNextP : Procedure mulStateCode (prodCode graphCode (listCode refCode))
    (fun s=>if isZero s.val.graph ((s.val.rhs.drop s.val.curr).headD (0,false)) then (s.val.graph,s.val.output)
      else let added:=add s.val.graph s.val.output (shift s.val.lhs s.val.curr)
        ifVec added.1 ((s.val.rhs.drop s.val.curr).headD (0,false)) added.2 s.val.output) := by
  let c:=(listGet refCode (0,false)).comp (mulCurrP.pair mulRhsP)
  let test:=isZeroP.comp (mulGraphP.pair c)
  let no:=(ifVecP.comp mulIfInputP).congrFun mulIfInput_value
  exact conditional test (mulGraphP.pair mulOutputP) no
noncomputable def mulStepP : Procedure mulStateCode mulStateCode mulStep := by
  let len:=(listUnaryLength refCode (0,false)).comp mulLhsP
  let cost:=unaryMul.comp ((Procedure.constant _ unaryCode 16).pair len)
  let b:=unarySuccessor.comp (unaryAdd.comp (mulBudgetP.pair cost))
  let g:=(first graphCode (listCode refCode)).comp mulNextP
  let out:=(second graphCode (listCode refCode)).comp mulNextP
  exact (packAddP.comp (b.pair (g.pair (mulLhsP.pair (mulRhsP.pair
    ((successor.comp mulCurrP).pair (mulCinP.pair out))))))).result (by intro s;rfl)
noncomputable def mulIterationP : Procedure (prodCode unaryCode mulStateCode) mulStateCode
    (fun x=>(mulStep^[x.1]) x.2) :=
  mulStepP.iterate (Polynomial.C 97200*(Polynomial.X+1)^4) (by
    intro n s i hi
    have hh:=mulStateCode_bound ((mulStep^[i]) s)
    rw [mulStep_iterate_budget] at hh
    have hb:=mulBudget_le_code s
    have hl:=s.property.1.2.1.1
    let M:=n+(mulStateCode s).length+1
    have hM : 1 ≤ M:=by dsimp [M];omega
    have hB : s.val.budget+1 ≤ M:=by dsimp [M];omega
    have hw : 16*s.val.lhs.length+1 ≤ 17*M:=by omega
    have hii : i ≤ M:=by dsimp [M];omega
    have hm:=Nat.mul_le_mul hw hii
    have hx : s.val.budget+(16*s.val.lhs.length+1)*i+1 ≤ 18*M^2:=by nlinarith
    have hp:=Nat.pow_le_pow_left hx 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    calc
      (mulStateCode ((mulStep^[i]) s)).length ≤ 300*(s.val.budget+(16*s.val.lhs.length+1)*i+1)^2:=hh
      _ ≤ 300*(18*M^2)^2:=Nat.mul_le_mul_left _ hp
      _ = 97200*(n+(mulStateCode s).length+1)^4:=by dsimp [M] <;> ring)
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGMulWrapper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

abbrev BinaryState:={s : AddState // s.val.lhs.length=s.val.rhs.length}
def binaryStateCode (s : BinaryState) : List Bool:=addStateCode s.val
lemma RefsBound.zeros {B w : ℕ} (h : w≤B) : RefsBound B (List.replicate w (0,false)) := by
  refine ⟨by simpa,?_⟩
  intro a ha
  have he:=List.eq_of_mem_replicate ha
  simpa only [he] using Nat.zero_le B

def mulFirstInput (s : BinaryState) : AddState:=
  ⟨⟨s.val.val.budget,s.val.val.graph,s.val.val.lhs,List.replicate s.val.val.lhs.length (0,false),
    0,s.val.val.rhs.headD (0,false),[]⟩,
  s.val.property.1,s.val.property.2.1,RefsBound.zeros s.val.property.2.1.1,Nat.zero_le _,
  by simpa using s.val.property.2.2.1.get 0,Nat.zero_le _,by intro a ha;cases ha⟩
def mulFirst (s : BinaryState) : AddState:=ifVecState (mulFirstInput s)
lemma mulFirst_budget (s : BinaryState) : (mulFirst s).val.budget=s.val.val.budget+3*s.val.val.lhs.length:=
  ifVecState_budget _
lemma mulFirst_length (s : BinaryState) : (mulFirst s).val.output.length=s.val.val.lhs.length:=
  ifVecState_length _
lemma mulFirst_value (s : BinaryState) : ((mulFirst s).val.graph,(mulFirst s).val.output)=
    ifVec s.val.val.graph (s.val.val.rhs.headD (0,false)) s.val.val.lhs
      (List.replicate s.val.val.lhs.length (0,false)):=ifVecState_value _
def initializeMul (s : BinaryState) : MulState:=
  ⟨⟨(mulFirst s).val.budget+1,(mulFirst s).val.graph,s.val.val.lhs,s.val.val.rhs,1,(0,false),
      (mulFirst s).val.output⟩,
  ⟨(mulFirst s).property.1.mono (by dsimp only;omega),
    s.val.property.2.1.mono (by dsimp only;rw [mulFirst_budget];omega),
    s.val.property.2.2.1.mono (by dsimp only;rw [mulFirst_budget];omega),by dsimp only;omega,Nat.zero_le _,
    (mulFirst s).property.2.2.2.2.2.mono (by dsimp only;omega)⟩,s.property,mulFirst_length s⟩
def mulBlastState (s : BinaryState) : MulState:=(mulStep^[s.val.val.lhs.length-1]) (initializeMul s)
lemma mulBlastState_value (s : BinaryState) :
    ((mulBlastState s).val.graph,(mulBlastState s).val.output)=
      mulBlast s.val.val.graph s.val.val.lhs s.val.val.rhs := by
  rw [mulBlastState,mulStep_iterate_loop]
  have hh:=mulFirst_value s
  have h1:=congrArg Prod.fst hh
  have h2:=congrArg Prod.snd hh
  dsimp only [Prod.fst] at h1
  dsimp only [Prod.snd] at h2
  dsimp only [initializeMul]
  rw [h1,h2,mulBlast]
  split
  · rename_i hz
    have hl:=List.length_eq_zero_iff.mp hz
    simp only [hl,List.length_nil,Nat.zero_sub,List.replicate_zero,ifVec,ifLoop,mulLoop]
  · rfl

def swapBinary (s : BinaryState) : BinaryState:=⟨swapAdd s.val,s.property.symm⟩
def mulState (s : BinaryState) : MulState:=
  if countKnown s.val.val.graph s.val.val.lhs < countKnown s.val.val.graph s.val.val.rhs then
    mulBlastState s else mulBlastState (swapBinary s)
lemma mulState_value (s : BinaryState) : ((mulState s).val.graph,(mulState s).val.output)=
    mul s.val.val.graph s.val.val.lhs s.val.val.rhs := by
  unfold mulState mul
  split <;> exact mulBlastState_value _

namespace Emission
noncomputable def binaryGraphP : Procedure binaryStateCode graphCode (fun s=>s.val.val.graph):=
  addGraphP.precompose (fun s:BinaryState=>s.val.val)
noncomputable def binaryLhsP : Procedure binaryStateCode (listCode refCode) (fun s=>s.val.val.lhs):=
  addLhsP.precompose (fun s:BinaryState=>s.val.val)
noncomputable def binaryRhsP : Procedure binaryStateCode (listCode refCode) (fun s=>s.val.val.rhs):=
  addRhsP.precompose (fun s:BinaryState=>s.val.val)
noncomputable def zerosP : Procedure (listCode refCode) (listCode refCode)
    (fun xs=>List.replicate xs.length (0,false)) :=
  (listMap (0,false) (0,false) (Procedure.constant refCode refCode (0,false))).congrFun (by
    intro xs;exact List.map_const')
noncomputable def mulFirstInputP : Procedure binaryStateCode addStateCode mulFirstInput := by
  let b:=((first unaryCode addTail1).comp addViewP).precompose (fun s:BinaryState=>s.val.val)
  let c:=(listHead refCode (0,false)).comp binaryRhsP
  exact (packAddP.comp (b.pair (binaryGraphP.pair (binaryLhsP.pair ((zerosP.comp binaryLhsP).pair
    ((Procedure.constant _ Nat.bits 0).pair (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result
    (by intro s;rfl)
noncomputable def mulFirstP : Procedure binaryStateCode addStateCode mulFirst:=ifVecStateP.comp mulFirstInputP
noncomputable def initializeMulP : Procedure binaryStateCode mulStateCode initializeMul := by
  let f:=mulFirstP
  let b:=unarySuccessor.comp ((((first unaryCode addTail1).comp addViewP).precompose
    (fun s:AddState=>s.val)).comp f)
  let g:=(addGraphP.precompose (fun s:AddState=>s.val)).comp f
  let out:=(addOutputP.precompose (fun s:AddState=>s.val)).comp f
  exact (packAddP.comp (b.pair (g.pair (binaryLhsP.pair (binaryRhsP.pair
    ((Procedure.constant _ Nat.bits 1).pair ((Procedure.constant _ refCode (0,false)).pair out))))))).result
      (by intro s;rfl)
noncomputable def mulBlastStateP : Procedure binaryStateCode mulStateCode mulBlastState :=
  mulIterationP.comp ((unaryPred.comp ((listUnaryLength refCode (0,false)).comp binaryLhsP)).pair initializeMulP)
noncomputable def swapBinaryP : Procedure binaryStateCode binaryStateCode swapBinary :=
  (swapAddP.precompose (fun s:BinaryState=>s.val)).result (by intro s;rfl)
noncomputable def mulStateP : Procedure binaryStateCode mulStateCode mulState := by
  let lk:=countKnownP.comp (binaryGraphP.pair binaryLhsP)
  let rk:=countKnownP.comp (binaryGraphP.pair binaryRhsP)
  exact (conditional (binaryLt.comp (lk.pair rk)) mulBlastStateP
    (mulBlastStateP.comp swapBinaryP)).congrFun (by intro s;unfold mulState;split <;> simp_all)
noncomputable def mulP : Procedure binaryStateCode (prodCode graphCode (listCode refCode))
    (fun s=>mul s.val.val.graph s.val.val.lhs s.val.val.rhs):=
  (((addGraphP.pair addOutputP).precompose (fun s:MulState=>s.val)).comp mulStateP).congrFun mulState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGNot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

def notVec (xs : List Ref) : List Ref:=xs.map notRef
lemma notVec_length (xs : List Ref) : (notVec xs).length=xs.length:=List.length_map _
lemma notVec_refs {B : ℕ} {xs : List Ref} (h : RefsBound B xs) : RefsBound B (notVec xs) := by
  refine ⟨by simpa only [notVec_length] using h.1,?_⟩
  intro a ha
  obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha
  exact h.2 b hb
namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def notVecP : Procedure (listCode refCode) (listCode refCode) notVec:=
  listMap (0,false) (0,false) notRefP
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGSub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

def oneVec (w : ℕ) : List Ref:=(List.range w).map (fun i=>(0,decide (i=0)))
lemma oneVec_length (w : ℕ) : (oneVec w).length=w:=by simp [oneVec]
lemma oneVec_refs {B w : ℕ} (h : w≤B) : RefsBound B (oneVec w) := by
  refine ⟨by simpa only [oneVec_length],?_⟩
  intro a ha
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp ha
  exact Nat.zero_le _

def neg (r : Graph) (xs : List Ref) : Graph×List Ref :=add r (notVec xs) (oneVec xs.length)
def sub (r : Graph) (lhs rhs : List Ref) : Graph×List Ref :=
  let s:=neg r rhs
  add s.1 lhs s.2
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGSubProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

lemma neg_bound {B : ℕ} {g : Graph} {xs : List Ref} (hg : Bounded B g) (hx : RefsBound B xs) :
    Bounded (B+13*xs.length) (neg g xs).1 ∧
    RefsBound (B+13*xs.length) (neg g xs).2 ∧ (neg g xs).2.length=xs.length := by
  simpa only [notVec_length,neg] using add_bound hg (notVec_refs hx) (oneVec_refs hx.1)
    (by rw [notVec_length,oneVec_length])
lemma sub_bound {B : ℕ} {g : Graph} {lhs rhs : List Ref}
    (hg : Bounded B g) (hl : RefsBound B lhs) (hr : RefsBound B rhs) (he : lhs.length=rhs.length) :
    Bounded (B+26*lhs.length) (sub g lhs rhs).1 ∧
    RefsBound (B+26*lhs.length) (sub g lhs rhs).2 ∧ (sub g lhs rhs).2.length=lhs.length := by
  have hn:=neg_bound hg hr
  have hh:=add_bound hn.1 (hl.mono (by omega)) hn.2.1 (he.trans hn.2.2.symm)
  have hb : B+13*rhs.length+13*lhs.length=B+26*lhs.length:=by omega
  simpa only [hb,sub] using hh

def negInput (s : AddState) : AddState:=⟨⟨s.val.budget,s.val.graph,notVec s.val.rhs,oneVec s.val.rhs.length,
    0,(0,false),[]⟩,
  s.property.1,notVec_refs s.property.2.2.1,oneVec_refs s.property.2.2.1.1,
    Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
def negState (s : AddState) : AddState:=addState (negInput s)
lemma negState_value (s : AddState) : ((negState s).val.graph,(negState s).val.output)=
    neg s.val.graph s.val.rhs:=addState_value _
lemma negState_budget (s : AddState) : (negState s).val.budget=s.val.budget+13*s.val.rhs.length := by
  have hh:=addState_budget_eq (negInput s) (by dsimp only [negInput];rw [notVec_length,oneVec_length])
  simpa only [negState,negInput,notVec_length] using hh
lemma negState_length (s : AddState) : (negState s).val.output.length=s.val.rhs.length := by
  have hh:=addState_length (negInput s) (by dsimp only [negInput];rw [notVec_length,oneVec_length])
  simpa only [negState,negInput,notVec_length] using hh

def subNext (s : BinaryState) : AddState:=⟨⟨(negState s.val).val.budget,(negState s.val).val.graph,
  s.val.val.lhs,(negState s.val).val.output,0,(0,false),[]⟩,
  (negState s.val).property.1,s.val.property.2.1.mono (by dsimp only;rw [negState_budget];omega),
  (negState s.val).property.2.2.2.2.2,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
def subState (s : BinaryState) : AddState:=addState (subNext s)
lemma subState_value (s : BinaryState) : ((subState s).val.graph,(subState s).val.output)=
    sub s.val.val.graph s.val.val.lhs s.val.val.rhs := by
  have hh:=addState_value (subNext s)
  change _=add (negState s.val).val.graph s.val.val.lhs (negState s.val).val.output at hh
  rw [show (negState s.val).val.graph=(neg s.val.val.graph s.val.val.rhs).1 from
    congrArg Prod.fst (negState_value s.val),show (negState s.val).val.output=(neg s.val.val.graph s.val.val.rhs).2 from
    congrArg Prod.snd (negState_value s.val)] at hh
  exact hh
lemma subState_budget (s : BinaryState) : (subState s).val.budget=s.val.val.budget+26*s.val.val.lhs.length := by
  have hh:=addState_budget_eq (subNext s) (by
    change s.val.val.lhs.length=(negState s.val).val.output.length
    rw [negState_length];exact s.property)
  change (subState s).val.budget=(negState s.val).val.budget+13*s.val.val.lhs.length at hh
  rw [hh,negState_budget,←s.property];omega

end ExactQuantumFactoring.NativeAIG
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_EmissionFurther2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

namespace Emission
noncomputable def oneVecP : Procedure unaryCode (listCode refCode) oneVec := by
  let oneBit:=(Procedure.constant (prodCode unaryCode boolCode) Nat.bits 0).pair
    (unaryZero.comp (first unaryCode boolCode))
  exact ((tabulate (f:=fun (_ : Bool) i => (0,decide (i=0))) (0,false) oneBit).comp
    ((identity unaryCode).pair (Procedure.constant unaryCode boolCode false))).congrFun (by intro w;rfl)
noncomputable def negInputP : Procedure addStateCode addStateCode negInput := by
  let b:=((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)
  let g:=addGraphP.precompose (fun s:AddState=>s.val)
  let rhs:=addRhsP.precompose (fun s:AddState=>s.val)
  let one:=oneVecP.comp ((listUnaryLength refCode (0,false)).comp rhs)
  exact (packAddP.comp (b.pair (g.pair ((notVecP.comp rhs).pair (one.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def negStateP : Procedure addStateCode addStateCode negState:=addStateP.comp negInputP
noncomputable def subNextP : Procedure binaryStateCode addStateCode subNext := by
  let ns:=negStateP.precompose (fun s:BinaryState=>s.val)
  let b:=(((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)).comp ns
  let g:=(addGraphP.precompose (fun s:AddState=>s.val)).comp ns
  let rhs:=(addOutputP.precompose (fun s:AddState=>s.val)).comp ns
  exact (packAddP.comp (b.pair (g.pair (binaryLhsP.pair (rhs.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def subStateP : Procedure binaryStateCode addStateCode subState:=addStateP.comp subNextP
noncomputable def subP : Procedure binaryStateCode (prodCode graphCode (listCode refCode))
    (fun s=>sub s.val.val.graph s.val.val.lhs s.val.val.rhs):=
  (((addGraphP.pair addOutputP).precompose (fun s:AddState=>s.val)).comp subStateP).congrFun subState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGCarry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

def carryLoop : ℕ→Graph→List Ref→List Ref→ℕ→Ref→Graph×Ref
  | 0,r,_,_,_,cin=>(r,cin)
  | k+1,r,lhs,rhs,curr,cin=>
    let s:=fullCarry r ((lhs.drop curr).headD (0,false)) ((rhs.drop curr).headD (0,false)) cin
    carryLoop k s.1 lhs rhs (curr+1) s.2
def overflow (r : Graph) (lhs rhs : List Ref) (cin : Ref) : Graph×Ref :=
  carryLoop lhs.length r lhs rhs 0 cin
def ult (r : Graph) (lhs rhs : List Ref) : Graph×Ref:=
  let s:=overflow r lhs (notVec rhs) (0,true)
  (s.1,notRef s.2)
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGCarryProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def carryStepData (s : AddData) : AddData:=
  let next:=fullCarry s.graph ((s.lhs.drop s.curr).headD (0,false))
    ((s.rhs.drop s.curr).headD (0,false)) s.cin
  ⟨s.budget+6,next.1,s.lhs,s.rhs,s.curr+1,next.2,s.output⟩
lemma carryStep_ok (s : AddState) : AddOK (carryStepData s.val) := by
  obtain ⟨hg,hl,hr,hc,hci,ho⟩:=s.property
  have hh:=fullCarry_bound hg _ _ s.val.cin (hl.get s.val.curr) (hr.get s.val.curr) hci
  dsimp only [AddOK,carryStepData]
  exact ⟨hh.1,hl.mono (by omega),hr.mono (by omega),by omega,hh.2,ho.mono (by omega)⟩
def carryStep (s : AddState) : AddState:=⟨carryStepData s.val,carryStep_ok s⟩
lemma carryStep_budget (s : AddState) : (carryStep s).val.budget=s.val.budget+6:=rfl
lemma carryStep_iterate_budget (s : AddState) (k : ℕ) :
    ((carryStep^[k]) s).val.budget=s.val.budget+6*k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,carryStep_budget];omega
lemma carryStep_iterate_loop (s : AddState) (k : ℕ) :
    (((carryStep^[k]) s).val.graph,((carryStep^[k]) s).val.cin)=
      carryLoop k s.val.graph s.val.lhs s.val.rhs s.val.curr s.val.cin := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl

def overflowState (s : AddState) : AddState:=(carryStep^[s.val.lhs.length]) (initializeIf s)
lemma overflowState_value (s : AddState) : ((overflowState s).val.graph,(overflowState s).val.cin)=
    overflow s.val.graph s.val.lhs s.val.rhs s.val.cin:=carryStep_iterate_loop _ _
lemma overflowState_budget (s : AddState) : (overflowState s).val.budget=s.val.budget+6*s.val.lhs.length:=
  carryStep_iterate_budget _ _
def ultInput (s : AddState) : AddState:=⟨⟨s.val.budget,s.val.graph,s.val.lhs,notVec s.val.rhs,0,(0,true),[]⟩,
  s.property.1,s.property.2.1,notVec_refs s.property.2.2.1,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,
  by intro a ha;cases ha⟩
def ultState (s : AddState) : AddState:=overflowState (ultInput s)
lemma ultState_value (s : AddState) : ((ultState s).val.graph,notRef (ultState s).val.cin)=
    ult s.val.graph s.val.lhs s.val.rhs :=by
  have hh:=overflowState_value (ultInput s)
  exact congrArg (fun x : Graph×Ref=>(x.1,notRef x.2)) hh
lemma ult_bound {B : ℕ} {g : Graph} {lhs rhs : List Ref}
    (hg : Bounded B g) (hl : RefsBound B lhs) (hr : RefsBound B rhs) :
    Bounded (B+6*lhs.length) (ult g lhs rhs).1 ∧ (ult g lhs rhs).2.1≤B+6*lhs.length := by
  let s : AddState:=⟨⟨B,g,lhs,rhs,0,(0,false),[]⟩,
    hg,hl,hr,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
  have hh:=(ultState s).property
  have hb:=overflowState_budget (ultInput s)
  rw [←ultState_value s]
  change Bounded (B+6*lhs.length) (ultState s).val.graph ∧ (ultState s).val.cin.1≤B+6*lhs.length
  change (ultState s).val.budget=B+6*lhs.length at hb
  rw [←hb]
  exact ⟨hh.1,hh.2.2.2.2.1⟩
namespace Emission
noncomputable def carryStepDataP : Procedure addDataCode addDataCode carryStepData := by
  let b:=unaryAdd.comp (((first unaryCode addTail1).comp addViewP).pair (Procedure.constant _ unaryCode 6))
  let lhs:=(listGet refCode (0,false)).comp (addCurrP.pair addLhsP)
  let rhs:=(listGet refCode (0,false)).comp (addCurrP.pair addRhsP)
  let s:=fullCarryP.comp (addGraphP.pair (lhs.pair (rhs.pair addCinP)))
  let g:=(first graphCode refCode).comp s
  let c:=(second graphCode refCode).comp s
  exact (packAddP.comp (b.pair (g.pair (addLhsP.pair (addRhsP.pair
    ((successor.comp addCurrP).pair (c.pair addOutputP))))))).congrFun (by intro s;rfl)
noncomputable def carryStepP : Procedure addStateCode addStateCode carryStep:=
  (carryStepDataP.precompose (fun s:AddState=>s.val)).result (by intro s;rfl)
noncomputable def carryIterationP : Procedure (prodCode unaryCode addStateCode) addStateCode
    (fun x=>(carryStep^[x.1]) x.2):=
  carryStepP.iterate (Polynomial.C 10800*(Polynomial.X+1)^2) (by
    intro n s i hi
    have hh:=addStateCode_bound ((carryStep^[i]) s)
    rw [carryStep_iterate_budget] at hh
    have hb:=budget_le_code s
    have h : s.val.budget+6*i+1 ≤ 6*(n+(addStateCode s).length+1):=by omega
    have hp:=Nat.pow_le_pow_left h 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    nlinarith)
noncomputable def overflowStateP : Procedure addStateCode addStateCode overflowState:=
  carryIterationP.comp (((listUnaryLength refCode (0,false)).comp
    (addLhsP.precompose (fun s:AddState=>s.val))).pair initializeIfP)
noncomputable def ultInputP : Procedure addStateCode addStateCode ultInput := by
  let b:=((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)
  let g:=addGraphP.precompose (fun s:AddState=>s.val)
  let lhs:=addLhsP.precompose (fun s:AddState=>s.val)
  let rhs:=notVecP.comp (addRhsP.precompose (fun s:AddState=>s.val))
  exact (packAddP.comp (b.pair (g.pair (lhs.pair (rhs.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,true)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def ultStateP : Procedure addStateCode addStateCode ultState:=overflowStateP.comp ultInputP
noncomputable def ultP : Procedure addStateCode (prodCode graphCode refCode)
    (fun s=>ult s.val.graph s.val.lhs s.val.rhs) :=
  ((((addGraphP.pair (notRefP.comp addCinP)).precompose (fun s:AddState=>s.val)).comp ultStateP)).congrFun
    ultState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGExtend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

def extend (xs : List Ref) (w : ℕ) : List Ref:=
  (List.range w).map (fun i=>(xs.drop i).headD (0,false))
lemma extend_length (xs : List Ref) (w : ℕ) : (extend xs w).length=w:=by simp [extend]
def shiftConcat (xs : List Ref) (a : Ref) : List Ref:=extend (a::xs) xs.length
lemma shiftConcat_length (xs : List Ref) (a : Ref) : (shiftConcat xs a).length=xs.length:=extend_length _ _
lemma shiftConcat_refs {B : ℕ} {xs : List Ref} {a : Ref} (hx : RefsBound B xs) (ha : a.1≤B) :
    RefsBound B (shiftConcat xs a) := by
  refine ⟨by simpa only [shiftConcat_length] using hx.1,?_⟩
  intro b hb
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp hb
  cases i with
  | zero=>simpa using ha
  | succ i=>simpa using hx.get i
namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def extendP : Procedure (prodCode unaryCode (listCode refCode)) (listCode refCode)
    (fun x=>extend x.2 x.1):=
  tabulate (f:=fun (xs : List Ref) i=>(xs.drop i).headD (0,false)) (0,false)
    ((listGet refCode (0,false)).comp
      ((unaryToBits.comp (first unaryCode (listCode refCode))).pair (second unaryCode (listCode refCode))))
noncomputable def shiftConcatP : Procedure (prodCode (listCode refCode) refCode) (listCode refCode)
    (fun x=>shiftConcat x.1 x.2) := by
  let xs:=first (listCode refCode) refCode
  let a:=second (listCode refCode) refCode
  exact extendP.comp (((listUnaryLength refCode (0,false)).comp xs).pair
    ((listCons refCode).comp (a.pair xs)))
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGZipFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat

abbrev BinOp:=Graph→Ref→Ref→Graph×Ref
def zipLoop (op : BinOp) : ℕ→Graph→List Ref→List Ref→ℕ→List Ref→Graph×List Ref
  | 0,r,_,_,_,out=>(r,out)
  | k+1,r,lhs,rhs,curr,out=>
    let s:=op r ((lhs.drop curr).headD (0,false)) ((rhs.drop curr).headD (0,false))
    zipLoop op k s.1 lhs rhs (curr+1) (out++[s.2])
def zipVec (op : BinOp) (r : Graph) (lhs rhs : List Ref) : Graph×List Ref:=
  zipLoop op lhs.length r lhs rhs 0 []
def foldLoop (op : BinOp) : ℕ→Graph→List Ref→ℕ→Ref→Graph×Ref
  | 0,r,_,_,acc=>(r,acc)
  | k+1,r,xs,curr,acc=>
    let s:=op r acc ((xs.drop curr).headD (0,false))
    foldLoop op k s.1 xs (curr+1) s.2
def foldVec (op : BinOp) (r : Graph) (xs : List Ref) : Graph×Ref:=
  foldLoop op xs.length r xs 0 (0,true)

def eqGate (r : Graph) (a b : Ref) : Graph×Ref:=xorGate r a (notRef b)

def eqVec (r : Graph) (lhs rhs : List Ref) : Graph×Ref:=
  let s:=zipVec eqGate r lhs rhs
  foldVec gate s.1 s.2
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGDiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide Std.Tactic.BVDecide.BVExpr.bitblast

def divStep (g : Graph) (lhs rhs : List Ref) (wn : ℕ) (q rem : List Ref) : Graph×(List Ref×List Ref):=
  let r':=shiftConcat rem ((lhs.drop (wn-1)).headD (0,false))
  let posQ:=shiftConcat q (0,false)
  let negQ:=shiftConcat q (0,true)
  let negR:=sub g r' rhs
  let discr:=ult negR.1 r' rhs
  let nextQ:=ifVec discr.1 discr.2 posQ negQ
  let nextR:=ifVec nextQ.1 discr.2 r' negR.2
  (nextR.1,nextQ.2,nextR.2)
def divLoop : ℕ→Graph→List Ref→List Ref→ℕ→List Ref→List Ref→Graph×(List Ref×List Ref)
  | 0,g,_,_,_,q,rem=>(g,q,rem)
  | k+1,g,lhs,rhs,wn,q,rem=>
    let s:=divStep g lhs rhs wn q rem
    divLoop k s.1 lhs rhs (wn-1) s.2.1 s.2.2
def divide (g : Graph) (lhs rhs : List Ref) : Graph×List Ref:=
  let zero:=List.replicate lhs.length (0,false)
  let d:=eqVec g rhs zero
  let out:=divLoop lhs.length d.1 lhs rhs lhs.length zero zero
  ifVec out.1 d.2 zero out.2.1

end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGDivBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
lemma divStep_bound {B : ℕ} {g : Graph} {lhs rhs q rem : List Ref} (wn : ℕ)
    (hg : Bounded B g) (hl : RefsBound B lhs) (hr : RefsBound B rhs)
    (hq : RefsBound B q) (hm : RefsBound B rem)
    (he : lhs.length=rhs.length) (hql : q.length=lhs.length) (hml : rem.length=lhs.length) :
    Bounded (B+38*lhs.length) (divStep g lhs rhs wn q rem).1 ∧
    RefsBound (B+38*lhs.length) (divStep g lhs rhs wn q rem).2.1 ∧
    RefsBound (B+38*lhs.length) (divStep g lhs rhs wn q rem).2.2 ∧
    (divStep g lhs rhs wn q rem).2.1.length=lhs.length ∧
    (divStep g lhs rhs wn q rem).2.2.length=lhs.length := by
  let r':=shiftConcat rem ((lhs.drop (wn-1)).headD (0,false))
  let posQ:=shiftConcat q (0,false)
  let negQ:=shiftConcat q (0,true)
  have hm' : RefsBound B r':=shiftConcat_refs hm (hl.get _)
  have hpq : RefsBound B posQ:=shiftConcat_refs hq (Nat.zero_le _)
  have hnq : RefsBound B negQ:=shiftConcat_refs hq (Nat.zero_le _)
  have hrlen : r'.length=lhs.length:=(shiftConcat_length _ _).trans hml
  have hplen : posQ.length=lhs.length:=(shiftConcat_length _ _).trans hql
  have hsub:=sub_bound hg hm' hr (hrlen.trans he)
  rw [hrlen] at hsub
  have hu:=ult_bound hsub.1 (hm'.mono (by omega)) (hr.mono (by omega))
  rw [hrlen] at hu
  have ht:=ifVec_bound hu.1 (hpq.mono (by omega)) (hnq.mono (by omega)) hu.2
  rw [hplen] at ht
  have ho:=ifVec_bound ht.1 (hm'.mono (by omega)) (hsub.2.1.mono (by omega)) (hu.2.trans (by omega))
  rw [hrlen] at ho
  have hB : B+26*lhs.length+6*lhs.length+3*lhs.length+3*lhs.length=B+38*lhs.length:=by omega
  rw [hB] at ho
  exact ⟨ho.1,ht.2.1.mono (by omega),ho.2.1,ht.2.2,ho.2.2⟩

structure DivData where
  base : AddData
  quotient : List Ref

def DivOK (s : DivData) : Prop:=
  AddOK s.base ∧ s.base.lhs.length=s.base.rhs.length ∧
    s.base.output.length=s.base.lhs.length ∧ RefsBound s.base.budget s.quotient ∧
    s.quotient.length=s.base.lhs.length
abbrev DivState:={s : DivData // DivOK s}
def divDataCode (s : DivData) : List Bool:=prodCode addDataCode (listCode refCode) (s.base,s.quotient)
def divStateCode (s : DivState) : List Bool:=divDataCode s.val

def divStepData (s : DivData) : DivData:=
  let ss:=divStep s.base.graph s.base.lhs s.base.rhs s.base.curr s.quotient s.base.output
  ⟨⟨s.base.budget+38*s.base.lhs.length,ss.1,s.base.lhs,s.base.rhs,s.base.curr-1,s.base.cin,ss.2.2⟩,ss.2.1⟩
lemma divStep_ok (s : DivState) : DivOK (divStepData s.val) := by
  obtain ⟨⟨hg,hl,hr,hc,hci,ho⟩,he,hm,hq,hql⟩:=s.property
  have hh:=divStep_bound s.val.base.curr hg hl hr hq ho he hql hm
  have hb : s.val.base.budget ≤ s.val.base.budget+38*s.val.base.lhs.length:=by omega
  exact ⟨⟨hh.1,hl.mono hb,hr.mono hb,by dsimp only [divStepData];omega,hci.trans hb,hh.2.2.1⟩,
    he,hh.2.2.2.2,hh.2.1,hh.2.2.2.1⟩
def divStepState (s : DivState) : DivState:=⟨divStepData s.val,divStep_ok s⟩
lemma divStepState_budget (s : DivState) :
    (divStepState s).val.base.budget=s.val.base.budget+38*s.val.base.lhs.length:=rfl
lemma divStepState_lhs (s : DivState) : (divStepState s).val.base.lhs=s.val.base.lhs:=rfl
lemma divStepState_iterate_lhs (s : DivState) (k : ℕ) :
    ((divStepState^[k]) s).val.base.lhs=s.val.base.lhs:=by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih,divStepState_lhs]
lemma divStepState_iterate_budget (s : DivState) (k : ℕ) :
    ((divStepState^[k]) s).val.base.budget=s.val.base.budget+38*s.val.base.lhs.length*k:=by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,divStepState_budget,divStepState_lhs];ring
lemma divStepState_iterate_loop (s : DivState) (k : ℕ) :
    (((divStepState^[k]) s).val.base.graph,((divStepState^[k]) s).val.quotient,
      ((divStepState^[k]) s).val.base.output)=
    divLoop k s.val.base.graph s.val.base.lhs s.val.base.rhs s.val.base.curr s.val.quotient s.val.base.output:=by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl
lemma divStateCode_bound (s : DivState) : (divStateCode s).length≤1000*(s.val.base.budget+1)^2 := by
  have ha:=addStateCode_bound ⟨s.val.base,s.property.1⟩
  have hq:=refsCode_bound s.property.2.2.2.1
  simp only [divStateCode,divDataCode,prodCode,pairBits_length]
  change _≤_ at hq
  dsimp only [addStateCode] at ha
  nlinarith [Nat.zero_le s.val.base.budget]
lemma divBudget_le_code (s : DivState) : s.val.base.budget≤(divStateCode s).length := by
  have ha:=budget_le_code ⟨s.val.base,s.property.1⟩
  simp only [divStateCode,divDataCode,prodCode,pairBits_length]
  dsimp only [addStateCode] at ha
  omega
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGDivOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def divSubInput (s : DivState) : BinaryState:=
  ⟨⟨⟨s.val.base.budget,s.val.base.graph,
      shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false)),
      s.val.base.rhs,0,(0,false),[]⟩,
    s.property.1.1,shiftConcat_refs s.property.1.2.2.2.2.2 (s.property.1.2.1.get _),s.property.1.2.2.1,
    Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩,
    (shiftConcat_length _ _).trans (s.property.2.2.1.trans s.property.2.1)⟩
def divSubState (s : DivState) : AddState:=subState (divSubInput s)
lemma divSub_budget (s : DivState) :
    (divSubState s).val.budget=s.val.base.budget+26*s.val.base.lhs.length:=by
  rw [divSubState,subState_budget]
  change s.val.base.budget+26*(shiftConcat _ _).length=_
  rw [shiftConcat_length,s.property.2.2.1]
lemma divSub_value (s : DivState) : ((divSubState s).val.graph,(divSubState s).val.output)=
    sub s.val.base.graph
      (shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false))) s.val.base.rhs:=
  subState_value _
def divUltInput (s : DivState) : AddState:=
  ⟨⟨(divSubState s).val.budget,(divSubState s).val.graph,
    shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false)),
    s.val.base.rhs,0,(0,false),[]⟩,
  (divSubState s).property.1,
  (shiftConcat_refs s.property.1.2.2.2.2.2 (s.property.1.2.1.get _)).mono (by rw [divSub_budget];omega),
  s.property.1.2.2.1.mono (by rw [divSub_budget];omega),Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
def divUltState (s : DivState) : AddState:=ultState (divUltInput s)
lemma ultState_budget (s : AddState) : (ultState s).val.budget=s.val.budget+6*s.val.lhs.length:=
  overflowState_budget (ultInput s)
lemma divUlt_budget (s : DivState) :
    (divUltState s).val.budget=s.val.base.budget+32*s.val.base.lhs.length:=by
  rw [divUltState,ultState_budget]
  change (divSubState s).val.budget+
    6*(shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false))).length=_
  rw [divSub_budget,shiftConcat_length,s.property.2.2.1];omega
lemma divUlt_value (s : DivState) : ((divUltState s).val.graph,notRef (divUltState s).val.cin)=
    ult (sub s.val.base.graph
      (shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false))) s.val.base.rhs).1
      (shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false))) s.val.base.rhs:=by
  have hh:=ultState_value (divUltInput s)
  change _=ult (divSubState s).val.graph _ _ at hh
  rw [show (divSubState s).val.graph=_ from congrArg Prod.fst (divSub_value s)] at hh
  exact hh

def divQInput (s : DivState) : AddState:=
  ⟨⟨(divUltState s).val.budget,(divUltState s).val.graph,
    shiftConcat s.val.quotient (0,false),shiftConcat s.val.quotient (0,true),0,
    notRef (divUltState s).val.cin,[]⟩,
  (divUltState s).property.1,
  (shiftConcat_refs s.property.2.2.2.1 (Nat.zero_le _)).mono (by rw [divUlt_budget];omega),
  (shiftConcat_refs s.property.2.2.2.1 (Nat.zero_le _)).mono (by rw [divUlt_budget];omega),
  Nat.zero_le _,(divUltState s).property.2.2.2.2.1,Nat.zero_le _,by intro a ha;cases ha⟩
def divQState (s : DivState) : AddState:=ifVecState (divQInput s)
lemma divQ_budget (s : DivState) : (divQState s).val.budget=s.val.base.budget+35*s.val.base.lhs.length:=by
  rw [divQState,ifVecState_budget]
  change (divUltState s).val.budget+3*(shiftConcat s.val.quotient (0,false)).length=_
  rw [divUlt_budget,shiftConcat_length,s.property.2.2.2.2];omega
def divRInput (s : DivState) : AddState:=
  ⟨⟨(divQState s).val.budget,(divQState s).val.graph,
    shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false)),
    (divSubState s).val.output,0,notRef (divUltState s).val.cin,[]⟩,
  (divQState s).property.1,
  (shiftConcat_refs s.property.1.2.2.2.2.2 (s.property.1.2.1.get _)).mono (by rw [divQ_budget];omega),
  (divSubState s).property.2.2.2.2.2.mono (by rw [divSub_budget,divQ_budget];omega),Nat.zero_le _,
  (divUltState s).property.2.2.2.2.1.trans (by rw [divUlt_budget,divQ_budget];omega),
  Nat.zero_le _,by intro a ha;cases ha⟩
def divRState (s : DivState) : AddState:=ifVecState (divRInput s)
lemma divQR_value (s : DivState) :
    ((divRState s).val.graph,(divQState s).val.output,(divRState s).val.output)=
      divStep s.val.base.graph s.val.base.lhs s.val.base.rhs s.val.base.curr s.val.quotient s.val.base.output:=by
  have hq:=ifVecState_value (divQInput s)
  have hr:=ifVecState_value (divRInput s)
  change ((divQState s).val.graph,(divQState s).val.output)=ifVec (divUltState s).val.graph
    (notRef (divUltState s).val.cin) (shiftConcat s.val.quotient (0,false)) (shiftConcat s.val.quotient (0,true)) at hq
  change ((divRState s).val.graph,(divRState s).val.output)=ifVec (divQState s).val.graph
    (notRef (divUltState s).val.cin)
    (shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false)))
    (divSubState s).val.output at hr
  have h2:=congrArg Prod.snd (divSub_value s)
  have h3:=congrArg Prod.fst (divUlt_value s)
  have h4:=congrArg Prod.snd (divUlt_value s)
  dsimp only [Prod.fst,Prod.snd] at h2 h3 h4
  rw [h3,h4] at hq
  rw [show (divQState s).val.graph=_ from congrArg Prod.fst hq,h4,h2] at hr
  dsimp only [divStep]
  apply Prod.ext
  · exact congrArg (fun x : Graph×List Ref=>x.1) hr
  · apply Prod.ext
    · exact congrArg (fun x : Graph×List Ref=>x.2) hq
    · exact congrArg (fun x : Graph×List Ref=>x.2) hr
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGDivProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG.Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def stateBudgetP : Procedure addStateCode unaryCode (fun s=>s.val.budget):=
  ((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)
noncomputable def stateGraphP : Procedure addStateCode graphCode (fun s=>s.val.graph):=
  addGraphP.precompose (fun s:AddState=>s.val)
noncomputable def stateOutputP : Procedure addStateCode (listCode refCode) (fun s=>s.val.output):=
  addOutputP.precompose (fun s:AddState=>s.val)
noncomputable def stateNotCinP : Procedure addStateCode refCode (fun s=>notRef s.val.cin):=
  (notRefP.comp addCinP).precompose (fun s:AddState=>s.val)
noncomputable def divBaseP : Procedure divStateCode addDataCode (fun s=>s.val.base):=
  (first addDataCode (listCode refCode)).precompose (fun s:DivState=>(s.val.base,s.val.quotient))
noncomputable def divQuotientP : Procedure divStateCode (listCode refCode) (fun s=>s.val.quotient):=
  (second addDataCode (listCode refCode)).precompose (fun s:DivState=>(s.val.base,s.val.quotient))
noncomputable def divBudgetP : Procedure divStateCode unaryCode (fun s=>s.val.base.budget):=
  ((first unaryCode addTail1).comp addViewP).comp divBaseP
noncomputable def divGraphP : Procedure divStateCode graphCode (fun s=>s.val.base.graph):=addGraphP.comp divBaseP
noncomputable def divLhsP : Procedure divStateCode (listCode refCode) (fun s=>s.val.base.lhs):=addLhsP.comp divBaseP
noncomputable def divRhsP : Procedure divStateCode (listCode refCode) (fun s=>s.val.base.rhs):=addRhsP.comp divBaseP
noncomputable def divRemP : Procedure divStateCode (listCode refCode) (fun s=>s.val.base.output):=addOutputP.comp divBaseP
noncomputable def divCurrP : Procedure divStateCode Nat.bits (fun s=>s.val.base.curr):=addCurrP.comp divBaseP
noncomputable def divCinP : Procedure divStateCode refCode (fun s=>s.val.base.cin):=addCinP.comp divBaseP
noncomputable def divPredP : Procedure divStateCode Nat.bits (fun s=>s.val.base.curr-1):=
  binarySub.comp (divCurrP.pair (Procedure.constant _ Nat.bits 1))
noncomputable def divShiftRemP : Procedure divStateCode (listCode refCode)
    (fun s=>shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false))):=
  shiftConcatP.comp (divRemP.pair ((listGet refCode (0,false)).comp (divPredP.pair divLhsP)))
noncomputable def divSubInputP : Procedure divStateCode binaryStateCode divSubInput := by
  exact (packAddP.comp (divBudgetP.pair (divGraphP.pair (divShiftRemP.pair (divRhsP.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def divSubStateP : Procedure divStateCode addStateCode divSubState:=subStateP.comp divSubInputP
noncomputable def divUltInputP : Procedure divStateCode addStateCode divUltInput := by
  let b:=stateBudgetP.comp divSubStateP
  let g:=stateGraphP.comp divSubStateP
  exact (packAddP.comp (b.pair (g.pair (divShiftRemP.pair (divRhsP.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def divUltStateP : Procedure divStateCode addStateCode divUltState:=ultStateP.comp divUltInputP
noncomputable def divQInputP : Procedure divStateCode addStateCode divQInput := by
  let b:=stateBudgetP.comp divUltStateP
  let g:=stateGraphP.comp divUltStateP
  let c:=stateNotCinP.comp divUltStateP
  let q0:=shiftConcatP.comp (divQuotientP.pair (Procedure.constant _ refCode (0,false)))
  let q1:=shiftConcatP.comp (divQuotientP.pair (Procedure.constant _ refCode (0,true)))
  exact (packAddP.comp (b.pair (g.pair (q0.pair (q1.pair
    ((Procedure.constant _ Nat.bits 0).pair (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result
      (by intro s;rfl)
noncomputable def divQStateP : Procedure divStateCode addStateCode divQState:=ifVecStateP.comp divQInputP
noncomputable def divRInputP : Procedure divStateCode addStateCode divRInput := by
  let b:=stateBudgetP.comp divQStateP
  let g:=stateGraphP.comp divQStateP
  let c:=stateNotCinP.comp divUltStateP
  let nr:=stateOutputP.comp divSubStateP
  exact (packAddP.comp (b.pair (g.pair (divShiftRemP.pair (nr.pair
    ((Procedure.constant _ Nat.bits 0).pair (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result
      (by intro s;rfl)
noncomputable def divRStateP : Procedure divStateCode addStateCode divRState:=ifVecStateP.comp divRInputP
noncomputable def divNextP : Procedure divStateCode
    (prodCode graphCode (prodCode (listCode refCode) (listCode refCode)))
    (fun s=>divStep s.val.base.graph s.val.base.lhs s.val.base.rhs s.val.base.curr s.val.quotient s.val.base.output):=
  ((stateGraphP.comp divRStateP).pair ((stateOutputP.comp divQStateP).pair
    (stateOutputP.comp divRStateP))).congrFun divQR_value
noncomputable def divStepStateP : Procedure divStateCode divStateCode divStepState := by
  let ns:=divNextP
  let g:=(first graphCode _).comp ns
  let q:=(first (listCode refCode) (listCode refCode)).comp ((second graphCode _).comp ns)
  let r:=(second (listCode refCode) (listCode refCode)).comp ((second graphCode _).comp ns)
  let len:=(listUnaryLength refCode (0,false)).comp divLhsP
  let b:=unaryAdd.comp (divBudgetP.pair (unaryMul.comp ((Procedure.constant _ unaryCode 38).pair len)))
  let base:=packAddP.comp (b.pair (g.pair (divLhsP.pair (divRhsP.pair (divPredP.pair (divCinP.pair r))))))
  exact (base.pair q).result (by intro s;rfl)
noncomputable def divIterationP : Procedure (prodCode unaryCode divStateCode) divStateCode
    (fun x=>(divStepState^[x.1]) x.2):=
  divStepStateP.iterate (Polynomial.C 1521000*(Polynomial.X+1)^4) (by
    intro n s i hi
    have hh:=divStateCode_bound ((divStepState^[i]) s)
    rw [divStepState_iterate_budget] at hh
    have hb:=divBudget_le_code s
    have hl:=s.property.1.2.1.1
    let M:=n+(divStateCode s).length+1
    have hM : 1≤M:=by dsimp [M];omega
    have hB : s.val.base.budget+1≤M:=by dsimp [M];omega
    have hw : 38*s.val.base.lhs.length≤38*M:=by omega
    have hii : i≤M:=by dsimp [M];omega
    have hm:=Nat.mul_le_mul hw hii
    have hx : s.val.base.budget+38*s.val.base.lhs.length*i+1≤39*M^2:=by nlinarith
    have hp:=Nat.pow_le_pow_left hx 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    calc
      (divStateCode ((divStepState^[i]) s)).length≤1000*(s.val.base.budget+38*s.val.base.lhs.length*i+1)^2:=hh
      _ ≤ 1000*(39*M^2)^2:=Nat.mul_le_mul_left _ hp
      _ = 1521000*(n+(divStateCode s).length+1)^4:=by dsimp [M] <;> ring)
end ExactQuantumFactoring.NativeAIG.Emission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGZipFoldProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def BinBound (C : ℕ) (op : BinOp) : Prop:=∀{B : ℕ} {r : Graph},Bounded B r→∀a b,
  a.1≤B→b.1≤B→Bounded (B+C) (op r a b).1 ∧ (op r a b).2.1≤B+C

def binaryStepData (collect : Bool) (C : ℕ) (op : BinOp) (s : AddData) : AddData:=
  let a:=if collect then (s.lhs.drop s.curr).headD (0,false) else s.cin
  let ss:=op s.graph a ((s.rhs.drop s.curr).headD (0,false))
  ⟨s.budget+C+1,ss.1,s.lhs,s.rhs,s.curr+1,ss.2,if collect then s.output++[ss.2] else s.output⟩
lemma binaryStep_ok (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    AddOK (binaryStepData collect C op s.val) := by
  obtain ⟨hg,hl,hr,hc,hci,ho⟩:=s.property
  have ha : (if collect then ((s.val.lhs.drop s.val.curr).headD (0,false)) else s.val.cin).1 ≤ s.val.budget:=by
    cases collect <;> simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true] <;> first | exact hci | exact hl.get _
  have hh:=hop hg _ _ ha (hr.get s.val.curr)
  dsimp only [AddOK,binaryStepData]
  refine ⟨hh.1.mono (by omega),hl.mono (by omega),hr.mono (by omega),by omega,hh.2.trans (by omega),?_⟩
  cases collect <;> simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  · exact ho.mono (by omega)
  · refine ⟨by simp only [List.length_append,List.length_singleton];have:=ho.1;omega,?_⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (ho.2 a ha).trans (by omega)
    · have he:=List.mem_singleton.mp ha
      rw [he];exact hh.2.trans (by omega)
def binaryStep (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) : AddState:=
  ⟨binaryStepData collect C op s.val,binaryStep_ok collect hop s⟩
lemma binaryStep_budget (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    (binaryStep collect hop s).val.budget=s.val.budget+C+1:=rfl
lemma binaryStep_iterate_budget (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) (k : ℕ) :
    ((binaryStep collect hop)^[k] s).val.budget=s.val.budget+(C+1)*k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,binaryStep_budget];ring
lemma binaryStep_zipLoop {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) (k : ℕ) :
    (((binaryStep true hop)^[k] s).val.graph,((binaryStep true hop)^[k] s).val.output)=
      zipLoop op k s.val.graph s.val.lhs s.val.rhs s.val.curr s.val.output := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl
lemma binaryStep_foldLoop {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) (k : ℕ) :
    (((binaryStep false hop)^[k] s).val.graph,((binaryStep false hop)^[k] s).val.cin)=
      foldLoop op k s.val.graph s.val.rhs s.val.curr s.val.cin := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl
lemma binaryStep_zipLength {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) (k : ℕ) :
    ((binaryStep true hop)^[k] s).val.output.length=s.val.output.length+k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih];simp only [binaryStep,binaryStepData,ite_true, if_true,
      List.length_append,List.length_singleton];omega

def zipState {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) : AddState:=
  (binaryStep true hop)^[s.val.lhs.length] (initializeAdd s)
lemma zipState_value {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    ((zipState hop s).val.graph,(zipState hop s).val.output)=zipVec op s.val.graph s.val.lhs s.val.rhs:=
  binaryStep_zipLoop hop _ _
lemma zipState_budget {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    (zipState hop s).val.budget=s.val.budget+(C+1)*s.val.lhs.length:=binaryStep_iterate_budget _ _ _ _
lemma zipState_length {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    (zipState hop s).val.output.length=s.val.lhs.length:=by
  unfold zipState
  rw [binaryStep_zipLength]
  simp only [initializeAdd,initializeAddData,List.length_nil,Nat.zero_add]

def initializeFold (s : AddState) : AddState:=⟨⟨s.val.budget,s.val.graph,s.val.lhs,s.val.rhs,0,(0,true),[]⟩,
  s.property.1,s.property.2.1,s.property.2.2.1,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
def foldState {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) : AddState:=
  (binaryStep false hop)^[s.val.rhs.length] (initializeFold s)
lemma foldState_value {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    ((foldState hop s).val.graph,(foldState hop s).val.cin)=foldVec op s.val.graph s.val.rhs:=
  binaryStep_foldLoop hop _ _
lemma foldState_budget {C : ℕ} {op : BinOp} (hop : BinBound C op) (s : AddState) :
    (foldState hop s).val.budget=s.val.budget+(C+1)*s.val.rhs.length:=binaryStep_iterate_budget _ _ _ _

namespace Emission
noncomputable def binaryStepDataP (collect : Bool) (C : ℕ) {op : BinOp}
    (p : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode) (fun x=>op x.1 x.2.1 x.2.2)) :
    Procedure addDataCode addDataCode (binaryStepData collect C op) := by
  let b:=(unaryAdd.comp (((first unaryCode addTail1).comp addViewP).pair (Procedure.constant _ unaryCode (C+1))))
  let a:=conditional (Procedure.constant _ boolCode collect)
    ((listGet refCode (0,false)).comp (addCurrP.pair addLhsP)) addCinP
  let rhs:=(listGet refCode (0,false)).comp (addCurrP.pair addRhsP)
  let ss:=p.comp (addGraphP.pair (a.pair rhs))
  let g:=(first graphCode refCode).comp ss
  let c:=(second graphCode refCode).comp ss
  let out:=conditional (Procedure.constant _ boolCode collect)
    ((listAppend refCode (0,false)).comp (addOutputP.pair ((singleton refCode).comp c))) addOutputP
  exact (packAddP.comp (b.pair (g.pair (addLhsP.pair (addRhsP.pair
    ((successor.comp addCurrP).pair (c.pair out))))))).congrFun (by
      intro s;cases collect <;> simp only [binaryStepData,Nat.add_assoc,Function.comp_apply,
        Bool.false_eq_true,ite_true, if_true,ite_false, if_false,addDataView])
noncomputable def binaryStepP (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op)
    (p : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode) (fun x=>op x.1 x.2.1 x.2.2)) :
    Procedure addStateCode addStateCode (binaryStep collect hop):=
  ((binaryStepDataP collect C p).precompose (fun s:AddState=>s.val)).result (by intro s;rfl)
noncomputable def binaryIterationP (collect : Bool) {C : ℕ} {op : BinOp} (hop : BinBound C op)
    (p : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode) (fun x=>op x.1 x.2.1 x.2.2)) :
    Procedure (prodCode unaryCode addStateCode) addStateCode (fun x=>(binaryStep collect hop)^[x.1] x.2):=
  (binaryStepP collect hop p).iterate (Polynomial.C (300*(C+1)^2)*(Polynomial.X+1)^2) (by
    intro n s i hi
    have hh:=addStateCode_bound ((binaryStep collect hop)^[i] s)
    rw [binaryStep_iterate_budget] at hh
    have hb:=budget_le_code s
    have hs : s.val.budget+1≤(C+1)*((addStateCode s).length+1):=by nlinarith
    have hn:=Nat.mul_le_mul_left (C+1) hi
    have h : s.val.budget+(C+1)*i+1≤(C+1)*(n+(addStateCode s).length+1):=by nlinarith
    have hp:=Nat.pow_le_pow_left h 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    nlinarith)
noncomputable def zipStateP {C : ℕ} {op : BinOp} (hop : BinBound C op)
    (p : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode) (fun x=>op x.1 x.2.1 x.2.2)) :
    Procedure addStateCode addStateCode (zipState hop):=
  (binaryIterationP true hop p).comp (((listUnaryLength refCode (0,false)).comp
    (addLhsP.precompose (fun s:AddState=>s.val))).pair initializeAddP)
noncomputable def initializeFoldP : Procedure addStateCode addStateCode initializeFold := by
  let b:=((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)
  let g:=addGraphP.precompose (fun s:AddState=>s.val)
  let lhs:=addLhsP.precompose (fun s:AddState=>s.val)
  let rhs:=addRhsP.precompose (fun s:AddState=>s.val)
  exact (packAddP.comp (b.pair (g.pair (lhs.pair (rhs.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,true)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def foldStateP {C : ℕ} {op : BinOp} (hop : BinBound C op)
    (p : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode) (fun x=>op x.1 x.2.1 x.2.2)) :
    Procedure addStateCode addStateCode (foldState hop):=
  (binaryIterationP false hop p).comp (((listUnaryLength refCode (0,false)).comp
    (addRhsP.precompose (fun s:AddState=>s.val))).pair initializeFoldP)
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGEqProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
lemma eqGate_bound : BinBound 3 eqGate:=fun h a b ha hb=>xorGate_bound h a (notRef b) ha hb
lemma andGate_bound : BinBound 1 gate:=fun h a b ha hb=>gate_bound h a b ha hb

def eqNext (s : AddState) : AddState:=
  let z:=zipState eqGate_bound s
  ⟨⟨z.val.budget,z.val.graph,z.val.output,z.val.output,0,(0,true),[]⟩,
  z.property.1,z.property.2.2.2.2.2,z.property.2.2.2.2.2,Nat.zero_le _,Nat.zero_le _,
    Nat.zero_le _,by intro a ha;cases ha⟩
def eqState (s : AddState) : AddState:=foldState andGate_bound (eqNext s)
lemma eqState_value (s : AddState) : ((eqState s).val.graph,(eqState s).val.cin)=
    eqVec s.val.graph s.val.lhs s.val.rhs := by
  have hf:=foldState_value andGate_bound (eqNext s)
  change _=foldVec gate (zipState eqGate_bound s).val.graph (zipState eqGate_bound s).val.output at hf
  rw [show (zipState eqGate_bound s).val.graph=(zipVec eqGate s.val.graph s.val.lhs s.val.rhs).1 from
    congrArg Prod.fst (zipState_value eqGate_bound s),
    show (zipState eqGate_bound s).val.output=(zipVec eqGate s.val.graph s.val.lhs s.val.rhs).2 from
    congrArg Prod.snd (zipState_value eqGate_bound s)] at hf
  exact hf
lemma eqState_budget (s : AddState) : (eqState s).val.budget=s.val.budget+6*s.val.lhs.length := by
  rw [eqState,foldState_budget]
  change (zipState eqGate_bound s).val.budget+(1+1)*(zipState eqGate_bound s).val.output.length=_
  rw [zipState_budget,zipState_length];omega
namespace Emission
noncomputable def eqGateP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>eqGate x.1 x.2.1 x.2.2):=
  (xorP.comp ((first graphCode keyCode).pair
    ((((first refCode refCode).comp (second graphCode keyCode))).pair
      (notRefP.comp ((second refCode refCode).comp (second graphCode keyCode)))))).congrFun (by intro x;rfl)
noncomputable def eqNextP : Procedure addStateCode addStateCode eqNext := by
  let zp:=zipStateP eqGate_bound eqGateP
  let b:=(((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)).comp zp
  let g:=(addGraphP.precompose (fun s:AddState=>s.val)).comp zp
  let out:=(addOutputP.precompose (fun s:AddState=>s.val)).comp zp
  exact (packAddP.comp (b.pair (g.pair (out.pair (out.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,true)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def eqStateP : Procedure addStateCode addStateCode eqState:=
  (foldStateP andGate_bound gateP).comp eqNextP
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGDivWrapper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def divEqInput (s : BinaryState) : AddState:=
  ⟨⟨s.val.val.budget,s.val.val.graph,s.val.val.rhs,List.replicate s.val.val.lhs.length (0,false),
    0,(0,false),[]⟩,s.val.property.1,s.val.property.2.2.1,
    RefsBound.zeros s.val.property.2.1.1,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
def divEqState (s : BinaryState) : AddState:=eqState (divEqInput s)
lemma divEq_budget (s : BinaryState) : (divEqState s).val.budget=s.val.val.budget+6*s.val.val.lhs.length:=by
  rw [divEqState,eqState_budget]
  change s.val.val.budget+6*s.val.val.rhs.length=_
  rw [s.property]
lemma divEq_value (s : BinaryState) : ((divEqState s).val.graph,(divEqState s).val.cin)=
    eqVec s.val.val.graph s.val.val.rhs (List.replicate s.val.val.lhs.length (0,false)):=eqState_value _
def initializeDiv (s : BinaryState) : DivState:=
  ⟨⟨⟨(divEqState s).val.budget,(divEqState s).val.graph,s.val.val.lhs,s.val.val.rhs,
    s.val.val.lhs.length,(divEqState s).val.cin,List.replicate s.val.val.lhs.length (0,false)⟩,
    List.replicate s.val.val.lhs.length (0,false)⟩,
  ⟨(divEqState s).property.1,s.val.property.2.1.mono (by rw [divEq_budget];omega),
    s.val.property.2.2.1.mono (by rw [divEq_budget];omega),by
      change s.val.val.lhs.length ≤ (divEqState s).val.budget
      have h:=s.val.property.2.1.1;rw [divEq_budget];omega,
    (divEqState s).property.2.2.2.2.1,RefsBound.zeros (by
      have h:=s.val.property.2.1.1;rw [divEq_budget];omega)⟩,
  s.property,by simp,RefsBound.zeros (by have h:=s.val.property.2.1.1;rw [divEq_budget];omega),by simp⟩
def divLoopState (s : BinaryState) : DivState:=(divStepState^[s.val.val.lhs.length]) (initializeDiv s)
lemma divStepState_iterate_cin (s : DivState) (k : ℕ) :
    ((divStepState^[k]) s).val.base.cin=s.val.base.cin:=by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl
lemma divLoop_lhs (s : BinaryState) : (divLoopState s).val.base.lhs=s.val.val.lhs:=
  divStepState_iterate_lhs _ _
lemma divLoop_cin (s : BinaryState) : (divLoopState s).val.base.cin=(divEqState s).val.cin:=
  divStepState_iterate_cin _ _
lemma divLoop_value (s : BinaryState) :
    ((divLoopState s).val.base.graph,(divLoopState s).val.quotient,(divLoopState s).val.base.output)=
    divLoop s.val.val.lhs.length (divEqState s).val.graph s.val.val.lhs s.val.val.rhs s.val.val.lhs.length
      (List.replicate s.val.val.lhs.length (0,false)) (List.replicate s.val.val.lhs.length (0,false)):=
  divStepState_iterate_loop _ _
def divideOutInput (s : BinaryState) : AddState:=
  ⟨⟨(divLoopState s).val.base.budget,(divLoopState s).val.base.graph,
    List.replicate s.val.val.lhs.length (0,false),(divLoopState s).val.quotient,0,
    (divLoopState s).val.base.cin,[]⟩,
  (divLoopState s).property.1.1,RefsBound.zeros (by
    have h:=(divLoopState s).property.1.2.1.1;rw [divLoop_lhs] at h;exact h),
  (divLoopState s).property.2.2.2.1,Nat.zero_le _,(divLoopState s).property.1.2.2.2.2.1,
  Nat.zero_le _,by intro a ha;cases ha⟩
def divideState (s : BinaryState) : AddState:=ifVecState (divideOutInput s)
lemma divideState_value (s : BinaryState) : ((divideState s).val.graph,(divideState s).val.output)=
    divide s.val.val.graph s.val.val.lhs s.val.val.rhs := by
  have hh:=ifVecState_value (divideOutInput s)
  change _=ifVec (divLoopState s).val.base.graph (divLoopState s).val.base.cin
    (List.replicate s.val.val.lhs.length (0,false)) (divLoopState s).val.quotient at hh
  rw [divLoop_cin] at hh
  have he:=divEq_value s
  have hl:=divLoop_value s
  rw [show (divEqState s).val.graph=_ from congrArg Prod.fst he] at hl
  rw [show (divEqState s).val.cin=_ from congrArg Prod.snd he,
    show (divLoopState s).val.base.graph=_ from congrArg Prod.fst hl,
    show (divLoopState s).val.quotient=_ from congrArg (fun x=>x.2.1) hl] at hh
  exact hh

namespace Emission
noncomputable def divEqInputP : Procedure binaryStateCode addStateCode divEqInput := by
  let b:=stateBudgetP.precompose (fun s:BinaryState=>s.val)
  exact (packAddP.comp (b.pair (binaryGraphP.pair (binaryRhsP.pair ((zerosP.comp binaryLhsP).pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def divEqStateP : Procedure binaryStateCode addStateCode divEqState:=eqStateP.comp divEqInputP
noncomputable def initializeDivP : Procedure binaryStateCode divStateCode initializeDiv := by
  let b:=stateBudgetP.comp divEqStateP
  let g:=stateGraphP.comp divEqStateP
  let c:=(addCinP.precompose (fun s:AddState=>s.val)).comp divEqStateP
  let len:=(listLength refCode (0,false)).comp binaryLhsP
  let zs:=zerosP.comp binaryLhsP
  let s:=packAddP.comp (b.pair (g.pair (binaryLhsP.pair (binaryRhsP.pair (len.pair (c.pair zs))))))
  exact (s.pair zs).result (by intro s;rfl)
noncomputable def divLoopStateP : Procedure binaryStateCode divStateCode divLoopState:=
  divIterationP.comp (((listUnaryLength refCode (0,false)).comp binaryLhsP).pair initializeDivP)
noncomputable def divideOutInputP : Procedure binaryStateCode addStateCode divideOutInput := by
  let b:=divBudgetP.comp divLoopStateP
  let g:=divGraphP.comp divLoopStateP
  let c:=divCinP.comp divLoopStateP
  let q:=divQuotientP.comp divLoopStateP
  let zs:=zerosP.comp binaryLhsP
  exact (packAddP.comp (b.pair (g.pair (zs.pair (q.pair ((Procedure.constant _ Nat.bits 0).pair
    (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def divideStateP : Procedure binaryStateCode addStateCode divideState:=ifVecStateP.comp divideOutInputP
noncomputable def divideP : Procedure binaryStateCode (prodCode graphCode (listCode refCode))
    (fun s=>divide s.val.val.graph s.val.val.lhs s.val.val.rhs):=
  ((stateGraphP.pair stateOutputP).comp divideStateP).congrFun divideState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat
def rawInputs (n : ℕ) : Graph := ⟨.zero::(List.range n).map Decl.atom,[]⟩

namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def inputsP : Procedure unaryCode graphCode rawInputs := by
  let p : Procedure (prodCode unaryCode emptyCode) declCode (fun x=>Decl.atom x.1):=
    atomDecl.comp (unaryToBits.comp (first unaryCode emptyCode))
  let ds:=(tabulate (f:=fun (_ : Unit) i=>Decl.atom i) Decl.zero p).comp ((identity unaryCode).pair (Procedure.constant _ emptyCode ()))
  exact (packGraph.comp (((listCons declCode).comp
    ((Procedure.constant _ declCode Decl.zero).pair ds)).pair
      (Procedure.constant _ (listCode entryCode) []))).congrFun (by intro n;rfl)
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGMod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide Std.Tactic.BVDecide.BVExpr.bitblast

def remainder (g : Graph) (lhs rhs : List Ref) : Graph×List Ref:=
  let zero:=List.replicate lhs.length (0,false)
  let d:=eqVec g rhs zero
  let out:=divLoop lhs.length d.1 lhs rhs lhs.length zero zero
  ifVec out.1 d.2 lhs out.2.2

end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGModWrapper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def remainderOutInput (s : BinaryState) : AddState:=
  ⟨⟨(divLoopState s).val.base.budget,(divLoopState s).val.base.graph,
    s.val.val.lhs,(divLoopState s).val.base.output,0,(divLoopState s).val.base.cin,[]⟩,
  (divLoopState s).property.1.1,by
    have h:=(divLoopState s).property.1.2.1;rw [divLoop_lhs] at h;exact h,
  (divLoopState s).property.1.2.2.2.2.2,Nat.zero_le _,(divLoopState s).property.1.2.2.2.2.1,
  Nat.zero_le _,by intro a ha;cases ha⟩
def remainderState (s : BinaryState) : AddState:=ifVecState (remainderOutInput s)
lemma remainderState_value (s : BinaryState) : ((remainderState s).val.graph,(remainderState s).val.output)=
    remainder s.val.val.graph s.val.val.lhs s.val.val.rhs := by
  have hh:=ifVecState_value (remainderOutInput s)
  change _=ifVec (divLoopState s).val.base.graph (divLoopState s).val.base.cin
    s.val.val.lhs (divLoopState s).val.base.output at hh
  rw [divLoop_cin] at hh
  have he:=divEq_value s
  have hl:=divLoop_value s
  rw [show (divEqState s).val.graph=_ from congrArg Prod.fst he] at hl
  rw [show (divEqState s).val.cin=_ from congrArg Prod.snd he,
    show (divLoopState s).val.base.graph=_ from congrArg Prod.fst hl,
    show (divLoopState s).val.base.output=_ from congrArg (fun x=>x.2.2) hl] at hh
  exact hh
namespace Emission
noncomputable def remainderOutInputP : Procedure binaryStateCode addStateCode remainderOutInput := by
  let b:=divBudgetP.comp divLoopStateP
  let g:=divGraphP.comp divLoopStateP
  let c:=divCinP.comp divLoopStateP
  let rem:=divRemP.comp divLoopStateP
  exact (packAddP.comp (b.pair (g.pair (binaryLhsP.pair (rem.pair ((Procedure.constant _ Nat.bits 0).pair
    (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def remainderStateP : Procedure binaryStateCode addStateCode remainderState:=ifVecStateP.comp remainderOutInputP
noncomputable def remainderP : Procedure binaryStateCode (prodCode graphCode (listCode refCode))
    (fun s=>remainder s.val.val.graph s.val.val.lhs s.val.val.rhs):=
  ((stateGraphP.pair stateOutputP).comp remainderStateP).congrFun remainderState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGBinaryInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure Std.Sat
lemma rawInputs_bound (n : ℕ) : Bounded (n+1) (rawInputs n):=by
  refine ⟨by simp [rawInputs],by simp [rawInputs],?_,by simp [rawInputs]⟩
  intro d hd
  simp only [rawInputs,List.mem_cons,List.mem_map] at hd
  rcases hd with rfl | ⟨i,hi,rfl⟩
  · trivial
  · have hi:=List.mem_range.mp hi
    change i≤n+1
    omega

def rawWord (offset w : ℕ) : List Ref:=(List.range w).map (fun i=>(offset+i+1,false))
lemma rawWord_bound (o w : ℕ) : RefsBound (o+w+1) (rawWord o w):=by
  refine ⟨by simp [rawWord];omega,?_⟩
  intro a ha
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
  have hi:=List.mem_range.mp hi
  dsimp only
  omega
def binaryInput (w : ℕ) : BinaryState:=⟨⟨⟨w+w+1,rawInputs (w+w),rawWord 0 w,rawWord w w,0,(0,false),[]⟩,
  rawInputs_bound _,(rawWord_bound 0 w).mono (by change 0+w+1≤w+w+1;omega),rawWord_bound w w,
  Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩,by simp [rawWord]⟩
namespace Emission
noncomputable def rawWordP : Procedure (prodCode unaryCode unaryCode) (listCode refCode)
    (fun x=>rawWord x.1 x.2):=by
  let p:=(successor.comp (binaryAdd.comp
    ((unaryToBits.comp (second unaryCode unaryCode)).pair (unaryToBits.comp (first unaryCode unaryCode))))).pair
      (Procedure.constant _ boolCode false)
  exact ((tabulate (f:=fun o i=>(o+i+1,false)) (0,false) p).comp
    ((second unaryCode unaryCode).pair (first unaryCode unaryCode))).congrFun (by intro x;rfl)
noncomputable def binaryInputP : Procedure unaryCode binaryStateCode binaryInput:=by
  let w:=identity unaryCode
  let two:=unaryAdd.comp (w.pair w)
  let b:=unarySuccessor.comp two
  let g:=inputsP.comp two
  let l:=rawWordP.comp ((Procedure.constant _ unaryCode 0).pair w)
  let r:=rawWordP.comp (w.pair w)
  exact (packAddP.comp (b.pair (g.pair (l.pair (r.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro n;rfl)
noncomputable def inputAddP : Procedure unaryCode (prodCode graphCode (listCode refCode))
    (fun w=>add (rawInputs (w+w)) (rawWord 0 w) (rawWord w w)):=by
  refine (addP.comp (((identity addStateCode).precompose (fun s:BinaryState=>s.val)).comp binaryInputP)).congrFun ?_
  intro w
  change add (binaryInput w).val.val.graph (binaryInput w).val.val.lhs (binaryInput w).val.val.rhs = _
  congr 1
noncomputable def inputMulP : Procedure unaryCode (prodCode graphCode (listCode refCode))
    (fun w=>mul (rawInputs (w+w)) (rawWord 0 w) (rawWord w w)):=by
  refine (mulP.comp binaryInputP).congrFun ?_
  intro w
  change mul (binaryInput w).val.val.graph (binaryInput w).val.val.lhs (binaryInput w).val.val.rhs = _
  congr 1
noncomputable def inputSubP : Procedure unaryCode (prodCode graphCode (listCode refCode))
    (fun w=>sub (rawInputs (w+w)) (rawWord 0 w) (rawWord w w)):=by
  refine (subP.comp binaryInputP).congrFun ?_
  intro w
  change sub (binaryInput w).val.val.graph (binaryInput w).val.val.lhs (binaryInput w).val.val.rhs = _
  congr 1
noncomputable def inputDivP : Procedure unaryCode (prodCode graphCode (listCode refCode))
    (fun w=>divide (rawInputs (w+w)) (rawWord 0 w) (rawWord w w)):=by
  refine (divideP.comp binaryInputP).congrFun ?_
  intro w
  change divide (binaryInput w).val.val.graph (binaryInput w).val.val.lhs (binaryInput w).val.val.rhs = _
  congr 1
noncomputable def inputModP : Procedure unaryCode (prodCode graphCode (listCode refCode))
    (fun w=>remainder (rawInputs (w+w)) (rawWord 0 w) (rawWord w w)):=by
  refine (remainderP.comp binaryInputP).congrFun ?_
  intro w
  change remainder (binaryInput w).val.val.graph (binaryInput w).val.val.lhs (binaryInput w).val.val.rhs = _
  congr 1
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGBitArithmeticEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.AIGNetworkEmission
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
open BitStackProgram BitStackProgram.Procedure NetworkEmission

def binaryPack (op : NativeAIG.Graph→List NativeAIG.Ref→List NativeAIG.Ref→NativeAIG.Graph×List NativeAIG.Ref)
    (w : ℕ) : Pack:=
  let r:=op (NativeAIG.rawInputs (w+w)) (NativeAIG.rawWord 0 w) (NativeAIG.rawWord w w)
  compilePack (w+w) r.1.decls r.2

def ultPack (w : ℕ) : Pack:=
  let r:=NativeAIG.ult (NativeAIG.rawInputs (w+w)) (NativeAIG.rawWord 0 w) (NativeAIG.rawWord w w)
  compilePack (w+w) r.1.decls [r.2]

namespace Emission
noncomputable def binaryPackP
    {op : NativeAIG.Graph→List NativeAIG.Ref→List NativeAIG.Ref→NativeAIG.Graph×List NativeAIG.Ref}
    (p : Procedure unaryCode (prodCode NativeAIG.graphCode (listCode NativeAIG.refCode))
      (fun w=>op (NativeAIG.rawInputs (w+w)) (NativeAIG.rawWord 0 w) (NativeAIG.rawWord w w))) :
    Procedure unaryCode packCode (binaryPack op):=by
  let width:=unaryAdd.comp ((identity unaryCode).pair (identity unaryCode))
  let graph:=(first NativeAIG.graphCode (listCode NativeAIG.refCode)).comp p
  let ds:=NativeAIG.Emission.decls.comp graph
  let refs:=(second NativeAIG.graphCode (listCode NativeAIG.refCode)).comp p
  exact compilePackP.comp ((width.pair ds).pair refs)
noncomputable def addPackP : Procedure unaryCode packCode (binaryPack NativeAIG.add):=binaryPackP NativeAIG.Emission.inputAddP
noncomputable def mulPackP : Procedure unaryCode packCode (binaryPack NativeAIG.mul):=binaryPackP NativeAIG.Emission.inputMulP
noncomputable def subPackP : Procedure unaryCode packCode (binaryPack NativeAIG.sub):=binaryPackP NativeAIG.Emission.inputSubP
noncomputable def divPackP : Procedure unaryCode packCode (binaryPack NativeAIG.divide):=binaryPackP NativeAIG.Emission.inputDivP
noncomputable def modPackP : Procedure unaryCode packCode (binaryPack NativeAIG.remainder):=binaryPackP NativeAIG.Emission.inputModP
noncomputable def inputUltP : Procedure unaryCode (prodCode NativeAIG.graphCode NativeAIG.refCode)
    (fun w=>NativeAIG.ult (NativeAIG.rawInputs (w+w)) (NativeAIG.rawWord 0 w) (NativeAIG.rawWord w w)):=by
  refine (NativeAIG.Emission.ultP.comp (((identity NativeAIG.addStateCode).precompose
    (fun s:NativeAIG.BinaryState=>s.val)).comp NativeAIG.Emission.binaryInputP)).congrFun ?_
  intro w
  change NativeAIG.ult (NativeAIG.binaryInput w).val.val.graph (NativeAIG.binaryInput w).val.val.lhs
    (NativeAIG.binaryInput w).val.val.rhs=_
  congr 1
end Emission
end ExactQuantumFactoring.AIGNetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork
open scoped BigOperators

def any {n : ℕ} : List (BooleanNetwork n 1) → BooleanNetwork n 1
  | [] => constant false
  | c::cs => c.bor (any cs)

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordBlocks
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
attribute [-simp] _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open scoped BigOperators

/-- Consecutive fixed-width words; construction duplicates a word network at
most w times and so has a direct polynomial-size bound. -/
def wordBlocks {n s w : ℕ} (f : Fin s → BooleanNetwork n w) : BooleanNetwork n (s*w) :=
  vector (fun k => (f (finProdFinEquiv.symm k).1).rewire
    (fun _ => (finProdFinEquiv.symm k).2))

def blockNet (s w : ℕ) (i : Fin s) : BooleanNetwork (s*w) w :=
  select (fun j => finProdFinEquiv (i,j))

@[simp] lemma blockNet_eval {s w : ℕ} (i : Fin s) (x : Basis (s*w)) :
    (blockNet s w i).eval x = block x i := rfl
@[simp] lemma blockNet_count {s w : ℕ} (i : Fin s) : (blockNet s w i).net.count=0 := rfl

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BoundedStack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

/-- Push a word; the last slot is dropped. Capacity is verified separately in
controller invariants, rather than silently growing the physical width. -/
def stackPush {k s w : ℕ} (a : BooleanNetwork k w) (v : BooleanNetwork k (s*w)) :
    BooleanNetwork k (s*w) :=
  wordBlocks (fun i : Fin s => if h : i.val=0 then a
    else v.comp (blockNet s w ⟨i.val-1,by omega⟩))

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ModularMultiply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

/-- A word mux shares previously computed word outputs via fanout; it does not
recompute the operand circuit separately at every bit. -/
def wordMux {n w : ℕ} (c : BooleanNetwork n 1) (a b : BooleanNetwork n w) :
    BooleanNetwork n w :=
  ((c.pair a).pair b).comp (vector (fun i =>
    mux (bit ⟨0,by omega⟩) (bit ⟨1+i.val,by omega⟩)
      (bit ⟨1+w+i.val,by omega⟩)))

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ModularPower
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open scoped BigOperators

def powerBase (w b : ℕ) : BooleanNetwork (powerWidth w b) w :=
  select (fun i => ((i.castAdd w).castAdd b).castAdd w)
def powerModulus (w b : ℕ) : BooleanNetwork (powerWidth w b) w :=
  select (fun i => ((Fin.natAdd w i).castAdd b).castAdd w)
def powerAcc (w b : ℕ) : BooleanNetwork (powerWidth w b) w :=
  select (Fin.natAdd ((w+w)+b))
def powerBit (w : ℕ) {b : ℕ} (i : Fin b) : BooleanNetwork (powerWidth w b) 1 :=
  bit ((Fin.natAdd (w+w) i).castAdd w)

@[simp] lemma powerBase_eval {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) :
    (powerBase w b).eval (powerPack a m e z) = a := by
  funext i
  simp only [powerBase, eval_select, Function.comp_apply, powerPack, Fin.append_left]
@[simp] lemma powerModulus_eval {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) :
    (powerModulus w b).eval (powerPack a m e z) = m := by
  funext i
  simp only [powerModulus, eval_select, Function.comp_apply, powerPack, Fin.append_left,
    Fin.append_right]
@[simp] lemma powerAcc_eval {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) :
    (powerAcc w b).eval (powerPack a m e z) = z := by
  funext i
  simp only [powerAcc, eval_select, Function.comp_apply, powerPack, Fin.append_right]
@[simp] lemma powerBit_eval {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) (i : Fin b) :
    (powerBit w i).eval (powerPack a m e z) 0 = e i := by
  simp only [powerBit, eval_bit, powerPack, Fin.append_left, Fin.append_right]

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ChildQueue
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
namespace ChildQueue

def predBits {w : ℕ} (a : Basis w) : Basis w :=
  (sub w).eval (Fin.append a (fun i => (BitVec.ofNat w 1).getLsbD i.val))

/-- Children from the distinct prime fields, ignoring zero padding and 2.
Repeated labels in DIFFERENT node records are not identified. -/
def kids {w : ℕ} : List (Basis w) → List (Basis w)
  | [] => []
  | a::as => if 2<(bitsValue a).toNat ∧ a∉as then predBits a::kids as else kids as

def wordMember {k w : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w)) :
    BooleanNetwork k 1 := any (as.map (fun b => (a.pair b).comp (wordEq w)))


def source (k s w : ℕ) : BooleanNetwork (k+s*w) k := select (Fin.castAdd (s*w))
def queue (k s w : ℕ) : BooleanNetwork (k+s*w) (s*w) := select (Fin.natAdd k)
def liftWord {k w : ℕ} (s : ℕ) (a : BooleanNetwork k w) := (source k s w).comp a

def active {k w : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w)) : BooleanNetwork k 1 :=
  (wordLt (wordConstant (BitVec.ofNat w 2)) a).band (wordMember a as).bnot

def pushOne {k w : ℕ} (s : ℕ) (a : BooleanNetwork k w) (as : List (BooleanNetwork k w)) :
    BooleanNetwork (k+s*w) (k+s*w) :=
  (source k s w).pair
    (wordMux ((source k s w).comp (active a as))
      (stackPush (((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w)) (queue k s w))
      (queue k s w))

/-- Tail before head: the recursive network occurs just ONCE in the syntax.
All original factor fields remain read-only while the bounded queue is updated. -/
def pushAll {k w : ℕ} (s : ℕ) : List (BooleanNetwork k w) → BooleanNetwork (k+s*w) (k+s*w)
  | [] => select id
  | a::as => (pushAll s as).comp (pushOne s a as)

end ChildQueue
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitEmissionModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission

def primitiveCode (p : Primitive) : List Bool:=BitStackProgram.unaryCode p.code
end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerAcc_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBase_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerBit_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.powerModulus_eval _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality
open scoped BigOperators

noncomputable def decodeCyclic {s w : ℕ} (m : ℕ) (x : Basis (s*w)) : Cyclic (ZMod m) s :=
  cyclicOf (fun i => ((bitsValue (block x i)).toNat : ZMod m))

@[simp] lemma decodeCyclic_coeff {s w : ℕ} (m : ℕ) (x : Basis (s*w)) (i : Fin s) :
    (decodeCyclic m x).coeff i=((bitsValue (block x i)).toNat : ZMod m) := rfl

/-- Canonical representatives permit exact word comparison of arrays. -/
def CanonicalCyclic {s w : ℕ} (m : ℕ) (x : Basis (s*w)) : Prop :=
  ∀ i : Fin s, (bitsValue (block x i)).toNat < m

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicPowerCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality

def cyclicBase (s w b : ℕ) : BooleanNetwork (cyclicPowerWidth s w b) (s*w) :=
  select (fun i => ((i.castAdd w).castAdd b).castAdd (s*w))
def cyclicAcc (s w b : ℕ) : BooleanNetwork (cyclicPowerWidth s w b) (s*w) :=
  select (Fin.natAdd ((s*w+w)+b))

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeControlCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork FactorController

namespace NodeCircuit

def pending (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) := select (Fin.castAdd w)
def divisor (s w : ℕ) : BooleanNetwork (width s w) w := select (Fin.natAdd ((s+1)*w))
def top (s w : ℕ) : BooleanNetwork (width s w) w :=
  (pending s w).comp (blockNet (s+1) w 0)

end NodeCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end


