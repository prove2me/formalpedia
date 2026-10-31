-- Prove2me | Definitions.Def_OAIQ028V007
-- name    : OAIQ028V007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T00:14:58.13323+00:00
-- url     : https://prove2.me/theorems/a74c7d59-3d9c-4f44-b98f-d1a34e070204
-- title:
--   Definitions bundle OAIQ028V007 of the split of OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.VertexCover.explicit_cover_gap` and `OAI.VertexCover.every_fixed_factor_below_two`, carved from OpenAI's openai/math development (OpenAI, *The Factor-Two Hardness Threshold for Vertex Cover (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 367 declarations of OpenAI's Lean: 297 definitions, 1 instance and 69 theorems. The definitions and types are `OAI.UniqueGames.Foundations.Repetition.selectedLabelAccepts`, `OAI.VertexCover.ClauseProjection.fixedBaseTable`, `OAI.VertexCover.ClauseProjection.repetitionBase`, `OAI.VertexCover.LabelCover.repeatedStrategy`, `OAI.VertexCover.Machine.AddressMachine.search`, `OAI.VertexCover.Machine.AlphabetMachine.blockCount`, `OAI.VertexCover.Machine.AlphabetMachine.blockEquiv`, `OAI.VertexCover.Machine.BinaryOutput.bodyPoly`, `OAI.VertexCover.Machine.BinaryOutput.poly`, `OAI.VertexCover.Machine.CloudMachine.cloudFamily`, `OAI.VertexCover.Machine.CloudMachine.cloudFamilyPoly`, `OAI.VertexCover.Machine.CloudMachine.cloudLookup`, `OAI.VertexCover.Machine.CloudMachine.cloudLookupPoly`, `OAI.VertexCover.Machine.CloudMachine.cloudPoly`, `OAI.VertexCover.Machine.CloudMachine.dummies`, `OAI.VertexCover.Machine.CloudMachine.dummiesPoly`, `OAI.VertexCover.Machine.CloudMachine.dummyErase`, `OAI.VertexCover.Machine.CloudMachine.globalIndex`, `OAI.VertexCover.Machine.CloudMachine.globalIndexPoly`, `OAI.VertexCover.Machine.CloudMachine.localDummies`, `OAI.VertexCover.Machine.CloudMachine.localDummiesPoly`, `OAI.VertexCover.Machine.CloudMachine.ownerRank`, `OAI.VertexCover.Machine.CloudMachine.ownerRankPoly`, `OAI.VertexCover.Machine.CloudMachine.padding`, `OAI.VertexCover.Machine.CloudMachine.paddingPoly`, `OAI.VertexCover.Machine.CloudMachine.regularVerticesPoly`, `OAI.VertexCover.Machine.Dedup.poly`, `OAI.VertexCover.Machine.Divide.poly`, `OAI.VertexCover.Machine.ExpandMachine.capped`, `OAI.VertexCover.Machine.ExpandMachine.cappedIteratePoly`, `OAI.VertexCover.Machine.ExpandMachine.cappedPoly`, `OAI.VertexCover.Machine.ExpandMachine.cloudPaddedPoly`, `OAI.VertexCover.Machine.ExpandMachine.code`, `OAI.VertexCover.Machine.ExpandMachine.family`, `OAI.VertexCover.Machine.ExpandMachine.lookupPoly`, `OAI.VertexCover.Machine.ExpandMachine.paddedFamily`, `OAI.VertexCover.Machine.ExpandMachine.paddedFamilyPoly`, `OAI.VertexCover.Machine.ExpandMachine.paddedSizePoly`, `OAI.VertexCover.Machine.ExpandMachine.step`, `OAI.VertexCover.Machine.ExpandMachine.stepDataPoly` and 257 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `VertexCover_Analysis_BaseReductionCoherent`, `VertexCover_Analysis_PowerValueRepetition`, `VertexCover_Machines_Address`, `VertexCover_Machines_AlphabetFrame`, `VertexCover_Machines_Approximation`, `VertexCover_Machines_BinaryOutput`, `VertexCover_Machines_Cloud`, `VertexCover_Machines_CloudFamily`, `VertexCover_Machines_CloudIndex`, `VertexCover_Machines_DenseParse`, `VertexCover_Machines_ExpanderBound`, `VertexCover_Machines_ExpanderCorrect`, `VertexCover_Machines_ExpanderFamily`, `VertexCover_Machines_ExpanderStep`, `VertexCover_Machines_FinCode`, `VertexCover_Machines_FinalCNF`, `VertexCover_Machines_FinalCNFBase`, `VertexCover_Machines_FiniteFunction`, `VertexCover_Machines_FixedOps`, `VertexCover_Machines_Generic`, `VertexCover_Machines_GraphConstraint`, `VertexCover_Machines_GraphDescriptor`, `VertexCover_Machines_GraphFrame`, `VertexCover_Machines_GraphNumber`, `VertexCover_Machines_GraphOutput`, `VertexCover_Machines_InitialTable`, `VertexCover_Machines_LCData`, `VertexCover_Machines_Lazy`, `VertexCover_Machines_ListFilter`, `VertexCover_Machines_ListGrowing`, `VertexCover_Machines_ListIndex`, `VertexCover_Machines_ListMore`, `VertexCover_Machines_ListNat`, `VertexCover_Machines_ListParam`, `VertexCover_Machines_ListSearch`, `VertexCover_Machines_LoopFrom`, `VertexCover_Machines_NatDiv`, `VertexCover_Machines_NatLog`, `VertexCover_Machines_NatPath`, `VertexCover_Machines_NatWalk`, `VertexCover_Machines_Option`, `VertexCover_Machines_Overlay`, `VertexCover_Machines_Padding`, `VertexCover_Machines_ParseClause`, `VertexCover_Machines_ParseFormula`, `VertexCover_Machines_PortBuilder`, `VertexCover_Machines_PortCode`, `VertexCover_Machines_PowerLC`, `VertexCover_Machines_Regular`, `VertexCover_Machines_RegularRow`, `VertexCover_Machines_Serialization`, `VertexCover_Machines_SimpleLC`, `VertexCover_Machines_TableBase`, `VertexCover_Machines_TableCodeBound`, `VertexCover_Machines_Walk`, `VertexCover_Reduction_ReductionSound`, `VertexCover_Repetition_SelectedLikelihood`.
--
--   **Imports.** It imports the published bundle `Def_VertexCover`; the bundles `OAIQ028V003`, `OAIQ028V004` and `OAIQ028V005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ028V008`.
-- source:
--   OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_VertexCover
import Definitions.Def_OAIQ028V003
import Definitions.Def_OAIQ028V004
import Definitions.Def_OAIQ028V005

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedLikelihood
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                  
section

namespace UniqueGames.Foundations.Repetition
open Games
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedLabelAccepts (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : Bool := by
  classical
  exact decide (∀ i : selected, G.accepts (fixed i).1 (fixed i).2 (label.1 i) (label.2 i) = true)

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_BaseReductionCoherent
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

namespace VertexCover.ClauseProjection
open UniqueGames.Foundations
open Target

noncomputable def fixedBaseTable : PCP.RoundTables.BaseTable :=
  PCP.ExpanderTables.exists_base_table.choose

theorem fixedBaseTable_certificate :
    PCP.SpectralReturn.SpectralCertificate (PCP.ExpanderTables.graph fixedBaseTable) (1/100 : ℝ) :=
  PCP.ExpanderTables.exists_base_table.choose_spec

end VertexCover.ClauseProjection


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_PowerValueRepetition
attribute [-instance] _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfilePair _root_.OAI.VertexCover.LabelCover.Query.instDecidableProfileValid _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
open UniqueGames.Foundations.Games
noncomputable section

def repeatedStrategy (Φ : LabelCover) (n : ℕ) (A : (Φ.parallelPower n).Labeling) :
    Strategy (Fin n → Fin Φ.u) (Fin n → Fin Φ.v) (Fin n → Fin Φ.qU) (Fin n → Fin Φ.qV) :=
  (fun x => (tupleEquiv Φ.qU n).symm (A.1 (tupleEquiv Φ.u n x)),
   fun y => (tupleEquiv Φ.qV n).symm (A.2 (tupleEquiv Φ.v n y)))

theorem power_satisfies_iff (Φ : LabelCover) (n : ℕ) (A : (Φ.parallelPower n).Labeling)
    (es : Fin n → Fin Φ.M) :
    (Φ.parallelPower n).Satisfies A (tupleEquiv Φ.M n es) ↔
      ∀ i, Φ.projection (es i)
        ((Φ.repeatedStrategy n A).1 (fun j => Φ.left (es j)) i) =
        (Φ.repeatedStrategy n A).2 (fun j => Φ.right (es j)) i := by
  simp only [Satisfies, parallelPower, repeatedStrategy, Equiv.symm_apply_apply]
  rw [← Equiv.eq_symm_apply]
  exact funext_iff

end
end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_NatDiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                       
section

namespace VertexCover.Machine
namespace Divide

theorem run (d r q B : ℕ) (hsize : (enc (d,(r,q))).length ≤ B) :
    ∃ n, n ≤ r+1 ∧ BoundedRun enc body B (d,(r,q)) (result (d,(r,q))) n := by
  induction r using Nat.strong_induction_on generalizing q with
  | h r ih =>
    by_cases h : 0<d ∧ d ≤ r
    · have hlt : r-d < r := Nat.sub_lt (h.1.trans_le h.2) h.1
      have hs : (enc (d,(r-d,q+1))).length ≤ B := by
        simp only [enc,prodBits,pairBits_length,natBits_length] at hsize ⊢
        omega
      obtain ⟨n,hn,hr⟩ := ih (r-d) hlt (q+1) hs
      refine ⟨n+1,by omega,?_⟩
      have he : result (d,(r-d,q+1)) = result (d,(r,q)) := by
        simp only [result]
        rw [Nat.mod_eq_sub_mod h.2,Nat.div_eq_sub_div h.1 h.2]
        congr 2; omega
      rw [he] at hr
      refine .next _ _ n hsize ?_ ?_
      · simp [body,h]
      · simpa [body,h] using hr
    · have he : result (d,(r,q)) = (d,(r,q)) := by
        by_cases hd : d=0
        · simp [result,hd]
        · have hlt : r<d := by omega
          simp [result,Nat.mod_eq_of_lt hlt,Nat.div_eq_of_lt hlt]
      rw [he]
      refine ⟨1,by omega,?_⟩
      simpa only [body,h,ite_false] using
        (BoundedRun.stop (e := enc) (body := body) (d,(r,q)) hsize
          (by simp [body,h]))

noncomputable def poly : Poly enc enc result :=
  bodyPoly.loop result Polynomial.X (Polynomial.X+1) (by
    intro ⟨d,r,q⟩
    obtain ⟨n,hn,hr⟩ := run d r q (enc (d,(r,q))).length le_rfl
    refine ⟨n,?_,by simpa only [Polynomial.eval_X] using hr⟩
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,enc,prodBits,
      pairBits_length,natBits_length]
    omega)
end Divide

noncomputable def Poly.natDivMod : Poly (prodBits natBits natBits) (prodBits natBits natBits)
    (fun p : ℕ × ℕ => (p.1%p.2,p.1/p.2)) := by
  let input := (Poly.snd natBits natBits).pair
    ((Poly.fst natBits natBits).pair (Poly.const (prodBits natBits natBits) natBits 0))
  exact ((input.comp Divide.poly).comp (Poly.snd natBits (prodBits natBits natBits))).congr
    (fun p => by simp only [Function.comp_apply,Divide.result,Nat.zero_add])

noncomputable def Poly.natDiv : Poly (prodBits natBits natBits) natBits
    (fun p : ℕ × ℕ => p.1/p.2) := Poly.natDivMod.comp (Poly.snd natBits natBits)

noncomputable def Poly.natMod : Poly (prodBits natBits natBits) natBits
    (fun p : ℕ × ℕ => p.1%p.2) := Poly.natDivMod.comp (Poly.fst natBits natBits)

noncomputable def Poly.natPow (k : ℕ) : Poly natBits natBits (fun n => n^k) := by
  induction k with
  | zero => exact (Poly.const natBits natBits 1).congr (fun _ => rfl)
  | succ k ih =>
    exact ((ih.pair (Poly.identity natBits)).comp Poly.natMul).congr
      (fun n => (Nat.pow_succ n k).symm)

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_FinCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                            
section

namespace VertexCover.Machine

theorem finCode_injective (n : ℕ) : Function.Injective (finCode (n := n)) := by
  intro a b h
  apply Fin.ext
  have := congrArg List.length h
  simpa [finCode] using this

noncomputable def Poly.finMod (n : ℕ) (hn : 0 < n) :
    Poly natBits (finCode (n := n)) (fun i => (⟨i%n,Nat.mod_lt i hn⟩ : Fin n)) :=
  (((Poly.identity natBits).pair (Poly.const natBits natBits n)).comp Poly.natMod).encodeCongr
    id (fun _ => rfl) (fun _ => rfl)

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_FixedOps
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.dartNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                             
section

namespace VertexCover.Machine

noncomputable def Poly.fixedAll {α ι : Type} (ea : α → List Bool) (f : α → ι → Bool)
    (cf : ∀ i, Poly ea boolBits (fun a => f a i)) :
    (xs : List ι) → Poly ea boolBits (fun a => xs.all (f a))
  | [] => Poly.const ea boolBits true
  | i::xs => (((cf i).pair (Poly.fixedAll ea f cf xs)).comp (Poly.bool₂ (fun x => x.1 && x.2))).congr
     (fun _ => by simp only [Function.comp_apply,List.all_cons])

noncomputable def Poly.finiteAll {α ι : Type} [Fintype ι] (ea : α → List Bool)
    (f : α → ι → Bool) (cf : ∀ i, Poly ea boolBits (fun a => f a i)) :
    Poly ea boolBits (fun a => decide (∀ i, f a i = true)) := by
  classical
  exact (Poly.fixedAll ea f cf Finset.univ.toList).congr (fun a => by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true,Finset.mem_toList,Finset.mem_univ,forall_const,decide_eq_true_iff])

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListMore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                         
section

namespace VertexCover.Machine
open UniqueGames.Foundations.Complexity

noncomputable def Poly.listAppend {α : Type} (e : α → List Bool) (a₀ : α) :
    Poly (prodBits (listBits e) (listBits e)) (listBits e)
      (fun p : List α × List α => p.1++p.2) := by
  let c := Poly.snd (listBits e) (listBits e)
  let d := (Poly.fst (listBits e) (listBits e)).comp (Poly.listReverse e a₀)
  exact ((c.pair d).comp (Poly.reverseAppend e a₀)).congr
    (fun p => by simp only [Function.comp_apply, List.reverse_reverse])

noncomputable def Poly.mapFold {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (a₀ : α)
    {f : α → β} (cf : Poly ea eb f) :
    Poly (prodBits (listBits eb) (listBits ea)) (listBits eb)
      (fun p : List β × List α => (p.2.map f).reverse++p.1) := by
  let c := (((Poly.snd (listBits eb) ea).comp cf).pair
    (Poly.fst (listBits eb) ea)).comp (Poly.listCons eb)
  let size : Polynomial ℕ := 3*Polynomial.X +
    2*(2*cf.outputPolynomial+2)*Polynomial.X + 4
  have bound (b : List β) (xs pre suf : List α) (h : pre++suf=xs) :
      (prodBits (listBits eb) (listBits ea)
        (pre.foldl (fun b a => f a::b) b,suf)).length ≤
          size.eval (prodBits (listBits eb) (listBits ea) (b,xs)).length := by
    let N := (prodBits (listBits eb) (listBits ea) (b,xs)).length
    have hs : (listBits ea xs).length ≤ N := by dsimp [N,prodBits]; rw [pairBits_length]; omega
    have hb : (listBits eb b).length ≤ N := by dsimp [N,prodBits]; rw [pairBits_length]; omega
    have hp : pre.length ≤ N := by
      have := list_length_le_bits ea xs
      have hh := congrArg List.length h
      simp only [List.length_append] at hh
      omega
    have hparts := listBits_append_length ea pre suf
    rw [h] at hparts
    have hsf : (listBits ea suf).length ≤ N := by
      have := listBits_length_pos ea pre
      omega
    have hmap : (listBits eb (pre.map f)).length ≤
        (2*cf.outputPolynomial.eval N+2)*pre.length+1 :=
      listBits_map_bound eb f pre _ (fun a ha =>
        (cf.output_length a).trans (MachineComposition.natPolynomial_eval_mono _
          ((listBits_member_length ea (show a ∈ xs by rw [← h]; simp [ha])).trans hs)))
    have hac := listBits_append_length eb (pre.map f).reverse b
    rw [listBits_reverse_length] at hac
    change _ ≤ size.eval N
    simp only [prodBits, pairBits_length, foldl_map_cons]
    have hm := Nat.mul_le_mul_left (2*cf.outputPolynomial.eval N+2) hp
    simp only [size, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    nlinarith
  exact (Poly.fold ea (listBits eb) a₀ c size bound).congr (fun p => foldl_map_cons f p.2 p.1)

noncomputable def Poly.listMap {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) (b₀ : β) {f : α → β} (cf : Poly ea eb f) :
    Poly (listBits ea) (listBits eb) (List.map f) := by
  let c := ((Poly.const (listBits ea) (listBits eb) []).pair
    (Poly.identity (listBits ea))).comp (Poly.mapFold ea eb a₀ cf)
  exact (c.comp (Poly.listReverse eb b₀)).congr (fun p => by
    simp only [Function.comp_apply, List.append_nil, List.reverse_reverse, id_eq])

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                        
section

namespace VertexCover.Machine

namespace Range

noncomputable def poly : Poly (prodBits natBits (listBits natBits))
    (prodBits natBits (listBits natBits)) step := by
  let n := Poly.fst natBits (listBits natBits)
  let xs := Poly.snd natBits (listBits natBits)
  exact ((n.comp Poly.natSucc).pair ((n.pair xs).comp (Poly.listCons natBits))).congr (fun _ => rfl)

end Range

noncomputable def Poly.range : Poly natBits (listBits natBits) List.range := by
  let e := prodBits natBits (listBits natBits)
  let size : Polynomial ℕ := 20*(Polynomial.X+1)^2
  have bound (n : ℕ) (p : ℕ × List ℕ) (k l : ℕ) (h : k+l=n) :
      (prodBits natBits e (l,Iterate.run Range.step k p)).length ≤
        size.eval (prodBits natBits e (n,p)).length := by
    rcases p with ⟨a,xs⟩
    have hk : k ≤ n := by omega
    have hl : l ≤ n := by omega
    have hd := listBits_append_length natBits (List.range' a k).reverse xs
    rw [listBits_reverse_length] at hd
    have hb := Range.bits_bound k a
    have hk₂ := Nat.mul_le_mul hk hk
    have hak := Nat.mul_le_mul_left a hk
    simp only [prodBits,e,pairBits_length,natBits_length,Range.run,size,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    nlinarith
  let c := Poly.iterate e Range.poly size bound
  let input := (Poly.identity natBits).pair
    ((Poly.const natBits natBits 0).pair (Poly.const natBits (listBits natBits) []))
  exact (((input.comp c).comp (Poly.snd natBits (listBits natBits))).comp
    (Poly.listReverse natBits 0)).congr (fun n => by
      simp only [Function.comp_apply,Range.run,Nat.zero_add,← List.range_eq_range',
        List.append_nil,List.reverse_reverse,id_eq])

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListParam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                          
section

namespace VertexCover.Machine

namespace WithParam
variable {α β : Type}

noncomputable def poly (ea : α → List Bool) (eb : β → List Bool) :
    Poly (prodBits (prodBits ea (listBits (prodBits ea eb))) eb)
      (prodBits ea (listBits (prodBits ea eb))) step := by
  let s := Poly.fst (prodBits ea (listBits (prodBits ea eb))) eb
  let a := s.comp (Poly.fst ea (listBits (prodBits ea eb)))
  let out := s.comp (Poly.snd ea (listBits (prodBits ea eb)))
  let b := Poly.snd (prodBits ea (listBits (prodBits ea eb))) eb
  exact (a.pair (((a.pair b).pair out).comp (Poly.listCons (prodBits ea eb)))).congr (fun _ => rfl)

end WithParam

noncomputable def Poly.withParam {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) (b₀ : β) :
    Poly (prodBits ea (listBits eb)) (listBits (prodBits ea eb))
      (fun p : α × List β => p.2.map (p.1,·)) := by
  let e := prodBits ea (listBits (prodBits ea eb))
  let size : Polynomial ℕ := 20*(Polynomial.X+1)^2
  have bound (s : α × List (α × β)) (xs pre suf : List β) (h : pre++suf=xs) :
      (prodBits e (listBits eb) (pre.foldl (fun s b => WithParam.step (s,b)) s,suf)).length ≤
        size.eval (prodBits e (listBits eb) (s,xs)).length := by
    rcases s with ⟨a,out⟩
    have hparts := listBits_append_length eb pre suf
    rw [h] at hparts
    have hp := list_length_le_bits eb pre
    have hadd := listBits_append_length (prodBits ea eb) (pre.map (a,·)).reverse out
    rw [listBits_reverse_length,WithParam.mapped_length] at hadd
    let N := (prodBits e (listBits eb) ((a,out),xs)).length
    have ha : (ea a).length ≤ N := by dsimp [N,e,prodBits]; rw [pairBits_length,pairBits_length]; omega
    have hx : (listBits eb xs).length ≤ N := by dsimp [N,prodBits]; rw [pairBits_length]; omega
    have hout : (listBits (prodBits ea eb) out).length ≤ N := by
      dsimp [N,e,prodBits]; rw [pairBits_length,pairBits_length]; omega
    have hpre : pre.length ≤ N := by
      have := listBits_length_pos eb suf
      omega
    have hpr := Nat.mul_le_mul ha hpre
    change _ ≤ size.eval N
    simp only [prodBits,e,pairBits_length,WithParam.fold,size,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,
      Polynomial.eval_one]
    nlinarith
  let c := Poly.fold eb e b₀ (WithParam.poly ea eb) size bound
  let input := ((Poly.fst ea (listBits eb)).pair
    (Poly.const (prodBits ea (listBits eb)) (listBits (prodBits ea eb)) [])).pair
      (Poly.snd ea (listBits eb))
  exact (((input.comp c).comp (Poly.snd ea (listBits (prodBits ea eb)))).comp
    (Poly.listReverse (prodBits ea eb) (a₀,b₀))).congr (fun p => by
      simp only [Function.comp_apply,WithParam.fold,List.append_nil,List.reverse_reverse])

noncomputable def Poly.listMapWith {α β γ : Type} (ea : α → List Bool) (eb : β → List Bool)
    (ec : γ → List Bool) (a₀ : α) (b₀ : β) (c₀ : γ) {f : α × β → γ}
    (cf : Poly (prodBits ea eb) ec f) :
    Poly (prodBits ea (listBits eb)) (listBits ec)
      (fun p : α × List β => p.2.map (fun b => f (p.1,b))) :=
  ((Poly.withParam ea eb a₀ b₀).comp
    (Poly.listMap (prodBits ea eb) ec (a₀,b₀) c₀ cf)).congr (fun p => by
      simp only [Function.comp_apply,List.map_map,Function.comp_def])

noncomputable def Poly.listFlatten {α : Type} (e : α → List Bool) (a₀ : α) :
    Poly (listBits (listBits e)) (listBits e) List.flatten := by
  have bound (out : List α) (xs pre suf : List (List α)) (h : pre++suf=xs) :
      (prodBits (listBits e) (listBits (listBits e))
        (pre.foldl (fun b a => a.reverse++b) out,suf)).length ≤
          (3*Polynomial.X+3).eval (prodBits (listBits e) (listBits (listBits e)) (out,xs)).length := by
    have hp := listBits_append_length (listBits e) pre suf
    rw [h] at hp
    have hf := listBits_flatten_bound e pre
    have hh := listBits_append_length e pre.flatten.reverse out
    rw [listBits_reverse_length] at hh
    simp only [prodBits,pairBits_length,foldl_reverseAppend,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega
  let c := Poly.fold (listBits e) (listBits e) [] (Poly.reverseAppend e a₀)
    (3*Polynomial.X+3) bound
  let input := (Poly.const (listBits (listBits e)) (listBits e) []).pair
    (Poly.identity (listBits (listBits e)))
  exact ((input.comp c).comp (Poly.listReverse e a₀)).congr (fun xs => by
    simp only [Function.comp_apply,foldl_reverseAppend,List.append_nil,List.reverse_reverse,id_eq])

noncomputable def Poly.listFlatMap {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) (b₀ : β) {f : α → List β} (cf : Poly ea (listBits eb) f) :
    Poly (listBits ea) (listBits eb) (List.flatMap f) :=
  ((Poly.listMap ea (listBits eb) a₀ [] cf).comp (Poly.listFlatten eb b₀)).congr
    (fun _ => rfl)

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Option
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                          
section

namespace VertexCover.Machine

noncomputable def Poly.optionMap {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) {f : α → β} (cf : Poly ea eb f) :
    Poly (optionBits ea) (optionBits eb) (Option.map f) :=
  ((Poly.isSome ea).ite (((Poly.getD ea a₀).comp cf).comp (Poly.some eb))
    (Poly.const (optionBits ea) (optionBits eb) none)).congr (fun a => by cases a <;> rfl)

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_TableBase
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.FinalTableFormula.variable_count
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                              
section

namespace VertexCover.Machine
open UniqueGames.Foundations

noncomputable def Poly.tabulate {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) (b₀ : β) {n : α → ℕ} {f : α × ℕ → β}
    (cn : Poly ea natBits n) (cf : Poly (prodBits ea natBits) eb f) :
    Poly ea (listBits eb) (fun a => (List.range (n a)).map (fun i => f (a,i))) :=
  (((Poly.identity ea).pair (cn.comp Poly.range)).comp
    (Poly.listMapWith ea natBits eb a₀ 0 b₀ cf)).congr (fun _ => rfl)

namespace TableMachine
open PCP.GraphTables

def dataCode : Data → List Bool := prodBits natBits (listBits rowCode)
def tableCode (T : Table) : List Bool := dataCode (tableData T)

noncomputable def verticesPoly : Poly tableCode natBits Table.vertices :=
  (Poly.fst natBits (listBits rowCode)).encodeCongr tableData (fun _ => rfl) (fun _ => rfl)

noncomputable def rowsPoly : Poly tableCode (listBits rowCode) (fun T => T.rows.toList.map rowData) :=
  (Poly.snd natBits (listBits rowCode)).encodeCongr tableData (fun _ => rfl) (fun _ => rfl)

noncomputable def dartsPoly : Poly tableCode natBits Table.darts :=
  (rowsPoly.comp (Poly.listLength rowCode rowDefault)).congr (fun T => by simp)

noncomputable def lookupPoly : Poly (prodBits tableCode natBits) rowCode
    (fun p : Table × ℕ => (tableData p.1).2.getD p.2 rowDefault) := by
  let rows := (Poly.fst tableCode natBits).comp rowsPoly
  let idx := Poly.snd tableCode natBits
  exact ((idx.pair rows).comp (Poly.listGetD rowCode rowDefault)).congr (fun _ => by
    simp only [Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop,List.getD_eq_getElem?_getD]
    rfl)

noncomputable def tailPoly : Poly (prodBits tableCode natBits) natBits
    (fun p : Table × ℕ => ((tableData p.1).2.getD p.2 rowDefault).1.1) :=
  lookupPoly.comp ((Poly.fst (prodBits natBits natBits) relationCode).comp (Poly.fst natBits natBits))

noncomputable def reversePoly : Poly (prodBits tableCode natBits) natBits
    (fun p : Table × ℕ => ((tableData p.1).2.getD p.2 rowDefault).1.2) :=
  lookupPoly.comp ((Poly.fst (prodBits natBits natBits) relationCode).comp (Poly.snd natBits natBits))

noncomputable def relationPoly : Poly (prodBits tableCode natBits) relationCode
    (fun p : Table × ℕ => ((tableData p.1).2.getD p.2 rowDefault).2) :=
  lookupPoly.comp (Poly.snd (prodBits natBits natBits) relationCode)

end TableMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_PortCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                             
section

namespace VertexCover.Machine.PortMachine
open UniqueGames.Foundations.PCP
open TableMachine

abbrev Data := ℕ × (List ℕ × List GraphTables.RelationTable)
def dataCode : Data → List Bool :=
  prodBits natBits (prodBits (listBits natBits) (listBits relationCode))
def erase {q : ℕ} (T : PortTables.Input q) : Data :=
  (T.1,(T.2.reverseIndex.toList.map Fin.val,T.2.relations.toList))
def code {q : ℕ} (T : PortTables.Input q) : List Bool := dataCode (erase T)

noncomputable def verticesPoly {q : ℕ} : Poly (code (q := q)) natBits Sigma.fst :=
  (Poly.fst natBits (prodBits (listBits natBits) (listBits relationCode))).encodeCongr
    erase (fun _ => rfl) (fun _ => rfl)
noncomputable def reverseListPoly {q : ℕ} :
    Poly (code (q := q)) (listBits natBits) (fun T => T.2.reverseIndex.toList.map Fin.val) :=
  ((Poly.snd natBits (prodBits (listBits natBits) (listBits relationCode))).comp
    (Poly.fst (listBits natBits) (listBits relationCode))).encodeCongr erase
      (fun _ => rfl) (fun _ => rfl)
noncomputable def relationListPoly {q : ℕ} :
    Poly (code (q := q)) (listBits relationCode) (fun T => T.2.relations.toList) :=
  ((Poly.snd natBits (prodBits (listBits natBits) (listBits relationCode))).comp
    (Poly.snd (listBits natBits) (listBits relationCode))).encodeCongr erase
      (fun _ => rfl) (fun _ => rfl)
noncomputable def reversePoly {q : ℕ} : Poly (prodBits (code (q := q)) natBits) natBits
    (fun p => (p.1.2.reverseIndex.toList.map Fin.val).getD p.2 0) :=
  (((Poly.snd code natBits).pair ((Poly.fst code natBits).comp reverseListPoly)).comp
    (Poly.listGetD natBits 0)).congr (fun _ => by
    simp only [Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop,List.getD_eq_getElem?_getD])
noncomputable def relationPoly {q : ℕ} : Poly (prodBits (code (q := q)) natBits) relationCode
    (fun p => p.1.2.relations.toList.getD p.2 relationDefault) :=
  (((Poly.snd code natBits).pair ((Poly.fst code natBits).comp relationListPoly)).comp
    (Poly.listGetD relationCode relationDefault)).congr (fun _ => by
    simp only [Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop,List.getD_eq_getElem?_getD])

 theorem reverse_valid {q : ℕ} (T : PortTables.Input q) (i : Fin (T.1*q)) :
    (T.2.reverseIndex.toList.map Fin.val).getD i.val 0 = T.2.reverseIndex[i].val := by
  rw [List.getD_eq_getElem _ _ (by simp),List.getElem_map]
  rfl
 theorem relation_valid {q : ℕ} (T : PortTables.Input q) (i : Fin (T.1*q)) :
    T.2.relations.toList.getD i.val relationDefault = T.2.relations[i] := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  rfl

end VertexCover.Machine.PortMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_PortBuilder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                
section

namespace VertexCover.Machine.PortMachine
open UniqueGames.Foundations.PCP
open TableMachine

 theorem materialize_source {α : Type} {q : ℕ} (Q : α → PortTables.Input q)
    (r : α × ℕ → ℕ) (s : α × ℕ → GraphTables.RelationTable)
    (hr : ∀ a (i : Fin ((Q a).1*q)), r (a,i.val) = (Q a).2.reverseIndex[i].val)
    (hs : ∀ a (i : Fin ((Q a).1*q)), s (a,i.val) = (Q a).2.relations[i]) (a : α) :
    ((Q a).1,((List.range ((Q a).1*q)).map (fun i => r (a,i)),
      (List.range ((Q a).1*q)).map (fun i => s (a,i)))) = erase (Q a) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply List.ext_getElem
      · simp [erase]
      · intro i h₁ h₂
        simp only [erase,List.getElem_map,List.getElem_range,Vector.getElem_toList]
        exact hr a ⟨i,by simpa using h₁⟩
    · apply List.ext_getElem
      · simp [erase]
      · intro i h₁ h₂
        simp only [erase,List.getElem_map,List.getElem_range,Vector.getElem_toList]
        exact hs a ⟨i,by simpa using h₁⟩
noncomputable def materializePoly {α : Type} (ea : α → List Bool) (a₀ : α) {q : ℕ}
    (Q : α → PortTables.Input q) {r : α × ℕ → ℕ} {s : α × ℕ → GraphTables.RelationTable}
    (cn : Poly ea natBits (fun a => (Q a).1))
    (cr : Poly (prodBits ea natBits) natBits r)
    (cs : Poly (prodBits ea natBits) relationCode s)
    (hr : ∀ a (i : Fin ((Q a).1*q)), r (a,i.val) = (Q a).2.reverseIndex[i].val)
    (hs : ∀ a (i : Fin ((Q a).1*q)), s (a,i.val) = (Q a).2.relations[i]) :
    Poly ea code Q := by
  let len := (cn.pair (Poly.const ea natBits q)).comp Poly.natMul
  let rc := Poly.tabulate ea natBits a₀ 0 len cr
  let sc := Poly.tabulate ea relationCode a₀ relationDefault len cs
  let c := cn.pair (rc.pair sc)
  exact c.encodeCongr id (fun _ => rfl) (fun a => by
    change dataCode _ = dataCode _
    exact congrArg dataCode (materialize_source Q r s hr hs a))

end VertexCover.Machine.PortMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ExpanderStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

namespace ExpandMachine

def code {q : ℕ} (T : Input q) : List Bool := dataCode (erase T)

noncomputable def lookupPoly (q : ℕ) :
    Poly (prodBits (listBits natBits) (prodBits natBits natBits)) (prodBits natBits natBits) (lookup q) := by
  let e := prodBits (listBits natBits) (prodBits natBits natBits)
  let rows := Poly.fst (listBits natBits) (prodBits natBits natBits)
  let x := Poly.snd (listBits natBits) (prodBits natBits natBits)
  let v := x.comp (Poly.fst natBits natBits)
  let port := x.comp (Poly.snd natBits natBits)
  let base := ((Poly.const e natBits q).pair v).comp Poly.natMul
  let idx := (port.pair base).comp Poly.natAdd
  let r := (idx.pair rows).comp (Poly.listGetD natBits 0)
  let qp := r.pair (Poly.const e natBits q)
  exact ((qp.comp Poly.natDiv).pair (qp.comp Poly.natMod)).congr (fun _ => by
    simp only [Function.comp_apply,lookup,List.headD_eq_head?_getD,List.head?_drop,List.getD_eq_getElem?_getD])

 theorem lookup_erase {q v : ℕ} (T : ExpanderTables.Table v q) (x : Fin v × Fin q) :
    lookup q (T.rows.toList.map Fin.val,(x.1.val,x.2.val)) =
      ((ExpanderTables.lookup T x).1.val,(ExpanderTables.lookup T x).2.val) := by
  have hi : x.2.val+q*x.1.val < (T.rows.toList.map Fin.val).length := by
    simp only [List.length_map,Vector.length_toList]
    exact (ExpanderTables.rowIndex v q x).isLt
  rw [lookup,List.getD_eq_getElem _ _ hi,List.getElem_map]
  rfl

noncomputable def stepRowPoly (d : ℕ) (H : List ℕ) :
    Poly (prodBits dataCode natBits) natBits (stepRow d H) := by
  let e := prodBits dataCode natBits
  let D := d*d
  let g := D*D
  let c (n : ℕ) := Poly.const e natBits n
  let T := Poly.fst dataCode natBits
  let rows := T.comp (Poly.snd natBits (listBits natBits))
  let i := Poly.snd dataCode natBits
  let x := (i.pair (c D)).comp Poly.natDiv
  let port := (i.pair (c D)).comp Poly.natMod
  let Hc := Poly.const e (listBits natBits) H
  let first := (Hc.pair (((x.pair (c g)).comp Poly.natMod).pair
    ((port.pair (c d)).comp Poly.natDiv))).comp (lookupPoly d)
  let firstV := first.comp (Poly.fst natBits natBits)
  let firstP := first.comp (Poly.snd natBits natBits)
  let out₁ := (rows.pair (((x.pair (c g)).comp Poly.natDiv).pair
    ((firstV.pair (c D)).comp Poly.natDiv))).comp (lookupPoly D)
  let out₁V := out₁.comp (Poly.fst natBits natBits)
  let out₁P := out₁.comp (Poly.snd natBits natBits)
  let out₂ := (rows.pair (out₁V.pair ((firstV.pair (c D)).comp Poly.natMod))).comp (lookupPoly D)
  let out₂V := out₂.comp (Poly.fst natBits natBits)
  let out₂P := out₂.comp (Poly.snd natBits natBits)
  let lastV := (out₁P.pair (((c D).pair out₂P).comp Poly.natMul)).comp Poly.natAdd
  let last := (Hc.pair (lastV.pair ((port.pair (c d)).comp Poly.natMod))).comp (lookupPoly d)
  let v := ((last.comp (Poly.fst natBits natBits)).pair
    (((c g).pair out₂V).comp Poly.natMul)).comp Poly.natAdd
  let p := (firstP.pair (((c d).pair (last.comp (Poly.snd natBits natBits))).comp Poly.natMul)).comp Poly.natAdd
  exact (p.pair (((c D).pair v).comp Poly.natMul)).comp Poly.natAdd

noncomputable def stepDataPoly (d : ℕ) (H : List ℕ) : Poly dataCode dataCode (stepData d H) := by
  let v := ((Poly.fst natBits (listBits natBits)).pair
    (Poly.const dataCode natBits ((d*d)*(d*d)))).comp Poly.natMul
  let len := (v.pair (Poly.const dataCode natBits (d*d))).comp Poly.natMul
  exact v.pair (Poly.tabulate dataCode natBits (0,[]) 0 len (stepRowPoly d H))

end ExpandMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ExpanderCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                    
section

namespace VertexCover.Machine.ExpandMachine
open UniqueGames.Foundations.PCP

@[simp] theorem lookup_fst_val {q v : ℕ} (T : ExpanderTables.Table v q) (x : Fin v × Fin q) :
    (ExpanderTables.lookup T x).1.val = (lookup q (T.rows.toList.map Fin.val,(x.1.val,x.2.val))).1 :=
  (congrArg Prod.fst (lookup_erase T x)).symm
@[simp] theorem lookup_snd_val {q v : ℕ} (T : ExpanderTables.Table v q) (x : Fin v × Fin q) :
    (ExpanderTables.lookup T x).2.val = (lookup q (T.rows.toList.map Fin.val,(x.1.val,x.2.val))).2 :=
  (congrArg Prod.snd (lookup_erase T x)).symm

 theorem stepRow_lookup {v d : ℕ} (T : ExpanderTables.Table v (d*d))
    (H : ExpanderTables.Table ((d*d)*(d*d)) d) (i : Fin ((v*((d*d)*(d*d)))*(d*d))) :
    stepRow d (H.rows.toList.map Fin.val) (erase ⟨v,T⟩,i.val) =
      (ExpanderTables.rowIndex _ _ (ExpanderTables.stepLookup T H
        ((ExpanderTables.rowIndex _ _).symm i))).val := by
  simp only [ExpanderTables.stepLookup,index_val,index_inv_fst,index_inv_snd,
    lookup_fst_val,lookup_snd_val]
  rfl

 theorem stepRow_source {v d : ℕ} (T : ExpanderTables.Table v (d*d))
    (H : ExpanderTables.Table ((d*d)*(d*d)) d) (i : Fin ((v*((d*d)*(d*d)))*(d*d))) :
    stepRow d (H.rows.toList.map Fin.val) (erase ⟨v,T⟩,i.val) =
      (ExpanderTables.step T H).rows[i].val := by
  rw [stepRow_lookup,← ExpanderTables.lookup_step]
  simp only [ExpanderTables.lookup,Equiv.apply_symm_apply,ExpanderTables.reverseIndex]

 def step {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d) (T : Input (d*d)) : Input (d*d) :=
  ⟨T.1*((d*d)*(d*d)),ExpanderTables.step T.2 H⟩

 theorem stepData_source {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d) (T : Input (d*d)) :
    stepData d (H.rows.toList.map Fin.val) (erase T)=erase (step H T) := by
  apply Prod.ext
  · rfl
  · apply List.ext_getElem
    · simp [stepData,erase,step]
    · intro i h₁ h₂
      simp only [stepData,List.getElem_map,List.getElem_range,erase,step,Vector.getElem_toList]
      exact stepRow_source T.2 H ⟨i, by simpa [stepData,erase] using h₁⟩

noncomputable def stepPoly {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d) :
    Poly (code (q := d*d)) code (step H) :=
  (stepDataPoly d (H.rows.toList.map Fin.val)).encodeCongr erase (fun _ => rfl) (fun T => by
    change dataCode _ = dataCode _
    rw [stepData_source])

end VertexCover.Machine.ExpandMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ExpanderBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                  
section

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

namespace ExpandMachine

noncomputable def verticesPoly {q : ℕ} : Poly (code (q := q)) natBits Sigma.fst :=
  (Poly.fst natBits (listBits natBits)).encodeCongr erase (fun _ => rfl) (fun _ => rfl)

 theorem code_bound {q : ℕ} (T : Input q) :
    (code T).length ≤ 2*T.1+2+(T.1*q)*(2*(T.1*q)+2) := by
  have hb := listBits_length_bound natBits (T.2.rows.toList.map Fin.val) (T.1*q) (by
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    simpa only [natBits_length] using Nat.le_of_lt i.isLt)
  simp only [List.length_map,Vector.length_toList] at hb
  simp only [code,dataCode,erase,prodBits,pairBits_length,natBits_length]
  omega

 theorem vertices_le_code {q : ℕ} (T : Input q) : T.1 ≤ (code T).length := by
  simp only [code,dataCode,erase,prodBits,pairBits_length,natBits_length]
  omega

def capped {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d)
    (p : ℕ × Input (d*d)) : ℕ × Input (d*d) :=
  (p.1,if p.1 ≤ p.2.1 then p.2 else step H p.2)

noncomputable def cappedPoly {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d) :
    Poly (prodBits natBits (code (q := d*d))) (prodBits natBits code) (capped H) := by
  let ck := Poly.fst natBits (code (q := d*d))
  let ct := Poly.snd natBits (code (q := d*d))
  let test := (ck.pair (ct.comp verticesPoly)).comp Poly.natLE
  exact ck.pair ((test.ite ct (ct.comp (stepPoly H))).congr (fun p => by simp))

 theorem capped_iterate_bound {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d)
    (n : ℕ) (p : ℕ × Input (d*d)) :
    (Iterate.run (capped H) n p).1=p.1 ∧
    (Iterate.run (capped H) n p).2.1 ≤ max p.2.1 (((d*d)*(d*d))*p.1) := by
  induction n generalizing p with
  | zero => exact ⟨rfl,Nat.le_max_left _ _⟩
  | succ n ih =>
    have hh := ih (capped H p)
    refine ⟨hh.1,hh.2.trans ?_⟩
    apply max_le
    · simp only [capped]
      split
      · exact Nat.le_max_left _ _
      · rename_i h
        change p.2.1*((d*d)*(d*d)) ≤ _
        rw [Nat.mul_comm]
        exact (Nat.mul_le_mul_left _ (Nat.le_of_lt (Nat.lt_of_not_ge h))).trans (Nat.le_max_right _ _)
    · exact Nat.le_max_right _ _

noncomputable def cappedIteratePoly {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d) :
    Poly (prodBits natBits (prodBits natBits (code (q := d*d))))
      (prodBits natBits code) (fun p => Iterate.run (capped H) p.1 p.2) := by
  let g := (d*d)*(d*d)
  let Q := d*d
  let size : Polynomial ℕ := Polynomial.C (20*((g+1)*(Q+1)+1)^2)*(Polynomial.X+1)^2
  apply Poly.iterate _ (cappedPoly H) size
  intro n p k l h
  let N := (prodBits natBits (prodBits natBits (code (q := d*d))) (n,p)).length
  have hn : n ≤ N := by dsimp [N,prodBits]; simp only [pairBits_length,natBits_length]; omega
  have hp : p.1 ≤ N := by dsimp [N,prodBits]; simp only [pairBits_length,natBits_length]; omega
  have hv : p.2.1 ≤ N := by
    have hh := vertices_le_code p.2
    dsimp [N,prodBits]; simp only [pairBits_length,natBits_length]; omega
  have hb := capped_iterate_bound H k p
  change (prodBits natBits (prodBits natBits (code (q := d*d)))
    (l,Iterate.run (capped H) k p)).length ≤ size.eval N
  simp only [prodBits,pairBits_length,natBits_length,hb.1,size,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  exact encoding_bound Q g n p.1 p.2.1 _ l N _ hn hp hv (by omega) hb.2 (code_bound _)

end ExpandMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ExpanderFamily
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

namespace ExpandMachine

def family {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d) (e : ℕ) : Input (d*d) :=
  ⟨ExpanderTables.vertexCount (d*d) e,ExpanderTables.family H e⟩

 theorem capped_family {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d)
    (fuel k e : ℕ) :
    Iterate.run (capped H) fuel (k,family H e) =
      (k,family H (PreprocessingLevels.levelLoop ((d*d)*(d*d)) k fuel e
        (ExpanderTables.vertexCount (d*d) e)).1) := by
  induction fuel generalizing e with
  | zero => rfl
  | succ fuel ih =>
    by_cases hh : k ≤ ExpanderTables.vertexCount (d*d) e
    · rw [PreprocessingLevels.levelLoop,ite_eq_left hh]
      exact iterate_fixed (capped H) _ (by simp [capped,family,hh]) _
    · rw [PreprocessingLevels.levelLoop,ite_eq_right hh]
      change Iterate.run (capped H) fuel (capped H (k,family H e)) = _
      have hc : capped H (k,family H e) = (k,family H (e+1)) := by
        dsimp only [capped,family]
        rw [ite_eq_right hh]
        rfl
      rw [hc,ih]
      rfl

def paddedFamily (H : PreprocessingRegularTables.BaseTable) (k : ℕ) :
    Input PreprocessingRegularTables.internalDegree :=
  family H (PreprocessingLevels.boundedLevel k)

 theorem paddedFamily_run (H : PreprocessingRegularTables.BaseTable) (k : ℕ) :
    Iterate.run (capped H) k (k,family H 0) = (k,paddedFamily H k) := by
  rw [capped_family]
  unfold paddedFamily PreprocessingLevels.boundedLevel PreprocessingLevels.searchResult
  rw [growth_eq]
  rfl

noncomputable def paddedFamilyPoly (H : PreprocessingRegularTables.BaseTable) :
    Poly natBits code (paddedFamily H) := by
  let Q := Expanders.baseDegree*Expanders.baseDegree
  let start := (Poly.identity natBits).pair
    ((Poly.identity natBits).pair (Poly.const natBits (code (q := Q)) (family H 0)))
  exact (((start.comp (cappedIteratePoly H)).comp (Poly.snd natBits code))).congr
    (fun k => congrArg Prod.snd (paddedFamily_run H k))

 theorem paddedFamily_vertices (H : PreprocessingRegularTables.BaseTable) (k : ℕ) :
    (paddedFamily H k).1 = PreprocessingLevels.paddedSize k :=
  PreprocessingLevels.table_vertexCount_eq_paddedSize k

noncomputable def paddedSizePoly : Poly natBits natBits PreprocessingLevels.paddedSize := by
  let H := Classical.choose ExpanderTables.exists_base_table
  exact ((paddedFamilyPoly H).comp verticesPoly).congr (paddedFamily_vertices H)

noncomputable def cloudPaddedPoly : Poly natBits natBits PreprocessingLevels.cloudPaddedSize :=
  (Poly.natZero.ite (Poly.const natBits natBits 0) paddedSizePoly).congr (fun k => by
    simp [PreprocessingLevels.cloudPaddedSize])

end ExpandMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                               
section

namespace VertexCover.Machine

noncomputable def Poly.listSingleton {α : Type} (ea : α → List Bool) :
    Poly ea (listBits ea) (fun a => [a]) := by
  exact (((Poly.identity ea).pair (Poly.const ea (listBits ea) [])).comp (Poly.listCons ea))

noncomputable def Poly.listFilterWith {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) (b₀ : β) {f : α × β → Bool} (cf : Poly (prodBits ea eb) boolBits f) :
    Poly (prodBits ea (listBits eb)) (listBits eb)
      (fun p => p.2.filter (fun b => f (p.1,b))) := by
  let c := cf.ite ((Poly.snd ea eb).comp (Poly.listSingleton eb))
    (Poly.const (prodBits ea eb) (listBits eb) [])
  exact (((Poly.withParam ea eb a₀ b₀).comp
    (Poly.listFlatMap (prodBits ea eb) eb (a₀,b₀) b₀ c))).congr (fun p => by
    simp only [Function.comp_apply,List.flatMap_map]
    induction p.2 with
    | nil => rfl
    | cons b bs ih =>
      cases h : f (p.1,b) <;> simp [h,ih])

noncomputable def Poly.natLt : Poly (prodBits natBits natBits) boolBits
    (fun p : ℕ × ℕ => decide (p.1<p.2)) :=
  ((Poly.swap natBits natBits).comp Poly.natLE).comp (Poly.bool Bool.not) |>.congr
    (fun p => by
      by_cases h : p.1<p.2
      · have hn := Nat.not_le.mpr h
        simp [h,hn]
      · have hn := Nat.le_of_not_gt h
        simp [h,hn])

noncomputable def Poly.natPairEq : Poly (prodBits (prodBits natBits natBits) (prodBits natBits natBits))
    boolBits (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1 == p.2) := by
  let e := prodBits natBits natBits
  let a := Poly.fst e e
  let b := Poly.snd e e
  let cf := (((a.comp (Poly.fst natBits natBits)).pair
    (b.comp (Poly.fst natBits natBits))).comp Poly.natEq)
  let cs := (((a.comp (Poly.snd natBits natBits)).pair
    (b.comp (Poly.snd natBits natBits))).comp Poly.natEq)
  exact (cf.pair cs).comp (Poly.bool₂ (fun p => p.1 && p.2))

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Cloud
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

namespace TableMachine

def emptyTable : GraphTables.Table := GraphTables.ofGraph (n := 0)
  { reverse := Equiv.refl (Fin 0),reverse_involutive := fun _ => rfl,
    tail := fun e => e.elim0,accepts := fun _ _ _ => true,reverse_accepts := fun _ _ _ => rfl }

end TableMachine

namespace CloudMachine
open TableMachine

noncomputable def cloudPoly : Poly (prodBits tableCode natBits) (listBits natBits) cloud := by
  let ea := prodBits tableCode natBits
  let ctx := Poly.fst ea natBits
  let t := ctx.comp (Poly.fst tableCode natBits)
  let v := ctx.comp (Poly.snd tableCode natBits)
  let i := Poly.snd ea natBits
  let test := (((t.pair i).comp tailPoly).pair v).comp Poly.natEq
  let len := (Poly.fst tableCode natBits).comp dartsPoly
  exact (((Poly.identity ea).pair (len.comp Poly.range)).comp
    (Poly.listFilterWith ea natBits (emptyTable,0) 0 test))

def padding (p : GraphTables.Table × ℕ) : ℕ :=
  let k := (cloud p).length
  PreprocessingLevels.cloudPaddedSize k-k

noncomputable def paddingPoly : Poly (prodBits tableCode natBits) natBits padding := by
  let k := cloudPoly.comp (Poly.listLength natBits 0)
  exact ((k.comp ExpandMachine.cloudPaddedPoly).pair k).comp Poly.natSub

def localDummies (p : GraphTables.Table × ℕ) : List (ℕ × ℕ) :=
  (List.range (padding p)).map (p.2,·)

noncomputable def localDummiesPoly : Poly (prodBits tableCode natBits) (listBits pairCode) localDummies :=
  (((Poly.snd tableCode natBits).pair (paddingPoly.comp Poly.range)).comp
    (Poly.withParam natBits natBits 0 0))

def dummies (T : GraphTables.Table) : List (ℕ × ℕ) :=
  (List.range T.vertices).flatMap (fun v => localDummies (T,v))

noncomputable def dummiesPoly : Poly tableCode (listBits pairCode) dummies :=
  ((Poly.tabulate tableCode (listBits pairCode) emptyTable [] verticesPoly localDummiesPoly).comp
    (Poly.listFlatten pairCode (0,0))).congr (fun T => by
      rfl)

 theorem cloud_source (T : GraphTables.Table) (v : Fin T.vertices) :
    cloud (T,v.val) = (PreprocessingCloudIndex.cloudDarts T v).map Fin.val := by
  unfold cloud PreprocessingCloudIndex.cloudDarts
  rw [← map_finRange_val]
  rw [List.filter_map]
  apply congrArg (List.map Fin.val)
  congr 1
  funext e
  change (((tableData T).2.getD e.val rowDefault).1.1 == v.val) = _
  rw [lookup_valid]
  simp only [rowData,Fin.ext_iff]
  rfl

 theorem padding_source (T : GraphTables.Table) (v : Fin T.vertices) :
    padding (T,v.val) = PreprocessingRegularTables.padding T v := by
  simp only [padding,cloud_source,List.length_map,PreprocessingRegularTables.padding,
    PreprocessingCloudIndex.cloudSize]

 theorem dummies_source (T : GraphTables.Table) :
    dummies T = (PreprocessingRegularTables.paddingList (PreprocessingRegularTables.padding T)).map
      (fun z => (z.1.val,z.2.val)) := by
  unfold dummies PreprocessingRegularTables.paddingList
  rw [← map_finRange_val,List.flatMap_map]
  simp only [List.sigma,List.map_flatMap,List.map_map,Function.comp_def]
  apply List.flatMap_congr
  intro v _
  simp only [localDummies,padding_source]
  rw [← map_finRange_val,List.map_map]
  rfl

noncomputable def regularVerticesPoly : Poly tableCode natBits PreprocessingTables.regularVertices := by
  let c := (dartsPoly.pair (dummiesPoly.comp (Poly.listLength pairCode (0,0)))).comp Poly.natAdd
  exact c.congr (fun T => by
    simp only [Function.comp_apply,dummies_source,List.length_map,
      PreprocessingRegularTables.paddingList_length,PreprocessingTables.regularVertices,
      PreprocessingRegularTables.vertexCount])

end CloudMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_CloudFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                       
section

namespace VertexCover.Machine.CloudMachine
open UniqueGames.Foundations.PCP
open TableMachine PreprocessingCloudIndex PreprocessingRegularTables

 theorem erase_resize {n m q : ℕ} (h : n=m) (T : ExpanderTables.Table n q) :
    ExpandMachine.erase ⟨m,resizeTable h T⟩ = ExpandMachine.erase ⟨n,T⟩ := by
  subst m
  rfl

def cloudFamily (H : BaseTable) (k : ℕ) : ExpandMachine.Data :=
  if k=0 then (0,[]) else ExpandMachine.erase (ExpandMachine.paddedFamily H k)

noncomputable def cloudFamilyPoly (H : BaseTable) :
    Poly natBits ExpandMachine.dataCode (cloudFamily H) := by
  let c : Poly natBits ExpandMachine.dataCode (fun k => ExpandMachine.erase (ExpandMachine.paddedFamily H k)) :=
    (ExpandMachine.paddedFamilyPoly H).encodeCongr id (fun _ => rfl) (fun _ => rfl)
  exact Poly.natZero.ite (Poly.const natBits ExpandMachine.dataCode (0,[])) c |>.congr (fun k => by
    simp only [cloudFamily,decide_eq_true_eq])

def cloudLookup (H : BaseTable) (p : GraphTables.Table × (ℕ × (ℕ × ℕ))) : ℕ × ℕ :=
  ExpandMachine.lookup internalDegree
    ((cloudFamily H (cloud (p.1,p.2.1)).length).2,p.2.2)

noncomputable def cloudLookupPoly (H : BaseTable) :
    Poly (prodBits tableCode (prodBits natBits pairCode)) pairCode (cloudLookup H) := by
  let t := Poly.fst tableCode (prodBits natBits pairCode)
  let x := Poly.snd tableCode (prodBits natBits pairCode)
  let v := x.comp (Poly.fst natBits pairCode)
  let coords := x.comp (Poly.snd natBits pairCode)
  let rows := ((((t.pair v).comp cloudPoly).comp (Poly.listLength natBits 0)).comp
    (cloudFamilyPoly H)).comp (Poly.snd natBits (listBits natBits))
  exact (rows.pair coords).comp (ExpandMachine.lookupPoly internalDegree)

end VertexCover.Machine.CloudMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                           
section

namespace VertexCover.Machine

noncomputable def Poly.foldNonincreasing {α β : Type} (ea : α → List Bool)
    (eb : β → List Bool) (a₀ : α) {f : β × α → β}
    (cf : Poly (prodBits eb ea) eb f)
    (h : ∀ b a, (eb (f (b,a))).length ≤ (eb b).length) :
    Poly (prodBits eb (listBits ea)) eb (fun p => p.2.foldl (fun b a => f (b,a)) p.1) :=
  Poly.fold ea eb a₀ cf Polynomial.X (by
    intro b xs pre suf he
    have hf := foldl_bits_le eb f h pre b
    have hx := listBits_append_length ea pre suf
    have hp := listBits_length_pos ea pre
    rw [he] at hx
    simp only [Polynomial.eval_X,prodBits,pairBits_length]
    omega)

noncomputable def Poly.listAnd : Poly (listBits boolBits) boolBits (fun xs => xs.foldl (· && ·) true) :=
  (((Poly.const (listBits boolBits) boolBits true).pair (Poly.identity (listBits boolBits))).comp
    (Poly.foldNonincreasing boolBits boolBits false (Poly.bool₂ (fun p => p.1 && p.2))
      (by intros; rfl))).congr (fun _ => rfl)

noncomputable def Poly.listAny {α : Type} (ea : α → List Bool) (a₀ : α)
    {f : α → Bool} (cf : Poly ea boolBits f) :
    Poly (listBits ea) boolBits (fun xs => (xs.map f).foldl (· || ·) false) := by
  let c := Poly.foldNonincreasing boolBits boolBits false (Poly.bool₂ (fun p => p.1 || p.2))
    (by intros; rfl)
  exact ((Poly.listMap ea boolBits a₀ false cf).comp
    (((Poly.const (listBits boolBits) boolBits false).pair (Poly.identity (listBits boolBits))).comp c)).congr (fun _ => rfl)

noncomputable def Poly.listIsEmpty {α : Type} (ea : α → List Bool) :
    Poly (listBits ea) boolBits List.isEmpty :=
  ((Poly.listHasHead ea).comp (Poly.bool not)).congr (fun xs => by cases xs <;> rfl)

namespace ListCompare
variable {α : Type} [DecidableEq α]

noncomputable def poly (ea : α → List Bool) (a₀ : α)
    (ce : Poly (prodBits ea ea) boolBits (fun p : α × α => decide (p.1=p.2))) :
    Poly (prodBits (prodBits (listBits ea) boolBits) ea)
      (prodBits (listBits ea) boolBits) step := by
  let s := Poly.fst (prodBits (listBits ea) boolBits) ea
  let ys := s.comp (Poly.fst (listBits ea) boolBits)
  let b := s.comp (Poly.snd (listBits ea) boolBits)
  let a := Poly.snd (prodBits (listBits ea) boolBits) ea
  let test := ys.comp (Poly.listIsEmpty ea)
  let cmp := (a.pair (ys.comp (Poly.listHeadD ea a₀))).comp ce
  let flag := (b.pair (test.ite (Poly.const _ boolBits false) cmp)).comp
    (Poly.bool₂ (fun p => p.1 && p.2))
  exact ((ys.comp (Poly.listTail ea)).pair flag).congr (fun ⟨⟨ys,b⟩,a⟩ => by
    cases ys <;> rfl)
end ListCompare

noncomputable def Poly.listEq {α : Type} [DecidableEq α] (ea : α → List Bool) (a₀ : α)
    (ce : Poly (prodBits ea ea) boolBits (fun p : α × α => decide (p.1=p.2))) :
    Poly (prodBits (listBits ea) (listBits ea)) boolBits
      (fun p : List α × List α => decide (p.1=p.2)) := by
  let e := prodBits (listBits ea) boolBits
  let c := Poly.foldNonincreasing ea e a₀ (ListCompare.poly ea a₀ ce) (by
    intro ⟨ys,b⟩ a
    have ht := listBits_tail_length_le ea ys
    simp only [e,prodBits,pairBits_length,ListCompare.step,boolBits,List.length_singleton]
    omega)
  let input := ((Poly.snd (listBits ea) (listBits ea)).pair
    (Poly.const _ boolBits true)).pair (Poly.fst (listBits ea) (listBits ea))
  let finish := ((Poly.snd (listBits ea) boolBits).pair
    ((Poly.fst (listBits ea) boolBits).comp (Poly.listIsEmpty ea))).comp
      (Poly.bool₂ (fun p => p.1 && p.2))
  exact ((input.comp c).comp finish).congr (fun p => by
    simpa only [Function.comp_apply,Bool.true_and] using ListCompare.result p.1 p.2 true)

noncomputable def Poly.rawEq : Poly (prodBits id id) boolBits
    (fun p : List Bool × List Bool => decide (p.1=p.2)) := by
  let a := (Poly.fst id id).comp Poly.rawToList
  let b := (Poly.snd id id).comp Poly.rawToList
  exact (a.pair b).comp (Poly.listEq boolBits false (Poly.bool₂ (fun p => decide (p.1=p.2))))

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListGrowing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                            
section

namespace VertexCover.Machine

noncomputable def Poly.foldGrowing {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) {f : β × α → β} (cf : Poly (prodBits eb ea) eb f) (K : ℕ)
    (hstep : ∀ b a, (eb (f (b,a))).length ≤ (eb b).length + K * (2*(ea a).length+2)) :
    Poly (prodBits eb (listBits ea)) eb (fun p : β × List α => p.2.foldl (fun b a => f (b,a)) p.1) := by
  have grow (xs : List α) (b : β) :
      (eb (xs.foldl (fun b a => f (b,a)) b)).length ≤ (eb b).length+K*(listBits ea xs).length := by
    induction xs generalizing b with
    | nil => simp
    | cons a xs ih =>
      have hh := hstep b a
      have ht := ih (f (b,a))
      simp only [List.foldl_cons,listBits_cons_length]
      nlinarith
  exact Poly.fold ea eb a₀ cf (Polynomial.C (2*K+3)*Polynomial.X+3) (by
    intro b xs pre suf h
    have hg := grow pre b
    have hp := listBits_append_length ea pre suf
    rw [h] at hp
    have hpos := listBits_length_pos ea pre
    have hpos₂ := listBits_length_pos ea suf
    simp only [prodBits,pairBits_length,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat]
    nlinarith)

noncomputable def Poly.listAny' {α : Type} (ea : α → List Bool) (a₀ : α)
    {f : α → Bool} (cf : Poly ea boolBits f) :
    Poly (listBits ea) boolBits (fun xs => xs.any f) :=
  (Poly.listAny ea a₀ cf).congr (fun xs => by simp only [foldl_or_any,Bool.false_or])

noncomputable def Poly.listContains {α : Type} [BEq α] (ea : α → List Bool) (a₀ : α)
    (ce : Poly (prodBits ea ea) boolBits (fun p : α × α => p.1 == p.2)) :
    Poly (prodBits ea (listBits ea)) boolBits (fun p : α × List α => p.2.any (p.1 == ·)) :=
  ((Poly.withParam ea ea a₀ a₀).comp (Poly.listAny' (prodBits ea ea) (a₀,a₀) ce)).congr
    (fun p => by
      change (p.2.map (p.1,·)).any (fun q => q.1 == q.2) = _
      simp only [List.any_map,Function.comp_def])

namespace Dedup
variable {α : Type} [BEq α]

noncomputable def poly (ea : α → List Bool) (a₀ : α)
    (ce : Poly (prodBits ea ea) boolBits (fun p : α × α => p.1 == p.2)) :
    Poly (prodBits (listBits ea) ea) (listBits ea) step :=
  (((Poly.swap (listBits ea) ea).comp (Poly.listContains ea a₀ ce)).ite
    (Poly.fst (listBits ea) ea) ((Poly.swap (listBits ea) ea).comp (Poly.listCons ea))).congr
      (fun _ => rfl)
end Dedup

noncomputable def Poly.eraseDups {α : Type} [BEq α] (ea : α → List Bool) (a₀ : α)
    (ce : Poly (prodBits ea ea) boolBits (fun p : α × α => p.1 == p.2)) :
    Poly (listBits ea) (listBits ea) List.eraseDups := by
  let c := Poly.foldGrowing ea (listBits ea) a₀ (Dedup.poly ea a₀ ce) 1 (by
    intro out a
    simp only [Dedup.step]
    split
    · omega
    · rw [listBits_cons_length]; omega)
  exact ((((Poly.const (listBits ea) (listBits ea) []).pair (Poly.identity (listBits ea))).comp c).comp
    (Poly.listReverse ea a₀)).congr (fun xs => Dedup.fold xs [])

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                              
section

namespace VertexCover.Machine
namespace Index
variable {α : Type} [BEq α]

noncomputable def poly (ea : α → List Bool)
    (ce : Poly (prodBits ea ea) boolBits (fun p : α × α => p.1 == p.2)) :
    Poly (prodBits (prodBits ea natBits) ea) (prodBits ea natBits) step := by
  let s := Poly.fst (prodBits ea natBits) ea
  let a := s.comp (Poly.fst ea natBits)
  let n := s.comp (Poly.snd ea natBits)
  let x := Poly.snd (prodBits ea natBits) ea
  let test := (x.pair a).comp ce
  exact (a.pair (test.ite (Poly.const _ natBits 0) (n.comp Poly.natSucc))).congr (fun _ => rfl)
end Index

noncomputable def Poly.listIdxOf {α : Type} [BEq α] (ea : α → List Bool) (a₀ : α)
    (ce : Poly (prodBits ea ea) boolBits (fun p : α × α => p.1 == p.2)) :
    Poly (prodBits ea (listBits ea)) natBits (fun p : α × List α => p.2.idxOf p.1) := by
  let e := prodBits ea natBits
  let c := Poly.foldGrowing ea e a₀ (Index.poly ea ce) 1 (by
    intro ⟨a,n⟩ x
    simp only [Index.step,e,prodBits,pairBits_length,natBits_length]
    split <;> omega)
  let input := ((Poly.fst ea (listBits ea)).pair (Poly.const _ natBits 0)).pair
    ((Poly.snd ea (listBits ea)).comp (Poly.listReverse ea a₀))
  exact ((input.comp c).comp (Poly.snd ea natBits)).congr (fun ⟨a,xs⟩ => by
    change (xs.reverse.foldl (fun s x => Index.step (s,x)) (a,0)).2 = xs.idxOf a
    rw [List.foldl_reverse,Index.foldr])

noncomputable def Poly.bitsNatEq : Poly (prodBits Nat.bits Nat.bits) boolBits
    (fun p : ℕ × ℕ => p.1 == p.2) :=
  Poly.rawEq.encodeCongr (fun p => (p.1.bits,p.2.bits)) (fun _ => rfl) (fun p => by
    have he : p.1.bits=p.2.bits ↔ p.1=p.2 := by
      constructor
      · intro h
        have hh := congrArg UniqueGames.BinaryEncoding.bitsValue h
        simpa only [UniqueGames.BinaryEncoding.bitsValue_bits] using hh
      · exact congrArg Nat.bits
    simp only [he]
    apply congrArg boolBits
    apply Bool.eq_iff_iff.mpr
    simp)

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_CloudIndex
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.AlphabetRetraction.edgeSatisfied_pullback _root_.OAI.UniqueGames.Foundations.PCP.AlphabetRetraction.rejectionCount_pullback _root_.OAI.UniqueGames.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGames.Foundations.PCP.FiniteGraph.Bundle.ofGraph_graph _root_.OAI.UniqueGames.Foundations.PCP.FiniteGraph.Bundle.ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.FiniteGraph.Bundle.ofGraph_size _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                      
section

namespace VertexCover.Machine.CloudMachine
open UniqueGames.Foundations.PCP
open TableMachine PreprocessingCloudIndex PreprocessingRegularTables

def dummyErase {T : GraphTables.Table} (z : Dummy T) : ℕ × ℕ := (z.1.val,z.2.val)
 theorem dummyErase_injective (T : GraphTables.Table) : Function.Injective (dummyErase (T := T)) := by
  rintro ⟨v,i⟩ ⟨w,j⟩ h
  have hv : v=w := Fin.ext (congrArg Prod.fst h)
  subst w
  have hi : i=j := Fin.ext (congrArg Prod.snd h)
  subst j
  rfl

 theorem dummies_idx (T : GraphTables.Table) (z : Dummy T) :
    (dummies T).idxOf (dummyErase z) = (paddingOrder (PreprocessingRegularTables.padding T) z).val := by
  rw [dummies_source]
  exact idxOf_map_injective dummyErase (dummyErase_injective T) _ z

 theorem dummies_get (T : GraphTables.Table) (z : Dummy T) :
    (dummies T).getD (paddingOrder (PreprocessingRegularTables.padding T) z).val (0,0) = dummyErase z := by
  rw [← dummies_idx]
  apply getD_idxOf
  rw [dummies_source]
  exact List.mem_map.mpr ⟨z,mem_paddingList _ z,rfl⟩

 theorem cloud_idx (T : GraphTables.Table) (v : Fin T.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics T) v) :
    (cloud (T,v.val)).idxOf e.val.val = (cloudRank T v e).val := by
  rw [cloud_source]
  exact idxOf_map_injective Fin.val Fin.val_injective _ _

 theorem cloud_get (T : GraphTables.Table) (v : Fin T.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics T) v) :
    (cloud (T,v.val)).getD (cloudRank T v e).val 0 = e.val.val := by
  rw [← cloud_idx]
  apply getD_idxOf
  rw [cloud_source]
  exact List.mem_map.mpr ⟨e.val,(mem_cloudDarts T v _).mpr e.property,rfl⟩

def ownerRank (p : GraphTables.Table × ℕ) : ℕ × ℕ :=
  if p.2 < p.1.darts then
    let v := ((tableData p.1).2.getD p.2 rowDefault).1.1
    (v,(cloud (p.1,v)).idxOf p.2)
  else
    let z := (dummies p.1).getD (p.2-p.1.darts) (0,0)
    (z.1,(cloud (p.1,z.1)).length+z.2)

noncomputable def ownerRankPoly : Poly (prodBits tableCode natBits) pairCode ownerRank := by
  let e := prodBits tableCode natBits
  let t := Poly.fst tableCode natBits
  let i := Poly.snd tableCode natBits
  let m := t.comp dartsPoly
  let v := tailPoly
  let old := v.pair ((i.pair ((t.pair v).comp cloudPoly)).comp
    (Poly.listIdxOf natBits 0 Poly.natEq))
  let z := (((i.pair m).comp Poly.natSub).pair (t.comp dummiesPoly)).comp
    (Poly.listGetD pairCode (0,0))
  let zv := z.comp (Poly.fst natBits natBits)
  let zj := z.comp (Poly.snd natBits natBits)
  let len := ((t.pair zv).comp cloudPoly).comp (Poly.listLength natBits 0)
  let new := zv.pair ((len.pair zj).comp Poly.natAdd)
  exact ((i.pair m).comp Poly.natLt).ite old new |>.congr (fun p => by
    simp only [ownerRank,Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop,
      List.getD_eq_getElem?_getD,decide_eq_true_eq])

def globalIndex (p : GraphTables.Table × (ℕ × ℕ)) : ℕ :=
  let xs := cloud (p.1,p.2.1)
  if p.2.2 < xs.length then xs.getD p.2.2 0
  else p.1.darts + (dummies p.1).idxOf (p.2.1,p.2.2-xs.length)

noncomputable def globalIndexPoly : Poly (prodBits tableCode pairCode) natBits globalIndex := by
  let t := Poly.fst tableCode pairCode
  let x := Poly.snd tableCode pairCode
  let v := x.comp (Poly.fst natBits natBits)
  let i := x.comp (Poly.snd natBits natBits)
  let xs := (t.pair v).comp cloudPoly
  let len := xs.comp (Poly.listLength natBits 0)
  let old := (i.pair xs).comp (Poly.listGetD natBits 0)
  let index := (v.pair ((i.pair len).comp Poly.natSub)).pair (t.comp dummiesPoly)
  let new := ((t.comp dartsPoly).pair (index.comp
    (Poly.listIdxOf pairCode (0,0) Poly.natPairEq))).comp Poly.natAdd
  exact ((i.pair len).comp Poly.natLt).ite old new |>.congr (fun p => by
    simp only [globalIndex,Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop,
      List.getD_eq_getElem?_getD,decide_eq_true_eq])

 theorem ownerRank_source (T : GraphTables.Table)
    (e : Vertex T (PreprocessingRegularTables.padding T)) :
    ownerRank (T,(vertexOrder T (PreprocessingRegularTables.padding T) e).val) =
      ((DegreeReplacement.paddedGraph (GraphTables.semantics T)
          (fun v => Fin (PreprocessingRegularTables.padding T v))).tail e |>.val,
       (paddedCloudRank T (PreprocessingRegularTables.padding T) _ ⟨e,rfl⟩).val) := by
  cases e with
  | inl e =>
    rw [vertexOrder_original]
    rw [ownerRank,ite_eq_left e.isLt,lookup_valid]
    change (_,_) = (T.rows[e].tail.val,(cloudRank T T.rows[e].tail ⟨e,rfl⟩).val)
    exact Prod.ext rfl (cloud_idx T T.rows[e].tail ⟨e,rfl⟩)
  | inr z =>
    rw [vertexOrder_dummy]
    dsimp only [ownerRank]
    rw [ite_eq_right (by omega),Nat.add_sub_cancel_left,dummies_get]
    simp only [dummyErase,cloud_source,List.length_map]
    rfl

 theorem globalIndex_source (T : GraphTables.Table) (v : Fin T.vertices)
    (e : PaddedCloud T (PreprocessingRegularTables.padding T) v) :
    globalIndex (T,(v.val,(paddedCloudRank T (PreprocessingRegularTables.padding T) v e).val)) =
      (vertexOrder T (PreprocessingRegularTables.padding T) e.val).val := by
  rcases e with ⟨e,h⟩
  cases e with
  | inl e =>
    have he : (GraphTables.semantics T).tail e = v := h
    change globalIndex (T,(v.val,(cloudRank T v ⟨e,he⟩).val)) = e.val
    dsimp only [globalIndex]
    rw [ite_eq_left (by simpa only [cloud_source,List.length_map,cloudSize] using (cloudRank T v ⟨e,he⟩).isLt)]
    exact cloud_get T v ⟨e,he⟩
  | inr z =>
    have hz : z.1 = v := h
    rcases z with ⟨w,j⟩
    dsimp only at hz
    subst w
    change globalIndex (T,(v.val,cloudSize T v+j.val)) = _
    dsimp only [globalIndex]
    rw [show (cloud (T,v.val)).length = cloudSize T v by simp [cloud_source,cloudSize]]
    rw [ite_eq_right (by omega),Nat.add_sub_cancel_left]
    exact congrArg (T.darts+·) (dummies_idx T ⟨v,j⟩)

end VertexCover.Machine.CloudMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_RegularRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                      
section

namespace VertexCover.Machine.RegularMachine
open UniqueGames.Foundations.PCP
open TableMachine PreprocessingCloudIndex PreprocessingRegularTables CloudMachine

abbrev inputCode := prodBits tableCode pairCode

def reversePair (H : BaseTable) (x : GraphTables.Table × (ℕ × ℕ)) : ℕ × ℕ :=
  if x.2.2 < internalDegree then
    let w := ownerRank (x.1,x.2.1)
    let z := cloudLookup H (x.1,(w.1,(w.2,x.2.2)))
    (globalIndex (x.1,(w.1,z.1)),z.2)
  else
    (if x.2.1 < x.1.darts then ((tableData x.1).2.getD x.2.1 rowDefault).1.2 else x.2.1,
      internalDegree)

noncomputable def reversePairPoly (H : BaseTable) : Poly inputCode pairCode (reversePair H) := by
  let e := inputCode
  let t := Poly.fst tableCode pairCode
  let x := Poly.snd tableCode pairCode
  let v := x.comp (Poly.fst natBits natBits)
  let p := x.comp (Poly.snd natBits natBits)
  let c := Poly.const e natBits internalDegree
  let w := (t.pair v).comp ownerRankPoly
  let wv := w.comp (Poly.fst natBits natBits)
  let wi := w.comp (Poly.snd natBits natBits)
  let z := (t.pair (wv.pair (wi.pair p))).comp (cloudLookupPoly H)
  let newV := (t.pair (wv.pair (z.comp (Poly.fst natBits natBits)))).comp globalIndexPoly
  let inner := newV.pair (z.comp (Poly.snd natBits natBits))
  let rev := (t.pair v).comp TableMachine.reversePoly
  let inherited := (((v.pair (t.comp dartsPoly)).comp Poly.natLt).ite rev v).pair c
  exact ((p.pair c).comp Poly.natLt).ite inner inherited |>.congr (fun x => by
    simp only [reversePair,Function.comp_apply,decide_eq_true_eq])

def equalityRelation : GraphTables.RelationTable := GraphTables.relationOf (fun a b => decide (a=b))
def trueRelation : GraphTables.RelationTable := GraphTables.relationOf (fun _ _ => true)

def relation (x : GraphTables.Table × (ℕ × ℕ)) : GraphTables.RelationTable :=
  if x.2.2 < internalDegree then equalityRelation
  else if x.2.1 < x.1.darts then ((tableData x.1).2.getD x.2.1 rowDefault).2
  else trueRelation

noncomputable def relationPoly : Poly inputCode relationCode relation := by
  let t := Poly.fst tableCode pairCode
  let x := Poly.snd tableCode pairCode
  let v := x.comp (Poly.fst natBits natBits)
  let p := x.comp (Poly.snd natBits natBits)
  let old := (t.pair v).comp TableMachine.relationPoly
  let inherited := ((v.pair (t.comp dartsPoly)).comp Poly.natLt).ite old
    (Poly.const _ relationCode trueRelation)
  exact ((p.pair (Poly.const _ natBits internalDegree)).comp Poly.natLt).ite
    (Poly.const _ relationCode equalityRelation) inherited |>.congr (fun x => by
      simp only [relation,Function.comp_apply,decide_eq_true_eq])

end VertexCover.Machine.RegularMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Overlay
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine.OverlayMachine
open UniqueGames.Foundations.PCP
open TableMachine PreprocessingOverlayTables

abbrev Input (d e : ℕ) := Σ n, PortTables.Table n d × ExpanderTables.Table n e
def base {d e : ℕ} (T : Input d e) : PortTables.Input d := ⟨T.1,T.2.1⟩
def rows {d e : ℕ} (T : Input d e) : List ℕ := T.2.2.rows.toList.map Fin.val
def code {d e : ℕ} (T : Input d e) := prodBits PortMachine.code (listBits natBits) (base T,rows T)
def output {d e : ℕ} (T : Input d e) : PortTables.Input (d+e) := ⟨T.1,overlay T.2.1 T.2.2⟩

noncomputable def basePoly {d e : ℕ} : Poly (code (d := d) (e := e)) PortMachine.code base :=
  (Poly.fst PortMachine.code (listBits natBits)).encodeCongr (fun T => (base T,rows T))
    (fun _ => rfl) (fun _ => rfl)
noncomputable def rowsPoly {d e : ℕ} : Poly (code (d := d) (e := e)) (listBits natBits) rows :=
  (Poly.snd PortMachine.code (listBits natBits)).encodeCongr (fun T => (base T,rows T))
    (fun _ => rfl) (fun _ => rfl)

def pairReverse {d e : ℕ} (x : Input d e × (ℕ × ℕ)) : ℕ × ℕ :=
  if x.2.2 < d then
    ExpandMachine.lookup d ((x.1.2.1.reverseIndex.toList.map Fin.val),x.2)
  else
    let r := ExpandMachine.lookup e (rows x.1,(x.2.1,x.2.2-d))
    (r.1,d+r.2)
def reverse {d e : ℕ} (x : Input d e × ℕ) : ℕ :=
  let r := pairReverse (x.1,(x.2/(d+e),x.2%(d+e)))
  r.2+(d+e)*r.1
def relation {d e : ℕ} (x : Input d e × ℕ) : GraphTables.RelationTable :=
  if x.2%(d+e) < d then
    x.1.2.1.relations.toList.getD (x.2%(d+e)+d*(x.2/(d+e))) relationDefault
  else RegularMachine.trueRelation

noncomputable def pairReversePoly {d e : ℕ} :
    Poly (prodBits (code (d := d) (e := e)) (prodBits natBits natBits))
      (prodBits natBits natBits) pairReverse := by
  let en := prodBits natBits natBits
  let ec := code (d := d) (e := e)
  let t := Poly.fst ec en
  let x := Poly.snd ec en
  let v := x.comp (Poly.fst natBits natBits)
  let p := x.comp (Poly.snd natBits natBits)
  let c := Poly.const (prodBits ec en) natBits d
  let test := (p.pair c).comp Poly.natLt
  let old := ((t.comp (basePoly.comp PortMachine.reverseListPoly)).pair x).comp (ExpandMachine.lookupPoly d)
  let new := ((t.comp rowsPoly).pair (v.pair ((p.pair c).comp Poly.natSub))).comp (ExpandMachine.lookupPoly e)
  let out := (new.comp (Poly.fst natBits natBits)).pair
    ((c.pair (new.comp (Poly.snd natBits natBits))).comp Poly.natAdd)
  exact (test.ite old out).congr (fun _ => by simp only [Function.comp_apply,pairReverse,base,decide_eq_true_eq])

noncomputable def reversePoly {d e : ℕ} : Poly (prodBits (code (d := d) (e := e)) natBits) natBits reverse := by
  let ec := code (d := d) (e := e)
  let t := Poly.fst ec natBits
  let i := Poly.snd ec natBits
  let c := Poly.const (prodBits ec natBits) natBits (d+e)
  let x := ((i.pair c).comp Poly.natDiv).pair ((i.pair c).comp Poly.natMod)
  let r := (t.pair x).comp pairReversePoly
  exact ((r.comp (Poly.snd natBits natBits)).pair
    ((c.pair (r.comp (Poly.fst natBits natBits))).comp Poly.natMul)).comp Poly.natAdd

noncomputable def relationPoly {d e : ℕ} : Poly (prodBits (code (d := d) (e := e)) natBits) relationCode relation := by
  let ec := code (d := d) (e := e)
  let t := (Poly.fst ec natBits).comp basePoly
  let i := Poly.snd ec natBits
  let c := Poly.const (prodBits ec natBits) natBits (d+e)
  let cd := Poly.const (prodBits ec natBits) natBits d
  let v := (i.pair c).comp Poly.natDiv
  let p := (i.pair c).comp Poly.natMod
  let idx := (p.pair ((cd.pair v).comp Poly.natMul)).comp Poly.natAdd
  exact (((p.pair cd).comp Poly.natLt).ite ((t.pair idx).comp PortMachine.relationPoly)
    (Poly.const _ relationCode RegularMachine.trueRelation)).congr (fun _ => by
      simp only [Function.comp_apply,relation,base,decide_eq_true_eq])

 theorem lookup_port {n d : ℕ} (T : PortTables.Table n d) (x : Fin n × Fin d) :
    ExpandMachine.lookup d (T.reverseIndex.toList.map Fin.val,(x.1.val,x.2.val)) =
      ((PortTables.rotation T x).1.val,(PortTables.rotation T x).2.val) := by
  dsimp only [ExpandMachine.lookup]
  have hidx : x.2.val+d*x.1.val < (T.reverseIndex.toList.map Fin.val).length := by
    simpa using (PortTables.rowIndex n d x).isLt
  rw [List.getD_eq_getElem _ _ hidx,List.getElem_map]
  rfl

 theorem pairReverse_source {d e : ℕ} (T : Input d e) (v : Fin T.1) (p : Fin d ⊕ Fin e) :
    pairReverse (T,(v.val,(overlayPorts d e p).val)) =
      ((PortTables.rotation (output T).2 (v,overlayPorts d e p)).1.val,
       (PortTables.rotation (output T).2 (v,overlayPorts d e p)).2.val) := by
  change _ = ((PortTables.rotation (overlay T.2.1 T.2.2) (v,overlayPorts d e p)).1.val,
    (PortTables.rotation (overlay T.2.1 T.2.2) (v,overlayPorts d e p)).2.val)
  cases p with
  | inl p =>
    dsimp only [pairReverse]
    rw [overlayPorts_inl_val,ite_eq_left p.isLt]
    rw [lookup_port T.2.1 (v,p)]
    rw [overlay_rotation_old]
    rfl
  | inr p =>
    dsimp only [pairReverse,rows]
    rw [overlayPorts_inr_val,ite_eq_right (by omega),Nat.add_sub_cancel_left]
    rw [ExpandMachine.lookup_erase T.2.2 (v,p)]
    rw [overlay_rotation_expander]
    rfl

 theorem reverse_source {d e : ℕ} (T : Input d e) (i : Fin ((output T).1*(d+e))) :
    reverse (T,i.val) = (output T).2.reverseIndex[i].val := by
  let E := (Equiv.prodCongr (Equiv.refl (Fin T.1)) (overlayPorts d e)).trans (PortTables.rowIndex _ _)
  obtain ⟨⟨v,p⟩,rfl⟩ := E.surjective i
  have hi : ((E (v,p)).val/(d+e),(E (v,p)).val%(d+e)) = (v.val,(overlayPorts d e p).val) :=
    congrArg (fun z : Fin T.1 × Fin (d+e) => (z.1.val,z.2.val))
      ((PortTables.rowIndex _ _).symm_apply_apply (v,overlayPorts d e p))
  dsimp only [reverse]
  rw [hi,pairReverse_source]
  exact congrArg Fin.val (PortTables.rowIndex_rotation (output T).2 (v,overlayPorts d e p))

 theorem relation_source {d e : ℕ} (T : Input d e) (i : Fin ((output T).1*(d+e))) :
    relation (T,i.val) = (output T).2.relations[i] := by
  let E := (Equiv.prodCongr (Equiv.refl (Fin T.1)) (overlayPorts d e)).trans (PortTables.rowIndex _ _)
  obtain ⟨⟨v,p⟩,rfl⟩ := E.surjective i
  have hi : ((E (v,p)).val/(d+e),(E (v,p)).val%(d+e)) = (v.val,(overlayPorts d e p).val) :=
    congrArg (fun z : Fin T.1 × Fin (d+e) => (z.1.val,z.2.val))
      ((PortTables.rowIndex _ _).symm_apply_apply (v,overlayPorts d e p))
  change _ = (overlay T.2.1 T.2.2).relations[PortTables.rowIndex _ _ (v,overlayPorts d e p)]
  dsimp only [relation]
  have hv : (E (v,p)).val/(d+e) = v.val := congrArg Prod.fst hi
  have hp : (E (v,p)).val%(d+e) = (overlayPorts d e p).val := congrArg Prod.snd hi
  conv_lhs => rw [hv,hp]
  have extensionality {left right : GraphTables.RelationTable}
      (equal : ∀ first second,
        GraphTables.relationAt left first second = GraphTables.relationAt right first second) :
      left = right := by
    apply Vector.ext
    intro index index_lt
    simpa only [GraphTables.relationAt,Prod.eta,Equiv.apply_symm_apply,Fin.getElem_fin] using
      equal (GraphTables.relationIndex.symm ⟨index,index_lt⟩).1
        (GraphTables.relationIndex.symm ⟨index,index_lt⟩).2
  apply extensionality
  intro first second
  cases p with
  | inl p =>
    rw [overlayPorts_inl_val,ite_eq_left p.isLt,
      List.getD_eq_getElem _ _ (by simpa using (PortTables.rowIndex T.1 d (v,p)).isLt)]
    exact (overlay_accepts_old T.2.1 T.2.2 v p first second).symm
  | inr p =>
    rw [overlayPorts_inr_val,ite_eq_right (by omega),RegularMachine.trueRelation,GraphTables.relationAt_relationOf]
    exact (overlay_accepts_expander T.2.1 T.2.2 v p first second).symm

noncomputable def poly {d e : ℕ} : Poly (code (d := d) (e := e)) PortMachine.code output := by
  let zero : Input d e := ⟨0,
    PortTables.ofPortGraph {rot := Equiv.refl _,rot_involutive := fun _ => rfl}
      (fun _ _ _ => true) (fun _ _ _ => rfl),
    ExpanderTables.ofGraph {rot := Equiv.refl _,rot_involutive := fun _ => rfl}⟩
  exact PortMachine.materializePoly code zero output (basePoly.comp PortMachine.verticesPoly)
    reversePoly relationPoly reverse_source relation_source

end VertexCover.Machine.OverlayMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Walk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                
section

namespace VertexCover.Machine.WalkMachine
open UniqueGames.Foundations.PCP
open PoweringWalks TableMachine

abbrev State (d : ℕ) := Σ T : PortTables.Input d, Fin T.1
def step {d : ℕ} (p : Fin d) (s : State d) : State d :=
  ⟨s.1,next (PortTables.portGraph s.1.2) s.2 p⟩

def word {d : ℕ} (n : ℕ) (p : Fin n → Fin d) (s : State d) : State d :=
  ⟨s.1,wordEnd (PortTables.portGraph s.1.2) n s.2 p⟩

def edge {d : ℕ} (n : ℕ) (p : Fin (n+1) → Fin d) (k : Fin (n+1)) (s : State d) : State d × Fin d :=
  let e := edgeAt (PortTables.portGraph s.1.2) n (s.2,p) k
  (⟨s.1,e.1⟩,e.2)

 theorem relationCode_injective : Function.Injective relationCode := by
  intro a b hab
  exact Vector.toList_inj.mp hab

end VertexCover.Machine.WalkMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Address
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine

namespace FixedSearch

noncomputable def poly {α ι β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (p : α → ι → Bool) (f : α → ι → β) (z : β)
    (cp : ∀ i, Poly ea boolBits (fun a => p a i))
    (cf : ∀ i, Poly ea eb (fun a => f a i)) :
    (xs : List ι) → Poly ea eb (run p f z xs)
  | [] => Poly.const ea eb z
  | i::xs => (cp i).ite (cf i) (poly ea eb p f z cp cf xs)

end FixedSearch

namespace AddressMachine
open UniqueGames.Foundations.PCP
open PoweringLabels PoweringAddresses WalkMachine

def search {d : ℕ} (t : ℕ) (a : PaddedLabel (Fin d) t GraphTables.Label)
    (x : State d × ℕ) : GraphTables.Label :=
  FixedSearch.run (fun x w => decide ((word w.1.val w.2 x.1).2.val=x.2))
    (fun _ w => a w) 0 (allAddresses d t) x

 theorem search_decode {d : ℕ} (T : PortTables.Input d) (t : ℕ) (v : Fin T.1)
    (u : Ball (PortTables.portGraph T.2) t v) (a : PaddedLabel (Fin d) t GraphTables.Label) :
    search t a ((⟨T,v⟩ : State d),u.val.val) =
      decode (finitePortSelector (PortTables.portGraph T.2) t v) a u := by
  let p := fun w : PortWords (Fin d) t =>
    (wordToBall (PortTables.portGraph T.2) t v w).val = u.val
  have h : ∃ w ∈ allAddresses d t, p w := by
    obtain ⟨w,hw⟩ := wordToBall_surjective (PortTables.portGraph T.2) t v u
    exact ⟨w,mem_allAddresses d t w,congrArg Subtype.val hw⟩
  have hs := FixedSearch.eq_scan p a 0 (allAddresses d t) h
  change _ = a (scanWitness p (allAddresses d t) h).val
  rw [← hs]
  unfold search
  generalize allAddresses d t = xs
  induction xs with
  | nil => rfl
  | cons w xs ih =>
    dsimp only [FixedSearch.run]
    have hp : decide ((word w.1.val w.2 (⟨T,v⟩ : State d)).2.val = u.val.val) = decide (p w) := by
      simp only [p,word,wordToBall,Fin.val_inj]
      rfl
    exact if_congr (Iff.of_eq (congrArg (fun c : Bool => c=true) hp))
      rfl ih

end AddressMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ParseClause
attribute [-simp] _root_.OAI.UniqueGames.BinaryFormula.compactLiteral_positive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                
section

namespace VertexCover.Machine

noncomputable def Poly.optionMapWith {α β γ : Type} (ea : α → List Bool)
    (eb : β → List Bool) (ec : γ → List Bool) (b₀ : β)
    {f : α × β → γ} (cf : Poly (prodBits ea eb) ec f) :
    Poly (prodBits ea (optionBits eb)) (optionBits ec)
      (fun p : α × Option β => p.2.map (fun b => f (p.1,b))) := by
  let a := Poly.fst ea (optionBits eb)
  let b := Poly.snd ea (optionBits eb)
  let test := b.comp (Poly.isSome eb)
  let result := ((a.pair (b.comp (Poly.getD eb b₀))).comp cf).comp (Poly.some ec)
  exact (test.ite result (Poly.const _ (optionBits ec) none)).congr (fun ⟨a,b⟩ => by cases b <;> rfl)

namespace Parser

noncomputable def seqPoly {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) (b₀ : β) {pa : P α} {pb : P β}
    (ca : Poly id (optionBits (prodBits ea id)) pa)
    (cb : Poly id (optionBits (prodBits eb id)) pb) :
    Poly id (optionBits (prodBits (prodBits ea eb) id)) (seq pa pb) := by
  let e := prodBits eb id
  let a := Poly.fst ea e
  let b := (Poly.snd ea e).comp (Poly.fst eb id)
  let rest := (Poly.snd ea e).comp (Poly.snd eb id)
  let collect := (a.pair b).pair rest
  let step := (((Poly.fst ea id).pair ((Poly.snd ea id).comp cb)).comp
    (Poly.optionMapWith ea e (prodBits (prodBits ea eb) id) (b₀,[]) collect))
  exact (ca.comp (Poly.optionBind (prodBits ea id) (prodBits (prodBits ea eb) id)
    (a₀,[]) step)).congr (fun input => by
      cases ha : pa input with
      | none => simp [seq,ha]
      | some a => cases hb : pb a.2 <;> simp [seq,ha,hb])
end Parser

namespace FormulaParser
open UniqueGames.BinaryFormula UniqueGames.BinaryEncoding

noncomputable def literalPoly : Poly id (optionBits (prodBits literalCode id)) parseLiteral := by
  let e := prodBits Nat.bits id
  let sign := Poly.fst boolBits e
  let n := (Poly.snd boolBits e).comp (Poly.fst Nat.bits id)
  let rest := (Poly.snd boolBits e).comp (Poly.snd Nat.bits id)
  let mkLit : Poly (prodBits boolBits e) literalCode
      (fun p : Bool × (ℕ × List Bool) => ⟨p.2.1,p.1⟩) :=
    (sign.pair n).encodeCongr id (fun _ => rfl) (fun _ => rfl)
  let collect := mkLit.pair rest
  let parsed := ((Poly.headD false).pair (Poly.tail.comp NameParser.poly)).comp
    (Poly.optionMapWith boolBits e (prodBits literalCode id) (0,[]) collect)
  exact (Poly.isEmpty.ite (Poly.const id (optionBits (prodBits literalCode id)) none) parsed).congr (fun input => by
      cases input with
      | nil => rfl
      | cons b bs => cases h : parseName bs <;> simp [parseLiteral,h])

noncomputable def clausePoly : Poly id (optionBits (prodBits clauseCode id)) parseClause := by
  let c₁ := Parser.seqPoly literalCode literalCode literalDefault literalDefault literalPoly literalPoly
  let c₂ := Parser.seqPoly (prodBits literalCode literalCode) literalCode
    (literalDefault,literalDefault) literalDefault c₁ literalPoly
  refine c₂.encodeCongr id (fun _ => rfl) ?_
  intro input
  simp only [Parser.seq,parseClause,id_eq]
  cases h₁ : parseLiteral input with
  | none => rfl
  | some a =>
    rcases a with ⟨a,rest⟩
    cases h₂ : parseLiteral rest with
    | none => simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some, h₂, Option.bind_none, optionBits]
    | some b =>
      rcases b with ⟨b,rest₂⟩
      cases h₃ : parseLiteral rest₂ with
      | none => simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some, h₂, h₃, Option.bind_none, optionBits]
      | some c =>
        rcases c with ⟨c,rest₃⟩
        simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some, h₂, h₃]
        rfl

end FormulaParser
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_DenseParse
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.dartNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.VertexCover.ClauseProjection.instDecidableConsistent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                               
section

namespace VertexCover.Machine
namespace FormulaParser
open UniqueGames.BinaryFormula
open UniqueGames.Foundations

def targetClauseData {n : ℕ} (clause : Target.Clause n) : Triple (Bool × ℕ) :=
  ((targetLiteralData clause[0],targetLiteralData clause[1]),targetLiteralData clause[2])
def targetData (F : Target.Formula) : FormulaData :=
  (F.variables,F.clauses.map targetClauseData)
def targetCode (F : Target.Formula) : List Bool := dataCode (targetData F)

noncomputable def clauseGetPoly (i : Fin 3) : Poly clauseCode literalCode (fun clause => clause[i]) := by
  by_cases h₀ : i = 0
  · subst i
    exact (((Poly.fst (prodBits literalCode literalCode) literalCode).comp
      (Poly.fst literalCode literalCode)).encodeCongr (fun clause => ((clause[0],clause[1]),clause[2]))
      (fun _ => rfl) (fun _ => rfl))
  · by_cases h₁ : i = 1
    · subst i
      exact (((Poly.fst (prodBits literalCode literalCode) literalCode).comp
      (Poly.snd literalCode literalCode)).encodeCongr (fun clause => ((clause[0],clause[1]),clause[2]))
      (fun _ => rfl) (fun _ => rfl))
    · have h₂ : i = 2 := by omega
      subst i
      exact (Poly.snd (prodBits literalCode literalCode) literalCode).encodeCongr
        (fun clause => ((clause[0],clause[1]),clause[2])) (fun _ => rfl) (fun _ => rfl)

noncomputable def clauseNamesPoly : Poly clauseCode (listBits Nat.bits) clauseNames := by
  let n₀ := (clauseGetPoly 0).comp literalNamePoly
  let n₁ := (clauseGetPoly 1).comp literalNamePoly
  let n₂ := (clauseGetPoly 2).comp literalNamePoly
  let empty := Poly.const clauseCode (listBits Nat.bits) []
  let c₂ := (n₂.pair empty).comp (Poly.listCons Nat.bits)
  let c₁ := (n₁.pair c₂).comp (Poly.listCons Nat.bits)
  exact ((n₀.pair c₁).comp (Poly.listCons Nat.bits)).congr (fun _ => rfl)

noncomputable def sourceNamesPoly : Poly formulaCode (listBits Nat.bits) sourceNames :=
  (Poly.listFlatMap clauseCode Nat.bits clauseDefault 0 clauseNamesPoly).encodeCongr
    Formula.clauses (fun _ => rfl) (fun _ => rfl)

noncomputable def activeNamesPoly : Poly formulaCode (listBits Nat.bits) activeNames :=
  sourceNamesPoly.comp (Poly.eraseDups Nat.bits 0 Poly.bitsNatEq)

noncomputable def compactLiteralPoly : Poly (prodBits (listBits Nat.bits) literalCode)
    unaryLiteralCode compactDataLiteral := by
  let names := Poly.fst (listBits Nat.bits) literalCode
  let lit := Poly.snd (listBits Nat.bits) literalCode
  let idx := (((lit.comp literalNamePoly).pair names).comp (Poly.listIdxOf Nat.bits 0 Poly.bitsNatEq))
  exact ((lit.comp literalSignPoly).pair idx).congr (fun _ => rfl)

noncomputable def compactClausePoly : Poly (prodBits (listBits Nat.bits) clauseCode)
    unaryClauseCode compactDataClause := by
  let names := Poly.fst (listBits Nat.bits) clauseCode
  let clause := Poly.snd (listBits Nat.bits) clauseCode
  let lit (i : Fin 3) := (names.pair (clause.comp (clauseGetPoly i))).comp compactLiteralPoly
  exact ((lit 0).pair (lit 1)).pair (lit 2)

noncomputable def denseDataPoly : Poly formulaCode dataCode denseData := by
  let names := activeNamesPoly
  let count := names.comp (Poly.listLength Nat.bits 0)
  let clauses : Poly formulaCode (listBits clauseCode) Formula.clauses :=
    (Poly.identity (listBits clauseCode)).encodeCongr Formula.clauses (fun _ => rfl) (fun _ => rfl)
  let cs := (names.pair clauses).comp (Poly.listMapWith (listBits Nat.bits) clauseCode
    unaryClauseCode [] clauseDefault (((false,0),(false,0)),(false,0)) compactClausePoly)
  exact count.pair cs

 theorem denseData_eq (F : Formula) : denseData F = targetData (dense F) := by
  apply Prod.ext
  · rfl
  · simp only [denseData,targetData,dense,compactClauses,List.map_map]
    change F.clauses.map (fun clause => compactDataClause (activeNames F,clause)) =
      F.clauses.attach.map (fun clause => compactDataClause (activeNames F,clause.val))
    exact List.attach_map_val.symm

noncomputable def densePoly : Poly formulaCode targetCode dense :=
  denseDataPoly.encodeCongr id (fun _ => rfl) (fun F => by
    change dataCode (denseData F) = dataCode (targetData (dense F))
    rw [denseData_eq])

end FormulaParser
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_ReductionSound
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.ClauseProjection
open UniqueGames.Foundations
open LabelCover
noncomputable section

theorem baseGap_pos : 0 < baseGap := by
  exact div_pos (Rat.cast_pos.mpr PCP.PCPIteration.finalClauseGap_positive) (by norm_num)

def repetitionBase : ℝ := 1 - baseGap ^ 3 / 6000

end
end VertexCover.ClauseProjection


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ParseFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine.FormulaParser
open UniqueGames.BinaryFormula UniqueGames.BinaryEncoding

noncomputable def oneStepPoly : Poly accCode stateCode oneStep := by
  let out := Poly.fst (listBits clauseCode) id
  let bs := Poly.snd (listBits clauseCode) id
  let tail := bs.comp Poly.tail
  let parsed := tail.comp clausePoly
  let e := prodBits clauseCode id
  let cs := Poly.fst (listBits clauseCode) e
  let c := (Poly.snd (listBits clauseCode) e).comp (Poly.fst clauseCode id)
  let rest := (Poly.snd (listBits clauseCode) e).comp (Poly.snd clauseCode id)
  let collect := ((c.pair cs).comp (Poly.listCons clauseCode)).pair rest
  let data := (out.pair parsed).comp
    (Poly.optionMapWith (listBits clauseCode) e accCode (clauseDefault,[]) collect)
  let yes := (parsed.comp (Poly.isSome e)).pair data
  let no := (Poly.const accCode boolBits false).pair ((out.pair tail).comp (Poly.some accCode))
  let nonempty := (bs.comp (Poly.headD false)).ite yes no
  exact ((bs.comp Poly.isEmpty).ite (Poly.const accCode stateCode (false,none)) nonempty).congr (fun _ => rfl)

noncomputable def stepPoly : Poly stateCode stateCode step :=
  ((Poly.fst boolBits (optionBits accCode)).ite
    (((Poly.snd boolBits (optionBits accCode)).comp (Poly.getD accCode ([],[]))).comp oneStepPoly)
    (Poly.identity stateCode)).congr (fun _ => rfl)

noncomputable def runPoly : Poly (prodBits natBits stateCode) stateCode
    (fun p : ℕ × State => Iterate.run step p.1 p.2) :=
  Poly.iterate stateCode stepPoly (100*(Polynomial.X+1)) (by
    intro n s k l h
    have hs := (size_le_budget (Iterate.run step k s)).trans (run_budget k s)
    have hb := budget_le_size s
    simp only [prodBits,pairBits_length,natBits_length,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] at hs hb ⊢
    omega)

noncomputable def observePoly : Poly stateCode (optionBits accCode) observe :=
  ((Poly.fst boolBits (optionBits accCode)).ite
    (Poly.const stateCode (optionBits accCode) none) (Poly.snd boolBits (optionBits accCode))).congr (fun _ => rfl)

noncomputable def clausesPoly : Poly (prodBits natBits id) (optionBits accCode)
    (fun p : ℕ × List Bool => parseClauses p.1 p.2) := by
  let e := prodBits natBits id
  let clock := Poly.fst natBits id
  let empty := Poly.const e (listBits clauseCode) []
  let initial := (Poly.const e boolBits true).pair
    (((empty.pair (Poly.snd natBits id)).comp (Poly.some accCode)))
  let running := ((clock.pair initial).comp runPoly).comp observePoly
  let reverse := ((Poly.fst (listBits clauseCode) id).comp
    (Poly.listReverse clauseCode clauseDefault)).pair (Poly.snd (listBits clauseCode) id)
  let c := running.comp (Poly.optionMap accCode accCode ([],[]) reverse)
  refine c.congr ?_
  intro ⟨n,bs⟩
  change (observe (Iterate.run step n (true,some ([],bs)))).map
    (fun p => (p.1.reverse,p.2)) = parseClauses n bs
  rw [observe_run]
  cases h : parseClauses n bs <;> simp

noncomputable def decodePoly : Poly id (optionBits formulaCode) decodeFormula := by
  let parser := ((rawLength.comp Poly.natSucc).pair (Poly.identity id)).comp clausesPoly
  let done := (Poly.snd (listBits clauseCode) id).comp Poly.isEmpty
  let form : Poly accCode formulaCode (fun p : Acc => ⟨p.1⟩) :=
    (Poly.fst (listBits clauseCode) id).encodeCongr id (fun _ => rfl) (fun _ => rfl)
  let finish := done.ite (form.comp (Poly.some formulaCode))
    (Poly.const accCode (optionBits formulaCode) none)
  exact (parser.comp (Poly.optionBind accCode formulaCode ([],[]) finish)).congr (fun bs => by
    change ((parseClauses (bs.length+1) bs).bind (fun a =>
      if a.2.isEmpty then some (⟨a.1⟩ : Formula) else none)) = decodeFormula bs
    cases h : parseClauses (bs.length+1) bs with
    | none => simp [decodeFormula,h]
    | some p => rcases p with ⟨cs,rest⟩; cases rest <;> simp [decodeFormula,h])

noncomputable def inputFormulaPoly : Poly id formulaCode VertexCover.ClauseProjection.inputFormula :=
  decodePoly.comp (Poly.getD formulaCode VertexCover.ClauseProjection.falseFormula)

end VertexCover.Machine.FormulaParser
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Serialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                  
section

namespace VertexCover.Machine
open UniqueGames.Foundations.Complexity

noncomputable def Poly.rawFlatten : Poly (listBits (id : List Bool → List Bool)) id List.flatten := by
  let c := Poly.foldGrowing id id ([] : List Bool) Poly.append 1 (by
    intro out xs
    simp only [id_eq,List.length_append,Nat.one_mul]
    omega)
  let input := (Poly.const (listBits id) id ([] : List Bool)).pair (Poly.identity (listBits id))
  exact (input.comp c).congr (fun xs => by
    change xs.foldl (fun out xs => out++xs) [] = xs.flatten
    have h (xs : List (List Bool)) (out : List Bool) :
        xs.foldl (fun out xs => out++xs) out = out++xs.flatten := by
      induction xs generalizing out with
      | nil => simp
      | cons a xs ih => simp [List.foldl_cons,ih,List.append_assoc]
    simpa using h xs [])

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Generic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

noncomputable def Poly.rawBooleans : Poly (listBits boolBits) id (id : List Bool → List Bool) := by
  let bit : Poly boolBits id (fun b => [b]) :=
    (Poly.identity boolBits).encodeCongr id (fun _ => rfl) (fun _ => rfl)
  exact ((Poly.listMap boolBits id false [] bit).comp Poly.rawFlatten).congr (fun xs => by induction xs with
    | nil => rfl
    | cons b bs ih => simpa only [Function.comp_apply,id_eq,List.map_cons,List.flatten_cons,List.singleton_append] using congrArg (List.cons b) ih)

noncomputable def Poly.vectorOfFn {α : Type} (ea : α → List Bool) (n : ℕ)
    (f : α → Fin n → Bool) (cf : ∀ i, Poly ea boolBits (fun a => f a i)) :
    Poly ea (fun v : Vector Bool n => v.toList) (fun a => Vector.ofFn (f a)) := by
  let c := (Poly.fixedList ea boolBits f cf (List.ofFn id)).comp Poly.rawBooleans
  exact c.encodeCongr id (fun _ => rfl) (fun a => by
    simp only [Function.comp_apply,id_eq,List.map_ofFn,Function.comp_def]
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂; simp)

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_AlphabetFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                  
section

namespace VertexCover.Machine.AlphabetMachine
open UniqueGames.Foundations.PCP
open AlphabetTable
open Enumeration

def blockCount (q : ℕ) : ℕ := localCount q * 12
def blockEquiv (q : ℕ) : Local q ≃ Fin (blockCount q) :=
  (productEquiv (productEquiv (localEventEquiv q) (Equiv.refl (Fin 6))) boolEquiv).trans
    (finCongr (by simp [blockCount,Nat.mul_assoc]))
 theorem block_pos (q : ℕ) : 0<blockCount q := by
  unfold blockCount localCount fiveTapeCount pairTapeCount tapeCount
  positivity
 theorem block_val (q : ℕ) (l : Local q) :
    (blockEquiv q l).val = (localEventEquiv q l.1.1).val*12 + l.1.2.val*2+bitValue l.2 := by
  change (boolEquiv l.2).val+2*(l.1.2.val+6*(localEventEquiv q l.1.1).val)=_
  rw [boolEquiv_val]
  omega
 theorem dart_block_val {q m : ℕ} (e : Fin m) (l : Local q) :
    (dartEquiv m q (((e,l.1.1),l.1.2),l.2)).val = (blockEquiv q l).val+blockCount q*e.val := by
  rw [dartEquiv_val,eventEquiv_val,block_val]
  unfold blockCount
  ring

end VertexCover.Machine.AlphabetMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Approximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                             
section

namespace VertexCover
open Machine

noncomputable def decisionOfGap {α : ℝ} (hα : 1 ≤ α) (m : ℕ) (hm : 4 ≤ m)
    (hsep : α*(1/2+1/(m:ℝ)) < 1-1/(m:ℝ))
    (R : GapReduction m) (A : Approximation α) : ThreeSATDecision := by
  let c : Machine.Poly id boolBits (fun input => A.test m (R.construct input)) :=
    (⟨R.computation,R.finiteAlphabet⟩ : Machine.Poly id ExplicitGraph.bits R.construct).comp (A.testPoly m)
  refine ⟨fun input => A.test m (R.construct input),c.computation,c.finiteAlphabet,?_⟩
  intro input
  let G := R.construct input
  have hm1 : 1 ≤ m := by omega
  change decide (m*(A.run G).length < (m-1)*G.n)=true ↔ ThreeSAT input
  rw [decide_eq_true_eq,rational_threshold m G.n (A.run G).length hm1]
  constructor
  · intro hout
    by_contra hno
    have hlow := R.soundness input hno
    have hcover := A.coverNumber_le_length G
    have hc : (G.coverNumber:ℝ) ≤ (A.run G).length := by exact_mod_cast hcover
    exact (not_lt_of_ge hc) (lt_trans hout hlow)
  · intro hyes
    have hhigh := R.completeness input hyes
    have hcp : (0:ℝ) ≤ G.coverNumber := Nat.cast_nonneg _
    have hn : (0:ℝ) < G.n := by
      have hn0 : G.n ≠ 0 := by
        intro hz
        change (G.coverNumber:ℝ) < _ at hhigh
        rw [hz,Nat.cast_zero,mul_zero] at hhigh
        exact (not_lt_of_ge hcp) hhigh
      exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    have hαp : 0 < α := lt_of_lt_of_le zero_lt_one hα
    have hc := (A.quality G).trans_lt (mul_lt_mul_of_pos_left hhigh hαp)
    have hs := mul_lt_mul_of_pos_right hsep hn
    change ((A.run G).length : ℝ) < _
    exact hc.trans (by simpa only [mul_assoc] using hs)

end VertexCover
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_BinaryOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine
namespace BinaryOutput
noncomputable def bodyPoly : Poly enc (flagBits enc) body := by
  let n := Poly.fst natBits (id : List Bool → List Bool)
  let bs := Poly.snd natBits (id : List Bool → List Bool)
  let test := n.comp Poly.natZero
  let bit := (((n.pair (Poly.const enc natBits 2)).comp Poly.natMod).pair
    (Poly.const enc natBits 1)).comp Poly.natEq
  let out := bit.ite (bs.comp (Poly.cons true)) (bs.comp (Poly.cons false))
  let next := ((n.pair (Poly.const enc natBits 2)).comp Poly.natDiv).pair out
  exact ((test.comp (Poly.bool Bool.not)).flagPair (test.ite (Poly.identity enc) next)).congr
    (fun p => by
      by_cases h : p.1=0
      · simp [Function.comp_apply,body,h]
      · simp only [Function.comp_apply,body,h,ite_false,decide_false,Bool.not_false]
        congr 2
        by_cases hb : p.1%2=1 <;> simp [hb])
 theorem run (n : ℕ) (xs : List Bool) (B : ℕ) (hsize : (enc (n,xs)).length ≤ B) :
    ∃ k, k≤n+1 ∧ BoundedRun enc body B (n,xs) (result (n,xs)) k := by
  induction n using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      refine ⟨1,le_rfl,?_⟩
      simpa [body,result] using
        (BoundedRun.stop (e := enc) (body := body) (0,xs) hsize (by simp [body]))
    · have hlt := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1<2)
      have hs : (enc (n/2,decide (n%2=1)::xs)).length ≤ B := by
        simp only [enc,prodBits,pairBits_length,natBits_length,id_eq,List.length_cons] at hsize ⊢
        omega
      obtain ⟨k,hk,hr⟩ := ih (n/2) hlt _ hs
      have he : result (n/2,decide (n%2=1)::xs)=result (n,xs) := by
        simp only [result,bits_step n hn,List.reverse_cons,List.append_assoc,List.singleton_append]
      rw [he] at hr
      refine ⟨k+1,by omega,.next _ _ k hsize (by simp [body,hn]) ?_⟩
      simpa only [body,hn,ite_false] using hr
noncomputable def poly : Poly enc enc result :=
  bodyPoly.loop result Polynomial.X (Polynomial.X+1) (by
    intro ⟨n,xs⟩
    obtain ⟨k,hk,hr⟩ := run n xs (enc (n,xs)).length le_rfl
    refine ⟨k,?_,by simpa only [Polynomial.eval_X] using hr⟩
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,
      enc,prodBits,pairBits_length,natBits_length,id_eq]
    omega)
end BinaryOutput
noncomputable def Poly.rawReverse : Poly id id (List.reverse : List Bool → List Bool) :=
  ((Poly.rawToList.comp (Poly.listReverse boolBits false)).comp Poly.rawBooleans).congr (fun _ => rfl)
noncomputable def Poly.binaryDigits : Poly natBits id Nat.bits :=
  (((((Poly.identity natBits).pair (Poly.const natBits id ([] : List Bool))).comp BinaryOutput.poly).comp
    (Poly.snd natBits (id : List Bool → List Bool))).comp Poly.rawReverse).congr
      (fun n => by simp only [Function.comp_apply,BinaryOutput.result,List.append_nil,List.reverse_reverse,id_eq])
noncomputable def Poly.nameBits : Poly natBits id UniqueGames.BinaryEncoding.nameBits :=
  Poly.binaryDigits.comp Poly.binaryFrame
noncomputable def Poly.nameList : Poly (listBits natBits) id
    (fun xs => xs.flatMap UniqueGames.BinaryEncoding.nameBits) :=
  ((Poly.listMap natBits id 0 [] Poly.nameBits).comp Poly.rawFlatten).congr (fun xs => by
    simp only [Function.comp_apply]
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.map_cons,List.flatten_cons,List.flatMap_cons,ih])
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_FinalCNFBase
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instDecidableConsistent
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGames.Foundations.PCP.AlphabetRetraction.edgeSatisfied_pullback _root_.OAI.UniqueGames.Foundations.PCP.AlphabetRetraction.rejectionCount_pullback _root_.OAI.UniqueGames.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGames.Foundations.PCP.FiniteGraph.Bundle.ofGraph_graph _root_.OAI.UniqueGames.Foundations.PCP.FiniteGraph.Bundle.ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.FiniteGraph.Bundle.ofGraph_size _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine.FinalCNFMachine
open UniqueGames.Foundations
open PCP PCP.VerifierToCNF PCP.GraphTables Target FormulaParser TableMachine

def eraseClause {n : ℕ} (f : Fin n → ℕ) (cl : Clause n) : Triple (Bool × ℕ) :=
  ((eraseLiteral f cl[0],eraseLiteral f cl[1]),eraseLiteral f cl[2])
 theorem erase_split {n : ℕ} (f : Fin n → ℕ) (ls : List (Literal n)) (ys : List (Fin n)) :
    (splitLong ls ys).map (eraseClause f) = splitData (ls.map (eraseLiteral f)) (ys.map f) := by
  induction ys generalizing ls with
  | nil =>
    cases ls with
    | nil => rfl
    | cons a ls =>
      cases ls with
      | nil => rfl
      | cons b ls =>
        cases ls with
        | nil => rfl
        | cons c ls => cases ls <;> rfl
  | cons y ys ih =>
    cases ls with
    | nil => rfl
    | cons a ls =>
      cases ls with
      | nil => rfl
      | cons b rest =>
        simpa [splitLong,eraseClause,eraseLiteral,splitData] using
          congrArg (List.cons ((eraseLiteral f a,eraseLiteral f b),(true,f y)))
            (ih (⟨y,false⟩::rest))

 theorem erase_block {q : ℕ} (V W : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (e' : Fin W.events) (p : PatternIndex q)
    (f : Fin (outputVariables V) → ℕ) (g : Fin (outputVariables W) → ℕ)
    (hquery : ∀ i, f (oldIndex V (V.query e i)) = g (oldIndex W (W.query e' i)))
    (hfresh : ∀ j, f (freshIndex V e p j) = g (freshIndex W e' p j))
    (haccept : V.accepts e (patternAt q p) = W.accepts e' (patternAt q p)) :
    (block V hq e p).map (eraseClause f) = (block W hq e' p).map (eraseClause g) := by
  unfold block
  rw [haccept]
  split
  · rw [List.map_replicate,List.map_replicate]
    congr 1
    simp [tautology,eraseClause,eraseLiteral,hquery]
  · rw [erase_split,erase_split]
    congr 1
    · simp only [forbiddenClause,List.map_ofFn]
      congr 1
      funext i
      exact Prod.ext rfl (hquery i)
    · simp only [auxiliaryNames,List.map_ofFn]
      congr 1
      funext j
      exact hfresh j

theorem erase_event {q : ℕ} (V W : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (e' : Fin W.events)
    (f : Fin (outputVariables V) → ℕ) (g : Fin (outputVariables W) → ℕ)
    (hquery : ∀ i, f (oldIndex V (V.query e i)) = g (oldIndex W (W.query e' i)))
    (hfresh : ∀ p j, f (freshIndex V e p j) = g (freshIndex W e' p j))
    (haccept : ∀ p, V.accepts e (patternAt q p) = W.accepts e' (patternAt q p)) :
    (eventBlock V hq e).map (eraseClause f) = (eventBlock W hq e').map (eraseClause g) := by
  simp only [eventBlock,List.map_flatMap]
  apply List.flatMap_congr
  intro p _
  exact erase_block V W hq e e' p f g hquery (hfresh p) (haccept p)

def localVerifier (r : RelationTable) : FiniteVerifier 12 where
  «variables» := 12
  events := 1
  query := fun _ i => i
  accepts := fun _ bits => r[Complexity.FinalCNFPattern.relationAddress bits]
def skeleton (r : RelationTable) : List (Triple (Bool × ℕ)) :=
  (eventBlock (localVerifier r) (by decide) (0 : Fin 1)).map (eraseClause Fin.val)

def queryName (p : GraphTables.Table × ℕ) (i : Fin 12) : ℕ :=
  let rows := (tableData p.1).2
  let row := rows.getD p.2 rowDefault
  if i.val<6 then 6*row.1.1+i.val
  else 6*(rows.getD row.1.2 rowDefault).1.1+(i.val-6)

def rename (p : GraphTables.Table × ℕ) (j : ℕ) : ℕ :=
  if h : j<12 then queryName p ⟨j,h⟩
  else p.1.vertices*6+p.2*((patterns 12).length*9)+(j-12)
def renameLiteral (p : (GraphTables.Table × ℕ) × (Bool × ℕ)) : Bool × ℕ :=
  (p.2.1,rename p.1 p.2.2)
def renameClause (p : (GraphTables.Table × ℕ) × Triple (Bool × ℕ)) : Triple (Bool × ℕ) :=
  ((renameLiteral (p.1,p.2.1.1),renameLiteral (p.1,p.2.1.2)),renameLiteral (p.1,p.2.2))
theorem rename_erase {n : ℕ} (p : Table × ℕ) (cl : Clause n) :
    renameClause (p,eraseClause Fin.val cl) = eraseClause (rename p ∘ Fin.val) cl := rfl

def eventData (p : GraphTables.Table × ℕ) : List (Triple (Bool × ℕ)) :=
  (skeleton (((tableData p.1).2.getD p.2 rowDefault).2)).map (fun c => renameClause (p,c))
def output (T : GraphTables.Table) : FormulaData :=
  (T.vertices*6+T.darts*36864,(List.range T.darts).flatMap (fun e => eventData (T,e)))

 theorem queryName_correct (T : GraphTables.Table) (e : Fin T.darts) (i : Fin 12) :
    queryName (T,e.val) i = ((Complexity.FinalCNFPattern.tableVerifier T).query e i).val := by
  refine Fin.addCases (m := 6) (n := 6) ?_ ?_ i
  · intro j
    have hj := j.isLt
    simp only [queryName,lookup_valid,Fin.val_castAdd,ite_eq_left hj]
    rw [Fin.addCases_left]
    simp [FinalBooleanVerifier.bitIndex,finProdFinEquiv,rowData,Nat.add_comm]
  · intro j
    have hj : ¬6+j.val<6 := by omega
    simp only [queryName,lookup_valid,Fin.val_natAdd,ite_eq_right hj]
    change 6*((tableData T).2.getD T.rows[e].reverseIndex.val rowDefault).1.1+(6+j.val-6) = _
    rw [lookup_valid]
    rw [Fin.addCases_right]
    simp [FinalBooleanVerifier.bitIndex,finProdFinEquiv,rowData,Nat.add_comm,
      ConstraintGraph.head,Complexity.FinalCNFPattern.tableGraph]
    rfl

end VertexCover.Machine.FinalCNFMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_InitialTable
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine
open UniqueGames.Foundations
open PCP PCP.GraphTables
open FormulaParser TableMachine

namespace InitialTable

def accepts (s : Signs) (slot : Fin 3) (a b : InitialGraph.Label) : Bool :=
  InitialGraph.variableValid b &&
    (((PCP.literalValue s.1.1 a.1 || PCP.literalValue s.1.2 a.2.1) ||
      PCP.literalValue s.2 a.2.2) &&
      decide ((if slot=0 then a.1 else if slot=1 then a.2.1 else a.2.2) = b.1))

noncomputable def signsPoly : Poly unaryClauseCode signsCode signs := by
  let ab := Poly.fst (prodBits unaryLiteralCode unaryLiteralCode) unaryLiteralCode
  let a := (ab.comp (Poly.fst unaryLiteralCode unaryLiteralCode)).comp (Poly.fst boolBits natBits)
  let b := (ab.comp (Poly.snd unaryLiteralCode unaryLiteralCode)).comp (Poly.fst boolBits natBits)
  let c := (Poly.snd (prodBits unaryLiteralCode unaryLiteralCode) unaryLiteralCode).comp (Poly.fst boolBits natBits)
  exact (a.pair b).pair c

noncomputable def litPoly : Poly (prodBits unaryClauseCode (finCode (n := 3))) unaryLiteralCode
    (fun p : ClauseData × Fin 3 => lit p.1 p.2) := by
  let cs := Poly.fst unaryClauseCode (finCode (n := 3))
  let slot := Poly.snd unaryClauseCode (finCode (n := 3))
  let test (i : Fin 3) := slot.comp (Poly.finite finCode boolBits (finCode_injective 3) (fun j => decide (j=i)))
  let ab := cs.comp (Poly.fst (prodBits unaryLiteralCode unaryLiteralCode) unaryLiteralCode)
  let a := ab.comp (Poly.fst unaryLiteralCode unaryLiteralCode)
  let b := ab.comp (Poly.snd unaryLiteralCode unaryLiteralCode)
  let c := cs.comp (Poly.snd (prodBits unaryLiteralCode unaryLiteralCode) unaryLiteralCode)
  exact ((test 0).ite a ((test 1).ite b c)).congr (by intro p; simp only [Function.comp_apply,lit,decide_eq_true_eq])

end InitialTable
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_FinalCNF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                    
section

namespace VertexCover.Machine.FinalCNFMachine
open UniqueGames.Foundations
open PCP PCP.GraphTables FormulaParser TableMachine
noncomputable def skeletonPoly : Poly relationCode (listBits unaryClauseCode) skeleton := by
  letI := AlphabetMachine.relationFintype 64
  exact Poly.finite relationCode _ (fun _ _ h => Vector.toList_inj.mp h) skeleton
end VertexCover.Machine.FinalCNFMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_LCData
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                           
section

namespace VertexCover.Machine

noncomputable def finiteCode (α : Type) [Fintype α] (a : α) : List Bool :=
  finCode (Fintype.equivFin α a)
theorem finiteCode_injective (α : Type) [Fintype α] : Function.Injective (finiteCode α) :=
  (finCode_injective _).comp (Fintype.equivFin α).injective

namespace FixedLC
variable {a b : ℕ}
noncomputable def mapCode : Map a b → List Bool := finiteCode (Map a b)
noncomputable def rowCode : Row a b → List Bool := prodBits (prodBits natBits natBits) mapCode
noncomputable def dataCode : Data a b → List Bool := prodBits natBits (prodBits natBits (listBits rowCode))
noncomputable def code (I : FixedLC a b) : List Bool := dataCode I.data
noncomputable def uPoly : Poly (code (a := a) (b := b)) natBits FixedLC.u :=
  (Poly.fst natBits (prodBits natBits (listBits rowCode))).encodeCongr data (fun _ => rfl) (fun _ => rfl)
noncomputable def restPoly : Poly (code (a := a) (b := b)) (prodBits natBits (listBits rowCode))
    (fun I => I.data.2) :=
  (Poly.snd natBits (prodBits natBits (listBits rowCode))).encodeCongr data (fun _ => rfl) (fun _ => rfl)
noncomputable def vPoly : Poly (code (a := a) (b := b)) natBits FixedLC.v :=
  restPoly.comp (Poly.fst natBits (listBits rowCode))
noncomputable def rowsPoly : Poly (code (a := a) (b := b)) (listBits rowCode) (fun I => I.data.2.2) :=
  restPoly.comp (Poly.snd natBits (listBits rowCode))
noncomputable def MPoly (hb : 0<b) : Poly (code (a := a) (b := b)) natBits FixedLC.M :=
  (rowsPoly.comp (Poly.listLength rowCode (rowDefault hb))).congr (fun I => by simp [data])
noncomputable def lookupPoly (hb : 0<b) :
    Poly (prodBits (code (a := a) (b := b)) natBits) rowCode (lookup hb) :=
  (((Poly.snd code natBits).pair ((Poly.fst code natBits).comp rowsPoly)).comp
    (Poly.listGetD rowCode (rowDefault hb))).congr (fun _ => by
      simp only [Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop]
      rfl)
noncomputable def leftPoly (hb : 0<b) :
    Poly (prodBits (code (a := a) (b := b)) natBits) natBits (fun p => (lookup hb p).1.1) :=
  (lookupPoly hb).comp ((Poly.fst (prodBits natBits natBits) mapCode).comp (Poly.fst natBits natBits))
noncomputable def rightPoly (hb : 0<b) :
    Poly (prodBits (code (a := a) (b := b)) natBits) natBits (fun p => (lookup hb p).1.2) :=
  (lookupPoly hb).comp ((Poly.fst (prodBits natBits natBits) mapCode).comp (Poly.snd natBits natBits))

noncomputable def materializePoly {α : Type} (ea : α → List Bool) (a₀ : α)
    (Q : α → FixedLC a b) (hb : 0<b) {r : α × ℕ → Row a b}
    (cu : Poly ea natBits (fun x => (Q x).u))
    (cv : Poly ea natBits (fun x => (Q x).v))
    (cm : Poly ea natBits (fun x => (Q x).M))
    (cr : Poly (prodBits ea natBits) rowCode r)
    (hr : ∀ x (e : Fin (Q x).M), r (x,e.val) = (((Q x).left e |>.val,(Q x).right e |>.val),(Q x).projection e)) :
    Poly ea code Q := by
  let rows := Poly.tabulate ea rowCode a₀ (rowDefault hb) cm cr
  have he (x : α) : (List.range (Q x).M).map (fun e => r (x,e)) = (Q x).data.2.2 := by
    apply List.ext_getElem
    · simp [data]
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_range,data,List.getElem_ofFn]
      exact hr x ⟨i,by simpa using hi⟩
  exact (cu.pair (cv.pair rows)).encodeCongr id (fun _ => rfl) (fun x => by
    change dataCode ((Q x).u,((Q x).v,_)) = dataCode (data (Q x))
    rw [he]
    rfl)
end FixedLC
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_FiniteFunction
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine

noncomputable def Poly.finFunction {α β : Type} [Fintype β]
    (ea : α → List Bool) : (n : ℕ) → (f : α → Fin n → β) →
    (∀ i, Poly ea (finiteCode β) (fun a => f a i)) →
    Poly ea (finiteCode (Fin n → β)) f
  | 0,f,_ => (Poly.const ea (finiteCode (Fin 0 → β)) (fun i => Fin.elim0 i)).congr
    (fun a => by funext i; exact Fin.elim0 i)
  | n+1,f,cf =>
    (((cf 0).pair (Poly.finFunction ea n (fun a i => f a i.succ) (fun i => cf i.succ))).comp
      (Poly.finite _ _ (prodBits_injective (finiteCode_injective β) (finiteCode_injective (Fin n → β)))
        (fun p : β × (Fin n → β) => Fin.cons p.1 p.2))).congr
          (fun a => by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl)

noncomputable def Poly.finiteFunction {α β ι : Type} [Fintype β] [Fintype ι] [DecidableEq ι]
    (ea : α → List Bool) (f : α → ι → β)
    (cf : ∀ i, Poly ea (finiteCode β) (fun a => f a i)) :
    Poly ea (finiteCode (ι → β)) f := by
  let E := Fintype.equivFin ι
  exact ((Poly.finFunction ea (Fintype.card ι) (fun a i => f a (E.symm i))
    (fun i => cf (E.symm i))).comp
      (Poly.finite _ _ (finiteCode_injective _) (fun g : Fin (Fintype.card ι) → β => fun i => g (E i)))).congr
        (fun a => by funext i; exact congrArg (f a) (E.symm_apply_apply i))

noncomputable def Poly.finiteRecode {α : Type} [Fintype α] (ea : α → List Bool)
    (ha : Function.Injective ea) : Poly ea (finiteCode α) id :=
  Poly.finite ea (finiteCode α) ha id

noncomputable def Poly.fixedSum {α ι : Type} (ea : α → List Bool)
    (f : α → ι → ℕ) (cf : ∀ i, Poly ea natBits (fun a => f a i)) :
    (xs : List ι) → Poly ea natBits (fun a => (xs.map (f a)).sum)
  | [] => (Poly.const ea natBits 0).congr (fun _ => rfl)
  | i::xs => (((cf i).pair (Poly.fixedSum ea f cf xs)).comp Poly.natAdd).congr
    (fun a => by simp only [Function.comp_apply,List.map_cons,List.sum_cons])

noncomputable def Poly.finiteSum {α ι : Type} [Fintype ι] (ea : α → List Bool)
    (f : α → ι → ℕ) (cf : ∀ i, Poly ea natBits (fun a => f a i)) :
    Poly ea natBits (fun a => ∑ i, f a i) := by
  classical
  exact (Poly.fixedSum ea f cf Finset.univ.toList).congr (fun a => by simp)
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_GraphFrame
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                               
section

namespace VertexCover.Machine
noncomputable def Poly.boundAll {α : Type} (ea : α → List Bool) (a₀ : α)
    {n : α → ℕ} {f : α × ℕ → Bool} (cn : Poly ea natBits n)
    (cf : Poly (prodBits ea natBits) boolBits f) :
    Poly ea boolBits (fun a => decide (∀ i, i<n a → f (a,i)=true)) :=
  ((Poly.tabulate ea boolBits a₀ false cn cf).comp Poly.listAnd).congr (fun a => by
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,foldl_and_all,Bool.true_and,List.all_eq_true,List.mem_map,
      List.mem_range,decide_eq_true_iff]
    constructor
    · intro h i hi; exact h _ ⟨i,hi,rfl⟩
    · rintro h b ⟨i,hi,rfl⟩; exact h i hi)
noncomputable def Poly.decideAnd {α : Type} (ea : α → List Bool)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (cp : Poly ea boolBits (fun a => decide (P a)))
    (cq : Poly ea boolBits (fun a => decide (Q a))) :
    Poly ea boolBits (fun a => decide (P a ∧ Q a)) :=
  ((cp.pair cq).comp (Poly.bool₂ (fun p => p.1 && p.2))).congr (fun a => by simp)
noncomputable def Poly.decideForall {α ι : Type} [Fintype ι] (ea : α → List Bool)
    (P : α → ι → Prop) [∀ a, DecidablePred (P a)]
    (cp : ∀ i, Poly ea boolBits (fun a => decide (P a i))) :
    Poly ea boolBits (fun a => decide (∀ i, P a i)) :=
  (Poly.finiteAll ea (fun a i => decide (P a i)) cp).congr (fun a => by simp)
noncomputable def Poly.natEqual : Poly (prodBits natBits natBits) boolBits
    (fun p : ℕ × ℕ => decide (p.1=p.2)) := Poly.natEq.congr (fun _ => rfl)

namespace GraphMachine
open LabelCover
variable {a b d : ℕ}
noncomputable def weightCode : Weight a b d → List Bool := finiteCode _
noncomputable def vertexCode : RawVertex a b d → List Bool := prodBits natBits weightCode
noncomputable def frameCode : Frame a b d → List Bool := prodBits FixedLC.code (prodBits vertexCode vertexCode)
noncomputable def seed (I : FixedLC a b) (n : ℕ) : I.toLC.Seeds d :=
  fun e => ⟨n/I.M^(Fintype.equivFin (PositionPair d) e).val%I.M,Nat.mod_lt _ I.Mpos⟩
noncomputable abbrev Q (p : Frame a b d) (x : TracePos d) : p.1.toLC.Query d :=
  p.1.toLC.query (seed p.1 (vertexAt p x.1).1) x.2
noncomputable def rawVertex (I : FixedLC a b) (v : RawVertex a b d) : I.toLC.Vertex d :=
  (seed I v.1,v.2)
noncomputable def descriptor (p : Frame a b d) : Descriptor a b d := diagram (Q p) (W p)
noncomputable def instancePoly : Poly (frameCode (a := a) (b := b) (d := d)) FixedLC.code Prod.fst :=
  Poly.fst FixedLC.code (prodBits vertexCode vertexCode)
noncomputable def atPoly (x : Bool) : Poly (frameCode (a := a) (b := b) (d := d)) vertexCode (fun p => vertexAt p x) := by
  let c := Poly.snd (FixedLC.code (a := a) (b := b)) (prodBits (vertexCode (a := a) (b := b) (d := d)) (vertexCode (a := a) (b := b) (d := d)))
  cases x
  · exact (c.comp (Poly.fst vertexCode vertexCode)).congr (fun _ => rfl)
  · exact (c.comp (Poly.snd vertexCode vertexCode)).congr (fun _ => rfl)
noncomputable def seedNumberPoly (x : Bool) : Poly (frameCode (a := a) (b := b) (d := d)) natBits (fun p => (vertexAt p x).1) :=
  (atPoly x).comp (Poly.fst natBits weightCode)
noncomputable def weightPoly : Poly (frameCode (a := a) (b := b) (d := d)) (finiteCode (TraceWeights a b d)) W := by
  let c := ((atPoly (a := a) (b := b) (d := d) false).comp (Poly.snd natBits weightCode)).pair ((atPoly true).comp (Poly.snd natBits weightCode))
  exact (c.comp (Poly.finite _ _ (prodBits_injective (finiteCode_injective _) (finiteCode_injective _))
    (fun p : Weight a b d × Weight a b d => fun x : TracePos d => (if x.1 then p.2 else p.1) x.2))).congr
      (fun p => by funext x; rcases x with ⟨x,j⟩; cases x <;> rfl)
noncomputable def samplePoly (hb : 0<b) (x : Bool) (e : PositionPair d) :
    Poly (frameCode (a := a) (b := b) (d := d)) natBits
      (fun p => (seed p.1 (vertexAt p x).1 e).val) := by
  let cm := (instancePoly (a := a) (b := b) (d := d)).comp (FixedLC.MPoly hb)
  exact ((((seedNumberPoly x).pair (cm.comp (Poly.natPow (Fintype.equivFin (PositionPair d) e).val))).comp
    Poly.natDiv).pair cm |>.comp Poly.natMod)
noncomputable def questionUPoly (hb : 0<b) (x : TracePos d) (k : {k : Fin d // x.2 < k}) :
    Poly (frameCode (a := a) (b := b) (d := d)) natBits (fun p => ((Q p x).2.1 k).val) :=
  ((instancePoly.pair (samplePoly hb x.1 ⟨(x.2,k.val),k.property⟩)).comp (FixedLC.leftPoly hb)).congr
    (fun p => congrArg (fun r : FixedLC.Row a b => r.1.1)
      (FixedLC.lookup_valid hb p.1 (seed p.1 (vertexAt p x.1).1 ⟨(x.2,k.val),k.property⟩)))
noncomputable def questionVPoly (hb : 0<b) (x : TracePos d) (k : {k : Fin d // k < x.2}) :
    Poly (frameCode (a := a) (b := b) (d := d)) natBits (fun p => ((Q p x).2.2 k).val) :=
  ((instancePoly.pair (samplePoly hb x.1 ⟨(k.val,x.2),k.property⟩)).comp (FixedLC.rightPoly hb)).congr
    (fun p => congrArg (fun r : FixedLC.Row a b => r.1.2)
      (FixedLC.lookup_valid hb p.1 (seed p.1 (vertexAt p x.1).1 ⟨(k.val,x.2),k.property⟩)))
end GraphMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_GraphConstraint
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
attribute [-simp] _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.mem_ownList _root_.OAI.VertexCover.LabelCover.mem_privateFiber _root_.OAI.VertexCover.LabelCover.restrictionForm_energy _root_.OAI.VertexCover.LabelCover.restrictionFunction_apply _root_.OAI.VertexCover.LabelCover.selectionForm_apply _root_.OAI.VertexCover.LabelCover.weightProjection_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                    
section

namespace VertexCover.Machine.GraphMachine
open LabelCover
variable {a b d : ℕ}
attribute [local instance 0] Classical.propDecidable
noncomputable def eqUPoly (hb : 0<b) (x y : TracePos d)
    (k : {k : Fin d // x.2 < k}) (l : {k : Fin d // y.2 < k}) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide ((Q p x).2.1 k=(Q p y).2.1 l)) :=
  (((questionUPoly hb x k).pair (questionUPoly hb y l)).comp Poly.natEqual).congr
    (fun p => by simp only [Function.comp_apply,Fin.ext_iff])
noncomputable def eqVPoly (hb : 0<b) (x y : TracePos d)
    (k : {k : Fin d // k < x.2}) (l : {k : Fin d // k < y.2}) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide ((Q p x).2.2 k=(Q p y).2.2 l)) :=
  (((questionVPoly hb x k).pair (questionVPoly hb y l)).comp Poly.natEqual).congr
    (fun p => by simp only [Function.comp_apply,Fin.ext_iff])
noncomputable def overlapUPoly (hb : 0<b) (x y : TracePos d) (A B : Query.Profile a b d) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide (∀ k : {k : Fin d // x.2 < k}, ∀ l : {k : Fin d // y.2 < k},
        (Q p x).2.1 k=(Q p y).2.1 l → A.1 k=B.1 l)) :=
  Poly.decideForall frameCode _ (fun k => Poly.decideForall frameCode _ (fun l =>
    ((eqUPoly hb x y k l).comp (Poly.bool (fun z => !z || decide (A.1 k=B.1 l)))).congr
      (fun _ => by simp)))
noncomputable def overlapVPoly (hb : 0<b) (x y : TracePos d) (A B : Query.Profile a b d) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide (∀ k : {k : Fin d // k < x.2}, ∀ l : {k : Fin d // k < y.2},
        (Q p x).2.2 k=(Q p y).2.2 l → A.2 k=B.2 l)) :=
  Poly.decideForall frameCode _ (fun k => Poly.decideForall frameCode _ (fun l =>
    ((eqVPoly hb x y k l).comp (Poly.bool (fun z => !z || decide (A.2 k=B.2 l)))).congr
      (fun _ => by simp)))
noncomputable def rowTest (hb : 0<b) (x y : TracePos d)
    (k : {k : Fin d // x.2 < k}) (l : {k : Fin d // k < y.2}) (A : Fin a) (B : Fin b)
    (p : Frame a b d × ℕ) : Bool :=
  decide ((FixedLC.lookup hb (p.1.1,p.2)).1.1=((Q p.1 x).2.1 k).val →
    (FixedLC.lookup hb (p.1.1,p.2)).1.2=((Q p.1 y).2.2 l).val →
    (FixedLC.lookup hb (p.1.1,p.2)).2 A=B)
noncomputable def rowTestPoly (hb : 0<b) (x y : TracePos d)
    (k : {k : Fin d // x.2 < k}) (l : {k : Fin d // k < y.2}) (A : Fin a) (B : Fin b) :
    Poly (prodBits (frameCode (a := a) (b := b) (d := d)) natBits) boolBits (rowTest hb x y k l A B) := by
  let p := Poly.fst (frameCode (a := a) (b := b) (d := d)) natBits
  let c := ((p.comp instancePoly).pair (Poly.snd frameCode natBits)).comp (FixedLC.lookupPoly hb)
  let cl := (((c.comp (Poly.fst (prodBits natBits natBits) FixedLC.mapCode)).comp (Poly.fst natBits natBits)).pair
    (p.comp (questionUPoly hb x k))).comp Poly.natEqual
  let cr := (((c.comp (Poly.fst (prodBits natBits natBits) FixedLC.mapCode)).comp (Poly.snd natBits natBits)).pair
    (p.comp (questionVPoly hb y l))).comp Poly.natEqual
  let cm := (c.comp (Poly.snd (prodBits natBits natBits) FixedLC.mapCode)).comp
    (Poly.finite FixedLC.mapCode boolBits (finiteCode_injective _) (fun f : Fin a → Fin b => decide (f A=B)))
  exact (((cl.pair cr).comp (Poly.bool₂ (fun p => p.1 && p.2))).pair cm |>.comp
    (Poly.bool₂ (fun p => !p.1 || p.2))).congr (fun p => by simp [rowTest,Bool.or_assoc])
noncomputable def crossAtomPoly (ha : 0<a) (hb : 0<b) (x y : TracePos d)
    (k : {k : Fin d // x.2 < k}) (l : {k : Fin d // k < y.2}) (A : Fin a) (B : Fin b) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide (∀ c : Fin p.1.M, p.1.left c=(Q p x).2.1 k →
        p.1.right c=(Q p y).2.2 l → p.1.projection c A=B)) := by
  let c := Poly.boundAll frameCode (defaultFrame ha hb) (instancePoly.comp (FixedLC.MPoly hb))
    (rowTestPoly hb x y k l A B)
  exact c.congr (fun p => by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_iff]
    constructor
    · intro h e
      have hh := h e.val e.isLt
      simp only [rowTest,FixedLC.lookup_valid,decide_eq_true_eq] at hh
      intro hl hr
      exact hh (congrArg Fin.val hl) (congrArg Fin.val hr)
    · intro h n hn
      have hh := h ⟨n,hn⟩
      simp only [rowTest,FixedLC.lookup_valid hb p.1 ⟨n,hn⟩,decide_eq_true_eq]
      intro hl hr
      exact hh (Fin.ext hl) (Fin.ext hr))
noncomputable def crossPoly (ha : 0<a) (hb : 0<b) (x y : TracePos d) (A B : Query.Profile a b d) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide (∀ c : Fin p.1.M, ∀ k : {k : Fin d // x.2 < k}, ∀ l : {k : Fin d // k < y.2},
        p.1.left c=(Q p x).2.1 k → p.1.right c=(Q p y).2.2 l → p.1.projection c (A.1 k)=B.2 l)) := by
  exact (Poly.decideForall frameCode _ (fun k => Poly.decideForall frameCode _ (fun l =>
    crossAtomPoly ha hb x y k l (A.1 k) (B.2 l)))).congr (fun p => by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_iff]
      constructor
      · intro h c k l; exact h k l c
      · intro h k l c; exact h c k l)
noncomputable def pairPoly (ha : 0<a) (hb : 0<b) (x y : TracePos d) (A B : Query.Profile a b d) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide (Query.ProfilePair (Q p x) (Q p y) A B)) :=
  (Poly.decideAnd frameCode _ _ (overlapUPoly hb x y A B)
    (Poly.decideAnd frameCode _ _ (overlapVPoly hb x y A B) (crossPoly ha hb x y A B))).congr
      (fun _ => by apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_iff]; rfl)
end VertexCover.Machine.GraphMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_GraphDescriptor
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.LabelCover.batchLaw_probability _root_.OAI.VertexCover.LabelCover.oppositePairKeyFintype _root_.OAI.VertexCover.LabelCover.starKeyFintype
attribute [-simp] _root_.OAI.VertexCover.LabelCover.batchSumCLM_apply _root_.OAI.VertexCover.LabelCover.mem_ownFiber _root_.OAI.VertexCover.LabelCover.mem_ownList _root_.OAI.VertexCover.LabelCover.mem_privateFiber _root_.OAI.VertexCover.LabelCover.restrictionForm_energy _root_.OAI.VertexCover.LabelCover.restrictionFunction_apply _root_.OAI.VertexCover.LabelCover.selectionForm_apply _root_.OAI.VertexCover.LabelCover.weightProjection_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                    
section

namespace VertexCover.Machine.GraphMachine
open LabelCover
variable {a b d : ℕ}
attribute [local instance 0] Classical.propDecidable
noncomputable instance descriptorFintype (a b d : ℕ) : Fintype (Descriptor a b d) := by
  classical
  letI : Fintype (ProfileRep a b d → Bool) := inferInstance
  letI : Fintype (TracePos d × TracePos d → Bool) := inferInstance
  letI : Fintype (ProfileRep a b d × ProfileRep a b d → Bool) := inferInstance
  letI : Fintype (TraceWeights a b d) := inferInstance
  letI : Fintype ((ProfileRep a b d × ProfileRep a b d → Bool) × TraceWeights a b d) := inferInstance
  letI : Fintype ((TracePos d × TracePos d → Bool) ×
    ((ProfileRep a b d × ProfileRep a b d → Bool) × TraceWeights a b d)) := inferInstance
  exact inferInstanceAs (Fintype ((_ → Bool) × _))
noncomputable def validPoly (ha : 0<a) (hb : 0<b) (x : TracePos d) (A : Query.Profile a b d) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide ((Q p x).ProfileValid A)) := by
  let c₁ := Poly.const (frameCode (a := a) (b := b) (d := d)) boolBits
    (decide (∀ k, ¬x.2 < k → A.1 k=⟨0,ha⟩))
  let c₂ := Poly.const (frameCode (a := a) (b := b) (d := d)) boolBits
    (decide (∀ k, ¬k < x.2 → A.2 k=⟨0,hb⟩))
  exact (Poly.decideAnd frameCode _ _ c₁ (Poly.decideAnd frameCode _ _ c₂ (pairPoly ha hb x x A A))).congr
    (fun _ => by apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_iff]; rfl)
noncomputable def queryEqualPoly (hb : 0<b) (x y : TracePos d) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide (Q p x=Q p y)) := by
  rcases x with ⟨s,j⟩
  rcases y with ⟨t,k⟩
  by_cases h : j=k
  · subst k
    let cu := Poly.decideForall (frameCode (a := a) (b := b) (d := d))
      (fun p (i : {k : Fin d // j<k}) => (Q p (s,j)).2.1 i=(Q p (t,j)).2.1 i)
      (fun i => (eqUPoly hb (s,j) (t,j) i i).congr (fun _ => by simp))
    let cv := Poly.decideForall (frameCode (a := a) (b := b) (d := d))
      (fun p (i : {k : Fin d // k<j}) => (Q p (s,j)).2.2 i=(Q p (t,j)).2.2 i)
      (fun i => (eqVPoly hb (s,j) (t,j) i i).congr (fun _ => by simp))
    exact (Poly.decideAnd frameCode _ _ cu cv).congr (fun p => by
      apply Bool.decide_congr
      simp only [Q,LabelCover.query,Sigma.mk.inj_iff,heq_eq_eq,
        Prod.mk.injEq,funext_iff,true_and])
  · exact (Poly.const frameCode boolBits false).congr (fun p => by
      symm
      apply decide_eq_false
      intro hh
      exact h (congrArg Sigma.fst hh))
noncomputable def boolFinite : Poly boolBits (finiteCode Bool) id :=
  Poly.finite boolBits (finiteCode Bool) (by intro a b h; simpa [boolBits] using h) id
noncomputable def descriptorPoly (ha : 0<a) (hb : 0<b) :
    Poly (frameCode (a := a) (b := b) (d := d)) (finiteCode (Descriptor a b d)) descriptor := by
  let cv := Poly.finiteFunction (frameCode (a := a) (b := b) (d := d))
    (fun p (r : ProfileRep a b d) => decide ((Q p r.1).ProfileValid r.2))
    (fun r => ((validPoly ha hb r.1 r.2).comp boolFinite).congr (fun _ => rfl))
  let ce := Poly.finiteFunction (frameCode (a := a) (b := b) (d := d))
    (fun p (xy : TracePos d × TracePos d) => decide (Q p xy.1=Q p xy.2))
    (fun xy => ((queryEqualPoly hb xy.1 xy.2).comp boolFinite).congr (fun _ => rfl))
  let cp := Poly.finiteFunction (frameCode (a := a) (b := b) (d := d))
    (fun p (rs : ProfileRep a b d × ProfileRep a b d) => decide (Query.ProfilePair (Q p rs.1.1) (Q p rs.2.1) rs.1.2 rs.2.2))
    (fun rs => ((pairPoly ha hb rs.1.1 rs.2.1 rs.1.2 rs.2.2).comp boolFinite).congr (fun _ => rfl))
  let cw := weightPoly (a := a) (b := b) (d := d)
  let ec : Descriptor a b d → List Bool := prodBits (finiteCode (ProfileRep a b d → Bool))
    (prodBits (finiteCode (TracePos d × TracePos d → Bool))
      (prodBits (finiteCode (ProfileRep a b d × ProfileRep a b d → Bool))
        (finiteCode (TraceWeights a b d))))
  let cc : Poly ec (finiteCode (Descriptor a b d)) id := Poly.finite _ _
    (prodBits_injective (finiteCode_injective _) (prodBits_injective (finiteCode_injective _)
      (prodBits_injective (finiteCode_injective _) (finiteCode_injective _)))) id
  exact ((cv.pair (ce.pair (cp.pair cw))).comp cc).congr (fun p => by
    apply Prod.ext
    · funext r; exact Bool.decide_congr Iff.rfl
    · apply Prod.ext
      · funext xy; exact Bool.decide_congr Iff.rfl
      · apply Prod.ext
        · funext rs; exact Bool.decide_congr Iff.rfl
        · rfl)
noncomputable def testFinitePoly (t : ℝ) :
    Poly (finiteCode (Descriptor a b d)) boolBits (Descriptor.test (a := a) (b := b) (d := d) t) :=
  Poly.finite (finiteCode (Descriptor a b d)) boolBits
    (finiteCode_injective (Descriptor a b d)) (Descriptor.test t)
noncomputable def normTestPoly (ha : 0<a) (hb : 0<b) (t : ℝ) :=
  @Poly.comp (Frame a b d) (Descriptor a b d) Bool
    (frameCode (a := a) (b := b) (d := d)) (finiteCode (Descriptor a b d)) boolBits
    (descriptor (a := a) (b := b) (d := d)) (Descriptor.test (a := a) (b := b) (d := d) t)
    (descriptorPoly (a := a) (b := b) (d := d) ha hb) (testFinitePoly (a := a) (b := b) (d := d) t)
 theorem diagramSum_frame (p : Frame a b d) :
    diagramSum (Q p) (W p)=p.1.toLC.sumVector (p.1.toLC.profileVertexEquiv d (rawVertex p.1 p.2.1)) +
      p.1.toLC.sumVector (p.1.toLC.profileVertexEquiv d (rawVertex p.1 p.2.2)) := by
  classical
  simp only [diagramSum,Fintype.sum_prod_type,Fintype.sum_bool]
  exact add_comm _ _
 theorem normTest_correct (p : Frame a b d) (t : ℝ) :
    (descriptor p).test t=true ↔ p.1.toLC.compatibilityNorm
      (p.1.toLC.sumVector (p.1.toLC.profileVertexEquiv d (rawVertex p.1 p.2.1))+
      p.1.toLC.sumVector (p.1.toLC.profileVertexEquiv d (rawVertex p.1 p.2.2))) ≤ 2*t := by
  have h := diagram_test (Φ := p.1.toLC) (Q p) (W (a := a) (b := b) p) t
  exact h.trans (Iff.of_eq (congrArg
    (fun f : p.1.toLC.Coordinate d → ℝ => p.1.toLC.compatibilityNorm f ≤ 2*t)
    (diagramSum_frame p)))
end VertexCover.Machine.GraphMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_GraphNumber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                
section

namespace VertexCover.Machine.GraphMachine
open LabelCover
noncomputable section
variable {a b d : ℕ}
def count (I : FixedLC a b) (d : ℕ) : ℕ := I.M ^ Fintype.card (PositionPair d) * weightCount a b d

def seedEquiv (I : FixedLC a b) (d : ℕ) : Fin (I.M ^ Fintype.card (PositionPair d)) ≃ I.toLC.Seeds d :=
  finFunctionFinEquiv.symm.trans (Equiv.arrowCongr (Fintype.equivFin (PositionPair d)).symm (Equiv.refl _))

def numberEquiv (I : FixedLC a b) (d : ℕ) : Fin (count I d) ≃ I.toLC.Vertex d :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (seedEquiv I d) (Fintype.equivFin (Weight a b d)).symm)

def fullEquiv (I : FixedLC a b) (d : ℕ) : Fin (count I d) ≃ I.toLC.Vertex d :=
  (numberEquiv I d).trans (I.toLC.profileVertexEquiv d)
def graph (I : FixedLC a b) (d : ℕ) (t : ℝ) : SimpleGraph (Fin (count I d)) :=
  (I.toLC.graph d t).comap (fullEquiv I d)
def explicitGraph (I : FixedLC a b) (d : ℕ) (t : ℝ) : ExplicitGraph :=
  ExplicitGraph.numbered (graph I d t)

def countPoly (hb : 0<b) (d : ℕ) : Poly (FixedLC.code (a := a) (b := b)) natBits (fun I => count I d) :=
  ((((FixedLC.MPoly hb).comp (Poly.natPow (Fintype.card (PositionPair d)))).pair
    (Poly.const FixedLC.code natBits (weightCount a b d))).comp Poly.natMul).congr (fun _ => rfl)
def decodePoly : Poly natBits (vertexCode (a := a) (b := b) (d := d)) decode := by
  let q := ((Poly.identity natBits).pair (Poly.const natBits natBits (weightCount a b d))).comp Poly.natDiv
  let r := (Poly.finMod (weightCount a b d) weightCount_pos).comp
    (Poly.finite finCode weightCode (finCode_injective _) (Fintype.equivFin (Weight a b d)).symm)
  exact (q.pair r).congr (fun _ => rfl)

def numberFramePoly : Poly (prodBits (FixedLC.code (a := a) (b := b)) (prodBits natBits natBits))
    (frameCode (a := a) (b := b) (d := d)) numberFrame := by
  let I := Poly.fst (FixedLC.code (a := a) (b := b)) (prodBits natBits natBits)
  let p := Poly.snd (FixedLC.code (a := a) (b := b)) (prodBits natBits natBits)
  exact I.pair (((p.comp (Poly.fst natBits natBits)).comp decodePoly).pair
    ((p.comp (Poly.snd natBits natBits)).comp decodePoly))

def test (t : ℝ) (p : FixedLC a b × (ℕ × ℕ)) : Bool :=
  decide (p.2.1<p.2.2) && (descriptor (numberFrame (d := d) p)).test t

attribute [local irreducible] Descriptor.test

def normNumberPoly (ha : 0<a) (hb : 0<b) (t : ℝ) :=
  (numberFramePoly (a := a) (b := b) (d := d)).comp
    (normTestPoly (a := a) (b := b) (d := d) ha hb t)
def lessPoly (a b : ℕ) :=
  (Poly.snd (FixedLC.code (a := a) (b := b)) (prodBits natBits natBits)).comp Poly.natLt
def testPrePoly (ha : 0<a) (hb : 0<b) (t : ℝ) :=
  ((lessPoly a b).pair (normNumberPoly (d := d) ha hb t)).comp
    (Poly.bool₂ (fun p => p.1 && p.2))
def testPoly (ha : 0<a) (hb : 0<b) (t : ℝ) :
    Poly (prodBits (FixedLC.code (a := a) (b := b)) (prodBits natBits natBits)) boolBits (test (d := d) t) :=
  (testPrePoly (d := d) ha hb t).congr (fun _ => rfl)

theorem test_correct (I : FixedLC a b) (t : ℝ) (u v : Fin (count I d)) :
    test (d := d) t (I,(u.val,v.val))=true ↔ u<v ∧ (graph I d t).Adj u v := by
  classical
  simp only [test,Bool.and_eq_true,decide_eq_true_iff]
  rw [normTest_correct]
  change (u.val<v.val ∧ _) ↔ (u<v ∧ fullEquiv I d u ≠ fullEquiv I d v ∧ _)
  have he (n : Fin (count I d)) : fullEquiv I d n=I.toLC.profileVertexEquiv d (rawVertex I (decode n.val)) := rfl
  simp only [he,numberFrame]
  constructor
  · rintro ⟨hl,hn⟩
    exact ⟨hl,fun h => (ne_of_lt hl) (congrArg Fin.val ((fullEquiv I d).injective h)),hn⟩
  · rintro ⟨hl,_,hn⟩; exact ⟨hl,hn⟩
end
end VertexCover.Machine.GraphMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_GraphOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                
section

namespace VertexCover.Machine.GraphMachine
open LabelCover
noncomputable section
variable {a b d : ℕ}

def candidates (I : FixedLC a b) (d : ℕ) : List (ℕ × ℕ) :=
  (List.range (count I d * count I d)).map (fun i => (i/count I d,i%count I d))
def edgeValues (I : FixedLC a b) (d : ℕ) (t : ℝ) : List (ℕ × ℕ) :=
  (candidates I d).filter (fun p => test (d := d) t (I,p))

theorem candidates_eq (I : FixedLC a b) (d : ℕ) :
    candidates I d = (List.ofFn fun e : Fin (count I d * count I d) => finProdFinEquiv.symm e).map
      (fun p => (p.1.val,p.2.val)) := by
  apply List.ext_getElem
  · simp [candidates]
  · intro i hi hj
    simp only [candidates,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    rfl

theorem edgeValues_eq (I : FixedLC a b) (d : ℕ) (t : ℝ) :
    edgeValues I d t=(explicitGraph I d t).edges.map (fun p => (p.1.val,p.2.val)) := by
  classical
  rw [edgeValues,candidates_eq,List.filter_map]
  change List.map _ (List.filter _ _) = List.map _ (List.filter _ _)
  congr 1
  apply List.filter_congr
  intro p hp
  apply Bool.eq_iff_iff.mpr
  exact (test_correct I t p.1 p.2).trans decide_eq_true_iff.symm

def candidatesPoly (ha : 0<a) (hb : 0<b) (d : ℕ) :
    Poly (FixedLC.code (a := a) (b := b)) (listBits (prodBits natBits natBits)) (fun I => candidates I d) := by
  let c := countPoly (a := a) hb d
  let n := (c.pair c).comp Poly.natMul
  let count := (Poly.fst (FixedLC.code (a := a) (b := b)) natBits).comp c
  let i := Poly.snd (FixedLC.code (a := a) (b := b)) natBits
  let pair := ((i.pair count).comp Poly.natDiv).pair ((i.pair count).comp Poly.natMod)
  exact Poly.tabulate FixedLC.code (prodBits natBits natBits) (FixedLC.one ha hb) (0,0) n pair

def edgeValuesPoly (ha : 0<a) (hb : 0<b) (d : ℕ) (t : ℝ) :
    Poly (FixedLC.code (a := a) (b := b)) (listBits (prodBits natBits natBits)) (fun I => edgeValues I d t) :=
  (((Poly.identity FixedLC.code).pair (candidatesPoly ha hb d)).comp
    (Poly.listFilterWith FixedLC.code (prodBits natBits natBits) (FixedLC.one ha hb) (0,0)
      (testPoly (d := d) ha hb t))).congr (fun _ => rfl)

def endpointPoly : Poly (prodBits natBits natBits) (listBits natBits) (fun p : ℕ × ℕ => [p.1,p.2]) :=
  (((Poly.fst natBits natBits).pair ((Poly.snd natBits natBits).comp (Poly.listSingleton natBits))).comp
    (Poly.listCons natBits)).congr (fun _ => rfl)
def names (I : FixedLC a b) (d : ℕ) (t : ℝ) : List ℕ :=
  [count I d] ++ List.range (count I d) ++ [(edgeValues I d t).length] ++
    (edgeValues I d t).flatMap (fun p => [p.1,p.2])
def namesPoly (ha : 0<a) (hb : 0<b) (d : ℕ) (t : ℝ) :
    Poly (FixedLC.code (a := a) (b := b)) (listBits natBits) (fun I => names I d t) := by
  let n := countPoly (a := a) hb d
  let head := n.comp (Poly.listSingleton natBits)
  let verts := n.comp Poly.range
  let es := edgeValuesPoly ha hb d t
  let ne := ((es.comp (Poly.listLength (prodBits natBits natBits) (0,0))).comp (Poly.listSingleton natBits))
  let ends := es.comp (Poly.listFlatMap (prodBits natBits natBits) natBits (0,0) 0 endpointPoly)
  let one := (head.pair verts).comp (Poly.listAppend natBits 0)
  let two := (one.pair ne).comp (Poly.listAppend natBits 0)
  exact ((two.pair ends).comp (Poly.listAppend natBits 0)).congr (fun _ => rfl)

theorem names_bits (I : FixedLC a b) (d : ℕ) (t : ℝ) :
    (names I d t).flatMap UniqueGames.BinaryEncoding.nameBits = (explicitGraph I d t).bits := by
  rw [names,edgeValues_eq]
  simp only [List.length_map,List.flatMap_map]
  rfl

def outputPoly (ha : 0<a) (hb : 0<b) (d : ℕ) (t : ℝ) :
    Poly (FixedLC.code (a := a) (b := b)) ExplicitGraph.bits (fun I => explicitGraph I d t) :=
  ((namesPoly ha hb d t).comp Poly.nameList).encodeCongr id (fun _ => rfl) (fun I => names_bits I d t)
end
end VertexCover.Machine.GraphMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Lazy
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                
section

namespace VertexCover.Machine.LazyMachine
open UniqueGames.Foundations.PCP
open TableMachine PreprocessingOverlayTables

def output {d : ℕ} (T : PortTables.Input d) : PortTables.Input (2*d) := ⟨T.1,lazy T.2⟩

def reverse {d : ℕ} (x : PortTables.Input d × ℕ) : ℕ :=
  let v := x.2/(2*d)
  let p := x.2%(2*d)
  if p<d then x.2 else
    let r := ExpandMachine.lookup d (x.1.2.reverseIndex.toList.map Fin.val,(v,p-d))
    (r.2+d)+(2*d)*r.1

def relation {d : ℕ} (x : PortTables.Input d × ℕ) : GraphTables.RelationTable :=
  if x.2%(2*d)<d then RegularMachine.trueRelation else
    x.1.2.relations.toList.getD (x.2%(2*d)-d+d*(x.2/(2*d))) relationDefault

noncomputable def reversePoly {d : ℕ} : Poly (prodBits (PortMachine.code (q := d)) natBits) natBits reverse := by
  let ec := PortMachine.code (q := d)
  let t := Poly.fst ec natBits
  let i := Poly.snd ec natBits
  let c := Poly.const (prodBits ec natBits) natBits (2*d)
  let cd := Poly.const (prodBits ec natBits) natBits d
  let v := (i.pair c).comp Poly.natDiv
  let p := (i.pair c).comp Poly.natMod
  let r := ((t.comp PortMachine.reverseListPoly).pair
    (v.pair ((p.pair cd).comp Poly.natSub))).comp (ExpandMachine.lookupPoly d)
  let rv := r.comp (Poly.fst natBits natBits)
  let rp := r.comp (Poly.snd natBits natBits)
  let out := (((rp.pair cd).comp Poly.natAdd).pair
    ((c.pair rv).comp Poly.natMul)).comp Poly.natAdd
  exact (((p.pair cd).comp Poly.natLt).ite i out).congr (fun _ => by
    simp only [Function.comp_apply,reverse,decide_eq_true_eq])

noncomputable def relationPoly {d : ℕ} : Poly (prodBits (PortMachine.code (q := d)) natBits) relationCode relation := by
  let ec := PortMachine.code (q := d)
  let t := Poly.fst ec natBits
  let i := Poly.snd ec natBits
  let c := Poly.const (prodBits ec natBits) natBits (2*d)
  let cd := Poly.const (prodBits ec natBits) natBits d
  let v := (i.pair c).comp Poly.natDiv
  let p := (i.pair c).comp Poly.natMod
  let idx := (((p.pair cd).comp Poly.natSub).pair ((cd.pair v).comp Poly.natMul)).comp Poly.natAdd
  exact (((p.pair cd).comp Poly.natLt).ite (Poly.const _ relationCode RegularMachine.trueRelation)
    ((t.pair idx).comp PortMachine.relationPoly)).congr (fun _ => by
      simp only [Function.comp_apply,relation,decide_eq_true_eq])

 theorem reverse_source {d : ℕ} (T : PortTables.Input d) (i : Fin ((output T).1*(2*d))) :
    reverse (T,i.val) = (output T).2.reverseIndex[i].val := by
  let E := (Equiv.prodCongr (Equiv.refl (Fin T.1)) (lazyPorts d)).trans (PortTables.rowIndex _ _)
  obtain ⟨⟨v,b,p⟩,rfl⟩ := E.surjective i
  have hi : ((E (v,b,p)).val/(2*d),(E (v,b,p)).val%(2*d)) = (v.val,(lazyPorts d (b,p)).val) :=
    congrArg (fun z : Fin T.1 × Fin (2*d) => (z.1.val,z.2.val))
      ((PortTables.rowIndex _ _).symm_apply_apply (v,lazyPorts d (b,p)))
  change _ = (lazy T.2).reverseIndex[PortTables.rowIndex _ _ (v,lazyPorts d (b,p))].val
  dsimp only [reverse]
  have hv : (E (v,b,p)).val/(2*d) = v.val := congrArg Prod.fst hi
  have hp : (E (v,b,p)).val%(2*d) = (lazyPorts d (b,p)).val := congrArg Prod.snd hi
  conv_lhs => rw [hv,hp]
  rw [← PortTables.rowIndex_rotation]
  cases b with
  | false =>
    rw [lazyPorts_false_val,ite_eq_left p.isLt,lazy_rotation_false]
    rfl
  | true =>
    rw [lazyPorts_true_val,ite_eq_right (by omega),Nat.add_sub_cancel_right,OverlayMachine.lookup_port T.2 (v,p),
      lazy_rotation_true]
    simp only [PortTables.rowIndex_val,lazyPorts_true_val]

 theorem relation_source {d : ℕ} (T : PortTables.Input d) (i : Fin ((output T).1*(2*d))) :
    relation (T,i.val) = (output T).2.relations[i] := by
  let E := (Equiv.prodCongr (Equiv.refl (Fin T.1)) (lazyPorts d)).trans (PortTables.rowIndex _ _)
  obtain ⟨⟨v,b,p⟩,rfl⟩ := E.surjective i
  have hi : ((E (v,b,p)).val/(2*d),(E (v,b,p)).val%(2*d)) = (v.val,(lazyPorts d (b,p)).val) :=
    congrArg (fun z : Fin T.1 × Fin (2*d) => (z.1.val,z.2.val))
      ((PortTables.rowIndex _ _).symm_apply_apply (v,lazyPorts d (b,p)))
  change _ = (lazy T.2).relations[PortTables.rowIndex _ _ (v,lazyPorts d (b,p))]
  dsimp only [relation]
  have hv : (E (v,b,p)).val/(2*d) = v.val := congrArg Prod.fst hi
  have hp : (E (v,b,p)).val%(2*d) = (lazyPorts d (b,p)).val := congrArg Prod.snd hi
  conv_lhs => rw [hv,hp]
  have extensionality {left right : GraphTables.RelationTable}
      (equal : ∀ first second,
        GraphTables.relationAt left first second = GraphTables.relationAt right first second) :
      left = right := by
    apply Vector.ext
    intro index index_lt
    simpa only [GraphTables.relationAt,Prod.eta,Equiv.apply_symm_apply,Fin.getElem_fin] using
      equal (GraphTables.relationIndex.symm ⟨index,index_lt⟩).1
        (GraphTables.relationIndex.symm ⟨index,index_lt⟩).2
  apply extensionality
  intro a c
  cases b with
  | false =>
    rw [lazyPorts_false_val,ite_eq_left p.isLt,RegularMachine.trueRelation,GraphTables.relationAt_relationOf]
    exact (lazy_accepts_false T.2 v p a c).symm
  | true =>
    rw [lazyPorts_true_val,ite_eq_right (by omega),Nat.add_sub_cancel_right,
      List.getD_eq_getElem _ _ (by simpa using (PortTables.rowIndex T.1 d (v,p)).isLt)]
    exact (lazy_accepts_true T.2 v p a c).symm

noncomputable def poly {d : ℕ} : Poly (PortMachine.code (q := d)) PortMachine.code output := by
  let zero : PortTables.Input d := ⟨0,PortTables.ofPortGraph
    {rot := Equiv.refl _,rot_involutive := fun _ => rfl} (fun _ _ _ => true) (fun _ _ _ => rfl)⟩
  exact PortMachine.materializePoly PortMachine.code zero output PortMachine.verticesPoly
    reversePoly relationPoly reverse_source relation_source

end VertexCover.Machine.LazyMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_LoopFrom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                             
section

namespace VertexCover.Machine
open Turing

noncomputable def Poly.loopFrom {α β : Type} {e : α → List Bool} {body : α → Bool × α}
    (c : Poly e (flagBits e) body) (initial result : β → α) (size count : Polynomial ℕ)
    (spec : ∀ b, ∃ n, n ≤ count.eval (e (initial b)).length ∧
      BoundedRun e body (size.eval (e (initial b)).length) (initial b) (result b) n) :
    Poly (fun b => e (initial b)) e result where
  computation := {
    tm := Loop.machine c.computation.tm c.computation.inputAlphabet c.computation.outputAlphabet
    inputAlphabet := c.computation.inputAlphabet
    outputAlphabet := Equiv.refl Bool
    time := count * (loopCost c.computation).comp size
    outputsFun := fun a => Classical.choice (by
      simp only [show (Equiv.refl Bool).invFun = id from rfl, List.map_id]
      obtain ⟨n, hn, run⟩ := spec a
      obtain ⟨execution⟩ := boundedRun_execution c.computation run
      refine ⟨{ execution with steps_le_m := ?_ }⟩
      simp only [Polynomial.eval_mul, Polynomial.eval_comp]
      exact execution.steps_le_m.trans (Nat.mul_le_mul_right _ hn)) }
  finiteAlphabet := Loop.finiteAlphabet _ _ _ c.finiteAlphabet

noncomputable def Poly.initializeLoop {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {initial : α → β} {result : α → β} (ci : Poly ea eb initial)
    (cl : Poly (fun a => eb (initial a)) eb result) : Poly ea eb result := by
  let first : Poly ea (fun a => eb (initial a)) id := ci.encodeCongr id (fun _ => rfl) (fun _ => rfl)
  exact (first.comp cl).congr (fun _ => rfl)

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_NatLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                           
section

namespace VertexCover.Machine
namespace Logarithm
noncomputable def bodyPoly : Poly enc (flagBits enc) body := by
  let n := Poly.fst natBits natBits
  let c := Poly.snd natBits natBits
  let test := ((Poly.const enc natBits 2).pair n).comp Poly.natLE
  let next := ((n.pair (Poly.const enc natBits 2)).comp Poly.natDiv).pair (c.comp Poly.natSucc)
  exact (test.flagPair (test.ite next (Poly.identity enc))).congr (fun p => by
    by_cases h : 2 ≤ p.1 <;> simp [Function.comp_apply,body,h])
noncomputable def poly : Poly enc enc result :=
  bodyPoly.loop result Polynomial.X (Polynomial.X+1) (by
    intro ⟨n,c⟩
    obtain ⟨k,hk,hr⟩ := run n c (enc (n,c)).length le_rfl
    refine ⟨k,?_,by simpa only [Polynomial.eval_X] using hr⟩
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,enc,prodBits,pairBits_length,natBits_length]
    omega)
end Logarithm
noncomputable def Poly.natLog2 : Poly natBits natBits Nat.log2 :=
  ((((Poly.identity natBits).pair (Poly.const natBits natBits 0)).comp Logarithm.poly).comp
    (Poly.snd natBits natBits)).congr (fun n => by simp only [Function.comp_apply,Logarithm.result,Nat.zero_add,id_eq])
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_NatWalk
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.dartNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine.NatWalkMachine
open UniqueGames.Foundations.PCP TableMachine

def code {d : ℕ} : State d → List Bool := prodBits PortMachine.code natBits

def step {d : ℕ} (p : Fin d) (s : State d) : State d :=
  (s.1,(ExpandMachine.lookup d (s.1.2.reverseIndex.toList.map Fin.val,s.2,p.val)).1)
noncomputable def stepPoly {d : ℕ} (p : Fin d) : Poly (code (d := d)) code (step p) := by
  let t := Poly.fst (PortMachine.code (q := d)) natBits
  let v := Poly.snd (PortMachine.code (q := d)) natBits
  let r := (((t.comp PortMachine.reverseListPoly).pair
    (v.pair (Poly.const code natBits p.val))).comp (ExpandMachine.lookupPoly d)).comp
      (Poly.fst natBits natBits)
  exact t.pair r

def word {d : ℕ} : (n : ℕ) → (Fin n → Fin d) → State d → State d
  | 0, _, s => s
  | n+1, p, s => word n (fun j => p j.succ) (step (p 0) s)
noncomputable def wordPoly {d : ℕ} : (n : ℕ) → (p : Fin n → Fin d) → Poly (code (d := d)) code (word n p)
  | 0, _ => Poly.identity code
  | n+1, p => (stepPoly (p 0)).comp (wordPoly n (fun j => p j.succ))

def edge {d : ℕ} : (n : ℕ) → (Fin (n+1) → Fin d) → Fin (n+1) → State d → State d × Fin d
  | 0, p, _, s => (s,p 0)
  | n+1, p, k, s => Fin.cases (s,p 0) (fun j => edge n (fun i => p i.succ) j (step (p 0) s)) k
noncomputable def edgePoly {d : ℕ} : (n : ℕ) → (p : Fin (n+1) → Fin d) → (k : Fin (n+1)) →
    Poly (code (d := d)) (prodBits code finCode) (edge n p k)
  | 0, p, _ => (Poly.identity code).pair (Poly.const code finCode (p 0))
  | n+1, p, k => Fin.cases
      ((Poly.identity code).pair (Poly.const code finCode (p 0)))
      (fun j => (stepPoly (p 0)).comp (edgePoly n (fun i => p i.succ) j)) k

noncomputable def stepVariablePoly {d : ℕ} (hd : 0<d) :
    Poly (prodBits (code (d := d)) finCode) code (fun x => step x.2 x.1) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact Poly.finiteBranch code finCode code (finCode_injective d) (fun s p => step p s) stepPoly

def forget {d : ℕ} (s : WalkMachine.State d) : State d := (s.1,s.2.val)
 theorem step_forget {d : ℕ} (p : Fin d) (s : WalkMachine.State d) :
    step p (forget s) = forget (WalkMachine.step p s) := by
  change (s.1,_)=(s.1,_)
  apply congrArg (fun n => (s.1,n))
  exact congrArg Prod.fst (OverlayMachine.lookup_port s.1.2 (s.2,p))
 theorem word_forget {d : ℕ} : ∀ (n : ℕ) (p : Fin n → Fin d) (s : WalkMachine.State d),
    word n p (forget s) = forget (WalkMachine.word n p s) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih => intro p s; rw [word,step_forget,ih]; rfl
 theorem edge_forget {d : ℕ} : ∀ (n : ℕ) (p : Fin (n+1) → Fin d) (k : Fin (n+1)) (s : WalkMachine.State d),
    edge n p k (forget s) = (forget (WalkMachine.edge n p k s).1,(WalkMachine.edge n p k s).2) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro p k s
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · simp only [edge,Fin.cases_succ,step_forget,ih]
      rfl

def accepts {d : ℕ} (p : Fin d) (a b : GraphTables.Label) (s : State d) : Bool :=
  GraphTables.relationAt (s.1.2.relations.toList.getD (p.val+d*s.2) relationDefault) a b
noncomputable def acceptsPoly {d : ℕ} (p : Fin d) (a b : GraphTables.Label) :
    Poly (code (d := d)) boolBits (accepts p a b) := by
  let t := Poly.fst (PortMachine.code (q := d)) natBits
  let v := Poly.snd (PortMachine.code (q := d)) natBits
  let idx := ((Poly.const code natBits p.val).pair
    (((Poly.const code natBits d).pair v).comp Poly.natMul)).comp Poly.natAdd
  let r := (t.pair idx).comp PortMachine.relationPoly
  letI : Fintype GraphTables.RelationTable := Fintype.ofEquiv (Fin (64*64) → Bool)
    { toFun := Vector.ofFn
      invFun := fun r i => r[i]
      left_inv := by intro f; funext i; simp
      right_inv := by intro r; ext i; simp }
  exact r.comp (Poly.finite relationCode boolBits WalkMachine.relationCode_injective
    (fun t => GraphTables.relationAt t a b))
noncomputable def acceptsVariablePoly {d : ℕ} (hd : 0<d) :
    Poly (prodBits (code (d := d)) (prodBits finCode (prodBits finCode finCode))) boolBits
      (fun x => accepts x.2.1 x.2.2.1 x.2.2.2 x.1) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact Poly.finiteBranch code (prodBits finCode (prodBits finCode finCode)) boolBits
    (prodBits_injective (finCode_injective d)
      (prodBits_injective (finCode_injective 64) (finCode_injective 64)))
    (fun s x => accepts x.1 x.2.1 x.2.2 s) (fun x => acceptsPoly x.1 x.2.1 x.2.2)
 theorem accepts_forget {d : ℕ} (p : Fin d) (a b : GraphTables.Label) (s : WalkMachine.State d) :
    accepts p a b (forget s) = PortTables.accepts s.1.2 (s.2,p) a b := by
  unfold accepts forget
  rw [List.getD_eq_getElem _ _ (by simpa using (PortTables.rowIndex s.1.1 d (s.2,p)).isLt)]
  rfl

end VertexCover.Machine.NatWalkMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_NatPath
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine.NatPathMachine
open UniqueGames.Foundations.PCP
open PoweringWalks PoweringLabels PoweringAddresses PoweringReach NatWalkMachine

def search {d : ℕ} (t : ℕ) (a : PaddedLabel (Fin d) t GraphTables.Label)
    (x : State d × ℕ) : GraphTables.Label :=
  FixedSearch.run (fun x w => decide ((word w.1.val w.2 x.1).2=x.2))
    (fun _ w => a w) 0 (allAddresses d t) x
noncomputable def searchPoly {d : ℕ} (t : ℕ) (a : PaddedLabel (Fin d) t GraphTables.Label) :
    Poly (prodBits (code (d := d)) natBits) finCode (search t a) :=
  FixedSearch.poly (prodBits code natBits) finCode _ _ 0
    (fun w => ((((Poly.fst code natBits).comp (wordPoly w.1.val w.2)).comp
      (Poly.snd PortMachine.code natBits)).pair (Poly.snd code natBits)).comp Poly.natEq)
    (fun w => Poly.const _ finCode (a w)) (allAddresses d t)
 theorem search_forget {d : ℕ} (t : ℕ) (a : PaddedLabel (Fin d) t GraphTables.Label)
    (s : WalkMachine.State d) (u : ℕ) :
    search t a (forget s,u) = AddressMachine.search t a (s,u) := by
  unfold search AddressMachine.search
  generalize allAddresses d t = xs
  induction xs with
  | nil => rfl
  | cons w xs ih =>
    dsimp only [FixedSearch.run]
    exact if_congr (Iff.of_eq (congrArg (fun x : State d => decide (x.2=u)=true)
      (word_forget w.1.val w.2 s))) rfl ih

def edgeTest {d : ℕ} (n : ℕ) (p : Fin (n+1) → Fin d)
    (a b : PaddedLabel (Fin d) (n+1) GraphTables.Label) (k : Fin (n+1)) (s : State d) : Bool :=
  let e := edge n p k s
  accepts e.2 (search (n+1) a (s,e.1.2))
    (search (n+1) b (word (n+1) p s,(step e.2 e.1).2)) e.1
noncomputable def edgeTestPoly {d : ℕ} (hd : 0<d) (n : ℕ) (p : Fin (n+1) → Fin d)
    (a b : PaddedLabel (Fin d) (n+1) GraphTables.Label) (k : Fin (n+1)) :
    Poly (code (d := d)) boolBits (edgeTest n p a b k) := by
  let es := edgePoly n p k
  let ts := es.comp (Poly.fst code finCode)
  let hs := es.comp (stepVariablePoly hd)
  let al := (((Poly.identity code).pair (ts.comp (Poly.snd PortMachine.code natBits))).comp (searchPoly (n+1) a))
  let bl := (((wordPoly (n+1) p).pair (hs.comp (Poly.snd PortMachine.code natBits))).comp (searchPoly (n+1) b))
  let pr := es.comp (Poly.snd code finCode)
  exact (ts.pair (pr.pair (al.pair bl))).comp (acceptsVariablePoly hd)

 theorem edgeTest_source {d : ℕ} (n : ℕ) (p : Fin (n+1) → Fin d)
    (a b : PaddedLabel (Fin d) (n+1) GraphTables.Label) (k : Fin (n+1)) (s : WalkMachine.State d) :
    edgeTest n p a b k (forget s) =
      PortTables.accepts s.1.2 (edgeAt (PortTables.portGraph s.1.2) n (s.2,p) k)
        (decode (finitePortSelector (PortTables.portGraph s.1.2) (n+1) s.2) a
          (tailFromStart (PortTables.portGraph s.1.2) n (s.2,p) k))
        (decode (finitePortSelector (PortTables.portGraph s.1.2) (n+1)
          (endpoint (PortTables.portGraph s.1.2) (s.2,p))) b
          (headFromEnd (PortTables.portGraph s.1.2) n (s.2,p) k)) := by
  simp only [edgeTest,edge_forget,step_forget,word_forget,search_forget,accepts_forget]
  rcases s with ⟨T,v⟩
  exact congrArg₂ (PortTables.accepts T.2 (edgeAt (PortTables.portGraph T.2) n (v,p) k))
    (AddressMachine.search_decode T (n+1) v
      (tailFromStart (PortTables.portGraph T.2) n (v,p) k) a)
    (AddressMachine.search_decode T (n+1) (endpoint (PortTables.portGraph T.2) (v,p))
      (headFromEnd (PortTables.portGraph T.2) n (v,p) k) b)

def path {d : ℕ} (n : ℕ) (p : Fin (n+1) → Fin d)
    (a b : PaddedLabel (Fin d) (n+1) GraphTables.Label) (s : State d) : Bool :=
  decide (∀ k, edgeTest n p a b k s=true)
noncomputable def pathPoly {d : ℕ} (hd : 0<d) (n : ℕ) (p : Fin (n+1) → Fin d)
    (a b : PaddedLabel (Fin d) (n+1) GraphTables.Label) :
    Poly (code (d := d)) boolBits (path n p a b) :=
  (Poly.finiteAll code _ (edgeTestPoly hd n p a b)).congr (fun _ => by
    apply Bool.eq_iff_iff.mpr
    simp only [path,decide_eq_true_iff])

end VertexCover.Machine.NatPathMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Padding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine.PaddingMachine
open UniqueGames.Foundations.PCP
open PortMachine TableMachine PreprocessingPaddingTables

abbrev Input (q : ℕ) := PortTables.Input q

def padded {q : ℕ} (T : Input q) : Input q :=
  ⟨PreprocessingLevels.paddedSize T.1,pad T.2 (PreprocessingLevels.le_paddedSize T.1)⟩

def reverse {q : ℕ} (x : Input q × ℕ) : ℕ :=
  if x.2 < x.1.1*q then (x.1.2.reverseIndex.toList.map Fin.val).getD x.2 0 else x.2

def relation {q : ℕ} (x : Input q × ℕ) : GraphTables.RelationTable :=
  if x.2 < x.1.1*q then x.1.2.relations.toList.getD x.2 relationDefault else RegularMachine.trueRelation

noncomputable def testPoly {q : ℕ} : Poly (prodBits (code (q := q)) natBits) boolBits
    (fun x => decide (x.2 < x.1.1*q)) := by
  let n := ((Poly.fst (code (q := q)) natBits).comp verticesPoly).pair (Poly.const _ natBits q)
  exact ((Poly.snd code natBits).pair (n.comp Poly.natMul)).comp Poly.natLt

noncomputable def reversePoly {q : ℕ} : Poly (prodBits (code (q := q)) natBits) natBits reverse :=
  testPoly.ite PortMachine.reversePoly (Poly.snd code natBits) |>.congr (fun _ => by
    simp only [reverse,decide_eq_true_eq])

noncomputable def relationPoly {q : ℕ} : Poly (prodBits (code (q := q)) natBits) relationCode relation :=
  testPoly.ite PortMachine.relationPoly (Poly.const _ relationCode RegularMachine.trueRelation) |>.congr
    (fun _ => by simp only [relation,decide_eq_true_eq])

 theorem reverse_source {q : ℕ} (T : Input q) (i : Fin ((padded T).1*q)) :
    reverse (T,i.val) = (padded T).2.reverseIndex[i].val := by
  let h := PreprocessingLevels.le_paddedSize T.1
  let E := (Equiv.prodCongr (vertexEquiv h) (Equiv.refl (Fin q))).trans (PortTables.rowIndex _ q)
  obtain ⟨⟨v,p⟩,rfl⟩ := E.surjective i
  cases v with
  | inl v =>
    have hi : (E (Sum.inl v,p)).val = (PortTables.rowIndex T.1 q (v,p)).val := rfl
    dsimp only [reverse]
    conv_lhs => rw [hi,ite_eq_left (PortTables.rowIndex T.1 q (v,p)).isLt,PortMachine.reverse_valid]
    change _ = (pad T.2 h).reverseIndex[PortTables.rowIndex _ q (v.castLE h,p)].val
    rw [reverseIndex_pad_old]
    exact (congrArg Fin.val (PortTables.rowIndex_rotation T.2 (v,p))).symm
  | inr v =>
    have hi : T.1*q ≤ (E (Sum.inr v,p)).val := by
      change T.1*q ≤ p.val+q*(T.1+v.val)
      nlinarith
    dsimp only [reverse]
    rw [ite_eq_right (by omega)]
    change _ = (pad T.2 h).reverseIndex[PortTables.rowIndex _ q (vertexEquiv h (Sum.inr v),p)].val
    rw [reverseIndex_pad_new]
    rfl

 theorem relation_source {q : ℕ} (T : Input q) (i : Fin ((padded T).1*q)) :
    relation (T,i.val) = (padded T).2.relations[i] := by
  let h := PreprocessingLevels.le_paddedSize T.1
  let E := (Equiv.prodCongr (vertexEquiv h) (Equiv.refl (Fin q))).trans (PortTables.rowIndex _ q)
  obtain ⟨⟨v,p⟩,rfl⟩ := E.surjective i
  cases v with
  | inl v =>
    have hi : (E (Sum.inl v,p)).val = (PortTables.rowIndex T.1 q (v,p)).val := rfl
    dsimp only [relation]
    conv_lhs => rw [hi,ite_eq_left (PortTables.rowIndex T.1 q (v,p)).isLt,PortMachine.relation_valid]
    exact (relations_pad_old T.2 h v p).symm
  | inr v =>
    have hi : T.1*q ≤ (E (Sum.inr v,p)).val := by
      change T.1*q ≤ p.val+q*(T.1+v.val)
      nlinarith
    dsimp only [relation]
    rw [ite_eq_right (by omega)]
    change RegularMachine.trueRelation =
      (pad T.2 h).relations[PortTables.rowIndex _ q (vertexEquiv h (Sum.inr v),p)]
    apply Vector.ext
    intro index indexBound
    let labels := GraphTables.relationIndex.symm ⟨index,indexBound⟩
    have agreement := (accepts_pad_new T.2 h v p labels.1 labels.2).symm
    have true_value : GraphTables.relationAt RegularMachine.trueRelation labels.1 labels.2 = true := by
      rw [RegularMachine.trueRelation,GraphTables.relationAt_relationOf]
    rw [← true_value] at agreement
    simpa only [PortTables.accepts,GraphTables.relationAt,labels,Prod.eta,
      Equiv.apply_symm_apply,Fin.getElem_fin]
      using agreement

noncomputable def poly {q : ℕ} : Poly (code (q := q)) code padded := by
  let zero : Input q := ⟨0,PortTables.ofPortGraph
    {rot := Equiv.refl _,rot_involutive := fun _ => rfl} (fun _ _ _ => true) (fun _ _ _ => rfl)⟩
  exact materializePoly code zero padded (PortMachine.verticesPoly.comp ExpandMachine.paddedSizePoly)
    reversePoly relationPoly reverse_source relation_source

end VertexCover.Machine.PaddingMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_PowerLC
attribute [-instance] _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine.FixedLC

variable {a b : ℕ}

noncomputable def powerRowPoly (_ha : 0<a) (hb : 0<b) (n : ℕ) :
    Poly (prodBits (code (a := a) (b := b)) natBits) rowCode (powerRow hb n) := by
  let enc := prodBits (code (a := a) (b := b)) natBits
  let I := Poly.fst (code (a := a) (b := b)) natBits
  let e := Poly.snd (code (a := a) (b := b)) natBits
  let count := I.comp (MPoly hb)
  let row (i : Fin n) :=
    (I.pair (((e.pair (count.comp (Poly.natPow i.val))).comp Poly.natDiv).pair count |>.comp Poly.natMod)).comp (lookupPoly hb)
  let left := Poly.finiteSum enc (fun p (i : Fin n) =>
      (lookup hb (p.1,p.2/p.1.M^i.val%p.1.M)).1.1*p.1.u^i.val)
    (fun i => ((((row i).comp (Poly.fst (prodBits natBits natBits) mapCode)).comp
      (Poly.fst natBits natBits)).pair ((I.comp uPoly).comp (Poly.natPow i.val)) |>.comp Poly.natMul))
  let right := Poly.finiteSum enc (fun p (i : Fin n) =>
      (lookup hb (p.1,p.2/p.1.M^i.val%p.1.M)).1.2*p.1.v^i.val)
    (fun i => ((((row i).comp (Poly.fst (prodBits natBits natBits) mapCode)).comp
      (Poly.snd natBits natBits)).pair ((I.comp vPoly).comp (Poly.natPow i.val)) |>.comp Poly.natMul))
  let maps := Poly.finFunction enc n (fun p i => (lookup hb (p.1,p.2/p.1.M^i.val%p.1.M)).2)
    (fun i => (row i).comp (Poly.snd (prodBits natBits natBits) mapCode))
  exact (left.pair right).pair (maps.comp (Poly.finite _ _ (finiteCode_injective _) (powerMap n)))
noncomputable def powerPoly (ha : 0<a) (hb : 0<b) (n : ℕ) :
    Poly (code (a := a) (b := b)) code (power n) :=
  materializePoly code (one ha hb) (power n) (pow_pos hb _)
    (uPoly.comp (Poly.natPow n)) (vPoly.comp (Poly.natPow n))
    ((MPoly hb).comp (Poly.natPow n)) (powerRowPoly ha hb n)
    (powerRow_correct hb n)
end VertexCover.Machine.FixedLC
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine.TableMachine
open UniqueGames.Foundations.PCP
 theorem relation_ext {r s : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt r a b = GraphTables.relationAt s a b) : r=s := by
  apply Vector.ext
  intro i hi
  simpa only [GraphTables.relationAt,Prod.eta,Equiv.apply_symm_apply,Fin.getElem_fin] using
    h (GraphTables.relationIndex.symm ⟨i,hi⟩).1 (GraphTables.relationIndex.symm ⟨i,hi⟩).2
end VertexCover.Machine.TableMachine

namespace VertexCover.Machine.RegularMachine
open UniqueGames.Foundations.PCP
open TableMachine PreprocessingCloudIndex PreprocessingRegularTables CloudMachine

abbrev degree := internalDegree+1

def flatReverse (H : BaseTable) (x : GraphTables.Table × ℕ) : ℕ :=
  let z := reversePair H (x.1,(x.2/degree,x.2%degree))
  z.2+degree*z.1

def flatRelation (x : GraphTables.Table × ℕ) : GraphTables.RelationTable :=
  relation (x.1,(x.2/degree,x.2%degree))

noncomputable def coordsPoly : Poly (prodBits tableCode natBits) inputCode
    (fun x => (x.1,(x.2/degree,x.2%degree))) := by
  let t := Poly.fst tableCode natBits
  let i := Poly.snd tableCode natBits
  let p := i.pair (Poly.const _ natBits degree)
  exact t.pair ((p.comp Poly.natDiv).pair (p.comp Poly.natMod))

noncomputable def flatReversePoly (H : BaseTable) :
    Poly (prodBits tableCode natBits) natBits (flatReverse H) := by
  let r := coordsPoly.comp (reversePairPoly H)
  let v := r.comp (Poly.fst natBits natBits)
  let p := r.comp (Poly.snd natBits natBits)
  exact (p.pair (((Poly.const _ natBits degree).pair v).comp Poly.natMul)).comp Poly.natAdd

noncomputable def flatRelationPoly : Poly (prodBits tableCode natBits) relationCode flatRelation :=
  coordsPoly.comp relationPoly

def regularData (H : BaseTable) (T : GraphTables.Table) : PortMachine.Data :=
  let n := PreprocessingTables.regularVertices T
  (n,((List.range (n*degree)).map (fun i => flatReverse H (T,i)),
      (List.range (n*degree)).map (fun i => flatRelation (T,i))))

noncomputable def regularLengthPoly : Poly tableCode natBits
    (fun T => PreprocessingTables.regularVertices T*degree) :=
  (regularVerticesPoly.pair (Poly.const tableCode natBits degree)).comp Poly.natMul

noncomputable def reverseListPoly (H : BaseTable) : Poly tableCode (listBits natBits)
    (fun T => (List.range (PreprocessingTables.regularVertices T*degree)).map (fun i => flatReverse H (T,i))) :=
  Poly.tabulate tableCode natBits TableMachine.emptyTable 0 regularLengthPoly (flatReversePoly H)

noncomputable def relationListPoly : Poly tableCode (listBits relationCode)
    (fun T => (List.range (PreprocessingTables.regularVertices T*degree)).map (fun i => flatRelation (T,i))) :=
  Poly.tabulate tableCode relationCode TableMachine.emptyTable relationDefault regularLengthPoly flatRelationPoly

noncomputable def regularDataPoly (H : BaseTable) :
    Poly tableCode PortMachine.dataCode (regularData H) :=
  regularVerticesPoly.pair ((reverseListPoly H).pair relationListPoly)

end VertexCover.Machine.RegularMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_SimpleLC
attribute [-instance] _root_.OAI.VertexCover.Machine.GraphMachine.descriptorFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                    
section

namespace VertexCover.Machine.SimpleLC
open UniqueGames.Foundations
open FormulaParser InitialTable ClauseProjection

noncomputable def sigCode : Signature → List Bool :=
  prodBits (finiteCode (Fin 3 → Bool)) (finiteCode (Fin 3 × Fin 3 → Bool))

noncomputable def signaturePoly : Poly unaryClauseCode sigCode signature := by
  let litAt (k : Fin 3) := ((Poly.identity unaryClauseCode).pair
    (Poly.const unaryClauseCode (finCode (n := 3)) k)).comp litPoly
  let signs := Poly.finiteFunction unaryClauseCode (fun cs k => (lit cs k).1)
    (fun k => ((litAt k).comp (Poly.fst boolBits natBits)).comp
      (Poly.finiteRecode boolBits boolBits_injective))
  let equalities := Poly.finiteFunction unaryClauseCode
    (fun cs (kl : Fin 3 × Fin 3) => decide ((lit cs kl.1).2=(lit cs kl.2).2))
    (fun kl => ((((litAt kl.1).comp (Poly.snd boolBits natBits)).pair
      ((litAt kl.2).comp (Poly.snd boolBits natBits))).comp Poly.natBEq).comp
        (Poly.finiteRecode boolBits boolBits_injective))
  exact signs.pair equalities

noncomputable def relationPoly : Poly (prodBits sigCode (finCode (n := 3)))
    (FixedLC.mapCode (a := 7) (b := 2)) (fun p => relation p.1 p.2) :=
  Poly.finite _ _ (prodBits_injective
    (prodBits_injective (finiteCode_injective _) (finiteCode_injective _)) (finCode_injective 3)) _
noncomputable def rowPoly : Poly (prodBits FormulaParser.dataCode natBits) FixedLC.rowCode row := by
  let enc := prodBits FormulaParser.dataCode natBits
  let F := Poly.fst FormulaParser.dataCode natBits
  let i := Poly.snd FormulaParser.dataCode natBits
  let j := (i.pair (Poly.const enc natBits 3)).comp Poly.natDiv
  let k := i.comp (Poly.finMod 3 (by decide))
  let rows := F.comp (Poly.snd natBits (listBits unaryClauseCode))
  let cs := (j.pair rows).comp (Poly.listGetD unaryClauseCode clauseDefault)
  exact ((j.pair (((cs.pair k).comp litPoly).comp (Poly.snd boolBits natBits))).pair
    (((cs.comp signaturePoly).pair k).comp relationPoly)).congr (fun p => by
      simp only [Function.comp_apply,row,List.headD_eq_head?_getD,List.head?_drop,
        List.getD_eq_getElem?_getD])

end VertexCover.Machine.SimpleLC
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_TableCodeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP
namespace TableMachine
 theorem size_le_code (T : GraphTables.Table) : T.vertices+T.darts ≤ (tableCode T).length := by
  have h := list_length_le_bits rowCode (T.rows.toList.map rowData)
  simp only [List.length_map,Vector.length_toList] at h
  simp only [tableCode,dataCode,tableData,prodBits,pairBits_length,natBits_length]
  omega
 theorem rowLength_le {n m : ℕ} (r : GraphTables.DartRow n m) :
    (rowCode (rowData r)).length ≤ 4100*(n+m+1) := by
  have ht := r.tail.isLt
  have hr := r.reverseIndex.isLt
  simp only [rowCode,rowData,prodBits,pairBits_length,natBits_length,relationCode_length]
  omega
 theorem codeLength_le (T : GraphTables.Table) :
    (tableCode T).length ≤ 10000*(T.vertices+T.darts+1)^2 := by
  have h := listBits_length_le rowCode (T.rows.toList.map rowData) (4100*(T.vertices+T.darts+1)) (by
    intro a ha
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp ha
    exact rowLength_le r)
  simp only [List.length_map,Vector.length_toList] at h
  have hm : T.darts ≤ T.vertices+T.darts := Nat.le_add_left _ _
  have hp := Nat.mul_le_mul_right (2*(4100*(T.vertices+T.darts+1))+2) hm
  simp only [tableCode,dataCode,tableData,prodBits,pairBits_length,natBits_length]
  nlinarith
 theorem codeLength_le_eval (T : GraphTables.Table) :
    (tableCode T).length ≤ lengthPolynomial.eval (T.vertices+T.darts) := by
  simpa only [lengthPolynomial,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using codeLength_le T
end TableMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end


