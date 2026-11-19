-- Prove2me | solution 1 for APSCounting893.Main.native_modular_jacobian_verification
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T19:17:04.174696+00:00
-- url     : https://prove2.me/submissions/b70b183a-3c5e-4de2-b419-e65ff48498f1

import Definitions.Def_APSCounting893_Main_ModularJacobianComputation
import Definitions.Def_APSCounting893_Main_ModularJacobianData
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
import Mathlib
import Mathlib.Algebra.DualNumber
import Mathlib.Data.Nat.Size
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_modAdd : ComputableTidilyInPolyTime
    (fun q : ℕ × (ℕ × ℕ) => modAdd q.1 q.2.1 q.2.2)
    (encPair encNat (encPair encNat encNat)) encNat := by
  have hi := id' (encIn:=encPair encNat (encPair encNat encNat))
  exact binary_mod' (binary_add' hi.snd'.fst' hi.snd'.snd') hi.fst'

lemma native_modMul : ComputableTidilyInPolyTime
    (fun q : ℕ × (ℕ × ℕ) => modMul q.1 q.2.1 q.2.2)
    (encPair encNat (encPair encNat encNat)) encNat := by
  have hi := id' (encIn:=encPair encNat (encPair encNat encNat))
  exact binary_mod' (binary_mul' hi.snd'.fst' hi.snd'.snd') hi.fst'

lemma native_modSub : ComputableTidilyInPolyTime
    (fun q : ℕ × (ℕ × ℕ) => modSub q.1 q.2.1 q.2.2)
    (encPair encNat (encPair encNat encNat)) encNat := by
  have hi := id' (encIn:=encPair encNat (encPair encNat encNat))
  have hp := hi.fst'
  exact binary_mod' (binary_sub' (binary_add' (binary_mod' hi.snd'.fst' hp) hp)
    (binary_mod' hi.snd'.snd' hp)) hp

lemma native_modSigned : ComputableTidilyInPolyTime
    (fun q : ℕ × (Bool × ℕ) => modSigned q.1 q.2)
    (encPair encNat (encPair encBool encNat)) encNat := by
  have hi := id' (encIn:=encPair encNat (encPair encBool encNat))
  have hnegative := native_modSub.comp (hi.fst'.prod ((const 0).prod hi.snd'.snd'))
  have hpositive := binary_mod' hi.snd'.snd' hi.fst'
  exact hi.snd'.fst'.cond hnegative hpositive

lemma native_residueJetAdd : ComputableTidilyInPolyTime
    (fun q : ℕ × (ResidueJet × ResidueJet) => residueJetAdd q.1 q.2.1 q.2.2)
    (encPair encNat (encPair encResidueJet encResidueJet)) encResidueJet := by
  have hi := id' (encIn:=encPair encNat (encPair encResidueJet encResidueJet))
  exact (native_modAdd.comp (hi.fst'.prod (hi.snd'.fst'.fst'.prod hi.snd'.snd'.fst'))).prod
    (native_modAdd.comp (hi.fst'.prod (hi.snd'.fst'.snd'.prod hi.snd'.snd'.snd')))

lemma native_residueJetSub : ComputableTidilyInPolyTime
    (fun q : ℕ × (ResidueJet × ResidueJet) => residueJetSub q.1 q.2.1 q.2.2)
    (encPair encNat (encPair encResidueJet encResidueJet)) encResidueJet := by
  have hi := id' (encIn:=encPair encNat (encPair encResidueJet encResidueJet))
  exact (native_modSub.comp (hi.fst'.prod (hi.snd'.fst'.fst'.prod hi.snd'.snd'.fst'))).prod
    (native_modSub.comp (hi.fst'.prod (hi.snd'.fst'.snd'.prod hi.snd'.snd'.snd')))

lemma native_residueJetMul : ComputableTidilyInPolyTime
    (fun q : ℕ × (ResidueJet × ResidueJet) => residueJetMul q.1 q.2.1 q.2.2)
    (encPair encNat (encPair encResidueJet encResidueJet)) encResidueJet := by
  have hi := id' (encIn:=encPair encNat (encPair encResidueJet encResidueJet))
  have hprod := native_modMul.comp (hi.fst'.prod (hi.snd'.fst'.fst'.prod hi.snd'.snd'.fst'))
  have hleft := native_modMul.comp (hi.fst'.prod (hi.snd'.fst'.fst'.prod hi.snd'.snd'.snd'))
  have hright := native_modMul.comp (hi.fst'.prod (hi.snd'.fst'.snd'.prod hi.snd'.snd'.fst'))
  exact hprod.prod (native_modAdd.comp (hi.fst'.prod (hleft.prod hright)))

end APSCounting893.Main
end Component_0

section Component_1
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_residueFractionAdd : ComputableTidilyInPolyTime
    (fun q : ℕ × (ResidueFraction × ResidueFraction) => residueFractionAdd q.1 q.2.1 q.2.2)
    (encPair encNat (encPair encResidueFraction encResidueFraction)) encResidueFraction := by
  unfold residueFractionAdd residueJetAdd residueJetMul modAdd modMul encResidueFraction encResidueJet
  fun_prop

lemma native_residueFractionSub : ComputableTidilyInPolyTime
    (fun q : ℕ × (ResidueFraction × ResidueFraction) => residueFractionSub q.1 q.2.1 q.2.2)
    (encPair encNat (encPair encResidueFraction encResidueFraction)) encResidueFraction := by
  unfold residueFractionSub residueJetSub residueJetMul modAdd modMul modSub encResidueFraction encResidueJet
  fun_prop

lemma native_residueFractionMul : ComputableTidilyInPolyTime
    (fun q : ℕ × (ResidueFraction × ResidueFraction) => residueFractionMul q.1 q.2.1 q.2.2)
    (encPair encNat (encPair encResidueFraction encResidueFraction)) encResidueFraction := by
  unfold residueFractionMul residueJetMul modAdd modMul encResidueFraction encResidueJet
  fun_prop

lemma native_residueFractionDiv : ComputableTidilyInPolyTime
    (fun q : ℕ × (ResidueFraction × ResidueFraction) => residueFractionDiv q.1 q.2.1 q.2.2)
    (encPair encNat (encPair encResidueFraction encResidueFraction)) encResidueFraction := by
  unfold residueFractionDiv residueJetMul modAdd modMul encResidueFraction encResidueJet
  fun_prop

end APSCounting893.Main
end Component_1

section Component_2
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_getElem_binary {α γ : Type} (encA : α ↪ Word) (encI : γ ↪ Word)
    (list : γ → List α) (index : γ → ℕ) (fallback : α)
    (hl : ComputableTidilyInPolyTime list encI (encList encA))
    (hi : ComputableTidilyInPolyTime index encI encNat) :
    ComputableTidilyInPolyTime (fun x => (list x)[index x]?) encI (encOption encA) := by
  have hlen := unary_to_binary.comp ((length_list encA).comp hl)
  have hguard := binary_lt' hi hlen
  have hget := (optionSome encA).comp (listGetD_binary fallback hl hi)
  have hh := hguard.ite_decide hget (const (none : Option α))
  apply hh.of_enc_eq
  intro x
  by_cases h : index x < (list x).length
  · simp [h,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
  · simp [h,List.getElem?_eq_none (by omega : (list x).length ≤ index x)]

end APSCounting893.Main
end Component_2

section Component_3
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_rawPointEntry : ComputableTidilyInPolyTime
    (fun q : RawAssignment × ℕ => rawPointEntry q.1 q.2)
    (encPair encRawAssignment encNat) (encPair encBool encNat) := by
  let encE := encPair encNat (encPair encBool encNat)
  have hi := id' (encIn:=encPair encRawAssignment encNat)
  have hs := fst (encPair encRawAssignment encNat) encE
  have he := snd (encPair encRawAssignment encNat) encE
  have ht := decide_eq' he.fst' hs.snd'
  have hfind := findWithInput (test:=fun (q : RawAssignment × ℕ) (e : ℕ × (Bool × ℕ)) => decide (e.1=q.2)) (encA:=encE) hi.fst' ht
  have hget := optionGetDWithInput hfind (const (0,(false,0)))
  exact hget.snd'

lemma native_rawPointResidue : ComputableTidilyInPolyTime
    (fun q : ℕ × (RawAssignment × ℕ) => rawPointResidue q.1 q.2.1 q.2.2)
    (encPair encNat (encPair encRawAssignment encNat)) encNat := by
  have hi := id' (encIn:=encPair encNat (encPair encRawAssignment encNat))
  exact native_modSigned.comp (hi.fst'.prod (native_rawPointEntry.comp hi.snd'))

lemma signedNatValue_of_int (z : ℤ) : signedNatValue (decide (z<0),z.natAbs)=z := by
  cases z <;> simp [signedNatValue] <;> omega

end APSCounting893.Main
end Component_3

section Component_4
set_option autoImplicit false
namespace APSCounting893.Main
open Turing.MultiTapeTM

end APSCounting893.Main
end Component_4

section Component_5
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_residueBinaryOperation : ComputableTidilyInPolyTime
    (fun q : (ℕ × ℕ) × (ResidueFraction × ResidueFraction) =>
      residueBinaryOperation q.1.1 q.1.2 q.2.1 q.2.2)
    (encPair (encPair encNat encNat) (encPair encResidueFraction encResidueFraction))
    encResidueFraction := by
  have hi := id' (encIn:=encPair (encPair encNat encNat) (encPair encResidueFraction encResidueFraction))
  have harg := hi.fst'.fst'.prod hi.snd'
  have ha := native_residueFractionAdd.comp harg
  have hs := native_residueFractionSub.comp harg
  have hm := native_residueFractionMul.comp harg
  have hd := native_residueFractionDiv.comp harg
  exact (decide_eq' hi.fst'.snd' (const 2)).ite_decide ha
    ((decide_eq' hi.fst'.snd' (const 3)).ite_decide hs
      ((decide_eq' hi.fst'.snd' (const 4)).ite_decide hm hd))

lemma native_residueGateBinary : ComputableTidilyInPolyTime
    (fun q : ℕ × (List ResidueFraction × RawGate) => residueGateBinary q.1 q.2.1 q.2.2)
    (encPair encNat (encPair (encList encResidueFraction) encRawGate))
    (encOption encResidueFraction) := by
  have hi := id' (encIn:=encPair encNat (encPair (encList encResidueFraction) encRawGate))
  have hl := native_getElem_binary encResidueFraction _ _ _ ((0,0),(1,0)) hi.snd'.fst' hi.snd'.snd'.snd'.fst'
  have hr := native_getElem_binary encResidueFraction _ _ _ ((0,0),(1,0)) hi.snd'.fst' hi.snd'.snd'.snd'.snd'.fst'
  have hld := optionGetDWithInput hl (const ((0,0),(1,0)))
  have hrd := optionGetDWithInput hr (const ((0,0),(1,0)))
  have hv := native_residueBinaryOperation.comp
    ((hi.fst'.prod hi.snd'.snd'.fst').prod (hld.prod hrd))
  have hsome := (optionSome encResidueFraction).comp hv
  have hguard := bool_and' hl.optionIsSome hr.optionIsSome
  exact hguard.cond hsome (const none)

lemma native_residueGateValue : ComputableTidilyInPolyTime
    (fun q : ResidueGateInput => residueGateValue q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2)
    encResidueGateInput (encOption encResidueFraction) := by
  have hi := id' (encIn:=encResidueGateInput)
  have hp := hi.fst'.fst'
  have ha := hi.fst'.snd'.fst'
  have hj := hi.fst'.snd'.snd'
  have hprior := hi.snd'.fst'
  have hg := hi.snd'.snd'
  have hpoint := native_rawPointResidue.comp (hp.prod (ha.prod hg.snd'.fst'))
  have hderiv := (decide_eq' hg.snd'.fst' hj).ite_decide
    (binary_mod' (const 1) hp) (const 0)
  have hone := binary_mod' (const 1) hp
  have hvar := (optionSome encResidueFraction).comp
    ((hpoint.prod hderiv).prod (hone.prod (const 0)))
  have hnum := native_modSigned.comp (hp.prod (hg.snd'.snd'.snd'.prod hg.snd'.fst'))
  have hden := binary_mod' hg.snd'.snd'.fst' hp
  have hconst := (optionSome encResidueFraction).comp
    ((hnum.prod (const 0)).prod (hden.prod (const 0)))
  have hbin := native_residueGateBinary.comp (hp.prod (hprior.prod hg))
  exact (decide_eq' hg.fst' (const 0)).ite_decide hvar
    ((decide_eq' hg.fst' (const 1)).ite_decide hconst hbin)

end APSCounting893.Main
end Component_5

section Component_6
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_safeModulus : ComputableTidilyInPolyTime safeModulus encNat encNat := by
  exact (binary_le' (const 2) (id' (encIn:=encNat))).ite_decide id' (const 2)

lemma native_residueCircuitStep : ComputableTidilyInPolyTime
    (fun q : (GateParameters × Option (List ResidueFraction)) × RawGate =>
      residueCircuitStep q.1.1 q.1.2 q.2)
    (encPair (encPair encGateParameters encResidueValues) encRawGate) encResidueValues := by
  let encI := encPair (encPair encGateParameters encResidueValues) encRawGate
  have hi := fst encI (encList encResidueFraction)
  have hprior := snd encI (encList encResidueFraction)
  have hpar := hi.fst'.fst'
  have hp := native_safeModulus.comp hpar.fst'
  have harg := (hp.prod hpar.snd').prod (hprior.prod hi.snd')
  have hgate := native_residueGateValue.comp harg
  have hsaved := fst (encPair encI (encList encResidueFraction)) encResidueFraction
  have hvalue := snd (encPair encI (encList encResidueFraction)) encResidueFraction
  have hlist := listAppend' (hprior.comp hsaved) (cons' hvalue (const []))
  have hsome := (optionSome (encList encResidueFraction)).comp hlist
  have hinner := optionElimWithInput
    (body:=fun (saved : ((GateParameters × Option (List ResidueFraction)) × RawGate) ×
      List ResidueFraction) (value : ResidueFraction) => some (saved.2++[value]))
    hgate (const (none : Option (List ResidueFraction))) hsome
  exact optionElimWithInput
    (body:=fun (q : (GateParameters × Option (List ResidueFraction)) × RawGate)
      (prior : List ResidueFraction) =>
        (residueGateValue (safeModulus q.1.1.1) q.1.1.2.1 q.1.1.2.2 prior q.2).elim none
          fun value => some (prior++[value]))
    ((fst (encPair encGateParameters encResidueValues) encRawGate).snd')
    (const (none : Option (List ResidueFraction))) hinner

end APSCounting893.Main
end Component_6

section Component_7
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace APSCounting893.Main
open Turing.MultiTapeTM

def ResidueJetBound (p : ℕ) (a : ResidueJet) : Prop := a.1 < p ∧ a.2 < p
def ResidueFractionBound (p : ℕ) (a : ResidueFraction) : Prop :=
  ResidueJetBound p a.1 ∧ ResidueJetBound p a.2

lemma residueJetAdd_bound (p : ℕ) (hp : 0 < p) (a b : ResidueJet) :
    ResidueJetBound p (residueJetAdd p a b) := by
  exact ⟨Nat.mod_lt _ hp,Nat.mod_lt _ hp⟩
lemma residueJetSub_bound (p : ℕ) (hp : 0 < p) (a b : ResidueJet) :
    ResidueJetBound p (residueJetSub p a b) := by
  exact ⟨Nat.mod_lt _ hp,Nat.mod_lt _ hp⟩
lemma residueJetMul_bound (p : ℕ) (hp : 0 < p) (a b : ResidueJet) :
    ResidueJetBound p (residueJetMul p a b) := by
  exact ⟨Nat.mod_lt _ hp,Nat.mod_lt _ hp⟩

lemma residueBinaryOperation_bound (p tag : ℕ) (hp : 0 < p) (a b : ResidueFraction) :
    ResidueFractionBound p (residueBinaryOperation p tag a b) := by
  unfold residueBinaryOperation
  split
  · exact ⟨residueJetAdd_bound p hp _ _,residueJetMul_bound p hp _ _⟩
  · split
    · exact ⟨residueJetSub_bound p hp _ _,residueJetMul_bound p hp _ _⟩
    · split <;> exact ⟨residueJetMul_bound p hp _ _,residueJetMul_bound p hp _ _⟩

lemma residueGateValue_bound (p : ℕ) (hp : 0 < p) (a : RawAssignment) (j : ℕ)
    (prior : List ResidueFraction) (g : RawGate) (value : ResidueFraction)
    (h : residueGateValue p a j prior g=some value) : ResidueFractionBound p value := by
  unfold residueGateValue at h
  split at h
  · cases h
    refine ⟨⟨?_,?_⟩,⟨Nat.mod_lt _ hp,hp⟩⟩
    · unfold rawPointResidue modSigned
      split <;> exact Nat.mod_lt _ hp
    · split <;> first | exact Nat.mod_lt _ hp | exact hp
  · split at h
    · cases h
      refine ⟨⟨?_,hp⟩,⟨Nat.mod_lt _ hp,hp⟩⟩
      unfold modSigned
      split <;> exact Nat.mod_lt _ hp
    · unfold residueGateBinary at h
      dsimp only at h
      split at h
      · cases h
        exact residueBinaryOperation_bound p _ hp _ _
      · contradiction

lemma residueFraction_encoding_bound (p : ℕ) (a : ResidueFraction)
    (ha : ResidueFractionBound p a) :
    (encResidueFraction a).length ≤ 9*p.bits.length+4 := by
  have hsize (v : ℕ) (hv : v < p) : v.bits.length ≤ p.bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.le_of_lt hv)
  have h1:=hsize _ ha.1.1
  have h2:=hsize _ ha.1.2
  have h3:=hsize _ ha.2.1
  have h4:=hsize _ ha.2.2
  simp only [encResidueFraction,encResidueJet,length_encPair,encNat_apply]
  omega

end APSCounting893.Main
end Component_7

section Component_8
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma safeModulus_pos (p : ℕ) : 0 < safeModulus p := by unfold safeModulus;split <;> omega

lemma safeModulus_bits (p : ℕ) : (safeModulus p).bits.length ≤ p.bits.length+2 := by
  unfold safeModulus
  split
  · omega
  · change 2 ≤ p.bits.length+2
    omega

lemma residueCircuitStep_growth (par : GateParameters) (acc : Option (List ResidueFraction))
    (g : RawGate) :
    (encResidueValues (residueCircuitStep par acc g)).length ≤
      (encResidueValues acc).length+18*par.1.bits.length+45 := by
  cases acc with
  | none => simp [residueCircuitStep,encResidueValues]
  | some prior =>
    unfold residueCircuitStep
    simp only [Option.elim_some]
    cases hv : residueGateValue (safeModulus par.1) par.2.1 par.2.2 prior g with
    | none => simp [encResidueValues]
    | some value =>
      have hb := residueFraction_encoding_bound (safeModulus par.1) value
        (residueGateValue_bound _ (safeModulus_pos _) _ _ _ _ value hv)
      have hs := safeModulus_bits par.1
      simp only [encResidueValues,Option.elim_some,encOption_some,List.length_cons,
        encList_append,encList_cons,encList_nil,List.length_append,length_frame,List.length_nil]
      omega

lemma native_residueCircuitValues : ComputableTidilyInPolyTime
    (fun q : GateParameters × List RawGate => residueCircuitValues q.1 q.2)
    (encPair encGateParameters (encList encRawGate)) encResidueValues := by
  let encI := encPair encGateParameters (encList encRawGate)
  have hi := fst (encPair encI encResidueValues) encRawGate
  have hg := snd (encPair encI encResidueValues) encRawGate
  have hstep := native_residueCircuitStep.comp ((hi.fst'.fst'.prod hi.snd').prod hg)
  apply foldlWithInput_of_bounded_growth
    (growth:=fun q : GateParameters × List RawGate => 18*q.1.1.bits.length+45) (const (some ([] : List ResidueFraction)))
    ⟨snd encGateParameters (encList encRawGate),hstep,inferInstance,inferInstance⟩
  refine ⟨PolyBounded.of_forall_le 63 1 ?_,?_⟩
  · intro q
    have hleft := length_le_encPair_left encGateParameters (encList encRawGate) q
    have hp := length_le_encPair_left encNat (encPair encRawAssignment encNat) q.1
    simp only [encNat_apply] at hp
    change (encPair encNat (encPair encRawAssignment encNat) q.1).length ≤ _ at hleft
    simp only [pow_one]
    omega
  · intro q acc g _
    exact residueCircuitStep_growth q.1 acc g

end APSCounting893.Main
end Component_8

section Component_9
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_residueCircuitOutput : ComputableTidilyInPolyTime
    (fun q : (GateParameters × List RawGate) × ℕ => residueCircuitOutput q.1.1 q.1.2 q.2)
    (encPair (encPair encGateParameters (encList encRawGate)) encNat) encResidueFraction := by
  have hi := id' (encIn:=encPair (encPair encGateParameters (encList encRawGate)) encNat)
  have hvalues := native_residueCircuitValues.comp hi.fst'
  have hlist := optionGetDWithInput hvalues (const [])
  have hget := native_getElem_binary encResidueFraction _ _ _ ((0,0),(1,0)) hlist hi.snd'
  have hmod := native_safeModulus.comp hi.fst'.fst'.fst'
  have hone := binary_mod' (const 1) hmod
  have hdefault : ComputableTidilyInPolyTime
      (fun q : (GateParameters × List RawGate) × ℕ => ((0,0),(1%safeModulus q.1.1.1,0)))
      (encPair (encPair encGateParameters (encList encRawGate)) encNat) encResidueFraction :=
    ((const 0).prod (const 0)).prod (hone.prod (const 0))
  exact optionGetDWithInput hget hdefault

lemma native_residueDerivativePair : ComputableTidilyInPolyTime
    (fun q : ℕ × ResidueFraction => residueDerivativePair q.1 q.2)
    (encPair encNat encResidueFraction) (encPair encNat encNat) := by
  unfold residueDerivativePair modSub modMul encResidueFraction encResidueJet
  fun_prop

end APSCounting893.Main
end Component_9

section Component_10
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_modularProduct : ComputableTidilyInPolyTime
    (fun q : ℕ × List ℕ => modularProduct q.1 q.2)
    (encPair encNat (encList encNat)) encNat := by
  let encI := encPair encNat (encList encNat)
  have hi := fst (encPair encI encNat) encNat
  have hv := snd (encPair encI encNat) encNat
  have hp := native_safeModulus.comp hi.fst'.fst'
  have hstep := native_modMul.comp (hp.prod (hi.snd'.prod hv))
  have hinit := binary_mod' (const 1) (native_safeModulus.comp (fst encNat (encList encNat)))
  apply foldlWithInput_of_bounded_growth (growth:=fun q : ℕ × List ℕ => q.1.bits.length+2)
    hinit ⟨snd encNat (encList encNat),hstep,inferInstance,inferInstance⟩
  refine ⟨PolyBounded.of_forall_le 3 1 ?_,?_⟩
  · intro q
    have h := length_le_encPair_left encNat (encList encNat) q
    simp only [encNat_apply] at h
    simp only [pow_one]
    omega
  · intro q state value _
    have hlt : modMul (safeModulus q.1) state value < safeModulus q.1 :=
      Nat.mod_lt _ (safeModulus_pos _)
    have hb : (modMul (safeModulus q.1) state value).bits.length ≤ (safeModulus q.1).bits.length := by
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.le_of_lt hlt)
    have hs := safeModulus_bits q.1
    simp only [encNat_apply]
    omega

lemma native_rangeBinary : ComputableTidilyInPolyTime List.range encUnary (encList encNat) := by
  have hm := (map unary_to_binary).comp range
  apply hm.of_enc_eq
  intro n
  congr 1
  exact (List.map_id (List.range n)).symm

end APSCounting893.Main
end Component_10

section Component_11
set_option autoImplicit false
namespace APSCounting893.Main
open Turing.MultiTapeTM

end APSCounting893.Main
end Component_11

section Component_12
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_residueJacobianEntry : ComputableTidilyInPolyTime
    (fun q : MatrixParameters × (ℕ × ℕ) => residueJacobianEntry q.1 q.2.1 q.2.2)
    (encPair encMatrixParameters (encPair encNat encNat)) (encPair encNat encNat) := by
  have hi := id' (encIn:=encPair encMatrixParameters (encPair encNat encNat))
  have hp := hi.fst'.fst'
  have hc := hi.fst'.snd'.fst'
  have ha := hi.fst'.snd'.snd'.fst'
  have ho := hi.fst'.snd'.snd'.snd'.fst'
  have hv := hi.fst'.snd'.snd'.snd'.snd'
  have hvar := listGetD_binary (encA:=encNat) 0 hv hi.snd'.snd'
  have hout := listGetD_binary (encA:=encNat) 0 ho hi.snd'.fst'
  have hwire := listGetD_binary (encA:=encNat) 0 hc.snd'.snd' hout
  have hparams := hp.prod (ha.prod hvar)
  have hvalue := native_residueCircuitOutput.comp ((hparams.prod hc.snd'.fst').prod hwire)
  have hh := native_residueDerivativePair.comp ((native_safeModulus.comp hp).prod hvalue)
  apply hh.of_enc_eq
  intro q
  rfl



lemma native_residueClearedEntry : ComputableTidilyInPolyTime
    (fun q : MatrixParameters × (ℕ × ℕ) => residueClearedEntry q.1 q.2.1 q.2.2)
    (encPair encMatrixParameters (encPair encNat encNat)) encNat := by
  let encI := encPair encMatrixParameters (encPair encNat encNat)
  have hi := id' (encIn:=encI)
  have hp := hi.fst'.fst'
  have hv := hi.fst'.snd'.snd'.snd'.snd'
  have hindices := native_rangeBinary.comp ((length_list encNat).comp hv)
  have hs := fst encI encNat
  have hl := snd encI encNat
  have hpair := native_residueJacobianEntry.comp (hs.fst'.prod (hs.snd'.fst'.prod hl))
  have hden := (decide_eq' hl hs.snd'.snd').ite_decide (const 1) hpair.snd'
  have hlist := mapWithInput
    (f:=fun (q : MatrixParameters × (ℕ × ℕ)) (l : ℕ) =>
      if l=q.2.2 then 1 else (residueJacobianEntry q.1 q.2.1 l).2)
    (encA:=encNat) (encB:=encNat) hindices hden
  have hprod := native_modularProduct.comp (hp.prod hlist)
  have hnum := native_residueJacobianEntry.fst'
  exact native_modMul.comp ((native_safeModulus.comp hp).prod (hnum.prod hprod))

end APSCounting893.Main
end Component_12

section Component_13
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_residueMatrixProductEntry : ComputableTidilyInPolyTime
    (fun q : (MatrixParameters × List ℕ) × (ℕ × ℕ) =>
      residueMatrixProductEntry q.1.1 q.1.2 q.2.1 q.2.2)
    (encPair (encPair encMatrixParameters (encList encNat)) (encPair encNat encNat)) encNat := by
  let encI := encPair (encPair encMatrixParameters (encList encNat)) (encPair encNat encNat)
  have hi := id' (encIn:=encI)
  have hpar := hi.fst'.fst'
  have hp := native_safeModulus.comp hpar.fst'
  have ho := hpar.snd'.snd'.snd'.fst'
  have hrange := native_rangeBinary.comp ((length_list encNat).comp ho)
  have hs := fst encI encNat
  have hl := snd encI encNat
  have hspar := hs.fst'.fst'
  have hentry := native_residueClearedEntry.comp (hspar.prod (hs.snd'.fst'.prod hl))
  have hlen := unary_to_binary.comp ((length_list encNat).comp hspar.snd'.snd'.snd'.fst')
  have hindex := binary_add' (binary_mul' hl hlen) hs.snd'.snd'
  have hinverse := listGetD_binary (encA:=encNat) 0 hs.fst'.snd' hindex
  have hterm := native_modMul.comp ((native_safeModulus.comp hspar.fst').prod (hentry.prod hinverse))
  have hterms := mapWithInput
    (f:=fun (q : (MatrixParameters × List ℕ) × (ℕ × ℕ)) (l : ℕ) =>
      modMul (safeModulus q.1.1.1) (residueClearedEntry q.1.1 q.2.1 l)
        (q.1.2.getD (l*q.1.1.2.2.2.1.length+q.2.2) 0)) hrange hterm
  exact binary_mod' (binary_sum.comp hterms) hp

lemma native_residueMatrixInverseTest : ComputableTidilyInPolyTime
    (fun q : MatrixParameters × List ℕ => residueMatrixInverseTest q.1 q.2)
    (encPair encMatrixParameters (encList encNat)) encBool := by
  let encI := encPair encMatrixParameters (encList encNat)
  let encJ := encPair encI encNat
  have hs := fst encJ encNat
  have hj := snd encJ encNat
  have hproduct := native_residueMatrixProductEntry.comp
    (hs.fst'.prod (hs.snd'.prod hj))
  have hrhs := (decide_eq' hs.snd' hj).ite_decide (const (encMid:=encNat) 1) (const 0)
  have htest := decide_eq' hproduct hrhs
  have hbase := fst encI encNat
  have hinnerList := native_rangeBinary.comp
    ((length_list encNat).comp hbase.fst'.snd'.snd'.snd'.fst')
  have hinner := allWithInput
    (test:=fun (q : (MatrixParameters × List ℕ) × ℕ) (j : ℕ) =>
      decide (residueMatrixProductEntry q.1.1 q.1.2 q.2 j = if q.2=j then 1 else 0))
    hinnerList htest
  have hi := id' (encIn:=encI)
  have houterList := native_rangeBinary.comp
    ((length_list encNat).comp hi.fst'.snd'.snd'.snd'.fst')
  exact allWithInput
    (test:=fun (q : MatrixParameters × List ℕ) (i : ℕ) =>
      (List.range q.1.2.2.2.1.length).all fun j =>
        decide (residueMatrixProductEntry q.1 q.2 i j = if i=j then 1 else 0))
    houterList hinner

end APSCounting893.Main
end Component_13

section Component_14
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma modAdd_cast (p a b : ℕ) : (modAdd p a b : ZMod p)=(a : ZMod p)+b := by
  simp [modAdd,ZMod.natCast_mod]

lemma modMul_cast (p a b : ℕ) : (modMul p a b : ZMod p)=(a : ZMod p)*b := by
  simp [modMul,ZMod.natCast_mod]

lemma modSub_cast (p a b : ℕ) (hp : 0 < p) :
    (modSub p a b : ZMod p)=(a : ZMod p)-b := by
  have hb : b%p ≤ a%p+p := by have := Nat.mod_lt b hp;omega
  simp [modSub,ZMod.natCast_mod,Nat.cast_sub hb]

lemma modSigned_cast (p : ℕ) (hp : 0 < p) (a : Bool × ℕ) :
    (modSigned p a : ZMod p) = if a.1 then -(a.2 : ZMod p) else (a.2 : ZMod p) := by
  cases a with
  | mk sign value => cases sign <;> simp [modSigned,modSub_cast, hp,ZMod.natCast_mod]

def residueJetCast (p : ℕ) (a : ResidueJet) : DualNumber (ZMod p) :=
  ((a.1 : ZMod p),(a.2 : ZMod p))

def residueFractionCast (p : ℕ) (a : ResidueFraction) :
    DualNumber (ZMod p) × DualNumber (ZMod p) :=
  (residueJetCast p a.1,residueJetCast p a.2)

lemma residueJetAdd_cast (p : ℕ) (a b : ResidueJet) :
    residueJetCast p (residueJetAdd p a b)=residueJetCast p a+residueJetCast p b := by
  apply TrivSqZeroExt.ext
  · change (modAdd p a.1 b.1 : ZMod p) = (a.1 : ZMod p) + b.1
    exact modAdd_cast p a.1 b.1
  · change (modAdd p a.2 b.2 : ZMod p) = (a.2 : ZMod p) + b.2
    exact modAdd_cast p a.2 b.2

lemma residueJetSub_cast (p : ℕ) (hp : 0 < p) (a b : ResidueJet) :
    residueJetCast p (residueJetSub p a b)=residueJetCast p a-residueJetCast p b := by
  apply TrivSqZeroExt.ext
  · change (modSub p a.1 b.1 : ZMod p) = (a.1 : ZMod p) - b.1
    exact modSub_cast p a.1 b.1 hp
  · change (modSub p a.2 b.2 : ZMod p) = (a.2 : ZMod p) - b.2
    exact modSub_cast p a.2 b.2 hp

lemma residueJetMul_cast (p : ℕ) (a b : ResidueJet) :
    residueJetCast p (residueJetMul p a b)=residueJetCast p a*residueJetCast p b := by
  apply TrivSqZeroExt.ext
  · change (modMul p a.1 b.1 : ZMod p) = (a.1 : ZMod p) * b.1
    exact modMul_cast p a.1 b.1
  · change (modAdd p (modMul p a.1 b.2) (modMul p a.2 b.1) : ZMod p) =
      (a.1 : ZMod p)*b.2+(a.2 : ZMod p)*b.1
    simp [modAdd_cast,modMul_cast]

end APSCounting893.Main
end Component_14

section Component_15
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace APSCounting893.Main

lemma residueFractionAdd_cast (p : ℕ) (a b : ResidueFraction) :
    residueFractionCast p (residueFractionAdd p a b)=
      ((residueFractionCast p a).1*(residueFractionCast p b).2+
        (residueFractionCast p b).1*(residueFractionCast p a).2,
        (residueFractionCast p a).2*(residueFractionCast p b).2) := by
  simp [residueFractionAdd,residueFractionCast,residueJetAdd_cast,residueJetMul_cast]

lemma residueFractionSub_cast (p : ℕ) (hp : 0 < p) (a b : ResidueFraction) :
    residueFractionCast p (residueFractionSub p a b)=
      ((residueFractionCast p a).1*(residueFractionCast p b).2-
        (residueFractionCast p b).1*(residueFractionCast p a).2,
        (residueFractionCast p a).2*(residueFractionCast p b).2) := by
  simp [residueFractionSub,residueFractionCast,residueJetSub_cast,residueJetMul_cast,hp]

lemma residueFractionMul_cast (p : ℕ) (a b : ResidueFraction) :
    residueFractionCast p (residueFractionMul p a b)=
      ((residueFractionCast p a).1*(residueFractionCast p b).1,
        (residueFractionCast p a).2*(residueFractionCast p b).2) := by
  simp [residueFractionMul,residueFractionCast,residueJetMul_cast]

lemma residueFractionDiv_cast (p : ℕ) (a b : ResidueFraction) :
    residueFractionCast p (residueFractionDiv p a b)=
      ((residueFractionCast p a).1*(residueFractionCast p b).2,
        (residueFractionCast p a).2*(residueFractionCast p b).1) := by
  simp [residueFractionDiv,residueFractionCast,residueJetMul_cast]

end APSCounting893.Main
end Component_15

section Component_16
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace APSCounting893.Main

lemma rawPointEntry_correct {n : ℕ} (a : List (Fin n × ℤ)) (i : Fin n) :
    signedNatValue (rawPointEntry (rawAssignmentOf a) i.val) = sparseAssignmentPoint a i := by
  induction a with
  | nil => simp [rawPointEntry,rawAssignmentOf,sparseAssignmentPoint,signedNatValue]
  | cons e a ih =>
    rcases e with ⟨j,z⟩
    by_cases h : j=i
    · subst j
      simp [rawPointEntry,rawAssignmentOf,sparseAssignmentPoint,List.lookup_cons,signedNatValue_of_int]
    · have hbeq : (i == j) = false := by
        apply Bool.eq_false_iff.mpr
        intro hh
        exact h (beq_iff_eq.mp hh).symm
      have hv : j.val ≠ i.val := by intro hh;exact h (Fin.ext hh)
      simp only [rawAssignmentOf,List.map_cons,rawPointEntry,List.find?_cons,decide_eq_false hv,
        Bool.false_eq_true,if_false,Prod.snd,sparseAssignmentPoint,List.lookup_cons]
      simpa only [hbeq,Bool.false_eq_true,rawPointEntry,rawAssignmentOf,sparseAssignmentPoint] using ih
/- simpa [h,Ne.symm h,beq_iff_eq,rawPointEntry,rawAssignmentOf,sparseAssignmentPoint] using ih -/

lemma rawPointResidue_correct {n : ℕ} (p : ℕ) (hp : 0 < p)
    (a : List (Fin n × ℤ)) (i : Fin n) :
    (rawPointResidue p (rawAssignmentOf a) i.val : ZMod p) =
      (sparseAssignmentPoint a i : ZMod p) := by
  have hcast (entry : Bool × ℕ) : (modSigned p entry : ZMod p) =
      (signedNatValue entry : ZMod p) := by
    rw [modSigned_cast p hp]
    cases entry with
    | mk sign value => cases sign <;> simp [signedNatValue]
  rw [rawPointResidue,hcast,rawPointEntry_correct]

end APSCounting893.Main
end Component_16

section Component_17
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

abbrev NumericFraction (R : Type) := R × R

def numericFractionMap {R S : Type} [CommRing R] [CommRing S] (h : R →+* S)
    (p : NumericFraction R) : NumericFraction S := (h p.1,h p.2)

def numericFractionGate {R : Type} [CommRing R] {n : ℕ} (x : Fin n → R)
    (prior : List (NumericFraction R)) : ArithmeticGate n → Option (NumericFraction R)
  | .variable i => some (x i,1)
  | .constant cs => let q:=cs.headD 0;some ((q.num : R),(q.den : R))
  | .add a b => do
      let p←prior[a]?;let q←prior[b]?;return (p.1*q.2+q.1*p.2,p.2*q.2)
  | .sub a b => do
      let p←prior[a]?;let q←prior[b]?;return (p.1*q.2-q.1*p.2,p.2*q.2)
  | .mul a b => do
      let p←prior[a]?;let q←prior[b]?;return (p.1*q.1,p.2*q.2)
  | .div a b => do
      let p←prior[a]?;let q←prior[b]?;return (p.1*q.2,p.2*q.1)

def numericCircuitValues {R : Type} [CommRing R] {n : ℕ} (x : Fin n → R)
    (C : ArithmeticCircuit n) : Option (List (NumericFraction R)) :=
  C.gates.foldl (fun acc g=>do
    let prior←acc
    let value←numericFractionGate x prior g
    return prior++[value]) (some [])

lemma numericFractionGate_integer_map {R : Type} [CommRing R] {n : ℕ} (x : Fin n → R)
    (prior : List (IntegerPolynomialPair n)) (g : ArithmeticGate n) :
    numericFractionGate x (prior.map (numericFractionMap (MvPolynomial.eval₂Hom (Int.castRingHom R) x))) g=
      (integerGateValue prior g).map (numericFractionMap (MvPolynomial.eval₂Hom (Int.castRingHom R) x)) := by
  cases g with
  | «variable» i => simp [numericFractionGate,integerGateValue,numericFractionMap]
  | constant cs => simp [numericFractionGate,integerGateValue,numericFractionMap]
  | add a b | sub a b | mul a b | div a b =>
    cases ha : prior[a]? <;> cases hb : prior[b]? <;>
      simp [numericFractionGate,integerGateValue,ha,hb,List.getElem?_map,
        numericFractionMap,IntegerPolynomialPair.add,IntegerPolynomialPair.sub,IntegerPolynomialPair.mul,IntegerPolynomialPair.div]

lemma numericCircuitValues_integer_map {R : Type} [CommRing R] {n : ℕ} (x : Fin n → R)
    (C : ArithmeticCircuit n) :
    numericCircuitValues x C=(integerCircuitValues C).map
      (List.map (numericFractionMap (MvPolynomial.eval₂Hom (Int.castRingHom R) x))) := by
  let f:=numericFractionMap (MvPolynomial.eval₂Hom (Int.castRingHom R) x)
  have hh (gs : List (ArithmeticGate n)) (acc : Option (List (IntegerPolynomialPair n))) :
      gs.foldl (fun acc g=>do
        let prior←acc
        let value←numericFractionGate x prior g
        return prior++[value]) (acc.map (List.map f))=
      (gs.foldl (fun acc g=>do
        let prior←acc
        let value←integerGateValue prior g
        return prior++[value]) acc).map (List.map f) := by
    induction gs generalizing acc with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have heq : (do
          let prior←acc.map (List.map f)
          let value←numericFractionGate x prior g
          pure (prior++[value]))=
          (do
            let prior←acc
            let value←integerGateValue prior g
            pure (prior++[value])).map (List.map f) := by
        cases acc with
        | none => rfl
        | some prior =>
          change (numericFractionGate x (prior.map f) g).bind (fun value=>some (prior.map f++[value]))=
            ((integerGateValue prior g).bind (fun value=>some (prior++[value]))).map (List.map f)
          dsimp only [f]
          rw [numericFractionGate_integer_map]
          cases integerGateValue prior g <;> simp [List.map_append,f]
      rw [heq,ih]
  exact hh C.gates (some [])

end APSCounting893.Main
end Component_17

section Component_18
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma modSigned_int_cast (p : ℕ) (hp : 0 < p) (z : ℤ) :
    (modSigned p (decide (z<0),z.natAbs) : ZMod p)=(z : ZMod p) := by
  rw [modSigned_cast p hp]
  have h := congrArg (fun t : ℤ => (t : ZMod p)) (signedNatValue_of_int z)
  simpa [signedNatValue] using h

@[simp] lemma residueJetCast_one (p : ℕ) : residueJetCast p (1%p,0)=1 := by
  apply TrivSqZeroExt.ext <;> simp [residueJetCast,ZMod.natCast_mod]

@[simp] lemma residueJetCast_zero (p : ℕ) : residueJetCast p (0,0)=0 := by
  apply TrivSqZeroExt.ext <;> simp [residueJetCast]

lemma residueGateValue_cast {n : ℕ} (p : ℕ) (hp : 0 < p) (a : List (Fin n × ℤ))
    (v : Fin n) (prior : List ResidueFraction) (g : ArithmeticGate n) :
    (residueGateValue p (rawAssignmentOf a) v.val prior g.raw).map (residueFractionCast p) =
      numericFractionGate (R:=DualNumber (ZMod p))
        (fun l => ((sparseAssignmentPoint a l : ZMod p),if l=v then 1 else 0))
        (prior.map (residueFractionCast p)) g := by
  cases g with
  | «variable» i =>
    simp only [ArithmeticGate.raw,rawVariable,residueGateValue,if_pos rfl,Option.map_some,
      numericFractionGate,residueFractionCast,residueJetCast_one,ite_true]
    congr 2
    apply TrivSqZeroExt.ext
    · exact rawPointResidue_correct p hp a i
    · by_cases h : i=v
      · subst i;simp [residueJetCast,ZMod.natCast_mod]
      · have hv : i.val ≠ v.val := by intro heq;exact h (Fin.ext heq)
        simp [residueJetCast,h,hv]
  | constant cs =>
    simp only [ArithmeticGate.raw,rawConstant,residueGateValue,show (1:ℕ)≠0 by decide,
      if_false,if_pos rfl,Option.map_some,numericFractionGate,residueFractionCast,ite_true]
    congr 2 <;> apply TrivSqZeroExt.ext <;>
      simp [residueJetCast,ZMod.natCast_mod]
    simpa using modSigned_int_cast p hp (cs.headD 0).num
  | add x y | sub x y | mul x y | div x y =>
    cases hx : prior[x]? <;> cases hy : prior[y]? <;>
      simp [ArithmeticGate.raw,rawOperation,residueGateValue,residueGateBinary,
        residueBinaryOperation,hx,hy,List.getElem?_map,numericFractionGate,
        residueFractionAdd_cast,residueFractionSub_cast,residueFractionMul_cast,
        residueFractionDiv_cast,hp]

end APSCounting893.Main
end Component_18

section Component_19
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

noncomputable def polynomialJetEvaluation {R : Type} [CommRing R] {n : ℕ}
    (x : Fin n → R) (j : Fin n) : MvPolynomial (Fin n) ℤ →+* DualNumber R where
  toFun p := ((MvPolynomial.eval₂ (Int.castRingHom R) x p,
    MvPolynomial.eval₂ (Int.castRingHom R) x (MvPolynomial.pderiv j p)) : DualNumber R)
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' p q := by
    apply TrivSqZeroExt.ext
    · change MvPolynomial.eval₂ (Int.castRingHom R) x (p+q)=_
      simp only [TrivSqZeroExt.fst_add,TrivSqZeroExt.fst_mul,TrivSqZeroExt.fst_mk,MvPolynomial.eval₂_add,MvPolynomial.eval₂_mul]
    · change MvPolynomial.eval₂ (Int.castRingHom R) x (MvPolynomial.pderiv j (p+q))=_
      simp only [TrivSqZeroExt.snd_add,TrivSqZeroExt.snd_mk,map_add,MvPolynomial.eval₂_add]
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · change MvPolynomial.eval₂ (Int.castRingHom R) x (p*q)=_
      simp only [TrivSqZeroExt.fst_add,TrivSqZeroExt.fst_mul,TrivSqZeroExt.fst_mk,MvPolynomial.eval₂_add,MvPolynomial.eval₂_mul]
    · change MvPolynomial.eval₂ (Int.castRingHom R) x (MvPolynomial.pderiv j (p*q))=_
      simp [MvPolynomial.pderiv_mul,DualNumber.snd_mul]
      <;> ring

@[simp] lemma polynomialJetEvaluation_fst {R : Type} [CommRing R] {n : ℕ}
    (x : Fin n → R) (j : Fin n) (p : MvPolynomial (Fin n) ℤ) :
    (polynomialJetEvaluation x j p).fst=MvPolynomial.eval₂ (Int.castRingHom R) x p := rfl

@[simp] lemma polynomialJetEvaluation_snd {R : Type} [CommRing R] {n : ℕ}
    (x : Fin n → R) (j : Fin n) (p : MvPolynomial (Fin n) ℤ) :
    (polynomialJetEvaluation x j p).snd=MvPolynomial.eval₂ (Int.castRingHom R) x (MvPolynomial.pderiv j p) := rfl

@[simp] lemma polynomialJetEvaluation_C {R : Type} [CommRing R] {n : ℕ}
    (x : Fin n → R) (j : Fin n) (z : ℤ) :
    polynomialJetEvaluation x j (MvPolynomial.C z)=((z:R),0) := by
  ext <;> simp

@[simp] lemma polynomialJetEvaluation_X {R : Type} [CommRing R] {n : ℕ}
    (x : Fin n → R) (j i : Fin n) :
    polynomialJetEvaluation x j (MvPolynomial.X i)=(x i,if i=j then 1 else 0) := by
  ext <;> simp
  by_cases hi : i=j
  · subst i;simp
  · simp [Pi.single_apply,Ne.symm hi,hi]

end APSCounting893.Main
end Component_19

section Component_20
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def numericCircuitOutput {R : Type} [CommRing R] {n : ℕ} (x : Fin n → R)
    (C : ArithmeticCircuit n) (j : Fin C.outputs.length) : NumericFraction R :=
  (((numericCircuitValues x C).getD [])[C.outputs[j]]?).getD (0,1)

lemma numericCircuitOutput_integer_map {R : Type} [CommRing R] {n : ℕ} (x : Fin n → R)
    (C : ArithmeticCircuit n) (j : Fin C.outputs.length) :
    numericCircuitOutput x C j=numericFractionMap (MvPolynomial.eval₂Hom (Int.castRingHom R) x) (integerCircuitOutput C j) := by
  unfold numericCircuitOutput integerCircuitOutput
  rw [numericCircuitValues_integer_map]
  cases hvals : integerCircuitValues C with
  | none => simp [numericFractionMap]
  | some vals =>
    simp only [Option.map_some,Option.getD_some,List.getElem?_map]
    cases vals[C.outputs[j]]? <;> simp [numericFractionMap]

lemma polynomialJetEvaluation_eq_eval₂Hom {R : Type} [CommRing R] {n : ℕ}
    (x : Fin n → R) (j : Fin n) :
    polynomialJetEvaluation x j=MvPolynomial.eval₂Hom (Int.castRingHom (DualNumber R))
      (fun i=>(x i,if i=j then 1 else 0)) := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [MvPolynomial.eval₂Hom_C]
  · intro i
    simp only [polynomialJetEvaluation_X,MvPolynomial.eval₂Hom_X']

lemma numericCircuitOutput_jet {R : Type} [CommRing R] {n : ℕ}
    (x : Fin n → R) (v : Fin n) (C : ArithmeticCircuit n) (j : Fin C.outputs.length) :
    numericCircuitOutput (R:=DualNumber R) (fun i=>(x i,if i=v then 1 else 0) : Fin n → DualNumber R) C j=
      numericFractionMap (polynomialJetEvaluation x v) (integerCircuitOutput C j) := by
  rw [numericCircuitOutput_integer_map (R:=DualNumber R),polynomialJetEvaluation_eq_eval₂Hom]

end APSCounting893.Main
end Component_20

section Component_21
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma residueCircuitValues_cast {n : ℕ} (p : ℕ) (hp : 2 ≤ p) (a : List (Fin n × ℤ))
    (v : Fin n) (C : ArithmeticCircuit n) :
    (residueCircuitValues (p,(rawAssignmentOf a,v.val)) (C.gates.map ArithmeticGate.raw)).map
      (List.map (residueFractionCast p)) =
      numericCircuitValues (R:=DualNumber (ZMod p))
        (fun l => ((sparseAssignmentPoint a l : ZMod p),if l=v then 1 else 0)) C := by
  let cast := residueFractionCast p
  let x : Fin n → DualNumber (ZMod p) :=
    fun l => ((sparseAssignmentPoint a l : ZMod p),if l=v then 1 else 0)
  have hg (prior : List ResidueFraction) (g : ArithmeticGate n) :=
    residueGateValue_cast p (by omega) a v prior g
  have hh (gs : List (ArithmeticGate n)) (acc : Option (List ResidueFraction)) :
      ((gs.map ArithmeticGate.raw).foldl (residueCircuitStep (p,(rawAssignmentOf a,v.val))) acc).map
        (List.map cast) =
      gs.foldl (fun st g => do
        let prior ← st
        let value ← numericFractionGate x prior g
        return prior++[value]) (acc.map (List.map cast)) := by
    induction gs generalizing acc with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      rw [ih]
      congr 1
      cases acc with
      | none => rfl
      | some prior =>
        simp only [residueCircuitStep,Option.elim_some,safeModulus,if_pos hp]
        change ((residueGateValue p (rawAssignmentOf a) v.val prior g.raw).elim none
          (fun value => some (prior++[value]))).map (List.map cast) =
          (numericFractionGate (R:=DualNumber (ZMod p)) x (prior.map cast) g).bind
            (fun value => some (prior.map cast++[value]))
        have hgg : (residueGateValue p (rawAssignmentOf a) v.val prior g.raw).map cast =
            numericFractionGate (R:=DualNumber (ZMod p)) x (prior.map cast) g := hg prior g
        rw [←hgg]
        cases residueGateValue p (rawAssignmentOf a) v.val prior g.raw <;>
          simp [cast,List.map_append]
  exact hh C.gates (some [])

end APSCounting893.Main
end Component_21

section Component_22
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def numericDerivativePair {R : Type} [CommRing R] (p : NumericFraction (DualNumber R)) : NumericFraction R :=
  (p.1.snd*p.2.fst-p.1.fst*p.2.snd,p.2.fst^2)

def numericJacobianPairs {R : Type} [CommRing R] {n k : ℕ} (x : Fin n → R) (C : ArithmeticCircuit n)
    (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) : Matrix (Fin k) (Fin k) (NumericFraction R) :=
  fun i j=>numericDerivativePair (numericCircuitOutput (R:=DualNumber R)
    (fun l=>(x l,if l=v j then 1 else 0) : Fin n → DualNumber R) C (o i))

def numericClearedMatrix {R : Type} [CommRing R] {k : ℕ} (M : Matrix (Fin k) (Fin k) (NumericFraction R)) :
    Matrix (Fin k) (Fin k) R := fun i j=>(M i j).1*∏ l ∈ Finset.univ.erase j,(M i l).2

lemma numericJacobianPairs_integer_map {R : Type} [CommRing R] {n k : ℕ} (x : Fin n → R)
    (C : ArithmeticCircuit n) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) (i j : Fin k) :
    numericJacobianPairs x C o v i j=
      numericFractionMap (MvPolynomial.eval₂Hom (Int.castRingHom R) x) (circuitJacobianIntegerPairs C o v i j) := by
  unfold numericJacobianPairs
  rw [numericCircuitOutput_jet]
  apply Prod.ext <;> simp [numericDerivativePair,numericFractionMap,circuitJacobianIntegerPairs,
    IntegerPolynomialPair.derivative]

lemma numericClearedMatrix_integer_map {R : Type} [CommRing R] {n k : ℕ} (x : Fin n → R)
    (C : ArithmeticCircuit n) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) :
    numericClearedMatrix (numericJacobianPairs x C o v)=
      (clearedIntegerMatrix (circuitJacobianIntegerPairs C o v)).map (MvPolynomial.eval₂Hom (Int.castRingHom R) x) := by
  funext i j
  simp only [numericClearedMatrix,numericJacobianPairs_integer_map,numericFractionMap,
    Matrix.map_apply,clearedIntegerMatrix,map_mul,map_prod]

lemma numericJacobianDeterminant_integer_map {R : Type} [CommRing R] {n k : ℕ} (x : Fin n → R)
    (C : ArithmeticCircuit n) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) :
    (numericClearedMatrix (numericJacobianPairs x C o v)).det=
      MvPolynomial.eval₂ (Int.castRingHom R) x (circuitJacobianIntegerMinor C o v) := by
  rw [numericClearedMatrix_integer_map]
  exact (RingHom.map_det (MvPolynomial.eval₂Hom (Int.castRingHom R) x) _).symm

lemma matrix_right_inverse_det_ne_zero {R : Type} [CommRing R] [Nontrivial R] {k : ℕ}
    (M B : Matrix (Fin k) (Fin k) R) (h : M*B=1) : M.det≠0 := by
  have hh:=congrArg Matrix.det h
  rw [Matrix.det_mul,Matrix.det_one] at hh
  intro hz
  rw [hz,zero_mul] at hh
  exact zero_ne_one hh

lemma matrix_right_inverse_iff_det_ne_zero {R : Type} [Field R] {k : ℕ}
    (M : Matrix (Fin k) (Fin k) R) : (∃ B,M*B=1) ↔ M.det≠0 := by
  constructor
  · rintro ⟨B,hB⟩;exact matrix_right_inverse_det_ne_zero M B hB
  · intro h;exact ⟨M⁻¹,Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr h)⟩

end APSCounting893.Main
end Component_22

section Component_23
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma residueCircuitOutput_cast {n : ℕ} (p : ℕ) (hp : 2 ≤ p) (a : List (Fin n × ℤ))
    (v : Fin n) (C : ArithmeticCircuit n) (o : Fin C.outputs.length) :
    residueFractionCast p (residueCircuitOutput (p,(rawAssignmentOf a,v.val))
      (C.gates.map ArithmeticGate.raw) C.outputs[o]) =
      numericCircuitOutput (R:=DualNumber (ZMod p))
        (fun l => ((sparseAssignmentPoint a l : ZMod p),if l=v then 1 else 0)) C o := by
  have hvals := residueCircuitValues_cast p hp a v C
  unfold numericCircuitOutput
  rw [←hvals]
  unfold residueCircuitOutput
  simp only [safeModulus,if_pos hp]
  cases hv : residueCircuitValues (p,(rawAssignmentOf a,v.val)) (C.gates.map ArithmeticGate.raw) with
  | none => simp [residueFractionCast]
  | some vals =>
    simp only [Option.map_some,Option.getD_some,List.getElem?_map]
    cases vals[C.outputs[o]]? <;> simp [residueFractionCast]

lemma residueDerivativePair_cast (p : ℕ) (hp : 0 < p) (f : ResidueFraction) :
    ((residueDerivativePair p f).1 : ZMod p) =
      (numericDerivativePair (residueFractionCast p f)).1 ∧
    ((residueDerivativePair p f).2 : ZMod p) =
      (numericDerivativePair (residueFractionCast p f)).2 := by
  constructor <;> simp [residueDerivativePair,numericDerivativePair,residueFractionCast,
    residueJetCast,modSub_cast,modMul_cast,hp,pow_two]

end APSCounting893.Main
end Component_23

section Component_24
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace APSCounting893.Main

lemma modularProduct_cast (p : ℕ) (hp : 2 ≤ p) (values : List ℕ) :
    (modularProduct p values : ZMod p) = (values.map (fun (v : ℕ) => (v : ZMod p))).prod := by
  have h (xs : List ℕ) (initial : ℕ) :
      ((xs.foldl (modMul p) initial : ℕ) : ZMod p) =
        (initial : ZMod p)*(xs.map (fun (v : ℕ) => (v : ZMod p))).prod := by
    induction xs generalizing initial with
    | nil => simp
    | cons v xs ih =>
      simp only [List.foldl_cons,ih,List.map_cons,List.prod_cons,modMul_cast,mul_assoc]
  simp only [modularProduct,safeModulus,if_pos hp]
  rw [h]
  simp [ZMod.natCast_mod]

end APSCounting893.Main
end Component_24

section Component_25
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def matrixParametersOf {n k : ℕ} (p : ℕ) (C : ArithmeticCircuit n) (a : List (Fin n × ℤ))
    (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) : MatrixParameters :=
  (p,(C.raw,(rawAssignmentOf a,(List.ofFn (fun i => (o i).val),List.ofFn (fun j => (v j).val)))))

lemma residueJacobianEntry_correct {n k : ℕ} (p : ℕ) (hp : 2 ≤ p) (C : ArithmeticCircuit n)
    (a : List (Fin n × ℤ)) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) (i j : Fin k) :
    ((residueJacobianEntry (matrixParametersOf p C a o v) i.val j.val).1 : ZMod p) =
      (numericJacobianPairs (fun l => (sparseAssignmentPoint a l : ZMod p)) C o v i j).1 ∧
    ((residueJacobianEntry (matrixParametersOf p C a o v) i.val j.val).2 : ZMod p) =
      (numericJacobianPairs (fun l => (sparseAssignmentPoint a l : ZMod p)) C o v i j).2 := by
  have h := residueDerivativePair_cast p (by omega)
    (residueCircuitOutput (p,(rawAssignmentOf a,(v j).val)) (C.gates.map ArithmeticGate.raw)
      C.outputs[o i])
  rw [residueCircuitOutput_cast p hp a (v j) C (o i)] at h
  simpa [residueJacobianEntry,matrixParametersOf,ArithmeticCircuit.raw,
    List.getD_eq_getElem?_getD,safeModulus,hp,numericJacobianPairs] using h

lemma residueClearedEntry_correct {n k : ℕ} (p : ℕ) (hp : 2 ≤ p) (C : ArithmeticCircuit n)
    (a : List (Fin n × ℤ)) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) (i j : Fin k) :
    (residueClearedEntry (matrixParametersOf p C a o v) i.val j.val : ZMod p) =
      numericClearedMatrix (numericJacobianPairs (fun l => (sparseAssignmentPoint a l : ZMod p)) C o v) i j := by
  let par := matrixParametersOf p C a o v
  let M := numericJacobianPairs (fun l => (sparseAssignmentPoint a l : ZMod p)) C o v
  have hnum := (residueJacobianEntry_correct p hp C a o v i j).1
  unfold residueClearedEntry
  simp only [matrixParametersOf,List.length_ofFn]
  change (modMul (safeModulus p) (residueJacobianEntry par i.val j.val).1
    (modularProduct p ((List.range k).map (fun l => if l=j.val then 1 else
      (residueJacobianEntry par i.val l).2))) : ZMod p) = _
  rw [show safeModulus p=p by simp [safeModulus,hp],modMul_cast]
  rw [modularProduct_cast p hp]
  rw [hnum]
  simp only [List.map_map,Function.comp_apply]
  have hrange {α : Type} (f : ℕ → α) (n : ℕ) :
      (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
    apply List.ext_getElem
    · simp
    · intro t ht ht'
      simp
  rw [hrange,Fin.prod_ofFn]
  unfold numericClearedMatrix
  congr 1
  have hprod : (∏ l : Fin k, ((if l.val=j.val then 1 else
      (residueJacobianEntry par i.val l.val).2 : ℕ) : ZMod p)) =
      ∏ l : Fin k, if l=j then 1 else (M i l).2 := by
    apply Finset.prod_congr rfl
    intro l _
    have hd := (residueJacobianEntry_correct p hp C a o v i l).2
    by_cases hlj : l=j
    · subst l
      simp
    · have hlval : l.val ≠ j.val := by intro heq;exact hlj (Fin.ext heq)
      simpa [hlj,hlval,par,M] using hd
  change (∏ l : Fin k, ((if l.val=j.val then 1 else
      (residueJacobianEntry par i.val l.val).2 : ℕ) : ZMod p)) =
      ∏ l ∈ Finset.univ.erase j, (M i l).2
  rw [hprod,Finset.prod_ite]
  simp only [Finset.prod_const_one,one_mul]
  apply Finset.prod_congr
  · ext l
    simp
  · intro l _
    rfl

end APSCounting893.Main
end Component_25

section Component_26
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma polynomial_integer_eval_cast {R : Type} [CommRing R] {n : ℕ} (a : Fin n → ℤ)
    (p : MvPolynomial (Fin n) ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom R) (fun i=>(a i:R)) p=(MvPolynomial.eval a p:R) := by
  simpa [Function.comp_def,MvPolynomial.eval₂_id] using
    (MvPolynomial.eval₂_comp_left (Int.castRingHom R) (RingHom.id ℤ) a p).symm

lemma numericJacobian_right_inverse_sound {n k p : ℕ} (hp : 2≤p) (C : ArithmeticCircuit n)
    (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) (a : List (Fin n × ℤ))
    (B : Matrix (Fin k) (Fin k) (ZMod p))
    (hB : numericClearedMatrix (numericJacobianPairs (fun i=>(sparseAssignmentPoint a i:ZMod p)) C o v)*B=1) :
    circuitJacobianIntegerMinor C o v≠0 := by
  letI : Fact (1<p):=⟨by omega⟩
  have hdet:=matrix_right_inverse_det_ne_zero _ B hB
  rw [numericJacobianDeterminant_integer_map,polynomial_integer_eval_cast] at hdet
  intro hz
  apply hdet
  simp [hz]

lemma numericJacobian_right_inverse_complete {n k p : ℕ} (hp : p.Prime) (C : ArithmeticCircuit n)
    (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) (a : List (Fin n × ℤ))
    (hne : (MvPolynomial.eval (sparseAssignmentPoint a) (circuitJacobianIntegerMinor C o v):ZMod p)≠0) :
    ∃ B : Matrix (Fin k) (Fin k) (ZMod p),
      numericClearedMatrix (numericJacobianPairs (fun i=>(sparseAssignmentPoint a i:ZMod p)) C o v)*B=1 := by
  letI : Fact p.Prime:=⟨hp⟩
  apply (matrix_right_inverse_iff_det_ne_zero _).mpr
  rwa [numericJacobianDeterminant_integer_map,polynomial_integer_eval_cast]

lemma numericJacobian_prime_divisor_certificate {n k p : ℕ} (hp : 2≤p) (C : ArithmeticCircuit n)
    (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) (a : List (Fin n × ℤ))
    (B : Matrix (Fin k) (Fin k) (ZMod p))
    (hB : numericClearedMatrix (numericJacobianPairs (fun i=>(sparseAssignmentPoint a i:ZMod p)) C o v)*B=1) :
    ∃ q : ℕ,q.Prime ∧ q≤p ∧
      (MvPolynomial.eval (sparseAssignmentPoint a) (circuitJacobianIntegerMinor C o v):ZMod q)≠0 := by
  obtain ⟨q,hq,hqp⟩:=Nat.exists_prime_and_dvd (show p≠1 by omega)
  letI : Fact q.Prime:=⟨hq⟩
  have hh:=congrArg Matrix.det hB
  rw [Matrix.det_mul,Matrix.det_one,numericJacobianDeterminant_integer_map,polynomial_integer_eval_cast] at hh
  have hmap:=congrArg (ZMod.castHom hqp (ZMod q)) hh
  simp only [map_mul,map_intCast,map_one] at hmap
  refine ⟨q,hq,Nat.le_of_dvd (by omega) hqp,?_⟩
  intro hz
  rw [hz,zero_mul] at hmap
  exact zero_ne_one hmap

end APSCounting893.Main
end Component_26

section Component_27
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def matrixEntryList {R : Type} {k : ℕ} (B : Matrix (Fin k) (Fin k) R) : List R :=
  (List.finRange k).flatMap (fun i=>(List.finRange k).map (B i))

def encodeModularMatrix {p k : ℕ} (B : Matrix (Fin k) (Fin k) (ZMod p)) : Word :=
  encodeList encodeNat (matrixEntryList B |>.map ZMod.val)

lemma matrixEntryList_length {R : Type} {k : ℕ} (B : Matrix (Fin k) (Fin k) R) :
    (matrixEntryList B).length=k*k := by
  simp [matrixEntryList,List.length_flatMap]

lemma flatMap_word_length_le {α : Type} (xs : List α) (f : α → Word) (M : ℕ)
    (h : ∀ x ∈ xs,(f x).length≤M) : (xs.flatMap f).length≤xs.length*M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx:=h x (by simp)
    have ht:=ih (fun y hy=>h y (by simp [hy]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith

lemma encodeModularMatrix_length {p k : ℕ} (hp : 2≤p) (B : Matrix (Fin k) (Fin k) (ZMod p)) :
    (encodeModularMatrix B).length ≤ 2*(k*k).bits.length+1+k*k*(2*p.bits.length+1) := by
  letI : NeZero p:=⟨by omega⟩
  have hbit (z : ZMod p) : z.val.bits.length≤p.bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (ZMod.val_lt z).le
  have hh:=flatMap_word_length_le ((matrixEntryList B).map ZMod.val) encodeNat (2*p.bits.length+1)
    (by
      intro a ha
      obtain ⟨z,hz,rfl⟩:=List.mem_map.mp ha
      have hzbits:=hbit z
      simp only [encodeNat,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
      omega)
  unfold encodeModularMatrix encodeList
  simp only [List.length_append,List.length_map,matrixEntryList_length]
  calc
    (encodeNat (k*k)).length+(((matrixEntryList B).map ZMod.val).flatMap encodeNat).length ≤
        (encodeNat (k*k)).length+k*k*(2*p.bits.length+1) := by
      have hlen : ((matrixEntryList B).map ZMod.val).length=k*k := by simp [matrixEntryList_length]
      rw [hlen] at hh
      omega
    _ = _ := by simp [encodeNat];omega

end APSCounting893.Main
end Component_27

section Component_28
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def inverseResidueList {p k : ℕ} (B : Matrix (Fin k) (Fin k) (ZMod p)) : List ℕ :=
  List.ofFn (fun t : Fin (k*k) =>
    (B (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2).val)

lemma inverseResidueList_length {p k : ℕ} (B : Matrix (Fin k) (Fin k) (ZMod p)) :
    (inverseResidueList B).length=k*k := by simp [inverseResidueList]

lemma inverseResidueList_getD {p k : ℕ} (B : Matrix (Fin k) (Fin k) (ZMod p)) (i j : Fin k) :
    (inverseResidueList B).getD (i.val*k+j.val) 0=(B i j).val := by
  have hlt : i.val*k+j.val < k*k := by nlinarith [i.isLt,j.isLt]
  have heq : (⟨i.val*k+j.val,hlt⟩ : Fin (k*k))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  simp only [inverseResidueList,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos hlt,Option.getD_some]
  rw [heq]
  simp

end APSCounting893.Main
end Component_28

section Component_29
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def inverseMatrixFromList (p k : ℕ) (values : List ℕ) : Matrix (Fin k) (Fin k) (ZMod p) :=
  fun i j => (values.getD (i.val*k+j.val) 0 : ZMod p)

lemma residueMatrixProductEntry_correct {n k : ℕ} (p : ℕ) (hp : 2 ≤ p) (C : ArithmeticCircuit n)
    (a : List (Fin n × ℤ)) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n)
    (inverse : List ℕ) (i j : Fin k) :
    (residueMatrixProductEntry (matrixParametersOf p C a o v) inverse i.val j.val : ZMod p) =
      (numericClearedMatrix (numericJacobianPairs (fun l => (sparseAssignmentPoint a l : ZMod p)) C o v)*
        inverseMatrixFromList p k inverse) i j := by
  let par := matrixParametersOf p C a o v
  let M := numericClearedMatrix (numericJacobianPairs (fun l => (sparseAssignmentPoint a l : ZMod p)) C o v)
  unfold residueMatrixProductEntry
  simp only [matrixParametersOf,List.length_ofFn]
  change (((List.range k).map (fun l => modMul (safeModulus p)
    (residueClearedEntry par i.val l) (inverse.getD (l*k+j.val) 0))).sum % safeModulus p : ZMod p) = _
  rw [show safeModulus p=p by simp [safeModulus,hp],ZMod.natCast_mod]
  push_cast
  rw [List.map_map]
  have hrange {α : Type} (f : ℕ → α) (r : ℕ) :
      (List.range r).map f = List.ofFn (fun t : Fin r => f t.val) := by
    apply List.ext_getElem
    · simp
    · intro t ht ht'
      simp
  rw [hrange,Fin.sum_ofFn]
  change (∑ l : Fin k, (modMul p (residueClearedEntry par i.val l.val)
    (inverse.getD (l.val*k+j.val) 0) : ZMod p)) = (M*inverseMatrixFromList p k inverse) i j
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [modMul_cast,residueClearedEntry_correct p hp C a o v i l]
  rfl

lemma residueMatrixInverseTest_iff {n k : ℕ} (p : ℕ) (hp : 2 ≤ p) (C : ArithmeticCircuit n)
    (a : List (Fin n × ℤ)) (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n)
    (inverse : List ℕ) :
    residueMatrixInverseTest (matrixParametersOf p C a o v) inverse=true ↔
      numericClearedMatrix (numericJacobianPairs (fun l => (sparseAssignmentPoint a l : ZMod p)) C o v)*
        inverseMatrixFromList p k inverse=1 := by
  let par := matrixParametersOf p C a o v
  let M := numericClearedMatrix (numericJacobianPairs (fun l => (sparseAssignmentPoint a l : ZMod p)) C o v)
  have hlen : par.2.2.2.1.length=k := by simp [par,matrixParametersOf]
  change (List.range par.2.2.2.1.length).all (fun i =>
    (List.range par.2.2.2.1.length).all fun j =>
      decide (residueMatrixProductEntry par inverse i j=if i=j then 1 else 0))=true ↔ _
  rw [hlen]
  simp only [List.all_eq_true,List.mem_range,decide_eq_true_eq]
  constructor
  · intro h
    apply Matrix.ext
    intro i j
    rw [←residueMatrixProductEntry_correct p hp C a o v inverse i j]
    rw [h i.val i.isLt j.val j.isLt]
    by_cases hij : i=j
    · subst j;simp
    · have hv : i.val≠j.val := by intro heq;exact hij (Fin.ext heq)
      simp [hij,hv,Matrix.one_apply]
  · intro h i hi j hj
    let fi : Fin k := ⟨i,hi⟩
    let fj : Fin k := ⟨j,hj⟩
    have hcast := residueMatrixProductEntry_correct p hp C a o v inverse fi fj
    rw [h] at hcast
    have heq : (residueMatrixProductEntry par inverse i j : ZMod p)=
        ((if i=j then 1 else 0 : ℕ) : ZMod p) := by
      simpa [fi,fj,par,Matrix.one_apply,Fin.ext_iff] using hcast
    have ha : residueMatrixProductEntry par inverse i j < p := by
      unfold residueMatrixProductEntry
      simpa [par,matrixParametersOf,safeModulus,hp] using
        Nat.mod_lt (((List.range par.2.2.2.1.length).map fun l =>
          modMul (safeModulus par.1) (residueClearedEntry par i l)
            (inverse.getD (l*par.2.2.2.1.length+j) 0)).sum) (show 0<p by omega)
    have hb : (if i=j then 1 else 0 : ℕ)<p := by split <;> omega
    have hm := (ZMod.natCast_eq_natCast_iff _ _ p).mp heq
    change residueMatrixProductEntry par inverse i j % p = (if i=j then 1 else 0) % p at hm
    simpa only [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using hm

end APSCounting893.Main
end Component_29

section Component_30
set_option autoImplicit false
namespace APSCounting893.Main
end APSCounting893.Main
end Component_30

open APSCounting893.Main
set_option backward.isDefEq.respectTransparency.types false
theorem solution :
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun q : MatrixParameters × List ℕ => residueMatrixInverseTest q.1 q.2)
      (Turing.MultiTapeTM.encPair encMatrixParameters (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat))
      Turing.MultiTapeTM.encBool ∧
    (∀ (n k p : ℕ) (hp : 2 ≤ p) (C : ArithmeticCircuit n) (a : List (Fin n × ℤ))
      (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) (inverse : List ℕ),
      residueMatrixInverseTest
        (p,(C.raw,(rawAssignmentOf a,(List.ofFn (fun i => (o i).val),List.ofFn (fun j => (v j).val)))))
        inverse = true ↔
      (clearedIntegerMatrix (circuitJacobianIntegerPairs C o v)).map
        (MvPolynomial.eval₂Hom (Int.castRingHom (ZMod p)) (fun l => (sparseAssignmentPoint a l : ZMod p)))*
        Matrix.of (fun i j : Fin k => (inverse.getD (i.val*k+j.val) 0 : ZMod p))=1)  := by
  refine ⟨native_residueMatrixInverseTest.computableInPolyTime,?_⟩
  intro n k p hp C a o v inverse
  rw [←numericClearedMatrix_integer_map]
  exact residueMatrixInverseTest_iff p hp C a o v inverse
