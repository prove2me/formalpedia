-- Prove2me | solution 1 for APSCounting893.Main.native_long_sum_carry_query
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T21:45:38.951102+00:00
-- url     : https://prove2.me/submissions/8f3d8c7b-dfd5-48de-9e56-fa564199eaf5

import Definitions.Def_APSCounting893_Main_LongSumCarryMachine
import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Basic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_binary_bit_read : ComputableTidilyInPolyTime
    (fun x : ℕ × ℕ => x.1.testBit x.2) (encPair encNat encNat) encBool := by
  have hs := Turing.MultiTapeTM.ComputableInPolyTime.binary_shiftRight.tidy
  have hm := binary_mod' hs (const 2)
  have hh := decide_eq' hm (const 1)
  apply hh.of_enc_eq
  intro x
  simp only [Nat.testBit_eq_decide_div_mod_eq,Nat.shiftRight_eq_div_pow,Function.comp_apply]

end APSCounting893.Main
end Component_0

section Component_1
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
lemma native_carryBaseValue : ComputableTidilyInPolyTime
    (fun p : ℕ × (ℕ × ℕ) => carryBaseValue p.1 p.2.1 p.2.2)
    (encPair encNat (encPair encNat encNat)) encNat := by
  have hi := id' (encIn:=encPair encNat (encPair encNat encNat))
  exact ite_decide (decide_eq' hi.snd'.fst' (const 0)) (const 0) (binary_div' hi.snd'.snd' hi.fst')

lemma native_carryGenerateTest : ComputableTidilyInPolyTime
    (fun p : ℕ × (ℕ × (ℕ × ℕ)) => carryGenerateTest p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair encNat (encPair encNat (encPair encNat encNat))) encBool := by
  have hi := id' (encIn:=encPair encNat (encPair encNat (encPair encNat encNat)))
  have hB := hi.fst'
  have hn := hi.snd'.fst'
  have hv := hi.snd'.snd'.fst'
  have hp := hi.snd'.snd'.snd'
  have hbase := native_carryBaseValue.comp (hB.prod (hn.prod hp))
  exact binary_le' hB (binary_add' (binary_mod' hv hB) hbase)

lemma native_carryPropagateTest : ComputableTidilyInPolyTime
    (fun p : ℕ × (ℕ × (ℕ × ℕ)) => carryPropagateTest p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair encNat (encPair encNat (encPair encNat encNat))) encBool := by
  have hi := id' (encIn:=encPair encNat (encPair encNat (encPair encNat encNat)))
  have hB := hi.fst'
  have hn := hi.snd'.fst'
  have hv := hi.snd'.snd'.fst'
  have hp := hi.snd'.snd'.snd'
  have hbase := native_carryBaseValue.comp (hB.prod (hn.prod hp))
  exact decide_eq' (binary_add' (binary_add' (binary_mod' hv hB) hbase) (const 1)) hB

lemma native_carryOutputTest : ComputableTidilyInPolyTime
    (fun p : ℕ × (ℕ × (ℕ × (ℕ × (ℕ × ℕ)))) =>
      carryOutputTest p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
    (encPair encNat (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))) encBool := by
  have hi := id' (encIn:=encPair encNat (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat)))))
  have hB := hi.fst'
  have hn := hi.snd'.fst'
  have hv := hi.snd'.snd'.fst'
  have hp := hi.snd'.snd'.snd'.fst'
  have hc := hi.snd'.snd'.snd'.snd'.fst'
  have hpos := hi.snd'.snd'.snd'.snd'.snd'
  have hbase := native_carryBaseValue.comp (hB.prod (hn.prod hp))
  have hvalue := binary_mod' (binary_add' (binary_add' hv hbase) hc) hB
  exact native_binary_bit_read.comp (hvalue.prod hpos)
end APSCounting893.Main
end Component_1

section Component_2
set_option autoImplicit false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
lemma native_polyBound_unary (a b : ℕ) : ComputableTidilyInPolyTime
    (polyBound a b) encUnary encUnary := by
  have hi := id' (encIn:=encUnary)
  have hplus := unary_add.comp (hi.prod (const 1))
  have hp := (unary_pow b).comp hplus
  have hh := unary_mul.comp ((const a).prod hp)
  exact hh.of_enc_eq (fun n => rfl)
end APSCounting893.Main
end Component_2

section Component_3
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
lemma native_carry_x : ComputableTidilyInPolyTime CarryMatrixInput.x encCarryMatrixInput encBits :=
  (id' (encIn:=encCarryMatrixInput)).fst'

lemma native_carry_q : ComputableTidilyInPolyTime CarryMatrixInput.q encCarryMatrixInput encNat :=
  (id' (encIn:=encCarryMatrixInput)).snd'.fst'

lemma native_carry_carry : ComputableTidilyInPolyTime CarryMatrixInput.carry encCarryMatrixInput encNat :=
  (id' (encIn:=encCarryMatrixInput)).snd'.snd'.fst'

lemma native_carry_generator : ComputableTidilyInPolyTime CarryMatrixInput.generator encCarryMatrixInput encNat :=
  (id' (encIn:=encCarryMatrixInput)).snd'.snd'.snd'.fst'

lemma native_carry_universal : ComputableTidilyInPolyTime CarryMatrixInput.universal encCarryMatrixInput encNat :=
  (id' (encIn:=encCarryMatrixInput)).snd'.snd'.snd'.snd'.fst'

lemma native_carry_counter : ComputableTidilyInPolyTime CarryMatrixInput.counter encCarryMatrixInput encNat :=
  (id' (encIn:=encCarryMatrixInput)).snd'.snd'.snd'.snd'.snd'.fst'

lemma native_carry_current : ComputableTidilyInPolyTime CarryMatrixInput.current encCarryMatrixInput encBits :=
  (id' (encIn:=encCarryMatrixInput)).snd'.snd'.snd'.snd'.snd'.snd'.fst'

lemma native_carry_previous : ComputableTidilyInPolyTime CarryMatrixInput.previous encCarryMatrixInput encBits :=
  (id' (encIn:=encCarryMatrixInput)).snd'.snd'.snd'.snd'.snd'.snd'.snd'.fst'

lemma native_carry_gen : ComputableTidilyInPolyTime CarryMatrixInput.gen encCarryMatrixInput encBits :=
  (id' (encIn:=encCarryMatrixInput)).snd'.snd'.snd'.snd'.snd'.snd'.snd'.snd'.fst'

lemma native_carry_genPrevious : ComputableTidilyInPolyTime CarryMatrixInput.genPrevious encCarryMatrixInput encBits :=
  (id' (encIn:=encCarryMatrixInput)).snd'.snd'.snd'.snd'.snd'.snd'.snd'.snd'.snd'.fst'

lemma native_carry_prop : ComputableTidilyInPolyTime CarryMatrixInput.prop encCarryMatrixInput encBits :=
  (id' (encIn:=encCarryMatrixInput)).snd'.snd'.snd'.snd'.snd'.snd'.snd'.snd'.snd'.snd'.fst'

lemma native_carry_propPrevious : ComputableTidilyInPolyTime CarryMatrixInput.propPrevious encCarryMatrixInput encBits :=
  (id' (encIn:=encCarryMatrixInput)).snd'.snd'.snd'.snd'.snd'.snd'.snd'.snd'.snd'.snd'.snd'
end APSCounting893.Main
end Component_3

section Component_4
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
lemma native_carryMatrixWidth (a b : ℕ) : ComputableTidilyInPolyTime
    (carryMatrixWidth a b) encCarryMatrixInput encUnary :=
  unary_add.comp (((native_polyBound_unary a b).comp (length_bits.comp native_carry_x)).prod (const 1))

lemma native_carryMatrixBase (a b : ℕ) : ComputableTidilyInPolyTime
    (carryMatrixBase a b) encCarryMatrixInput encNat :=
  binary_two_pow.comp (native_carryMatrixWidth a b)

lemma native_carryMatrixIndex (a b : ℕ) : ComputableTidilyInPolyTime
    (carryMatrixIndex a b) encCarryMatrixInput encNat :=
  binary_div' native_carry_q (unary_to_binary.comp (native_carryMatrixWidth a b))

lemma native_carryMatrixPosition (a b : ℕ) : ComputableTidilyInPolyTime
    (carryMatrixPosition a b) encCarryMatrixInput encNat :=
  binary_mod' native_carry_q (unary_to_binary.comp (native_carryMatrixWidth a b))

lemma native_carryMatrixGenIndex : ComputableTidilyInPolyTime
    carryMatrixGenIndex encCarryMatrixInput encNat :=
  ite_decide (decide_eq' native_carry_carry (const 1)) native_carry_generator native_carry_universal

lemma native_carryMatrixPropIndex : ComputableTidilyInPolyTime
    carryMatrixPropIndex encCarryMatrixInput encNat :=
  ite_decide (decide_eq' native_carry_carry (const 1)) native_carry_universal native_carry_counter

lemma native_carryMatrixGeneration (a b : ℕ) : ComputableTidilyInPolyTime
    (carryMatrixGeneration a b) encCarryMatrixInput encBool :=
  native_carryGenerateTest.comp ((native_carryMatrixBase a b).prod
    (native_carryMatrixGenIndex.prod ((bitsToNat.comp native_carry_gen).prod
      (bitsToNat.comp native_carry_genPrevious))))

lemma native_carryMatrixPropagation (a b : ℕ) : ComputableTidilyInPolyTime
    (carryMatrixPropagation a b) encCarryMatrixInput encBool :=
  native_carryPropagateTest.comp ((native_carryMatrixBase a b).prod
    (native_carryMatrixPropIndex.prod ((bitsToNat.comp native_carry_prop).prod
      (bitsToNat.comp native_carry_propPrevious))))

lemma native_carryMatrixOutput (a b : ℕ) : ComputableTidilyInPolyTime
    (carryMatrixOutput a b) encCarryMatrixInput encBool :=
  native_carryOutputTest.comp ((native_carryMatrixBase a b).prod
    ((native_carryMatrixIndex a b).prod ((bitsToNat.comp native_carry_current).prod
      ((bitsToNat.comp native_carry_previous).prod (native_carry_carry.prod (native_carryMatrixPosition a b))))))

lemma native_carryMatrixGuard (a b : ℕ) : ComputableTidilyInPolyTime
    (carryMatrixGuard a b) encCarryMatrixInput encBool := by
  have hmode := decide_eq' native_carry_carry (const 1)
  have hk := native_carryMatrixIndex a b
  have hJk := binary_lt' native_carry_generator hk
  have hJU := binary_lt' native_carry_generator native_carry_universal
  have hUk := binary_lt' native_carry_universal hk
  have hUL := binary_lt' native_carry_universal native_carry_counter
  have hLk := binary_lt' native_carry_counter hk
  have hg := native_carryMatrixGeneration a b
  have hp := native_carryMatrixPropagation a b
  have hpropImp := bool_or.comp ((bool_not.comp (bool_and' hJU hUk)).prod hp)
  have hone := bool_and' hg hpropImp
  have hbad := bool_and' (bool_and' hUL hLk) (bool_not.comp hp)
  have hcounter := bool_or.comp ((bool_not.comp hg).prod hbad)
  have hzero := bool_or.comp ((bool_not.comp hUk).prod hcounter)
  have hbranch := hmode.cond hone hzero
  have hJguard := bool_or.comp ((bool_not.comp hmode).prod hJk)
  have hhead := bool_and' (binary_le' native_carry_carry (const 1)) (native_carryMatrixOutput a b)
  have hh := bool_and' hhead (bool_and' hJguard hbranch)
  exact hh.of_enc_eq (fun p => rfl)
end APSCounting893.Main
end Component_4

section Component_5
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
lemma native_carryGraphWord : ComputableTidilyInPolyTime
    (fun p : Word × (ℕ × Word) => carryGraphWord p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encNat encBits)) encBits := by
  have hi := id' (encIn:=encPair encBits (encPair encNat encBits))
  have hd := bitsAppend ((bitsFrame encBits).comp hi.fst') (natBits.comp hi.snd'.fst')
  have hh := bitsAppend (const [false,false]) (bitsAppend ((bitsFrame encBits).comp hd) hi.snd'.snd')
  exact hh.of_enc_eq (fun p => rfl)
end APSCounting893.Main
end Component_5

section Component_6
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
lemma native_carryMatrixQuery (a b : ℕ) : ComputableTidilyInPolyTime
    (carryMatrixQuery a b) (encPair encCarryMatrixInput encNat) encBits := by
  have hd := fst encCarryMatrixInput encNat
  have hsel := snd encCarryMatrixInput encNat
  have hx := native_carry_x.comp hd
  have hk := (native_carryMatrixIndex a b).comp hd
  have hg := native_carryMatrixGenIndex.comp hd
  have hp := native_carryMatrixPropIndex.comp hd
  have hcall0 := native_carryGraphWord.comp (hx.prod (hk.prod (native_carry_current.comp hd)))
  have hcall1 := native_carryGraphWord.comp (hx.prod ((binary_sub' hk (const 1)).prod (native_carry_previous.comp hd)))
  have hcall2 := native_carryGraphWord.comp (hx.prod (hg.prod (native_carry_gen.comp hd)))
  have hcall3 := native_carryGraphWord.comp (hx.prod ((binary_sub' hg (const 1)).prod (native_carry_genPrevious.comp hd)))
  have hcall4 := native_carryGraphWord.comp (hx.prod (hp.prod (native_carry_prop.comp hd)))
  have hcall5 := native_carryGraphWord.comp (hx.prod ((binary_sub' hp (const 1)).prod (native_carry_propPrevious.comp hd)))
  have hcase5 := ite_decide (decide_eq' hsel (const 5)) hcall5 (const [true,true])
  have hcase4 := ite_decide (decide_eq' hsel (const 4)) hcall4 hcase5
  have hcase3 := ite_decide (decide_eq' hsel (const 3)) hcall3 hcase4
  have hcase2 := ite_decide (decide_eq' hsel (const 2)) hcall2 hcase3
  have hcase1 := ite_decide (decide_eq' hsel (const 1)) hcall1 hcase2
  have hcase0 := ite_decide (decide_eq' hsel (const 0)) hcall0 hcase1
  have hh := ((native_carryMatrixGuard a b).comp hd).cond hcase0 (const [true,false])
  exact hh.of_enc_eq (fun p => rfl)
end APSCounting893.Main
end Component_6

section Component_7

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_readWordField {α : Type} {encA : α ↪ Word} {width : α → ℕ} {word : α → Word}
    (hW : ComputableTidilyInPolyTime width encA encUnary)
    (hw : ComputableTidilyInPolyTime word encA encBits) (i : ℕ) :
    ComputableTidilyInPolyTime (fun x => readWordField (width x) i (word x)) encA encBits := by
  exact bitsTakeWithInput (bitsDropWithInput hw (unary_mul.comp ((const i).prod hW))) hW

lemma native_readNatField {α : Type} {encA : α ↪ Word} {width : α → ℕ} {word : α → Word}
    (hW : ComputableTidilyInPolyTime width encA encUnary)
    (hw : ComputableTidilyInPolyTime word encA encBits) (i : ℕ) :
    ComputableTidilyInPolyTime (fun x => readNatField (width x) i (word x)) encA encNat :=
  bitsToNat.comp (native_readWordField hW hw i)

end APSCounting893.Main
end Component_7

section Component_8
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def fastUnaryPrefix (w : Word) : Option (ℕ × Word):=
  let n:=w.idxOf false
  if n<w.length then some (n,w.drop (n+1)) else none

lemma fastUnaryPrefix_eq_readUnary (w : Word) : fastUnaryPrefix w=readUnary w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false => simp [fastUnaryPrefix,readUnary]
    | true =>
      unfold fastUnaryPrefix at ih ⊢
      simp only [List.idxOf_cons_ne w (show (true:Bool)≠false by decide),List.length_cons]
      rw [readUnary,←ih]
      by_cases h : w.idxOf false<w.length
      · simp [h,List.drop_succ_cons]
      · simp [h,List.drop_succ_cons]

lemma native_fastUnaryPrefix :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime fastUnaryPrefix Turing.MultiTapeTM.encBits
      (Turing.MultiTapeTM.encOption (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encBits)) := by
  open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  have hlist := bitsToList
  open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  have hidx : ComputableTidilyInPolyTime (fun w : Word=>w.idxOf false) encBits encUnary :=
    (idxOf encBool).comp (hlist.prod (const false))
  open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  have hlen : ComputableTidilyInPolyTime (fun w : Word=>w.length) encBits encUnary:=length_bits
  open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  have hnext := unary_add.comp (hidx.prod (const 1))
  open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  have hrest := bitsDropWithInput (id' (encIn:=encBits)) hnext
  open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  have hguard := binary_lt' (unary_to_binary.comp hidx) (unary_to_binary.comp hlen)
  open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  have hsome := (optionSome (encPair encUnary encBits)).comp (hidx.prod hrest)
  open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime in
  exact hguard.ite_decide hsome (const none)

end APSCounting893.Main
end Component_8

section Component_9
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma apsCanonicalBits_append_singleton (w : Word) (b : Bool) : canonicalBits (w++[b])=b := by
  induction w with
  | nil => rfl
  | cons a w ih => cases w with
    | nil => rfl
    | cons c w => exact ih

lemma apsCanonicalBits_reverse_getD (w : Word) : canonicalBits w=w.reverse.getD 0 true := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w b ih => simp [apsCanonicalBits_append_singleton]

lemma native_apsCanonicalBits : ComputableTidilyInPolyTime canonicalBits encBits encBool := by
  have hh:=bitsGetDWithInput bitsReverse (const 0) true
  apply hh.of_enc_eq
  intro w
  rw [apsCanonicalBits_reverse_getD]


def fastBinaryPayload (p : ℕ × Word) : Option (ℕ × Word):=
  if p.1≤p.2.length then
    if canonicalBits (p.2.take p.1) then some (ofBits (p.2.take p.1),p.2.drop p.1) else none
  else none

lemma native_fastBinaryPayload : ComputableTidilyInPolyTime fastBinaryPayload
    (encPair encUnary encBits) (encOption (encPair encNat encBits)) := by
  have hn:=fst encUnary encBits
  have hw:=snd encUnary encBits
  have hlength:=length_bits.comp hw
  have hguard:=binary_le' (unary_to_binary.comp hn) (unary_to_binary.comp hlength)
  have htake:=bitsTakeWithInput hw hn
  have hdrop:=bitsDropWithInput hw hn
  have hvalue:=bitsToNat.comp htake
  have hcanon:=native_apsCanonicalBits.comp htake
  have hsome:=(optionSome (encPair encNat encBits)).comp (hvalue.prod hdrop)
  have hinner:=hcanon.cond hsome (const none)
  exact hguard.ite_decide hinner (const none)

lemma fastBinaryPayload_eq (p : ℕ × Word) : fastBinaryPayload p=
    if p.1≤p.2.length then
      if canonicalBits (p.2.take p.1) then some (bitsValue (p.2.take p.1),p.2.drop p.1) else none
    else none := rfl

end APSCounting893.Main
end Component_9

section Component_10
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

lemma native_decodeNat : ComputableTidilyInPolyTime decodeNat encBits
    (encOption (encPair encNat encBits)) := by
  have hbody:=native_fastBinaryPayload.comp (snd encBits (encPair encUnary encBits))
  have hh:=optionElimWithInput (body:=fun (_ : Word) (p : ℕ × Word)=>fastBinaryPayload p)
    native_fastUnaryPrefix (const (none : Option (ℕ × Word))) hbody
  apply hh.of_enc_eq
  intro w
  rw [fastUnaryPrefix_eq_readUnary]
  unfold decodeNat
  cases hp : readUnary w with
  | none => rfl
  | some p =>
    simp only [Option.elim_some,fastBinaryPayload_eq]
    rfl

end APSCounting893.Main
end Component_10

section Component_11
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
lemma native_parseNaturalBitQuery : ComputableTidilyInPolyTime parseNaturalBitQuery encBits
    (encOption (encPair encBits encNat)) := by
  have hdecode := native_decodeNat.comp ComputableTidilyInPolyTime.dropFrame
  have hs := fst encBits (encPair encNat encBits)
  have hqr := snd encBits (encPair encNat encBits)
  have htail := decide_eq' hqr.snd' (const [])
  have hcode := bitsAppend ((bitsFrame encBits).comp (ComputableTidilyInPolyTime.unframe.comp hs))
    (ComputableTidilyInPolyTime.dropFrame.comp hs)
  have hguard := decide_and htail (decide_eq' hs hcode)
  have hresult := (optionSome (encPair encBits encNat)).comp
    ((ComputableTidilyInPolyTime.unframe.comp hs).prod hqr.fst')
  have hbody := ite_decide hguard hresult (const (none : Option (Word × ℕ)))
  have hh := optionElimWithInput
    (body:=fun (z : Word) (qr : ℕ × Word) =>
      if qr.2=[] ∧ z=Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe z)++Turing.MultiTapeTM.dropFrame z
        then some (Turing.MultiTapeTM.unframe z,qr.1) else none)
    hdecode (const (none : Option (Word × ℕ))) hbody
  apply hh.of_enc_eq
  intro z
  unfold parseNaturalBitQuery
  dsimp only [Function.comp_apply]
  cases decodeNat (Turing.MultiTapeTM.dropFrame z) <;> rfl
end APSCounting893.Main
end Component_11

section Component_12
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
lemma native_longSumMatrixData (a b : ℕ) : ComputableTidilyInPolyTime
    (fun p : Word × (Word × ℕ) => longSumMatrixData a b p.1 p.2)
    (encPair encBits (encPair encBits encNat)) encCarryMatrixInput := by
  have hz := fst encBits (encPair encBits encNat)
  have hparsed := snd encBits (encPair encBits encNat)
  have hu1 := unframe.comp hz
  have hu2 := unframe.comp hu1
  have hu3 := unframe.comp hu2
  have hroot := unframe.comp hu3
  have hout := dropFrame.comp hu3
  have hU := dropFrame.comp hu2
  have hin := dropFrame.comp hu1
  have hW := (native_polyBound_unary (2*a+3) (b+1)).comp (length_bits.comp hroot)
  have hh := hparsed.fst'.prod (hparsed.snd'.prod
    ((native_readNatField hW hout 0).prod ((native_readNatField hW hout 1).prod
    ((native_readNatField hW hU 0).prod ((native_readNatField hW hin 0).prod
    ((native_readWordField hW hout 2).prod ((native_readWordField hW hout 3).prod
    ((native_readWordField hW hin 1).prod ((native_readWordField hW hin 2).prod
    ((native_readWordField hW hin 3).prod (native_readWordField hW hin 4)))))))))))
  exact hh.of_enc_eq (fun p => rfl)

lemma native_longSumMatrixQuery (a b : ℕ) : ComputableTidilyInPolyTime
    (longSumMatrixQuery a b) encBits encBits := by
  have hi := id' (encIn:=encBits)
  have hroot := ComputableTidilyInPolyTime.unframe.comp (ComputableTidilyInPolyTime.unframe.comp (ComputableTidilyInPolyTime.unframe.comp ComputableTidilyInPolyTime.unframe))
  have hparse := native_parseNaturalBitQuery.comp hroot
  have hz := fst encBits (encPair encBits encNat)
  have hsel := bitsToNat.comp (dropFrame.comp hz)
  have hbody := (native_carryMatrixQuery a b).comp
    ((native_longSumMatrixData a b).prod hsel)
  have hh := optionElimWithInput
    (body:=fun z xq => carryMatrixQuery a b (longSumMatrixData a b z xq,longSumSelector z))
    hparse (const [true,false]) hbody
  apply hh.of_enc_eq
  intro z
  change encBits (longSumMatrixQuery a b z)=encBits ((parseNaturalBitQuery (longSumRoot z)).elim [true,false] (fun xq => carryMatrixQuery a b (longSumMatrixData a b z xq,longSumSelector z)))
  unfold longSumMatrixQuery
  cases parseNaturalBitQuery (longSumRoot z) <;> rfl
end APSCounting893.Main
end Component_12

open APSCounting893.Main
theorem solution (a b : ℕ) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime (longSumMatrixQuery a b)
      Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits := by
  exact native_longSumMatrixQuery a b
