-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSLexicographicCounter
-- name    : QEC_Coding_ExpanderCodes_LPSLexicographicCounter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:53:21.22621+00:00
-- url     : https://prove2.me/theorems/91de8c20-cef4-42d7-9c79-bb77d0e1d736
-- title:
--   LPSLexicographic Counter
-- statement:
--   Definitions and structural lemmas for LPSLexicographic Counter, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSLexicographicCounter.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
theorem finRange_val (q:ℕ):(List.finRange q).map Fin.val=List.range q:=by
 apply List.ext_getElem
 · simp
 · intro i h1 h2
   simp
theorem range_blocks (m q:ℕ):
 (List.range m).flatMap (fun a=>(List.range q).map (fun b=>b+q*a))=List.range (q*m):=by
 induction m with
 |zero=>simp
 |succ m ih=>
  rw [List.range_succ,List.flatMap_append,ih]
  simp only [List.flatMap_singleton]
  rw [Nat.mul_succ,List.range_add]
  congr 1
  apply List.map_congr_left
  intro b hb
  omega
theorem finRange_blocks (m q:ℕ):
 (List.finRange m).flatMap (fun a=>(List.range q).map (fun b=>b+q*a.val))=List.range (q*m):=by
 rw [←range_blocks m q,←finRange_val m,List.flatMap_map]
def orderedDigits (q:ℕ):ℕ→List (List ℕ)
 | 0 => [[]]
 | k+1 => (List.finRange q).flatMap (fun a=>(orderedDigits q k).map (fun xs=>xs++[a.val]))
theorem orderedDigits_length (q k:ℕ) (xs:List ℕ) (h:xs∈orderedDigits q k):xs.length=k:=by
 induction k generalizing xs with
 |zero=>simp only [orderedDigits,List.mem_singleton] at h;subst xs;rfl
 |succ k ih=>
  simp only [orderedDigits,List.mem_flatMap,List.mem_map] at h
  rcases h with ⟨a,ha,ys,hy,rfl⟩
  simp [ih ys hy]
theorem rank_append (q:ℕ) (xs ys:List ℕ):
 QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank q (xs++ys)=QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank q xs+q^xs.length*QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank q ys:=by
 induction xs with
 |nil=>simp [QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank]
 |cons x xs ih=>simp only [List.cons_append,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank,List.length_cons,pow_succ,ih];ring
theorem orderedDigits_ranks (q k:ℕ):
 (orderedDigits q k).map (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank q)=List.range (q^k):=by
 induction k with
 |zero=>simp [orderedDigits,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank]
 |succ k ih=>
  simp only [orderedDigits,List.map_flatMap,List.map_map,Function.comp_def]
  have hm (a:Fin q):
   (orderedDigits q k).map (fun xs=>QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank q (xs++[a.val]))=
   (List.range (q^k)).map (fun b=>b+q^k*a.val):=by
   rw [←ih,List.map_map]
   apply List.map_congr_left
   intro xs hx
   simp only [Function.comp_def,rank_append,orderedDigits_length q k xs hx,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank,Nat.mul_zero,Nat.add_zero]
  simp_rw [hm]
  simpa only [pow_succ] using finRange_blocks q (q^k)
abbrev Tuple (q:ℕ):=Fin q×Fin q×Fin q×Fin q
def coords {q:ℕ} (x:Tuple q):List ℕ:=[x.2.2.2.val,x.2.2.1.val,x.2.1.val,x.1.val]
def rawTuples (q:ℕ):List (Tuple q):=
 (List.finRange q).flatMap fun a=>
  (List.finRange q).flatMap fun b=>
   (List.finRange q).flatMap fun c=>
    (List.finRange q).map fun d=>(a,b,c,d)
theorem rawTuples_coords (q:ℕ):
 (rawTuples q).map coords=orderedDigits q 4:=by
 simp only [rawTuples,coords,orderedDigits,List.map_flatMap,List.map_map,
  Function.comp_def,List.map_singleton,List.nil_append,List.cons_append]
 simp only [←List.map_eq_flatMap]
def ordinal {q:ℕ} (x:Tuple q):ℕ:=QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank q (coords x)
theorem rawTuples_ordinals (q:ℕ):
 (rawTuples q).map ordinal=List.range (q^4):=by
 change (rawTuples q).map (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank q ∘ coords)=_
 rw [←List.map_map,rawTuples_coords,orderedDigits_ranks]
theorem coords_lt {q:ℕ} (x:Tuple q):∀a∈coords x,a<q:=by
 intro a ha
 simp only [coords,List.mem_cons,List.not_mem_nil,or_false] at ha
 rcases ha with rfl|rfl|rfl|rfl
 · exact x.2.2.2.isLt
 · exact x.2.2.1.isLt
 · exact x.2.1.isLt
 · exact x.1.isLt
def next {q:ℕ} (x:Tuple q):Tuple q:=
 let d:Fin q:=⟨QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.digit q x.2.2.2.val true,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.digit_lt q _ true x.2.2.2.isLt⟩
 let cd:=QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.carried q x.2.2.2.val true
 let c:Fin q:=⟨QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.digit q x.2.2.1.val cd,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.digit_lt q _ cd x.2.2.1.isLt⟩
 let cc:=QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.carried q x.2.2.1.val cd
 let b:Fin q:=⟨QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.digit q x.2.1.val cc,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.digit_lt q _ cc x.2.1.isLt⟩
 let cb:=QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.carried q x.2.1.val cc
 let a:Fin q:=⟨QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.digit q x.1.val cb,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.digit_lt q _ cb x.1.isLt⟩
 (a,b,c,d)
def overflow {q:ℕ} (x:Tuple q):Bool:=(QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.digits q true (coords x)).1
theorem digits_next {q:ℕ} (x:Tuple q):(QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.digits q true (coords x)).2=coords (next x):=rfl
theorem overflow_iff_last {q:ℕ} (x:Tuple q):overflow x=true ↔ ordinal x+1=q^4:=by
 simpa only [overflow,ordinal,coords,List.length_cons,List.length_nil] using QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.overflow_iff_last q (coords x) (coords_lt x)
theorem ordinal_next {q:ℕ} (x:Tuple q) (h:overflow x=false):ordinal (next x)=ordinal x+1:=by
 simpa only [ordinal,digits_next] using QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank_next q (coords x) h
def input (q:ℕ) (x:Tuple q×List Bool):List Bool:=QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.payload q (coords x.1) x.2
theorem coords_injective (q:ℕ):Function.Injective (@coords q):=by
 intro x y h
 have hd:=List.cons.inj h
 have hc:=List.cons.inj hd.2
 have hb:=List.cons.inj hc.2
 have ha:=List.cons.inj hb.2
 exact Prod.ext (Fin.ext ha.1) (Prod.ext (Fin.ext hb.1) (Prod.ext (Fin.ext hc.1) (Fin.ext hd.1)))
noncomputable def exec (q:ℕ) (x:Tuple q×List Bool):
 EvalsToInTime (TM2.step (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 3).program) ((QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 3).init (input q x))
  (some ((QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 3).halt (overflow x.1::input q (next x.1,x.2))))
  ((QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.time 3).eval (input q x).length):=by
 simpa only [QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.output,digits_next,overflow,input,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.payload] using
 QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.polyExec 3 q (coords x.1) x.2 (by rfl) (coords_lt x.1)
noncomputable def computableInPolyTime (q:ℕ):
 TM2ComputableInPolyTime (input q) id (fun x:Tuple q×List Bool=>overflow x.1::input q (next x.1,x.2)) where
 tm:=(QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 3).toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.time 3
 outputsFun:=fun x=>by
  change TM2OutputsInTime (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 3).toFinTM2 (List.map id (input q x))
   (some (List.map id (overflow x.1::input q (next x.1,x.2)))) _
  have h:=Machine.outputsInTime (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 3) _ _ _ (exec q x)
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
noncomputable def traversalExec (q:ℕ) (x:Tuple q×List Bool):
 EvalsToInTime (TM2.step (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.loopMachine 3).program) ((QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.loopMachine 3).init (input q x))
  (some ((QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.loopMachine 3).halt (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.payload q [0,0,0,0] x.2)))
  ((QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.traverseTime 3).eval (input q x).length):=by
 have hq:0<q:=by have h:=x.1.1.isLt;omega
 exact QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.traversePolyExec 3 q (coords x.1) x.2 hq (by rfl) (coords_lt x.1)
def indexInput (q:ℕ) [Fact q.Prime] (x:Fin (lpsPSLList q).length×List Bool):List Bool:=
 QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.payload (lpsPSLList q).length [x.1.val] x.2
def indexNext (q:ℕ) [Fact q.Prime] (i:Fin (lpsPSLList q).length):Fin (lpsPSLList q).length:=
 ⟨QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.digit (lpsPSLList q).length i.val true,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.digit_lt _ _ true i.isLt⟩
def indexOverflow (q:ℕ) [Fact q.Prime] (i:Fin (lpsPSLList q).length):Bool:=
 QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.carried (lpsPSLList q).length i.val true
noncomputable def indexExec (q:ℕ) [Fact q.Prime] (x:Fin (lpsPSLList q).length×List Bool):
 EvalsToInTime (TM2.step (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 0).program) ((QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 0).init (indexInput q x))
  (some ((QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 0).halt (indexOverflow q x.1::indexInput q (indexNext q x.1,x.2))))
  ((QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.time 0).eval (indexInput q x).length):=by
 simpa only [QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.output,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.digits,indexInput,indexNext,indexOverflow,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.payload] using
 QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.polyExec 0 (lpsPSLList q).length [x.1.val] x.2 (by rfl) (by simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq];exact x.1.isLt)
noncomputable def indexTraversalExec (q:ℕ) [Fact q.Prime] (x:Fin (lpsPSLList q).length×List Bool):
 EvalsToInTime (TM2.step (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.loopMachine 0).program) ((QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.loopMachine 0).init (indexInput q x))
  (some ((QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.loopMachine 0).halt (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.payload (lpsPSLList q).length [0] x.2)))
  ((QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.traverseTime 0).eval (indexInput q x).length):=by
 have hN:0<(lpsPSLList q).length:=by have h:=x.1.isLt;omega
 exact QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.traversePolyExec 0 (lpsPSLList q).length [x.1.val] x.2 hN (by rfl) (by simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq];exact x.1.isLt)
theorem canonical_rank_injective (q:ℕ) (xs ys:List ℕ) (hlen:xs.length=ys.length)
 (hx:∀a∈xs,a<q) (hy:∀a∈ys,a<q)
 (he:QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank q xs=QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank q ys):xs=ys:=by
 induction xs generalizing ys with
 |nil=>
  have h:ys=[]:=List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
  exact h.symm
 |cons x xs ih=>
  cases ys with
  |nil=>simp only [List.length_cons,List.length_nil] at hlen;omega
  |cons y ys=>
   have hx0:=hx x (by simp)
   have hy0:=hy y (by simp)
   have hm:=congrArg (fun z:ℕ=>z%q) he
   simp only [QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank,Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hx0,Nat.mod_eq_of_lt hy0] at hm
   have hq:0<q:=by omega
   have ht:QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank q xs=QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank q ys:=by
    simp only [QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank] at he
    nlinarith
   have hl:xs.length=ys.length:=by simp only [List.length_cons] at hlen;omega
   exact congrArg₂ List.cons hm (ih ys hl (fun a ha=>hx a (by simp [ha])) (fun a ha=>hy a (by simp [ha])) ht)
theorem ordinal_injective (q:ℕ):Function.Injective (@ordinal q):=by
 intro x y h
 exact coords_injective q (canonical_rank_injective q (coords x) (coords y) (by rfl)
  (coords_lt x) (coords_lt y) h)
theorem rawTuples_length (q:ℕ):(rawTuples q).length=q^4:=by
 simpa only [List.length_map,List.length_range] using congrArg List.length (rawTuples_ordinals q)
def atOrdinal (q:ℕ) (i:Fin (q^4)):Tuple q:=
 (rawTuples q).get ⟨i.val,by rw [rawTuples_length];exact i.isLt⟩
theorem atOrdinal_ordinal (q:ℕ) (i:Fin (q^4)):ordinal (atOrdinal q i)=i.val:=by
 have h:=congrArg (fun l:List ℕ=>l[i.val]?) (rawTuples_ordinals q)
 have hi:i.val<(rawTuples q).length:=by rw [rawTuples_length];exact i.isLt
 simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem?_range i.isLt,
  Option.map_some,Option.some.injEq,atOrdinal,List.get_eq_getElem] using h
theorem next_atOrdinal (q:ℕ) (i:Fin (q^4)) (hi:i.val+1<q^4):
 next (atOrdinal q i)=atOrdinal q ⟨i.val+1,hi⟩:=by
 apply ordinal_injective q
 have hf:overflow (atOrdinal q i)=false:=by
  have hlast:=overflow_iff_last (atOrdinal q i)
  rw [atOrdinal_ordinal] at hlast
  cases hb:overflow (atOrdinal q i)
  · rfl
  · have ht:=hlast.mp hb;omega
 rw [ordinal_next _ hf,atOrdinal_ordinal,atOrdinal_ordinal]
noncomputable def atOrdinalExec (q:ℕ) (i:Fin (q^4)) (hi:i.val+1<q^4) (s:List Bool):
 EvalsToInTime (TM2.step (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 3).program)
  ((QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 3).init (input q (atOrdinal q i,s)))
  (some ((QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 3).halt
   (false::input q (atOrdinal q ⟨i.val+1,hi⟩,s))))
  ((QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.time 3).eval (input q (atOrdinal q i,s)).length):=by
 have h:=exec q (atOrdinal q i,s)
 rw [next_atOrdinal q i hi] at h
 have hf:overflow (atOrdinal q i)=false:=by
  have hl:=overflow_iff_last (atOrdinal q i)
  rw [atOrdinal_ordinal] at hl
  cases hb:overflow (atOrdinal q i)
  · rfl
  · have ht:=hl.mp hb;omega
 rwa [hf] at h
noncomputable def traversalComputableInPolyTime (q:ℕ):
 TM2ComputableInPolyTime (input q) id
  (fun x:Tuple q×List Bool=>QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.payload q [0,0,0,0] x.2) where
 tm:=(QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.loopMachine 3).toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.traverseTime 3
 outputsFun:=fun x=>by
  change TM2OutputsInTime (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.loopMachine 3).toFinTM2 (List.map id (input q x))
   (some (List.map id (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.payload q [0,0,0,0] x.2))) _
  have h:=Machine.outputsInTime (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.loopMachine 3) _ _ _ (traversalExec q x)
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
noncomputable def indexComputableInPolyTime (q:ℕ) [Fact q.Prime]:
 TM2ComputableInPolyTime (indexInput q) id
  (fun x:Fin (lpsPSLList q).length×List Bool=>indexOverflow q x.1::indexInput q (indexNext q x.1,x.2)) where
 tm:=(QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 0).toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.time 0
 outputsFun:=fun x=>by
  change TM2OutputsInTime (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 0).toFinTM2 (List.map id (indexInput q x))
   (some (List.map id (indexOverflow q x.1::indexInput q (indexNext q x.1,x.2)))) _
  have h:=Machine.outputsInTime (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 0) _ _ _ (indexExec q x)
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
noncomputable def indexTraversalComputableInPolyTime (q:ℕ) [Fact q.Prime]:
 TM2ComputableInPolyTime (indexInput q) id
  (fun x:Fin (lpsPSLList q).length×List Bool=>QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.payload (lpsPSLList q).length [0] x.2) where
 tm:=(QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.loopMachine 0).toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.traverseTime 0
 outputsFun:=fun x=>by
  change TM2OutputsInTime (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.loopMachine 0).toFinTM2 (List.map id (indexInput q x))
   (some (List.map id (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.payload (lpsPSLList q).length [0] x.2))) _
  have h:=Machine.outputsInTime (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.loopMachine 0) _ _ _ (indexTraversalExec q x)
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
end QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter


