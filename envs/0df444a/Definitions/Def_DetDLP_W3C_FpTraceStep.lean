-- Prove2me | Definitions.Def_DetDLP_W3C_FpTraceStep
-- name    : DetDLP_W3C_FpTraceStep
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T23:46:09.52538+00:00
-- url     : https://prove2.me/theorems/6c8e8c99-46dc-4763-bd1d-060817b78f2b

import Definitions.Def_DetDLP_W3C_FpTraceCore

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 900000
namespace DetDLP.W3C.FpTraceStep
open Groundwork DetDLP_W1_Queries FpStep BlockLookup NineOracleLoop NewtonPoly OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] PolyT.comp PolyT.fst PolyT.snd PolyT.prodMk PolyT.id' PolyT.const PolyT.flatMap PolyT.map PolyT.length PolyT.flatten
  PolyT.beq' PolyT.cond' PolyT.add PolyT.mod PolyT.mul PolyT.sub PolyT.div PolyT.decide_eq PolyT.decide_lt PolyT.decide_le w5_M6Sort.cw_poly w5_M6Sort.encode_poly frame_poly
  S8G.FpMoment.Code.width_poly P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219
variable {α β : Type} [Enc α] [Enc β]
attribute [local irreducible] decodeFrames decodeBlocks S8G.FpMoment.Code.width w5_M6Sort.decode massPosWord PolyT.bval
def nextState (w : W) (k i : ℕ) (blocks rep pkt pre : W) : FpState := let s := unpackState w
  {s with phase := k, idx := i, blocksWord := blocks, repWord := rep, pktWord := pkt, pre := pre, fuel := bif k == 8 then s.fuel+1 else s.fuel}
@[local fun_prop] private theorem nextP {w b r t u : α → W} {k i : α → ℕ} (hw : PolyT w) (hk : PolyT k) (hi : PolyT i)
    (hb : PolyT b) (hr : PolyT r) (ht : PolyT t) (hu : PolyT u) : PolyT fun x => nextState (w x) (k x) (i x) (b x) (r x) (t x) (u x) := by
  change PolyT fun x => fields (nextState _ _ _ _ _ _ _); unfold fields nextState unpackState; dsimp only; fun_prop
def emit (j : Fin 9) (w : W) (k i : ℕ) (b r t u queryPre : W) := call j (nextState w k i b r t u) (nextState w k i b r t queryPre)
@[local fun_prop] private theorem emitP (j : Fin 9) {w b r t u v : α → W} {k i : α → ℕ} (hw : PolyT w) (hk : PolyT k) (hi : PolyT i)
    (hb : PolyT b) (hr : PolyT r) (ht : PolyT t) (hu : PolyT u) (hv : PolyT v) : PolyT fun x => emit j (w x) (k x) (i x) (b x) (r x) (t x) (u x) (v x) := by unfold emit; fun_prop
def seek (w u : W) := let s := unpackState w; let bs := decodeBlocks s.blocksWord; let b := S8G.FpMoment.Code.width s.p
  if u.length < 4*bs.length*b then emit 6 w 6 1 s.blocksWord s.repWord [] u (u++[false]) else
    let v := tupleWords b u; let h := 2*bs.length
    emit 8 w 8 0 s.blocksWord s.repWord (rowPkt (s.p-1) 1 (shiftRowCounts bs (v.take h) (v.drop h))) [] []
@[local fun_prop] private theorem seekP {w u : α → W} (hw : PolyT w) (hu : PolyT u) : PolyT fun x => seek (w x) (u x) := by
  unfold seek; dsimp only [unpackState]; fun_prop
/-- 3 seeds the full coset; 4 and 5 install the initial rows; 6 and 7 build and contract a probe;
    8 installs the violated shift. `idx=0` denotes a root probe and `idx=1` a left-child probe. -/
def resume (z : W × W) := let w := z.1; let a := z.2; let s := unpackState w; let bs := decodeBlocks s.blocksWord
  bif s.phase == 3 then let b := decodeBlocks a; let r := coords b
    emit 8 w 4 0 a (fullRep r) (rowPkt (s.p-1) 1 (r.map fun i => if i=b.flatten.length then 1 else 0)) [] []
  else bif s.phase == 4 then if s.idx < bs.flatten.length+2 then emit 3 w 5 s.idx s.blocksWord a [] [] [] else emit 6 w 6 0 s.blocksWord a [] [] []
  else bif s.phase == 5 then emit 8 w 4 (s.idx+1) s.blocksWord s.repWord (rowPkt (s.p-1) 0 (initRowCounts bs (decodeFrames a) s.idx)) [] []
  else bif s.phase == 6 then emit 7 w 7 s.idx s.blocksWord s.repWord a s.pre s.pre
  else bif s.phase == 7 then let pos := positive (s.p-1) s.pktWord a
    bif s.idx == 0 then bif pos then seek w [] else true :: countWord ((repLabels s.repWord).getD (bs.flatten.length+1) 0)
    else seek w (s.pre ++ [!pos])
  else bif s.phase == 8 then emit 6 w 6 0 s.blocksWord a [] [] [] else [true]
@[fun_prop] theorem resume_poly : PolyT resume := by unfold resume; dsimp only [unpackState,coords,positive]; fun_prop
theorem step_poly : PolyT (FpStep.step resume) := FpStep.step_poly resume_poly
theorem round_eq (s : FpState) (a : W) (h : 3 ≤ s.phase) :
    FpStep.step resume (pairWord (packState s) a) = resume (packState s,a) := by simp [FpStep.step_saved,show s.phase ≠ 1 by omega,show s.phase ≠ 2 by omega]
theorem child_round {q : w3_Query} {C : ℕ} (n : w3_Net q C) {v : W} (hv : EncodesTruncPoly (w3_precision q) (w3_len q) v (BTNContract n.G n.T))
    (s : FpState) (hk : s.phase=7) (hi : s.idx=1) (hm : s.p-1=q.M) (hp : s.pktWord=w3_packet n) :
    FpStep.step resume (pairWord (packState s) v) = seek (packState s) (s.pre++[decide (w3_mass q ≤ 0)]) := by
  rw [round_eq s v (by omega)]; simp [resume,hk,hi,hm,hp,positive_spec n hv,← decide_not,not_lt]
theorem prefix_invariant (q : w3_Query) {u : W} {L : ℕ} (width : ∀ X Y, (q.code X Y).length = L)
    (hlen : u.length < L) (hroot : 0 < w3c_massAt q u) {pos : Bool} (h : pos = decide (0 < w3c_massAt q (u++[false]))) :
    (u++[!pos]).length = u.length+1 ∧ 0 < w3c_massAt q (u++[!pos]) := by
  have := w3c_split q width hlen; by_cases c : 0 < w3c_massAt q (u++[false]); all_goals simp [h,c]; all_goals omega
theorem hnf_invariant {M N : ℕ} [NeZero M] {z : w3_Label M N} {s t : w3_Rep M N} {r : w3_Row M N}
    (hs : Stage2Trace.Invariant z s) (hz : w3_holds r z) (hu : w3_update r s t)
    (half : 2*Nat.card (w3_coset t) ≤ Nat.card (w3_coset s)) {k : ℕ} (cap : Nat.card (w3_coset s) ≤ 2^(k+1)) :
    Stage2Trace.Invariant z t ∧ Nat.card (w3_coset t) ≤ 2^k := by
  rw [pow_succ] at cap; exact ⟨Stage2Trace.preserve hs.2 hz hu,by omega⟩
/-- Bridge the row lemmas of `BlockLookup` to the actual HNF machine input. -/
theorem update_input {M N : ℕ} [NeZero M] (s : FpState) (x : Fin N → ℕ) (B : Matrix (Fin N) (Fin N) ℤ) (r : Fin N → ZMod M) (rhs : ℕ) (raw : List ℤ)
    (hM : s.p-1=M) (hN : (decodeBlocks s.blocksWord).flatten.length+2=N) (hr : raw.map (fun z : ℤ => (z : ZMod M)) = List.ofFn r) :
    queryInput 8 {s with repWord := encodeCosetRep x B, pktWord := rowPkt M rhs raw} = encodeCosetUpdateInput M x B (fun i => (r i).val) rhs := by
  have hh := congrArg (List.map (fun z : ZMod M => z.val)) hr; simp only [List.map_map,List.map_ofFn] at hh
  have he : raw.map (residue M) = List.ofFn (fun i => (r i).val) := by simpa only [Function.comp_def,← residue_eq] using hh
  change updateWord (s.p-1) ((decodeBlocks s.blocksWord).flatten ++ [countWord s.g,countWord s.a]).length _ _ _ = _
  simp only [List.length_append,List.length_cons,List.length_nil,hM,hN,rowPkt,first_cons,second,more_cons,id_eq,w5_M6Sort.decode_encode,decode_count,he]; exact updateWord_correct ..
theorem contract_round (s : FpState) {j : ℕ} (h : s.phase=6) (a y : W) (R : W → W → Prop) (hR : R (tag9 7 a) y)
    {out : W} {bound : ℕ} (h₀ : (pairWord (packState s) a).length ≤ bound) :
    let v := packState (nextState (packState s) 7 s.idx s.blocksWord s.repWord a s.pre)
    (pairWord v (tag9 7 a)).length ≤ bound → y.length ≤ bound → LoopRuns (FpStep.step resume) R j v y out bound →
    LoopRuns (FpStep.step resume) R (j+1) (packState s) a out bound := by
  intro v h₁ h₂ tail; refine Or.inr ⟨v,tag9 7 a,y,?_,h₀,h₁,h₂,hR,tail⟩
  rw [round_eq _ _ (by omega)]; simp [v,resume,h,emit,call,queryInput,nextState]
theorem root_output {M N : ℕ} [NeZero M] (s : FpState) (rep : w3_Rep M N) (j : Fin N) (hk : s.phase=7) (hi : s.idx=0)
    (hM : s.p-1=M) (hr : s.repWord = encodeCosetRep (fun i => (rep.1 i).val) rep.2) (ht : (decodeBlocks s.blocksWord).flatten.length+1=j.val)
    {v : W} (hz : positive M s.pktWord v = false) : FpStep.step resume (pairWord (packState s) v) = true :: countWord (rep.1 j).val := by
  rw [round_eq s v (by omega)]; simp only [resume,unpackState_packState,hk,hi,hM,hr,ht,hz,repLabels_correct]; simp [List.getD_eq_getElem?_getD,j.isLt]
end DetDLP.W3C.FpTraceStep


