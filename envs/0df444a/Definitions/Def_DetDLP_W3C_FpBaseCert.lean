-- Prove2me | Definitions.Def_DetDLP_W3C_FpBaseCert
-- name    : DetDLP_W3C_FpBaseCert
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T05:38:35.265667+00:00
-- url     : https://prove2.me/theorems/54b236f6-215d-550a-88e3-56892b0940a5

import Definitions.Def_DetDLP_W3C_FpBaseChain
import Definitions.Def_DetDLP_W3C_FpTraceBounds

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpBaseCert
open FpOracles FpStep FpTraceStep FpBaseOne BlockLookup NineOracleLoop
open Groundwork DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

variable {p : ℕ} [Fact p.Prime]
abbrev enc (x : Additive (ZMod p)ˣ) := countWord (x.toMul : ZMod p).val
abbrev repWord {M N : ℕ} [NeZero M] (r : w3_Rep M N) := encodeCosetRep (fun i => (r.1 i).val) r.2
variable (B : FpOracles.Blocks p)
noncomputable abbrev fb := w3_fpFB B

theorem wireBlocks : decodeBlocks (encodeFpFactorBlocks B) = blocks (fb B) enc := by
  rw [native_blocks]; congr 1; funext i; simp [fb,w3_fpFB,List.map_map,Function.comp_def,enc]

theorem sizeBlocks : (decodeBlocks (encodeFpFactorBlocks B)).flatten.length = (fb B).totalBaseSize := by
  simp [wireBlocks,blocks,List.length_flatten,List.ofFn_eq_map,List.map_map,Function.comp_def,
    IndexedFactorBase.totalBaseSize,Fin.sum_univ_def]

theorem coordinate (g a : (ZMod p)ˣ) (j : Fin (fb B).totalCoords) :
    ((decodeBlocks (encodeFpFactorBlocks B)).flatten ++ [enc (Additive.ofMul g), enc (Additive.ofMul a)]).getD j [] =
      enc ((fb B).elem (Additive.ofMul g) (Additive.ofMul a) j) := by
  let xs := (List.finRange (m p)).flatMap (fb B).blocks
  have hx : xs.length = (fb B).totalBaseSize := by simp [xs,IndexedFactorBase.totalBaseSize,List.length_flatMap,Fin.sum_univ_def]
  have he : (decodeBlocks (encodeFpFactorBlocks B)).flatten = xs.map enc := by
    rw [wireBlocks]; simp only [xs,blocks,List.ofFn_eq_map,List.map_flatMap]; rfl
  rw [he]; unfold IndexedFactorBase.elem
  split_ifs with h e
  · have lt : j.val < (xs.map enc).length := by simpa [hx] using h
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_append]; omega),List.getElem_append_left lt,List.getElem_map]; rfl
  · rw [List.getD_eq_getElem]; simp [List.getElem_append_right,hx,e]; simp [hx,e]
  · have hj := j.isLt; change j.val < (fb B).totalBaseSize + 2 at hj
    have hj' : j.val = (fb B).totalBaseSize + 1 := by omega
    rw [List.getD_eq_getElem]; simp [List.getElem_append_right,hx,hj']; simp [hx,hj']

variable {en de : Port} (kit : Kit en de) (L : Plan p)
variable (large : w3_large p (p-1)) (ok : m89_fp_plan_ok L)
variable (hB : ∀ i, (B i).Nodup ∧ (B i).toFinset = m89_fp_plan_block L i)

include large ok hB in
/-- Decompose an actual native coordinate and recover its indexed tuple from the same answer. -/
theorem tupleAnswer (x : (ZMod p)ˣ) : ∃ (U : (fb B).BlockTuple) (u : List Bool),
    (fb B).tupleVal U = Additive.ofMul x ∧ decodeFrames u = words (fb B) enc U ∧
    run (kit.ports 3) (Encoding.encodeList id [encodeNatListBin [p,(x:ZMod p).val],m89_fp_plan_word L]) u
      (mainSpaceBound kit.decC (bitLen p)) (polyBound kit.decC (bitLen p)) := by
  classical
  obtain ⟨A,D,mem,prod,run⟩ := kit.decompose p L ok x (FpTraceBounds.planCover large L ok x)
  have idx (i : Fin (m p)) (v : (ZMod p)ˣ) (hv : v ∈ m89_fp_plan_block L i) :
      ∃ k : Fin ((fb B).blocks i).length, ((fb B).blocks i).get k = Additive.ofMul v := by
    apply List.mem_iff_get.mp
    change _ ∈ (B i).map Additive.ofMul
    exact List.mem_map.mpr ⟨v,List.mem_toFinset.mp ((hB i).2.symm ▸ hv),rfl⟩
  choose kA hkA using fun i => idx i (A i) (mem i).1
  choose kD hkD using fun i => idx i (D i) (mem i).2
  let U : (fb B).BlockTuple := fun i => ![kA i,kD i]
  refine ⟨U,encodeFpDecomp A D,?_,?_,run⟩
  · simp only [IndexedFactorBase.tupleVal,U,Matrix.cons_val_zero,Matrix.cons_val_one,hkA,hkD,← ofMul_mul,← ofMul_prod]; exact congrArg Additive.ofMul prod
  · simp only [encodeFpDecomp,encodeNatListBin,decodeFrames_map,List.map_flatMap,List.map_cons,List.map_nil,BlockLookup.words,U,Matrix.cons_val_zero,Matrix.cons_val_one,hkA,hkD]; rfl

variable (g a : (ZMod p)ˣ)

structure Ready (s : FpState) : Prop where
  phase : s.phase = 4
  prime : s.p = p
  gen : s.g = (g : ZMod p).val
  target : s.a = (a : ZMod p).val
  plan : s.planWord = m89_fp_plan_word L
  blocks : s.blocksWord = encodeFpFactorBlocks B

abbrev R {en de : Port} (kit : Kit en de) (p N : ℕ) :=
  let u := polyBound kit.updateC (N+bitLen (p-1))
  FpLargeEntry.calls kit (max u (mainSpaceBound kit.decC (bitLen p))) (max u (polyBound kit.decC (bitLen p)))

include large ok hB in
/-- Native decompositions and actual slot-8 answers generate all remaining phase-4 cycles.
    The cap can be enlarged without choosing different oracle answers. -/
theorem chain [NeZero (p-1)] (z : w3_Label (p-1) (fb B).totalCoords)
    (consistent : ∀ (j : Fin (fb B).totalCoords) (T : (fb B).BlockTuple),
      (fb B).tupleVal T = (fb B).elem (Additive.ofMul g) (Additive.ofMul a) j →
      w3_holds ((fun i => w3_unitRow (fb B) (p-1) j i - ((fb B).tupleCnt T i : ZMod (p-1))),0) z)
    (s : FpState) (hs : Ready B L g a s) (rep : w3_Rep (p-1) (fb B).totalCoords)
    (inv : Stage2Trace.Invariant z rep) (n : ℕ) (hn : s.idx + n = (fb B).totalCoords) :
    ∃ (endState : FpState) (r : w3_Rep (p-1) (fb B).totalCoords) (cap : ℕ),
      Ready B L g a endState ∧ endState.idx = (fb B).totalCoords ∧ Stage2Trace.Invariant z r ∧
      endState.T = s.T ∧ w3_coset r ⊆ w3_coset rep ∧
      (∀ j : Fin (fb B).totalCoords, s.idx ≤ j.val → ∃ T : (fb B).BlockTuple,
        (fb B).tupleVal T = (fb B).elem (Additive.ofMul g) (Additive.ofMul a) j ∧
        ∀ y ∈ w3_coset r, w3_holds ((fun i => w3_unitRow (fb B) (p-1) j i - ((fb B).tupleCnt T i : ZMod (p-1))),0) y) ∧
      ∀ c ≥ cap, FpDecompLoop.Chain (R kit p (fb B).totalCoords) c n s (repWord rep) endState (repWord r) := by
  classical
  induction n generalizing s rep with
  | zero => exact ⟨s,rep,0,hs,by omega,inv,rfl,Set.Subset.rfl,fun j hj => by have := j.isLt; omega,fun _ _ => .done⟩
  | succ n ih =>
    let j : Fin (fb B).totalCoords := ⟨s.idx,by omega⟩
    let x := ((fb B).elem (Additive.ofMul g) (Additive.ofMul a) j).toMul
    obtain ⟨T,u,hT,hu,hdec⟩ := tupleAnswer B kit L large ok hB x
    let mid := nextState (packState s) 5 s.idx s.blocksWord (repWord rep) [] []
    let v := updateState s (repWord rep) u
    have hv : Ready B L g a v := by
      obtain ⟨_,hp,hg,ha,hl,hb⟩ := hs
      simp only [v,updateState,nextState,unpackState_packState]; exact ⟨rfl,hp,hg,ha,hl,hb⟩
    have hvIdx : v.idx = s.idx+1 := by simp [v,updateState,nextState]
    have dim : (decodeBlocks s.blocksWord).flatten.length+2 = (fb B).totalCoords := by rw [hs.blocks,sizeBlocks]; rfl
    have dim' : (decodeBlocks v.blocksWord).flatten.length+2 = (fb B).totalCoords := by rw [hv.blocks,sizeBlocks]; rfl
    have hq : queryInput 3 mid = Encoding.encodeList id [encodeNatListBin [p,(x:ZMod p).val],m89_fp_plan_word L] := by
      simp only [queryInput,mid,nextState,unpackState_packState,hs.prime,hs.gen,hs.target,hs.plan,hs.blocks]
      rw [show ((decodeBlocks (encodeFpFactorBlocks B)).flatten ++ [countWord (g:ZMod p).val,countWord (a:ZMod p).val]).getD s.idx [] = enc (Additive.ofMul x) from coordinate B g a j]; simp [enc]
    have dc : R kit p (fb B).totalCoords (tag9 3 (queryInput 3 mid)) u := by
      rw [hq]; exact ⟨3,_,rfl,MachineComposition.runsWithin_mono hdec (le_max_right ..) (le_max_right ..)⟩
    let row : w3_Row (p-1) (fb B).totalCoords := (fun i => w3_unitRow (fb B) (p-1) j i - ((fb B).tupleCnt T i : ZMod (p-1)),0)
    let raw := initRowCounts (decodeBlocks s.blocksWord) (decodeFrames u) s.idx
    have nd (i) : (((fb B).blocks i).map enc).Nodup := by
      change (((B i).map Additive.ofMul).map enc).Nodup
      rw [List.map_map]; apply (hB i).1.map; intro x y h; apply Units.ext; apply ZMod.val_injective
      exact (decode_count _).symm.trans ((congrArg PolyT.bval h).trans (decode_count _))
    have rawok : raw.map (fun t : ℤ => (t : ZMod (p-1))) = List.ofFn row.1 := by
      have h := congrArg Prod.fst (initRowCounts_correct (fb B) enc nd (p-1) (fun _ => T) j)
      simpa [raw,hs.blocks,wireBlocks,hu,row,w3_initRows,j] using h
    obtain ⟨r,upd,hi,_,hc⟩ := FpRowTrace.update_call kit (by have := large.2.1; omega : 2 ≤ p-1)
      (fb B).genCoord.pos v rep row z inv (consistent j T hT) raw (by rw [hv.prime]) dim' rawok
    have eqv : {v with repWord := repWord rep, pktWord := rowPkt (p-1) row.2.val raw} = v := by
      dsimp only [v,updateState,nextState]; simp only [unpackState_packState,hs.prime,row,ZMod.val_zero]; rfl
    change FpRowTrace.calls kit _ _ (tag9 8 (queryInput 8 {v with repWord := repWord rep, pktWord := rowPkt (p-1) row.2.val raw})) (repWord r) at hc
    rw [eqv] at hc
    obtain ⟨i,w,eq,hr⟩ := hc
    have uc : R kit p (fb B).totalCoords (tag9 8 (queryInput 8 v)) (repWord r) :=
      ⟨i,w,eq,MachineComposition.runsWithin_mono hr (le_max_left ..) (le_max_left ..)⟩
    obtain ⟨e,last,cap,he,hei,hil,hT',sub,rows,tail⟩ := ih v hv r hi (by omega)
    let lim := cap + (pairWord (packState s) (repWord rep)).length + (pairWord (packState mid) (tag9 3 (queryInput 3 mid))).length + u.length + (pairWord (packState mid) u).length + (pairWord (packState v) (tag9 8 (queryInput 8 v))).length + (repWord r).length
    have vv : v.T = s.T := by simp [v,updateState,nextState]
    have stepSub : w3_coset r ⊆ w3_coset rep := by rw [upd.2]; exact Set.sep_subset ..
    refine ⟨e,last,lim,he,hei,hil,hT'.trans vv,sub.trans stepSub,?_,fun c h => ?_⟩
    · intro i hj
      by_cases eqi : i = j
      · subst i; refine ⟨T,hT,fun y hy => ?_⟩; have mem := sub hy; rw [upd.2] at mem; exact mem.2
      · exact rows i (by have hne : i.val ≠ s.idx := fun h => eqi (Fin.ext h); omega)
    dsimp only [lim] at h
    exact .step (cycle_of_answers hs.phase (by omega) dc uc (by omega)
      (by change (pairWord (packState mid) (tag9 3 (queryInput 3 mid))).length ≤ c; omega) (by omega)
      (by change (pairWord (packState mid) u).length ≤ c; omega)
      (by change (pairWord (packState v) (tag9 8 (queryInput 8 v))).length ≤ c; omega) (by omega)) (tail c (by omega))

end DetDLP.W3C.FpBaseCert


