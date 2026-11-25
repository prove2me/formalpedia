-- Prove2me | Definitions.Def_DetDLP_W3C_FpCutExec
-- name    : DetDLP_W3C_FpCutExec
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T06:06:44.199924+00:00
-- url     : https://prove2.me/theorems/fe23cfeb-8f36-5540-926e-fc30e6606874
-- title:
--   Execute bounded prime-field Stage-II cuts
-- statement:
--   The actual builder, contraction and HNF replies generate a bounded cut chain. Each nonterminal root performs the greedy prefix search and an exact update, and a zero root reads the terminal coordinate.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_FpCosetLoop
import Definitions.Def_DetDLP_W3C_FpDriverFromCounts

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpCutExec
open FpOracles FpStep FpTraceStep FpLargeEntry NineOracleLoop BlockLookup
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

variable {en de : Port} (kit : Kit en de)

/-- Local certificates compose by taking the maximum of the oracle budgets and word caps. -/
theorem enlarge {t σ T S : ℝ} {r c C : ℕ} {w a o : Word}
    (ht : t ≤ T) (hs : σ ≤ S) (hcap : c ≤ C)
    (tr : LoopRuns stepFn (calls kit t σ) r w a o c) : LoopRuns stepFn (calls kit T S) r w a o C := by
  induction r generalizing w a with
  | zero => exact False.elim tr
  | succ r ih =>
    rcases tr with ⟨h,h₀,h₁⟩ | ⟨v,q,y,h,h₀,h₁,h₂,⟨j,x,hx,hr⟩,tail⟩
    · exact Or.inl ⟨h,h₀.trans hcap,h₁.trans hcap⟩
    · exact Or.inr ⟨v,q,y,h,h₀.trans hcap,h₁.trans hcap,h₂.trans hcap,
        ⟨j,x,hx,MachineComposition.runsWithin_mono hr ht hs⟩,ih tail⟩

abbrev AnyCall (q y : Word) := ∃ t σ, calls kit t σ q y
abbrev Finish (r : ℕ) (w a o : Word) := ∃ t σ cap, LoopRuns stepFn (calls kit t σ) r w a o cap

theorem prepend {r : ℕ} {w a o v q y : Word}
    (h : stepFn (pairWord w a) = false :: pairWord v q) (hr : AnyCall kit q y)
    (tail : Finish kit r v y o) : Finish kit (r+1) w a o := by
  obtain ⟨t,s,⟨j,x,he,run⟩⟩ := hr
  obtain ⟨t',s',c,tr⟩ := tail
  let C := c + (pairWord w a).length + (pairWord v q).length + y.length
  refine ⟨max t t',max s s',C,Or.inr ⟨v,q,y,h,by dsimp [C]; omega,by dsimp [C]; omega,
    by dsimp [C]; omega,⟨j,x,he,MachineComposition.runsWithin_mono run (le_max_left ..) (le_max_left ..)⟩,
    enlarge kit (le_max_right ..) (le_max_right ..) (by dsimp [C]; omega) tr⟩⟩

abbrev repWord {M N : ℕ} [NeZero M] (r : w3_Rep M N) := encodeCosetRep (fun i => (r.1 i).val) r.2
abbrev st (s : FpState) (k i f : ℕ) (r t u : Word) :=
  {s with phase := k, idx := i, fuel := f, repWord := r, pktWord := t, pre := u}

variable (q : w3_Query) (s : FpState)
abbrev Rep := w3_Rep q.M q.FB.totalCoords
def probe (r : Rep q) (u : Word) : w3_Query :=
  {q with y := r.1, pre := u, input := queryInput 6 (st s 6 0 0 (repWord r) [] u)}
noncomputable abbrev path (r : Rep q) := DetDLP_W3C_PrefixSearch (w3c_massAt (Stage2Trace.root q r))

/-- The exact native wire interfaces needed by the generic controller induction. -/
structure Wires (L : ℕ) (enc : q.V → Word) : Prop where
  modulus : s.p-1 = q.M
  dimension : (decodeBlocks s.blocksWord).flatten.length+2 = q.FB.totalCoords
  blocks : decodeBlocks s.blocksWord = BlockLookup.blocks q.FB enc
  length : 4*(decodeBlocks s.blocksWord).length*S8G.FpMoment.Code.width s.p = L
  width : ∀ X Y, (q.code X Y).length = L
  injective : Function.Injective (Function.uncurry q.code)
  distinct : ∀ i, ((q.FB.blocks i).map enc).Nodup
  valid : ∀ r u, w3_fpQueries (probe q s r u)
  tuples : ∀ X Y, let v := tupleWords (S8G.FpMoment.Code.width s.p) (q.code X Y)
                  let n := 2*(decodeBlocks s.blocksWord).length
                  v.take n = words q.FB enc X ∧ v.drop n = words q.FB enc Y

abbrev Search (r : Rep q) (f : ℕ) (u : Word) := seek (packState (st s 7 0 f (repWord r) [] [])) u

private theorem seek_st (r : Rep q) (f j : ℕ) (a v u : Word) :
    seek (packState (st s 7 j f (repWord r) a v)) u = Search q s r f u := by
  simp [Search,seek,st,emit,nextState]

variable {q s} {L : ℕ} {enc : q.V → Word} (w : Wires q s L enc)

private theorem path_length (r : Rep q) (i : ℕ) : (path q r i).length = i := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [path,DetDLP_W3C_PrefixSearch] using ih

include w in
/-- Extend a continuation at the leaf back to the current seek instruction, charging two
    physical rounds per prefix bit. Query and saved prefixes differ at slot 6. -/
theorem seek_prefix (r : Rep q) (f : ℕ) {output : Word} {n : ℕ}
    (leaf : ∀ v a, stepFn (pairWord v a) = Search q s r f (path q r L) → Finish kit n v a output)
    (k i : ℕ) (ik : i+k=L) (v a : Word)
    (atSeek : stepFn (pairWord v a) = Search q s r f (path q r i)) : Finish kit (n+2*k) v a output := by
  induction k generalizing i v a with
  | zero => simpa using leaf v a (by simpa [← ik] using atSeek)
  | succ k ih =>
    let u := path q r i
    let z := probe q s r (u++[false])
    obtain ⟨net,ans,hb,ha,hc⟩ := kit.probe z (w.valid ..)
    let b := st s 6 1 f (repWord r) [] u
    let d := st s 7 1 f (repWord r) (w3_packet net) u
    have hlen : u.length < 4*(decodeBlocks s.blocksWord).length*S8G.FpMoment.Code.width s.p := by
      rw [w.length,path_length]; omega
    have hstep : stepFn (pairWord v a) = false :: pairWord (packState b) (tag9 6 z.input) := by
      rw [atSeek]; simp [Search,seek,emit,call,nextState,st,b,z,probe,u,show (path q r i).length < _ from hlen,queryInput]
    have hstep' : stepFn (pairWord (packState b) (w3_packet net)) = false :: pairWord (packState d) (tag9 7 (w3_packet net)) := by
      rw [stepFn,round_eq b _ (by decide : 3 ≤ 6)]; simp [resume,b,d,st,emit,call,queryInput,nextState]
    have hnext : stepFn (pairWord (packState d) ans) = Search q s r f (path q r (i+1)) := by
      rw [stepFn,child_round net ha d rfl rfl w.modulus rfl]; apply seek_st
    have tail := ih (i+1) (by omega) _ _ hnext
    have build : AnyCall kit (tag9 6 z.input) (w3_packet net) := ⟨_,_,6,_,rfl,hb⟩
    have contract : AnyCall kit (tag9 7 (w3_packet net)) ans := ⟨_,_,7,_,rfl,hc⟩
    simpa only [Nat.mul_succ,Nat.add_assoc] using prepend kit hstep build (prepend kit hstep' contract tail)

abbrev rootState (r : Rep q) (f : ℕ) := st s 6 0 f (repWord r) [] []
abbrev RootStep (r : Rep q) (f : ℕ) (v a : Word) :=
  stepFn (pairWord v a) = false :: pairWord (packState (rootState (s:=s) r f)) (tag9 6 (probe q s r []).input)

variable (z : w3_Label q.M q.FB.totalCoords) (pass : w3_pass q.FB q.M q.P z)
variable (hM : 2 ≤ q.M) (j : Fin q.FB.totalCoords) (hj : (decodeBlocks s.blocksWord).flatten.length+1 = j.val)

include w pass hM hj in
/-- The cardinality induction records the *executed* slot-8 answers. Each positive root
    costs one build, one contraction, two calls per bit and one HNF update. -/
theorem execute (k : ℕ) (r : Rep q) (inv : Stage2Trace.Invariant z r)
    (cap : Nat.card (w3_coset r) ≤ 2^k) (f : ℕ) (v a : Word) (root : RootStep (s:=s) r f v a) :
    ∃ n last, n ≤ k ∧ w3_Cuts q.FB q.M q.P n r last ∧ Stage2Trace.Invariant z last ∧
      w3_mass (Stage2Trace.root q last) = 0 ∧ Finish kit (3+n*(2*L+3)) v a (countWord (last.1 j).val) := by
  induction k using Nat.strong_induction_on generalizing r f v a with
  | h k rec =>
    by_cases hz : w3_mass (Stage2Trace.root q r) = 0
    · obtain ⟨t,σ,c,packet,hb,ht⟩ := FpDriverFromCounts.terminalProbe kit (w.valid r []) hz r j
        (rootState (s:=s) r f) rfl rfl w.modulus rfl hj
      refine ⟨0,r,Nat.zero_le _,.nil r,inv,hz,?_⟩
      rw [Nat.zero_mul,Nat.add_zero]; exact prepend kit (r:=2) root ⟨t,σ,hb⟩ ⟨t,σ,c,ht⟩
    · have hp : 0 < w3_mass (Stage2Trace.root q r) := lt_of_le_of_ne (w3c_mass_nonneg _) (Ne.symm hz)
      have row (b : ℕ) (bound : Nat.card (w3_coset r) ≤ 2^(b+1)) :=
        FpRowTrace.positive_row kit (Stage2Trace.root q r) w.width w.injective hM z pass r rfl inv bound hp s w.modulus enc w.dimension w.distinct
      cases k with
      | zero =>
        obtain ⟨X,Y,r',_,cut,hi,_,_⟩ := row 0 (by simpa using cap.trans (by decide : 2^0 ≤ 2^(0+1)))
        obtain ⟨_,_,_,_,_,_,half⟩ := cut
        have pos : 1 ≤ Nat.card (w3_coset (M:=q.M) r') := (Stage2Trace.card_bounds hi.2).1
        change 2 * Nat.card (w3_coset (M:=q.M) r') ≤ Nat.card (w3_coset (M:=q.M) r) at half
        simp only [pow_zero] at cap; omega
      | succ k =>
        obtain ⟨X,Y,r',hcode,cut,hi,cap',update⟩ := row k cap
        let raw := shiftRowCounts (blocks q.FB enc) (words q.FB enc X) (words q.FB enc Y)
        let pkt := rowPkt q.M 1 raw
        let up := st s 8 0 (f+1) (repWord r) pkt []
        have hrestart : RootStep (s:=s) r' (f+1) (packState up) (repWord r') := by
          unfold RootStep stepFn; rw [round_eq up _ (by decide : 3 ≤ 8)]
          simp [resume,emit,call,up,st,nextState,rootState,probe,queryInput]
        obtain ⟨n,last,hn,cuts,hl,hzero,tail⟩ := rec k (by omega) r' hi cap' (f+1) _ _ hrestart
        let zq := probe q s r []
        obtain ⟨net,ans,hb,ha,hc⟩ := kit.probe zq (w.valid r [])
        let b := rootState (s:=s) r f
        let d := st s 7 0 f (repWord r) (w3_packet net) []
        have hcontract : stepFn (pairWord (packState b) (w3_packet net)) = false :: pairWord (packState d) (tag9 7 (w3_packet net)) := by
          rw [stepFn,round_eq b _ (by decide : 3 ≤ 6)]; simp [resume,b,d,st,rootState,emit,call,queryInput,nextState]
        have hpos : positive (s.p-1) (w3_packet net) ans = true := by rw [w.modulus]; exact (positive_spec net ha).trans (decide_eq_true hp)
        have hseek : stepFn (pairWord (packState d) ans) = Search q s r f (path q r 0) := by
          rw [stepFn,round_eq d _ (by decide : 3 ≤ 7)]
          change resume (packState d,ans) = Search q s r f []
          simpa [resume,d,st,hpos] using seek_st q s r f 0 (w3_packet net) [] []
        have hup : AnyCall kit (tag9 8 (queryInput 8 up)) (repWord r') := by
          let U := polyBound kit.updateC (q.FB.totalCoords+bitLen q.M)
          refine ⟨U,U,?_⟩
          have h1 : (1 : ZMod q.M).val = 1 := ZMod.val_one'' (by omega)
          change FpRowTrace.calls kit U U (tag9 8 (queryInput 8 {s with repWord := repWord r, pktWord := rowPkt q.M (1 : ZMod q.M).val raw})) (repWord r') at update
          rw [h1] at update
          exact update
        have leaf (v' a' : Word) (he : stepFn (pairWord v' a') = Search q s r f (path q r L)) :
            Finish kit (3+n*(2*L+3)+1) v' a' (countWord (last.1 j).val) := by
          apply prepend kit _ hup tail
          rw [he,Search,seek]; simp only [unpackState_packState,st,w.length,path_length,lt_self_iff_false,if_false]
          change q.code X Y = path q r L at hcode
          rw [← hcode]; obtain ⟨hx,hy⟩ := w.tuples X Y
          rw [hx,hy]; simp only [w.blocks,w.modulus,emit,call,nextState,unpackState_packState,up,st,pkt,raw]; rfl
        have inner := seek_prefix kit w r f leaf L 0 (by omega) _ _ hseek
        have full := prepend kit root ⟨_,_,6,_,rfl,hb⟩ (prepend kit hcontract ⟨_,_,7,_,rfl,hc⟩ inner)
        refine ⟨n+1,last,by omega,.cons cut cuts,hl,hzero,?_⟩
        convert full using 1 <;> ring

end DetDLP.W3C.FpCutExec


