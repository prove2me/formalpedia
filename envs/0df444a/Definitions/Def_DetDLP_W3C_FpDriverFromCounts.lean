-- Prove2me | Definitions.Def_DetDLP_W3C_FpDriverFromCounts
-- name    : DetDLP_W3C_FpDriverFromCounts
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T01:24:29.763037+00:00
-- url     : https://prove2.me/theorems/fcdfc52e-6bcd-4a04-80c8-e76ad8525d4d
-- title:
--   Counts-based Stage-II driver
-- statement:
--   Driver trace-bound interfaces and composition
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_FpLargeEntry
import Theorems.Thm_DetDLP_w1d_fp_exponent_readback

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpDriverFromCounts
open FpOracles FpLargeEntry NineOracleLoop
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open FpStep FpTraceStep BlockLookup

/-- A root probe of mass zero consumes its certified builder and contraction
    answers and halts. The cap is computed from the words, not assumed. -/
theorem terminalProbe {en de : Port} (kit : Kit en de) {q : w3_Query}
    (hq : w3_fpQueries q) (hz : w3_mass q = 0) {N : ℕ} (rep : w3_Rep q.M N) (j : Fin N)
    (s : FpState) (hk : s.phase = 6) (hi : s.idx = 0) (hm : s.p-1 = q.M)
    (hr : s.repWord = encodeCosetRep (fun i => (rep.1 i).val) rep.2)
    (hj : (decodeBlocks s.blocksWord).flatten.length+1 = j.val) :
    ∃ t σ cap packet, calls kit t σ (tag9 6 q.input) packet ∧
      LoopRuns stepFn (calls kit t σ) 2 (packState s) packet (countWord (rep.1 j).val) cap := by
  obtain ⟨net,ans,hb,ha,hc⟩ := kit.probe q hq
  let packet := w3_packet net
  let t := max (polyBound kit.buildC q.input.length)
    (polyBound kit.contractC (net.S+net.desc.length) * mainTimeBound kit.contractC q.b)
  let σ := max (polyBound kit.buildC q.input.length) (polyBound kit.contractC (net.S+net.desc.length))
  let s' := nextState (packState s) 7 s.idx s.blocksWord s.repWord packet s.pre
  let v := packState s'
  let y := countWord (rep.1 j).val
  let cap := (pairWord (packState s) packet).length + (pairWord v (tag9 7 packet)).length +
    ans.length + (pairWord v ans).length + y.length
  have hc' : calls kit t σ (tag9 7 packet) ans :=
    ⟨7,_,rfl,MachineComposition.runsWithin_mono hc (le_max_right ..) (le_max_right ..)⟩
  refine ⟨t,σ,cap,packet,⟨6,_,rfl,MachineComposition.runsWithin_mono hb (le_max_left ..) (le_max_left ..)⟩,?_⟩
  have hpos : positive q.M packet ans = false := by simp [packet,positive_spec net ha,hz]
  have halt : stepFn (pairWord v ans) = true :: y := by
    apply root_output s' rep j
    · rfl
    · exact hi
    · simpa [s',nextState] using hm
    · exact hr
    · exact hj
    · exact hpos
  apply contract_round s hk packet ans _ hc'
  · dsimp only [cap]; omega
  · change (pairWord v (tag9 7 packet)).length ≤ cap; dsimp only [cap]; omega
  · dsimp only [cap]; omega
  · exact Or.inl ⟨halt,by change (pairWord v ans).length ≤ cap; dsimp only [cap]; omega,
      by change y.length ≤ cap; dsimp only [cap]; omega⟩

/-- Witnesses required at the call site of the loop compiler. The same driver
    constant `C` must work for every input, even though the budgets vary. -/
def TraceAt {en de : Port} (kit : Kit en de) (c C p : ℕ) [Fact p.Prime]
    (h a : (ZMod p)ˣ) :=
  ∃ (u r n : ℕ) (t s : ℝ), u < p-1 ∧ h^u = a ∧ 1 ≤ r ∧ 0 ≤ t ∧ 0 ≤ s ∧
    LoopRuns stepFn (calls kit t s) r (input h a) [] (countWord u) n ∧
    (r:ℝ) * (polyBound c n + (c:ℝ)*(t+s+1)) ≤ mainTimeBound C (bitLen p) ∧
    polyBound c n + (c:ℝ)*(s+1) ≤ mainSpaceBound C (bitLen p)

def TraceBounds {en de : Port} (kit : Kit en de) (K : ℕ) :=
  ∀ c : ℕ, 1 ≤ c → ∃ C : ℕ, ∀ p [Fact p.Prime] (h a : (ZMod p)ˣ), orderOf h = p-1 →
    (¬w3_large p (p-1) → TraceAt kit c C p h a) ∧
    (w3_large p (p-1) → ∀ F : Blocks p, w3_fpBaseCalls en.1 en.2 de.1 de.2 K F →
      TraceAt kit c C p h a)

/-- Final composition once the two controller branches have bounded traces. -/
theorem ofTraceBounds (counts : M89S1.CountOracle)
    (en : PrimitiveMachine) (eo : Fin en.tapeCount) (de : PrimitiveMachine) (do' : Fin de.tapeCount) (K : ℕ)
    (hnet : w3_terminalOps w3_fpQueries) (hupdate : w3_hnfOps)
    (bounds : TraceBounds (Classical.choice (available counts ⟨en,eo⟩ ⟨de,do'⟩ hnet hupdate)) K) :
    ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime] (h a : (ZMod p)ˣ),
        let M := p-1
        let m := blockCount (bitLen p)
        orderOf h = M →
          let accepts := fun u => RunsWithin D out (encodeFpDLPInput p (h : ZMod p).val (a : ZMod p).val) (countWord u)
                                    (mainTimeBound C (bitLen p)) (mainSpaceBound C (bitLen p))
          (¬ w3_large p M → w3_scanOutput M (Additive.ofMul h) (Additive.ofMul a) accepts) ∧
          (∀ hg : w3_large p M, letI : NeZero M := ⟨by have := hg.2.1; omega⟩
            ∀ F : Fin m → List (ZMod p)ˣ, w3_fpBaseCalls en eo de do' K F →
              ∃ (seed : FpSeed p m) (B : Fin m → List (ZMod p)ˣ),
                (∀ i, (B i).Nodup ∧ (B i).toFinset = fpFactorBlock (hashThreshold p M m M) seed i) ∧
                w3_traceOutput (w3_fpFB F) (w3_fpFB B) M (Additive.ofMul h) (Additive.ofMul a) accepts) := by
  let kit := Classical.choice (available counts ⟨en,eo⟩ ⟨de,do'⟩ hnet hupdate)
  obtain ⟨D,out,c,hc,hr⟩ := FpLoopSound.compileKitTrace kit
  obtain ⟨C,hC⟩ := bounds c hc
  refine ⟨D,out,C,?_⟩
  intro p hp h a
  dsimp only
  intro gen
  obtain ⟨sm,lg⟩ := hC p h a gen
  let ok := fun u => RunsWithin D out (input h a) (countWord u) (mainTimeBound C (bitLen p)) (mainSpaceBound C (bitLen p))
  have finish (tr : TraceAt kit c C p h a) : ∃ u, u < p-1 ∧ h^u = a ∧ ok u := by
    obtain ⟨u,r,n,t,s,hu,he,hr₀,ht,hs,trace,bt,bs⟩ := tr
    exact ⟨u,hu,he,MachineComposition.runsWithin_mono (hr t s ht hs r n _ _ hr₀ trace) bt bs⟩
  constructor
  · intro hn
    obtain ⟨u,hu,he,hrun⟩ := finish (sm hn)
    exact (w1d_fp_exponent_readback p h a gen ok u hu he hrun).1
  · intro hg F hf
    obtain ⟨u,hu,he,hrun⟩ := finish (lg hg F hf)
    exact (w1d_fp_exponent_readback p h a gen ok u hu he hrun).2 hg F

end DetDLP.W3C.FpDriverFromCounts


