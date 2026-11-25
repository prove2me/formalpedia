-- Prove2me | Definitions.Def_DetDLP_W3C_FpTraceBounds
-- name    : DetDLP_W3C_FpTraceBounds
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T03:25:43.233+00:00
-- url     : https://prove2.me/theorems/919ea4ca-d6f8-4792-a5a8-35fd739ce314
-- title:
--   FP trace bounds
-- statement:
--   Uniform trace bounds for the finite-field driver
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_FpDriverFromCounts
import Definitions.Def_DetDLP_W3C_FpRowTrace
import Theorems.Thm_DetDLP_w3_small_prime_bound
import Theorems.Thm_DetDLP_m89_s1_winning_seed_mean
import Theorems.Thm_DetDLP_lemma_3_2_collision_potential
import Theorems.Thm_DetDLP_dense_covering_and_2m_decomp
import Definitions.Def_DetDLP_W1_Bounds

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpTraceBounds
open FpDriverFromCounts FpLargeEntry FpOracles FpTraceStep FpStep NineOracleLoop
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private abbrev cap (p g a u : ℕ) :=
  let w := encodeFpDLPInput p g a
  let s := packState (start 1 w)
  let y := countWord u
  (pairWord w []).length + (pairWord s (tag9 0 w)).length + (pairWord s y).length + y.length

/-- Uniformly absorb a finite table of costs at positive bit lengths. -/
private theorem finiteCost {ι : Type} [Fintype ι] (b : ι → ℕ) (f : ι → ℝ) :
    ∃ C : ℕ, ∀ i, 1 ≤ b i → f i ≤ mainTimeBound C (b i) ∧ f i ≤ mainSpaceBound C (b i) := by
  classical
  let T (i : ι) := ⌈f i⌉₊
  let d (i : ι) := max (Real.sqrt (logLogSafe (b i))) ((logSafe (b i))^((1:ℝ)/4))
  let c (i : ι) := ⌈(T i:ℝ)*d i⌉₊
  let C := Finset.univ.sup c
  refine ⟨C,fun i hb => ?_⟩
  have hc : c i ≤ C := Finset.le_sup (f := c) (Finset.mem_univ i)
  have hd : (T i:ℝ)*d i ≤ C := (Nat.le_ceil _).trans (by exact_mod_cast hc)
  have hbR : (1:ℝ) ≤ b i := by exact_mod_cast hb
  have hCb : (C:ℝ) ≤ C*b i := by simpa using mul_le_mul_of_nonneg_left hbR (Nat.cast_nonneg C)
  have hbase : f i ≤ (2:ℝ)^(T i:ℝ) := by
    refine (Nat.le_ceil _).trans ?_
    rw [Real.rpow_natCast]; exact_mod_cast (Nat.lt_two_pow_self (n := T i)).le
  have hl : (0:ℝ) < logSafe (b i) := lt_of_lt_of_le zero_lt_one (le_max_left ..)
  have hll : (0:ℝ) < logLogSafe (b i) := lt_of_lt_of_le zero_lt_one (le_max_left ..)
  constructor
  · refine hbase.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ((le_div_iff₀ (Real.sqrt_pos.2 hll)).mpr ?_))
    exact (mul_le_mul_of_nonneg_left (le_max_left ..) (Nat.cast_nonneg (T i))).trans (hd.trans hCb)
  · refine hbase.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ((le_div_iff₀ (Real.rpow_pos_of_pos hl _)).mpr ?_))
    exact (mul_le_mul_of_nonneg_left (le_max_right ..) (Nat.cast_nonneg (T i))).trans (hd.trans hCb)

/-- The small branch has one oracle call and one halt; a single C bounds all its inputs. -/
theorem small {en de : Port} (kit : Kit en de) (c : ℕ) :
    ∃ C : ℕ, ∀ p [Fact p.Prime] (h a : (ZMod p)ˣ), orderOf h = p-1 →
      ¬w3_large p (p-1) → TraceAt kit c C p h a := by
  let H : ℕ := 2^32
  let I := Fin (H+1) × Fin (H+1) × Fin (H+1) × Fin (H+1)
  let b (i : I) := bitLen i.1
  let n (i : I) := cap i.1 i.2.1 i.2.2.1 i.2.2.2
  let t (i : I) := mainTimeBound kit.scanC (b i)
  let s (i : I) := mainSpaceBound kit.scanC (b i)
  let bt (i : I) := 2*(polyBound c (n i) + (c:ℝ)*(t i+s i+1))
  let bs (i : I) := polyBound c (n i) + (c:ℝ)*(s i+1)
  obtain ⟨C,hC⟩ := finiteCost b (fun i => max (bt i) (bs i))
  refine ⟨C,?_⟩
  intro p hp h a gen guard
  obtain ⟨u,find,run⟩ := kit.scan p h a gen guard
  have hu := List.mem_range.mp (List.mem_of_find?_eq_some find)
  have matched := List.find?_some find
  have he : h^u = a := of_decide_eq_true matched
  have hpH : p ≤ H := w3_small_prime_bound.1 p guard
  have hg := (h:ZMod p).val_lt
  have ha := (a:ZMod p).val_lt
  let i : I := (⟨p,by omega⟩,⟨(h:ZMod p).val,by omega⟩,⟨(a:ZMod p).val,by omega⟩,⟨u,by omega⟩)
  obtain ⟨hT,hS⟩ := hC i (Nat.clog_pos (by decide) hp.out.one_lt)
  have hcall : calls kit (t i) (s i) (tag9 0 (input h a)) (countWord u) := ⟨0,_,rfl,run⟩
  refine ⟨u,2,n i,t i,s i,hu,he,by decide,?_,?_,scan_loop resume _ _ _ _ _ guard hcall,?_,?_⟩
  · apply Real.rpow_nonneg (by norm_num)
  · apply Real.rpow_nonneg (by norm_num)
  · exact (le_max_left (bt i) (bs i)).trans hT
  · exact (le_max_right (bt i) (bs i)).trans hS

open M89S1

/-- Coverage holds for the actual plan returned by slot 1, not just some seed. -/
theorem planCover {p : ℕ} [Fact p.Prime] (large : w3_large p (p-1)) (L : Plan p)
    (ok : m89_fp_plan_ok L) (x : (ZMod p)ˣ) :
    ∃ A B : Fin (m p) → (ZMod p)ˣ,
      (∀ i, A i ∈ m89_fp_plan_block L i ∧ B i ∈ m89_fp_plan_block L i) ∧ (∏ i, A i*B i) = x := by
  obtain ⟨hp,hM,hbig⟩ := large
  have hm : 2 ≤ m p := le_max_left ..
  have big : 4096*m p ≤ p-1 := by change 4096*blockCount (bitLen p) ≤ p-1; omega
  cases L with
  | none => exact False.elim (ok ⟨hM,big⟩)
  | some v =>
    obtain ⟨t,seed⟩ := v
    obtain ⟨_,_,rfl,win⟩ := ok
    let μ := (qBlk p (p-1) (hashThreshold p (p-1) (m p) (p-1)))^(m p)
    have hstar : 0 < qStar (m p) (p-1) := lt_of_lt_of_le (by omega : 0 < 4096*m p) (le_max_left ..)
    have hp' : 0 < p := by omega
    have hM' : 0 < p-1 := by omega
    have hμ : 0 < μ := by unfold μ qBlk hashThreshold; positivity
    have avg := lemma_3_2_collision_potential.2 p (m p) hm hM big
    have good := (m89_s1_winning_seed_mean.1 p (m p) seed win).trans avg
    exact (dense_covering_and_2m_decomp.2 μ _ hμ (good.trans_lt (by norm_num))).2 x

open BlockLookup
private abbrev initialRaw (w : List Bool) : List ℤ :=
  (FpTraceStep.coords (decodeBlocks w)).map fun i => if i = (decodeBlocks w).flatten.length then 1 else 0
private abbrev firstUpdateState (s : FpState) (w : List Bool) :=
  nextState (packState s) 4 0 w (fullRep (FpTraceStep.coords (decodeBlocks w))) (rowPkt (s.p-1) 1 (initialRaw w)) []

/-- From the enumerator's answer, the next physical step emits the generator congruence. -/
theorem initialStep (s : FpState) (w : List Bool) (hk : s.phase = 3) :
    stepFn (pairWord (packState s) w) = false :: pairWord (packState (firstUpdateState s w))
      (tag9 8 (queryInput 8 (firstUpdateState s w))) := by
  unfold stepFn
  rw [round_eq s w (by omega)]
  simp only [resume,unpackState_packState,hk,beq_self_eq_true,cond_true,emit,call]

/-- The initial packet represents the full lattice and the row fixing the generator to one. -/
theorem initialCall {en de : Port} (kit : Kit en de) (s : FpState) (w : List Bool)
    {M N : ℕ} [NeZero M] (hM : 2 ≤ M) (hm : s.p-1 = M)
    (hn : (decodeBlocks w).flatten.length+2 = N) (j : Fin N) (hj : j.val = (decodeBlocks w).flatten.length)
    (z : w3_Label M N) (hz : z j = 1) :
    let r : w3_Row M N := (fun i => if i=j then 1 else 0,1)
    let budget := polyBound kit.updateC (N+bitLen M)
    ∃ rep, w3_update r (w3_full M N) rep ∧ Stage2Trace.Invariant z rep ∧
      calls kit budget budget (tag9 8 (queryInput 8 (firstUpdateState s w)))
        (encodeCosetRep (fun i => (rep.1 i).val) rep.2) := by
  intro r budget
  let v := firstUpdateState s w
  have coords' : FpTraceStep.coords (decodeBlocks w) = List.range N := by
    exact congrArg List.range hn
  have raw : (initialRaw w).map (fun x : ℤ => (x : ZMod M)) = List.ofFn r.1 := by
    simp only [initialRaw,coords',List.map_map]
    apply List.ext_getElem <;> simp [r,Fin.ext_iff,hj,apply_ite,Function.comp_def]
    intro i _; split <;> simp_all
  have holds : w3_holds r z := by simpa [r,w3_holds,ite_mul] using hz
  have h1 : (1 : ZMod M).val = 1 := ZMod.val_one'' (by omega)
  have hpack : fullRep (FpTraceStep.coords (decodeBlocks w)) =
      encodeCosetRep (fun i => ((w3_full M N).1 i).val) (w3_full M N).2 := by
    simp [coords',fullRep_correct,w3_full]
  obtain ⟨rep,hu,hi,_,hc⟩ := FpRowTrace.update_call kit hM (by omega : 1 ≤ N) v _ r z
    (Stage2Trace.full z) holds _ (by simpa [v,firstUpdateState,nextState] using hm) hn raw
  refine ⟨rep,hu,hi,?_⟩
  simpa only [v,firstUpdateState,nextState,unpackState_packState,hm,r,h1,hpack] using hc

open DetDLP_W1_Bounds

/-- Close the compiler bounds once round count, word cap, and oracle budgets
    have separate uniform bounds. The factor four converts the space scale to time. -/
theorem closeCosts {ι : Type} (b : ι → ℕ) (hb : ∀ i, 1 ≤ b i) (c : ℕ)
    (r n : ι → ℕ) (t s : ι → ℝ) (ht0 : ∀ i, 0 ≤ t i) (hs0 : ∀ i, 0 ≤ s i)
    (hr : Dom (fun i => sScale (b i)) (fun i => (r i : ℝ)))
    (hn : Dom (fun i => sScale (b i)) (fun i => (n i : ℝ)))
    (ht : Dom (fun i => tScale (b i)) t) (hs : Dom (fun i => sScale (b i)) s) :
    ∃ C : ℕ, ∀ i, (r i:ℝ) * (polyBound c (n i) + (c:ℝ)*(t i+s i+1)) ≤ mainTimeBound C (b i) ∧
      polyBound c (n i) + (c:ℝ)*(s i+1) ≤ mainSpaceBound C (b i) := by
  let S := fun i => sScale (b i)
  let T := fun i => 4*tScale (b i)
  have hS : ∀ i, 1 ≤ S i := fun i => scales_one (hb i)
  have hST : ∀ i, S i ≤ T i := fun i => compareScale (b i)
  have hT : ∀ i, 1 ≤ T i := fun i => (hS i).trans (hST i)
  have ht' : Dom T t := by
    obtain ⟨k,hk⟩ := ht
    refine ⟨k,fun i => (hk i).trans ?_⟩
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h := hT i; dsimp only [T] at h ⊢
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg k)
  have one : Dom S (fun _ => (1:ℝ)) := by simpa using dconst hS 1
  have cc := dconst hS c
  have pp : Dom S (fun i => polyBound c (n i)) :=
    Dom.mul cc ((Dom.add hS hn one).pow hS (fun _ => by positivity) c)
      (fun _ => by positivity) (fun _ => by positivity)
  have p0 : ∀ i, 0 ≤ polyBound c (n i) := fun i => by unfold polyBound; positivity
  have ss := Dom.add hS pp (Dom.mul cc (Dom.add hS hs one) (fun _ => by positivity) (fun i => by linarith [hs0 i]))
  have total := Dom.add hT (Dom.add hT ht' (liftTime hS hST hs)) (liftTime hS hST one)
  have per := Dom.add hT (liftTime hS hST pp) (Dom.mul (liftTime hS hST cc) total
    (fun _ => by positivity) (fun i => by linarith [ht0 i,hs0 i]))
  have times := Dom.mul (liftTime hS hST hr) per (fun _ => by positivity)
    (fun i => by positivity [p0 i, ht0 i, hs0 i])
  obtain ⟨k,hk⟩ := times
  obtain ⟨l,hl⟩ := ss
  refine ⟨max (4*k) l,fun i => ⟨(hk i).trans ?_,(hl i).trans ?_⟩⟩
  · rw [← tEq]
    have h : E (T i) k = E (tScale (b i)) (4*k) := by unfold E T; push_cast; ring_nf
    rw [h]; apply monoE _ (le_max_left ..)
    have := hT i; dsimp only [T] at this; linarith
  · rw [← sEq]; exact monoE (zero_le_one.trans (hS i)) (le_max_right ..)

open OAI.Algorithms.SubexponentialSAT.Computation

/-- Counts-based driver composition, conditional on the controller trace bounds. -/
theorem w3_fp_stage2_from_counts (counts : M89S1.CountOracle)
    (en : PrimitiveMachine) (eo : Fin en.tapeCount) (de : PrimitiveMachine) (do' : Fin de.tapeCount) (K : ℕ)
    (hnet : w3_terminalOps w3_fpQueries) (hupdate : w3_hnfOps)
    (bounds : FpDriverFromCounts.TraceBounds
      (Classical.choice (FpOracles.available counts ⟨en,eo⟩ ⟨de,do'⟩ hnet hupdate)) K) :
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
  exact FpDriverFromCounts.ofTraceBounds counts en eo de do' K hnet hupdate bounds

end DetDLP.W3C.FpTraceBounds


