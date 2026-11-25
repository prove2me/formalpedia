-- Prove2me | Definitions.Def_DetDLP_M6_DFSOracleTrace
-- name    : DetDLP_M6_DFSOracleTrace
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:39:50.623027+00:00
-- url     : https://prove2.me/theorems/771e6396-cd31-44fd-b6c0-d281e785faa6
-- title:
--   Depth-first factor-splitting oracle trace
-- statement:
--   A simulation invariant for the factor-splitting work stack identifies the recursive leaves and bounds every oracle packet by a polynomial in the root bit length, including when a rejected divisor answer exceeds the root.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Proposition 2.6 (pp. 10–11)

import Definitions.Def_DetDLP_W5_M6DriverFrames
import Theorems.Thm_DetDLP_m89_polyT_oracle_loop
import Definitions.Def_DetDLP_W5_M6RawCallback
import Definitions.Def_DetDLP_M6_DFSOracleStep
set_option autoImplicit false
namespace DetDLP.M6Loop
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open w5_SplitArithmetic
abbrev Todo := List (ℕ × ℕ)
def flat (p : Todo) := p.flatMap (fun z => [z.1,z.2])
def work (f : ℕ → ℕ) (p : Todo) := (p.flatMap (fun z => calls f z.1 z.2)).length
def leaves (f : ℕ → ℕ) (p : Todo) := p.flatMap (fun z => split f z.1 z.2)
@[simp] theorem flat_cons (k x : ℕ) (p : Todo) : flat ((k,x)::p) = k::x::flat p := rfl
@[simp] theorem work_cons (f : ℕ → ℕ) (k x : ℕ) (p : Todo) : work f ((k,x)::p) = (calls f k x).length + work f p := by simp [work]
@[simp] theorem leaves_cons (f : ℕ → ℕ) (k x : ℕ) (p : Todo) : leaves f ((k,x)::p) = split f k x ++ leaves f p := rfl
def Good (N n : ℕ) (z : ℕ × ℕ) := z.1 ≤ n ∧ 2 ≤ z.2 ∧ z.2 ≤ N
abbrev Loop (E : PrimitiveMachine) (o : Fin E.tapeCount) (T S : ℝ) :=
  Nat.rec (motive := fun _ => W → W → W → ℕ → Prop) (fun _ _ _ _ => False)
  (fun _ prev st ans outW m => (step (pair st ans) = true :: outW ∧ (pair st ans).length ≤ m ∧ outW.length ≤ m) ∨
    ∃ st' q ans', step (pair st ans) = false :: pair st' q ∧ (pair st ans).length ≤ m ∧ (pair st' q).length ≤ m ∧ ans'.length ≤ m ∧ RunsWithin E o q ans' T S ∧ prev st' ans' outW m)

/-- The loop takes one more dispatch than there are unprocessed tree nodes. -/
theorem simulate (f : ℕ → ℕ) (E : PrimitiveMachine) (o : Fin E.tapeCount) (T S : ℝ) (N n m : ℕ)
    (outList : List ℕ) (B : ℕ) (hout : (encodeNatListBin outList.mergeSort).length ≤ m)
    (hor : ∀ x, 2 ≤ x → x ≤ N → RunsWithin E o (countWord x) (countWord (f x)) T S)
    (hsize : ∀ (p : Todo) (a : List ℕ) k x, (∀ z ∈ (k,x)::p, Good N n z) →
      a.reverse ++ leaves f ((k,x)::p) = outList →
      (p.length+1)+a.length+work f ((k,x)::p) ≤ B →
      (pair (state (flat ((k,x)::p)) a) (countWord x)).length ≤ m ∧
      (pair (state (flat ((k,x)::p)) a) (countWord (f x))).length ≤ m ∧ (countWord (f x)).length ≤ m) :
    ∀ (p : Todo) (a : List ℕ) (st ans : W), (∀ z ∈ p, Good N n z) → a.reverse ++ leaves f p = outList →
      p.length+a.length+work f p ≤ B → step (pair st ans) = dispatch (flat p) a → (pair st ans).length ≤ m →
      Loop E o T S (work f p + 1) st ans (encodeNatListBin outList.mergeSort) m := by
  intro p
  induction hW : work f p using Nat.strong_induction_on generalizing p with
  | h u ih =>
    intro a st ans hg hs hB hstep hlen
    cases p with
    | nil =>
      simp only [work,List.flatMap_nil,List.length_nil] at hW; subst u
      have he : a.reverse = outList := by simpa [leaves] using hs
      exact Or.inl ⟨by simpa [flat,dispatch,w5_M6Sort.sort_eq,he] using hstep,hlen,hout⟩
    | cons z p =>
      obtain ⟨k,x⟩ := z
      have hg0 := hg (k,x) (by simp)
      have hgs : ∀ z ∈ p, Good N n z := fun z hz => hg z (by simp [hz])
      obtain ⟨hq,ha,had⟩ := hsize p a k x hg hs (by rw [hW]; exact hB)
      let st' := state (flat ((k,x)::p)) a
      have hquery : step (pair st ans) = false :: pair st' (countWord x) := by simpa [st',dispatch] using hstep
      have hnext : step (pair st' (countWord (f x))) = advance (flat ((k,x)::p)) a (f x) := next_eq ..
      have more (p' : Todo) (a' : List ℕ) (hw : work f p'+1=u) (goods : ∀ z ∈ p', Good N n z)
          (vals : a'.reverse ++ leaves f p' = outList) (bound : p'.length + a'.length + work f p' ≤ B)
          (next : advance (flat ((k,x)::p)) a (f x) = dispatch (flat p') a') :
          Loop E o T S (u+1) st ans (encodeNatListBin outList.mergeSort) m := by
        refine Or.inr ⟨st',countWord x,countWord (f x),hquery,hlen,hq,had,hor x hg0.2.1 hg0.2.2,?_⟩
        rw [←hw]; exact ih (work f p') (by omega) p' rfl a' st' _ goods vals bound (hnext.trans next) ha
      have leaf (hc : (calls f k x).length=1) (hl : split f k x=[x])
          (hnext : advance (flat ((k,x)::p)) a (f x) = dispatch (flat p) (x::a)) : _ :=
        more p (x::a) (by simpa [hc,Nat.add_comm] using hW) hgs
          (by simpa [hl,List.reverse_cons,List.append_assoc] using hs)
          (by simp only [work_cons,hc,List.length_cons] at hW hB ⊢; omega) hnext
      cases k with
      | zero => exact leaf rfl rfl (by simp [advance])
      | succ k =>
        by_cases hv : 2 ≤ f x ∧ f x < x ∧ f x ∣ x
        · obtain ⟨h₂,_,_⟩ := proper_divisor_bounds hv
          let p' := (k,f x)::(k,x/f x)::p
          have hw : work f p'+1=u := by simpa [p',calls,hv,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hW
          apply more p' a hw
          · intro z hz; simp only [p',List.mem_cons] at hz
            rcases hz with rfl|rfl|hz
            · exact ⟨by have := hg0.1; omega,hv.1,hv.2.1.le.trans hg0.2.2⟩
            · exact ⟨by have := hg0.1; omega,h₂,(Nat.div_le_self ..).trans hg0.2.2⟩
            · exact hgs _ hz
          · simpa [p',hv,List.append_assoc] using hs
          · change p.length+1+1 + a.length + work f p' ≤ B; simp only [List.length_cons] at hB; omega
          · simp [p',advance,hv,hv.2.2,Nat.mod_eq_zero_of_dvd hv.2.2]
        · exact leaf (by simp [calls,hv]) (by simp [hv]) (by simp only [Nat.dvd_iff_mod_eq_zero] at hv; simp [advance,hv])
end DetDLP.M6Loop

set_option autoImplicit false
namespace DetDLP.M6Loop
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open w5_SplitArithmetic
noncomputable def rate (K n : ℕ) := (2:ℝ)^((K:ℝ)*n/Real.sqrt (logSafe n))
def pol (K n : ℕ) := K*(n+1)^K
@[simp] theorem cast_pol (K n : ℕ) : ((pol K n : ℕ):ℝ) = polyBound K n := by simp [pol,polyBound]
def limit (K n : ℕ) := 100*(n+1)^2 + pol K n + 10
private theorem maxword {N n x : ℕ} (hn : n=bitLen (N+1)) (hn2 : 2 ≤ n) (h : x ≤ N) : (countWord x).length ≤ n := by
  by_cases hx : x=0
  · subst x; change 1 ≤ n; omega
  · rw [hn]; exact countWord_length_le_bitLen (by omega) h
private theorem depth_le {N : ℕ} : bitLen (N+1) ≤ N := by
  apply (Nat.clog_le_iff_le_pow (by norm_num)).mpr; have := Nat.lt_two_pow_self (n:=N); omega
private theorem pair_len (a b : W) : (pair a b).length = 2*a.length+1+b.length := by
  have h : (a.flatMap (fun v => [true,v])).length = 2*a.length := by induction a with | nil => rfl | cons v a ih => change (a.flatMap _).length + 1 + 1 = 2*(a.length+1); omega
  simp only [pair,List.length_append,h,List.length_singleton]
private theorem flat_len (p : Todo) : (flat p).length = 2*p.length := by induction p with | nil => rfl | cons z p ih => obtain ⟨k,x⟩ := z; simp [ih]; omega
private theorem word_bound (E : PrimitiveMachine) (o : Fin E.tapeCount) (q ans : W) (T : ℝ) (s : ℕ) (hq : q.isEmpty=false)
    (h : RunsWithin E o q ans T s) : ans.length ≤ s+9 := by
  cases q with
  | nil => contradiction
  | cons b w =>
    obtain ⟨k,rf,a,_,tr,he⟩ := w5_M6RawCallback.run E o b w ans T s h (fun _ => false)
    have hb := tr.within k _ le_rfl tr.forget (w5_M6RawCallback.ot E o)
    have hh := (w5_M6EntryCallHarvest.word_length (a (w5_M6RawCallback.ot E o)) (a (w5_M6RawCallback.ov E o))).trans hb
    rw [he] at hh; simpa using hh

theorem root (f : ℕ → ℕ) (E : PrimitiveMachine) (o : Fin E.tapeCount) (K N : ℕ) (hN : 2 ≤ N)
    (hd : ∀ x, 2 ≤ x → RunsWithin E o (countWord x) (countWord (f x)) (rate K (bitLen (x+1))) (polyBound K (bitLen (x+1)))) :
    let n := bitLen (N+1)
    Loop E o (rate K n) (polyBound K n) ((calls f n N).length+1) (countWord N) [] (encodeNatListBin (split f n N).mergeSort) (limit K n) := by
  intro n
  have hn : 2 ≤ n := w5_M6CallBudget.two_le_bitLen_of_two_le hN
  have dn : n ≤ N := depth_le
  have hor (x : ℕ) (hx : 2 ≤ x) (h : x ≤ N) : RunsWithin E o (countWord x) (countWord (f x)) (rate K n) (polyBound K n) := by
    have hbit : bitLen (x+1) ≤ n := Nat.clog_mono_right 2 (by omega)
    apply MachineComposition.runsWithin_mono (hd x hx) _ (w5_polyBound_mono_input K hbit)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h1 : (2:ℝ) ≤ bitLen (x+1) := by exact_mod_cast w5_M6CallBudget.two_le_bitLen_of_two_le hx
    have h2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    have hr := w5_sqrtLogRate_monotoneOn h1 h2 (by exact_mod_cast hbit)
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg K)
  let out := split f n N
  have hl := length_calls_lt_two_bitLen f n N hN
  change (calls f n N).length < 2*n at hl
  have hc := countWord_length_eq_bitLen N (by omega)
  change (countWord N).length = n at hc
  have outLen := length_encode_split_le f n N hN
  change (encodeNatListBin out.mergeSort).length ≤ (2*n+2)*n+1 at outLen
  have big : (2*n+2)*n+1 ≤ limit K n := by unfold limit; nlinarith
  have hs := simulate f E o (rate K n) (polyBound K n) N n (limit K n) out (2*n) (outLen.trans big) hor
  have sz : ∀ (p : Todo) (a : List ℕ) (k x : ℕ), (∀ z ∈ (k,x)::p, Good N n z) → a.reverse ++ leaves f ((k,x)::p) = out →
      (p.length+1)+a.length+work f ((k,x)::p) ≤ 2*n →
      (pair (state (flat ((k,x)::p)) a) (countWord x)).length ≤ limit K n ∧
      (pair (state (flat ((k,x)::p)) a) (countWord (f x))).length ≤ limit K n ∧ (countWord (f x)).length ≤ limit K n := by
    intro p a k x hg he hb
    let t : Todo := (k,x)::p
    have hx := hg (k,x) (by simp)
    have wx : (countWord x).length ≤ n := maxword rfl hn hx.2.2
    have wa := word_bound E o _ _ _ (pol K n) (empty_cw x) (by rw [cast_pol]; exact hor x hx.2.1 hx.2.2)
    have hflat : ∀ y ∈ flat t, (countWord y).length ≤ n := by
      intro y hy; obtain ⟨⟨d,b⟩,hz,hy⟩ := List.mem_flatMap.mp hy
      obtain ⟨h1,_,h3⟩ := hg _ hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl|rfl
      · exact maxword rfl hn (h1.trans dn)
      · exact maxword rfl hn h3
    have hacc : ∀ y ∈ a, (countWord y).length ≤ n := by
      intro y hy; have ho : y ∈ out := he ▸ List.mem_append_left _ (List.mem_reverse.mpr hy)
      exact maxword rfl hn (mem_split_bounds f n N hN y ho).2
    have ft := length_encodeList_le countWord (flat t) n hflat
    have at' := length_encodeList_le countWord a n hacc
    change (encodeNatListBin (flat t)).length ≤ _ at ft
    change (encodeNatListBin a).length ≤ _ at at'
    rw [flat_len] at ft
    have pt : t.length ≤ 2*n := by change p.length+1 ≤ _; omega
    have al : a.length ≤ 2*n := by omega
    have ht := ft.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (2*n+2) (Nat.mul_le_mul_left 2 pt)) 1)
    have ha := at'.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (2*n+2) al) 1)
    change (pair (state (flat t) a) (countWord x)).length ≤ _ ∧ (pair (state (flat t) a) (countWord (f x))).length ≤ _ ∧ _
    simp only [state,pair_len,limit]
    refine ⟨?_,?_,?_⟩
    · calc
        _ ≤ 2*(2*((2*n+2)*(2*(2*n))+1)+1+((2*n+2)*(2*n)+1))+1+n := by gcongr
        _ ≤ _ := by nlinarith [Nat.zero_le (pol K n), Nat.zero_le (n^2)]
    · calc
        _ ≤ 2*(2*((2*n+2)*(2*(2*n))+1)+1+((2*n+2)*(2*n)+1))+1+(pol K n+9) := by gcongr
        _ ≤ _ := by nlinarith [Nat.zero_le (n^2)]
    · omega
  have tr := hs sz [(n,N)] [] (countWord N) [] (by simp [Good,hN]) (by simp [out,leaves]) (by simp [work]; omega) (by simp [step,flat,hc]) (by rw [pair_len,hc]; simp [limit]; nlinarith)
  simpa [work,out] using tr
end DetDLP.M6Loop


