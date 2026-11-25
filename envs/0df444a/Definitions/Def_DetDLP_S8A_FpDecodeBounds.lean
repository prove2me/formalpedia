-- Prove2me | Definitions.Def_DetDLP_S8A_FpDecodeBounds
-- name    : DetDLP_S8A_FpDecodeBounds
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:33:53.894603+00:00
-- url     : https://prove2.me/theorems/e0b155bd-9818-4b74-a9e6-39bf9bd0b305
-- title:
--   Trace and resource bounds for the finite-field decoder
-- statement:
--   The count-guided decoder executes one round per fixed-width prefix bit and one final output round. State, query, and answer lengths are bounded by a single quadratic in the bit length of the prime. Reusing oracle tapes yields polynomial space and the Stage I time bound.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_S8A_FpPrefixSpec
import Theorems.Thm_DetDLP_m89_polyT_oracle_loop
import Theorems.Thm_DetDLP_stage1_complexity_dominance
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_comp

set_option autoImplicit false
namespace DetDLP.m89_decode_trace
open M89S1 m89_decode m89_decode_step m89_enum_words m89_decode_finish Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

abbrev LR (O : PrimitiveMachine) (o : Fin O.tapeCount) (t s : ℝ) := Nat.rec (motive := fun _ => Word → Word → Word → ℕ → Prop)
  (fun _ _ _ _ => False) (fun _ prev st ans outW maxLen =>
    (step (pair st ans) = true :: outW ∧ (pair st ans).length ≤ maxLen ∧ outW.length ≤ maxLen) ∨
    (∃ st' q ans', step (pair st ans) = false :: pair st' q ∧ (pair st ans).length ≤ maxLen ∧
      (pair st' q).length ≤ maxLen ∧ ans'.length ≤ maxLen ∧ RunsWithin O o q ans' t s ∧ prev st' ans' outW maxLen))

theorem linearTrace {O : PrimitiveMachine} {o : Fin O.tapeCount} {t s : ℝ} {n N : ℕ} (st ans q : ℕ → Word) (outW : Word)
    (hcont : ∀ k, k < n → step (pair (st k) (ans k)) = false :: pair (st (k+1)) (q k))
    (hstop : step (pair (st n) (ans n)) = true :: outW)
    (hlen : ∀ k, k ≤ n → (pair (st k) (ans k)).length ≤ N) (hout : outW.length ≤ N)
    (hcall : ∀ k, k < n → (pair (st (k+1)) (q k)).length ≤ N ∧ (ans (k+1)).length ≤ N ∧ RunsWithin O o (q k) (ans (k+1)) t s) :
    LR O o t s (n+1) (st 0) (ans 0) outW N := by
  have aux (r k : ℕ) (h : k+r = n) : LR O o t s (r+1) (st k) (ans k) outW N := by
    induction r generalizing k with
    | zero => have he : k = n := by omega
              subst k; exact Or.inl ⟨hstop,hlen _ le_rfl,hout⟩
    | succ r ih =>
      have hk : k < n := by omega
      obtain ⟨hq,ha,hr⟩ := hcall k hk
      exact Or.inr ⟨_,_,_,hcont k hk,hlen k hk.le,hq,ha,hr,ih (k+1) (by omega)⟩
  exact aux n 0 (by omega)

def px (p x : ℕ) := encodeNatListBin [p,x]
@[simp] theorem fields_px (p x : ℕ) : fields (px p x) = [countWord p,countWord x] := by
  change fields (Encoding.encodeList id [countWord p,countWord x]) = _; simp

variable {p : ℕ} [Fact p.Prime] {T : ℕ} (S : FpSeed p (blockCount (bitLen p))) (X : (ZMod p)ˣ)

noncomputable abbrev D := fpFactorBlock (p:=p) T S
noncomputable abbrev nbit (p : ℕ) := 2*blockCount (bitLen p)*bitLen p
noncomputable abbrev plan := m89_fp_plan_word (some (T,S))
abbrev data := px p (X : ZMod p).val
noncomputable abbrev pre (k : ℕ) := path (cnt (D (T:=T) S) X) k
noncomputable abbrev leftCount (k : ℕ) := cnt (D (T:=T) S) X (pre (T:=T) S X k ++ [false])
noncomputable def st : ℕ → Word
  | 0 => Encoding.encodeList id [data X,plan (T:=T) S]
  | k+1 => state (data X) (plan (T:=T) S) (pre (T:=T) S X k)
noncomputable def ans : ℕ → Word
  | 0 => []
  | k+1 => encodeNatListBin [leftCount (T:=T) S X k]
noncomputable def query (k : ℕ) := queryWord 5 (countWord p) [countWord T,List.ofFn (fpBits S),countWord (X : ZMod p).val,pre (T:=T) S X k ++ [false]]

theorem stage (k : ℕ) : step (pair (st (T:=T) S X k) (ans (T:=T) S X k)) = advance (data X) (plan (T:=T) S) (pre (T:=T) S X k) := by
  cases k with
  | zero => exact step_start ..
  | succ k => exact step_next ..

private theorem bval_count (n : ℕ) : bval (countWord n) = n := by by_cases hn : n = 0; subst n; rfl; simp [countWord,hn,bval_bits]
private theorem width_eq (p : ℕ) (hp : 2 ≤ p) : (p-1).size = bitLen p := by
  apply le_antisymm
  · apply Nat.size_le.2; have h : p ≤ 2^(bitLen p) := Nat.le_pow_clog (by decide) _; omega
  · apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2; have h := Nat.size_le.mp (le_refl (p-1).size); omega

theorem advance_eq (k : ℕ) : advance (data X) (plan (T:=T) S) (pre (T:=T) S X k) =
    if k < nbit p then false :: pair (st (T:=T) S X (k+1)) (query (T:=T) S X k)
    else true :: fpFinish (bitLen p) (pre (T:=T) S X k) := by
  have hs : (List.ofFn (fpBits S)).length = nbit p := by simp only [List.length_ofFn]; unfold nbit; ring
  simp only [advance,fields_px,plan,m89_fp_plan_word,List.tail_cons,fields_encode,List.getD_cons_zero,List.getD_cons_succ,hs,pre,path_length,bval_count,Nat.size_eq_bits_len,width_eq p (Fact.out : Nat.Prime p).two_le]; rfl

end DetDLP.m89_decode_trace

set_option autoImplicit false
namespace DetDLP.m89_decode_lengths
open M89S1 m89_decode m89_enum_words m89_decode_step m89_decode_trace
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

@[simp] theorem frame_len (w : Word) : (Encoding.frame w).length = 2*w.length+1 := by
  induction w with | nil => rfl | cons b w ih => change (Encoding.frame w).length+1+1=2*(w.length+1)+1; omega
@[simp] theorem econs {α : Type} (f : α → Word) (u : α) (us : List α) : (Encoding.encodeList f (u::us)).length = 2*(f u).length+2+(Encoding.encodeList f us).length := by simp [Encoding.encodeList]; omega
@[simp] theorem enil {α : Type} (f : α → Word) : (Encoding.encodeList f []).length = 1 := rfl
@[simp] theorem pair_len (s a : Word) : (pair s a).length = 2*s.length+1+a.length := by
  have eq : ∀ w : Word, (w.flatMap (fun b => [true,b])).length = 2*w.length := by intro w; induction w with | nil => rfl | cons b l ih => simp [List.flatMap_cons,ih]; omega
  simp [pair,eq]; omega

theorem cw (k n : ℕ) (h : n ≤ 2^k) : (countWord n).length ≤ k+2 := by
  by_cases hn : n=0
  · subst n; simp [countWord]
  · have hpos : 0 < (2:ℕ)^k := by positivity
    have hs : n.size ≤ k+1 := Nat.size_le.mpr (by rw [pow_succ]; omega)
    simpa only [countWord,if_neg hn,←Nat.size_eq_bits_len] using hs.trans (Nat.le_succ _)

theorem count_le {p m : ℕ} [Fact p.Prime] (D : Fin m → Finset (ZMod p)ˣ) (X : (ZMod p)ˣ) (w : Word) : cnt D X w ≤ 2^(2*m*bitLen p) := by
  classical
  have hc : Fintype.card (ZMod p)ˣ ≤ 2^(bitLen p) := by
    apply le_trans _ (Nat.le_pow_clog (by decide) p)
    simpa using Fintype.card_le_of_injective (Units.val : (ZMod p)ˣ → ZMod p) Units.val_injective
  have hh := Nat.pow_le_pow_left hc m
  calc cnt D X w ≤ Fintype.card ((Fin m → (ZMod p)ˣ) × (Fin m → (ZMod p)ˣ)) := Finset.card_le_univ _
       _ = (Fintype.card (ZMod p)ˣ)^m * (Fintype.card (ZMod p)ˣ)^m := by simp [Fintype.card_fun]
       _ ≤ (2^(bitLen p))^m * (2^(bitLen p))^m := Nat.mul_le_mul hh hh
       _ = _ := by rw [←Nat.pow_mul,←Nat.pow_add]; congr 1; ring

abbrev budget (b : ℕ) := 1024*(b+2)*(b+2)

theorem blocks (b : ℕ) : blockCount b ≤ b+2 := by
  apply max_le (by omega) (Nat.ceil_le.mpr ?_)
  have u : Nat.clog 2 (b+2) ≤ b+2 := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 (Nat.lt_pow_self (by decide)).le
  have v : 1 ≤ Nat.clog 2 (b+2) := Nat.clog_pos (by decide) (by omega)
  exact (Real.rpow_le_self_of_one_le (by exact_mod_cast v) (by norm_num)).trans (by exact_mod_cast u)

theorem bound0 (p : ℕ) : 128*(nbit p+bitLen p+2) ≤ budget (bitLen p) := by
  unfold nbit budget
  have h := Nat.mul_le_mul_right (bitLen p) (blocks (bitLen p)); nlinarith

variable {p : ℕ} [Fact p.Prime] {T : ℕ} (S : FpSeed p (blockCount (bitLen p))) (X : (ZMod p)ˣ)

theorem lengths (hok : m89_fp_plan_ok (some (T,S))) :
    (∀ k, k ≤ nbit p → (pair (st (T:=T) S X k) (ans (T:=T) S X k)).length ≤ budget (bitLen p)) ∧
    (∀ k, k < nbit p → (pair (st (T:=T) S X (k+1)) (query (T:=T) S X k)).length ≤ budget (bitLen p) ∧ (ans (T:=T) S X (k+1)).length ≤ budget (bitLen p)) := by
  let b := bitLen p; let n := nbit p
  have hpow : p ≤ 2^b := Nat.le_pow_clog (by decide) _
  have hp := cw b p hpow
  have hx := cw b (X : ZMod p).val ((ZMod.val_lt _).le.trans hpow)
  have ht := cw b T (le_trans (hok.2.2.1 ▸ threshold_le (le_max_left ..) hok.1 hok.2.1) hpow)
  have hseed : (List.ofFn (fpBits S)).length = n := by simp only [List.length_ofFn]; dsimp [n,nbit]; ring
  have hd : (data X).length ≤ 4*b+13 := by unfold data px encodeNatListBin; simp only [econs,enil]; omega
  have hplan : (plan (T:=T) S).length ≤ 2*b+2*n+10 := by unfold plan m89_fp_plan_word; simp only [List.length_cons,econs,enil,id_eq,hseed]; omega
  have hcnt (k : ℕ) := cw n _ (count_le (D (T:=T) S) X (pre (T:=T) S X k ++ [false]))
  have han (k : ℕ) : (ans (T:=T) S X (k+1)).length ≤ 2*n+7 := by unfold ans encodeNatListBin leftCount; simp only [econs,enil]; specialize hcnt k; omega
  have hst (k : ℕ) (hk : k ≤ n) : (st (T:=T) S X (k+1)).length ≤ 12*b+6*n+60 := by unfold st state; simp only [econs,enil,id_eq,pre,path_length]; omega
  have htag : (countWord 5).length = 3 := by decide
  have hq (k : ℕ) (hk : k ≤ n) : (query (T:=T) S X k).length ≤ 6*b+4*n+40 := by unfold query queryWord; simp only [econs,enil,id_eq,hseed,htag,List.length_append,List.length_cons,List.length_nil,pre,path_length]; omega
  have key : 128*(n+b+2) ≤ budget b := bound0 p
  constructor
  · intro k hk
    cases k with
    | zero => simp only [st,ans,pair_len,econs,enil,id_eq,List.length_nil]; change _ ≤ budget b; omega
    | succ k => have h1 := hst k (by change k+1 ≤ n at hk; omega); have h2 := han k; rw [pair_len]; change _ ≤ budget b; omega
  · intro k hk
    have h1 := hst k hk.le; have h2 := han k; have h3 := hq k hk.le; rw [pair_len]; change _ ≤ budget b ∧ _ ≤ budget b; omega

end DetDLP.m89_decode_lengths

set_option autoImplicit false
namespace DetDLP.m89_decode_cost
open Groundwork
private theorem scale_ge_one {b : ℕ} (hb : 1 ≤ b) : 1 ≤ (b : ℝ) / (logSafe b)^((1:ℝ)/4) := by
  have hbr : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hl : logSafe b ≤ (b:ℝ) := by
    apply max_le hbr
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (by positivity)).mpr
    rw [Real.rpow_natCast]; apply max_le
    · exact_mod_cast (show 2 ≤ 2^b by exact le_trans (by decide : 2 ≤ 2^1) (Nat.pow_le_pow_right (by decide) hb))
    · exact_mod_cast (show b < 2^b from Nat.lt_two_pow_self).le
  have hg : 1 ≤ logSafe (b:ℝ) := le_max_left _ _
  have hp : (logSafe (b:ℝ))^((1:ℝ)/4) ≤ logSafe b := by
    simpa using Real.rpow_le_rpow_of_exponent_le hg (by norm_num : (1:ℝ)/4 ≤ 1)
  apply (one_le_div (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hg) _)).mpr
  exact hp.trans hl
private theorem absorb (K k b : ℕ) (hb : 1 ≤ b) : (K:ℝ) * (mainSpaceBound k b)^3 ≤ mainSpaceBound (K+3*k) b := by
  let s := (b:ℝ)/(logSafe b)^((1:ℝ)/4)
  have hs : 1 ≤ s := scale_ge_one hb
  have rwW (j : ℕ) : mainSpaceBound j b = (2:ℝ)^((j:ℝ)*s) := by unfold mainSpaceBound s; congr 1; ring
  rw [rwW,rwW,← Real.rpow_mul_natCast (by norm_num)]
  have hK : (K:ℝ) ≤ (2:ℝ)^((K:ℝ)*s) := by
    calc (K:ℝ) ≤ (2:ℝ)^(K:ℝ) := by rw [Real.rpow_natCast]; exact_mod_cast (show K < 2^K from Nat.lt_two_pow_self).le
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [Nat.cast_nonneg (α:=ℝ) K])
  calc _ ≤ (2:ℝ)^((K:ℝ)*s) * (2:ℝ)^((k:ℝ)*s*(3:ℕ)) := mul_le_mul_of_nonneg_right hK (by positivity)
       _ = _ := by rw [← Real.rpow_add (by norm_num)]; push_cast; congr 1; ring


def budget (b : ℕ) := 1024*(b+2)*(b+2)
private def P (c b : ℕ) := c*(b+1)^c
private theorem Pb (c : ℕ) : PB (P c) := ⟨c,fun _ => le_rfl⟩
private theorem budgetPB : PB budget := by
  have hi : PB (fun n : ℕ => n) := ⟨1,by simp⟩
  have hb := hi.add (PB.const 2)
  exact ((PB.const 1024).mul hb).mul hb

private theorem Pr (c b : ℕ) : (P c b : ℝ) = polyBound c b := by simp [P,polyBound]

theorem budgets (k j : ℕ) : ∃ K : ℕ, ∀ (p : ℕ), 2 ≤ p → let b := bitLen p
    ∀ r : ℕ, r ≤ budget b →
    (r:ℝ) * (polyBound k (budget b) + k*(mainSpaceBound j b + polyBound j b + 1)) ≤ mainSpaceBound K b ∧
    polyBound k (budget b) + k*(polyBound j b+1) ≤ polyBound K b := by
  let F := fun b => P k (budget b) + k*(P j b + 1)
  have hF : PB F := ((Pb k).comp budgetPB).add ((PB.const k).mul ((Pb j).add (PB.const 1)))
  obtain ⟨a,ha⟩ := hF
  obtain ⟨d,hd⟩ := budgetPB
  obtain ⟨e,he⟩ := stage1_complexity_dominance.2.2.1 (max a d) 0
  let c := max e j
  let K := max a ((k+1)+3*c)
  refine ⟨K,?_⟩; intro p hp b r hr
  have hb : 1 ≤ b := Nat.clog_pos (by decide) hp
  have bound (i : ℕ) (hi : i ≤ max a d) : polyBound i b ≤ mainSpaceBound c b :=
    ((stage1_complexity_dominance.1 _ _ _ hi).2.trans (he p 0 hp (by omega)).1).trans (stage1_complexity_dominance.1 e c b (le_max_left ..)).1
  have rf : (r:ℝ) ≤ mainSpaceBound c b := by
    apply le_trans _ (bound d (le_max_right ..)); rw [←Pr]; exact_mod_cast hr.trans (hd b)
  have sf : polyBound k (budget b) + k*(polyBound j b+1) ≤ polyBound a b := by
    rw [←Pr,←Pr,←Pr]; exact_mod_cast ha b
  have sm := sf.trans (bound a (le_max_left ..))
  have sj := (stage1_complexity_dominance.1 j c b (le_max_right ..)).1
  have h1 : 1 ≤ mainSpaceBound c b := by unfold mainSpaceBound; apply Real.one_le_rpow (by norm_num); apply div_nonneg (by positivity) (Real.rpow_nonneg ((le_max_left 1 _).trans' zero_le_one) _)
  refine ⟨?_,sf.trans (stage1_complexity_dominance.1 a K b (le_max_left ..)).2⟩
  have base : polyBound k (budget b) + k*(mainSpaceBound j b + polyBound j b + 1) ≤ ((k:ℝ)+1)*mainSpaceBound c b := by nlinarith only [sm,mul_le_mul_of_nonneg_left sj (Nat.cast_nonneg (α:=ℝ) k)]
  have t := mul_le_mul rf base (by unfold polyBound mainSpaceBound; positivity) (by positivity)
  apply t.trans; apply le_trans _ ((absorb (k+1) c b hb).trans (stage1_complexity_dominance.1 _ K b (le_max_right ..)).1)
  rw [Nat.cast_add_one]; generalize mainSpaceBound c b = v at *
  have hh := mul_le_mul_of_nonneg_right h1 (sq_nonneg v)
  nlinarith only [mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (k:ℝ)+1)]
end DetDLP.m89_decode_cost


