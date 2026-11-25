-- Prove2me | Definitions.Def_DetDLP_S8A_FpPrefixSpec
-- name    : DetDLP_S8A_FpPrefixSpec
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:13:07.319454+00:00
-- url     : https://prove2.me/theorems/2d054d12-debb-46c3-994f-6f7885a9447e
-- title:
--   Correctness of finite-field prefix decoding
-- statement:
--   The path selected by left-prefix counts ends at a valid tuple. Each query on the path has the stated count; reading its fixed-width chunks and serializing their values yields the required interleaved factor decomposition.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_S8A_FpPrefixStep
set_option autoImplicit false
namespace DetDLP.m89_decode
open M89S1

abbrev W := List Bool

/-- The left query is the only count used at each level. -/
def path (count : W → ℕ) : ℕ → W
  | 0 => []
  | k+1 => let w := path count k; w ++ [decide (count (w ++ [false]) = 0)]

@[simp] theorem path_length (count : W → ℕ) (k : ℕ) : (path count k).length = k := by
  induction k with | zero => rfl | succ k ih => simp [path,ih]

theorem next_take (w : W) (k : ℕ) (h : k < w.length) :
    w.take (k+1) = w.take k ++ [w[k]] := by
  induction k generalizing w with
  | zero => cases w with
    | nil => exact False.elim (Nat.not_lt_zero _ h)
    | cons a w => rfl
  | succ k ih => cases w with
    | nil => simp at h
    | cons a v => simpa using ih v (by simpa using h)

theorem path_spec {α : Type} (valid : α → Prop) (word : α → W) (n : ℕ)
    (fixed : ∀ a, (word a).length = n) (count : W → ℕ)
    (pos : ∀ w, 0 < count w ↔ ∃ a, valid a ∧ (word a).take w.length = w)
    (existsValid : ∃ a, valid a) : ∃ a, valid a ∧ word a = path count n := by
  have extend (k : ℕ) (hk : k ≤ n) : ∃ a, valid a ∧ (word a).take k = path count k := by
    induction k with
    | zero => obtain ⟨a,ha⟩ := existsValid; exact ⟨a,ha,rfl⟩
    | succ k ih =>
      let w := path count k
      have len : (w ++ [false]).length = k+1 := by simp [w]
      by_cases hz : count (w ++ [false]) = 0
      · obtain ⟨a,ha,hw⟩ := ih (by omega)
        have hkn : k < (word a).length := by rw [fixed]; omega
        have bit : (word a)[k] = true := by
          cases he : (word a)[k] with
          | true => rfl
          | false =>
            have hp := (pos (w ++ [false])).2 ⟨a,ha,by rw [len,next_take _ _ hkn,hw,he]⟩
            omega
        exact ⟨a,ha,by rw [next_take _ _ hkn,hw,bit]; simp [path,←show w=path count k from rfl,hz]⟩
      · obtain ⟨a,ha,hw⟩ := (pos (w ++ [false])).1 (Nat.pos_of_ne_zero hz)
        rw [len] at hw
        exact ⟨a,ha,by simpa [path,←show w=path count k from rfl,hz] using hw⟩
  obtain ⟨a,ha,hw⟩ := extend n le_rfl
  exact ⟨a,ha,by simpa [←fixed a] using hw⟩

abbrev coeff {p : ℕ} [Fact p.Prime] (x : (ZMod p)ˣ) := digitWord (bitLen p) (x : ZMod p).val

theorem tuple_length {p m : ℕ} [Fact p.Prime] (ab : (Fin m → (ZMod p)ˣ) × (Fin m → (ZMod p)ˣ)) :
    (tupleWord coeff ab).length = 2*m*bitLen p := by
  have gen (l : List (Fin m)) : (l.flatMap (fun i => coeff (ab.1 i) ++ coeff (ab.2 i))).length = 2*l.length*bitLen p := by
    induction l with
    | nil => simp
    | cons i l ih => simp [List.flatMap_cons,ih,coeff,digitWord]; ring
  simpa [tupleWord] using gen (List.finRange m)

noncomputable def cnt {p m : ℕ} [Fact p.Prime] (D : Fin m → Finset (ZMod p)ˣ) (X : (ZMod p)ˣ) :=
  pairCount D coeff (fun ab => (∏ i, (ab.1 i * ab.2 i)) = X)

theorem path_witness {p m : ℕ} [Fact p.Prime] (D : Fin m → Finset (ZMod p)ˣ) (X : (ZMod p)ˣ)
    (h : ∃ A B : Fin m → (ZMod p)ˣ, (∀ i, A i ∈ D i ∧ B i ∈ D i) ∧ (∏ i, (A i * B i)) = X) :
    ∃ A B : Fin m → (ZMod p)ˣ, (∀ i, A i ∈ D i ∧ B i ∈ D i) ∧ (∏ i, (A i * B i)) = X ∧
      tupleWord coeff (A,B) = path (cnt D X) (2*m*bitLen p) := by
  classical
  let valid := fun ab : (Fin m → (ZMod p)ˣ) × (Fin m → (ZMod p)ˣ) =>
    (∀ i, ab.1 i ∈ D i ∧ ab.2 i ∈ D i) ∧ (∏ i, (ab.1 i * ab.2 i)) = X
  have hn (w : W) : 0 < cnt D X w ↔ ∃ ab, valid ab ∧ (tupleWord coeff ab).take w.length = w := by
    simp only [cnt,pairCount,Finset.card_pos,Finset.Nonempty,Finset.mem_filter,Finset.mem_univ,true_and,valid]
    exact exists_congr (fun _ => by tauto)
  obtain ⟨A,B,hmem,hprod⟩ := h
  obtain ⟨⟨a,b⟩,⟨ha,hb⟩,he⟩ := path_spec valid (tupleWord coeff) _ tuple_length _ hn ⟨(A,B),hmem,hprod⟩
  exact ⟨a,b,ha,hb,he⟩

end DetDLP.m89_decode
set_option autoImplicit false
namespace DetDLP.m89_decode
open M89S1 OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem threshold_le {p m : ℕ} (hm : 2 ≤ m) (h64 : 64 ≤ p-1) (h4096 : 4096*m ≤ p-1) :
    hashThreshold p (p-1) m (p-1) ≤ p := by
  let n := p-1
  have hn : (64:ℝ) ≤ (n:ℝ) := by exact_mod_cast h64
  have hp : 0 < (n:ℝ) := by linarith
  have he : (1:ℝ)/(m:ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hm)
  have h16 : (16*(n:ℝ))^((1:ℝ)/(m:ℝ)) ≤ (n:ℝ) := by
    calc
      _ ≤ (16*(n:ℝ))^((1:ℝ)/2) := Real.rpow_le_rpow_of_exponent_le (by linarith) he
      _ ≤ ((n:ℝ)^2)^((1:ℝ)/2) := Real.rpow_le_rpow (by positivity) (by nlinarith [mul_nonneg (by linarith : 0 ≤ (n:ℝ)-16) hp.le]) (by norm_num)
      _ = _ := by rw [← Real.rpow_natCast_mul hp.le]; norm_num
  have hq : qStar m n ≤ n := max_le h4096 (Nat.ceil_le.mpr h16)
  change Nat.ceil ((p:ℝ)*(qStar m n:ℝ)/(n:ℝ)) ≤ p
  apply Nat.ceil_le.mpr
  exact (div_le_iff₀ hp).mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hq) (by positivity))

theorem next_query {p : ℕ} [Fact p.Prime] {T : ℕ} {S : FpSeed p (blockCount (bitLen p))}
    (hok : m89_fp_plan_ok (some (T,S))) (X : (ZMod p)ˣ) (k : ℕ) (hk : k < 2*blockCount (bitLen p)*bitLen p) :
    let D := fpFactorBlock (p:=p) T S
    let η := path (cnt D X) k ++ [false]
    Query (queryWord 5 (countWord p) [countWord T,List.ofFn (fpBits S),countWord (X : ZMod p).val,η]) (bitLen p) (cnt D X η) := by
  intro D η
  rcases hok with ⟨h64,h4096,hT,_⟩
  refine Query.fpPair p T (hT ▸ threshold_le (le_max_left ..) h64 h4096) S X η ?_
  simpa [η] using hk

end DetDLP.m89_decode
set_option autoImplicit false
namespace DetDLP.m89_decode_finish
open M89S1 m89_decode m89_enum_words m89_decode_step Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem bval_fixed (b n : ℕ) (hn : n < 2^b) : bval (List.ofFn (fun i : Fin b => n.testBit i.val)) = n := by
  induction b generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    subst n; rfl
  | succ b ih =>
    rw [List.ofFn_succ,bval_cons]
    simp only [Fin.val_zero,Fin.val_succ,Nat.testBit_succ]
    rw [ih (n/2) ((Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa [pow_succ] using hn)),Nat.testBit_zero]
    by_cases h : n % 2 = 1 <;> simp [h] <;> omega

private theorem bval_digit (b n : ℕ) (hn : n < 2^b) : bval (digitWord b n).reverse = n := by
  apply Eq.trans _ (bval_fixed b n hn); apply congrArg bval
  apply List.ext_getElem (by simp [digitWord]); intro j hj hk
  simp only [digitWord,List.getElem_reverse,List.getElem_ofFn,List.length_ofFn,Fin.val_rev]
  congr 1; simp only [List.length_ofFn] at hk; omega

private theorem filter_range (l t : ℕ) (ht : t ≤ l) : (List.range l).filter (fun u => decide (u<t)) = List.range t := by
  induction l, ht using Nat.le_induction with
  | base => apply List.filter_eq_self.mpr; intro a h; simpa using h
  | succ l hl ih => rw [List.range_succ,List.filter_append,ih]; simp [Nat.not_lt.mpr hl]


private theorem packed_length (b : ℕ) (ns : List ℕ) : (ns.flatMap (digitWord b)).length = ns.length * b := by
  induction ns with
  | nil => simp
  | cons n ns ih => rw [List.flatMap_cons,List.length_append,ih]; simp [digitWord,Nat.succ_mul,Nat.add_comm]

private theorem slice (b : ℕ) (ns : List ℕ) (i : ℕ) (hi : i < ns.length) :
    (((ns.flatMap (digitWord b)).drop (i*b)).take b) = digitWord b ns[i] := by
  induction ns generalizing i with
  | nil => simp at hi
  | cons n ns ih =>
    have hlen : (digitWord b n).length = b := by simp [digitWord]
    cases i with
    | zero => simp only [List.flatMap_cons, Nat.zero_mul, List.drop_zero, List.getElem_cons_zero]; simpa only [hlen] using List.take_left (l₁ := digitWord b n) (l₂ := ns.flatMap (digitWord b))
    | succ i =>
      simp only [List.flatMap_cons, Nat.succ_mul, List.drop_append, hlen, List.getElem_cons_succ]
      have hd : (digitWord b n).drop (i*b+b) = [] := List.drop_eq_nil_of_le (by rw [hlen]; omega)
      simpa [hd] using ih i (by simpa using hi)

theorem finish_packed (b : ℕ) (hb : 0 < b) (ns : List ℕ) (hn : ∀ x ∈ ns, x < 2^b) :
    fpFinish b (ns.flatMap (digitWord b)) = encodeNatListBin ns := by
  unfold fpFinish indices
  simp only [packed_length,Nat.mul_div_cancel _ hb]
  rw [filter_range _ _ (Nat.le_mul_of_pos_right _ hb)]
  congr 1
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map,List.getElem_range,coord,slice b ns i hj]
  exact bval_digit b _ (hn _ (List.getElem_mem ..))

theorem finish_tuple {p m : ℕ} [Fact p.Prime] (A B : Fin m → (ZMod p)ˣ) :
    fpFinish (bitLen p) (tupleWord coeff (A,B)) = encodeFpDecomp A B := by
  let ns := (List.finRange m).flatMap (fun i => [(A i : ZMod p).val,(B i : ZMod p).val])
  have flat : tupleWord coeff (A,B) = ns.flatMap (digitWord (bitLen p)) := by
    simp [ns,tupleWord,coeff,List.flatMap_assoc]
  rw [flat]; apply finish_packed _ (Nat.clog_pos (by decide) (Fact.out : Nat.Prime p).two_le)
  intro x hx
  obtain ⟨i,_,h⟩ := List.mem_flatMap.mp hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl <;> exact (ZMod.val_lt _).trans_le (Nat.le_pow_clog (by decide) p)

end DetDLP.m89_decode_finish


