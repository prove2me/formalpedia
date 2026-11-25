-- Prove2me | Definitions.Def_DetDLP_S8E_ECTrace
-- name    : DetDLP_S8E_ECTrace
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:45:23.223523+00:00
-- url     : https://prove2.me/theorems/769434c3-7563-44f8-ba1e-afdaaac666c9
-- title:
--   EC prefix decoder: ECTrace
-- statement:
--   Word-level components and correctness interfaces for elliptic-curve decomposition by exact prefix counts.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_S8E_ECDecoder
import Definitions.Def_DetDLP_S8A_FpDecodeBounds
set_option autoImplicit false
namespace DetDLP.s8e
open M89S1 m89_enum_words Groundwork.PolyT
open m89_decode (path path_length path_spec W)
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
@[simp] theorem word_len {p : ℕ} [NeZero p] {E : WeierstrassCurve (ZMod p)} (b : ℕ) (P : E.toAffine.Point) : (ecWord b P).length = 2*b+1 := by cases P <;> simp [ecWord,digitWord] <;> omega
theorem tuple_length {p m : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)} (ab : (Fin m → E.toAffine.Point) × (Fin m → E.toAffine.Point)) :
    (tupleWord (ecWord (bitLen p)) ab).length = 2*m*(2*bitLen p+1) := by
  have gen (l : List (Fin m)) : (l.flatMap (fun i => (ecWord (bitLen p)) (ab.1 i) ++ (ecWord (bitLen p)) (ab.2 i))).length = 2*l.length*(2*bitLen p+1) := by
    induction l with
    | nil => simp
    | cons i l ih => simp [List.flatMap_cons,ih,word_len]; ring
  simpa [tupleWord] using gen (List.finRange m)

noncomputable def cnt {p m : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)} (D : Fin m → Finset E.toAffine.Point) (X : E.toAffine.Point) :=
  letI := ecPointFintype E
  pairCount D (ecWord (bitLen p)) (fun ab => (∑ i, (ab.1 i + ab.2 i)) = X)

theorem path_witness {p m : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)} (D : Fin m → Finset E.toAffine.Point) (X : E.toAffine.Point)
    (h : ∃ A B : Fin m → E.toAffine.Point, (∀ i, A i ∈ D i ∧ B i ∈ D i) ∧ (∑ i, (A i + B i)) = X) :
    ∃ A B : Fin m → E.toAffine.Point, (∀ i, A i ∈ D i ∧ B i ∈ D i) ∧ (∑ i, (A i + B i)) = X ∧
      tupleWord (ecWord (bitLen p)) (A,B) = path (cnt D X) (2*m*(2*bitLen p+1)) := by
  classical
  letI := ecPointFintype E
  let valid := fun ab : (Fin m → E.toAffine.Point) × (Fin m → E.toAffine.Point) =>
    (∀ i, ab.1 i ∈ D i ∧ ab.2 i ∈ D i) ∧ (∑ i, (ab.1 i + ab.2 i)) = X
  have hn (w : W) : 0 < cnt D X w ↔ ∃ ab, valid ab ∧ (tupleWord (ecWord (bitLen p)) ab).take w.length = w := by
    simp only [cnt,pairCount,Finset.card_pos,Finset.Nonempty,Finset.mem_filter,Finset.mem_univ,true_and,valid]
    exact exists_congr (fun _ => by tauto)
  obtain ⟨A,B,hmem,hprod⟩ := h
  obtain ⟨⟨a,b⟩,⟨ha,hb⟩,he⟩ := path_spec valid (tupleWord (ecWord (bitLen p))) _ (tuple_length (E:=E)) _ hn ⟨(A,B),hmem,hprod⟩
  exact ⟨a,b,ha,hb,he⟩

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


theorem threshold_le {p m g : ℕ} (hm : 2 ≤ m) (h64 : 64 ≤ g) (h4096 : 4096*m ≤ g-1) :
    hashThreshold p (g-1) m g ≤ p := by
  have hn : (64:ℝ) ≤ g := by exact_mod_cast h64
  have hg : ((g-1:ℕ):ℝ) = (g:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ g)]; norm_num
  have hp : 0 < ((g-1:ℕ):ℝ) := by rw [hg]; linarith
  have he : (1:ℝ)/(m:ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hm)
  have h16 : (16*(g:ℝ))^((1:ℝ)/(m:ℝ)) ≤ ((g-1:ℕ):ℝ) := by
    calc
      _ ≤ (16*(g:ℝ))^((1:ℝ)/2) := Real.rpow_le_rpow_of_exponent_le (by linarith) he
      _ ≤ (((g-1:ℕ):ℝ)^2)^((1:ℝ)/2) := Real.rpow_le_rpow (by positivity) (by rw [hg]; nlinarith [mul_nonneg (by linarith : 0 ≤ (g:ℝ)-18) (by positivity : 0 ≤ (g:ℝ))]) (by norm_num)
      _ = _ := by rw [← Real.rpow_natCast_mul hp.le]; norm_num
  have hq : qStar m g ≤ g-1 := max_le h4096 (Nat.ceil_le.mpr h16)
  apply Nat.ceil_le.mpr
  exact (div_le_iff₀ hp).mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hq) (by positivity))

private theorem point_dec {p : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)} (P : E.toAffine.Point) :
    onePoint (bitLen p) (ecWord (bitLen p) P) = encodeNatListBin (pointCoords P) := by
  let b := bitLen p
  have coord_eq (x y : ℕ) (hx : x < 2^b) (hy : y < 2^b) :
      coord (digitWord b x ++ digitWord b y) b 0 = x ∧ coord (digitWord b x ++ digitWord b y) b 1 = y := by
    have hl : (digitWord b x).length = b := by simp [digitWord]
    have hly : (digitWord b y).length = b := by simp [digitWord]
    have ht : (digitWord b x ++ digitWord b y).take b = digitWord b x := by simpa only [hl] using List.take_left (l₁:=digitWord b x) (l₂:=digitWord b y)
    have hd : (digitWord b x ++ digitWord b y).drop b = digitWord b y := by simpa only [hl] using List.drop_left (l₁:=digitWord b x) (l₂:=digitWord b y)
    simp [coord,ht,hd,List.take_of_length_le hly.le,bval_digit _ _ hx,bval_digit _ _ hy]
  have hz : 0 < 2^b := by positivity
  have hv (z : ZMod p) : z.val < 2^b := (ZMod.val_lt z).trans_le (Nat.le_pow_clog (by decide) p)
  cases P with
  | zero => simpa [onePoint,ecWord,pointCoords,←show b=bitLen p from rfl,(coord_eq 0 0 hz hz).1,(coord_eq 0 0 hz hz).2]
  | some x y h => simpa [onePoint,ecWord,pointCoords,←show b=bitLen p from rfl,(coord_eq _ _ (hv x) (hv y)).1,(coord_eq _ _ (hv x) (hv y)).2]

private theorem slice {α : Type} (f : α → W) (d : ℕ) (hf : ∀ x, (f x).length = d) (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (((xs.flatMap f).drop (i*d)).take d) = f xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp only [List.flatMap_cons,Nat.zero_mul,List.drop_zero,List.getElem_cons_zero]; simpa only [hf] using List.take_left (l₁:=f x) (l₂:=xs.flatMap f)
    | succ i =>
      simp only [List.flatMap_cons,Nat.succ_mul,List.drop_append,hf,List.getElem_cons_succ]
      have hd : (f x).drop (i*d+d) = [] := List.drop_eq_nil_of_le (by rw [hf]; omega)
      simpa [hd] using ih i (by simpa using hi)

theorem finish_tuple {p m : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)} (A B : Fin m → E.toAffine.Point) :
    finish (bitLen p) (tupleWord (ecWord (bitLen p)) (A,B)) = encodeECDecomp A B := by
  let xs := (List.finRange m).flatMap (fun i => [A i,B i]); let b := bitLen p; let d := 2*b+1
  let f := ecWord (E:=E) b
  have flat : tupleWord f (A,B) = xs.flatMap f := by simp [tupleWord,xs,List.flatMap_assoc]
  have hf (x) : (f x).length = d := word_len ..
  have hl (l : List E.toAffine.Point) : (l.flatMap f).length = l.length*d := by
    induction l with | nil => simp | cons x l ih => simp [List.flatMap_cons,hf,ih,Nat.add_mul,Nat.add_comm]
  change finish b (tupleWord f (A,B)) = _; rw [flat]; unfold finish indices
  change Encoding.encodeList id (((List.range (xs.flatMap f).length).filter (fun i => decide (i < (xs.flatMap f).length/d))).map (fun i => onePoint b (((xs.flatMap f).drop (i*d)).take d))) = _
  have hd : 0 < d := Nat.zero_lt_succ _
  simp only [hl,Nat.mul_div_cancel _ hd,filter_range _ _ (Nat.le_mul_of_pos_right _ hd)]
  have he : Encoding.encodeList (fun P : E.toAffine.Point => encodeNatListBin (pointCoords P)) xs = Encoding.encodeList id (xs.map (fun P => encodeNatListBin (pointCoords P))) := by
    generalize xs = ys; induction ys with | nil => rfl | cons x ys ih => simp [Encoding.encodeList,ih]
  rw [show encodeECDecomp A B = _ from he]; congr 1
  apply List.ext_getElem (by simp); intro i hi hj
  simp only [List.getElem_map,List.getElem_range]; rw [slice f d hf xs i (by simpa using hj)]; exact point_dec _

end DetDLP.s8e
noncomputable section
namespace DetDLP.s8e
open M89S1 m89_decode_step m89_enum_words Groundwork.PolyT
open m89_decode (path path_length)
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
abbrev LR (O : PrimitiveMachine) (o : Fin O.tapeCount) (t s : ℝ) := Nat.rec (motive := fun _ => Word → Word → Word → ℕ → Prop)
  (fun _ _ _ _ => False) (fun _ prev st ans outW maxLen =>
    (s8e.step (pair st ans) = true :: outW ∧ (pair st ans).length ≤ maxLen ∧ outW.length ≤ maxLen) ∨
    (∃ st' q ans', s8e.step (pair st ans) = false :: pair st' q ∧ (pair st ans).length ≤ maxLen ∧
      (pair st' q).length ≤ maxLen ∧ ans'.length ≤ maxLen ∧ RunsWithin O o q ans' t s ∧ prev st' ans' outW maxLen))

theorem linearTrace {O : PrimitiveMachine} {o : Fin O.tapeCount} {t s : ℝ} {n N : ℕ} (st ans q : ℕ → Word) (outW : Word)
    (hcont : ∀ k, k < n → s8e.step (pair (st k) (ans k)) = false :: pair (st (k+1)) (q k))
    (hstop : s8e.step (pair (st n) (ans n)) = true :: outW)
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

variable {p : ℕ} [Fact p.Prime] {T : ℕ} (S : ECSeed p (blockCount (bitLen p))) {E : WeierstrassCurve (ZMod p)} (X : E.toAffine.Point)

abbrev D := ecFactorBlock E T S
abbrev nbit (p : ℕ) := 2*blockCount (bitLen p)*(2*bitLen p+1)
abbrev plan := m89_ec_plan_word (some (T,S))
abbrev data := Encoding.encodeList id [encodeCurveInput p E,encodeNatListBin (pointCoords X)]
noncomputable abbrev pre (k : ℕ) := path (cnt (D (E:=E) (T:=T) S) X) k
noncomputable abbrev leftCount (k : ℕ) := cnt (D (E:=E) (T:=T) S) X (pre (T:=T) S X k ++ [false])
noncomputable def st : ℕ → Word
  | 0 => Encoding.encodeList id [data X,plan (T:=T) S]
  | k+1 => state (data X) (plan (T:=T) S) (pre (T:=T) S X k)
noncomputable def ans : ℕ → Word
  | 0 => []
  | k+1 => encodeNatListBin [leftCount (T:=T) S X k]
noncomputable def query (k : ℕ) := queryWord 6 (encodeCurveInput p E) [countWord T,List.ofFn (ecBits S),encodeNatListBin (pointCoords X),pre (T:=T) S X k ++ [false]]

theorem stage (k : ℕ) : s8e.step (pair (st (T:=T) S X k) (ans (T:=T) S X k)) = s8e.advance (data X) (plan (T:=T) S) (pre (T:=T) S X k) := by
  cases k with
  | zero => exact step_start ..
  | succ k => exact step_next ..

private theorem width_eq (p : ℕ) (hp : 2 ≤ p) : (p-1).size = bitLen p := by
  apply le_antisymm
  · apply Nat.size_le.2; have h : p ≤ 2^(bitLen p) := Nat.le_pow_clog (by decide) _; omega
  · apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2; have h := Nat.size_le.mp (le_refl (p-1).size); omega

theorem advance_eq (k : ℕ) : s8e.advance (data X) (plan (T:=T) S) (pre (T:=T) S X k) =
    if k < nbit p then false :: pair (st (T:=T) S X (k+1)) (query (T:=T) S X k)
    else true :: finish (bitLen p) (pre (T:=T) S X k) := by
  let b := bitLen p; let m := blockCount b
  have hb : 0 < b := Nat.clog_pos (by decide) (Fact.out : Nat.Prime p).two_le
  have hs : (List.ofFn (ecBits S)).length = (2*m)*(2*b) := by simp only [List.length_ofFn]; change m*4*b=_; ring
  have hlen : (2*m)*(2*b) + ((2*m)*(2*b))/(2*b) = nbit p := by rw [Nat.mul_div_cancel _ (by omega)]; unfold nbit; dsimp [b,m]; ring
  simp only [s8e.advance,data,fields_encode,plan,m89_ec_plan_word,List.tail_cons,List.getD_cons_zero,List.getD_cons_succ,encodeCurveInput,w5_M6Sort.decode_encode,Nat.size_eq_bits_len,width_eq p (Fact.out : Nat.Prime p).two_le,hs,pre,path_length]; change (if k < (2*m)*(2*b) + ((2*m)*(2*b))/(2*b) then _ else _) = _; rw [hlen]; rfl

theorem next_query [E.IsElliptic] (hp : 3 < p) (hok : m89_ec_plan_ok E (some (T,S))) (k : ℕ) (hk : k < nbit p) :
    Query (query (T:=T) S X k) (bitLen p) (leftCount (T:=T) S X k) := by
  rcases hok with ⟨h64,h4096,hT,_⟩
  apply Query.ecPair p hp E T (hT ▸ threshold_le (le_max_left ..) h64 h4096) S X
  change k < 2*blockCount (bitLen p)*(2*bitLen p+1) at hk
  simp only [List.length_append,List.length_cons,List.length_nil,pre,path_length]; omega
end DetDLP.s8e


