-- Prove2me | Definitions.Def_DetDLP_W3C_PrefixDescent
-- name    : DetDLP_W3C_PrefixDescent
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:01:32.200088+00:00
-- url     : https://prove2.me/theorems/04b3824b-4a31-4b05-9d75-c9eb9052ceff
-- title:
--   Stage II exact Newton readout and greedy prefix descent
-- statement:
--   Proves exact arithmetic Newton readout of separator mass, Proposition 4.1 zero-mass termination, binary prefix mass conservation, and L-step greedy prefix descent to a violated shift row.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3_Driver
import Definitions.Def_DetDLP_W5_M6Sort
import Theorems.Thm_DetDLP_proposition_4_1_fixed_shift_soundness

set_option autoImplicit false
namespace DetDLP

/-- Evaluate the Newton difference as integer arithmetic, without building a polynomial. -/
def w3c_coeff (s M j : ℕ) : ℤ := ∑ t ∈ Finset.range (j+1),
  (-1 : ℤ)^(j-t) * (Nat.choose j t : ℤ) *
    ∏ k ∈ Finset.range (2*s+1), ((t:ℤ) - (1+(-(s:ℤ)+k)*M))^2

/-- Decode a contraction packet and return the least nonnegative Newton scalar. -/
def w3c_readout (m M prec len : ℕ) (w : List Bool) : ℤ :=
  let c := w5_M6Sort.decode w
  ((∑ j : Fin len, w3c_coeff (2*m) M j * (c.getD j 0 : ℤ)) % (2:ℤ)^prec)

theorem w3c_readout_correct {q : w3_Query} {C : ℕ} (n : w3_Net q C) {w : List Bool}
    (hw : EncodesTruncPoly (w3_precision q) (w3_len q) w (BTNContract n.G n.T)) :
    w3c_readout q.m q.M (w3_precision q) (w3_len q) w = w3_mass q := by
  obtain ⟨c,hc,rfl,h⟩ := hw
  have eqc (j : ℕ) : w3c_coeff (2*q.m) q.M j = newtonCoeff (2*q.m) q.M j := by
    simp only [w3c_coeff,newtonCoeff,filterPoly,Polynomial.eval_prod,Polynomial.eval_pow,
      Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,Int.Icc_eq_finset_map,Finset.prod_map]
    have hlen : (((2*q.m:ℕ):ℤ) + 1 - -((2*q.m:ℕ):ℤ)).toNat = 2*(2*q.m)+1 := by omega
    rw [hlen]; rfl
  rw [w3c_readout,w5_M6Sort.decode_encode,← n.readout c hc h]
  simp only [eqc, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (Fin.isLt _)]
  let a : ℤ := ∑ j : Fin (w3_len q), newtonCoeff (2*q.m) q.M j * (c j : ℤ)
  change a % (2:ℤ)^w3_precision q = _
  have ha := ZMod.val_intCast (n := 2^w3_precision q) a
  push_cast at ha; rw [← ha]; simp [a]

variable (q : w3_Query)
private abbrev Pair := q.FB.BlockTuple × q.FB.BlockTuple
private noncomputable abbrev wt (t : Pair q) := (filterPoly (2*q.m) q.M).eval (w3_delta q.FB q.M q.y t.1 t.2)
private lemma nonneg (t : Pair q) : 0 ≤ wt q t := by
  simp only [wt, filterPoly, Polynomial.eval_prod, Polynomial.eval_pow]
  exact Finset.prod_nonneg fun _ _ => sq_nonneg _

/-- Change the mathematical prefix only; mass does not consult the machine input field. -/
noncomputable def w3c_massAt (p : List Bool) := w3_mass {q with pre := p}
private noncomputable def term (p : List Bool) (t : Pair q) : ℤ := by
  classical exact if q.FB.tupleVal t.2 = q.FB.tupleVal t.1 + q.P ∧ p <+: q.code t.1 t.2 then wt q t else 0
private lemma sum_eq (p : List Bool) : w3c_massAt q p = ∑ t, term q p t := by
  classical unfold w3c_massAt w3_mass term w3_valid; apply Finset.sum_congr rfl; intro t _; split_ifs <;> rfl

theorem w3c_mass_nonneg : 0 ≤ w3_mass q := by
  change 0 ≤ w3c_massAt q q.pre
  rw [sum_eq]; exact Finset.sum_nonneg fun t _ => by unfold term; split <;> first | exact nonneg q t | rfl

private lemma row_iff (t : Pair q) : w3_holds (w3_shiftRow q.FB q.M t.1 t.2) q.y ↔
    ((w3_delta q.FB q.M q.y t.1 t.2 : ℤ) : ZMod q.M) = 1 := by
  simp [w3_holds,w3_shiftRow,w3_delta,IndexedFactorBase.tupleLabelSum,sub_mul,
    Finset.sum_sub_distrib]

private lemma zero_row (t : Pair q) (h : wt q t = 0) : w3_holds (w3_shiftRow q.FB q.M t.1 t.2) q.y := by
  simp [wt,filterPoly,Polynomial.eval_prod,Finset.prod_eq_zero_iff] at h
  obtain ⟨k,_,hk⟩ := h
  apply (row_iff q t).2
  rw [sub_eq_zero.mp hk]; simp

/-- No coverage hypothesis is needed to pass all represented shifts. -/
theorem w3c_zero_pass (hp : q.pre = []) (h : w3_mass q = 0) : w3_pass q.FB q.M q.P q.y := by
  classical
  change w3c_massAt q q.pre = 0 at h
  rw [hp,sum_eq] at h
  intro X Y hg
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (f := term q []) (fun t _ => by
    unfold term; split <;> first | exact nonneg q t | rfl)).mp h (X,Y) (Finset.mem_univ _)
  apply zero_row q (X,Y); simpa [term,hg] using hz

/-- With Stage I coverage and initialization, vanishing root mass recovers every label. -/
theorem w3c_zero_recover [Fintype q.V] [DecidableEq q.V] (hM : 2 ≤ q.M)
    (card : Fintype.card q.V = q.M) (Q : q.V) (gen : addOrderOf q.P = q.M)
    (cover : Function.Surjective q.FB.tupleVal) (U : Fin q.FB.totalCoords → q.FB.BlockTuple)
    (hU : ∀ j, q.FB.tupleVal (U j) = q.FB.elem q.P Q j) (lam : w3_Label q.M q.FB.totalCoords)
    (hlam : ∀ j, (lam j).val • q.P = q.FB.elem q.P Q j) (init : q.FB.SatisfiesInitialCongruences q.M U q.y)
    (hp : q.pre = []) (h : w3_mass q = 0) : ∀ j, q.y j = lam j :=
  proposition_4_1_fixed_shift_soundness q.M hM card q.P Q gen q.FB cover U hU lam hlam q.y init
    (fun X Y hXY => (row_iff q (X,Y)).mp (w3c_zero_pass q hp h X Y hXY))

private lemma tuple_bound (X : q.FB.BlockTuple) : 0 ≤ q.FB.tupleLabelSum q.M q.y X ∧
    q.FB.tupleLabelSum q.M q.y X ≤ ((2*q.m:ℕ):ℤ)*((q.M:ℤ)-1) := by
  have slots : q.FB.tupleLabelSum q.M q.y X = ∑ i, ∑ k, ((q.y (q.FB.coordOf i (X i k))).val : ℤ) := by
    simp only [IndexedFactorBase.tupleLabelSum,IndexedFactorBase.tupleCnt,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.sum_mul]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _; simp [ite_mul]
  rw [slots]; constructor
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => by positivity
  calc _ ≤ ∑ _i : Fin q.m, ∑ _k : Fin 2, ((q.M:ℤ)-1) := by
              gcongr with i _ k; have := (q.y (q.FB.coordOf i (X i k))).val_lt; omega
       _ = _ := by simp; ring

private lemma bad_row (t : Pair q) (hM : 2 ≤ q.M) (hw : 0 < wt q t) : ¬w3_holds (w3_shiftRow q.FB q.M t.1 t.2) q.y := by
  intro hr
  let d := w3_delta q.FB q.M q.y t.1 t.2
  have hc : (d : ZMod q.M) = ((1:ℤ):ZMod q.M) := by simpa [d] using (row_iff q t).mp hr
  obtain ⟨j,hj⟩ := Int.modEq_iff_dvd.mp ((ZMod.intCast_eq_intCast_iff d 1 q.M).mp hc)
  have hx := tuple_bound q t.1; have hy := tuple_bound q t.2
  have hd : d = q.FB.tupleLabelSum q.M q.y t.2 - q.FB.tupleLabelSum q.M q.y t.1 := rfl
  have hm : (2:ℤ) ≤ q.M := by exact_mod_cast hM
  have hjmem : -j ∈ Finset.Icc (-((2*q.m:ℕ):ℤ)) ((2*q.m:ℕ):ℤ) := by
    rw [Finset.mem_Icc]; constructor <;> by_contra! h <;> push_cast at * <;> nlinarith
  have hz : wt q t = 0 := by
    simp only [wt,filterPoly,Polynomial.eval_prod,Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
    apply Finset.prod_eq_zero hjmem; change (d - (1 + -j * q.M))^2 = 0; have : d - (1 + -j*q.M) = 0 := by nlinarith
    rw [this]; decide
  omega

/-- Fixed width partitions every internal prefix into two disjoint children. -/
theorem w3c_split {L : ℕ} (width : ∀ X Y, (q.code X Y).length = L) {p : List Bool} (hp : p.length < L) :
    w3c_massAt q p = w3c_massAt q (p++[false]) + w3c_massAt q (p++[true]) := by
  classical
  simp only [sum_eq,← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro t _
  by_cases h : p <+: q.code t.1 t.2
  · obtain ⟨r,hr⟩ := h
    have hl := width t.1 t.2
    cases r with
    | nil => simp_all
    | cons b r => cases b <;> by_cases hg : q.FB.tupleVal t.2 = q.FB.tupleVal t.1 + q.P <;>
        simp [term,hg,← hr,List.prefix_append_right_inj]
  · have hn (b : Bool) : ¬ p++[b] <+: q.code t.1 t.2 := fun hh => h ((List.prefix_append _ _).trans hh)
    simp [term,h,hn]

/-- Greedy search uses one left-child mass query per bit and prefers false on ties. -/
def DetDLP_W3C_PrefixSearch (mass : List Bool → ℤ) : ℕ → List Bool
  | 0 => []
  | n+1 => let p := DetDLP_W3C_PrefixSearch mass n; p ++ [decide (mass (p++[false]) ≤ 0)]

theorem w3c_descent {L : ℕ} (width : ∀ X Y, (q.code X Y).length = L)
    (inj : Function.Injective (Function.uncurry q.code)) (hM : 2 ≤ q.M) (root : 0 < w3c_massAt q []) :
    let p := DetDLP_W3C_PrefixSearch (w3c_massAt q) L
    p.length = L ∧ 0 < w3c_massAt q p ∧ ∃! t : q.FB.BlockTuple × q.FB.BlockTuple,
      q.code t.1 t.2 = p ∧ q.FB.tupleVal t.2 = q.FB.tupleVal t.1 + q.P ∧
      0 < (filterPoly (2*q.m) q.M).eval (w3_delta q.FB q.M q.y t.1 t.2) ∧
      ¬ w3_holds (w3_shiftRow q.FB q.M t.1 t.2) q.y := by
  classical
  let path := DetDLP_W3C_PrefixSearch (w3c_massAt q)
  have inv (i : ℕ) (hi : i ≤ L) : (path i).length = i ∧ 0 < w3c_massAt q (path i) := by
    induction i with
    | zero => exact ⟨rfl,root⟩
    | succ i ih =>
      obtain ⟨hl,hm⟩ := ih (by omega)
      have hs := w3c_split q width (p := path i) (by omega)
      change ((path i) ++ [_]).length = i+1 ∧ _
      constructor
      · simp [hl]
      · change 0 < w3c_massAt q (path i ++ [decide (w3c_massAt q (path i ++ [false]) ≤ 0)])
        by_cases hh : w3c_massAt q (path i ++ [false]) ≤ 0 <;> simp [hh] <;> omega
  obtain ⟨hl,hm⟩ := inv L le_rfl
  refine ⟨hl,hm,?_⟩
  rw [sum_eq] at hm
  have hex : ∃ t, 0 < term q (path L) t := by
    by_contra! hn; exact hm.not_ge (Finset.sum_nonpos fun t _ => hn t)
  obtain ⟨t,ht⟩ := hex
  unfold term at ht; split at ht
  · rename_i hv
    have he : q.code t.1 t.2 = path L := hv.2.eq_of_length (by rw [hl,width]) |>.symm
    exact ⟨t,⟨he,hv.1,ht,bad_row q t hM ht⟩,fun u hu => inj (hu.1.trans he.symm)⟩
  · omega

end DetDLP


