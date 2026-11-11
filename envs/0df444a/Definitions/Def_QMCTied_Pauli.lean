-- Prove2me | Definitions.Def_QMCTied_Pauli
-- name    : QMCTied_Pauli
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T10:16:40.118761+00:00
-- url     : https://prove2.me/theorems/cd7120a8-4cd1-450f-85aa-5bcb341385f8
-- title:
--   The Pauli moment relaxation as a tied-entry SDP instance
-- statement:
--   The rows computed by the program are exactly the Pauli words of support at most $k$, each once. With classes given by product words and signs by the real parts of phases, the instance's Gram matrix is the level-$k$ real Gram matrix reindexed, so feasibility transfers in both directions, and the relaxation objective equals the total weight times the normalized instance objective. The program's sign and class tables represent the instance.
-- source:
--   Supporting library for QuantumMaxCutEnergy.PauliSDP.uniform_value_lower_approximation_compiler (Prove2me Quantum Max-Cut campaign; level-k Pauli moment relaxation as in Gribling, Sinjorgo and Sotirov, arXiv:2504.11120, Section 2). Method: integer penalty supergradient iteration with matrix-power certificates.

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Definitions.Def_QMCSub_LinAlg
import Definitions.Def_QMCSub_Lap
import Definitions.Def_QMCSub_Edge
import Definitions.Def_QMCSub_Bridge1
import Definitions.Def_QMCTied_Defs
import Definitions.Def_QMCTied_Prog

/-!
The level-`k` Pauli moment relaxation of an input graph as a tied-entry SDP instance whose rows,
signs, classes and objective coefficients are the ones computed by the list program.
-/

namespace QMCTied
open QuantumMaxCutEnergy QMCNumericRuntime QMCSub
open scoped BigOperators

/-- Decode a rational label. -/
def lab (q : ℚ) : Fin 4 := if q = 1 then 1 else if q = 2 then 2 else if q = 3 then 3 else 0

/-- Decode a list word into a Pauli word on `n` sites. -/
def decW (n : ℕ) (w : Vec) : PauliSDP.Word n := fun p => lab (gv w p.val)

/-- The program's row list for an input graph. -/
abbrev RW (k : ℕ) (G : Input) : List Vec := rowsW k (List.range G.n)

/-- The Pauli instance: classes are product words, signs are real parts of phases, and the
objective coefficients are read off the program's table. -/
noncomputable def pauliInst (k : ℕ) (G : Input) :
    Inst (RW k G).length (PauliSDP.Word G.n) where
  cls i j := PauliSDP.wordProduct (decW G.n (rowAt (RW k G) i)) (decW G.n (rowAt (RW k G) j))
  sgn i j := ⌊(PauliSDP.wordPhase (decW G.n (rowAt (RW k G) i))
    (decW G.n (rowAt (RW k G) j))).re⌋
  k0 := PauliSDP.identityWord G.n
  Cs i j := gm (csTabW (List.range G.n) (RW k G) (inputEdges G)) i j
  c0 := 1 / 2

/-! ### Encoded words -/

/-- Encode a Pauli word as a dense list of rational labels. -/
def enc {n : ℕ} (P : PauliSDP.Word n) : Vec := List.ofFn (fun p => (((P p).val : ℕ) : ℚ))

theorem gv_enc {n : ℕ} (P : PauliSDP.Word n) (p : Fin n) :
    gv (enc P) p.val = (((P p).val : ℕ) : ℚ) := by
  simp [gv, enc]

theorem lab_val (a : Fin 4) : lab (((a.val : ℕ) : ℚ)) = a := by
  fin_cases a <;> simp [lab]

theorem decW_enc {n : ℕ} (P : PauliSDP.Word n) : decW n (enc P) = P := by
  funext p
  simp only [decW, gv_enc, lab_val]

theorem enc_injective {n : ℕ} : Function.Injective (enc (n := n)) := fun P Q h => by
  rw [← decW_enc P, ← decW_enc Q, h]

theorem zeroW_eq (n : ℕ) : zeroW (List.range n) = enc (PauliSDP.identityWord n) :=
  map_range_congr n _ _ (fun i => by simp [PauliSDP.identityWord])

theorem setW_enc {n : ℕ} (P : PauliSDP.Word n) (p : Fin n) (a : Fin 4) :
    setW (List.range n) (enc P) p.val (((a.val : ℕ) : ℚ)) = enc (Function.update P p a) := by
  refine map_range_congr n _ _ (fun q => ?_)
  by_cases h : q = p
  · subst h
    simp
  · have h' : ¬ q.val = p.val := fun e => h (Fin.ext e)
    simp [h, h', gv_enc]

theorem support_update_card_le {n : ℕ} (P : PauliSDP.Word n) (p : Fin n) (a : Fin 4) :
    (PauliSDP.support (Function.update P p a)).card ≤ (PauliSDP.support P).card + 1 := by
  classical
  have hsub : PauliSDP.support (Function.update P p a) ⊆ insert p (PauliSDP.support P) := by
    intro q hq
    simp only [PauliSDP.support, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert] at hq ⊢
    by_cases h : q = p
    · exact Or.inl h
    · rw [Function.update_of_ne h] at hq
      exact Or.inr hq
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-! ### The rows -/

theorem rowsRaw_sound (n : ℕ) : ∀ k, ∀ w ∈ rowsRaw k (List.range n),
    ∃ P : PauliSDP.Word n, (PauliSDP.support P).card ≤ k ∧ w = enc P
  | 0 => by
      intro w hw
      simp only [rowsRaw, List.mem_singleton] at hw
      exact ⟨PauliSDP.identityWord n, by simp [PauliSDP.support, PauliSDP.identityWord],
        hw.trans (zeroW_eq n)⟩
  | k + 1 => by
      intro w hw
      simp only [rowsRaw, extW, List.mem_append, List.mem_flatMap, List.mem_map,
        List.mem_range] at hw
      rcases hw with hw | ⟨v, hv, p, hp, a, ha, rfl⟩
      · obtain ⟨P, hP, rfl⟩ := rowsRaw_sound n k w hw
        exact ⟨P, by omega, rfl⟩
      · obtain ⟨P, hP, rfl⟩ := rowsRaw_sound n k v hv
        have hb : ∃ b : Fin 4, a = (((b.val : ℕ) : ℚ)) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl
          · exact ⟨1, by simp⟩
          · exact ⟨2, by simp⟩
          · exact ⟨3, by simp⟩
        obtain ⟨b, rfl⟩ := hb
        exact ⟨Function.update P ⟨p, hp⟩ b,
          (support_update_card_le P ⟨p, hp⟩ b).trans (by omega), setW_enc P ⟨p, hp⟩ b⟩

theorem rowsRaw_complete (n : ℕ) : ∀ k (P : PauliSDP.Word n),
    (PauliSDP.support P).card ≤ k → enc P ∈ rowsRaw k (List.range n)
  | 0, P, h => by
      have hP : P = PauliSDP.identityWord n := by
        funext p
        by_contra hne
        have hm : p ∈ PauliSDP.support P := by
          simp only [PauliSDP.support, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hne
        have := Finset.card_pos.mpr ⟨p, hm⟩
        omega
      rw [hP, ← zeroW_eq]
      simp [rowsRaw]
  | k + 1, P, h => by
      by_cases hk : (PauliSDP.support P).card ≤ k
      · have := rowsRaw_complete n k P hk
        simp only [rowsRaw, extW, List.mem_append]
        exact Or.inl this
      · have hpos : 0 < (PauliSDP.support P).card := by omega
        obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
        have hsupp : PauliSDP.support (Function.update P p 0) = (PauliSDP.support P).erase p := by
          ext q
          simp only [PauliSDP.support, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_erase]
          by_cases hq : q = p
          · subst hq
            simp
          · rw [Function.update_of_ne hq]
            simp [hq]
        have hQ : (PauliSDP.support (Function.update P p 0)).card ≤ k := by
          rw [hsupp, Finset.card_erase_of_mem hp]
          omega
        have ih := rowsRaw_complete n k _ hQ
        simp only [rowsRaw, extW, List.mem_append, List.mem_flatMap, List.mem_map,
          List.mem_range]
        right
        refine ⟨_, ih, p.val, p.isLt, (((P p).val : ℕ) : ℚ), ?_, ?_⟩
        · have hne : P p ≠ 0 := by
            simpa [PauliSDP.support] using hp
          revert hne
          generalize P p = a
          fin_cases a <;> simp
        · rw [setW_enc]
          congr 1
          simp

theorem wordEq_enc {n : ℕ} (P Q : PauliSDP.Word n) :
    wordEq (List.range n) (enc P) (enc Q) = true ↔ P = Q := by
  unfold wordEq
  rw [List.isEmpty_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    funext p
    have h1 := h p.val (List.mem_range.mpr p.isLt)
    simp only [gv_enc, Bool.not_eq_true', decide_eq_false_iff_not, not_not] at h1
    exact Fin.ext (by exact_mod_cast h1)
  · rintro rfl q _
    simp

theorem getD_mem (R : List Vec) (i : ℕ) (h : i < R.length) : R[i]?.getD [] ∈ R := by
  rw [List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem dedup_keep (idxn : List ℕ) (R : List Vec)
    (heq : ∀ w ∈ R, ∀ v ∈ R, (wordEq idxn w v = true ↔ w = v)) (i : ℕ) (hi : i < R.length) :
    ((List.range R.length).filter (fun i' =>
      decide (i' < i) && wordEq idxn (R[i']?.getD []) (R[i]?.getD []))).isEmpty = true ↔
      ∀ i', i' < i → R[i']?.getD [] ≠ R[i]?.getD [] := by
  rw [List.isEmpty_iff, List.filter_eq_nil_iff]
  constructor
  · intro h i' hi' he
    apply h i' (List.mem_range.mpr (by omega))
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hi', (heq _ (getD_mem R i' (by omega)) _ (getD_mem R i hi)).mpr he⟩
  · intro h i' hi'r hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact h i' hc.1
      ((heq _ (getD_mem R i' (List.mem_range.mp hi'r)) _ (getD_mem R i hi)).mp hc.2)

theorem dedupW_spec (idxn : List ℕ) (R : List Vec)
    (heq : ∀ w ∈ R, ∀ v ∈ R, (wordEq idxn w v = true ↔ w = v)) :
    (∀ w, w ∈ dedupW idxn R ↔ w ∈ R) ∧ (dedupW idxn R).Nodup := by
  constructor
  · intro w
    unfold dedupW
    simp only [List.mem_map, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨i, ⟨hi, _⟩, rfl⟩
      exact getD_mem R i hi
    · intro hw
      classical
      have hex : ∃ i, i < R.length ∧ R[i]?.getD [] = w := by
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
        exact ⟨i, hi, by rw [List.getElem?_eq_getElem hi]; rfl⟩
      refine ⟨Nat.find hex, ⟨(Nat.find_spec hex).1, ?_⟩, (Nat.find_spec hex).2⟩
      rw [dedup_keep idxn R heq _ (Nat.find_spec hex).1]
      intro i' hi' he
      exact Nat.find_min hex hi'
        ⟨by have := (Nat.find_spec hex).1; omega, he.trans (Nat.find_spec hex).2⟩
  · unfold dedupW
    apply List.Nodup.map_on _ (List.nodup_range.filter _)
    intro x hx y hy hxy
    simp only [List.mem_filter, List.mem_range] at hx hy
    rw [dedup_keep idxn R heq _ hx.1] at hx
    rw [dedup_keep idxn R heq _ hy.1] at hy
    rcases lt_trichotomy x y with h | h | h
    · exact absurd hxy (hy.2 x h)
    · exact h
    · exact absurd hxy.symm (hx.2 y h)

theorem rowsW_spec (k n : ℕ) :
    (∀ w, w ∈ rowsW k (List.range n) ↔
      ∃ P : PauliSDP.Word n, (PauliSDP.support P).card ≤ k ∧ w = enc P) ∧
    (rowsW k (List.range n)).Nodup := by
  have heq : ∀ w ∈ rowsRaw k (List.range n), ∀ v ∈ rowsRaw k (List.range n),
      (wordEq (List.range n) w v = true ↔ w = v) := by
    intro w hw v hv
    obtain ⟨P, _, rfl⟩ := rowsRaw_sound n k w hw
    obtain ⟨Q, _, rfl⟩ := rowsRaw_sound n k v hv
    rw [wordEq_enc]
    exact ⟨fun h => h ▸ rfl, fun h => enc_injective h⟩
  obtain ⟨h1, h2⟩ := dedupW_spec _ _ heq
  refine ⟨fun w => ?_, h2⟩
  rw [rowsW, h1]
  exact ⟨rowsRaw_sound n k w, fun ⟨P, hP, e⟩ => e ▸ rowsRaw_complete n k P hP⟩

/-- Every row is the encoding of its decoding, which has support at most `k`. -/
theorem rowAt_canon (k : ℕ) (G : Input) (i : ℕ) (hi : i < (RW k G).length) :
    rowAt (RW k G) i = enc (decW G.n (rowAt (RW k G) i)) ∧
      (PauliSDP.support (decW G.n (rowAt (RW k G) i))).card ≤ k := by
  have hm : rowAt (RW k G) i ∈ RW k G := getD_mem _ i hi
  obtain ⟨P, hP, e⟩ := ((rowsW_spec k G.n).1 _).mp hm
  rw [e, decW_enc]
  exact ⟨rfl, hP⟩

theorem row_inj (k : ℕ) (G : Input) (i j : Fin (RW k G).length)
    (h : decW G.n (rowAt (RW k G) i) = decW G.n (rowAt (RW k G) j)) : i = j := by
  have e : rowAt (RW k G) i = rowAt (RW k G) j := by
    rw [(rowAt_canon k G i i.isLt).1, (rowAt_canon k G j j.isLt).1, h]
  unfold rowAt at e
  rw [List.getElem?_eq_getElem i.isLt, List.getElem?_eq_getElem j.isLt] at e
  simp only [Option.getD_some] at e
  exact Fin.ext (((rowsW_spec k G.n).2.getElem_inj_iff).mp e)

theorem row_surj (k : ℕ) (G : Input) (P : PauliSDP.Word G.n)
    (hP : (PauliSDP.support P).card ≤ k) :
    ∃ i : Fin (RW k G).length, decW G.n (rowAt (RW k G) i) = P := by
  have hm : enc P ∈ RW k G := ((rowsW_spec k G.n).1 _).mpr ⟨P, hP, rfl⟩
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hm
  refine ⟨⟨i, hi⟩, ?_⟩
  have : rowAt (RW k G) i = enc P := by
    unfold rowAt
    rw [List.getElem?_eq_getElem hi]
    exact e
  rw [this, decW_enc]

/-! ### Label arithmetic -/

/-- Exponent of `i` in the phase of a product of two labels. -/
def lE : Fin 4 → Fin 4 → ℕ := ![![0, 0, 0, 0], ![0, 0, 1, 3], ![0, 3, 0, 1], ![0, 1, 3, 0]]

theorem lp_val (a b : Fin 4) :
    lp (((a.val : ℕ) : ℚ)) (((b.val : ℕ) : ℚ)) = (((PauliSDP.localProduct a b).val : ℕ) : ℚ) := by
  fin_cases a <;> fin_cases b <;> simp [lp, PauliSDP.localProduct] <;> norm_num

theorem le_val (a b : Fin 4) :
    le (((a.val : ℕ) : ℚ)) (((b.val : ℕ) : ℚ)) = ((lE a b : ℕ) : ℚ) := by
  fin_cases a <;> fin_cases b <;> simp [le, lE] <;> norm_num

theorem localPhase_eq (a b : Fin 4) : PauliSDP.localPhase a b = Complex.I ^ (lE a b) := by
  fin_cases a <;> fin_cases b <;> simp [PauliSDP.localPhase, lE, pow_succ]

theorem localProduct_eq_zero (a b : Fin 4) : PauliSDP.localProduct a b = 0 ↔ a = b := by
  revert a b
  decide

theorem localProduct_comm (a b : Fin 4) :
    PauliSDP.localProduct a b = PauliSDP.localProduct b a := by
  revert a b
  decide

theorem localProduct_zero_right (a : Fin 4) : PauliSDP.localProduct a 0 = a := by
  revert a
  decide

theorem localProduct_zero_left (a : Fin 4) : PauliSDP.localProduct 0 a = a := by
  revert a
  decide

theorem localPhase_self (a : Fin 4) : PauliSDP.localPhase a a = 1 := by
  fin_cases a <;> simp [PauliSDP.localPhase]

theorem localPhase_zero_right (a : Fin 4) : PauliSDP.localPhase a 0 = 1 := by
  fin_cases a <;> simp [PauliSDP.localPhase]

theorem localPhase_zero_left (a : Fin 4) : PauliSDP.localPhase 0 a = 1 := by
  fin_cases a <;> simp [PauliSDP.localPhase]

theorem localPhase_swap (a b : Fin 4) :
    PauliSDP.localPhase b a = star (PauliSDP.localPhase a b) := by
  fin_cases a <;> fin_cases b <;> simp [PauliSDP.localPhase]

/-- Real part of `i ^ t`, as an integer. -/
def reI (t : ℕ) : ℤ := if t % 4 = 0 then 1 else if t % 4 = 2 then -1 else 0

theorem I_pow_re (t : ℕ) : (Complex.I ^ t).re = ((reI t : ℤ) : ℝ) := by
  have h : Complex.I ^ t = Complex.I ^ (t % 4) := by
    conv_lhs => rw [← Nat.div_add_mod t 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
  rw [h]
  unfold reI
  have h4 : t % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize t % 4 = r at h4 ⊢
  interval_cases r <;> simp [pow_succ]

theorem reI_abs (t : ℕ) : |reI t| ≤ 1 := by
  unfold reI
  split_ifs <;> simp

theorem sgnOf_nat (t : ℕ) : sgnOf (t : ℚ) = ((reI t : ℤ) : ℚ) := by
  have hq : qfloor ((t : ℚ) / 4) = (((t / 4 : ℕ) : ℕ) : ℚ) := by
    rw [qfloor_eq_floor _ (by positivity)]
    have h1 : ⌊((t : ℚ)) / 4⌋ = (t : ℤ) / 4 := by
      simpa using Rat.floor_intCast_div_natCast (t : ℤ) 4
    rw [h1]
    norm_cast
  have hmod : (t : ℚ) - 4 * (((t / 4 : ℕ) : ℕ) : ℚ) = (((t % 4 : ℕ) : ℕ) : ℚ) := by
    have h2 : (t : ℚ) = 4 * (((t / 4 : ℕ) : ℕ) : ℚ) + (((t % 4 : ℕ) : ℕ) : ℚ) := by
      exact_mod_cast (Nat.div_add_mod t 4).symm
    linarith
  unfold sgnOf reI
  rw [hq, hmod]
  have h4 : t % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize t % 4 = r at h4 ⊢
  interval_cases r <;> norm_num

/-! ### Words -/

/-- The integer sign of a pair of words. -/
def sg {n : ℕ} (P Q : PauliSDP.Word n) : ℤ := reI (∑ p, lE (P p) (Q p))

theorem wordPhase_eq {n : ℕ} (P Q : PauliSDP.Word n) :
    PauliSDP.wordPhase P Q = Complex.I ^ (∑ p, lE (P p) (Q p)) := by
  unfold PauliSDP.wordPhase
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun p _ => localPhase_eq _ _

theorem wordPhase_re {n : ℕ} (P Q : PauliSDP.Word n) :
    (PauliSDP.wordPhase P Q).re = ((sg P Q : ℤ) : ℝ) := by
  rw [wordPhase_eq, I_pow_re]
  rfl

theorem floor_wordPhase_re {n : ℕ} (P Q : PauliSDP.Word n) :
    ⌊(PauliSDP.wordPhase P Q).re⌋ = sg P Q := by
  rw [wordPhase_re, Int.floor_intCast]

theorem wordPhase_self {n : ℕ} (P : PauliSDP.Word n) : PauliSDP.wordPhase P P = 1 :=
  Finset.prod_eq_one fun _ _ => localPhase_self _

theorem wordPhase_swap {n : ℕ} (P Q : PauliSDP.Word n) :
    PauliSDP.wordPhase Q P = star (PauliSDP.wordPhase P Q) := by
  unfold PauliSDP.wordPhase
  rw [star_prod]
  exact Finset.prod_congr rfl fun p _ => localPhase_swap _ _

theorem wordProduct_comm {n : ℕ} (P Q : PauliSDP.Word n) :
    PauliSDP.wordProduct P Q = PauliSDP.wordProduct Q P := by
  funext p
  exact localProduct_comm _ _

theorem wordProduct_eq_id {n : ℕ} (P Q : PauliSDP.Word n) :
    PauliSDP.wordProduct P Q = PauliSDP.identityWord n ↔ P = Q := by
  constructor
  · intro h
    funext p
    exact (localProduct_eq_zero _ _).mp (congrFun h p)
  · rintro rfl
    funext p
    exact (localProduct_eq_zero _ _).mpr rfl

theorem prodW_enc {n : ℕ} (P Q : PauliSDP.Word n) :
    prodW (List.range n) (enc P) (enc Q) = enc (PauliSDP.wordProduct P Q) :=
  map_range_congr n _ _ (fun p => by rw [gv_enc, gv_enc, lp_val]; rfl)

theorem expoW_enc {n : ℕ} (P Q : PauliSDP.Word n) :
    expoW (List.range n) (enc P) (enc Q) = (((∑ p, lE (P p) (Q p) : ℕ) : ℕ) : ℚ) := by
  unfold expoW
  rw [sum_range_congr n _ (fun p : Fin n => ((lE (P p) (Q p) : ℕ) : ℚ))
    (fun p => by rw [gv_enc, gv_enc, le_val])]
  push_cast
  rfl

theorem gm_tab (N : ℕ) (F : ℕ → ℕ → ℚ) (i j : ℕ) (hi : i < N) (hj : j < N) :
    gm ((List.range N).map (fun i => (List.range N).map (fun j => F i j))) i j = F i j := by
  simp [gm, hi, hj]

/-- The program's sign table is the instance's sign function. -/
theorem sgnTab_eq (k : ℕ) (G : Input) (i j : Fin (RW k G).length) :
    gm (sgnTabW (List.range G.n) (RW k G)) i j = ((pauliInst k G).sgn i j : ℚ) := by
  unfold sgnTabW
  rw [gm_tab _ _ _ _ i.isLt j.isLt, (rowAt_canon k G i i.isLt).1, (rowAt_canon k G j j.isLt).1,
    expoW_enc, sgnOf_nat]
  show _ = ((⌊(PauliSDP.wordPhase (decW G.n (rowAt (RW k G) i))
    (decW G.n (rowAt (RW k G) j))).re⌋ : ℤ) : ℚ)
  rw [floor_wordPhase_re]
  rfl

/-! ### Class identifiers -/

theorem findIdx_congr_mem {α : Type*} (px py : α → Bool) :
    ∀ l : List α, (∀ p ∈ l, px p = py p) → l.findIdx px = l.findIdx py
  | [], _ => rfl
  | a :: l, h => by
      rw [List.findIdx_cons, List.findIdx_cons, h a List.mem_cons_self,
        findIdx_congr_mem px py l (fun p hp => h p (List.mem_cons_of_mem _ hp))]

theorem findIdx_eq_iff {α β : Type*} (l : List α) (f : α → β) (px py : α → Bool) (x y : α)
    (hx : x ∈ l) (_hy : y ∈ l) (hpx : ∀ p ∈ l, (px p = true ↔ f p = f x))
    (hpy : ∀ p ∈ l, (py p = true ↔ f p = f y)) :
    l.findIdx px = l.findIdx py ↔ f x = f y := by
  constructor
  · intro h
    have hlt : l.findIdx px < l.length :=
      List.findIdx_lt_length_of_exists ⟨x, hx, (hpx x hx).mpr rfl⟩
    have h1 : px l[l.findIdx px] = true := List.findIdx_getElem
    have hlt' : l.findIdx py < l.length := h ▸ hlt
    have h2 : py l[l.findIdx py] = true := List.findIdx_getElem
    have e1 := (hpx _ (List.getElem_mem hlt)).mp h1
    have e2 := (hpy _ (List.getElem_mem hlt')).mp h2
    have e3 : l[l.findIdx px] = l[l.findIdx py] := by simp only [h]
    rw [← e1, ← e2, e3]
  · intro h
    apply findIdx_congr_mem
    intro p hp
    rw [Bool.eq_iff_iff, hpx p hp, hpy p hp, h]

theorem mem_pairsW (R : List Vec) (p : ℕ × ℕ) :
    p ∈ pairsW R ↔ p.1 < R.length ∧ p.2 < R.length := by
  unfold pairsW
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨ha, hb⟩
  · rintro ⟨h1, h2⟩
    exact ⟨p.1, h1, p.2, h2, rfl⟩

/-- The program's class identifiers agree exactly when the product words agree. -/
theorem clsTab_iff (k : ℕ) (G : Input) (i j i' j' : Fin (RW k G).length) :
    gm (clsTabW (List.range G.n) (RW k G)) i j = gm (clsTabW (List.range G.n) (RW k G)) i' j' ↔
      (pauliInst k G).cls i j = (pauliInst k G).cls i' j' := by
  have hp : ∀ a b : Fin (RW k G).length, ∀ p ∈ pairsW (RW k G),
      (wordEq (List.range G.n) (prodW (List.range G.n) (rowAt (RW k G) p.1) (rowAt (RW k G) p.2))
        (prodW (List.range G.n) (rowAt (RW k G) a) (rowAt (RW k G) b)) = true ↔
      (fun p : ℕ × ℕ => PauliSDP.wordProduct (decW G.n (rowAt (RW k G) p.1))
        (decW G.n (rowAt (RW k G) p.2))) p =
      (fun p : ℕ × ℕ => PauliSDP.wordProduct (decW G.n (rowAt (RW k G) p.1))
        (decW G.n (rowAt (RW k G) p.2))) (a.val, b.val)) := by
    intro a b p hp
    obtain ⟨h1, h2⟩ := (mem_pairsW _ p).mp hp
    rw [(rowAt_canon k G p.1 h1).1, (rowAt_canon k G p.2 h2).1, (rowAt_canon k G a a.isLt).1,
      (rowAt_canon k G b b.isLt).1, prodW_enc, prodW_enc, wordEq_enc]
  have hgm : ∀ a b : Fin (RW k G).length,
      gm (clsTabW (List.range G.n) (RW k G)) a b =
        (((pairsW (RW k G)).findIdx (fun p =>
          wordEq (List.range G.n)
            (prodW (List.range G.n) (rowAt (RW k G) p.1) (rowAt (RW k G) p.2))
            (prodW (List.range G.n) (rowAt (RW k G) a) (rowAt (RW k G) b))) : ℕ) : ℚ) := by
    intro a b
    unfold clsTabW
    exact gm_tab _ _ _ _ a.isLt b.isLt
  rw [hgm, hgm, Nat.cast_inj]
  exact findIdx_eq_iff (pairsW (RW k G)) _ _ _ (i.val, j.val) (i'.val, j'.val)
    ((mem_pairsW _ _).mpr ⟨i.isLt, j.isLt⟩) ((mem_pairsW _ _).mpr ⟨i'.isLt, j'.isLt⟩)
    (hp i j) (hp i' j')

/-! ### Feasibility -/

/-- The index of a row in the relaxation's Gram matrix. -/
noncomputable def idxOf (k : ℕ) (G : Input) (i : Fin (RW k G).length) : PauliSDP.Index G.n k :=
  ⟨decW G.n (rowAt (RW k G) i), (rowAt_canon k G i i.isLt).2⟩

theorem Gam_eq (k : ℕ) (G : Input) (L : PauliSDP.Word G.n → ℝ) :
    Gam (pauliInst k G) L = (PauliSDP.realGram k L).submatrix (idxOf k G) (idxOf k G) := by
  ext i j
  show ((⌊(PauliSDP.wordPhase (decW G.n (rowAt (RW k G) i))
    (decW G.n (rowAt (RW k G) j))).re⌋ : ℤ) : ℝ) * L _ = _
  rw [floor_wordPhase_re, ← wordPhase_re]
  rfl

theorem feas_of_pauli (k : ℕ) (G : Input) (L : PauliSDP.Word G.n → ℝ)
    (h : PauliSDP.Feasible k L) : Feas (pauliInst k G) L := by
  refine ⟨h.1, ?_⟩
  rw [Gam_eq]
  exact h.2.submatrix _

theorem pauli_of_feas (k : ℕ) (G : Input) (L : PauliSDP.Word G.n → ℝ)
    (h : Feas (pauliInst k G) L) : PauliSDP.Feasible k L := by
  refine ⟨h.1, ?_⟩
  have hs : ∀ P : PauliSDP.Index G.n k, ∃ i, idxOf k G i = P := by
    intro P
    obtain ⟨i, hi⟩ := row_surj k G P.1 P.2
    exact ⟨i, Subtype.ext hi⟩
  choose e he using hs
  have hG : PauliSDP.realGram k L = (Gam (pauliInst k G) L).submatrix e e := by
    rw [Gam_eq]
    ext P Q
    simp only [Matrix.submatrix_apply, he]
  rw [hG]
  exact h.2.submatrix _

/-! ### Single-site words -/

/-- The word with label `a` at site `p` and identity elsewhere. -/
def single {n : ℕ} (a : Fin 4) (p : Fin n) : PauliSDP.Word n := fun i => if i = p then a else 0

theorem single_inj {n : ℕ} (a b : Fin 4) (p q : Fin n) (ha : a ≠ 0)
    (h : single a p = single b q) : a = b ∧ p = q := by
  have h1 : a = if p = q then b else 0 := by simpa [single] using congrFun h p
  by_cases hpq : p = q
  · rw [if_pos hpq] at h1
    exact ⟨h1, hpq⟩
  · rw [if_neg hpq] at h1
    exact absurd h1 ha

theorem support_single_card {n : ℕ} (a : Fin 4) (p : Fin n) :
    (PauliSDP.support (single a p)).card ≤ 1 := by
  have hsub : PauliSDP.support (single a p) ⊆ {p} := by
    intro q hq
    rw [Finset.mem_singleton]
    by_contra hne
    have hq' : single a p q ≠ 0 := (Finset.mem_filter.mp hq).2
    exact hq' (if_neg hne)
  exact (Finset.card_le_card hsub).trans (by simp)

theorem wordProduct_single {n : ℕ} (a : Fin 4) (e : Edge n) :
    PauliSDP.wordProduct (single a e.val.1) (single a e.val.2) = PauliSDP.twoBody a e := by
  funext i
  have hlt := e.2
  show PauliSDP.localProduct (if i = e.val.1 then a else 0) (if i = e.val.2 then a else 0) =
    if i = e.val.1 ∨ i = e.val.2 then a else 0
  by_cases h1 : i = e.val.1
  · have h2 : ¬ i = e.val.2 := by
      rw [h1]
      exact ne_of_lt hlt
    rw [if_pos h1, if_neg h2, if_pos (Or.inl h1), localProduct_zero_right]
  · by_cases h2 : i = e.val.2
    · rw [if_neg h1, if_pos h2, if_pos (Or.inr h2), localProduct_zero_left]
    · rw [if_neg h1, if_neg h2, if_neg (by tauto), localProduct_zero_left]

theorem wordPhase_single {n : ℕ} (a b : Fin 4) (p q : Fin n) (h : p ≠ q) :
    PauliSDP.wordPhase (single a p) (single b q) = 1 :=
  Finset.prod_eq_one fun i _ => by
    show PauliSDP.localPhase (if i = p then a else 0) (if i = q then b else 0) = 1
    by_cases h1 : i = p
    · rw [if_neg (fun e : i = q => h (h1.symm.trans e)), localPhase_zero_right]
    · rw [if_neg h1, localPhase_zero_left]

theorem mem_suppW {n : ℕ} (P : PauliSDP.Word n) (x : ℕ) :
    x ∈ suppW (List.range n) (enc P) ↔ ∃ h : x < n, P ⟨x, h⟩ ≠ 0 := by
  unfold suppW
  simp only [List.mem_filter, List.mem_range, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro ⟨h, hne⟩
    refine ⟨h, fun h0 => hne ?_⟩
    have e := gv_enc P ⟨x, h⟩
    rw [h0] at e
    simpa using e
  · rintro ⟨h, hne⟩
    refine ⟨h, fun h0 => hne ?_⟩
    have e := gv_enc P ⟨x, h⟩
    rw [e] at h0
    exact Fin.ext (Nat.cast_eq_zero.mp h0)

theorem suppW_single {n : ℕ} (a : Fin 4) (p : Fin n) (ha : a ≠ 0) :
    suppW (List.range n) (enc (single a p)) = [p.val] := by
  have hnd : (suppW (List.range n) (enc (single a p))).Nodup := List.nodup_range.filter _
  apply List.perm_singleton.mp
  refine (List.perm_ext_iff_of_nodup hnd (List.nodup_singleton _)).mpr ?_
  intro x
  rw [mem_suppW, List.mem_singleton]
  constructor
  · rintro ⟨h, hne⟩
    by_contra hx
    apply hne
    show (if (⟨x, h⟩ : Fin n) = p then a else 0) = 0
    rw [if_neg (fun e => hx (congrArg Fin.val e))]
  · rintro rfl
    refine ⟨p.isLt, ?_⟩
    show (if (⟨p.val, p.isLt⟩ : Fin n) = p then a else 0) ≠ 0
    rw [if_pos rfl]
    exact ha

theorem suppW_len_one {n : ℕ} (P : PauliSDP.Word n)
    (h : (suppW (List.range n) (enc P)).length = 1) :
    ∃ a : Fin 4, ∃ p : Fin n, a ≠ 0 ∧ P = single a p := by
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp h
  have hm : x ∈ suppW (List.range n) (enc P) := by
    rw [hx]
    exact List.mem_singleton.mpr rfl
  obtain ⟨hxn, hne⟩ := (mem_suppW P x).mp hm
  refine ⟨P ⟨x, hxn⟩, ⟨x, hxn⟩, hne, ?_⟩
  funext q
  show P q = if q = ⟨x, hxn⟩ then P ⟨x, hxn⟩ else 0
  by_cases hq : q = ⟨x, hxn⟩
  · rw [if_pos hq, hq]
  · rw [if_neg hq]
    by_contra hq0
    have hqm : q.val ∈ suppW (List.range n) (enc P) := (mem_suppW P q.val).mpr ⟨q.isLt, hq0⟩
    rw [hx, List.mem_singleton] at hqm
    exact hq (Fin.ext hqm)

/-! ### Objective coefficients -/

/-- One entry of the program's coefficient table, as a function of the two row words. -/
def csE (idxn : List ℕ) (xs : List NumericEdge) (w v : Vec) : ℚ :=
  if (suppW idxn w).length = 1 then
    (if (suppW idxn v).length = 1 then
      (if gv w ((suppW idxn w).head?.getD 0) = gv v ((suppW idxn v).head?.getD 0) then
        (if (suppW idxn w).head?.getD 0 < (suppW idxn v).head?.getD 0
          then -(edgeW xs ((suppW idxn w).head?.getD 0) ((suppW idxn v).head?.getD 0)) /
            (2 * edgeWeightSum xs)
          else 0)
        else 0)
      else 0)
    else 0

theorem gv_single_self {n : ℕ} (a : Fin 4) (p : Fin n) :
    gv (enc (single a p)) p.val = (((a.val : ℕ) : ℚ)) := by
  rw [gv_enc]
  simp [single]

theorem csE_single (G : Input) (a : Fin 4) (ha : a ≠ 0) (p q : Fin G.n) (hpq : p < q) :
    csE (List.range G.n) (inputEdges G) (enc (single a p)) (enc (single a q)) =
      -((G.weights ⟨(p, q), hpq⟩ : ℚ)) / (2 * Wq G) := by
  unfold csE
  rw [suppW_single a p ha, suppW_single a q ha]
  simp only [List.length_singleton, List.head?_cons, Option.getD_some, gv_single_self, if_true,
    Fin.lt_def.mp hpq, edgeW_inputEdges, edgeWeightSum_inputEdges]
  unfold Aq
  rw [dif_pos hpq]

theorem csE_nonzero {n : ℕ} (xs : List NumericEdge) (P Q : PauliSDP.Word n)
    (h : csE (List.range n) xs (enc P) (enc Q) ≠ 0) :
    ∃ a : Fin 4, a ≠ 0 ∧ ∃ p q : Fin n, p < q ∧ P = single a p ∧ Q = single a q := by
  unfold csE at h
  by_cases h1 : (suppW (List.range n) (enc P)).length = 1
  swap
  · rw [if_neg h1] at h
    exact absurd rfl h
  by_cases h2 : (suppW (List.range n) (enc Q)).length = 1
  swap
  · rw [if_pos h1, if_neg h2] at h
    exact absurd rfl h
  rw [if_pos h1, if_pos h2] at h
  obtain ⟨a, p, ha, rfl⟩ := suppW_len_one P h1
  obtain ⟨b, q, hb, rfl⟩ := suppW_len_one Q h2
  rw [suppW_single a p ha, suppW_single b q hb] at h
  simp only [List.head?_cons, Option.getD_some, gv_single_self] at h
  by_cases hab : (((a.val : ℕ) : ℚ)) = (((b.val : ℕ) : ℚ))
  swap
  · exact absurd (if_neg hab) h
  by_cases hpq : p.val < q.val
  swap
  · exact absurd ((if_pos hab).trans (if_neg hpq)) h
  have hab' : a = b := Fin.ext (Nat.cast_injective hab)
  subst hab'
  exact ⟨a, ha, p, q, Fin.lt_def.mpr hpq, rfl, rfl⟩

theorem Cs_eq (k : ℕ) (G : Input) (i j : Fin (RW k G).length) :
    (pauliInst k G).Cs i j = csE (List.range G.n) (inputEdges G)
      (enc (decW G.n (rowAt (RW k G) i))) (enc (decW G.n (rowAt (RW k G) j))) := by
  show gm (csTabW (List.range G.n) (RW k G) (inputEdges G)) i j = _
  rw [← (rowAt_canon k G i i.isLt).1, ← (rowAt_canon k G j j.isLt).1]
  unfold csTabW
  exact gm_tab _ (fun i j => csE (List.range G.n) (inputEdges G) (rowAt (RW k G) i)
    (rowAt (RW k G) j)) _ _ i.isLt j.isLt

theorem Cs_nonzero (k : ℕ) (G : Input) (i j : Fin (RW k G).length)
    (h : (pauliInst k G).Cs i j ≠ 0) :
    ∃ a : Fin 4, a ≠ 0 ∧ ∃ p q : Fin G.n, p < q ∧
      decW G.n (rowAt (RW k G) i) = single a p ∧ decW G.n (rowAt (RW k G) j) = single a q := by
  rw [Cs_eq] at h
  exact csE_nonzero _ _ _ h

theorem Cs_single (k : ℕ) (G : Input) (i j : Fin (RW k G).length) (a : Fin 4) (ha : a ≠ 0)
    (p q : Fin G.n) (hpq : p < q) (hi : decW G.n (rowAt (RW k G) i) = single a p)
    (hj : decW G.n (rowAt (RW k G) j) = single a q) :
    (pauliInst k G).Cs i j = -((G.weights ⟨(p, q), hpq⟩ : ℚ)) / (2 * Wq G) := by
  rw [Cs_eq, hi, hj]
  exact csE_single G a ha p q hpq

/-! ### Row indices of words -/

/-- The row index of a word of support at most `k`. -/
noncomputable def rIdx (k : ℕ) (G : Input) (P : PauliSDP.Word G.n)
    (hP : (PauliSDP.support P).card ≤ k) : Fin (RW k G).length :=
  Classical.choose (row_surj k G P hP)

theorem rIdx_spec (k : ℕ) (G : Input) (P : PauliSDP.Word G.n)
    (hP : (PauliSDP.support P).card ≤ k) :
    decW G.n (rowAt (RW k G) (rIdx k G P hP)) = P :=
  Classical.choose_spec (row_surj k G P hP)

/-- The row index of a single-site word. -/
noncomputable def sIdx (k : ℕ) (G : Input) (hk : 1 ≤ k) (a : Fin 4) (p : Fin G.n) :
    Fin (RW k G).length :=
  rIdx k G (single a p) ((support_single_card a p).trans hk)

theorem sIdx_spec (k : ℕ) (G : Input) (hk : 1 ≤ k) (a : Fin 4) (p : Fin G.n) :
    decW G.n (rowAt (RW k G) (sIdx k G hk a p)) = single a p :=
  rIdx_spec k G _ _

/-- A double sum over rows that vanishes off the support of the coefficient table is a sum over
labels and edges. -/
theorem cs_sum_reindex {M : Type*} [AddCommMonoid M] (k : ℕ) (G : Input) (hk : 1 ≤ k)
    (g : Fin (RW k G).length → Fin (RW k G).length → M)
    (hg : ∀ i j, (pauliInst k G).Cs i j = 0 → g i j = 0) :
    ∑ i, ∑ j, g i j = ∑ t : Fin 3 × Edge G.n,
      g (sIdx k G hk t.1.succ t.2.val.1) (sIdx k G hk t.1.succ t.2.val.2) := by
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_of_injective
    (fun t : Fin 3 × Edge G.n =>
      (sIdx k G hk t.1.succ t.2.val.1, sIdx k G hk t.1.succ t.2.val.2))
    ?_ _ (fun x : Fin (RW k G).length × Fin (RW k G).length => g x.1 x.2) ?_ (fun t => rfl)
  · intro t t' h
    have h1 := congrArg (fun x => decW G.n (rowAt (RW k G) x.1)) h
    have h2 := congrArg (fun x => decW G.n (rowAt (RW k G) x.2)) h
    simp only [sIdx_spec] at h1 h2
    obtain ⟨ha, hp⟩ := single_inj _ _ _ _ (Fin.succ_ne_zero _) h1
    obtain ⟨-, hq⟩ := single_inj _ _ _ _ (Fin.succ_ne_zero _) h2
    exact Prod.ext (Fin.succ_injective _ ha) (Subtype.ext (Prod.ext hp hq))
  · intro x hx
    apply hg
    by_contra hne
    obtain ⟨a, ha, p, q, hpq, hi, hj⟩ := Cs_nonzero k G x.1 x.2 hne
    apply hx
    refine ⟨(a.pred ha, ⟨(p, q), hpq⟩), ?_⟩
    show (sIdx k G hk (a.pred ha).succ p, sIdx k G hk (a.pred ha).succ q) = x
    exact Prod.ext (row_inj k G _ _ (by simp only [sIdx_spec, Fin.succ_pred, hi]))
      (row_inj k G _ _ (by simp only [sIdx_spec, Fin.succ_pred, hj]))

/-! ### The instance is good -/

theorem pauliInst_good (k : ℕ) (G : Input) (hk : 1 ≤ k) (hW : 0 < Wq G) :
    (pauliInst k G).Good := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact wordProduct_comm _ _
  · intro i j
    show ⌊(PauliSDP.wordPhase _ _).re⌋ = ⌊(PauliSDP.wordPhase _ _).re⌋
    rw [wordPhase_swap]
    simp
  · intro i j
    show |⌊(PauliSDP.wordPhase _ _).re⌋| ≤ 1
    rw [floor_wordPhase_re]
    exact reI_abs _
  · intro i j
    show PauliSDP.wordProduct _ _ = PauliSDP.identityWord G.n ↔ _
    rw [wordProduct_eq_id]
    exact ⟨row_inj k G i j, fun h => h ▸ rfl⟩
  · intro i
    show ⌊(PauliSDP.wordPhase _ _).re⌋ = 1
    rw [wordPhase_self]
    simp
  · intro i
    by_contra hne
    obtain ⟨a, ha, p, q, hpq, hi, hj⟩ := Cs_nonzero k G i i hne
    exact absurd (single_inj _ _ _ _ ha (hi.symm.trans hj)).2 (ne_of_lt hpq)
  · rw [cs_sum_reindex k G hk (fun i j => |(pauliInst k G).Cs i j|)
      (fun i j h => by rw [h, abs_zero])]
    have hne : Wq G ≠ 0 := hW.ne'
    have hterm : ∀ t : Fin 3 × Edge G.n,
        |(pauliInst k G).Cs (sIdx k G hk t.1.succ t.2.val.1) (sIdx k G hk t.1.succ t.2.val.2)| =
          (G.weights t.2 : ℚ) / (2 * Wq G) := by
      intro t
      have hc : (pauliInst k G).Cs (sIdx k G hk t.1.succ t.2.val.1)
          (sIdx k G hk t.1.succ t.2.val.2) = -((G.weights t.2 : ℚ)) / (2 * Wq G) :=
        Cs_single k G _ _ t.1.succ (Fin.succ_ne_zero _) t.2.val.1 t.2.val.2 t.2.2
          (sIdx_spec k G hk _ _) (sIdx_spec k G hk _ _)
      rw [hc, neg_div, abs_neg,
        abs_of_nonneg (div_nonneg (NNRat.coe_nonneg _) (by linarith))]
    have he : ∑ e : Edge G.n, (G.weights e : ℚ) / (2 * Wq G) = 1 / 2 := by
      rw [← Finset.sum_div]
      show Wq G / (2 * Wq G) = 1 / 2
      rw [div_eq_div_iff (mul_ne_zero two_ne_zero hne) two_ne_zero]
      ring
    rw [Finset.sum_congr rfl (fun t _ => hterm t), Fintype.sum_prod_type]
    simp only [he]
    norm_num [Finset.sum_const, Finset.card_univ]
  · intro i j h
    obtain ⟨a, ha, p, q, hpq, hi, hj⟩ := Cs_nonzero k G i j h
    show ⌊(PauliSDP.wordPhase _ _).re⌋ ≠ 0
    rw [hi, hj, wordPhase_single a a p q (ne_of_lt hpq)]
    simp
  · show (0 : ℚ) ≤ 1 / 2
    norm_num
  · show (1 / 2 : ℚ) ≤ 1 / 2
    exact le_rfl

theorem rows_length_ge (k : ℕ) (G : Input) (hk : 1 ≤ k) (hW : 0 < Wq G) :
    2 ≤ (RW k G).length := by
  obtain ⟨e, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show ∑ e : Edge G.n, (G.weights e : ℚ) ≠ 0 from hW.ne')
  have h0 : (PauliSDP.support (PauliSDP.identityWord G.n)).card ≤ k := by
    simp [PauliSDP.support, PauliSDP.identityWord]
  have hne : rIdx k G _ h0 ≠ sIdx k G hk 1 e.val.1 := by
    intro h
    have h1 := congrArg (fun x : Fin (RW k G).length => decW G.n (rowAt (RW k G) x)) h
    simp only [rIdx_spec, sIdx_spec] at h1
    have h2 := congrFun h1 e.val.1
    simp [PauliSDP.identityWord, single] at h2
  have h1 := (rIdx k G _ h0).isLt
  have h2 := (sIdx k G hk 1 e.val.1).isLt
  have h3 : (rIdx k G _ h0).val ≠ (sIdx k G hk 1 e.val.1).val := fun h => hne (Fin.ext h)
  omega

/-! ### The objective -/

theorem Wq_cast (G : Input) : ((Wq G : ℚ) : ℝ) = ∑ e : Edge G.n, (G.weights e : ℝ) := by
  unfold Wq
  rw [Rat.cast_sum]
  exact Finset.sum_congr rfl fun e _ => Rat.cast_nnratCast _

/-- The relaxation objective is the total weight times the normalized instance objective. -/
theorem objective_eq (k : ℕ) (G : Input) (hk : 1 ≤ k) (hW : 0 < Wq G)
    (L : PauliSDP.Word G.n → ℝ) :
    PauliSDP.objective G.weights L = ((Wq G : ℚ) : ℝ) * obj (pauliInst k G) L := by
  have hW0 : ((Wq G : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  unfold obj
  rw [cs_sum_reindex k G hk
    (fun i j => ((pauliInst k G).Cs i j : ℝ) * L ((pauliInst k G).cls i j))
    (fun i j h => by rw [h, Rat.cast_zero, zero_mul])]
  have hterm : ∀ t : Fin 3 × Edge G.n,
      ((pauliInst k G).Cs (sIdx k G hk t.1.succ t.2.val.1)
          (sIdx k G hk t.1.succ t.2.val.2) : ℝ) *
        L ((pauliInst k G).cls (sIdx k G hk t.1.succ t.2.val.1)
          (sIdx k G hk t.1.succ t.2.val.2)) =
      -((G.weights t.2 : ℝ)) / (2 * ((Wq G : ℚ) : ℝ)) * L (PauliSDP.twoBody t.1.succ t.2) := by
    intro t
    have hc : (pauliInst k G).Cs (sIdx k G hk t.1.succ t.2.val.1)
        (sIdx k G hk t.1.succ t.2.val.2) = -((G.weights t.2 : ℚ)) / (2 * Wq G) :=
      Cs_single k G _ _ t.1.succ (Fin.succ_ne_zero _) t.2.val.1 t.2.val.2 t.2.2
        (sIdx_spec k G hk _ _) (sIdx_spec k G hk _ _)
    have hcl : (pauliInst k G).cls (sIdx k G hk t.1.succ t.2.val.1)
        (sIdx k G hk t.1.succ t.2.val.2) = PauliSDP.twoBody t.1.succ t.2 := by
      have e1 := sIdx_spec k G hk t.1.succ t.2.val.1
      have e2 := sIdx_spec k G hk t.1.succ t.2.val.2
      show PauliSDP.wordProduct
        (decW G.n (rowAt (RW k G) (sIdx k G hk t.1.succ t.2.val.1)))
        (decW G.n (rowAt (RW k G) (sIdx k G hk t.1.succ t.2.val.2))) = _
      rw [e1, e2, wordProduct_single]
    rw [hc, hcl, Rat.cast_div, Rat.cast_neg, Rat.cast_mul, Rat.cast_nnratCast, Rat.cast_ofNat]
  have hc0 : (((pauliInst k G).c0 : ℚ) : ℝ) = 1 / 2 := by
    show (((1 / 2 : ℚ)) : ℝ) = 1 / 2
    norm_num
  have hhalf : ((Wq G : ℚ) : ℝ) * (1 / 2) = ∑ e : Edge G.n, (G.weights e : ℝ) / 2 := by
    rw [Wq_cast, Finset.sum_mul]
    exact Finset.sum_congr rfl fun e _ => by ring
  have s0 : (0 : Fin 3).succ = (1 : Fin 4) := rfl
  have s1 : (1 : Fin 3).succ = (2 : Fin 4) := rfl
  have s2 : (2 : Fin 3).succ = (3 : Fin 4) := rfl
  rw [Finset.sum_congr rfl (fun t _ => hterm t), Fintype.sum_prod_type, Finset.sum_comm, hc0,
    mul_add, hhalf, Finset.mul_sum, ← Finset.sum_add_distrib]
  unfold PauliSDP.objective
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Fin.sum_univ_three, s0, s1, s2]
  field_simp
  ring

theorem gram_abs_le {n : ℕ} (k : ℕ) (L : PauliSDP.Word n → ℝ) (h : PauliSDP.Feasible k L)
    (P Q : PauliSDP.Index n k) : |PauliSDP.realGram k L P Q| ≤ 1 := by
  have hpsd : ((PauliSDP.realGram k L).submatrix ![P, Q] ![P, Q]).PosSemidef := h.2.submatrix _
  have hdiag : ∀ i : Fin 2, ((PauliSDP.realGram k L).submatrix ![P, Q] ![P, Q]) i i = 1 := by
    intro i
    show (PauliSDP.wordPhase _ _).re * L (PauliSDP.wordProduct _ _) = 1
    rw [wordPhase_self, (wordProduct_eq_id _ _).mpr rfl, h.1]
    simp
  exact psd_unitDiag_abs_le_one hpsd hdiag 0 1

theorem twoBody_abs_le (k : ℕ) (G : Input) (hk : 1 ≤ k) (L : PauliSDP.Word G.n → ℝ)
    (h : PauliSDP.Feasible k L) (a : Fin 4) (e : Edge G.n) :
    |L (PauliSDP.twoBody a e)| ≤ 1 := by
  have hp : (PauliSDP.support (single a e.val.1)).card ≤ k := (support_single_card _ _).trans hk
  have hq : (PauliSDP.support (single a e.val.2)).card ≤ k := (support_single_card _ _).trans hk
  have hb := gram_abs_le k L h ⟨single a e.val.1, hp⟩ ⟨single a e.val.2, hq⟩
  have he : PauliSDP.realGram k L ⟨single a e.val.1, hp⟩ ⟨single a e.val.2, hq⟩ =
      L (PauliSDP.twoBody a e) := by
    show (PauliSDP.wordPhase _ _).re * L (PauliSDP.wordProduct _ _) = _
    rw [wordPhase_single a a _ _ (ne_of_lt e.2), wordProduct_single]
    simp
  rwa [he] at hb

theorem objective_le_two (k : ℕ) (G : Input) (hk : 1 ≤ k) (L : PauliSDP.Word G.n → ℝ)
    (h : PauliSDP.Feasible k L) :
    PauliSDP.objective G.weights L ≤ 2 * ((Wq G : ℚ) : ℝ) := by
  rw [Wq_cast, Finset.mul_sum]
  unfold PauliSDP.objective
  refine Finset.sum_le_sum fun e _ => ?_
  have h1 := (abs_le.mp (twoBody_abs_le k G hk L h 1 e)).1
  have h2 := (abs_le.mp (twoBody_abs_le k G hk L h 2 e)).1
  have h3 := (abs_le.mp (twoBody_abs_le k G hk L h 3 e)).1
  have hw : (0 : ℝ) ≤ (G.weights e : ℝ) := NNRat.cast_nonneg _
  have hm := mul_nonneg hw (by linarith : (0 : ℝ) ≤ 3 + L (PauliSDP.twoBody 1 e) +
    L (PauliSDP.twoBody 2 e) + L (PauliSDP.twoBody 3 e))
  linarith

theorem exists_feasible (k : ℕ) (G : Input) :
    ∃ L : PauliSDP.Word G.n → ℝ, PauliSDP.Feasible k L ∧
      0 ≤ PauliSDP.objective G.weights L := by
  refine ⟨fun P => if P = PauliSDP.identityWord G.n then 1 else 0, ⟨if_pos rfl, ?_⟩, ?_⟩
  · have hG : PauliSDP.realGram k
        (fun P => if P = PauliSDP.identityWord G.n then (1 : ℝ) else 0) = 1 := by
      ext P Q
      show (PauliSDP.wordPhase P.val Q.val).re *
        (if PauliSDP.wordProduct P.val Q.val = PauliSDP.identityWord G.n then 1 else 0) = _
      rw [Matrix.one_apply]
      by_cases hPQ : P = Q
      · subst hPQ
        rw [if_pos rfl, if_pos ((wordProduct_eq_id _ _).mpr rfl), wordPhase_self]
        simp
      · rw [if_neg hPQ,
          if_neg (fun h => hPQ (Subtype.ext ((wordProduct_eq_id _ _).mp h)))]
        simp
    rw [hG]
    exact Matrix.PosSemidef.one
  · unfold PauliSDP.objective
    refine Finset.sum_nonneg fun e _ => ?_
    have hne : ∀ a : Fin 4, a ≠ 0 → PauliSDP.twoBody a e ≠ PauliSDP.identityWord G.n := by
      intro a ha h
      have h1 := congrFun h e.val.1
      simp [PauliSDP.twoBody, PauliSDP.identityWord] at h1
      exact ha h1
    simp only [if_neg (hne 1 (by decide)), if_neg (hne 2 (by decide)),
      if_neg (hne 3 (by decide))]
    have hw : (0 : ℝ) ≤ (G.weights e : ℝ) := NNRat.cast_nonneg _
    linarith

theorem objective_zero (G : Input) (hW : Wq G = 0) (L : PauliSDP.Word G.n → ℝ) :
    PauliSDP.objective G.weights L = 0 := by
  have hw : ∀ e : Edge G.n, (G.weights e : ℚ) = 0 := fun e =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => NNRat.coe_nonneg _)).mp hW e
      (Finset.mem_univ e)
  unfold PauliSDP.objective
  refine Finset.sum_eq_zero fun e _ => ?_
  have h2 : G.weights e = 0 := by exact_mod_cast hw e
  rw [h2]
  simp

end QMCTied


