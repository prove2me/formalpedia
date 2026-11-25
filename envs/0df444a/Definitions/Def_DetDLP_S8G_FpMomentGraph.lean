-- Prove2me | Definitions.Def_DetDLP_S8G_FpMomentGraph
-- name    : DetDLP_S8G_FpMomentGraph
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:59:02.329633+00:00
-- url     : https://prove2.me/theorems/331c5514-6e73-4487-8b73-4c53a5cf3848
-- title:
--   Graph bounds for prime-field moment queries
-- statement:
--   Estimates on multiplier incidences, maximum degree and the query budget for prime-field moment graphs.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_W3_FpMulIncidence
import Definitions.Def_DetDLP_W3_IncQueryBounds
import Definitions.Def_DetDLP_S8G_FpMomentCount
import Definitions.Def_DetDLP_S8C_WireBTN
import Definitions.Def_DetDLP_S8C_Packet

set_option autoImplicit false
namespace DetDLP.S8G.FpMoment
open M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

def word (p : ℕ) (j : Fin 4) (T : ℕ) (η : List Bool) :=
  queryWord 1 (countWord p) [countWord j.val,countWord T,η]

theorem binaryLen {x p : ℕ} (h : x ≤ p) : (countWord x).length ≤ bitLen p + 1 := by
  by_cases hx : x = 0
  · simp [countWord,hx]
  · rw [countWord,if_neg hx,Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    exact h.trans_lt ((Nat.le_pow_clog (by decide : 1 < 2) p).trans_lt
      (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)))

theorem wordLen {p T m : ℕ} [Fact p.Prime] (j : Fin 4) (η : List Bool) (hm : 1 ≤ m)
    (hT : T ≤ p) (hη : η.length ≤ m*2*bitLen p) : (word p j T η).length ≤ 40*m*bitLen p := by
  have hb : 1 ≤ bitLen p := Nat.clog_pos (by decide) (Fact.out : p.Prime).one_lt
  have h1 := binaryLen (le_refl p)
  have h2 := binaryLen hT
  have hj := w3_queryIndexLength j.val
  have hj' := j.isLt
  have ht : (countWord 1).length = 1 := by decide
  have hm' : bitLen p ≤ m*bitLen p := Nat.le_mul_of_pos_left _ hm
  simp only [word,queryWord,Encoding.encodeList,id_eq,List.length_cons,List.length_append,
    w3_frameLength,List.length_nil,ht]
  rw [show m*2*bitLen p = 2*(m*bitLen p) by ring] at hη
  rw [show 40*m*bitLen p = 40*(m*bitLen p) by ring]
  omega

/-- At most two raw multipliers per modular product, including the hash products. -/
theorem multiplierEdges {b m k : ℕ} (hk : k ≤ 8*m) :
    k*(w3_fpMulLayout (b+1) (Nat.succ_pos _)).ne ≤ 17600*m*(b+2) := by
  have h := (w3_fpMulIncidenceBounds (Nat.succ_pos b)).1
  calc _ ≤ (8*m)*(2200*(b+2)) := Nat.mul_le_mul hk h.le
       _ = _ := by ring

def scale (m b : ℕ) := 65536*m*(b+2)

theorem degreeBudget {m b : ℕ} (hm : 1 ≤ m) :
    max 12 (Nat.ceil (136*((b:ℝ)+2)^((3:ℝ)/4))) ≤ Nat.ceil ((scale m b:ℝ)^((9:ℝ)/10)) := by
  have hb : (1:ℝ) ≤ (b:ℝ)+2 := by linarith [Nat.cast_nonneg (α := ℝ) b]
  have h1 : (136:ℝ) ≤ 65536^((9:ℝ)/10) := by
    have hr := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 65536)
      (by norm_num : (1:ℝ)/2 ≤ 9/10)
    rw [← Real.sqrt_eq_rpow] at hr
    refine le_trans ?_ hr
    exact (Real.le_sqrt_of_sq_le (by norm_num))
  have h2 := Real.rpow_le_rpow_of_exponent_le hb (by norm_num : (3:ℝ)/4 ≤ 9/10)
  have hs : 65536*((b:ℝ)+2) ≤ (scale m b:ℝ) := by
    unfold scale; push_cast; gcongr; exact_mod_cast Nat.le_mul_of_pos_right 65536 hm
  have h3 : 136*((b:ℝ)+2)^((3:ℝ)/4) ≤ (scale m b:ℝ)^((9:ℝ)/10) := by
    calc _ ≤ 65536^((9:ℝ)/10)*((b:ℝ)+2)^((9:ℝ)/10) := mul_le_mul h1 h2 (by positivity) (by positivity)
         _ = (65536*((b:ℝ)+2))^((9:ℝ)/10) := (Real.mul_rpow (by norm_num) (by positivity)).symm
         _ ≤ _ := Real.rpow_le_rpow (by positivity) hs (by norm_num)
  have h4 : 1 ≤ ((b:ℝ)+2)^((3:ℝ)/4) := Real.one_le_rpow hb (by norm_num)
  apply max_le _ (Nat.ceil_mono h3)
  have h5 : (12:ℝ) ≤ 136*((b:ℝ)+2)^((3:ℝ)/4) := by linarith
  exact_mod_cast h5.trans (h3.trans (Nat.le_ceil _))

theorem blockUpper (b : ℕ) : blockCount b ≤ b+2 := by
  unfold blockCount
  apply max_le (by omega)
  apply Nat.ceil_le.mpr
  have h := Nat.clog_le_of_le_pow (show b+2 < 2^(b+2) from Nat.lt_two_pow_self).le
  have hpos : 1 ≤ Nat.clog 2 (b+2) := Nat.clog_pos (by decide) (by omega)
  calc _ ≤ (Nat.clog 2 (b+2):ℝ)^((1:ℝ)) :=
         Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpos) (by norm_num)
       _ ≤ _ := by rw [Real.rpow_one]; exact_mod_cast h

theorem wordBudget {p T : ℕ} [Fact p.Prime] (j : Fin 4) (η : List Bool) (hT : T ≤ p)
    (hη : η.length ≤ blockCount (bitLen p)*2*bitLen p) :
    let b := bitLen p; let m := blockCount b; let w := word p j T η
    scale m b+w.length ≤ 200000*m*b ∧ scale m b+w.length ≤ 200000*(b+1)^200000 := by
  dsimp only
  let b := bitLen p
  let m := blockCount b
  have hm : 1 ≤ m := (by decide : 1 ≤ 2).trans (le_max_left _ _)
  have hb : 1 ≤ b := Nat.clog_pos (by decide) (Fact.out : p.Prime).one_lt
  have hw := wordLen j η hm hT hη
  have hs : scale m b ≤ 196608*m*b := by
    calc _ ≤ 65536*m*(3*b) := Nat.mul_le_mul_left _ (by omega)
         _ = _ := by ring
  have hfirst : scale m b+(word p j T η).length ≤ 200000*m*b := by nlinarith
  refine ⟨hfirst,hfirst.trans ?_⟩
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  have hmb := Nat.mul_le_mul_right b (blockUpper b)
  calc m*b ≤ (b+2)*b := hmb
       _ ≤ (b+1)^2 := by nlinarith
       _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)

/-- Incorporate the incidence bijection, numerical budgets, and encoded local test. -/
theorem ofLayout {p T : ℕ} [Fact p.Prime] (j : Fin 4) (η : List Bool) (hT : T ≤ p)
    (hη : η.length ≤ blockCount (bitLen p)*2*bitLen p)
    (A : w3_FactorLayout) (test : w3_factorTest A) (hg : Function.Surjective A.gate)
    (make port : List Bool → List Bool) {W : Type} [Fintype W]
    (witness : {b : Fin A.nb → Bool // ∀ g, test g (fun e => b (A.bit e.1)) = true} ≃ W)
    (count : Fintype.card W = value p (blockCount (bitLen p)) T η j)
    (edges : 2*A.ne < scale (blockCount (bitLen p)) (bitLen p))
    (degree : ∀ v, (w3_factorGraph A).deg v ≤ max 12 (Nat.ceil (136*((bitLen p:ℝ)+2)^((3:ℝ)/4))))
    (build : make (word p j T η) = encodeBTNInstance (word p j T η) (w3_factorGraph A).subdivision
      (scale (blockCount (bitLen p)) (bitLen p)) (scale (blockCount (bitLen p)) (bitLen p)) 1)
    (eval : ∀ v a, port (encodePortQuery (word p j T η) v.val (List.ofFn a)) =
      encodeNatListBin [if (w3_factorGraph A).subdivisionTensor (w3_factorChecks A test) v a then 1 else 0]) :
    S8C.Realizes make port 200000 (word p j T η) (bitLen p) (value p (blockCount (bitLen p)) T η j) := by
  let b := bitLen p
  let m := blockCount b
  let s := scale m b
  let w := word p j T η
  have hm : 1 ≤ m := (by decide : 1 ≤ 2).trans (le_max_left _ _)
  have hscale : b+2 ≤ s := Nat.le_mul_of_pos_left _ (by dsimp [m] at hm; dsimp [m]; positivity)
  have hs : 2 ≤ s := by omega
  have he : 2*A.ne < s := edges
  have dims := w3_incDims A hg
  have qs := w3_incQueryBounds A hg s (by omega) he.le w
  have wb := wordBudget j η hT hη
  rw [← count]
  refine S8C.wireRealizes make port 200000 s b w _ _ ((w3_factorEquiv A test).trans witness) hs
    (by omega) edges ?_ ?_ wb.1 wb.2 build ?_
  · change A.ng+A.nb+A.ne ≤ s^200000
    calc _ ≤ s^2 := by nlinarith [dims.1,dims.2]
         _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  · apply (max_le (Finset.sup_le (fun v _ => degree v)) (le_trans (by decide : 2 ≤ 12) (le_max_left _ _))).trans
    exact degreeBudget hm
  · intro v a
    refine ⟨(Nat.le_of_succ_le (qs.2 v a)).trans ?_,eval v a⟩
    exact (Nat.pow_le_pow_right (by omega) (by decide : 5 ≤ 200000)).trans
      (Nat.le_mul_of_pos_left _ (by decide))

/-- The outer tag can be read before inspecting the query's dependent indices. -/
theorem tagIntro (make port : List Bool → List Bool) (L : ℕ) (hm : Groundwork.PolyT make)
    (he : Groundwork.PolyT port)
    (h : ∀ (p : ℕ) [Fact p.Prime] (j : Fin 4) (T : ℕ) (η : List Bool), T ≤ p →
      η.length ≤ blockCount (bitLen p)*2*bitLen p →
      S8C.Realizes make port L (word p j T η) (bitLen p) (value p (blockCount (bitLen p)) T η j)) :
    S8C.TagSpec [1] := by
  refine ⟨make,port,L,hm,he,?_⟩
  rintro t ht base payload b n hq
  obtain rfl : t = 1 := by simpa using ht
  generalize hw : queryWord 1 base payload = w at hq ⊢
  have tag : Groundwork.PolyT.bval (DetDLP_W1_Queries.first w) = 1 := by
    subst w; simp [queryWord]
  cases hq <;> simp only [queryWord,DetDLP_W1_Queries.first_cons,id_eq,DetDLP_W1_Queries.decode_count] at tag
  all_goals first | contradiction | exact h _ _ _ _ (by assumption) (by assumption)

end DetDLP.S8G.FpMoment


