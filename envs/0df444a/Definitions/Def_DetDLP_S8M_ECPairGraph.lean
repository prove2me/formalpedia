-- Prove2me | Definitions.Def_DetDLP_S8M_ECPairGraph
-- name    : DetDLP_S8M_ECPairGraph
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:47:49.951805+00:00
-- url     : https://prove2.me/theorems/53b4efb1-a617-4d83-b6d8-3dd53d050e69
-- title:
--   Elliptic curve pair query graph bounds
-- statement:
--   Bounds the encoded Tag 6 query, incidence size and maximum degree, and derives the Tag 6 realization from a layout with a parsimonious witness equivalence and exact packet functions.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8G_FpMomentGraph

set_option autoImplicit false
namespace DetDLP.S8M.ECPair
open M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))

def word {m : ℕ} (T : ℕ) (S : ECSeed p m) (X : E.toAffine.Point) (η : List Bool) :=
  queryWord 6 (encodeCurveInput p E) [countWord T,List.ofFn (ecBits S),encodeNatListBin (pointCoords X),η]

private theorem listLength (xs : List ℕ) (h : ∀ x ∈ xs, x ≤ p) :
    (encodeNatListBin xs).length ≤ xs.length * (2*bitLen p+4)+1 := by
  induction xs with
  | nil => simp [encodeNatListBin,Encoding.encodeList]
  | cons x xs ih =>
    have h1 := S8G.FpMoment.binaryLen (h x List.mem_cons_self)
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [encodeNatListBin,Encoding.encodeList,List.length_cons,List.length_append,w3_frameLength,Nat.succ_mul] at *
    omega

theorem wordLen {m T : ℕ} (S : ECSeed p m) (X : E.toAffine.Point) (η : List Bool) (hm : 1 ≤ m)
    (hT : T ≤ p) (hη : η.length ≤ 2*m*(2*bitLen p+1)) :
    (word E T S X η).length ≤ 256*m*bitLen p := by
  have hb : 1 ≤ bitLen p := Nat.clog_pos (by decide) (Fact.out : p.Prime).one_lt
  have hc : (encodeCurveInput p E).length ≤ 6*(2*bitLen p+4)+1 := by
    apply listLength
    simp only [List.mem_cons,List.not_mem_nil,or_false]; rintro x (rfl|rfl|rfl|rfl|rfl|rfl) <;> first | exact le_rfl | exact (ZMod.val_lt _).le
  have hx : (encodeNatListBin (pointCoords X)).length ≤ 3*(2*bitLen p+4)+1 := by
    cases X <;> apply listLength <;> simp only [pointCoords,List.mem_cons,List.not_mem_nil,or_false] <;>
      rintro x (rfl|rfl|rfl) <;> first | exact Nat.zero_le _ | exact (Fact.out : p.Prime).one_lt.le | exact (ZMod.val_lt _).le
  have ht := S8G.FpMoment.binaryLen hT
  have h6 : (countWord 6).length = 3 := by decide
  have h1 := Nat.le_mul_of_pos_left (bitLen p) hm
  have h2 := Nat.le_mul_of_pos_right m hb
  simp only [word,queryWord,Encoding.encodeList,id_eq,List.length_cons,List.length_append,w3_frameLength,List.length_nil,List.length_ofFn,h6]
  ring_nf at hη ⊢
  omega

def scale (m b : ℕ) := 524288*m*(b+2)

theorem degreeBudget {m b : ℕ} (hm : 1 ≤ m) :
    max 12 (Nat.ceil (136*((b:ℝ)+2)^((3:ℝ)/4))) ≤ Nat.ceil ((scale m b:ℝ)^((9:ℝ)/10)) := by
  apply (S8G.FpMoment.degreeBudget hm).trans
  apply Nat.ceil_mono; apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  exact_mod_cast (show S8G.FpMoment.scale m b ≤ scale m b by unfold scale S8G.FpMoment.scale; gcongr <;> norm_num)

variable [E.IsElliptic]
noncomputable def value {m : ℕ} (T : ℕ) (S : ECSeed p m) (X : E.toAffine.Point) (η : List Bool) :=
  letI := ecPointFintype E
  pairCount (ecFactorBlock E T S) (ecWord (bitLen p)) (fun ab => (∑ i, (ab.1 i + ab.2 i)) = X) η

variable {T : ℕ} (S : ECSeed p (blockCount (bitLen p))) (X : E.toAffine.Point) (η : List Bool)

theorem wordBudget (hT : T ≤ p) (hη : η.length ≤ 2*blockCount (bitLen p)*(2*bitLen p+1)) :
    let b := bitLen p; let m := blockCount b; let w := word E T S X η
    scale m b+w.length ≤ 1600000*m*b ∧ scale m b+w.length ≤ 1600000*(b+1)^1600000 := by
  dsimp only; let b := bitLen p; let m := blockCount b
  have hm : 1 ≤ m := (by decide : 1 ≤ 2).trans (le_max_left _ _)
  have hb : 1 ≤ b := Nat.clog_pos (by decide) (Fact.out : p.Prime).one_lt
  have hw := wordLen E S X η hm hT hη
  have hs : scale m b ≤ 1572864*m*b := by
    calc _ ≤ 524288*m*(3*b) := Nat.mul_le_mul_left _ (by omega)
         _ = _ := by ring
  have hfirst : scale m b+(word E T S X η).length ≤ 1600000*m*b := by nlinarith
  refine ⟨hfirst,hfirst.trans ?_⟩
  rw [Nat.mul_assoc]; apply Nat.mul_le_mul_left
  calc m*b ≤ (b+2)*b := Nat.mul_le_mul_right b (S8G.FpMoment.blockUpper b)
       _ ≤ (b+1)^2 := by nlinarith
       _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)

theorem ofLayout (hT : T ≤ p) (hη : η.length ≤ 2*blockCount (bitLen p)*(2*bitLen p+1))
    (A : w3_FactorLayout) (test : w3_factorTest A) (hg : Function.Surjective A.gate)
    (make port : List Bool → List Bool) {W : Type} [Fintype W]
    (witness : {b : Fin A.nb → Bool // ∀ g, test g (fun e => b (A.bit e.1)) = true} ≃ W)
    (count : Fintype.card W = value E T S X η)
    (edges : 2*A.ne < scale (blockCount (bitLen p)) (bitLen p))
    (degree : ∀ v, (w3_factorGraph A).deg v ≤ max 12 (Nat.ceil (136*((bitLen p:ℝ)+2)^((3:ℝ)/4))))
    (build : make (word E T S X η) = encodeBTNInstance (word E T S X η) (w3_factorGraph A).subdivision
      (scale (blockCount (bitLen p)) (bitLen p)) (scale (blockCount (bitLen p)) (bitLen p)) 1)
    (eval : ∀ v a, port (encodePortQuery (word E T S X η) v.val (List.ofFn a)) =
      encodeNatListBin [if (w3_factorGraph A).subdivisionTensor (w3_factorChecks A test) v a then 1 else 0]) :
    S8C.Realizes make port 1600000 (word E T S X η) (bitLen p) (value E T S X η) := by
  let b := bitLen p; let m := blockCount b; let s := scale m b; let w := word E T S X η
  have hm : 1 ≤ m := (by decide : 1 ≤ 2).trans (le_max_left _ _)
  have hscale : b+2 ≤ s := Nat.le_mul_of_pos_left _ (by dsimp [m] at hm; dsimp [m]; positivity)
  have hs : 2 ≤ s := by omega
  have he : 2*A.ne < s := edges
  have dims := w3_incDims A hg
  have qs := w3_incQueryBounds A hg s (by omega) he.le w
  have wb := wordBudget E S X η hT hη
  rw [← count]
  refine S8C.wireRealizes make port 1600000 s b w _ _ ((w3_factorEquiv A test).trans witness) hs
    (by omega) edges ?_ ?_ wb.1 wb.2 build ?_
  · change A.ng+A.nb+A.ne ≤ s^1600000
    calc _ ≤ s^2 := by nlinarith [dims.1,dims.2]
         _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  · apply (max_le (Finset.sup_le (fun v _ => degree v)) (le_trans (by decide : 2 ≤ 12) (le_max_left _ _))).trans
    exact degreeBudget hm
  · intro v a
    refine ⟨(Nat.le_of_succ_le (qs.2 v a)).trans ?_,eval v a⟩
    exact (Nat.pow_le_pow_right (by omega) (by decide : 5 ≤ 1600000)).trans
      (Nat.le_mul_of_pos_left _ (by decide))

theorem tagIntro (make port : List Bool → List Bool) (L : ℕ) (hm : Groundwork.PolyT make)
    (he : Groundwork.PolyT port)
    (h : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
      (T : ℕ) (S : ECSeed p (blockCount (bitLen p))) (X : E.toAffine.Point) (η : List Bool), T ≤ p →
      η.length ≤ 2*blockCount (bitLen p)*(2*bitLen p+1) →
      S8C.Realizes make port L (word E T S X η) (bitLen p) (value E T S X η)) :
    S8C.TagSpec [6] := by
  refine ⟨make,port,L,hm,he,?_⟩
  rintro t ht base payload b n hq
  obtain rfl : t = 6 := by simpa using ht
  generalize hw : queryWord 6 base payload = w at hq ⊢
  have tag : Groundwork.PolyT.bval (DetDLP_W1_Queries.first w) = 6 := by subst w; simp [queryWord]
  cases hq <;> simp only [queryWord,DetDLP_W1_Queries.first_cons,id_eq,DetDLP_W1_Queries.decode_count] at tag
  all_goals first | contradiction | exact h _ (by assumption) _ _ _ _ _ (by assumption) (by assumption)

end DetDLP.S8M.ECPair


