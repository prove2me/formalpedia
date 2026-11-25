-- Prove2me | Definitions.Def_DetDLP_S8H0_OrderPacket
-- name    : DetDLP_S8H0_OrderPacket
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:45:51.313167+00:00
-- url     : https://prove2.me/theorems/65efd00a-4f37-417f-b922-a6bbae0c6847
-- title:
--   Size bounds and dispatch for the elliptic-curve order query
-- statement:
--   For an incidence layout whose accepting assignments decode bijectively to the seven-block physical transcripts, the encoded graph and evaluator realize the elliptic-curve point-count query under explicit linear-size and sublinear-degree hypotheses. The modulus bit length bounds the curve word, the instance scale, and every port-query word. Tag dispatch eliminates all query constructors except the order constructor.
-- source:
--   DetDLP.s8h_ec_order_query, f0e81f0e-6143-4672-a126-0c2b5aa2d552. Companion to the S8H0 seven-check compiler.

import Definitions.Def_DetDLP_S8G_FpMomentGraph
import Definitions.Def_DetDLP_S8H0_SevenChecks

set_option autoImplicit false
namespace DetDLP.S8H0.OrderPacket
open M89S1 S8C S8H.ECPointSlots SevenChecks
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))

def word := queryWord 0 (encodeCurveInput p E) []
def scale (b : ℕ) := 1048576*(b+2)
abbrev constant := 3200000

private theorem listLen (xs : List ℕ) (h : ∀ x ∈ xs, x ≤ p) :
    (encodeNatListBin xs).length ≤ xs.length*(2*bitLen p+4)+1 := by
  induction xs with
  | nil => simp [encodeNatListBin,Encoding.encodeList]
  | cons x xs ih =>
    have h1 := S8G.FpMoment.binaryLen (h x List.mem_cons_self)
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [encodeNatListBin,Encoding.encodeList,List.length_cons,List.length_append,w3_frameLength,Nat.succ_mul] at *
    omega

theorem wordLen : (word E).length ≤ 100*bitLen p := by
  have hb : 1 ≤ bitLen p := Nat.clog_pos (by decide) (Fact.out : p.Prime).one_lt
  have hc : (encodeCurveInput p E).length ≤ 6*(2*bitLen p+4)+1 := by
    apply listLen
    simp only [List.mem_cons,List.not_mem_nil,or_false]; rintro x (rfl|rfl|rfl|rfl|rfl|rfl) <;> first | exact le_rfl | exact (ZMod.val_lt _).le
  have hz : (countWord 0).length = 1 := by decide
  simp only [word,queryWord,Encoding.encodeList,id_eq,List.length_cons,List.length_append,w3_frameLength,List.length_nil,hz]
  omega

theorem budgets : let b := bitLen p; let s := scale b
    s+(word E).length ≤ constant * blockCount b * b ∧ s+(word E).length ≤ constant*(b+1)^constant := by
  dsimp only
  have hb : 1 ≤ bitLen p := Nat.clog_pos (by decide) (Fact.out : p.Prime).one_lt
  have h1 : scale (bitLen p)+(word E).length ≤ constant * bitLen p := by
    have := wordLen E; unfold scale constant; omega
  constructor
  · apply h1.trans
    apply Nat.mul_le_mul_right
    exact Nat.le_mul_of_pos_right _ (lt_of_lt_of_le (by decide : 0 < 2) (le_max_left _ _))
  · apply h1.trans; apply Nat.mul_le_mul_left
    exact (Nat.le_succ _).trans (Nat.le_self_pow (by decide : constant ≠ 0) _)

theorem degreeBudget (b : ℕ) : max 12 (Nat.ceil (136*((b:ℝ)+2)^((3:ℝ)/4))) ≤
    Nat.ceil ((scale b:ℝ)^((9:ℝ)/10)) := by
  apply (S8G.FpMoment.degreeBudget (b:=b) (m:=1) (by decide)).trans
  apply Nat.ceil_mono; apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  exact_mod_cast (show S8G.FpMoment.scale 1 b ≤ scale b by unfold scale S8G.FpMoment.scale; omega)

theorem ofLayout [E.IsElliptic] (mul : w3_modMulInterface) (A : w3_FactorLayout) (test : w3_factorTest A)
    (hg : A.ng ≤ scale (bitLen p)) (make port : List Bool → List Bool)
    (sem : {x : Fin A.nb → Bool // S8J.Accept A test x} ≃ {w : C p × Transcript p // physical E w.1 w.2})
    (edges : 2*A.ne < scale (bitLen p))
    (degree : ∀ v, (w3_factorGraph A).deg v ≤ max 12 (Nat.ceil (136*((bitLen p:ℝ)+2)^((3:ℝ)/4))))
    (build : make (word E) = encodeBTNInstance (word E) (w3_factorGraph A).subdivision (scale (bitLen p)) (scale (bitLen p)) 1)
    (eval : ∀ v a, port (encodePortQuery (word E) v.val (List.ofFn a)) =
      encodeNatListBin [if (w3_factorGraph A).subdivisionTensor (w3_factorChecks A test) v a then 1 else 0]) :
    Realizes make port constant (word E) (bitLen p) (@Fintype.card _ (ecPointFintype E)) := by
  letI := ecPointFintype E
  let b := bitLen p; let s := scale b; let w := word E
  have hs : b+2 ≤ s := Nat.le_mul_of_pos_left _ (by decide)
  have hn : A.nb ≤ A.ne := by simpa using Fintype.card_le_of_injective A.rep (Function.RightInverse.injective A.rep_bit)
  have hv : A.ng+A.nb+A.ne ≤ 2*s := by dsimp [s,b] at *; omega
  have wb := budgets E
  apply wireRealizes make port constant s b w (w3_factorGraph A) (w3_factorChecks A test)
    ((w3_factorEquiv A test).trans (sem.trans (pointEquiv E mul))) (by omega) (by omega) edges
  · change A.ng+A.nb+A.ne ≤ s^constant
    calc _ ≤ s^2 := by nlinarith
         _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  · apply (max_le (Finset.sup_le (fun v _ => degree v)) (le_trans (by decide : 2 ≤ 12) (le_max_left _ _))).trans (degreeBudget b)
  · exact wb.1
  · exact wb.2
  · exact build
  · intro v a; refine ⟨?_,eval v a⟩
    have hi : v.val < 2*s := v.isLt.trans_le hv
    have hd : ((w3_factorGraph A).subdivision.deg v) ≤ 2*A.ne :=
      (List.length_filter_le ..).trans (List.length_finRange.le.trans ((w3_factorGraph A).subdivision_nE.le))
    have hc := w3_queryIndexLength v.val
    rw [w3_queryExactLength,List.length_ofFn]
    have he : 2*A.ne < s := edges
    calc _ ≤ 16*(s+w.length+1) := by omega
         _ ≤ constant*(s+w.length+1)^constant := Nat.mul_le_mul (by decide) (Nat.le_self_pow (by decide : constant ≠ 0) _)

theorem tagIntro (make port : List Bool → List Bool) (hm : Groundwork.PolyT make) (hp : Groundwork.PolyT port)
    (h : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
      Realizes make port constant (word E) (bitLen p) (@Fintype.card _ (ecPointFintype E))) : TagSpec [0] := by
  refine ⟨make,port,constant,hm,hp,?_⟩
  rintro t ht base payload b n hq
  obtain rfl : t = 0 := by simpa using ht
  generalize hw : queryWord 0 base payload = w at hq ⊢
  have tag : Groundwork.PolyT.bval (DetDLP_W1_Queries.first w) = 0 := by subst w; simp [queryWord]
  cases hq <;> simp only [queryWord,DetDLP_W1_Queries.first_cons,id_eq,DetDLP_W1_Queries.decode_count] at tag
  all_goals first | contradiction | exact h _ (by assumption) _

end DetDLP.S8H0.OrderPacket


