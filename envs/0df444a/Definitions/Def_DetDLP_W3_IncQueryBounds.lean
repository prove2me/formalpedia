-- Prove2me | Definitions.Def_DetDLP_W3_IncQueryBounds
-- name    : DetDLP_W3_IncQueryBounds
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T02:06:13.475749+00:00
-- url     : https://prove2.me/theorems/689a94d8-4d60-48ff-a645-b8ba8ff58eca
-- title:
--   Length budgets for legal incidence graph queries
-- statement:
--   Suppose each gate reads at least one bit, every bit has a representative incidence, and twice the incidence count is at most a positive budget $S$. For an arbitrary descriptor of length $D$, both the number of subdivided vertices and the length plus one of any legal ordered-port query are at most $(S+D+1)^5$.

import Definitions.Def_DetDLP_W3_FpIncidence
import Definitions.Def_DetDLP_W3_FpWire1

set_option autoImplicit false
namespace DetDLP
open w4_M5Network
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem w3_incDims (A : w3_FactorLayout) (hg : Function.Surjective A.gate) :
    A.ng ≤ A.ne ∧ A.nb ≤ A.ne := by
  constructor
  · simpa using Fintype.card_le_of_surjective A.gate hg
  · simpa using Fintype.card_le_of_injective A.rep (Function.RightInverse.injective A.rep_bit)

theorem w3_queryExactLength (w a : List Bool) (v : ℕ) :
    (encodePortQuery w v a).length = 2*(w.length+(countWord v).length+a.length)+7 := by
  simp [encodePortQuery, Encoding.encodeList,w3_frameLength]; omega

theorem w3_queryIndexLength (n : ℕ) : (countWord n).length ≤ n+1 := by
  by_cases h : n = 0
  · simp [h,countWord]
  · simp only [countWord,if_neg h,Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr n.lt_two_pow_self).trans (Nat.le_succ _)

theorem w3_queryArith {nv ne deg v cw S D : ℕ} (h1 : nv ≤ 3*ne) (h2 : 2*ne ≤ S)
    (h3 : v < nv) (h4 : cw ≤ v+1) (h5 : deg ≤ 2*ne) :
    2*(D+cw+deg)+7+1 ≤ 16*(S+D+1) := by omega

theorem w3_incQueryBounds (A : w3_FactorLayout) (hg : Function.Surjective A.gate)
    (S : ℕ) (hS : 1 ≤ S) (he : 2*A.ne ≤ S) (desc : List Bool) :
    let G := (w3_factorGraph A).subdivision
    G.nV ≤ (S+desc.length+1)^5 ∧ ∀ (v : Fin G.nV) (a : Fin (G.deg v) → Bool),
      (encodePortQuery desc v.val (List.ofFn a)).length+1 ≤ (S+desc.length+1)^5 := by
  obtain ⟨hng,hnb⟩ := w3_incDims A hg
  let G := (w3_factorGraph A).subdivision
  let B := S+desc.length+1
  have hB : 2 ≤ B := by dsimp [B]; omega
  have hpow : 16*B ≤ B^5 := by
    rw [show (5:ℕ) = 4+1 by decide,pow_succ]
    exact Nat.mul_le_mul_right B (show 2^4 ≤ B^4 from Nat.pow_le_pow_left hB 4)
  have hv : G.nV ≤ 3*A.ne := by change A.ng+A.nb+A.ne ≤ _; omega
  have hn : G.nE = 2*A.ne := WireGraph.subdivision_nE _
  constructor
  · have ha : 3*A.ne ≤ 16*B := by dsimp [B]; omega
    exact hv.trans (ha.trans hpow)
  · intro v a
    have hd : G.deg v ≤ G.nE := (List.length_filter_le ..).trans List.length_finRange.le
    have hv' : v.val < G.nV := v.isLt
    have hc := w3_queryIndexLength v.val
    rw [w3_queryExactLength,List.length_ofFn]
    exact (w3_queryArith (D := desc.length) hv he hv' hc (hd.trans hn.le)).trans hpow

end DetDLP


