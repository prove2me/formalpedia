-- Prove2me | Definitions.Def_DetDLP_S6B_Budget
-- name    : DetDLP_S6B_Budget
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:20:10.38481+00:00
-- url     : https://prove2.me/theorems/1507ebd1-7f9f-4cc3-998b-a6b92642d40f
-- title:
--   Polynomial space budget for the prefix-search packets
-- statement:
--   For every legal prefix, the saved state, the next contraction query, the count reply and the terminal output are all bounded by one polynomial in the original binary input length. The bound applies uniformly at each search round.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Proposition 2.6 (pp. 10–11)

import Definitions.Def_DetDLP_S6B_Step
import Theorems.Thm_Groundwork_PB_comp
set_option autoImplicit false
namespace DetDLP.S6BBudget
open Groundwork Groundwork.PolyT S6BWords S6BPrefix S6BStep w5_M6DivisorConstraints
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem pbPow {t : ℕ → ℕ} (h : PB t) (k : ℕ) : PB (fun n => (t n)^k) := by
  induction k with
  | zero => simpa using PB.const 1
  | succ k ih => simpa [pow_succ] using ih.mul h

def P (k n : ℕ) := k*(n+1)^k
theorem Ppb (k : ℕ) {t : ℕ → ℕ} (ht : PB t) : PB (fun n => P k (t n)) := (PB.const k).mul (pbPow (ht.add (PB.const 1)) k)
@[simp] theorem cast_P (k n : ℕ) : ((P k n : ℕ):ℝ) = polyBound k n := by simp [P,polyBound]

@[simp] theorem length_pair (s a : Wd) : (pair s a).length = 2*s.length+1+a.length := by simp [pair_eq,w4_M5QueryBridge.length_frame]

private theorem replyBound (w p : Wd) : (reply w p).length ≤ 8*w.length+7 := by
  let d := w.length
  let c := completionCount (ProductIs (d:=d) (bval w)) (pins (p++[false]))
  have hc : c ≤ 2^(4*d) := by
    classical
    unfold c completionCount
    exact (Finset.card_filter_le ..).trans (by simp)
  have hlt : c < 2^(4*d+1) := by
    rw [pow_succ]; have hpos : 0 < 2^(4*d) := by positivity
    omega
  have hcw : (countWord c).length ≤ 4*d+1 := by
    by_cases hz : c=0
    · simp [hz,countWord]
    · simpa [countWord,hz,Nat.size_eq_bits_len] using Nat.size_le.mpr hlt
  change (encodeNatListBin [c]).length ≤ 8*d+7
  simp only [encodeNatListBin,Encoding.encodeList,List.length_cons,List.length_nil,List.length_append,w4_M5QueryBridge.length_frame]; omega

def bounds (L : ℕ → ℕ) := ∀ (w p : Wd), p.length ≤ 4*w.length →
  (pair w []).length ≤ L w.length ∧ (pair (pair w p) (req w p)).length ≤ L w.length ∧
  (pair (pair w p) (reply w p)).length ≤ L w.length ∧ (reply w p).length ≤ L w.length ∧
  (readout w p).length ≤ L w.length

theorem sizeBudget : ∃ L : ℕ → ℕ, PB L ∧ bounds L := by
  have H : PolyT (fun z : Wd × Wd => pair (pair z.1 z.2) (req z.1 z.2)) := by
    unfold req; apply pair_poly (pair_poly (Groundwork.PolyT.fst (f:=fun p : Wd × Wd => p) Groundwork.PolyT.id') (Groundwork.PolyT.snd (f:=fun p : Wd × Wd => p) Groundwork.PolyT.id'))
    apply inst_poly (Groundwork.PolyT.fst (f:=fun p : Wd × Wd => p) Groundwork.PolyT.id') (Groundwork.PolyT.append (Groundwork.PolyT.snd (f:=fun p : Wd × Wd => p) Groundwork.PolyT.id') (const [false]))
  have R : PolyT (fun z : Wd × Wd => readout z.1 z.2) := by unfold readout; apply w5_M6Sort.cw_poly; apply Groundwork.PolyT.ofBits; exact Groundwork.PolyT.take (Groundwork.PolyT.length (Groundwork.PolyT.fst (f:=fun z : Wd × Wd => z) Groundwork.PolyT.id')) (Groundwork.PolyT.snd (f:=fun z : Wd × Wd => z) Groundwork.PolyT.id')
  obtain ⟨_,j,_,hj⟩ := H
  obtain ⟨_,k,_,hk⟩ := R
  let s := fun n : ℕ => 32*(n+1)
  let L := fun n => P j (s n) + P k (s n) + s n
  have hs : PB s := (PB.const 32).mul (PB.id'.add (PB.const 1))
  refine ⟨L,((Ppb j hs).add (Ppb k hs)).add hs,?_⟩
  intro w p hp
  have hl : len (w,p) ≤ s w.length := by simp [len_pair,len_bools,s]; omega
  have hj' := hj (w,p); have hk' := hk (w,p)
  simp only [len_bools,Prod.fst,Prod.snd] at hj' hk'
  have h1 := Nat.mul_le_mul_left j (Nat.pow_le_pow_left (Nat.add_le_add_right hl 1) j)
  have h2 := Nat.mul_le_mul_left k (Nat.pow_le_pow_left (Nat.add_le_add_right hl 1) k)
  have hb := replyBound w p
  dsimp only [L,P]
  have hs' : s w.length = 32*(w.length+1) := rfl
  simp only [length_pair,List.length_nil] at hj' ⊢
  omega

end DetDLP.S6BBudget


