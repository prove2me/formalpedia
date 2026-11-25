-- Prove2me | Definitions.Def_DetDLP_W3C_NewtonPoly
-- name    : DetDLP_W3C_NewtonPoly
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:38:46.286194+00:00
-- url     : https://prove2.me/theorems/6fd37a9a-f645-4510-b6b3-fa45b61caa1c
-- title:
--   PolyT Newton mass readout and coset-row codecs for Stage II
-- statement:
--   The shared Stage II controller reads a coefficient packet of length $L=d_{\mathrm{filt}}(2m)+1$. The decoder bounds every range in the Newton difference by the number of entries actually read, so `massPosWord` is polynomial-time even on malformed packets. On a valid contraction packet its Boolean result is exactly $[0<\mathrm{mass}(q)]$. The test uses truncated quotients to detect divisibility by $2^{\mathrm{prec}}$ without allocating the modulus. The module also proves that `largeCheck` decides the large-instance predicate, that `updateWord` realizes the canonical HNF coset-update encoding, and that `repLabels` reads the representative coordinates from a coset packet.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_PrefixDescent
import Definitions.Def_DetDLP_S8G_FpMomentPoly
import Definitions.Def_ToTuring_Lib_Int
import Theorems.Thm_Groundwork_PolyT_len_mul_le

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DetDLP.W3C.NewtonPoly
open Groundwork S8G.FpMoment.Code
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const
  PolyT.map PolyT.mul PolyT.sum PolyT.length PolyT.div PolyT.div_pow PolyT.mod PolyT.pow_const
  P2M_Groundwork_PolyT_ite__226169acf219 PolyT.decide_and PolyT.decide_lt PolyT.decide_le
  width_poly slots_poly w5_M6Sort.decode_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f
variable {α : Type} [Enc α]

/-- The large-instance test shared by the finite-field and elliptic-curve controllers. -/
def largeCheck (p M : ℕ) := decide (67 < p ∧ 64 ≤ M ∧ 4096 * slots (width p) ≤ M - 1)
@[fun_prop] theorem largeCheck_poly {p M : α → ℕ} (hp : PolyT p) (hM : PolyT M) :
    PolyT fun x => largeCheck (p x) (M x) := by unfold largeCheck; fun_prop
theorem largeCheck_correct (p M : ℕ) : largeCheck p M = true ↔ w3_large p M := by
  simp [largeCheck, w3_large, slots_eq, width_eq]

@[local fun_prop] private theorem prodP {f : α → List ℕ} (hf : PolyT f) : PolyT fun x => (f x).prod := by
  obtain ⟨_,t,ht,_,_,hlen⟩ := hf.elim
  simp only [List.prod_eq_foldl]
  exact PolyT.foldl_add (g := fun _ a b => a*b) hf (by fun_prop) (by fun_prop)
    ⟨t,ht,fun x a b hb => (PolyT.len_mul_le a b).trans (Nat.add_le_add_left ((len_le_of_mem hb).trans (hlen x)) (len a))⟩
private theorem sum_split (l : List ℤ) : l.sum = ((l.map Int.toNat).sum : ℤ) - ((l.map fun z => (-z).toNat).sum : ℕ) := by
  induction l with | nil => simp | cons a l ih => simp only [List.map_cons,List.sum_cons,Nat.cast_add,ih]; omega
@[local fun_prop] private theorem sumP {f : α → List ℤ} (hf : PolyT f) : PolyT fun x => (f x).sum := by
  simp only [sum_split]; fun_prop

private def fac (r : List ℕ) (k : ℕ) := ((r.take k).map (· + 1)).prod
private def bin (r : List ℕ) (j t : ℕ) := fac r j / (fac r t * fac r (j-t))
private def square (s M k t : ℕ) := ((t : ℤ) - (1 + (-(s:ℤ) + k)*M)).natAbs ^ 2
private def sign (a : ℕ) : ℤ := if a % 2 = 0 then 1 else -1
private def coeff (r : List ℕ) (s M j : ℕ) : ℤ := ((r.take (j+1)).map fun t =>
  sign (j-t) * (bin r j t : ℤ) * (((r.take (2*s+1)).map fun k => square s M k t).prod : ℕ)).sum
private def scalar (m M : ℕ) (c : List ℕ) :=
  let r := List.range c.length
  (r.map fun j => coeff r (2*m) M j * (c.getD j 0 : ℤ)).sum

@[local fun_prop] private theorem rangeP {f : α → List ℕ} (hf : PolyT f) :
    PolyT fun x => List.range (f x).length := PolyT.range (Unary.of_length hf)
@[local fun_prop] private theorem facP {r : α → List ℕ} {k : α → ℕ} (hr : PolyT r) (hk : PolyT k) :
    PolyT fun x => fac (r x) (k x) := by unfold fac; fun_prop
@[local fun_prop] private theorem binP {r : α → List ℕ} {j t : α → ℕ} (hr : PolyT r) (hj : PolyT j) (ht : PolyT t) :
    PolyT fun x => bin (r x) (j x) (t x) := by unfold bin; fun_prop
@[local fun_prop] private theorem coeffP {r : α → List ℕ} {s M j : α → ℕ}
    (hr : PolyT r) (hs : PolyT s) (hM : PolyT M) (hj : PolyT j) :
    PolyT fun x => coeff (r x) (s x) (M x) (j x) := by unfold coeff sign square; fun_prop
@[local fun_prop] private theorem scalarP {m M : α → ℕ} {c : α → List ℕ} (hm : PolyT m) (hM : PolyT M) (hc : PolyT c) :
    PolyT fun x => scalar (m x) (M x) (c x) := by unfold scalar; fun_prop

/-- Testing divisibility by a power of two via two truncated quotients avoids allocating the modulus. -/
private def nz (z : ℤ) (prec : ℕ) := let a := z.natAbs
  decide (0 < a ∧ a / 2^prec = (a-1) / 2^prec)
private theorem nz_eq (z : ℤ) (p : ℕ) : nz z p = decide (0 < z % (2:ℤ)^p) := by
  have hh : (2^p : ℕ) ∣ z.natAbs ↔ (2^p : ℤ) ∣ z := by simpa using (Int.natAbs_dvd_natAbs (a := (2:ℤ)^p) (b := z))
  have hn := Int.emod_nonneg z (show (2:ℤ)^p ≠ 0 by positivity)
  rw [Int.dvd_iff_emod_eq_zero] at hh
  dsimp only [nz]; apply decide_eq_decide.mpr
  cases h : z.natAbs with
  | zero => simp [h] at hh ⊢; omega
  | succ a => rw [h] at hh; simp only [Nat.succ_sub_one,Nat.zero_lt_succ,true_and]; rw [Nat.succ_div]; split <;> simp_all <;> omega

/-- On valid packets every required range fits within the decoded coefficient count. -/
def massPosWord (m M prec : ℕ) (w : List Bool) : Bool := nz (scalar m M (w5_M6Sort.decode w)) prec
@[fun_prop] theorem massPosWord_poly {m M p : α → ℕ} {w : α → List Bool}
    (hm : PolyT m) (hM : PolyT M) (hp : PolyT p) (hw : PolyT w) :
    PolyT fun x => massPosWord (m x) (M x) (p x) (w x) := by unfold massPosWord nz; fun_prop

private theorem fac_eq (l k : ℕ) (hk : k ≤ l) : fac (List.range l) k = k.factorial := by
  rw [fac,List.take_range,Nat.min_eq_left hk,← Finset.prod_range_add_one_eq_factorial,← List.toFinset_range k,List.prod_toFinset _ List.nodup_range]
private theorem coeff_eq (l s M j : ℕ) (hj : j < l) (hs : 2*s+1 ≤ l) :
    coeff (List.range l) s M j = w3c_coeff s M j := by
  simp only [coeff,List.take_range,Nat.min_eq_left (show j+1 ≤ l by omega),Nat.min_eq_left hs,w3c_coeff,
    ← List.toFinset_range,List.sum_toFinset _ List.nodup_range,List.prod_toFinset _ List.nodup_range]
  apply congrArg List.sum; apply List.map_congr_left; intro t ht
  have htj : t ≤ j := by simpa using List.mem_range.mp ht
  have hb : bin (List.range l) j t = j.choose t := by
    rw [bin,fac_eq _ _ (by omega),fac_eq _ _ (by omega),fac_eq _ _ (by omega),Nat.choose_eq_factorial_div_factorial htj]
  simp only [hb,sign,neg_one_pow_eq_ite,Nat.even_iff,Nat.cast_list_prod,List.map_map]
  congr 2; apply List.map_congr_left; intro k _
  simp [square, sq_abs]

theorem massPosWord_correct {q : w3_Query} {C : ℕ} (n : w3_Net q C) {w : List Bool}
    (hw : EncodesTruncPoly (w3_precision q) (w3_len q) w (BTNContract n.G n.T)) :
    massPosWord q.m q.M (w3_precision q) w = decide (0 < w3_mass q) := by
  rw [← w3c_readout_correct n hw,massPosWord,nz_eq]
  have hl : (w5_M6Sort.decode w).length = w3_len q := by
    obtain ⟨c,_,rfl,_⟩ := hw; simp [w5_M6Sort.decode_encode]
  let F := fun j : ℕ => w3c_coeff (2*q.m) q.M j * ((w5_M6Sort.decode w).getD j 0 : ℤ)
  change decide (0 < scalar q.m q.M _ % _) = decide (0 < (∑ j : Fin (w3_len q), F j) % _)
  rw [Fin.sum_univ_eq_sum_range F, ← List.toFinset_range, List.sum_toFinset _ List.nodup_range]
  simp only [scalar,hl,F]; congr 4; apply List.map_congr_left; intro j hj; rw [coeff_eq _ _ _ _ (List.mem_range.mp hj) (by unfold w3_len dFilt; omega)]

open DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] frame_poly first_poly w5_M6Sort.cw_poly w5_M6Sort.encode_poly P2M_Groundwork_PolyT_cons__3a60f43a3b86
private def field (w tail : List Bool) := true :: (DetDLP_W1_Queries.frame w ++ tail)
@[local fun_prop] private theorem fieldP {w t : α → List Bool} (hw : PolyT w) (ht : PolyT t) :
    PolyT fun x => field (w x) (t x) := by unfold field; fun_prop

/-- Reuse the HNF packet verbatim and append the new congruence in canonical row order. -/
def updateWord (M N : ℕ) (rep : List Bool) (row : List ℕ) (rhs : ℕ) : List Bool :=
  field (countWord M) (field (countWord N) (field rep (field (encodeNatListBin row) (field (countWord rhs) [false]))))
@[fun_prop] theorem updateWord_poly {M N rhs : α → ℕ} {rep : α → List Bool} {row : α → List ℕ}
    (hm : PolyT M) (hn : PolyT N) (hr : PolyT rep) (ha : PolyT row) (hb : PolyT rhs) :
    PolyT fun x => updateWord (M x) (N x) (rep x) (row x) (rhs x) := by
  unfold updateWord; fun_prop
theorem updateWord_correct (M : ℕ) {N : ℕ} (x a : Fin N → ℕ) (B : Matrix (Fin N) (Fin N) ℤ) (rhs : ℕ) :
    updateWord M N (encodeCosetRep x B) (List.ofFn a) rhs = encodeCosetUpdateInput M x B a rhs := by
  simp [updateWord,field,frame_correct,encodeCosetUpdateInput,Encoding.encodeList]

/-- Read the label vector from the returned affine-coset packet. -/
def repLabels (rep : List Bool) := w5_M6Sort.decode (first rep)
@[fun_prop] theorem repLabels_poly {r : α → List Bool} (hr : PolyT r) : PolyT fun x => repLabels (r x) := by
  unfold repLabels; fun_prop
theorem repLabels_correct {N : ℕ} (x : Fin N → ℕ) (B : Matrix (Fin N) (Fin N) ℤ) :
    repLabels (encodeCosetRep x B) = List.ofFn x := by
  simp [repLabels,encodeCosetRep,first_cons,w5_M6Sort.decode_encode]

end DetDLP.W3C.NewtonPoly


