-- Prove2me | Definitions.Def_DetDLP_S8H4_ElemDecoder
-- name    : DetDLP_S8H4_ElemDecoder
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T07:02:30.570224+00:00
-- url     : https://prove2.me/theorems/2e519bf7-d75b-41d7-a5e5-edcaada30fd6
-- title:
--   Decoding the public parameters of an elliptic factor-block element query
-- statement:
--   A Tag 4 query supplies the curve coefficients, threshold, packed affine seeds, block index, and point prefix. Reading the fixed-width seed field at coordinate $4i+k$ recovers the $k$-th coefficient of block $i$. The decoder is total on arbitrary input words and runs in polynomial time.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8A_FpPrefixStep
import Definitions.Def_DetDLP_S8M_ECPairPacket

set_option autoImplicit false
namespace DetDLP.S8H4.ElemDecoder
open M89S1 Groundwork DetDLP_W1_Queries m89_enum_words
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
abbrev W := List Bool

def word {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (T : ℕ)
    (S : ECSeed p m) (i : Fin m) (η : W) := queryWord 4 (encodeCurveInput p E)
    [countWord T,List.ofFn (ecBits S),countWord i.val,η]

abbrev prime := S8M.ECPair.Packet.prime
abbrev threshold := S8M.ECPair.Packet.threshold
abbrev seed := S8M.ECPair.Packet.seed
abbrev pfx := S8M.ECPair.Packet.prefixBits
def index (w : W) := PolyT.bval (third (more (more w)))
def coeffs (w : W) := w5_M6Sort.decode (second w)
def coeff (w : W) (k : ℕ) := (coeffs w).getD k 0
def width (w : W) := S8G.FpMoment.Code.width (prime w)
def seedEntry (w : W) (k : ℕ) := coord (seed w) (width w) (index w*4+k)

attribute [local fun_prop] PolyT.const PolyT.comp PolyT.prodMk PolyT.fst PolyT.snd PolyT.id' PolyT.mul
  S8M.ECPair.Packet.prime_poly S8M.ECPair.Packet.seed_poly S8G.FpMoment.Code.width_poly
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f more_poly first_poly w5_M6Sort.decode_poly co_poly

@[local fun_prop] theorem index_poly : PolyT index := by unfold index third second; fun_prop
@[local fun_prop] theorem coeffs_poly : PolyT coeffs := by unfold coeffs second; fun_prop
theorem coeff_poly : PolyT fun z : W × ℕ => coeff z.1 z.2 := by unfold coeff; fun_prop
@[local fun_prop] theorem width_poly : PolyT width := by unfold width prime; fun_prop
theorem seedEntry_poly : PolyT fun z : W × ℕ => seedEntry z.1 z.2 := by unfold seedEntry seed; fun_prop

variable {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (T : ℕ) (S : ECSeed p m) (i : Fin m) (η : W)

theorem fields : let w := word E T S i η
    prime w = p ∧ threshold w = T ∧ seed w = List.ofFn (ecBits S) ∧ index w = i.val ∧ pfx w = η ∧
    coeffs w = [p,E.a₁.val,E.a₂.val,E.a₃.val,E.a₄.val,E.a₆.val] := by
  simp [prime,threshold,seed,pfx,index,coeffs,word,S8M.ECPair.Packet.prime,S8M.ECPair.Packet.threshold,
    S8M.ECPair.Packet.seed,S8M.ECPair.Packet.prefixBits,second,third,queryWord,encodeCurveInput,encodeNatListBin]

  exact w5_M6Sort.decode_encode _
private theorem little (b x : ℕ) (h : x < 2^b) :
    PolyT.bval (List.ofFn fun j : Fin b => x.testBit j.val) = x := by
  induction b generalizing x with
  | zero =>
    obtain rfl : x=0 := by simpa using h
    rfl
  | succ b ih =>
    rw [List.ofFn_succ,PolyT.bval_cons]
    simp only [Fin.val_zero,Fin.val_succ,Nat.testBit_succ]
    rw [ih (x/2) ((Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa [pow_succ] using h)),Nat.testBit_zero]
    by_cases h : x%2=1 <;> simp [h] <;> omega

theorem packedSlice {m t b : ℕ} (f : Fin m → Fin t → ℕ) (i : Fin m) (k : Fin t) :
    (((List.ofFn (packBits (b:=b) f)).drop ((i.val*t+k.val)*b)).take b) = digitWord b (f i k) := by
  let u := finProdFinEquiv (i,k)
  have hu : u.val = i.val*t+k.val := by change k.val+t*i.val=_; ring
  have hb : (u.val+1)*b ≤ m*t*b := Nat.mul_le_mul_right _ u.isLt
  rw [Nat.add_mul,one_mul] at hb
  rw [← hu]; apply List.ext_getElem
  · simp [digitWord]; omega
  · intro j _ h; have hj : j < b := by simpa [digitWord] using h
    simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn,digitWord]
    let v : Fin b := ⟨j,hj⟩
    have hv : (finProdFinEquiv (u,v)).val = u.val*b+j := by change j+b*u.val=_; ring
    have eq : (⟨u.val*b+j,by omega⟩ : Fin (m*t*b)) = finProdFinEquiv (u,v) := Fin.ext hv.symm
    change packBits f (⟨u.val*b+j,_⟩ : Fin (m*t*b)) = (f i k).testBit v.rev.val
    rw [eq]
    simp only [packBits,Equiv.symm_apply_apply]
    simp only [u,Equiv.symm_apply_apply]

theorem seedEntry_eq (k : Fin 4) : seedEntry (word E T S i η) k.val = ecWords S i k := by
  obtain ⟨hp,_,hs,hi,_,_⟩ := fields E T S i η
  simp only [seedEntry,width,hp,S8G.FpMoment.Code.width_eq,hs,hi,coord,ecBits,packedSlice]
  have hlt : ecWords S i k < p := by
    unfold ecWords; dsimp only; split
    · have := (S i (decide (2 ≤ k.val))).1.isLt; omega
    · exact (S i _).2.isLt
  apply Eq.trans _ (little (bitLen p) _ (hlt.trans_le (Nat.le_pow_clog (by decide) p)))
  apply congrArg PolyT.bval
  apply List.ext_getElem (by simp [digitWord]); intro j hj hk
  simp only [digitWord,List.getElem_reverse,List.getElem_ofFn,List.length_ofFn,Fin.val_rev]
  congr 1; simp only [List.length_ofFn] at hk; omega

end DetDLP.S8H4.ElemDecoder


