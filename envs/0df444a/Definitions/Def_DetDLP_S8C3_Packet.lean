-- Prove2me | Definitions.Def_DetDLP_S8C3_Packet
-- name    : DetDLP_S8C3_Packet
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T07:05:05.743808+00:00
-- url     : https://prove2.me/theorems/1b74f2bc-63e8-48fe-98ee-95851abac21c
-- title:
--   Prime-field element query decoder and arithmetic tile
-- statement:
--   The decoder reads the selected affine hash coefficients from a Tag 3 query word in polynomial time. The joined hash and subtraction tile has linear incidence count and polynomial-time addresses; on encoded run assignments the tests agree with the hash and strict threshold predicates.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8C3_Layout
import Definitions.Def_DetDLP_S8H_PointAddresses

set_option autoImplicit false
namespace DetDLP.S8C3.Packet
open M89S1 Groundwork DetDLP_W1_Queries S8C S8H w4_M5Network
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace


abbrev prime := S8G.FpMoment.Code.prime
abbrev threshold := S8G.FpMoment.Code.idx
abbrev seed (w : W) := third (more w)
abbrev index (w : W) := PolyT.bval (third (more (more w)))
abbrev pfx (w : W) := third (more (more (more w)))

def coeff (w : W) (k : ℕ) :=
  let b := S8G.FpMoment.Code.width (prime w)
  PolyT.bval (((seed w).drop ((2*index w+k)*b) |>.take b).reverse)

attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const
  first_poly more_poly PolyT.length PolyT.mul S8G.FpMoment.Code.width_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f

@[local fun_prop] theorem coeff_poly (k : ℕ) : PolyT fun w => coeff w k := by
  unfold coeff prime S8G.FpMoment.Code.prime index seed third second; fun_prop

variable {p m : ℕ} (T : ℕ) (S : FpSeed p m) (i : Fin m) (η : W)

@[simp] theorem fields : let w := word T S i η
    prime w = p ∧ threshold w = T ∧ seed w = List.ofFn (fpBits S) ∧ index w = i.val ∧ pfx w = η := by
  simp [prime,S8G.FpMoment.Code.prime,threshold,S8G.FpMoment.Code.idx,seed,index,pfx,word,queryWord,second,third]

private theorem readBits (b n : ℕ) (hn : n < 2^b) : PolyT.bval (List.ofFn fun i : Fin b => n.testBit i.val) = n := by
  induction b generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    subst n; rfl
  | succ b ih =>
    rw [List.ofFn_succ,PolyT.bval_cons]
    simp only [Fin.val_zero,Fin.val_succ,Nat.testBit_succ]
    rw [ih (n/2) ((Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa [pow_succ] using hn)),Nat.testBit_zero]
    by_cases h : n%2=1 <;> simp [h] <;> omega

private theorem readDigit (b n : ℕ) (hn : n < 2^b) : PolyT.bval (digitWord b n).reverse = n := by
  apply Eq.trans _ (readBits b n hn); apply congrArg PolyT.bval
  apply List.ext_getElem (by simp [digitWord]); intro j hj hk
  simp only [digitWord,List.getElem_reverse,List.getElem_ofFn,List.length_ofFn,Fin.val_rev]
  congr 1; simp only [List.length_ofFn] at hk; omega

theorem coeff_word (k : Fin 2) : coeff (word T S i η) k.val = fpWords S i k := by
  let b := bitLen p
  have bound : fpWords S i k < 2^b := by
    unfold fpWords; split
    · have h := (S i).1.isLt; have hh : p ≤ 2^b := Nat.le_pow_clog (by decide) p; omega
    · exact (S i).2.isLt.trans_le (Nat.le_pow_clog (by decide) p)
  have hslice : ((List.ofFn (fpBits S)).drop ((2*i.val+k.val)*b)).take b = digitWord b (fpWords S i k) := by
    have reach := Nat.mul_le_mul_right b (show 2*i.val+k.val+1 ≤ m*2 by have := i.isLt; have := k.isLt; omega)
    rw [Nat.add_mul,Nat.one_mul] at reach
    apply List.ext_getElem (by simp only [digitWord,List.length_take,List.length_drop,List.length_ofFn]; change min b (m*2*b-(2*i.val+k.val)*b)=b; omega)
    intro j hj hk
    have jb : j < b := by simpa [digitWord] using hk
    let ix := finProdFinEquiv (finProdFinEquiv (i,k), (⟨j,jb⟩ : Fin b))
    have idx : ix.val = (2*i.val+k.val)*b+j := by simp [ix,finProdFinEquiv_apply_val]; ring
    rw [List.getElem_take,List.getElem_drop,List.getElem_ofFn]; change packBits (b:=b) (fpWords S) _ = _
    have eq : (⟨(2*i.val+k.val)*b+j,by omega⟩ : Fin (m*2*b)) = ix := Fin.ext idx.symm
    rw [eq]; simp [ix,packBits,digitWord]
  obtain ⟨hp,_,hs,hi,_⟩ := fields T S i η
  simp only [coeff,hp,hs,hi,S8G.FpMoment.Code.width_eq]; exact (congrArg (fun l : W => PolyT.bval l.reverse) hslice).trans (readDigit b _ bound)

theorem make_word (a : S8G.FpMoment.Code.Addresses) (G : WireGraph)
    (hv : a.nv (word T S i η) = G.nV) (he : a.ne (word T S i η) = G.nE)
    (hs : ∀ j : Fin G.nE, a.src (word T S i η) j.val = (G.endpoints j).1.val)
    (hd : ∀ j : Fin G.nE, a.dst (word T S i η) j.val = (G.endpoints j).2.val) :
    let w := word T S i η; let s := S8G.FpMoment.scale (blockCount (bitLen p)) (bitLen p)
    S8G.FpMoment.Code.make a w = encodeBTNInstance w G.subdivision s s 1 := by
  dsimp only
  have hp : S8G.FpMoment.Code.prime (word T S i η) = p := (fields T S i η).1
  rw [S8G.FpMoment.Code.make,hv,he,WirePacket.packet_eq G _ _ hs hd,S8G.FpMoment.Code.sizeField,hp,S8G.FpMoment.Code.width_eq,S8G.FpMoment.Code.slots_eq,outerPacket_eq]

open S8J S8H.PointAddresses

/-- The hash columns and the subtraction columns share the same width parameter. -/
def tile {d : ℕ} (hd : 1 ≤ d) := join (HashGateLayout.layout d hd) (AddLayout.layout (d+1))

def tileCode (d : ℕ) := PointAddresses.sum (PointAddresses.hash d) (PointAddresses.add (d+1))

theorem tile_spec {d : ℕ} (hd : 1 ≤ d) : Models (tileCode d) (tile hd) :=
  sum_spec (hash_spec hd) (add_spec _)

theorem tile_poly : Uniform tileCode := sum_poly hash_poly (add_poly _ (by intros; fun_prop))

theorem tile_edges {d : ℕ} (hd : 1 ≤ d) : (tile hd).ne < 5010*(d+2) := by
  change (HashGateLayout.layout d hd).ne + (d+1)*5 < _
  have := HashGateLayout.edges hd; omega

noncomputable def tileTest {d p : ℕ} (hd : 1 ≤ d) (a x : ℕ) (r : w3_fpHashCert d p hd) : w3_factorTest (tile hd) :=
  joinTest (HashGateLayout.tests hd a x r) (AddLayout.test true)

def tileBits {d p : ℕ} (hd : 1 ≤ d) (b z t : ℕ) (r : w3_fpHashCert d p hd) (h : w3_slotHashAux d) (l : w3_slotDiff d) : Fin (tile hd).nb → Bool :=
  Fin.append (HashGateLayout.encode hd b z r h) (HashGateLayout.addBits z l.1.val t l.2)

theorem tile_iff {d p : ℕ} (hd : 1 ≤ d) (a b x z t : ℕ) (r : w3_fpHashCert d p hd) (h : w3_slotHashAux d) (l : w3_slotDiff d) :
    Accept _ (tileTest hd a x r) (tileBits hd b z t r h l) ↔ w3_slotHashBits hd a b x z r h ∧ w3_slotLt d z t l :=
  (HashGateLayout.joined _ _ _ _).trans <| and_congr (HashGateLayout.encode_iff ..) (CircuitRealizes.lessBlock_iff ..)

end DetDLP.S8C3.Packet


