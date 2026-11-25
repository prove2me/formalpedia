-- Prove2me | Definitions.Def_DetDLP_S8C3_Layout
-- name    : DetDLP_S8C3_Layout
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:56:58.718821+00:00
-- url     : https://prove2.me/theorems/ca3cc14b-9084-4bc9-b2d1-93f74ba9689e
-- title:
--   Expanded prime-field element certificates and query bounds
-- statement:
--   For a Tag 3 prefix query, nonzero scan, threshold subtraction and hash-column witnesses lift each valid element uniquely. Their projection is an equivalence with the filtered factor block. The query encoding fits the linear block budget and the uniform polynomial budget.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8G_FpMomentPoly
import Definitions.Def_DetDLP_S8J_CircuitRealizes
import Definitions.Def_DetDLP_S8C_FpQueryCount

set_option autoImplicit false
namespace DetDLP.S8C3
open M89S1 S8C S8J S8G.FpMoment
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

abbrev W := List Bool

def word {p m : ℕ} (T : ℕ) (S : FpSeed p m) (i : Fin m) (η : W) :=
  queryWord 3 (countWord p) [countWord T, List.ofFn (fpBits S), countWord i.val, η]

theorem wordBudget {p T : ℕ} [Fact p.Prime] (S : FpSeed p (blockCount (bitLen p)))
    (i : Fin (blockCount (bitLen p))) (η : W) (hT : T ≤ p) (hη : η.length ≤ bitLen p) :
    let b := bitLen p; let m := blockCount b
    scale m b + (word T S i η).length ≤ 200000*m*b ∧
    scale m b + (word T S i η).length ≤ 200000*(b+1)^200000 := by
  dsimp only
  let b := bitLen p
  let m := blockCount b
  have hm : 2 ≤ m := le_max_left ..
  have hb : 1 ≤ b := Nat.clog_pos (by decide) (Fact.out : p.Prime).one_lt
  have h1 : (countWord p).length ≤ b+1 := binaryLen (le_refl p)
  have h2 : (countWord T).length ≤ b+1 := binaryLen hT
  have h3 := w3_queryIndexLength i.val
  have hi : i.val < m := i.isLt
  have hmb : b ≤ m*b := Nat.le_mul_of_pos_left _ (by omega)
  have hmb' : m ≤ m*b := Nat.le_mul_of_pos_right _ hb
  have ht : (countWord 3).length = 2 := by decide
  have hw : (word T S i η).length ≤ 64*(m*b) := by
    simp only [word,queryWord,Encoding.encodeList,id_eq,List.length_cons,List.length_append,
      w3_frameLength,List.length_nil,ht,List.length_ofFn]
    change η.length ≤ b at hη
    change  _ ≤ 64*(m*b)
    rw [show blockCount (bitLen p)*2*bitLen p = 2*(m*b) by change m*2*b = 2*(m*b); ring]
    omega
  have hs : scale m b ≤ 196608*m*b := by
    calc _ ≤ 65536*m*(3*b) := Nat.mul_le_mul_left _ (by omega)
         _ = _ := by ring
  have hf : scale m b + (word T S i η).length ≤ 200000*m*b := by nlinarith
  refine ⟨hf,hf.trans ?_⟩
  rw [Nat.mul_assoc]; apply Nat.mul_le_mul_left
  calc m*b ≤ (b+2)*b := Nat.mul_le_mul_right _ (blockUpper b)
       _ ≤ (b+1)^2 := by nlinarith
       _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)

abbrev Aux (p : ℕ) := w3_slotHashAux (atomWidth p) × w3_slotDiff (atomWidth p) × (Fin (atomWidth p) → Bool)

def checked {p m : ℕ} [Fact p.Prime] (T : ℕ) (S : FpSeed p m) (i : Fin m) (η : W)
    (u : (ZMod p)ˣ) (r : AtomRun p) (c : Aux p) : Prop :=
  let x := (w3_fpResidue u).val
  let d := atomWidth p
  w3_slotHashBits (Nat.succ_pos (bitLen p)) ((S i).1.val+1) (S i).2.val x r.1.val r.2 c.1 ∧
    (w3_slotLt d r.1.val T c.2.1 ∧ w3_slotOr d x false c.2.2) ∧ (elemWord u).take η.length = η

theorem checked_lift {p m : ℕ} [Fact p.Prime] {T : ℕ} (hT : T ≤ p) (S : FpSeed p m)
    (i : Fin m) (η : W) (u : (ZMod p)ˣ) (r : AtomRun p) :
    w3_slotLift (elemOK S i T η u r) (checked T S i η u r) := by
  let x := (w3_fpResidue u).val
  have hx : x < 2^atomWidth p := (w3_fpResidue u).isLt.trans (primeFitsAtom p)
  have H := w3_slotHash_spec (a := (S i).1.val+1) (x := x) (Nat.succ_pos (bitLen p))
    (primeFitsAtom p) (S i).2.isLt r.1.isLt r.2
  have L := w3_slotLt_spec (r.1.isLt.trans (primeFitsAtom p)) (hT.trans (primeFitsAtom p).le)
  have O := w3_slotOr_spec false hx
  have J := w3_slotLiftProd H (w3_slotLiftProd L O)
  constructor
  · rintro c ⟨hh,hl,hη⟩
    obtain ⟨hc,ht,hx'⟩ := J.1 c ⟨hh,hl⟩
    exact ⟨⟨hx'.resolve_left (by decide),ht,hc⟩,hη⟩
  · rintro ⟨⟨hx',ht,hc⟩,hη⟩
    obtain ⟨c,hc',uc⟩ := J.2 ⟨hc,ht,Or.inr hx'⟩
    exact ⟨c,⟨hc'.1,hc'.2,hη⟩,fun v hv => uc _ ⟨hv.1,hv.2.1⟩⟩

noncomputable def checkedEquiv {p m : ℕ} [Fact p.Prime] {T : ℕ} (hT : T ≤ p)
    (mul : w3_modMulInterface) (S : FpSeed p m) (i : Fin m) (η : W) :
    {v : (ZMod p)ˣ × (AtomRun p × Aux p) // checked T S i η v.1 v.2.1 v.2.2} ≃ ↥(elemSet S i T η) := by
  apply certEquiv (elemSet S i T η) (fun u (rc : AtomRun p × Aux p) => checked T S i η u rc.1 rc.2)
  · rintro u ⟨r,c⟩ hc
    obtain ⟨ha,hη⟩ := (checked_lift hT S i η u r).1 c hc
    exact Finset.mem_filter.mpr ⟨atom_sound mul S i T u r ha,hη⟩
  · intro u hu
    obtain ⟨hm,hη⟩ := Finset.mem_filter.mp hu
    obtain ⟨r,hr,ur⟩ := (atom_mem_iff mul S i T u).mpr hm
    obtain ⟨c,hc,uc⟩ := (checked_lift hT S i η u r).2 ⟨hr,hη⟩
    refine ⟨(r,c),hc,?_⟩
    rintro ⟨r',c'⟩ hc'
    obtain rfl : r' = r := ur _ ((checked_lift hT S i η u r').1 c' hc').1
    exact Prod.ext rfl (uc _ hc')

theorem tagIntro (make port : W → W) (L : ℕ) (hm : Groundwork.PolyT make) (he : Groundwork.PolyT port)
    (h : ∀ (p : ℕ) [Fact p.Prime] (T : ℕ) (S : FpSeed p (blockCount (bitLen p)))
      (i : Fin (blockCount (bitLen p))) (η : W), T ≤ p → η.length ≤ bitLen p →
      Realizes make port L (word T S i η) (bitLen p) (elemCount (fpFactorBlock T S i) elemWord η)) :
    TagSpec [3] := by
  refine ⟨make,port,L,hm,he,?_⟩
  rintro t ht base payload b n hq
  obtain rfl : t = 3 := by simpa using ht
  generalize hw : queryWord 3 base payload = w at hq ⊢
  have tag : Groundwork.PolyT.bval (DetDLP_W1_Queries.first w) = 3 := by subst w; simp [queryWord]
  cases hq <;> simp only [queryWord,DetDLP_W1_Queries.first_cons,id_eq,DetDLP_W1_Queries.decode_count] at tag
  all_goals first | contradiction | exact h _ _ _ _ _ (by assumption) (by assumption)

end DetDLP.S8C3


