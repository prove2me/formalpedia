-- Prove2me | Definitions.Def_DetDLP_S8L_PairOrder
-- name    : DetDLP_S8L_PairOrder
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:49:10.082552+00:00
-- url     : https://prove2.me/theorems/0d831ae1-b85d-4739-baca-0efaf2dcd91b
-- title:
--   Tag 5 factor order and prefix digits
-- statement:
--   The family-first factor array and the two indexed families are equivalent. Its partial product equals the tuple product, while the alternating most-significant-first digit sequence is exactly the encoded tuple word.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8L_ChainLift

set_option autoImplicit false
namespace DetDLP.S8L.PairOrder
open S8H0.ResidueWires RowSound S8C M89S1 AtomLift
variable {p m : ℕ} [Fact p.Prime]
abbrev Factors (p m : ℕ) := Fin (2*m) → (ZMod p)ˣ
abbrev l (i : Fin m) : Fin (2*m) := ⟨i,by omega⟩
abbrev r (i : Fin m) : Fin (2*m) := ⟨m+i,by omega⟩
def pair : Factors p m ≃ UnitPair p m where
  toFun f := (fun i => f (l i),fun i => f (r i))
  invFun ab j := if h : j.val < m then ab.1 ⟨j,h⟩ else ab.2 ⟨j-m,by have := j.isLt; omega⟩
  left_inv f := by funext j; dsimp only; split <;> congr 1 <;> apply Fin.ext <;> dsimp [l,r] <;> omega
  right_inv ab := Prod.ext (funext fun i => by simp [i.isLt]) (funext fun i => by simp)

def seq (f : Factors p m) (j : ℕ) : ZMod p := if h : j < 2*m then (f ⟨j,h⟩ : ZMod p) else 1

theorem prod_eq (f : Factors p m) (hm : 1 ≤ m) :
    ChainLift.partialProd (seq f) (2*m-1) = ((∏ i, (pair f).1 i * (pair f).2 i : (ZMod p)ˣ) : ZMod p) := by
  rw [ChainLift.partialProd,show 2*m-1+1=m+m by omega,← Fin.prod_univ_eq_prod_range,Fin.prod_univ_add]
  simp [seq,pair,l,r,Finset.prod_mul_distrib,Units.coe_prod,Nat.add_comm m,show ∀ j : Fin m, j.val+m < 2*m by intro j; omega,
    show ∀ j : Fin m, j.val < 2*m by intro j; omega]

def atDigit (f : Factors p m) (b k : ℕ) :=
  if h : k/b/2 < m then ((f ⟨k/b/2+(if k/b%2=0 then 0 else m),by split <;> omega⟩ : ZMod p).val).testBit (b-1-k%b) else false

theorem tuple_eq (f : Factors p m) : tupleWord elemWord (pair f) =
    List.ofFn (fun k : Fin ((m*2)*bitLen p) => atDigit f (bitLen p) k) := by
  let b := bitLen p
  have hb : 0 < b := Nat.clog_pos (by decide) (Fact.out : p.Prime).one_lt
  rw [List.ofFn_mul]; unfold tupleWord
  let word (i : Fin (m*2)) := List.ofFn fun j : Fin b => atDigit f b (i.val*b+j.val)
  change _ = (List.ofFn word).flatten
  rw [List.ofFn_mul word,List.flatten_flatten,List.ofFn_eq_map,List.flatMap_def]
  apply congrArg List.flatten
  rw [List.map_map]; apply List.map_congr_left
  intro i _; change elemWord ((pair f).1 i) ++ elemWord ((pair f).2 i) = (List.ofFn fun j : Fin 2 => word ⟨i.val*2+j.val,_⟩).flatten
  rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_zero]; simp only [List.flatten_cons,List.flatten_nil,List.append_nil,Fin.val_zero,Fin.val_succ,Nat.zero_add,Nat.add_zero]
  change digitWord b _ ++ digitWord b _ = word ⟨i.val*2,_⟩ ++ word ⟨i.val*2+1,_⟩
  apply congrArg₂ List.append <;> unfold digitWord word <;> apply congrArg List.ofFn <;> funext j
  all_goals
    have div (k : ℕ) : (k*b+j.val)/b=k := by rw [Nat.mul_comm k b,Nat.mul_add_div hb,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
    have dv : (i.val*2+1)/2=i.val := by omega
    have md : (i.val*2+1)%2=1 := by omega
    simp [atDigit,div,dv,md,Nat.mod_eq_of_lt j.isLt,i.isLt,pair,l,r,Fin.val_rev,Nat.add_comm i.val m,
      show b-(j.val+1)=b-1-j.val by omega]

noncomputable def unitEquiv (S : FpSeed p m) (i : Fin m) (T : ℕ) : Accepted S i T ≃ ↥(fpFactorBlock T S i) := by
  refine (atomEquiv (d:=0) S i T).trans ?_
  let z := S8H0.ResidueWires.zmodFin p
  refine { toFun := fun a => ⟨Units.mk0 (z a.1) (fun h => a.2.1 (by have := congrArg ZMod.val h; simpa [z,S8H0.ResidueWires.zmodFin,ZMod.val_natCast_of_lt a.1.isLt] using this)), ?_⟩
           invFun := fun a => ⟨w3_fpResidue a.1,(residue_mem_iff S i T a.1).mp a.2⟩
           left_inv := fun a => Subtype.ext (Fin.ext (ZMod.val_natCast_of_lt a.1.isLt))
           right_inv := fun a => Subtype.ext (Units.ext (ZMod.natCast_zmod_val _)) }
  apply (residue_mem_iff ..).mpr; simpa only [w3_fpResidue,Units.val_mk0,z,S8H0.ResidueWires.zmodFin,Equiv.coe_fn_mk,ZMod.val_natCast_of_lt a.1.isLt] using a.2

theorem unit_val (S : FpSeed p m) (i : Fin m) (T : ℕ) (v : Accepted S i T) :
    (((unitEquiv S i T v).val : ZMod p)).val = num v.val.1.1 := ZMod.val_natCast_of_lt (residue S i T v).isLt

end DetDLP.S8L.PairOrder


