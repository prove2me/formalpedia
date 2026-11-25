-- Prove2me | Definitions.Def_DetDLP_S8I_ECQueryCount
-- name    : DetDLP_S8I_ECQueryCount
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:43:07.74879+00:00
-- url     : https://prove2.me/theorems/509f2794-aacd-4fcc-b918-e85f60a2f760
-- title:
--   Exact cardinalities for elliptic-curve pair and moment queries
-- statement:
--   The number of ordered block pairs satisfying a prefix and a target sum is the pair query count. Over seeds extending a prefix, the four moment counts are cardinalities of seeds, single tuples, ordered tuple pairs, and equal-sum collisions, respectively.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_M89_S1_Queries

noncomputable section

set_option autoImplicit false
namespace DetDLP.S8I.ECQueryCount
open M89S1

section Fibers
variable {G : Type} [AddCommGroup G] [DecidableEq G] [Fintype G] {m : ℕ}
variable (D : Fin m → Finset G)

abbrev Tuple := ↥(Fintype.piFinset D)
abbrev Fiber (g : G) := ↥((Fintype.piFinset D).filter fun A => ∑ i, A i = g)
abbrev Collision := {ab : Tuple D × Tuple D // (∑ i, ab.1.val i) = ∑ i, ab.2.val i}

/-- The common sum is uniquely determined by either member of a collision. -/
def splitCollision : Collision D ≃ Σ g : G, Fiber D g × Fiber D g where
  toFun ab := ⟨∑ i, ab.1.1.val i,
    ⟨_,Finset.mem_filter.mpr ⟨ab.1.1.2,rfl⟩⟩,
    ⟨_,Finset.mem_filter.mpr ⟨ab.1.2.2,ab.2.symm⟩⟩⟩
  invFun := fun ⟨_,A,B⟩ => ⟨(⟨_,(Finset.mem_filter.mp A.2).1⟩,⟨_,(Finset.mem_filter.mp B.2).1⟩),
    (Finset.mem_filter.mp A.2).2.trans (Finset.mem_filter.mp B.2).2.symm⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨g,⟨A,hA⟩,⟨B,hB⟩⟩
    obtain ⟨_,rfl⟩ := Finset.mem_filter.mp hA
    rfl

omit [AddCommGroup G] [DecidableEq G] [Fintype G] in
theorem tuple_card : Fintype.card (Tuple D) = productSize D := by
  exact (Fintype.card_coe _).trans (Fintype.card_piFinset D)

theorem collision_card : Fintype.card (Collision D) = collisionEnergyAdd D := by
  rw [Fintype.card_congr (splitCollision D), Fintype.card_sigma]
  simp only [Fintype.card_prod, Fiber, Fintype.card_coe, collisionEnergyAdd, repCountAdd, pow_two]
end Fibers

variable (p m : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (T : ℕ) (η : List Bool)

abbrev seedSet := Finset.univ.filter fun S : ECSeed p m => (List.ofFn (ecBits S)).take η.length = η
abbrev value (j : Fin 4) :=
  letI : Fintype E.toAffine.Point := ecPointFintype E
  moment (@ecBits p m)
  (fun S => productSize (ecFactorBlock E T S)) (fun S => collisionEnergyAdd (ecFactorBlock E T S)) j η

abbrev Mass := ↥(seedSet p m η)
abbrev Single := Σ S : Mass p m η, Tuple (ecFactorBlock E T S.val)
abbrev Double := Σ S : Mass p m η, Tuple (ecFactorBlock E T S.val) × Tuple (ecFactorBlock E T S.val)
abbrev EqualSum := Σ S : Mass p m η, Collision (ecFactorBlock E T S.val)

theorem mass_card : Fintype.card (Mass p m η) = value p m E T η 0 := by
  rw [Fintype.card_coe]
  simp [seedSet, value, moment]

theorem single_card : Fintype.card (Single p m E T η) = value p m E T η 1 := by
  rw [Fintype.card_sigma]
  simp only [tuple_card]
  rw [Finset.sum_coe_sort (seedSet p m η) (fun S => productSize (ecFactorBlock E T S))]
  simp [value, moment, seedSet]

theorem double_card : Fintype.card (Double p m E T η) = value p m E T η 2 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, tuple_card, ← sq]
  rw [Finset.sum_coe_sort (seedSet p m η) (fun S => productSize (ecFactorBlock E T S) ^ 2)]
  simp [value, moment, seedSet]

local instance : Fintype E.toAffine.Point := ecPointFintype E

theorem equalSum_card : Fintype.card (EqualSum p m E T η) = value p m E T η 3 := by
  rw [Fintype.card_sigma]
  simp only [collision_card]
  rw [Finset.sum_coe_sort (seedSet p m η) (fun S => collisionEnergyAdd (ecFactorBlock E T S))]
  simp [value, moment, seedSet]

abbrev PointPair := (Fin m → E.toAffine.Point) × (Fin m → E.toAffine.Point)

def pairSet (b : ℕ) (S : ECSeed p m) (X : E.toAffine.Point) : Finset (PointPair p m E) := by
  classical
  letI : Fintype E.toAffine.Point := ecPointFintype E
  exact Finset.univ.filter fun ab => (∀ i, ab.1 i ∈ ecFactorBlock E T S i ∧ ab.2 i ∈ ecFactorBlock E T S i) ∧
    (tupleWord (ecWord b) ab).take η.length = η ∧ (∑ i, (ab.1 i + ab.2 i)) = X

abbrev PairSet (b : ℕ) (S : ECSeed p m) (X : E.toAffine.Point) := ↥(pairSet p m E T η b S X)

theorem pair_card (b : ℕ) (S : ECSeed p m) (X : E.toAffine.Point) :
    Fintype.card (PairSet p m E T η b S X) = pairCount (ecFactorBlock E T S) (ecWord b)
      (fun ab => (∑ i, (ab.1 i + ab.2 i)) = X) η := by
  classical
  rw [Fintype.card_coe]; unfold pairSet pairCount
  apply congrArg Finset.card
  ext ab
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end DetDLP.S8I.ECQueryCount


