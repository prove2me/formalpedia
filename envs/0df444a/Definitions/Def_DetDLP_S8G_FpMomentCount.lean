-- Prove2me | Definitions.Def_DetDLP_S8G_FpMomentCount
-- name    : DetDLP_S8G_FpMomentCount
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:51:00.662201+00:00
-- url     : https://prove2.me/theorems/affb4e04-3adf-4c2d-970d-899932fe4a1e
-- title:
--   Finite witness sets for the four prime-field moments
-- statement:
--   For seeds whose binary encoding extends the given prefix, the four moments count seeds, single factor tuples, ordered pairs of factor tuples, and pairs with equal products. Partitioning the last set by the common product gives the sum of squared representation counts.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_M89_S1_Queries

set_option autoImplicit false
namespace DetDLP.S8G.FpMoment
open M89S1

section Fibers
variable {G : Type} [CommGroup G] [DecidableEq G] [Fintype G] {m : ℕ}
variable (D : Fin m → Finset G)

abbrev Tuple := ↥(Fintype.piFinset D)
abbrev Fiber (g : G) := ↥((Fintype.piFinset D).filter fun A => ∏ i, A i = g)
abbrev Collision := {ab : Tuple D × Tuple D // (∏ i, ab.1.val i) = ∏ i, ab.2.val i}

/-- The common product is uniquely determined by either member of a collision. -/
def splitCollision : Collision D ≃ Σ g : G, Fiber D g × Fiber D g where
  toFun ab := ⟨∏ i, ab.1.1.val i,
    ⟨_,Finset.mem_filter.mpr ⟨ab.1.1.2,rfl⟩⟩,
    ⟨_,Finset.mem_filter.mpr ⟨ab.1.2.2,ab.2.symm⟩⟩⟩
  invFun := fun ⟨_,A,B⟩ => ⟨(⟨_,(Finset.mem_filter.mp A.2).1⟩,⟨_,(Finset.mem_filter.mp B.2).1⟩),
    (Finset.mem_filter.mp A.2).2.trans (Finset.mem_filter.mp B.2).2.symm⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨g,⟨A,hA⟩,⟨B,hB⟩⟩
    obtain ⟨_,rfl⟩ := Finset.mem_filter.mp hA
    rfl

omit [CommGroup G] [DecidableEq G] [Fintype G] in
theorem tuple_card : Fintype.card (Tuple D) = productSize D := by
  exact (Fintype.card_coe _).trans (Fintype.card_piFinset D)

theorem collision_card : Fintype.card (Collision D) = collisionEnergyMul D := by
  rw [Fintype.card_congr (splitCollision D), Fintype.card_sigma]
  simp only [Fintype.card_prod, Fiber, Fintype.card_coe, collisionEnergyMul, repCountMul, pow_two]
end Fibers

variable (p m T : ℕ) [Fact p.Prime] (η : List Bool)

abbrev seedSet := Finset.univ.filter fun S : FpSeed p m => (List.ofFn (fpBits S)).take η.length = η
abbrev value (j : Fin 4) := moment (@fpBits p m)
  (fun S => productSize (fpFactorBlock T S)) (fun S => collisionEnergyMul (fpFactorBlock T S)) j η

abbrev Mass := ↥(seedSet p m η)
abbrev Single := Σ S : Mass p m η, Tuple (fpFactorBlock T S.val)
abbrev Double := Σ S : Mass p m η, Tuple (fpFactorBlock T S.val) × Tuple (fpFactorBlock T S.val)
abbrev EqualProd := Σ S : Mass p m η, Collision (fpFactorBlock T S.val)

theorem mass_card : Fintype.card (Mass p m η) = value p m T η 0 := by
  rw [Fintype.card_coe]
  simp [seedSet, value, moment]

theorem single_card : Fintype.card (Single p m T η) = value p m T η 1 := by
  rw [Fintype.card_sigma]
  simp only [tuple_card]
  rw [Finset.sum_coe_sort (seedSet p m η) (fun S => productSize (fpFactorBlock T S))]
  simp [value, moment, seedSet]

theorem double_card : Fintype.card (Double p m T η) = value p m T η 2 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, tuple_card, ← sq]
  rw [Finset.sum_coe_sort (seedSet p m η) (fun S => productSize (fpFactorBlock T S) ^ 2)]
  simp [value, moment, seedSet]

theorem equalProd_card : Fintype.card (EqualProd p m T η) = value p m T η 3 := by
  rw [Fintype.card_sigma]
  simp only [collision_card]
  rw [Finset.sum_coe_sort (seedSet p m η) (fun S => collisionEnergyMul (fpFactorBlock T S))]
  simp [value, moment, seedSet]

end DetDLP.S8G.FpMoment


