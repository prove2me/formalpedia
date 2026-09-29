-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCover.obd_obd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/64ce3386-7e18-54d4-8b43-9dbc9bcfe14f

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrderedChains
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_obd

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

open AlgebraicGeometry.Scheme.OrderedAffineCover

theorem BdBdAux.sign_swap {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (-1 : ℤ) ^ (((i.succAbove j : Fin (n + 2)) : ℕ) + ((j.predAbove i : Fin (n + 1)) : ℕ)) = -((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) := by
  rcases j.castSucc.lt_or_le i with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.predAbove_of_castSucc_lt _ _ h, Fin.val_castSucc, Fin.val_pred]
    have hi : 1 ≤ (i : ℕ) := by
      have := Fin.lt_def.mp h; simp only [Fin.val_castSucc] at this; omega
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (i : ℕ) = m + 1 := ⟨(i : ℕ) - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel, show m + 1 + (j : ℕ) = (j + m) + 1 by omega, pow_succ, mul_neg_one]
    rw [neg_neg]
  · rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.predAbove_of_le_castSucc _ _ h, Fin.val_succ, Fin.coe_castPred,
      show (j : ℕ) + 1 + (i : ℕ) = ((i : ℕ) + (j : ℕ)) + 1 by omega, pow_succ, mul_neg_one]

theorem solution
    {V : Scheme.{u}} (K : V.OrderedAffineCover) (n : ℕ) (x : K.OCh (n + 2)) :
    K.obd n (K.obd (n + 1) x) = 0 := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | single u a =>
    rw [← mul_one a, ← Finsupp.smul_single', map_zsmul, map_zsmul]
    suffices h : K.obd n (K.obd (n + 1) (Finsupp.single u 1)) = 0 by rw [h, smul_zero]
    rw [K.obd_single, map_sum]
    simp only [map_zsmul, K.obd_single, Finset.smul_sum, smul_smul]
    rw [← Finset.sum_product' Finset.univ Finset.univ
      (fun (i : Fin (n + 1 + 2)) (j : Fin (n + 2)) => ((-1 : ℤ) ^ (i : ℕ) * (-1 : ℤ) ^ (j : ℕ)) •
        Finsupp.single (K.oface (K.oface u i) j) (1 : ℤ))]
    refine Finset.sum_involution
      (fun (p : Fin (n + 1 + 2) × Fin (n + 2)) _ => ((p.1.succAbove p.2 : Fin (n + 1 + 2)), p.2.predAbove p.1)) ?_ ?_ ?_ ?_
    ·
      rintro ⟨i, j⟩ _
      have hface : K.oface (K.oface u (i.succAbove j)) (j.predAbove i) = K.oface (K.oface u i) j := by
        funext k
        change u ((i.succAbove j).succAbove ((j.predAbove i).succAbove k)) = u (i.succAbove (j.succAbove k))
        rw [Fin.succAbove_succAbove_succAbove_predAbove]
      change ((-1 : ℤ) ^ (i : ℕ) * (-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (K.oface (K.oface u i) j) (1 : ℤ) +
        ((-1 : ℤ) ^ ((i.succAbove j : Fin (n + 1 + 2)) : ℕ) * (-1 : ℤ) ^ ((j.predAbove i : Fin (n + 2)) : ℕ)) •
          Finsupp.single (K.oface (K.oface u (i.succAbove j)) (j.predAbove i)) (1 : ℤ) = 0
      rw [hface, ← add_smul, ← pow_add, ← pow_add, BdBdAux.sign_swap i j, add_neg_cancel, zero_smul]
    · rintro ⟨i, j⟩ _ _
      exact fun h => Fin.succAbove_ne i j (congrArg Prod.fst h)
    · rintro ⟨i, j⟩ _; exact Finset.mem_univ _
    · rintro ⟨i, j⟩ _
      exact Prod.ext (Fin.succAbove_succAbove_predAbove i j) (Fin.predAbove_predAbove_succAbove i j)

end S_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_obd
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_obd (solution)
