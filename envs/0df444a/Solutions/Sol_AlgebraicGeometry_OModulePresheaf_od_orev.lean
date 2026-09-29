-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.od_orev
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/dfcb7c4e-4174-5c3f-ab3c-a707bd8d874f

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechReversal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_od_orev

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

open AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.Scheme.OrderedAffineCover in
theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (c : F.ocochain K n) :
    F.od K n (F.orev K n c) = F.orev K (n + 1) (F.od K n c) := by
  classical
  funext t
  rw [od_apply, orev_apply, od_apply, map_sum, Finset.smul_sum]
  have hchain : ∀ i : Fin (n + 2),
      K.oface (t ∘ Fin.rev) i = (K.oface t ((Fin.revPerm : Equiv.Perm (Fin (n + 2))) i)) ∘ Fin.rev := by
    intro i; funext k
    show t (Fin.rev (i.succAbove k)) = t ((Fin.rev i).succAbove (Fin.rev k))
    rw [Fin.rev_succAbove]
  have key : ∀ (w w' : K.OIdx n), w = w' → ∀ (h : K.ointer t ≤ K.ointer w) (h' : K.ointer t ≤ K.ointer w'),
      F.res h (c w) = F.res h' (c w') := by
    intro w w' e; subst e; intro h h'; rfl
  have hE : (n + 1) * (n + 1 + 1) / 2 = n * (n + 1) / 2 + (n + 1) := by
    have : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
    rw [this, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
  symm
  refine Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Fin (n + 2))) _ _ (fun i => ?_)
  rw [map_zsmul, smul_smul, F.res_res, orev_apply, map_zsmul, smul_smul, F.res_res]
  rw [key _ _ (hchain i) _
    ((K.ointer_le_ointer_oface t ((Fin.revPerm : Equiv.Perm (Fin (n + 2))) i)).trans (K.ointer_le_ointer_comp_rev _))]
  congr 1
  have hm : n + 1 = (((Fin.revPerm : Equiv.Perm (Fin (n + 2))) i : Fin (n + 2)) : ℕ) + (i : ℕ) := by
    have hi := i.is_lt
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  have hm' : (-1 : ℤ) ^ (n + 1) = (-1 : ℤ) ^ (((Fin.revPerm : Equiv.Perm (Fin (n + 2))) i : Fin (n + 2)) : ℕ) * (-1 : ℤ) ^ (i : ℕ) := by
    rw [← pow_add, ← hm]
  have h2 : ((-1 : ℤ) ^ (i : ℕ)) * ((-1 : ℤ) ^ (i : ℕ)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [hE, pow_add, hm']
  linear_combination ((-1 : ℤ) ^ (n * (n + 1) / 2) *
    (-1 : ℤ) ^ (((Fin.revPerm : Equiv.Perm (Fin (n + 2))) i : Fin (n + 2)) : ℕ)) * h2

end S_AlgebraicGeometry_OModulePresheaf_od_orev
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_od_orev (solution)
