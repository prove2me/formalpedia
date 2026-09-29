-- Prove2me | solution 1 for AlgebraicCurve.GluedPic0.eq_zero_of_pow_char_smul_eq_zero_of_toPic0Pair_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/4d3a7dd4-13fd-5329-9f97-c3740810813e

import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_GluedPic0_ker_toPic0Pair_eq_range_nodeUnit
import Theorems.Thm_AlgebraicCurve_GluedPic0_nodeUnit_eq_zero_iff_of_constantsAreBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_GluedPic0_eq_zero_of_pow_char_smul_eq_zero_of_toPic0Pair_eq_zero

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (hCB : ConstantsAreBase K F)
    (S : Finset (Place K F × Place K F))
    (hrat : ∀ s : ↥S,
      Function.Surjective (algebraMap K ((s : Place K F × Place K F).1.ResidueField)) ∧
        Function.Surjective (algebraMap K ((s : Place K F × Place K F).2.ResidueField)))
    (p : ℕ) [Fact p.Prime] [CharP K p] (k : ℕ)
    (x : GluedPic0 K F S) (hx : (p ^ k : ℤ) • x = 0) (h0 : GluedPic0.toPic0Pair S x = 0) :
    x = 0 := by

  have hker : x ∈ (GluedPic0.toPic0Pair S).ker := (AddMonoidHom.mem_ker).2 h0
  rw [AlgebraicCurve.GluedPic0.ker_toPic0Pair_eq_range_nodeUnit S hrat] at hker
  obtain ⟨w, rfl⟩ := hker

  have hx' : GluedPic0.nodeUnit S (((p : ℤ) ^ k) • w) = 0 := by rw [map_zsmul]; exact hx
  obtain ⟨c, hc⟩ := (AlgebraicCurve.GluedPic0.nodeUnit_eq_zero_iff_of_constantsAreBase hCB S _).1 hx'

  have hppos : 0 < p ^ k := pow_pos (Fact.out : p.Prime).pos k
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (c : K) hppos
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hppos.ne'] at hz
    exact c.ne_zero hz.symm
  have hws : ∀ s : ↥S, ((Additive.toMul (w s) : Kˣ) : K) = z := by
    intro s
    have h1 := congrFun hc s

    have h2 : ((Additive.toMul (w s) : Kˣ) : K) ^ (p ^ k) = z ^ (p ^ k) := by
      have h3 : Additive.toMul ((((p : ℤ) ^ k) • w) s) = c := by rw [h1]; rfl
      rw [Pi.smul_apply, toMul_zsmul, ← Nat.cast_pow, zpow_natCast] at h3
      rw [hz, ← h3, Units.val_pow_eq_pow_val]
    have hinj : Function.Injective (fun y : K => y ^ (p ^ k)) := by
      have := Function.Injective.iterate (frobenius_inj K p) k
      intro a b hab
      apply this
      simp only [iterate_frobenius]
      exact hab
    exact hinj h2
  have hw : w = fun _ => Additive.ofMul (Units.mk0 z hz0) := by
    funext s
    refine Additive.toMul.injective (Units.ext ?_)
    rw [hws s]
    rfl
  rw [hw]
  exact AlgebraicCurve.GluedPic0.nodeUnit_const S _

end S_AlgebraicCurve_GluedPic0_eq_zero_of_pow_char_smul_eq_zero_of_toPic0Pair_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_GluedPic0_eq_zero_of_pow_char_smul_eq_zero_of_toPic0Pair_eq_zero (solution)
