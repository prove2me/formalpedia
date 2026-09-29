-- Prove2me | solution 1 for Algebra.exists_adjoin_ne_zero_mul_forall_valuationSubring_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f91bbcf9-3534-58f8-ab1c-269e27a7754f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem

set_option autoImplicit false
set_option maxHeartbeats 9600000

open Polynomial

noncomputable section

theorem solution
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (f : F) [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (z : F) :
    ∃ q₀ : Algebra.adjoin L ({f} : Set F), q₀ ≠ 0 ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → (q₀ : F) * z ∈ V := by
  classical
  set Lf := Algebra.adjoin L ({f} : Set F) with hLf
  set Kf := IntermediateField.adjoin L ({f} : Set F) with hKf

  have hle : Lf ≤ Kf.toSubalgebra := Algebra.adjoin_le
    (Set.singleton_subset_iff.mpr
      (show f ∈ Kf from IntermediateField.mem_adjoin_simple_self L f))
  let ι : Lf →+* Kf := Subsemiring.inclusion hle
  have hι : ∀ a : Lf, ((ι a : Kf) : F) = (a : F) := fun _ => rfl
  have hιinj : Function.Injective ι := fun a b h => Subtype.ext
    (congrArg (fun x : Kf => (x : F)) h)

  letI algLK : Algebra Lf Kf := ι.toAlgebra
  haveI istLKF : IsScalarTower Lf Kf F := by
    refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => ?_)
    show (a : F) = ((ι a : Kf) : F)
    rfl
  haveI ifrLK : IsFractionRing Lf Kf := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    ·
      rintro ⟨m, hm⟩
      refine isUnit_iff_ne_zero.mpr fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hm) ?_
      exact hιinj (h.trans (map_zero ι).symm)
    ·
      intro c
      obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff L (c : F)).mp c.2
      have hrLf : aeval f r ∈ Lf := by
        rw [hLf, Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨r, rfl⟩
      have hsLf : aeval f s ∈ Lf := by
        rw [hLf, Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨s, rfl⟩
      rcases eq_or_ne (aeval f s) 0 with hs0 | hs0
      · have hc0 : c = 0 := Subtype.ext (show (c : F) = 0 from by rw [hrs, hs0, div_zero])
        exact ⟨⟨0, 1⟩, by rw [hc0]; simp⟩
      · refine ⟨⟨⟨aeval f r, hrLf⟩,
          ⟨⟨aeval f s, hsLf⟩,
            mem_nonZeroDivisors_iff_ne_zero.mpr fun h => hs0 (Subtype.ext_iff.mp h)⟩⟩, ?_⟩
        apply Subtype.ext
        show (c : F) * aeval f s = aeval f r
        rw [hrs, div_mul_cancel₀ _ hs0]
    ·
      intro a b h
      exact ⟨1, by rw [hιinj h]⟩

  have hz : IsIntegral Kf z := IsIntegral.of_finite Kf z

  obtain ⟨⟨m, hm⟩, hint⟩ :=
    hz.exists_multiple_integral_of_isLocalization (nonZeroDivisors Lf)
  refine ⟨m, mem_nonZeroDivisors_iff_ne_zero.mp hm, fun V hL hfV => ?_⟩

  have hsmul : (m : F) * z = (m : Lf) • z := (Algebra.smul_def m z).symm
  rw [hsmul]

  set s : Set F := Set.range (algebraMap L F) ∪ {f}
  have hcl : Subring.closure s = Lf.toSubring :=
    (Algebra.adjoin_eq_ring_closure ({f} : Set F)).symm
  have hint2 : IsIntegral (Subring.closure s) ((m : Lf) • z) := by
    refine hint.map_of_comp_eq (Subring.inclusion hcl.ge) (RingHom.id F) ?_
    ext a; rfl
  have hmem : (m : Lf) • z ∈ (integralClosure (Subring.closure s) F).toSubring := hint2
  rw [← iInf_valuationSubring_superset (s := s)] at hmem
  simp only [Subring.mem_iInf] at hmem
  exact hmem ⟨V, fun x hx => hx.elim (fun ⟨c, hc⟩ => hc ▸ hL c) (fun hx => hx ▸ hfV)⟩

end
end S_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem
end P2MW
export P2MW.S_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem (solution)
