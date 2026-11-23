-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:26.335851+00:00
-- url     : https://prove2.me/theorems/09f4fbcb-cb10-49c1-a0c9-aa3c4c4569db
-- title:
--   FBId Jet
-- statement:
--   Definitions and structural lemmas for FBId Jet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdJet.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]
theorem psTrunc_mem_orig {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) (g : MvPowerSeries τ R)
    (hg : MvPowerSeries.constantCoeff g = 0) : psTrunc m g ∈ orig R τ := by
  unfold psTrunc
  refine Ideal.sum_mem _ fun e _ => ?_
  by_cases he : e = 0
  · subst he
    first
    | simp [hg]
    | (rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg, map_zero]; exact Ideal.zero_mem _)
  · obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext fun j => by simp [h j])
    have key : MvPolynomial.monomial e (MvPowerSeries.coeff e g) =
        MvPolynomial.monomial (e - Finsupp.single i 1) (MvPowerSeries.coeff e g) *
          MvPolynomial.X i := by
      have hs : e - Finsupp.single i 1 + Finsupp.single i 1 = e := by
        ext j
        by_cases h : j = i
        · subst h
          first
          | (simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_eq_same]; omega)
          | (simp [Finsupp.single_apply]; omega)
          | simp [Finsupp.single_apply]
        · first
          | (simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne (Ne.symm h)]; omega)
          | simp [Finsupp.single_apply, h, Ne.symm h]
      rw [MvPolynomial.X, MvPolynomial.monomial_mul, mul_one, hs]
    rw [key]
    refine Ideal.mul_mem_left _ _ ?_
    first
    | exact Ideal.subset_span ⟨i, rfl⟩
    | (unfold orig; exact Ideal.subset_span ⟨i, rfl⟩)
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet


