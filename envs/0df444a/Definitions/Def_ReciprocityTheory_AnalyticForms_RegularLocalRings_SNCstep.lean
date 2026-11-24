-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SNCstep
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_SNCstep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:42.567801+00:00
-- url     : https://prove2.me/theorems/f10f372c-b6e8-4d9a-a5da-901ff1b72127
-- title:
--   SNCstep
-- statement:
--   Definitions and structural lemmas for SNCstep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SNCstep.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M
section SlopeTestRemainingChoices
variable {n : ℕ}
noncomputable def locEvalPt (I : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ g ∈ I, eval p g = 0) : locRing I p →+* ℂ :=
  Ideal.Quotient.lift _
    (IsLocalization.lift (M := (ptIdeal p).primeCompl) (S := locPt p) (g := eval p)
      (fun y => by
        have hy : (y : MvPolynomial (Fin n) ℂ) ∉ ptIdeal p := y.2
        exact isUnit_iff_ne_zero.2 fun h => hy (RingHom.mem_ker.2 h)))
    (by
      intro z hz
      have hle : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) I ≤
          RingHom.ker (IsLocalization.lift (M := (ptIdeal p).primeCompl) (S := locPt p)
            (g := eval p) (fun y => by
              have hy : (y : MvPolynomial (Fin n) ℂ) ∉ ptIdeal p := y.2
              exact isUnit_iff_ne_zero.2 fun h => hy (RingHom.mem_ker.2 h))) := by
        rw [Ideal.map_le_iff_le_comap]
        intro g hg
        simp only [Ideal.mem_comap, RingHom.mem_ker, IsLocalization.lift_eq]
        exact hp g hg
      exact hle hz)
end SlopeTestRemainingChoices
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end ReciprocityTheory.AnForm.R


