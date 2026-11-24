-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:12.582083+00:00
-- url     : https://prove2.me/theorems/711af865-6565-4f1b-996e-7a1b1a9fd816
-- title:
--   Inter Good
-- statement:
--   Definitions and structural lemmas for Inter Good, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGood.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
def scaleBlock (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => (if p.1 = k0 then c else 1) * z p
def evQ (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) :
    MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P →+* ℂ :=
  Ideal.Quotient.lift (qIdeal P) (eval₂Hom (algebraMap ℚ ℂ) z) fun a ha => by
    have hle : qIdeal P ≤ RingHom.ker (eval₂Hom (algebraMap ℚ ℂ) z) := by
      refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, coe_eval₂Hom, eval₂_map]
      have h := hz.2 f hf
      rw [eval_map] at h
      convert h using 2
      exact RingHom.ext_int _ _
    exact hle ha
end
end ReciprocityTheory.ChartRestriction.G.Geo


