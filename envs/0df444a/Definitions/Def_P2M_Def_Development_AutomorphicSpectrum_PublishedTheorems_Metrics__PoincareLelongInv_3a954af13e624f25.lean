-- Prove2me | Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__PoincareLelongInv_3a954af13e624f25
-- name    : P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__PoincareLelongInv_3a954af13e624f25
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:48.998026+00:00
-- url     : https://prove2.me/theorems/f246f4be-13ec-41c9-b6e0-1354401a0421
-- title:
--   Poincare Lelong Inv
-- statement:
--   Definitions and structural lemmas for Poincare Lelong Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Metrics₂/PoincareLelongInv.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.Hypotheses₂
open ReciprocityTheory.ChartRestriction.G.Geo
def PoincareLelongInv : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    (∀ j, IsConjInvariantH (L j)) → IsConjInvariantH A → IsConjInvariantH B →
    B.a = 0 → IsSectionOn P A s →
    ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (logNorm A s) =
      (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
          (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z))) -
        ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (fun z => Real.log (B.h z))
end GlobalTheory.CompanionTheory.Hypotheses₂


