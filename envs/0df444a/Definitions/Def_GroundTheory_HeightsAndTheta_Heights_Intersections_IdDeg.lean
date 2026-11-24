-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IdDeg
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_IdDeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:43.661819+00:00
-- url     : https://prove2.me/theorems/0c4c7ee8-e53a-48ad-b74a-e5535c807c89
-- title:
--   Id Deg
-- statement:
--   Definitions and structural lemmas for Id Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IdDeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalSpanXb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
def ArithmeticIntersectionDivisorPushforward.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ)) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (E : Ideal (MRing ι') → ℤ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J →
    IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    (∀ W' ∈ divSupp P' (rename v s), imageZ v W' = W →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)),
        IsFieldIntersection J' ∧ E W' = J' (fibreIdeal κ G') 0 Fin.elim0) →
    ∑ᶠ W' ∈ {W' | W' ∈ divSupp P' (rename v s) ∧ imageZ v W' = W},
        (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℤ) * E W' =
      J (fibreIdeal κ G) 0 Fin.elim0 * multAt (imageZ v P' ⊔ Ideal.span {s}) W
section Inhabitants
open Classical in

def idDeg (W' : Ideal (MRing (GlobalTheory 2))) : ℤ :=
  if h : W'.IsPrime then
    haveI := h
    noBlockFam (genFibreIdOf W').Φ (fibreIdx (GlobalTheory 2) (id : Unit → Unit))
      (fibreIdeal id (genFibreIdOf W')) 0 Fin.elim0
  else 0
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


