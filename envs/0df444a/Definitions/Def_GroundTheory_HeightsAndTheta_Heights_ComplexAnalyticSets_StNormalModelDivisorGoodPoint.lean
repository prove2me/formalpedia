-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelDivisorGoodPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelDivisorGoodPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:54.596277+00:00
-- url     : https://prove2.me/theorems/271d37eb-3436-44c0-a505-4bbf95d71ea3
-- title:
--   St Normal Model Divisor Good Point
-- statement:
--   Definitions and structural lemmas for St Normal Model Divisor Good Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModelDivisorGoodPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
noncomputable section
def NormalModelDivisorGoodPoint {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (u : Fin n → ℂ) (d : ℕ) (w : Fin n ⊕ Fin M.m → ℂ) : Prop :=
  w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧
  ∃ (c : ℕ) (f : Fin c → MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (h g a b : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (k : ℕ),
    c + (d + 1) = n + M.m ∧ (∀ j, f j ∈ M.ideal) ∧
    eval w h ≠ 0 ∧ (∀ p ∈ M.ideal, ∃ e : ℕ, h ^ e * p ∈ Ideal.span (Set.range f)) ∧
    eval w g = 0 ∧
    LinearIndependent ℂ (Fin.cons (fun s ↦ eval w (pderiv s g)) (fun j s ↦ eval w (pderiv s (f j))) :
      Fin (c + 1) → Fin n ⊕ Fin M.m → ℂ) ∧
    0 < k ∧ eval w a ≠ 0 ∧ eval w b ≠ 0 ∧
    b * rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m) (linForm u) - a * g ^ k ∈ M.ideal ∧
    ∀ v : Fin n ⊕ Fin M.m → ℂ, (∀ i : Fin n, v (Sum.inl i) = 0) →
      ∑ s, eval w (pderiv s g) * v s = 0 → (∀ j, ∑ s, eval w (pderiv s (f j)) * v s = 0) → v = 0
end
end GroundTheory.Heights₂.Heights


