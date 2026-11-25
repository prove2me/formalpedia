-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BetaSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BetaSt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:00:21.269577+00:00
-- url     : https://prove2.me/theorems/2664a843-90cd-4b2c-b6a2-071775a78cd2
-- title:
--   Beta St
-- statement:
--   Definitions and structural lemmas for Beta St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BetaSt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
def pairR {f : ℕ} (χ β : Fin f → ℝ) : ℝ := ∑ i, χ i * β i
def BetaStatement : Prop :=
  ∀ (f : ℕ) (b : Module.Basis (Fin f) ℝ (Fin f → ℝ)) (m : ℕ), 0 < m →
    let SS : Submodule ℤ (Fin f → ℝ) := Submodule.span ℤ (Set.range b)
    ∀ χ₀ ∈ SS, (∀ i, 0 ≤ χ₀ i) →
      ∃ β : Fin f → ℝ, (∀ i, 0 < β i) ∧ (∀ χ ∈ SS, ∃ z : ℤ, pairR χ β = m * z) ∧
        ∀ χ ∈ SS, (∀ i, 0 ≤ χ i) → pairR χ β = pairR χ₀ β → χ = χ₀
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank


