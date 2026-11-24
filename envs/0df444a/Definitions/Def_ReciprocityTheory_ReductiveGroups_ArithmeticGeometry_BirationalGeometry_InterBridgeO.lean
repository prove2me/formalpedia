-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeO
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeO
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:39.105862+00:00
-- url     : https://prove2.me/theorems/fb2b2ae9-4071-40b4-85c5-7ffe6fc2915f
-- title:
--   Inter Bridge O
-- statement:
--   Definitions and structural lemmas for Inter Bridge O, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeO.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeJ
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory
def NormPolyStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (f : MRing ι) (a : K → ℕ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsMultiHomog f a → f ∉ P →
    ∃ (c : MvPolynomial (Fin (e + 1)) ℂ) (m : ℕ), c ≠ 0 ∧ c.IsHomogeneous m ∧
      ∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) f) = 0 → eval (Ψ (segre z)) c = 0
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
end ReciprocityTheory.ChartRestriction.G.Geo


