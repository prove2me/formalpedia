-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangeSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangeSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:43.657843+00:00
-- url     : https://prove2.me/theorems/3930be55-a1dd-443e-ac25-685a4bf8e297
-- title:
--   Basis Change St
-- statement:
--   Definitions and structural lemmas for Basis Change St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BasisChangeSt.lean

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
def BasisChangeStatement : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) [Fintype ι] (P : MvPolynomial ι K) (d : ℕ),
    P.IsHomogeneous d → (∀ μ, ‖MvPolynomial.coeff μ P‖ ≤ 1) →
    ∀ (A : ι → ι → K) (C : ℝ), 1 ≤ C → (∀ i k, ‖A i k‖ ≤ C) →
      ∀ μ, ‖MvPolynomial.coeff μ
        (MvPolynomial.bind₁ (fun i => ∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) P)‖ ≤ C ^ d
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank


