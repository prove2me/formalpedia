-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:38:10.063579+00:00
-- url     : https://prove2.me/theorems/91b8d97e-97ab-4cff-a70b-4dd24ec0157e
-- title:
--   Is Multi Homog Xpow
-- statement:
--   Definitions and structural lemmas for Is Multi Homog Xpow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsMultiHomogXpow.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
def xpow (i : ∀ k, ι k) (e : K → ℕ) : MRing ι := ∏ k, (X ⟨k, i k⟩ : MRing ι) ^ (e k)
def dehomI (W : Ideal (MRing ι)) (i : ∀ k, ι k) : Ideal (MRing ι) :=
  W ⊔ Ideal.span (Set.range fun k => (X ⟨k, i k⟩ : MRing ι) - 1)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


