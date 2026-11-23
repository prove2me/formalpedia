-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:19.900603+00:00
-- url     : https://prove2.me/theorems/02217f4d-ec37-47f7-b8f5-ab0f15c062db
-- title:
--   Orthogonal Projector Mul Vec Conjugate
-- statement:
--   Definitions and structural lemmas for Orthogonal Projector Mul Vec Conjugate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulVecConjugate.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField ComplexConjugate NumberField.ComplexEmbedding
open scoped ComplexOrder Kronecker
section Gram
variable {K : Type} [Field K] [NumberField K] {r k m : ℕ}
end Gram
section GramDet
variable {K : Type} [Field K] [NumberField K] {r k m : ℕ}
noncomputable def hwv (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) :
    Fin m × Module.Free.ChooseBasisIndex ℤ (𝓞 K) → EuclideanSpace ℝ (hIdx K r) :=
  fun p => hpv b (integralBasis K p.2 • c p.1)
end GramDet
end ReciprocityTheory.ChartRestriction.G.T0


