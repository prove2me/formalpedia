-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsPrimeFiltrationOfIsMultiHomogIdeal
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsPrimeFiltrationOfIsMultiHomogIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:45.33999+00:00
-- url     : https://prove2.me/theorems/a5d380e9-e9da-4f18-abe2-4cac77fa1a2a
-- title:
--   Exists Prime Filtration Of Is Multi Homog Ideal
-- statement:
--   Definitions and structural lemmas for Exists Prime Filtration Of Is Multi Homog Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsPrimeFiltrationOfIsMultiHomogIdeal.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
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
noncomputable abbrev lexDecEq (n : ℕ) : DecidableEq (Lex (Fin n → ℕ)) := LinearOrder.toDecidableEq
attribute [local instance 2000] lexDecEq
section Lex
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}
def lexW (e : K ≃ Fin n) : (Σ k, ι k) → Lex (Fin n → ℕ) :=
  fun p => toLex (Pi.single (e p.1) 1)
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end Lex
section Filtration
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end Filtration
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


