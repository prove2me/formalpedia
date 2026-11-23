-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:37.891243+00:00
-- url     : https://prove2.me/theorems/31a67b4c-c9ba-4725-9afc-2e2bed287ab9
-- title:
--   Single Mem Standard Lattice
-- statement:
--   Definitions and structural lemmas for Single Mem Standard Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SingleMemStandardLattice.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate
import Definitions.Def_ReciprocityTheory_SemistableReduction_DegAddHolds
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder
section Deg
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
def hStd (K : Type) [Field K] [NumberField K] (r : ℕ) : Submodule (𝓞 K) (Fin r → K) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 K) K)
end Deg
section Deg2
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
end Deg2
end ReciprocityTheory.ChartRestriction.G.T0


