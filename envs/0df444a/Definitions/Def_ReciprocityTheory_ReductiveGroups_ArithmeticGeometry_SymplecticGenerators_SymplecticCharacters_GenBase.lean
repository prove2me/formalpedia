-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:30.207909+00:00
-- url     : https://prove2.me/theorems/7add9a24-b900-40c5-9a1b-2f83792c92ff
-- title:
--   Gen Base
-- statement:
--   Definitions and structural lemmas for Gen Base, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenBase.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
abbrev spH (g : ℕ) : Submonoid (Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :=
  Submonoid.closure (spGens g)
def spLow (S : Matrix (Fin g) (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
  fromBlocks 1 0 S 1
abbrev eJ (j : Fin g) : Matrix (Fin g) (Fin g) ℤ := single j j 1
def spPJ (j : Fin g) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
  fromBlocks (1 - eJ j) (eJ j) (-eJ j) (1 - eJ j)
end ReciprocityTheory.ChartRestriction.G.Key.Chi


