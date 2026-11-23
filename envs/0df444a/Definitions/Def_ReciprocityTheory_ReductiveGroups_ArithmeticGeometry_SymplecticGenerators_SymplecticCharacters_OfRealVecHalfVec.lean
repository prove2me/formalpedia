-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:18:27.53291+00:00
-- url     : https://prove2.me/theorems/66cde756-1f0a-44c3-9352-0581cf8d7759
-- title:
--   Of Real Vec Half Vec
-- statement:
--   Definitions and structural lemmas for Of Real Vec Half Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OfRealVecHalfVec.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
def ChiAtU (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) : Prop :=
  ∀ n n' : Fin g → ℤ, ∃ (k k' : Fin g → ℤ) (c : ℂ), c ^ 4 = 1 ∧
    ∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ,
      theta (halfVec k) (halfVec k') (zAct γ τ z) (spAct γ τ) ^ 2 =
        c * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec n) (halfVec n') z τ ^ 2
end ReciprocityTheory.ChartRestriction.G.Key.Chi


