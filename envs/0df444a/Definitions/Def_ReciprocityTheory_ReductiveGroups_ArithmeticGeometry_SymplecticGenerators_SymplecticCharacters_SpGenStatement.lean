-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:59:16.441777+00:00
-- url     : https://prove2.me/theorems/832933dd-65a5-431a-adf5-bc191df5507f
-- title:
--   Sp Gen Statement
-- statement:
--   Definitions and structural lemmas for Sp Gen Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/SpGenStatement.lean

import Mathlib
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
def spTransl {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
  fromBlocks 1 S 0 1
def spDiag {g : ℕ} (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
  fromBlocks (U : Matrix (Fin g) (Fin g) ℤ) 0 0 ((↑U⁻¹ : Matrix (Fin g) (Fin g) ℤ)ᵀ)
def spGens (g : ℕ) : Set (Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :=
  {M | ∃ S : Matrix (Fin g) (Fin g) ℤ, S.IsSymm ∧ M = spTransl S} ∪
    {M | ∃ U : (Matrix (Fin g) (Fin g) ℤ)ˣ, M = spDiag U} ∪ {J (Fin g) ℤ}
def SpGenStatement : Prop :=
  ∀ g : ℕ, ∀ M ∈ symplecticGroup (Fin g) ℤ, M ∈ Submonoid.closure (spGens g)
end ReciprocityTheory.ChartRestriction.G.Key.Chi


