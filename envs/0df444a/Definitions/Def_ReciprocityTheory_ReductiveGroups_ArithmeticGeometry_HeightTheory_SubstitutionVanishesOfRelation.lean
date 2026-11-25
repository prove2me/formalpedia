-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionVanishesOfRelation
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionVanishesOfRelation
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:19:51.868671+00:00
-- url     : https://prove2.me/theorems/fad67178-07b6-55f4-9dec-c84bd2848c4c
-- title:
--   Substitution Vanishes Of Relation
-- statement:
--   Definitions and structural lemmas for Substitution Vanishes Of Relation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SubstitutionVanishesOfRelation.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionSplitIrreducibleOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
noncomputable def affineRowCombination (c : ι) (a : Fin (d.D + 2)) : MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c) :=
  ∑ k, X (a, k) * C (d.affineCoord c k)
noncomputable def pluckerSubstitution (c : ι) :
    MvPolynomial (TVar d.D d.N) (Ω c) →ₐ[Ω c] MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c) :=
  aeval fun t => d.affineRowCombination c 0 * X (t.1.succ, t.2) - d.affineRowCombination c t.1.succ * X (0, t.2)
end Data
end ReciprocityTheory.ChartRestriction.G.T0


