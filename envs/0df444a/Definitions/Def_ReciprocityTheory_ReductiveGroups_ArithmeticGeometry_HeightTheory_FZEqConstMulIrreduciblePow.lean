-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:06.143413+00:00
-- url     : https://prove2.me/theorems/b363e3ac-218e-4abe-b7eb-802a8e669739
-- title:
--   FZEq Const Mul Irreducible Pow
-- statement:
--   Definitions and structural lemmas for FZEq Const Mul Irreducible Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FZEqConstMulIrreduciblePow.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockSphereProbIsProbabilityMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
noncomputable def relationEliminateColumn (c : ι) : KTp K d.D d.N →ₐ[K] MvPolynomial (TVar d.D d.N) (Ω c) :=
  MvPolynomial.aeval fun t =>
    if t.2 = d.jc c then
      -∑ k ∈ Finset.univ.erase (d.jc c), MvPolynomial.X (t.1, k) *
        MvPolynomial.C (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c))
    else MvPolynomial.X t
end Data
end ReciprocityTheory.ChartRestriction.G.T0


