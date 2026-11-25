-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZMultiHomogeneousDegreeSum
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZMultiHomogeneousDegreeSum
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:29:19.556554+00:00
-- url     : https://prove2.me/theorems/110942c1-eab7-4673-bc7d-b2c315c07bf1
-- title:
--   FZMulti Homogeneous Degree Sum
-- statement:
--   Definitions and structural lemmas for FZMulti Homogeneous Degree Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FZMultiHomogeneousDegreeSum.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
section Swap
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
def swapT : TVar D N ≃ TVar D N := Equiv.prodCongr (Equiv.swap 0 1) (Equiv.refl _)
def swapS : (Fin (D + 1) × Fin N) ≃ (Fin (D + 1) × Fin N) :=
  Equiv.prodCongr (Equiv.swap 0 1) (Equiv.refl _)
end Swap
end ReciprocityTheory.ChartRestriction.G.T0
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
end Data
end ReciprocityTheory.ChartRestriction.G.T0


