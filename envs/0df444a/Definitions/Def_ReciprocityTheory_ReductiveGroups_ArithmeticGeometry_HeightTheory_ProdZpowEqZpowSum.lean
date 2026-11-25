-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:14:21.098208+00:00
-- url     : https://prove2.me/theorems/c79cb270-d2cd-5691-8b8d-04317fa9b8b4
-- title:
--   Prod Zpow Eq Zpow Sum
-- statement:
--   Definitions and structural lemmas for Prod Zpow Eq Zpow Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ProdZpowEqZpowSum.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
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
noncomputable def cMM (h : d.S1) (c : ι) : KTf K d.D d.N :=
  ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p
noncomputable def aMM (h : d.S1) (c : ι) : ℤ :=
  ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
    d.nPMM h c (d.w (d.jc c) c) p * (d.dg (d.gen p) : ℤ)
end Data
end ReciprocityTheory.ChartRestriction.G.T0


