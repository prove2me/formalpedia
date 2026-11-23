-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:30.624769+00:00
-- url     : https://prove2.me/theorems/c348874b-082d-4ea1-8fc5-866b67cf99ce
-- title:
--   HDisc BDefs
-- statement:
--   Definitions and structural lemmas for HDisc BDefs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscBDefs.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormDefs
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
noncomputable def fDivE (hd : d.AxH 𝒜) (h : d.S1) : KTf K d.D d.N :=
  ∏ c, ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nP h c d.wF (hd.a4.choose c) p
noncomputable def omE (hd : d.AxH 𝒜) (h : d.S1) : KTf K d.D d.N := d.De hd h * d.fDivE hd h ^ 2
def IsPres (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) : Prop :=
  b ≠ 0 ∧ algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a =
    d.De hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b ∧
  ∃ m : Fin (d.D + 1) → ℕ, m 0 = 0 ∧ ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m a ∧
    ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m b
noncomputable def mSgP (sg : K →+* ℂ) (a b : KTp K d.D d.N) : ℝ :=
  ∫ z, (Real.log ‖d.evT sg 0 (d.tOf z) a‖ - Real.log ‖d.evT sg 0 (d.tOf z) b‖)
    ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))
end Data
end ReciprocityTheory.ChartRestriction.G.T0


