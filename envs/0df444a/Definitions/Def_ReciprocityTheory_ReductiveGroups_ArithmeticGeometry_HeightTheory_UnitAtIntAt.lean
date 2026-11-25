-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UnitAtIntAt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UnitAtIntAt
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:43:02.585748+00:00
-- url     : https://prove2.me/theorems/27c20490-6dbf-4463-8672-9a88bb1ea8fd
-- title:
--   Unit At Int At
-- statement:
--   Definitions and structural lemmas for Unit At Int At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/UnitAtIntAt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DiscLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
namespace LocAt
variable {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
def IntAt (p : Ideal R) (x : F) : Prop :=
  ∃ a s : R, s ∉ p ∧ x * algebraMap R F s = algebraMap R F a
def UnitAt (p : Ideal R) (x : F) : Prop :=
  ∃ a s : R, a ∉ p ∧ s ∉ p ∧ x * algebraMap R F s = algebraMap R F a
variable {p : Ideal R} [hP : p.IsPrime]
include hP
end LocAt
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


