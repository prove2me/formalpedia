-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FiniteTranslateSets
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FiniteTranslateSets
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:01:16.093837+00:00
-- url     : https://prove2.me/theorems/771f235b-ff74-44cd-8160-fe5440cade6f
-- title:
--   Finite Translate Sets
-- statement:
--   Definitions and structural lemmas for Finite Translate Sets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FiniteTranslateSets.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace FiniteTranslateSets
open NumberField Module
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def Sh (R : ℝ) : Set E :=
  {β | ∃ α : 𝓞 E, (α : E) = (X.den : E) * β ∧ ∀ σ : E →+* ℂ, ‖σ (α : E)‖ ≤ R}
def Sz (T : ℝ) : Set ℤ := {n | ((n : ℝ)) ^ 2 ≤ T}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def TS (R T : ℝ) : Set ((ι → ι → E) × (Free.ChooseBasisIndex ℤ (𝓞 E) → ι → ι → ℤ)) :=
  {t | ∃ f : Basis ι ℤ X.Λ, ((∀ i j, (HermitianLatticeMaps.ty X f).1 i j ∈ Sh X R) ∧
    ∀ k i j, (HermitianLatticeMaps.ty X f).2 k i j ∈ Sz T) ∧ HermitianLatticeMaps.ty X f = t}
end FiniteTranslateSets
end ReciprocityTheory.ChartRestriction.G.FD


