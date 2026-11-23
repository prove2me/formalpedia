-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PeriodLatticeCountable
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PeriodLatticeCountable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:54:23.418539+00:00
-- url     : https://prove2.me/theorems/ad699b4f-22e3-4bc5-a870-afccd2247466
-- title:
--   Period Lattice Countable
-- statement:
--   Definitions and structural lemmas for Period Lattice Countable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PeriodLatticeCountable.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
section Lattice
variable (X : Data E r) (la : Wt X.Ψ r)
noncomputable def perB : Module.Basis (Module.Free.ChooseBasisIndex ℤ (perL X la)) ℝ (X.Ψ → ℝ) :=
  (Module.Free.chooseBasis ℤ (perL X la)).ofZLatticeBasis ℝ (perL X la)
instance periods_countable : Countable (X.periods la) := inferInstanceAs (Countable (perL X la))
end Lattice
section Glue
variable (X : Data E r) (u : Fin 2 → Fin r → E)
def e00 (s : X.Ψ → ℝ) : X.Ψ → Fin 2 → Fin 2 → ℂ := fun τ i k => if i = 0 ∧ k = 0 then (s τ : ℂ) else 0
end Glue
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable


