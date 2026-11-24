-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EnvelopingAlgebraGrowthBound
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EnvelopingAlgebraGrowthBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:52.521294+00:00
-- url     : https://prove2.me/theorems/0d44f3fb-db3b-4554-a5b7-7e14b7ad35c1
-- title:
--   Enveloping Algebra Growth Bound
-- statement:
--   Definitions and structural lemmas for Enveloping Algebra Growth Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EnvelopingAlgebraGrowthBound.lean

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
namespace PositivityTheory.CW
namespace IdentityFiltrationBound
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
def W (n k : ℕ) : Finset (List (Fin n × Fin n)) := (List.finite_length_le (Fin n × Fin n) k).toFinset
def wd (E : Fin n → Fin n → Module.End ℂ V) (l : List (Fin n × Fin n)) : Module.End ℂ V :=
  (l.map fun p => E p.1 p.2).prod
def N (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) (v : V) : ℝ := ∑ l ∈ W n k, ‖wd E l v‖
end IdentityFiltrationBound
end PositivityTheory.CW
end


