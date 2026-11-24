-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_MeasurableSh
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_MeasurableSh
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:30.791147+00:00
-- url     : https://prove2.me/theorems/7dc897d7-205f-4f60-b258-7614447d7162
-- title:
--   Measurable Sh
-- statement:
--   Definitions and structural lemmas for Measurable Sh, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/SiegelWeilActions/MeasurableSh.lean

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_IsFirstChernFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.deprecated false
namespace PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum
variable {V A : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
  [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
def sh (Λ : (V × V) ≃ₜ+ (V × V)) (Q : V × V → A) (Z : V → V → A) (c : V × A) (p : V × (V × A)) : V × A :=
  (c.1 + (Λ (p.2.1, p.1)).2, c.2 + (p.2.2 + (Q (p.2.1, p.1) + Z c.1 (Λ (p.2.1, p.1)).1)))
end PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum
end


