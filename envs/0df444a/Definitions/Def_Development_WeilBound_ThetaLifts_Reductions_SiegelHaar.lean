-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_SiegelHaar
-- name    : Development_WeilBound_ThetaLifts_Reductions_SiegelHaar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:43.605926+00:00
-- url     : https://prove2.me/theorems/6018737f-c76c-4c02-a8bd-676d1aa28d40
-- title:
--   Siegel Haar
-- statement:
--   Definitions and structural lemmas for Siegel Haar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulNn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory MeasureTheory.Measure Topology Set
open scoped NNReal ENNReal Pointwise
namespace PositivityTheory.ThKR.Sieg
section Retract
variable {H N : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
  [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
  [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N]
end Retract
section Heis
variable {A B : Type} [AddCommGroup A] [AddCommGroup B]
@[nolint unusedArguments]
def Heis (_ : A →+ A →+ B) : Type := A × B
variable (β : A →+ A →+ B)
instance : Group (Heis β) where
  mul x y := (x.1 + y.1, x.2 + y.2 + β x.1 y.1)
  one := (0, 0)
  inv x := (-x.1, -x.2 + β x.1 x.1)
  mul_assoc x y z := Prod.ext (add_assoc _ _ _) (by
    change x.2 + y.2 + β x.1 y.1 + z.2 + β (x.1 + y.1) z.1 = x.2 + (y.2 + z.2 + β y.1 z.1) + β x.1 (y.1 + z.1)
    simp only [map_add, AddMonoidHom.add_apply]
    abel)
  one_mul x := Prod.ext (zero_add _) (by change 0 + x.2 + β 0 x.1 = x.2; simp)
  mul_one x := Prod.ext (add_zero _) (by change x.2 + 0 + β x.1 0 = x.2; simp)
  inv_mul_cancel x := Prod.ext (neg_add_cancel _) (by
    change -x.2 + β x.1 x.1 + x.2 + β (-x.1) x.1 = 0; simp)
variable [TopologicalSpace A] [TopologicalSpace B]
instance : TopologicalSpace (Heis β) := inferInstanceAs (TopologicalSpace (A × B))
instance [T2Space A] [T2Space B] : T2Space (Heis β) := inferInstanceAs (T2Space (A × B))
instance [LocallyCompactSpace A] [LocallyCompactSpace B] : LocallyCompactSpace (Heis β) :=
  inferInstanceAs (LocallyCompactSpace (A × B))
instance [SecondCountableTopology A] [SecondCountableTopology B] : SecondCountableTopology (Heis β) :=
  inferInstanceAs (SecondCountableTopology (A × B))
instance [MeasurableSpace A] [MeasurableSpace B] : MeasurableSpace (Heis β) :=
  inferInstanceAs (MeasurableSpace (A × B))
instance [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B] [SecondCountableTopology A] :
    BorelSpace (Heis β) := inferInstanceAs (BorelSpace (A × B))
variable [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
variable [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
  [LocallyCompactSpace B] [SecondCountableTopology B] [T2Space B] [MeasurableSpace B] [BorelSpace B]
end Heis
section Bound
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {r : ℕ}
end Bound
end PositivityTheory.ThKR.Sieg
end


