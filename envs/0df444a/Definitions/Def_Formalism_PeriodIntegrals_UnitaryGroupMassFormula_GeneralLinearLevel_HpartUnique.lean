-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T15:18:09.583902+00:00
-- url     : https://prove2.me/theorems/7dc782fc-9696-4a8a-8ed5-595c56d84cd5
-- title:
--   Hpart Unique
-- statement:
--   Definitions and structural lemmas for Hpart Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/HpartUnique.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
def Skew (X : Mx k r) : Prop := Xᴴ * Hpk k r + Hpk k r * X = 0
def LieL (k r : ℕ) (i : Fin (r + 1)) : Set (Mx k r) :=
  {X | Skew X ∧ ∀ a : Fin r, a.val < i.val →
    X *ᵥ bvec (eI k r a) = 0 ∧ X *ᵥ bvec (esI k r a) = 0}
def Out (k r : ℕ) (i : Fin (r + 1)) (p : Fin (2 * r + k + 1)) : Prop :=
  p.val < i.val ∨ 2 * r + k - i.val < p.val
def InV (k r : ℕ) (i : Fin (r + 1)) (Z : Mx k r) : Prop :=
  ∀ p q : Fin (2 * r + k + 1), (Out k r i p ∨ Out k r i q) → Z p q = 0
end Formalism.FourierDecayAlt.Q.EabGlW


