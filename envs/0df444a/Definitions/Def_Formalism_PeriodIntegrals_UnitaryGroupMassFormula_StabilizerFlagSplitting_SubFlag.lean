-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:27:08.572804+00:00
-- url     : https://prove2.me/theorems/d338eb84-9906-430b-b376-315cefd8b018
-- title:
--   Sub Flag
-- statement:
--   Definitions and structural lemmas for Sub Flag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/SubFlag.lean

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
namespace PI.StabSplit
def Xsp (k r : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun a : Fin r => bvec (eI k r a))
def FixSub : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → FixSet k r z ⊆ Sset k r z
def SubFlag : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → Sset k r z ⊆ FlagStab k r z
def UnipN : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), StdZ k r z →
    ∀ g ∈ Sset k r z, ∀ p : ℕ, (g - 1) ^ p = 0 → g ∈ Nset k r
def NPerp : Prop :=
  ∀ (k r : ℕ), ∀ g ∈ Nset k r, ∀ v : Fin (2 * r + k + 1) → ℂ,
    (∀ a : Fin r, herm (Hpk k r) v (bvec (eI k r a)) = 0) → (g - 1) *ᵥ v ∈ Xsp k r
end PI.StabSplit


