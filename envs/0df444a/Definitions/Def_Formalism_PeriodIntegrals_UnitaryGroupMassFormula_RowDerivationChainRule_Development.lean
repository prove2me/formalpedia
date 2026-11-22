-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:20.79477+00:00
-- url     : https://prove2.me/theorems/a2751626-2517-4f97-819b-9f33d2e48045
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowDerivationChainRule/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowLetter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace PI.RL.W
open PI.RL
def ChainRule : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (vec : Bool) (a b : Fin (m + 1)) (P : MvPolynomial (Fin (m + 1)) K),
    RE K (m + 1) a b (theta K m vec P) =
      ∑ c, theta K m vec (pderiv c P) * RE K (m + 1) a b (Nv K m vec c)
def VecX : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (a b c : Fin (m + 1)),
    RE K (m + 1) a b (Nv K m true c) = if c = b then Nv K m true a else 0
def KeyCov : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (a b c : Fin (m + 1)),
    RE K (m + 1) a b (Nv K m false c) =
      (if a = b then Nv K m false c else 0) - (if a = c then Nv K m false b else 0)
def HdHom : Prop :=
  ∀ (K : Type) [Field K] (k d : ℕ) (P : MvPolynomial (Fin k) K), P ∈ Hd K k d → P.IsHomogeneous d
end PI.RL.W


