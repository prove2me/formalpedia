-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementF
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:21.004808+00:00
-- url     : https://prove2.me/theorems/b76e1f20-77cc-4894-b9b8-219855ac965d
-- title:
--   Statement F
-- statement:
--   Definitions and structural lemmas for Statement F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/StatementF.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementC
import Definitions.Def_Formalism_MahlerMeasure_StatementTM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M Formalism.GM
def DischargeP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (e1 : ℕ), kapC p r LL.total ≤ e1 → HypP p LL ρ e1
def DischargeW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (e1 : ℕ), kapC p r LL.total ≤ e1 → HypW p (r := r) LL e1
def DischargeE : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (e1 : ℕ), kapC p r LL.total ≤ e1 → HypE p LL ρ e1
def HeightBoundImplication : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (a : ℕ) (κ : ℝ),
    (∀ x, LL.deg x ≤ 2 * a) → 2 * a * N + r ≤ p ^ 2 * (8 * a + r) ^ 2 → ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ →
    HypP p LL ρ ⌈κ / (N + 2)⌉₊ ∧ HypW p (r := r) LL ⌈κ / (N + 2)⌉₊ ∧ HypE p LL ρ ⌈κ / (N + 2)⌉₊
end Formalism.InvariantFactorPaths.PW


