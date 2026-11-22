-- Prove2me | Definitions.Def_Formalism_TorsionNormIteration_LTLemma
-- name    : Formalism_TorsionNormIteration_LTLemma
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:42:57.0508+00:00
-- url     : https://prove2.me/theorems/ba2047d9-6e1a-4646-9968-648bd6de4855
-- title:
--   LTLemma
-- statement:
--   Definitions and structural lemmas for LTLemma, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/LTLemma.lean

import Definitions.Def_Formalism_TorsionNormIteration_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
namespace Formalism.LT
open Formalism.G
def LTLemma : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (p q : ℕ) (π : K), LTSetting K p q π →
    ∀ e e' : PowerSeries K, IsLTSeries q π e → IsLTSeries q π e' →
    ∀ (n : ℕ) (a : Fin n → K), (∀ i, ‖a i‖ ≤ 1) →
      ∃ φ : MvPowerSeries (Fin n) K, IntegralMv φ ∧ MvPowerSeries.constantCoeff φ = 0 ∧
        (∀ i, MvPowerSeries.coeff (Finsupp.single i 1) φ = a i) ∧
        e.subst φ = MvPowerSeries.subst (fun i => e'.subst (MvPowerSeries.X i)) φ ∧
        ∀ ψ : MvPowerSeries (Fin n) K, MvPowerSeries.constantCoeff ψ = 0 →
          (∀ i, MvPowerSeries.coeff (Finsupp.single i 1) ψ = a i) →
          e.subst ψ = MvPowerSeries.subst (fun i => e'.subst (MvPowerSeries.X i)) ψ → ψ = φ
end Formalism.LT


