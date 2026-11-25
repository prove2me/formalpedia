-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
-- name    : Formalism_LocalToGlobal_CharacterGerms_AltInv
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:14:03.878875+00:00
-- url     : https://prove2.me/theorems/b26c0bd8-0a86-434c-8ba9-6e47d4a143ba
-- title:
--   Alt Inv
-- statement:
--   Definitions and structural lemmas for Alt Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AltInv.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
namespace Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))
def IntC (x : C) : Prop := 0 ≤ v x
def IntS {σ : Type*} (f : MvPowerSeries σ C) : Prop := ∀ μ, IntC v (coeff μ f)
variable {v}
variable {σ τ : Type*}
def LowLt {σ : Type*} (K : ℕ) (f : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, μ.degree < K → IntC v (coeff μ f)
def OrdV {σ : Type*} (D : ℕ) (f : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, μ.degree < D → coeff μ f = 0
end Formalism.L2.FormalSeriesBounds.AltInv


