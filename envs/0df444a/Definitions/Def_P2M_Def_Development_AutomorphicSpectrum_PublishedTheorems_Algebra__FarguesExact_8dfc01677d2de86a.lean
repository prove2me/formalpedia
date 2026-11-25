-- Prove2me | Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__FarguesExact_8dfc01677d2de86a
-- name    : P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__FarguesExact_8dfc01677d2de86a
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:37.564856+00:00
-- url     : https://prove2.me/theorems/10578e88-8336-43ee-8063-de945f5f9901
-- title:
--   Fargues Exact
-- statement:
--   Definitions and structural lemmas for Fargues Exact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Algebra₂/FarguesExact.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.HT
open TensorProduct GlobalTheory.PDivGroup
def FarguesExact : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C] [Algebra ℤ_[p] O], v.Integers O → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : O)}) O → ∀ G : PDivGroup p O,
    ∀ (ζ : ℕ → O) (h0 : ζ 0 = 1) (h : ∀ n, ζ (n + 1) ^ p = ζ n), ζ 1 ≠ 1 →
      ∀ B : O ⊗[ℤ_[p]] G.Tate →ₗ[O] O ⊗[ℤ_[p]] G.dual.Tate →ₗ[O] O,
        (∀ (x : G.Tate) (χ : G.dual.Tate), ∃ a : ℤ_[p], pairing G O x χ = a • muTate O ζ h0 h ∧
          B (1 ⊗ₜ x) (1 ⊗ₜ χ) = algebraMap ℤ_[p] O a) →
        ∀ x, hodgeTateLinear G x = 0 ↔ ∀ y, dlogLinear G y = 0 → B x y = 0
end GlobalTheory.CompanionTheory.Ar.HT


