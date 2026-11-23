-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_FunEqAll
-- name    : Formalism_PeriodIntegrals_FunEqAll
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:34.829798+00:00
-- url     : https://prove2.me/theorems/4a234354-4422-4e65-b083-931bc2894d61
-- title:
--   Fun Eq All
-- statement:
--   Definitions and structural lemmas for Fun Eq All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/FunEqAll.lean

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
open Classical
namespace PI.FunEqAll
def JetTdeg {σ : Type*} (m : σ →₀ ℕ) : ℕ := m.sum (fun _ k => k)
def jetLogG (l d : ℕ) [Fact l.Prime] {β : Type*} (v : ZMod d × β) : MvPowerSeries (ZMod d × β) ℂ_[l] :=
  fun m => ∑ e ∈ Finset.range (JetTdeg m + 1),
    if m = Finsupp.single (v.1 - 2 * (e : ZMod d), v.2) ((l ^ 2) ^ e) then (((l : ℂ_[l]) ^ e)⁻¹) else 0
def NonzeroIndexPlace {l : ℕ} [Fact l.Prime] (c : ℂ_[l]) : Prop :=
  c ∈ closure {x : ℂ_[l] | ∃ m : ℕ, 0 < m ∧ Nat.Coprime m l ∧ ∃ (ζ : ℂ_[l]) (a : Fin m → ℚ_[l]),
    ζ ^ m = 1 ∧ x = ∑ k, algebraMap ℚ_[l] ℂ_[l] (a k) * ζ ^ (k : ℕ)}
def InW {l : ℕ} [Fact l.Prime] (c : ℂ_[l]) : Prop := NonzeroIndexPlace c ∧ ‖c‖ ≤ 1
def zL (l d : ℕ) [Fact l.Prime] (s : ZMod d) : MvPowerSeries (ZMod d × Unit) ℂ_[l] :=
  jetLogG l d (s, ())
def zC (l d : ℕ) [Fact l.Prime] (c : Fin 3) (s : ZMod d) : MvPowerSeries (Fin 3 × ZMod d) ℂ_[l] :=
  MvPowerSeries.subst (fun k : ZMod d × Unit => (MvPowerSeries.X (c, k.1) : MvPowerSeries (Fin 3 × ZMod d) ℂ_[l]))
    (zL l d s)
def ExistsIntegralAdditionSeries (l d : ℕ) [Fact l.Prime] : Prop :=
  ∃ Fg : ZMod d → MvPowerSeries (Fin 3 × ZMod d) ℂ_[l],
    (∀ s n, InW (MvPowerSeries.coeff n (Fg s))) ∧
    ∀ s, MvPowerSeries.subst (fun k : ZMod d × Unit => Fg k.1) (zL l d s) = zC l d 0 s + zC l d 1 s
def Target : Prop := ∀ (l d : ℕ) [Fact l.Prime] [NeZero d], ExistsIntegralAdditionSeries l d
end PI.FunEqAll


