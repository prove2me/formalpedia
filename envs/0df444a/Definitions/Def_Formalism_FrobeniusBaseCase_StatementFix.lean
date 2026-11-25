-- Prove2me | Definitions.Def_Formalism_FrobeniusBaseCase_StatementFix
-- name    : Formalism_FrobeniusBaseCase_StatementFix
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:14:51.499984+00:00
-- url     : https://prove2.me/theorems/86bbcdcd-a481-4770-8c0a-d3a865347d26
-- title:
--   Statement Fix
-- statement:
--   Definitions and structural lemmas for Statement Fix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/StatementFix.lean

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
namespace Formalism.BaseCaseIdentities
noncomputable section
open Classical
namespace Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)
def UnitEntryAll : Prop :=
  ∀ (s : ℕ), 1 ≤ s → s < D.K → ∀ (c : C), D.lev c = s → ∀ (P : Z → k),
    D.m s c = MvPowerSeries.C ((-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹) *
      ∑ d, MvPowerSeries.C (P d) * X d ^ (D.q ^ s) →
    ∀ d : Z, D.v (P d) = 0 → ¬ D.InW D.zvec
def StartEqZ : Prop :=
  (∀ (s : ℕ) (c : C), 1 ≤ s → s < D.K → D.lev c = s → D.m s c = 0) → D.start = D.zvec
def LogEq (t : C → MvPowerSeries Z k) : Prop :=
  ∀ (b : C) (A : Z →₀ ℕ) (N : ℕ), A.degree ≤ N →
    coeff A (t b + ∑ c, ∑ j ∈ Finset.Icc 1 N, MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j)) =
      coeff A (D.zvec b)
def LogIffFix : Prop := ∀ t : C → MvPowerSeries Z k, NoConst t → (D.LogEq t ↔ D.Psi t = t)
def LogUnique : Prop := ∃! t : C → MvPowerSeries Z k, NoConst t ∧ D.LogEq t
def ChainIILog : Prop := ∀ t : C → MvPowerSeries Z k, NoConst t → D.LogEq t → D.InW t
end Data
end
end Formalism.BaseCaseIdentities


