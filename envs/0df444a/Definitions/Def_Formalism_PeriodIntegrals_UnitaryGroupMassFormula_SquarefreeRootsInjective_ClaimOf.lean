-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_ClaimOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_ClaimOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:52:21.074412+00:00
-- url     : https://prove2.me/theorems/7ba20318-9568-4816-a4d6-14fb08305ff2
-- title:
--   Claim Of
-- statement:
--   Definitions and structural lemmas for Claim Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/ClaimOf.lean

import Definitions.Def_Formalism_PeriodIntegrals_SqfRootsInj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace PI.SqfRootsInj.W
open PI.SqfLab
def Lp (g e ℓ : ℕ) : ℕ := ℓ ^ padicValNat ℓ (g ^ e - 1)
def CaseA (g r ℓ : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : Prop :=
  ∃ (e j : ℕ) (w : Fbar g), 2 ≤ e ∧ e ≤ r ∧ 1 ≤ j ∧ 2 * j ≤ e ∧ ℓ ∣ g ^ e - 1 ∧
    (minpoly (ZMod g) w).natDegree = e ∧ minpoly (ZMod g) w ∣ f ∧
    w ^ ((g ^ j - 1) * Lp g e ℓ) = 1
def CaseB (g r ℓ : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : Prop :=
  ∃ (e e' : ℕ) (x y : Fbar g), 1 ≤ e' ∧ e' ≤ e ∧ e + e' ≤ r ∧
    ℓ ∣ (g ^ e - 1) * (g ^ e' - 1) ∧
    (minpoly (ZMod g) x).natDegree = e ∧ (minpoly (ZMod g) y).natDegree = e' ∧
    minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f ∧ y ^ (g ^ e') = y ∧
    x ^ Lp g e ℓ = (primeToPart ℓ y) ^ Lp g e ℓ
def Witness : Prop :=
  ∀ (g r : ℕ) [Fact g.Prime] (f : (ZMod g)[X]), Eii g r f →
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ BB r g ∧ (CaseA g r ℓ f ∨ CaseB g r ℓ f)
def Count : Prop :=
  ∀ (g r : ℕ) [Fact g.Prime], 100 ≤ r → 2 ^ 12 ≤ g →
    ∀ T : Finset (ZMod g)[X],
      (∀ f ∈ T, IsLab g r f ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ BB r g ∧ (CaseA g r ℓ f ∨ CaseB g r ℓ f)) →
      (T.card : ℝ) ≤ 23 * Real.log g * (g : ℝ) ^ (-(1 / 2 : ℝ)) * (g : ℝ) ^ r
end PI.SqfRootsInj.W


