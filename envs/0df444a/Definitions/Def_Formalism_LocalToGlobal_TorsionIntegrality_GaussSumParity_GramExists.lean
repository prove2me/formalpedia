-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_GramExists
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_GramExists
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:32:30.344864+00:00
-- url     : https://prove2.me/theorems/815c1042-dcf4-43bf-ae9c-9c2b5b4bba83
-- title:
--   Gram Exists
-- statement:
--   Definitions and structural lemmas for Gram Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/GramExists.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
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
namespace Formalism.L2.Th1.D
open Formalism.InvariantFactorPaths.G7 (lgF at1 UnrOK)
def EigenOdd : Prop :=
  ∀ (K : Type) [Field K] (l d : ℕ) [NeZero d] (σ : K →+* K), 2 ≤ l → ∀ (ι : Type) [Fintype ι]
    (om oms : ι → K) (b : K) (c : ι → ι → K), (∀ r r', σ (σ (c r' r)) = c r' r) →
    (∀ r, b * oms r = ∑ r', σ (c r' r) * oms r') → ∀ s : ZMod d, s.val % 2 = 1 →
    MvPowerSeries.subst (fun x : Bool × ι => if x.1 = true then
        PowerSeries.subst (∑ r, MvPowerSeries.C (c x.2 r) * at1 (true, r) (lgF K l)) (expF K l)
        else (MvPowerSeries.X x : MvPowerSeries (Bool × ι) K)) (zXY l σ om oms s) =
      MvPowerSeries.C (σ^[s.val] b) * zXY l σ om oms s
def GramExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → (∃ ζ : K, IsPrimitiveRoot ζ (l ^ 2 - 1)) →
    ∀ (E : Type) [Fintype E] [DecidableEq E],
      ∃ c : Bool × E → Bool × E → K,
        (∀ k x, ‖c k x‖ ≤ 1 ∧ σ (σ (c k x)) = c k x) ∧
        ∀ x x' : Bool × E, ∑ k, c k x * σ (c k x') = if x.1 ≠ x'.1 ∧ x.2 = x'.2 then 1 else 0
end Formalism.L2.Th1.D


