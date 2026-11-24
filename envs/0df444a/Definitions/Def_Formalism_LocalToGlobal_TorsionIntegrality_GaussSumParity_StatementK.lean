-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementK
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:51.582612+00:00
-- url     : https://prove2.me/theorems/02e9f3f9-5451-4f06-b2e9-c191029f5c05
-- title:
--   Statement K
-- statement:
--   Definitions and structural lemmas for Statement K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/StatementK.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_CMGoodModels_Statement
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
open Formalism.DworkPowerSeriesWeights (Unram)
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
def muPrime (l : ℕ) [Fact l.Prime] : Set ℂ_[l] := {ζ | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1}
def ringA (l : ℕ) [Fact l.Prime] : Subring ℂ_[l] := Subring.closure (muPrime l)
def ringB (l : ℕ) [Fact l.Prime] : Subring ℂ_[l] := (ringA l).topologicalClosure
def KurUnram : Prop := ∀ (l : ℕ) [Fact l.Prime], Unram l (MaximalUnramifiedExtension l)
def KurIntegers : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    (∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1) ∧
    (∀ x ∈ ringB l, ‖x‖ < 1 → ∃ y ∈ ringB l, x = (l : ℂ_[l]) * y) ∧
    (∀ x ∈ ringB l, ‖x‖ = 1 → x⁻¹ ∈ ringB l)
def KurRoots : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ¬ l ∣ n → ∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ n
def KurComplete : Prop := ∀ (l : ℕ) [Fact l.Prime], CompleteSpace (MaximalUnramifiedExtension l)
def KurFrob : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 2 < l →
    ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ ∧
      ∀ ζ : MaximalUnramifiedExtension l, (ζ : ℂ_[l]) ∈ muPrime l → σ ζ = ζ ^ l
def TrDualExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → Even d → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∃ om oms : Fin (d / 2) → K, OwOK d σ om oms ∧ TrDual d σ om oms
end Formalism.L2.Th1.D


