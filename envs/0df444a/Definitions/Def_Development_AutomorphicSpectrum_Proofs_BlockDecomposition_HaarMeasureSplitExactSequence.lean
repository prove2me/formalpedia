-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureSplitExactSequence
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureSplitExactSequence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:31.041816+00:00
-- url     : https://prove2.me/theorems/8eea2c3b-1c77-4266-b71d-a3a77aca9a31
-- title:
--   Haar Measure Split Exact Sequence
-- statement:
--   Definitions and structural lemmas for Haar Measure Split Exact Sequence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarMeasureSplitExactSequence.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
namespace GlobalTheory.CompanionTheory.FiberInt
variable {A A' : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] [LocallyCompactSpace A']
  [T2Space A'] [SecondCountableTopology A'] [MeasurableSpace A'] [BorelSpace A']
noncomputable def periodized (π : A →+ A') (Γ' : AddSubgroup A') (lam : Measure A) (𝓖 : Set A) :
    Measure A' :=
  Measure.sum fun γ : Γ' => ((lam.restrict 𝓖).map π).map ((γ : A') + ·)
instance {π : A →+ A'} {Γ' : AddSubgroup A'} [Countable Γ'] {lam : Measure A} [SFinite lam]
    {𝓖 : Set A} : SFinite (periodized π Γ' lam 𝓖) := by
  unfold periodized; infer_instance
end GlobalTheory.CompanionTheory.FiberInt


