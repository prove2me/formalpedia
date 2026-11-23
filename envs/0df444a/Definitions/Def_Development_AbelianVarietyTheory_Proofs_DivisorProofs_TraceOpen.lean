-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:35.403526+00:00
-- url     : https://prove2.me/theorems/0dc09116-5ad3-4b30-a4d0-ce515f63955e
-- title:
--   Trace Open
-- statement:
--   Definitions and structural lemmas for Trace Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TraceOpen.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneMemH0WeightZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace GlobalTheory.QSA
def TraceOpen (R : Type) [CommRing R] [TopologicalSpace R] (a b : R) : Prop :=
  ∀ g : ℍ[R, a, b], nrm g = 1 → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g →
    ∃ O : Set R, IsOpen O ∧ O.Nonempty ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t
def SqOpen (K : Type) [Monoid K] [TopologicalSpace K] : Prop :=
  ∀ V ∈ 𝓝 (1 : K), ∃ U ∈ 𝓝 (1 : K), ∀ r ∈ U, ∃ μ ∈ V, μ ^ 2 = r
end GlobalTheory.QSA


