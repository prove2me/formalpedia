-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:13.850061+00:00
-- url     : https://prove2.me/theorems/47730faa-c323-4d7c-b3cc-d2a8aa928734
-- title:
--   Type Int
-- statement:
--   Definitions and structural lemmas for Type Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/TypeInt.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames
section gen
variable {K U V : Type} [Field K] [CharZero K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
def pr0 (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) : Module.End K (U →ₗ[K] V) :=
  ∑ ν ∈ S, postC (G₂.comp ν) * preC (G₁.comp ν)
def Psi (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (l : ℕ) : Module.End K (U →ₗ[K] V) :=
  InvOp (homAct G₁.E G₂.E) l (List.finRange n) * pr0 G₁ G₂ S
noncomputable def QQ (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (l : ℕ) {k : ℕ}
    (b : Module.Basis (Fin k) K U) : V →ₗ[K] V :=
  (k : K) • ∑ i, LinearMap.applyₗ (b i) ∘ₗ Psi G₁ G₂ S l ∘ₗ LinearMap.smulRightₗ (b.coord i)
end gen
section iso
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}
end iso
section padic
variable (p : ℕ) [Fact p.Prime] {U V : Type} [AddCommGroup U] [Module ℚ_[p] U] [AddCommGroup V] [Module ℚ_[p] V]
  {n : ℕ}
end padic
end Formalism.InvariantFactorPaths.PW


