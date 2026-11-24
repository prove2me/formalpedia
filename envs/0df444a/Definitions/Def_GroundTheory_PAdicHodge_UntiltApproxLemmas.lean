-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
-- name    : GroundTheory_PAdicHodge_UntiltApproxLemmas
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:32.112217+00:00
-- url     : https://prove2.me/theorems/26b7a5fc-fe03-4daa-8487-b7f5ac918b0f
-- title:
--   Untilt Approx Lemmas
-- statement:
--   Definitions and structural lemmas for Untilt Approx Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
open Polynomial
section Conj
variable {F E : Type*} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
  [NormedField E] [NormedAlgebra F E]
end Conj
section Roots
variable {E : Type*} [NormedField E] [IsUltrametricDist E]
end Roots
section Tilt
variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField C p]
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
def monicOfCoeffs (e : ℕ) (a : ℕ → 𝒪C♭) : 𝒪C♭[X] :=
  X ^ e + ∑ m ∈ Finset.range e, Polynomial.C (a m) * X ^ m
end Tilt
section Scale
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [IsAlgClosed E]
end Scale
section IntermediateField
variable {K C : Type*} [NontriviallyNormedField K] [NormedField C] [NormedAlgebra K C]
instance normedAlgebraIntermediateField (F : IntermediateField K C) : NormedAlgebra F C where
  norm_smul_le r x := by
    rw [Algebra.smul_def, norm_mul]
    rfl
end IntermediateField
end GroundTheory.PAdicHodge


