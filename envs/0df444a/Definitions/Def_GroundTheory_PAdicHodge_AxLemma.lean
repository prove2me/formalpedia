-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_AxLemma
-- name    : GroundTheory_PAdicHodge_AxLemma
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T11:26:31.273794+00:00
-- url     : https://prove2.me/theorems/660c67cb-2c6a-4847-ac28-363a3bdaf597
-- title:
--   Ax Lemma
-- statement:
--   Definitions and structural lemmas for Ax Lemma, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.PAdicHodge
open Polynomial
noncomputable section
section Norms
variable {p : ℕ} [hp : Fact p.Prime]
end Norms
section Ultra
variable {E : Type*} [NormedField E] [IsUltrametricDist E]
end Ultra
section Key
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
end Key
section Induction
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
def axExponent (p k : ℕ) : ℝ := (p : ℝ) / ((p : ℝ) - 1) ^ 2 * (1 - ((p : ℝ) ^ k)⁻¹)
end Induction
section Ax
variable {p : ℕ} [hp : Fact p.Prime]
def axConstant (p : ℕ) : ℝ := (p : ℝ) ^ ((p : ℝ) / ((p : ℝ) - 1) ^ 2)
end Ax
section AxSenTate
open UniformSpace Topology
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
end AxSenTate
end
end GroundTheory.PAdicHodge


