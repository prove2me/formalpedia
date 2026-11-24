-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:47.898356+00:00
-- url     : https://prove2.me/theorems/bf1a721f-5c90-4ba8-bf79-25a9b7ba07a1
-- title:
--   Mem Left Highest Weight Of Is Minimal Joint Vector
-- statement:
--   Definitions and structural lemmas for Mem Left Highest Weight Of Is Minimal Joint Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
namespace PI.FJMP
open PI.FJM
section Gen
variable {σ : Type*}
def NoVar (P : MvPolynomial σ ℂ) (v : σ) : Prop := ∀ e ∈ P.support, e v = 0
variable {κ : Type*} [Fintype κ]
def gR (u v : κ → σ) (pos : κ → Bool) (P : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ c, if pos c = true then X (u c) * pderiv (v c) P else -(X (v c) * pderiv (u c) P)
def sw (e : σ →₀ ℕ) (w : κ → σ) (pos : κ → Bool) : ℤ :=
  ∑ c, if pos c = true then (e (w c) : ℤ) else -(e (w c) : ℤ)
end Gen
end PI.FJMP


