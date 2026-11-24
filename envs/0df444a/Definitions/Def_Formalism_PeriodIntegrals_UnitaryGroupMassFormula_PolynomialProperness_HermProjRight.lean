-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:52:31.766206+00:00
-- url     : https://prove2.me/theorems/0f12b3ed-5f06-4a57-b9d4-9def152fb5bf
-- title:
--   Herm Proj Right
-- statement:
--   Definitions and structural lemmas for Herm Proj Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
namespace PI.PolynomialProperness.CoreW
def eN {n : ℕ} (x : Fin n → ℂ) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖
section form
variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
end form
section proj
variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
def coef (H : Matrix (Fin n) (Fin n) ℂ) (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    ι → ℂ :=
  Γi *ᵥ fun k => herm H y (p k)
def proj (H : Matrix (Fin n) (Fin n) ℂ) (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    Fin n → ℂ :=
  ∑ i, coef H Γi p y i • p i
end proj
end PI.PolynomialProperness.CoreW


