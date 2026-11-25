-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivisorClosedHolds
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivisorClosedHolds
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:37.048868+00:00
-- url     : https://prove2.me/theorems/3debe670-f8b6-4e4c-a981-3a4db4a589ff
-- title:
--   Divisor Closed Holds
-- statement:
--   Definitions and structural lemmas for Divisor Closed Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/DivisorClosedHolds.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.SG.Pf.ColDictValCPf
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf Matrix MvPolynomial
open scoped ComplexOrder
section Div
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
def genAct (τ : ι) : MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ]
    MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (Fin n × Fin n) ℂ) :=
  aeval fun v => if v.1 = τ then ∑ c : Fin n, C (X (v.2.1, c)) * X (τ, c, v.2.2) else X v
def pushφ (φ : Module.Dual ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ))
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (Fin n × Fin n) ℂ)) :
    MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ m ∈ Q.support, φ (monomial m 1) • Q.coeff m
def elem (a b : Fin n) (t : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + replicateCol (Fin 1) (Pi.single b t) * replicateRow (Fin 1) (Pi.single a (1 : ℂ))
end Div
end Formalism.L2.SG.Pf.ColDictValCPf


