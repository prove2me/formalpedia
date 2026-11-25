-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_CayleyIsometry
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_CayleyIsometry
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T11:29:52.886677+00:00
-- url     : https://prove2.me/theorems/bef31ef3-3231-513f-8dc4-cfb343c7393d
-- title:
--   Cayley Isometry
-- statement:
--   Definitions and structural lemmas for Cayley Isometry, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/CayleyIsometry.lean

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
open Matrix MvPolynomial
open scoped ComplexOrder
namespace DensPf
variable {n : ℕ}
def Pm (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Bool × Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => X (true, i, j) + C Complex.I * X (false, i, j)
def Qm (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Bool × Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => X (true, j, i) - C Complex.I * X (false, j, i)
def Lp (G : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) (MvPolynomial (Bool × Fin n × Fin n) ℂ) :=
  Pm n - G⁻¹.map C * Qm n * G.map C
def Mp (G : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) (MvPolynomial (Bool × Fin n × Fin n) ℂ) :=
  (1 - Lp G) * adjugate (1 + Lp G)
def dp (G : Matrix (Fin n) (Fin n) ℂ) : MvPolynomial (Bool × Fin n × Fin n) ℂ := det (1 + Lp G)
def hq (G : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial (Bool × Fin n × Fin n) ℂ :=
  ∑ d ∈ p.support, C (p.coeff d) * dp G ^ (p.totalDegree - d.degree) *
    ∏ i : Fin n × Fin n, Mp G i.1 i.2 ^ d i
end DensPf
end Formalism.L2.SG.Pf.ColDictValCPf


