-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLGeometry
-- name    : QEC_Coding_QuantumTanner_ArithmeticPSLGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:22:47.415371+00:00
-- url     : https://prove2.me/theorems/86ed6c7e-b901-4c7a-ab68-02c741474791
-- title:
--   Arithmetic PSLGeometry
-- statement:
--   Definitions and structural lemmas for Arithmetic PSLGeometry, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticPSLGeometry.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionPSLGenerators
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_pslLeft_injective
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_pslLeft_inverse
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_pslRight_injective
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_pslRight_inverse
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_psl_total_nonconjugacy

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner.ArithmeticPSLGeometry
open QEC.Coding.ExpanderCodes.QuaternionGenerators
universe v
variable {F K : Type v} [Field F] [Field K] [Fintype F] [Fintype K]
instance (priority := low) finitePSL :
    Fintype (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
  Fintype.ofFinite _
variable (f : F →+* K) (epsilon : F) (r y s i : K)
  (hEpsilon : epsilon ≠ 0) (hRoot : r ^ 2 = f epsilon)
  (hR : r ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
  (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
  (hRatio : s ^ 2 = y / (1 + y)) (hI : i ^ 2 = -1)
local notation "L" => pslLeft f epsilon r y s i hEpsilon hRoot hR hTwoF
  hY hOne hTwo hRatio hI
local notation "R" => pslRight f epsilon r y s i hEpsilon hRoot hR hTwoF
  hY hOne hTwo hRatio hI
def squareComplex :
    LeftRightCayleySquareComplex (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
      (TorusIndex epsilon) (TorusIndex epsilon) (CayleySquare L R) :=
  cayleySquareComplex L R (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
    (pslLeft_injective f epsilon r y s i hEpsilon hRoot hR hTwoF hY hOne hTwo hRatio hI)
    (pslRight_injective f epsilon r y s i hEpsilon hRoot hR hTwoF hY hOne hTwo hRatio hI)
    (pslLeft_inverse f epsilon r y s i hEpsilon hRoot hR hTwoF hY hOne hTwo hRatio hI)
    (pslRight_inverse f epsilon r y s i hEpsilon hRoot hR hTwoF hY hOne hTwo hRatio hI)
    (fun g a b => psl_total_nonconjugacy f epsilon r y s i hEpsilon hRoot hR hTwoF
      hY hOne hTwo hRatio hI a b g)
end QEC.Coding.QuantumTanner.ArithmeticPSLGeometry


