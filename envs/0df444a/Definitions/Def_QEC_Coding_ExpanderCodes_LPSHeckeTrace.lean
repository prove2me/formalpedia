-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
-- name    : QEC_Coding_ExpanderCodes_LPSHeckeTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:42:37.035192+00:00
-- url     : https://prove2.me/theorems/c290db14-fbff-45da-9a65-20a5dcec3eb7
-- title:
--   LPSHecke Trace
-- statement:
--   Definitions and structural lemmas for LPSHecke Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
  [Group G] [Fintype G] [Fintype W]
  [DecidableEq G]
noncomputable def cayleyHeckeElement
    (label : W → G) (p : ℂ) (n : ℕ) : MonoidAlgebra ℂ G :=
  (lpsHeckePolynomial ℂ p n).eval₂
    (algebraMap ℂ (MonoidAlgebra ℂ G)) (cayleyGeneratorSum label)
section LPS
open scoped MatrixGroups
variable {p : ℕ}
noncomputable def lpsFiniteHeckeElement
    (a : LPSResiduePrime p) (n : ℕ) :
    MonoidAlgebra ℂ PSL(2, ZMod a.q) :=
  cayleyHeckeElement (lpsQuaternionLabel a) (p : ℂ) n
end LPS
end QEC.Coding.TannerLiftedProduct


