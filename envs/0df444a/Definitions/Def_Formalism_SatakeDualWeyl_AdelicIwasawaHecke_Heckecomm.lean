-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckecomm
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckecomm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:25:46.371229+00:00
-- url     : https://prove2.me/theorems/6947d268-b0ff-400a-8c29-b8df431a03e1
-- title:
--   Heckecomm
-- statement:
--   Definitions and structural lemmas for Heckecomm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Heckecomm.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
namespace Formalism.UG.P
open Formalism.UG
section Gelfand
variable {G : Type} [Group G]
end Gelfand
section Transpose
variable {R : Type} [CommRing R] {n : ℕ}
def heckecomm_tr (g : GL (Fin n) R) : GL (Fin n) R :=
  ⟨Matrix.transpose (g : Matrix (Fin n) (Fin n) R), Matrix.transpose ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R),
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩
end Transpose
end Formalism.UG.P


