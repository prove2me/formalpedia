-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartFinite
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T09:21:32.887247+00:00
-- url     : https://prove2.me/theorems/33ed6a18-972b-4d26-9ecf-ad8ac340d607
-- title:
--   PChart Finite
-- statement:
--   Definitions and structural lemmas for PChart Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PFGNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormMultiHomog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace ChartFinite
variable {F : Type} [Field F] {n e : ℕ}
def lineVar (t : Fin n → F) (m : Fin n) (ij : Fin (e + 1) × Fin n) :
    Polynomial (MvPolynomial (Fin e × Fin n) F) :=
  Fin.cases (motive := fun _ => Polynomial (MvPolynomial (Fin e × Fin n) F))
    (Polynomial.C (C (t ij.2)) * Polynomial.X - Polynomial.C (C (if ij.2 = m then 1 else 0)))
    (fun i => Polynomial.C (X (i, ij.2))) ij.1
def linePoly (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F) (m : Fin n) :
    Polynomial (MvPolynomial (Fin e × Fin n) F) :=
  aeval (lineVar t m) f
end ChartFinite
end
end GroundTheory.Heights₂.Heights


