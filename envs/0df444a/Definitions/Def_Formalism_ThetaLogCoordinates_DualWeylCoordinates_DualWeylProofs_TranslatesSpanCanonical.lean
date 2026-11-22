-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:30:36.924294+00:00
-- url     : https://prove2.me/theorems/eb0f239b-457a-4ee1-8277-d2edfe898943
-- title:
--   Translates Span Canonical
-- statement:
--   Definitions and structural lemmas for Translates Span Canonical, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/TranslatesSpanCanonical.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]
def translatesSpanCanonical (mu : Fin n → ℤ) : Submodule ℚ (MvPolynomial (Fin n × Fin n) ℚ) :=
  Submodule.span ℚ {f | ∃ g : Matrix (Fin n) (Fin n) ℚ, IsUnit g.det ∧ f = rowAct ℚ g (qd_P mu (canT mu))}
def qd_Lam (mu : Fin n → ℤ) : (TIdx mu → ℚ) →ₗ[ℚ] GLCoord ℚ n :=
  Fintype.linearCombination ℚ (fun K : TIdx mu => mapCoord ℚ (brk mu K))
def qd_gcan (mu : Fin n → ℤ) (γ : GL (Fin n) ℚ) : TIdx mu → ℚ := fun K => evGL γ (TMat mu K (canT mu))
end Formalism.InvariantFactorPaths.ColumnFamilies


