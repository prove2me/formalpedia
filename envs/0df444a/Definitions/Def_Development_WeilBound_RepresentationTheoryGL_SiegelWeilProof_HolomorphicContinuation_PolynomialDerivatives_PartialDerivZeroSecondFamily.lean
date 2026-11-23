-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:03.955089+00:00
-- url     : https://prove2.me/theorems/c302b68e-7b74-46a9-9cb5-1cfb0dd0b526
-- title:
--   Partial Deriv Zero Second Family
-- statement:
--   Definitions and structural lemmas for Partial Deriv Zero Second Family, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PartialDerivZeroSecondFamily.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
namespace PositivityTheory.Rg.Sw.LC
namespace CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
def pE : (Fin m × Fin n × Bool) ≃ (Fin m × Fin n × Bool) where
  toFun k := (k.1, k.2.1, !k.2.2)
  invFun k := (k.1, k.2.1, !k.2.2)
  left_inv k := by simp
  right_inv k := by simp
def piC (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ :=
  ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false)))
def Bal (s : Fin m × Fin n × Bool →₀ ℕ) : Prop := ∀ a i, s (a, i, false) = s (a, i, true)
instance (s : Fin m × Fin n × Bool →₀ ℕ) : Decidable (Bal s) := by unfold Bal; infer_instance
end CoreC
end PositivityTheory.Rg.Sw.LC


