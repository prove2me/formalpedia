-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableMonomial
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableMonomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:09:41.865889+00:00
-- url     : https://prove2.me/theorems/58b55ec9-5704-4912-af30-f58a3ad911fa
-- title:
--   Integrable Monomial
-- statement:
--   Definitions and structural lemmas for Integrable Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/IntegrableMonomial.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_OneMom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
namespace PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
def flip (k : Fin m × Fin n × Bool) : Fin m × Fin n × Bool := (k.1, k.2.1, !k.2.2)
def g1 (c : ℝ) (p q : ℕ) : ℂ := if p = q then ((Real.pi * (p.factorial : ℝ) / c ^ (p + 1) : ℝ) : ℂ) else 0
def phi (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ := ∏ a, ∏ i, g1 c (s (a, i, false)) (s (a, i, true))
def fac (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n) (z : ℂ) : ℂ :=
  z ^ s (a, i, false) * star z ^ s (a, i, true) * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))
variable (hM : OneMom)
end PositivityTheory.Rg.Sw.LC


