-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_PowSpan
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_PowSpan
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:16.645256+00:00
-- url     : https://prove2.me/theorems/fcf37835-1da5-493d-a86a-bf97b91bd611
-- title:
--   Pow Span
-- statement:
--   Definitions and structural lemmas for Pow Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/PowSpan.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PositivityTheory.Rg.Sw.FFTSteps
namespace PowSpanB
variable {m n : ℕ} (ε : Fin m → Bool)
def lf (b : Matrix (Fin n) (Fin n) ℂ) : PX m n := ∑ i, ∑ j, b i j • (Qp ε j i : PX m n)
def W : Set (PX m n) := {w | ∃ h : Matrix (Fin n) (Fin n) ℂ, h.IsHermitian ∧ w = lf ε h}
def S : Submodule ℂ (PX m n) :=
  Submodule.span ℂ {R | ∃ (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ), b.IsHermitian ∧
    R = (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ^ k}
end PowSpanB
end PositivityTheory.Rg.Sw.FFTSteps


