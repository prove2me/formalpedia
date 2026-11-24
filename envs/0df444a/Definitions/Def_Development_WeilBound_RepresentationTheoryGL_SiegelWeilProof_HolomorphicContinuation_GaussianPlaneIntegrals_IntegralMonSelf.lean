-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralMonSelf
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralMonSelf
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T13:27:19.141799+00:00
-- url     : https://prove2.me/theorems/92d2bb60-48fb-4086-a7b0-71744598a6df
-- title:
--   Integral Mon Self
-- statement:
--   Definitions and structural lemmas for Integral Mon Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/IntegralMonSelf.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate
namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
def mon (m : Sg ι A B →₀ ℕ) (z : Sg ι A B → ℂ) : ℂ := ∏ s, z s ^ m s
def kap (d : ι → ℝ) : Sg ι A B → ℝ := Sum.elim (fun _ => 1) (fun y => d y.1)
def lam (d : ι → ℝ) (m : Sg ι A B →₀ ℕ) : ℝ := ∏ s, kap d s ^ m s
end PositivityTheory.Rg.Sw.FFTSteps.PosProof


