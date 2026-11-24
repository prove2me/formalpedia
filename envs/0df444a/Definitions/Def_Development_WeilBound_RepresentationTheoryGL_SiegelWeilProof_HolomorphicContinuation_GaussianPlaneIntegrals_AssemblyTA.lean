-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTA
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTA
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:54:55.11627+00:00
-- url     : https://prove2.me/theorems/e0008f91-e47d-4e66-b338-41882328b979
-- title:
--   Assembly TA
-- statement:
--   Definitions and structural lemmas for Assembly TA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyTA.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ComplexOrder
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmA
variable {ι A B : Type} [Fintype ι]
def act (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) : (ι × A) ⊕ (ι × B) → ℂ :=
  Sum.elim (fun x => ∑ j, g x.1 j * z (Sum.inl (j, x.2))) (fun y => ∑ j, h y.1 j * z (Sum.inr (j, y.2)))
end PositivityTheory.Rg.Sw.FFTSteps.AsmA


