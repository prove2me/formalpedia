-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:18:54.127621+00:00
-- url     : https://prove2.me/theorems/e3901f40-0f94-4182-a6c7-7f8a806c18bf
-- title:
--   Restriction Local
-- statement:
--   Definitions and structural lemmas for Restriction Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
section Local
variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} (x : Fin (N + 1) → Ω) (y : Fin (N + 1) → K')
def locAt : Set Ω :=
  {a | ∃ (f s : Poly k N) (e : ℕ), f.IsHomogeneous e ∧ s.IsHomogeneous e ∧ aeval y s ≠ 0 ∧
    a = aeval x f / aeval x s}
open Classical in

def redAt (a : Ω) : K' :=
  if h : ∃ (p : Poly k N × Poly k N) (e : ℕ), p.1.IsHomogeneous e ∧ p.2.IsHomogeneous e ∧
      aeval y p.2 ≠ 0 ∧ a = aeval x p.1 / aeval x p.2
  then aeval y h.choose.1 / aeval y h.choose.2 else 0
variable {k x y}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
include hsp
end Local
section Specialize
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ}
end Specialize
end
end GroundTheory.Heights₂.Heights.Kleiman


