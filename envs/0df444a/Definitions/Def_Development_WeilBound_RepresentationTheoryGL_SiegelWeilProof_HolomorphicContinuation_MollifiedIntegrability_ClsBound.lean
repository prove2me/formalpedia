-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:41.390425+00:00
-- url     : https://prove2.me/theorems/01bb1091-4d56-42e6-b124-f3febb6d22bf
-- title:
--   Cls Bound
-- statement:
--   Definitions and structural lemmas for Cls Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
namespace PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
def ent (s : ℂ) (e : Bool × Fin n × Fin n) (y : E n) : ℂ := if e.1 then vM s y e.2.1 e.2.2 else uM s y e.2.1 e.2.2
def dEnt (s : ℂ) (k l : Fin n) (e : Bool × Fin n × Fin n) : MvPolynomial (Bool × Fin n × Fin n) ℂ :=
  if e.1 then -(C (Complex.I * s) * X (true, e.2.1, l) * X (true, k, e.2.2))
  else C (Complex.I * s) * X (false, e.2.1, l) * X (false, k, e.2.2)
def dR (s z : ℂ) (p q : ℕ) (k l : Fin n) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    MvPolynomial (Bool × Fin n × Fin n) ℂ :=
  C (Complex.I * s) * (C z * (X (false, k, l) - X (true, k, l)) + C (p : ℂ) * X (false, k, l) -
    C (q : ℂ) * X (true, k, l)) * R + ∑ e, MvPolynomial.pderiv e R * dEnt s k l e
end PositivityTheory.Rg.Sw.WR.B


