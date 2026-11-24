-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:58.777477+00:00
-- url     : https://prove2.me/theorems/b0087400-8413-46e7-8864-0545caa34af0
-- title:
--   Cay Div A
-- statement:
--   Definitions and structural lemmas for Cay Div A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
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
namespace PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
abbrev wz (n i : ℕ) : Fm n := MvPolynomial.C (Polynomial.X ^ i)
def cc (s : ℂ) (b : Bool) : ℂ := if b then Complex.I * s else -(Complex.I * s)
def aa (m : ℕ) (b : Bool) : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X
def RCP (T : Fm n →ₗ[ℂ] Fm n) : Prop := ∀ (R : Fm n) (q : Polynomial ℂ), T (R * MvPolynomial.C q) = T R * MvPolynomial.C q
def LCP (Q' : Fm n) (T : Fm n →ₗ[ℂ] Fm n) : Prop := ∀ R : Fm n, T (Q' * R) = Q' * T R
def AT (n : ℕ) : Subalgebra (Polynomial ℂ) (Fm n) :=
  Algebra.adjoin (Polynomial ℂ) (Set.range fun v : Fin n × Fin n => (MvPolynomial.X (true, v.1, v.2) : Fm n))
end PositivityTheory.Rg.Sw.SP


