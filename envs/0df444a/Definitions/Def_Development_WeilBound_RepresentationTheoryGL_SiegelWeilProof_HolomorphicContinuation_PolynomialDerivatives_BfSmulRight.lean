-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:08.077297+00:00
-- url     : https://prove2.me/theorems/b8d82430-d8de-4750-8fd7-9adaaf4f5e31
-- title:
--   Bf Smul Right
-- statement:
--   Definitions and structural lemmas for Bf Smul Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BfSmulRight.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
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
namespace PositivityTheory.Rg.Sw.LC.CoreC.G
variable {τ : Type} [Fintype τ] [DecidableEq τ]
def gf (w : (τ →₀ ℕ) → ℂ) (p q : MvPolynomial τ ℂ) : ℂ :=
  ∑ s ∈ p.support ∪ q.support, star (p.coeff s) * q.coeff s * w s
variable (w : (τ →₀ ℕ) → ℂ)
variable {w} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
include hw
omit hw
def bf (w : (τ →₀ ℕ) → ℂ) (p q : MvPolynomial τ ℂ) : ℂ :=
  ∑ s ∈ p.support ∪ q.support, p.coeff s * q.coeff s * w s
end PositivityTheory.Rg.Sw.LC.CoreC.G


