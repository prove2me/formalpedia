-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ComapDomainInlAdd
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ComapDomainInlAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:27.097132+00:00
-- url     : https://prove2.me/theorems/9e0e4df8-0306-455a-b324-1baedb2082d6
-- title:
--   Comap Domain Inl Add
-- statement:
--   Definitions and structural lemmas for Comap Domain Inl Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ComapDomainInlAdd.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
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
namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
abbrev Ix (m n : ℕ) := Fin m × Fin n × Bool
abbrev Dk (k : Ix m n) : Module.End ℂ (PX m n) := (pderiv (R := ℂ) k).toLinearMap
def dvE (e : Ix m n → ℕ) : Module.End ℂ (PX m n) :=
  ((Finset.univ : Finset (Ix m n)).toList.map fun k => Dk k ^ e k).prod
end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators


