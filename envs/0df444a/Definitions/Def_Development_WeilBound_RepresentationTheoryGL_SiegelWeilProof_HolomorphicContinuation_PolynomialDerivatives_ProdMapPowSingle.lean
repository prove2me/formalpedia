-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:31.693637+00:00
-- url     : https://prove2.me/theorems/d9fbac59-9271-40eb-8778-3d28bdb58b41
-- title:
--   Prod Map Pow Single
-- statement:
--   Definitions and structural lemmas for Prod Map Pow Single, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean

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
open MvPolynomial
namespace PositivityTheory.Rg.Sw.LC.CoreBb
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
def Dfun (e : Fin m × Fin n × Bool → ℕ) : Module.End ℂ (PX m n) :=
  ((Finset.univ : Finset (Fin m × Fin n × Bool)).toList.map fun k => (pderiv (R := ℂ) k).toLinearMap ^ (e k)).prod
def opL (s : Sym m n) : Module.End ℂ (PX m n) :=
  ∑ t ∈ s.support, s.coeff t •
    (LinearMap.mulLeft ℂ (monomial (t.comapDomain Sum.inl Sum.inl_injective.injOn) 1 : PX m n) ∘ₗ
      Dfun (fun k => t (Sum.inr k)))
end PositivityTheory.Rg.Sw.LC.CoreBb


