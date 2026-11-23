-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:30:00.82435+00:00
-- url     : https://prove2.me/theorems/bbdb853a-1a4d-4861-8904-687dacc768d8
-- title:
--   Functional Representation By Contraction
-- statement:
--   Definitions and structural lemmas for Functional Representation By Contraction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FunctionalRepresentationByContraction.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_XPderivMono
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
namespace PositivityTheory.Rg.Sw.LC
namespace CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
def cand (ε : Fin m → Bool) (r : Fin m → ℕ) : Finset (Fin m × Fin n × Bool →₀ ℕ) :=
  ((Fintype.piFinset fun _ : Fin m × Fin n × Bool => Finset.range (∑ a, r a + 1)).image
    Finsupp.equivFunOnFinite.symm).filter (fun t => (∀ k ∈ t.support, inF1 ε k) ∧ rdeg ε t = r)
def Bm (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (s : Fin m × Fin n × Bool →₀ ℕ) : PX m n :=
  if ∀ k ∈ s.support, inF1 ε k then
    ∑ t ∈ cand ε (rdeg ε s), (Λ (monomial s 1 * monomial (t.mapDomain pE) 1) / (wt c t : ℂ)) • monomial t 1
  else 0
def Bop (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) : Module.End ℂ (PX m n) :=
  (MvPolynomial.basisMonomials (Fin m × Fin n × Bool) ℂ).constr ℂ (Bm ε c Λ)
end CoreC
end PositivityTheory.Rg.Sw.LC


