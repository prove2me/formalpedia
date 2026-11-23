-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_DiagApply
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_DiagApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:19:49.161978+00:00
-- url     : https://prove2.me/theorems/041b5806-2281-4334-a5ec-3f1b891ce7c6
-- title:
--   Diag Apply
-- statement:
--   Definitions and structural lemmas for Diag Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/DiagApply.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SupPerp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.Rg.Sw.LC
namespace CoreA
variable {V : Type} [AddCommGroup V] [Module ℂ V] {φ : V → V → ℂ}
def diag (d : ℕ) : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (Fin d → V) where
  toFun f := LinearMap.pi fun k => f ∘ₗ LinearMap.proj k
  map_one' := LinearMap.ext fun w => funext fun k => by simp
  map_mul' f g := LinearMap.ext fun w => funext fun k => by simp
  map_zero' := LinearMap.ext fun w => funext fun k => by simp
  map_add' f g := LinearMap.ext fun w => funext fun k => by simp
  commutes' r := LinearMap.ext fun w => funext fun k => by simp
def amp (φ : V → V → ℂ) (d : ℕ) (v w : Fin d → V) : ℂ := ∑ k, φ (v k) (w k)
end CoreA
end PositivityTheory.Rg.Sw.LC


