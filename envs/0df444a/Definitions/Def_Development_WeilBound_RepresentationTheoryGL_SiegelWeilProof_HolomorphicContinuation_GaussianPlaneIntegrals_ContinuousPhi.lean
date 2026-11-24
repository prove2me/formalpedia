-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:11:47.241811+00:00
-- url     : https://prove2.me/theorems/576d9247-a697-46e8-a997-7a9e4b8da672
-- title:
--   Continuous Phi
-- statement:
--   Definitions and structural lemmas for Continuous Phi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ContinuousPhi.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralHkDiag
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
abbrev Sg (ι A B : Type) := (ι × A) ⊕ (ι × B)
def Phi (g : Matrix ι ι ℂ) (z : Sg ι A B → ℂ) : Sg ι A B → ℂ :=
  Sum.elim (fun x => z (Sum.inl x)) (fun y => ∑ j, g y.1 j * z (Sum.inr (j, y.2)))
def PhiL (g : Matrix ι ι ℂ) : (Sg ι A B → ℂ) →ₗ[ℝ] (Sg ι A B → ℂ) where
  toFun := Phi g
  map_add' z w := by
    funext s
    rcases s with x | y
    · rfl
    · simp [Phi, mul_add, Finset.sum_add_distrib]
  map_smul' c z := by
    funext s
    rcases s with x | y
    · rfl
    · simp only [Phi, Sum.elim_inr, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.real_smul, Complex.real_smul]
      ring
end PositivityTheory.Rg.Sw.FFTSteps.PosProof


