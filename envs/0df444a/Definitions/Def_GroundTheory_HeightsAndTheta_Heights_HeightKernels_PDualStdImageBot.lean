-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdImageBot
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdImageBot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:23.530566+00:00
-- url     : https://prove2.me/theorems/ff2a491a-3629-4a60-a68a-c803b4a85878
-- title:
--   PDual Std Image Bot
-- statement:
--   Definitions and structural lemmas for PDual Std Image Bot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdImageBot.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_SingleMemDualLatticeStandard
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
namespace StandardDualImageBottom
open DualArithmeticVariety
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]
def genPt (K : Type) [Field K] (i : ℕ) : (Σ _ : Unit, Fin i) → ProjField K i :=
  fun q => algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X q.2)
omit [Fintype T] in

theorem aeval_eq_zero_of_mem (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    {f : MRing (dualBlocks T)} (hf : f ∈ dualIdeal b) : aeval (dualLatticeCoord b) f = 0 := by
  have h : ∀ g : MRing (dualBlocks T),
      MvPolynomial.eval (fun _ : Unit => (1 : ProjField K i)) (mConeMap (dualLatticeCoord b) g) =
        aeval (dualLatticeCoord b) g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp]
      simp [mConeMap]
  rw [← h f, show mConeMap (dualLatticeCoord b) f = 0 from hf, map_zero]
def evalQ (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    MvPolynomial Unit (MRing (dualBlocks T) ⧸ dualIdeal b) →+* ProjField K i :=
  eval₂Hom (Ideal.Quotient.lift _ (aeval (dualLatticeCoord b)).toRingHom
    fun _ hf => aeval_eq_zero_of_mem b hf) fun _ => 1
end StandardDualImageBottom
end
end GroundTheory.Heights₂.Heights


