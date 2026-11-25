-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StMajorantTransport
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StMajorantTransport
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:36:03.271341+00:00
-- url     : https://prove2.me/theorems/25ea8743-f2d9-534d-bc28-378b06168b2f
-- title:
--   St Majorant Transport
-- statement:
--   Definitions and structural lemmas for St Majorant Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StMajorantTransport.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def MajorantTransport.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ M : Majorant h v, ∃ (d : ℕ) (κ : ℝ), ∀ g : archUnitary h v,
    ∃ T : (InfinitePlace E → ι → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin d),
      (∀ y, ‖T y‖ = M.len (invApply g y)) ∧
      ∀ (L : Submodule ℤ (InfinitePlace E → ι → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L],
        ZLattice.covolume (ZLattice.comap ℝ L T.symm.toLinearMap) = κ * ZLattice.covolume L
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


