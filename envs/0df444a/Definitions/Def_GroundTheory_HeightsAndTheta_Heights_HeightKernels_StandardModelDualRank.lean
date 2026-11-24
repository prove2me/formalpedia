-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:45.40394+00:00
-- url     : https://prove2.me/theorems/b419dccc-a618-4acd-8ee0-9e7e5b741d69
-- title:
--   Standard Model Dual Rank
-- statement:
--   Definitions and structural lemmas for Standard Model Dual Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField DualArithmeticVariety
noncomputable section
namespace StandardModelDualRank
variable {K : Type} [Field K] {i : ℕ}
abbrev gen (K : Type) [Field K] (i : ℕ) (j : Fin i) : ProjField K i :=
  algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j)
def embK (K : Type) [Field K] (i : ℕ) : K →+* dualStdModelField K i :=
  (dualStdModelEmb K i).comp (algebraMap K (ProjField K i))
def u (K : Type) [Field K] (i : ℕ) (j : Fin i) : dualStdModelField K i :=
  dualStdModelEmb K i (gen K i j) * dualStdModelS K i * dualStdModelT K i
def psiA (K : Type) [Field K] (i : ℕ) :
    MvPolynomial (Fin i) K →+* MvPolynomial Unit (MvPolynomial Unit (ProjField K i)) :=
  eval₂Hom (((C : MvPolynomial Unit (ProjField K i) →+* _).comp C).comp (algebraMap K (ProjField K i)))
    fun j => C (C (gen K i j)) * C (X ()) * X ()
def psi (K : Type) [Field K] (i : ℕ) : MvPolynomial (Fin i) K →+* dualStdModelField K i :=
  (algebraMap _ _).comp (psiA K i)
def psiZ (K : Type) [Field K] (i : ℕ) : MvPolynomial (Fin i) ℤ →+* dualStdModelField K i :=
  (psi K i).comp (MvPolynomial.map (Int.castRingHom K))
variable [NumberField K]
variable {T : Type}
def w (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (t : T) : dualStdModelField K i :=
  dualStdModelEmb K i (dualLatticeCoord b ⟨(), t⟩) * dualStdModelS K i * dualStdModelT K i
end StandardModelDualRank
end
end GroundTheory.Heights₂.Heights


