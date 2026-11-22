-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:13:53.3126+00:00
-- url     : https://prove2.me/theorems/9d7c7a7d-5f21-46b0-8e35-4296c9a91165
-- title:
--   Kernel Nonzero Modulus Determinant Eq
-- statement:
--   Definitions and structural lemmas for Kernel Nonzero Modulus Determinant Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
namespace Formalism.FourierDecayAlt.P.A5x5
section Index
variable {V W : Type} [AddCommGroup V] [AddCommGroup W]
def gi (A B : AddSubgroup V) : ℝ := (B.relIndex A : ℝ) / (A.relIndex B : ℝ)
variable [TopologicalSpace V] [IsTopologicalAddGroup V]
structure Lat (A : AddSubgroup V) : Prop where
  op : IsOpen (A : Set V)
  cp : IsCompact (A : Set V)
end Index
section Mod
variable {K : Type} [CommRing K] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K]
end Mod
section Mat
variable {K : Type} [CommRing K] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] {R : Subring K}
def mv (M : Matrix ι ι K) : (ι → K) →+ (ι → K) := M.mulVecLin.toAddMonoidHom
def LL (R : Subring K) (ι : Type) : AddSubgroup (ι → K) :=
  AddSubgroup.pi Set.univ (fun _ => R.toAddSubgroup)
def dl (R : Subring K) (M : Matrix ι ι K) : ℝ := gi ((LL R ι).map (mv M)) (LL R ι)
variable [TopologicalSpace K] [IsTopologicalRing K]
end Mat
section Block
variable {K : Type} [CommRing K] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] {R : Subring K}
def resL : (ι ⊕ Unit → K) →+ (ι → K) where
  toFun v i := v (Sum.inl i)
  map_zero' := rfl
  map_add' _ _ := rfl
def evR : (ι ⊕ Unit → K) →+ K where
  toFun v := v (Sum.inr ())
  map_zero' := rfl
  map_add' _ _ := rfl
end Block
section Elim
variable {K : Type} [CommRing K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K] {ψ : AddChar K ℂ}
def Good (R : Subring K) (ι : Type) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ M : Matrix ι ι K, IsUnit M.det → dl R M = modK R M.det
end Elim
section Kern
variable {K : Type} [CommRing K] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K] {ψ : AddChar K ℂ}
end Kern
end Formalism.FourierDecayAlt.P.A5x5
namespace Formalism.FourierDecayAlt.P
open A5x5
end Formalism.FourierDecayAlt.P


