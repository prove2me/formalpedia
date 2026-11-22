-- Prove2me | Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
-- name    : Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:11.257752+00:00
-- url     : https://prove2.me/theorems/07413cd7-f659-4f44-ab56-b32394a487a5
-- title:
--   Transfer
-- statement:
--   Definitions and structural lemmas for Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
namespace Formalism.BranchingDeterminantCap
open Formalism.HN
namespace PrismTransfer
section Basic
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
end Basic
end PrismTransfer
open PrismTransfer
namespace PrismTransfer
section Mat
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end Mat
end PrismTransfer
namespace PrismTransfer
section Maps
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
def rowMap {n : ℕ} (c : K) (x : Fin n → V →ₗ[K] V) : (Fin n → V) →ₗ[K] V :=
  ∑ i, (c • x i) ∘ₗ LinearMap.proj i
def colMap {n : ℕ} (c : K) (x : Fin n → V →ₗ[K] V) : V →ₗ[K] (Fin n → V) :=
  LinearMap.pi fun i => c • x i
variable {W κ : Type} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]
end Maps
section Lat
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
end Lat
end PrismTransfer
open PrismTransfer
end Formalism.BranchingDeterminantCap


