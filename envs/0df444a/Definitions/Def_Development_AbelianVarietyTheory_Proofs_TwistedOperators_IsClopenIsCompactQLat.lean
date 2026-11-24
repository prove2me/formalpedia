-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:19.728686+00:00
-- url     : https://prove2.me/theorems/2ad14904-ecf0-4200-9fc6-c5f647b66261
-- title:
--   Is Clopen Is Compact QLat
-- statement:
--   Definitions and structural lemmas for Is Clopen Is Compact QLat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData
noncomputable section
namespace GlobalTheory.LastSteps
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type}
section Duals
variable [Fintype n] {L : Submodule 𝒪[k] (n → k)} {F : n → k}
end Duals
section Decomposition
variable [Fintype n'] {L : Submodule 𝒪[k] (n' → k)} {LY : Submodule 𝒪[k] (n → k)} {x₀ : Matrix n n' k}
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (P : Pair k n')
variable [LY.IsLattice k] (fW : {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0})
variable {M A : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup A] [Module ℂ A]
variable [DecidableEq n'] [Fintype n]
variable {π : Representation ℂ (GL n' k) M} {θ : M →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] A} {φ : Form k n' M}
end Decomposition
section Transform
variable [Fintype n]
variable [MeasurableSpace k] [BorelSpace k] (q : Unif k) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
  (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
include hψ
variable [Fintype n'] (ε : 𝒪[k]ˣ) (P : Pair k n') (x₀ : Matrix n n' k) (η : n → k)
end Transform
section Kernels
variable [Fintype n']
end Kernels
section Last
variable [Fintype n] [Fintype n'] (q : Unif k) (LY : Submodule 𝒪[k] (n → k)) [LY.IsLattice k]
  (L'' : Submodule 𝒪[k] (n'' → k)) [L''.IsLattice k] {M A : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup A]
  [Module ℂ A] (x' : Matrix n'' n k) (η : n → k)
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ε : 𝒪[k]ˣ)
  (μ : Measure (n → k)) [μ.IsAddHaarMeasure]
variable [DecidableEq n'] {L : Submodule 𝒪[k] (n' → k)} [L.IsLattice k] {φ : Form k n' M}
end Last
end GlobalTheory.LastSteps


