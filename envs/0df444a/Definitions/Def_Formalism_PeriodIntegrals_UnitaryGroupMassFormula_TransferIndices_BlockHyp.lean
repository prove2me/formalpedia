-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:54.679628+00:00
-- url     : https://prove2.me/theorems/c9d3cccf-7311-44b7-9f8a-13393717ed55
-- title:
--   Block Hyp
-- statement:
--   Definitions and structural lemmas for Block Hyp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/BlockHyp.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemTer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
section Cut
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
end Cut
section Block
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {n : ℕ}
def Φt (Φ : Fin n → V →ₗ[K] V) : (Fin n → V) →ₗ[K] V := ∑ i, Φ i ∘ₗ LinearMap.proj i
structure BlockHyp (X Y : Submodule K V) (Φ Ψ : Fin n → V →ₗ[K] V) (Γ : Matrix (Fin n) (Fin n) K) : Prop where
  det : Γ.det ≠ 0
  h1 : ∀ i j, ∀ x ∈ X, Ψ j (Φ i x) = Γ j i • x
  h2 : ∀ i, ∀ x ∈ X, Φ i x ∈ Y
  h3 : ∀ j, ∀ y ∈ Y, Ψ j y ∈ X
  h4 : ∀ y ∈ Y, ∃ x : Fin n → V, (∀ i, x i ∈ X) ∧ y = ∑ i, Φ i (x i)
variable {X Y : Submodule K V} {Φ Ψ : Fin n → V →ₗ[K] V} {Γ : Matrix (Fin n) (Fin n) K}
end Block
end PI.Dv.TIW


