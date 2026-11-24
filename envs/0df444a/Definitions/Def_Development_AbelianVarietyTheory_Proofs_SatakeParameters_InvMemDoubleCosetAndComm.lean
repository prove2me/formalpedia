-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:27:58.159392+00:00
-- url     : https://prove2.me/theorems/afd111d3-ab41-4cd9-97c9-7611343529ca
-- title:
--   Inv Mem Double Coset And Comm
-- statement:
--   Definitions and structural lemmas for Inv Mem Double Coset And Comm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
namespace GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
section Abstract
variable {V : Type} [AddCommGroup V] [Module L V] {σ : L →+* L}
def SelfDual (B : V →ₛₗ[σ] V →ₗ[L] L) (W : Submodule L V) (Λ : Set V) : Prop :=
  ∀ v, v ∈ Λ ↔ v ∈ W ∧ ∀ w ∈ Λ, B v w ∈ intL L
variable {B : V →ₛₗ[σ] V →ₗ[L] L} {W : Submodule L V} {Λ : Set V}
def perp (B : V →ₛₗ[σ] V →ₗ[L] L) (W : Submodule L V) (e f : V) : Submodule L V :=
  W ⊓ (LinearMap.ker (B e) ⊓ LinearMap.ker (B f))
def refl (B : V →ₛₗ[σ] V →ₗ[L] L) (w : V) (μ : L) : V →ₗ[L] V :=
  LinearMap.id - μ⁻¹ • (B w).smulRight w
end Abstract
section Matrices
variable {n : ℕ} {σ : L →+* L}
def form (σ : L →+* L) (J : Matrix (Fin n) (Fin n) L) : (Fin n → L) →ₛₗ[σ] (Fin n → L) →ₗ[L] L :=
  LinearMap.mk₂'ₛₗ σ (RingHom.id L) (fun u v => (σ ∘ u) ⬝ᵥ (J *ᵥ v))
    (fun u u' v => by
      rw [show σ ∘ (u + u') = σ ∘ u + σ ∘ u' from funext fun i => by simp, add_dotProduct])
    (fun c u v => by
      rw [show σ ∘ (c • u) = σ c • (σ ∘ u) from funext fun i => by simp, smul_dotProduct])
    (fun u v v' => by rw [Matrix.mulVec_add, dotProduct_add])
    (fun c u v => by rw [Matrix.mulVec_smul, dotProduct_smul]; rfl)
def intVec (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) : Set (Fin n → L) :=
  {v | ∀ i, v i ∈ intL L}
end Matrices
end GlobalTheory.UnitarySwap


