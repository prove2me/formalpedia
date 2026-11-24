-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:30.665053+00:00
-- url     : https://prove2.me/theorems/39343cb0-daf3-4503-bc64-6c479464a286
-- title:
--   Eq Zero Of Fisch Self
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Fisch Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqZeroOfFischSelf.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RowSpan
open MvPolynomial Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
def rowAct (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) k) :
    MvPolynomial (Letter T r n) k →ₐ[k] MvPolynomial (Letter T r n) k :=
  aeval fun ℓ => ∑ j, C (g ℓ.1 ℓ.2.1 j) * X ⟨ℓ.1, j, ℓ.2.2⟩
def RowStable (U : Submodule k (MvPolynomial (Letter T r n) k)) : Prop :=
  ∀ g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) k, (∀ σ, IsUnit (g σ).det) → ∀ P ∈ U, rowAct g P ∈ U
section Fischer
variable {σ : Type}
def fisch : MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ →ₗ[ℚ] ℚ :=
  (basisMonomials σ ℚ).constr ℚ fun m => ((m.prod fun _ e => e.factorial : ℕ) : ℚ) • lcoeff ℚ m
end Fischer
section Lower
variable {σ : Type} (w : σ → ℕ)
end Lower
def rowOf (ℓ : Letter T r n) : (Σ σ, Fin (r σ)) := ⟨ℓ.1, ℓ.2.1⟩
end GlobalTheory.RowSpan


