-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:27.162709+00:00
-- url     : https://prove2.me/theorems/d2d4220b-8f1c-4e7d-8ad0-ad0d7e06f3e4
-- title:
--   Apply Word Mem Dual Weyl
-- statement:
--   Definitions and structural lemmas for Apply Word Mem Dual Weyl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQBilin
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
namespace GlobalTheory.WeylDuality
theorem fockQ_symm {σ : Type} (f g : MvPolynomial σ ℚ) : fockQ f g = fockQ g f := by
  exact (fockQPos σ f g).1
def fockB (σ : Type) : LinearMap.BilinForm ℚ (MvPolynomial σ ℚ) :=
  LinearMap.mk₂ ℚ fockQ (fun f f' g => (fockQBilin σ f f' g 1).1)
    (fun c f g => (fockQBilin σ f 0 g c).2)
    (fun f g g' => by rw [fockQ_symm, (fockQBilin σ g g' f 1).1, fockQ_symm g, fockQ_symm g'])
    (fun c f g => by rw [fockQ_symm, (fockQBilin σ g 0 f c).2, fockQ_symm g]; rfl)
def normB {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : LinearMap.BilinForm ℚ (dualWeyl ℚ r n ν) :=
  (fockQ (hw ℚ hn ν) (hw ℚ hn ν))⁻¹ • (fockB _).restrict (dualWeyl ℚ r n ν)
def inV {r n : ℕ} (ν : Fin n → ℕ) (M : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ)) :
    Submodule ℤ (dualWeyl ℚ r n ν) :=
  M.comap ((dualWeyl ℚ r n ν).subtype.restrictScalars ℤ)
end GlobalTheory.WeylDuality


