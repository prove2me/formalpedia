-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:14:41.372547+00:00
-- url     : https://prove2.me/theorems/62ff533f-ac80-44be-a060-25fd35b2605a
-- title:
--   Phi Int
-- statement:
--   Definitions and structural lemmas for Phi Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.M.PhiIntegrality
open MvPolynomial Finset
open MvPolynomial Finset
section
variable {p : ℕ} [hp : Fact p.Prime]
def Bnd {σ : Type} (B : ℝ) (u : MvPolynomial σ ℚ_[p]) : Prop := ∀ m, ‖u.coeff m‖ ≤ B
variable {σ : Type}
end
open MvPolynomial Finset
section
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}
def Contr (C : ℝ) (T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) : Prop :=
  ∀ B, 0 ≤ B → ∀ u, Bnd B u → Bnd (B * C) (T u)
end
open MvPolynomial Finset
section
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}
end
open MvPolynomial Finset
end Formalism.GM.M.PhiIntegrality
namespace Formalism.GM
end Formalism.GM


