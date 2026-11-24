-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ColumnMapShift
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_ColumnMapShift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:44.664852+00:00
-- url     : https://prove2.me/theorems/667cb408-ccfa-4dd3-b11f-abdae78c60fa
-- title:
--   Column Map Shift
-- statement:
--   Definitions and structural lemmas for Column Map Shift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ColumnMapShift.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
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
namespace GlobalTheory.Proof.ColumnMapShift
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
section Col
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
def colMap (r : T → ℕ) (g : T → Fin n → Fin n → k) :
    MvPolynomial (Letter T r n) k →ₐ[k] MvPolynomial (Letter T r n) k :=
  aeval fun ℓ : Letter T r n => ∑ b, C (g ℓ.1 b ℓ.2.2) * X (⟨ℓ.1, ℓ.2.1, b⟩ : Letter T r n)
open Classical in

def rowWt (n : ℕ) (σ : T) (i : Fin (r σ)) (ℓ : Letter T r n) : ℕ :=
  if (⟨ℓ.1, ℓ.2.1⟩ : Σ s, Fin (r s)) = ⟨σ, i⟩ then 1 else 0
end Col
end GlobalTheory.Proof.ColumnMapShift


