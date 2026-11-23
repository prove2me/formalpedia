-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdDetMemHaO
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdDetMemHaO
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:50.476897+00:00
-- url     : https://prove2.me/theorems/1eb8ca9e-d27a-4359-b232-e3f04c167bcd
-- title:
--   Prod Det Mem Ha O
-- statement:
--   Definitions and structural lemmas for Prod Det Mem Ha O, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ProdDetMemHaO.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
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
open scoped BigOperators
open Classical MvPolynomial Formalism.L2.Pj Formalism.L2.Pj.Crude
namespace GlobalTheory.CombMinor
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k]
def cMat (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k) :
    Matrix (Fin s) (Fin s) (MvPolynomial (Letter Ty r n) k) :=
  Matrix.of fun ρ i : Fin s => ∑ b, C (B ρ b) * (X ⟨τ, Fin.castLE hs i, b⟩ : MvPolynomial (Letter Ty r n) k)
end GlobalTheory.CombMinor


