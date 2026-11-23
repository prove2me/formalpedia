-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvCotOfUnivDer
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvCotOfUnivDer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:21.450743+00:00
-- url     : https://prove2.me/theorems/84b187e5-d604-4230-a5a5-307bd640191a
-- title:
--   Ev Cot Of Univ Der
-- statement:
--   Definitions and structural lemmas for Ev Cot Of Univ Der, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvCotOfUnivDer.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
namespace GlobalTheory
namespace CotOf
variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}
variable (D : Dat p g B Tw Dt Oe σ cp)
section
variable (C : Type) [Field C] [Algebra (Tw.O : Type) C]
end
end CotOf
end GlobalTheory


