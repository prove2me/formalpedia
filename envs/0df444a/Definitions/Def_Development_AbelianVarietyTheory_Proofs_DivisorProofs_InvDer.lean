-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvDer
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvDer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:18.063221+00:00
-- url     : https://prove2.me/theorems/5e86897c-822c-4313-a688-86e930c502c8
-- title:
--   Inv Der
-- statement:
--   Definitions and structural lemmas for Inv Der, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvDer.lean

import Mathlib
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
open MvPowerSeries
namespace GlobalTheory.LawDer
variable {R : Type} [CommRing R] {d : ℕ}
def atZero (H : MvPowerSeries (Fin d ⊕ Fin d) R) : MvPowerSeries (Fin d) R :=
  subst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun _ => 0) H
def invDer (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (u : Fin d → R)
    (F : MvPowerSeries (Fin d) R) : MvPowerSeries (Fin d) R :=
  ∑ i, u i • atZero (pderiv R (Sum.inr i) (subst μ F))
end GlobalTheory.LawDer


