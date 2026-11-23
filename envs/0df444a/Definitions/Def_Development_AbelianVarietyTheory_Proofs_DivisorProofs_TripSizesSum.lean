-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TripSizesSum
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_TripSizesSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:47.70072+00:00
-- url     : https://prove2.me/theorems/77d3d87a-0b81-455e-9a01-372dc18e1d7f
-- title:
--   Trip Sizes Sum
-- statement:
--   Definitions and structural lemmas for Trip Sizes Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TripSizesSum.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.SmGL
namespace GlobalTheory.CuspBlock
def tripSizes (l d N : ℕ) : Fin 3 → ℕ := ![l, d, N - (l + d)]
theorem tripSizes_sum {l d N : ℕ} (h : l + d ≤ N) : ∑ j, tripSizes l d N j = N := by
  simp only [tripSizes, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  omega
def tripPlace {l d N : ℕ} (h : l + d ≤ N) : (Σ j : Fin 3, Fin (tripSizes l d N j)) ≃ Fin N :=
  finSigmaFinEquiv.trans (finCongr (tripSizes_sum h))
variable (k : Type) [CommRing k]
def midHom (l d N : ℕ) : GL (Fin d) k →* Levi k (fun j : Fin 3 => Fin (tripSizes l d N j)) :=
  MonoidHom.mulSingle (fun j : Fin 3 => GL (Fin (tripSizes l d N j)) k) 1
variable {k} in

def glCast {a b : ℕ} (h : a = b) : GL (Fin a) k →* GL (Fin b) k := h ▸ MonoidHom.id _
end GlobalTheory.CuspBlock


