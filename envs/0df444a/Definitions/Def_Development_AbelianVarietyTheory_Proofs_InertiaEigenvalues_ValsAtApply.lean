-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValsAtApply
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValsAtApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:58.99081+00:00
-- url     : https://prove2.me/theorems/d20b0f7f-d1fd-43d3-8995-44a3dc58624f
-- title:
--   Vals At Apply
-- statement:
--   Definitions and structural lemmas for Vals At Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValsAtApply.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.UnitLemma
def valsAt {G : Type} [Group G] {ι : Type} (w : ι → G →* Multiplicative ℤ) {r : ℕ} (e : Fin r → ι) :
    G →* Multiplicative (Fin r → ℤ) where
  toFun x := Multiplicative.ofAdd fun j => Multiplicative.toAdd (w (e j) x)
  map_one' := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    congr 1
    funext j
    simp
  map_mul' x y := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd (_ + _)
    congr 1
    funext j
    simp
end GlobalTheory.UnitLemma


