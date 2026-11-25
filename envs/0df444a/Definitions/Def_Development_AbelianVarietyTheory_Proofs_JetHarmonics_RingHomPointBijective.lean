-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_RingHomPointBijective
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_RingHomPointBijective
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:19:14.74672+00:00
-- url     : https://prove2.me/theorems/756c5bb4-8319-4960-bc18-b75c713ea994
-- title:
--   Ring Hom Point Bijective
-- statement:
--   Definitions and structural lemmas for Ring Hom Point Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/RingHomPointBijective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Theorems.Thm_GlobalTheory_latticeIsogeny_latticePoint
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticeIsogeny_latticePoint
attribute [local simp] GlobalTheory.latticePointEquiv_mk


set_option autoImplicit false
open PowerSeries GlobalTheory.MomOne WeierstrassCurve WeierstrassCurve.Affine
open scoped ComplexConjugate BigOperators Topology
open Classical
noncomputable section
namespace GlobalTheory.MomOne
def ringHomPointFun {k k' : Type*} [Field k] [Field k'] (f : k →+* k') (W : WeierstrassCurve k) :
    W.toAffine.Point → (W.map f).toAffine.Point
  | .zero => 0
  | .some x y hP => .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).mpr hP)
def ringHomPoint {k k' : Type*} [Field k] [Field k'] (f : k →+* k') (W : WeierstrassCurve k) :
    W.toAffine.Point →+ (W.map f).toAffine.Point :=
  AddMonoidHom.mk' (ringHomPointFun f W) <| by
    refine GlobalTheory.map_add_of_triples _ rfl ?_ ?_
    · rintro (_ | ⟨x, y, hP⟩)
      · rfl
      · simp only [Point.neg_some, ringHomPointFun, Point.some.injEq, true_and, negY,
          map_a₁, map_a₃, map_sub, map_neg, map_mul]
    · rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) (_ | ⟨x₃, y₃, h₃⟩) hP hQ hR h
      any_goals first | exact absurd rfl hP | exact absurd rfl hQ | exact absurd rfl hR
      obtain ⟨l, n, e₁, e₂, e₃, s₁, s₂, -⟩ := GlobalTheory.exists_line_of_add_add_eq_zero h
      refine GlobalTheory.add_add_eq_zero_of_line _ _ _ (f l) (f n) ?_ ?_ ?_ ?_ ?_
      · rw [e₁]; simp
      · rw [e₂]; simp
      · rw [e₃]; simp
      · simpa using congrArg f s₁
      · simpa [map_ofNat] using congrArg f s₂
end GlobalTheory.MomOne


