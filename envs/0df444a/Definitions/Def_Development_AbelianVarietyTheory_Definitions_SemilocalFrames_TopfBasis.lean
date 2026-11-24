-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_TopfBasis
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_TopfBasis
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:24:17.347138+00:00
-- url     : https://prove2.me/theorems/a627cb0f-3621-40c4-8119-0fb68d668f9a
-- title:
--   Topf Basis
-- statement:
--   Definitions and structural lemmas for Topf Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/TopfBasis.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RowLev
open Formalism.MainNotions.S Formalism.BasicNotions NumberField Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
def coordLat (W : HSpace E) : Submodule (𝓞 E) (Fin W.rank → E) :=
  W.L0.map (W.frame.equivFun.toLinearMap.restrictScalars (𝓞 E))
def congSet (cm : CMData F E) (W : HSpace E) (g : ℕ) : Set (Formalism.UG.UPts cm.sig W.gram (Af F)) :=
  {x | (x : GL (Fin W.rank) (E ⊗[F] Af F)) ∈ Formalism.UG.stabGL (lamAf (F := F) (coordLat W)) ∧
    ∀ y ∈ lamAf (F := F) (coordLat W), ∃ z ∈ lamAf (F := F) (coordLat W),
      ((x : GL (Fin W.rank) (E ⊗[F] Af F)) - 1 : Matrix (Fin W.rank) (Fin W.rank) (E ⊗[F] Af F)) *ᵥ y =
        (g : E ⊗[F] Af F) • z}
structure InstData (cm : CMData F E) (W : HSpace E) (ε : InfinitePlace F → Fin W.rank → Bool)
    (φ : InfinitePlace F → (E →+* ℂ)) where
  J_herm : Formalism.UG.IsHerm (starRingEnd E) W.gram
  J_det : W.gram.det ≠ 0
  L_span : Submodule.span E (coordLat W : Set (Fin W.rank → E)) = ⊤
  L_fg : (coordLat W).FG
  L_dual : ∀ x : Fin W.rank → E, x ∈ coordLat W ↔
    ∀ y ∈ coordLat W, Formalism.UG.hform (starRingEnd E) W.gram y x ∈ (algebraMap (𝓞 E) E).range
  φ_over : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a
  P : InfinitePlace F → Matrix (Fin W.rank) (Fin W.rank) ℂ
  P_unit : ∀ v, IsUnit (P v)
  P_spec : ∀ v, (P v)ᴴ * W.gram.map (φ v) * P v = Formalism.REAL.Jm (ε v)
  topf : TopologicalSpace (Formalism.UG.UPts cm.sig W.gram (Af F))
  topf_group : @IsTopologicalGroup _ topf _
  topf_open : ∀ g : ℕ, 1 ≤ g → @IsOpen _ topf (congSet cm W g)
  topf_basis : ∀ U ∈ @nhds _ topf 1, ∃ g : ℕ, 1 ≤ g ∧ congSet cm W g ⊆ U
@[reducible] def InstData.inst {cm : CMData F E} {W : HSpace E} {ε : InfinitePlace F → Fin W.rank → Bool}
    {φ : InfinitePlace F → (E →+* ℂ)} (X : InstData cm W ε φ) : AutInst where
  F := F
  E := E
  cm := cm
  n := W.rank
  J := W.gram
  J_herm := X.J_herm
  J_det := X.J_det
  L := coordLat W
  L_span := X.L_span
  L_fg := X.L_fg
  L_dual := X.L_dual
  ε := ε
  φ := φ
  φ_over := X.φ_over
  P := X.P
  P_unit := X.P_unit
  P_spec := X.P_spec
  topf := X.topf
  topf_group := X.topf_group
  topf_open := X.topf_open
  topf_basis := X.topf_basis
end GlobalTheory.RowLev


