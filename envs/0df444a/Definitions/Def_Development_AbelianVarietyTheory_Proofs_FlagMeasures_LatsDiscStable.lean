-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatsDiscStable
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatsDiscStable
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T04:33:06.36047+00:00
-- url     : https://prove2.me/theorems/5c5327f6-c00d-5664-939d-a1ec7b41a92b
-- title:
--   Lats Disc Stable
-- statement:
--   Definitions and structural lemmas for Lats Disc Stable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatsDiscStable.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumTransportEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
namespace GlobalTheory.Mass.Transp
section General
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V'']
def img (e : V ≃ₗ[K] V') (L : Submodule R V) : Submodule R V' :=
  L.map (e.toLinearMap.restrictScalars R)
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} in
theorem _root_.GlobalTheory.Mass.Transp.symm_isom (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) :
    ∀ x y, h (e.symm x) (e.symm y) = h' x y := by
  intro x y
  rw [← he]
  simp
def conj (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) : isom h ≃* isom h' where
  toFun g := ⟨(e.symm.trans g.1).trans e, fun x y => by
    simp only [LinearEquiv.trans_apply]
    rw [he, g.2, symm_isom e he]⟩
  invFun g := ⟨(e.trans g.1).trans e.symm, fun x y => by
    simp only [LinearEquiv.trans_apply]
    rw [symm_isom e he, g.2, he]⟩
  left_inv g := by ext x; simp
  right_inv g := by ext x; simp
  map_mul' g g' := by ext x; simp
end General
end GlobalTheory.Mass.Transp


