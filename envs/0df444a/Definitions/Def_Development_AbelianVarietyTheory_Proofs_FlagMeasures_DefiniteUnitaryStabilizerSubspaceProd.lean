-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteUnitaryStabilizerSubspaceProd
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteUnitaryStabilizerSubspaceProd
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T03:02:19.80626+00:00
-- url     : https://prove2.me/theorems/aa77ee1f-92b2-4815-abe3-6ca220395727
-- title:
--   Definite Unitary Stabilizer Subspace Prod
-- statement:
--   Definitions and structural lemmas for Definite Unitary Stabilizer Subspace Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DefiniteUnitaryStabilizerSubspaceProd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
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
namespace GlobalTheory.Mass.StabSplit
section
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] in
theorem _root_.GlobalTheory.Mass.StabSplit.mem_perp (h : V →ₗ⋆[K] V →ₗ[K] K)
    (U : Submodule K V) (v : V) :
    v ∈ _root_.GlobalTheory.Mass.perp h U ↔ ∀ x ∈ U, h x v = 0 := by
  unfold _root_.GlobalTheory.Mass.perp
  simp [Submodule.mem_iInf, LinearMap.mem_ker]
theorem smul_eq_map (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (U : Submodule K V) :
    g • U = U.map (g.1 : V →ₗ[K] V) := rfl
open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] in
lemma exists_preimage_mem_of_isom_smul_eq {h : V →ₗ⋆[K] V →ₗ[K] K} {g : _root_.Formalism.HermitianLatticesTheory.isom h}
    {U : Submodule K V} (hg : g • U = U) {x : V} (hx : x ∈ U) : ∃ u ∈ U, g.1 u = x := by
  rw [← hg, _root_.GlobalTheory.Mass.StabSplit.smul_eq_map] at hx
  obtain ⟨u, hu, hux⟩ := Submodule.mem_map.1 hx
  exact ⟨u, hu, hux⟩
open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] in
lemma isom_apply_mem_of_smul_eq {h : V →ₗ⋆[K] V →ₗ[K] K} {g : _root_.Formalism.HermitianLatticesTheory.isom h}
    {U : Submodule K V} (hg : g • U = U) {x : V} (hx : x ∈ U) : g.1 x ∈ U := by
  rw [← hg, _root_.GlobalTheory.Mass.StabSplit.smul_eq_map]
  exact Submodule.mem_map_of_mem hx
open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] in

theorem _root_.GlobalTheory.Mass.StabSplit.smul_perp (h : V →ₗ⋆[K] V →ₗ[K] K) (g : _root_.Formalism.HermitianLatticesTheory.isom h)
    (U : Submodule K V) (hg : g • U = U) :
    g • _root_.GlobalTheory.Mass.perp h U = _root_.GlobalTheory.Mass.perp h U := by
  ext v
  rw [_root_.GlobalTheory.Mass.StabSplit.smul_eq_map, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [_root_.GlobalTheory.Mass.StabSplit.mem_perp] at hw ⊢
    intro x hx
    obtain ⟨u, hu, rfl⟩ := exists_preimage_mem_of_isom_smul_eq hg hx
    have hiso : h (g.1 u) (g.1 w) = h u w := g.2 u w
    simp only [LinearEquiv.coe_coe] at hiso ⊢
    rw [hiso]
    exact hw u hu
  · intro hv
    refine ⟨g.1.symm v, ?_, by simp⟩
    rw [_root_.GlobalTheory.Mass.StabSplit.mem_perp] at hv ⊢
    intro x hx
    have hiso : h (g.1 x) (g.1 (g.1.symm v)) = h x (g.1.symm v) := g.2 x (g.1.symm v)
    rw [← hiso, LinearEquiv.apply_symm_apply]
    exact hv _ (isom_apply_mem_of_smul_eq hg hx)
noncomputable def res (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (g : isom h)
    (hg : g • U = U) : isom (hRes h U) :=
  ⟨g.1.ofSubmodules U U hg, fun x y => g.2 x y⟩
noncomputable def resHom (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) :
    MulAction.stabilizer (isom h) U →* isom (hRes h U) × isom (hRes h (perp h U)) :=
  MonoidHom.mk' (fun γ => (res h U γ.1 γ.2, res h (perp h U) γ.1 (smul_perp h γ.1 U γ.2)))
    fun _ _ => rfl
end
end GlobalTheory.Mass.StabSplit


