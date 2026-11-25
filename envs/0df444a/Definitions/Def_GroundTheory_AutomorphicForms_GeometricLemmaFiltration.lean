-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
-- name    : GroundTheory_AutomorphicForms_GeometricLemmaFiltration
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:16.201854+00:00
-- url     : https://prove2.me/theorems/6d71c39f-7871-4225-a536-8df7f1fabde3
-- title:
--   Geometric Lemma Filtration
-- statement:
--   Definitions and structural lemmas for Geometric Lemma Filtration, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
section Enumeration
variable {X : Type*} {k : ℕ} (C : Fin k → Set X)
def cellUnion (j : ℕ) : Set X := ⋃ l : Fin k, ⋃ (_ : (l : ℕ) < j), C l
variable {C}
variable [TopologicalSpace X]
variable (hdisj : Pairwise fun i j => Disjoint (C i) (C j)) (hcov : ∀ x, ∃ l, x ∈ C l)
  (hcl : ∀ j, closure (C j) ⊆ ⋃ l : Fin k, ⋃ (_ : j ≤ l), C l)
include hdisj hcov hcl
end Enumeration
section Cells
variable {F : Type*} [Field F] {n : ℕ} (β γ : Fin n → ℕ)
end Cells
section CellsTopology
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T1Space F] {n : ℕ}
  {β γ : Fin n → ℕ}
end CellsTopology
section Support
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β : Fin n → ℕ} (γ : Fin n → ℕ)
  {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
def supportedIn (Y : Set (GL (Fin n) F)) : Submodule ℂ (parabolicIndSpace F n β σ) where
  carrier := {f | ∀ g ∉ Y, (f : GL (Fin n) F → W) g = 0}
  add_mem' {f f'} hf hf' g hg := by
    simp [hf g hg, hf' g hg]
  zero_mem' g _ := rfl
  smul_mem' c f hf g hg := by
    simp [hf g hg]
variable {σ}
def jacquetFiltration (Y : Set (GL (Fin n) F)) :
    Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)) :=
  (supportedIn σ Y).map (Representation.Coinvariants.mk _)
end Support
end Parabolic
end GroundTheory.Automorphic


