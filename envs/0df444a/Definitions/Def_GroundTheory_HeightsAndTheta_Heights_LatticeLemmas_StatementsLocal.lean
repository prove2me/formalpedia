-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocal
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:31.613806+00:00
-- url     : https://prove2.me/theorems/f3219e1e-0f9b-4730-a048-2dcfba0b362b
-- title:
--   Statements Local
-- statement:
--   Definitions and structural lemmas for Statements Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsBundles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
noncomputable section
structure HermitianNorms (K : Type*) [Field K] [NumberField K] (V : Type*) [AddCommGroup V]
    [Module (𝓞 K) V] where

  form : ∀ σ : K →+* ℂ, InnerProductSpace.Core ℂ (Fibre σ V)

  form_conj : ∀ (σ : K →+* ℂ) (x y : Fibre σ V),
    (form (conjugate σ)).inner (conjMap σ V x) (conjMap σ V y) = starRingEnd ℂ ((form σ).inner x y)
structure FullLattice (K : Type*) [Field K] [NumberField K] (V : Type*) [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] where

  carrier : Submodule (𝓞 K) V
  fg : carrier.FG
  span_eq : Submodule.span K (carrier : Set V) = ⊤
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [NumberField K] in

theorem isTorsionFree_of_vectorSpace : Module.IsTorsionFree (𝓞 K) V :=
  Module.IsTorsionFree.of_smul_eq_zero fun a x hax ↦ by
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      have ha' : (a : K) ≠ 0 := by exact_mod_cast ha
      have : (a : K) • x = 0 := by rw [← hax]; exact algebraMap_smul K a x
      exact (smul_eq_zero.mp this).resolve_left ha'
def HermitianNorms.restrict (N : HermitianNorms K V) (L : Submodule (𝓞 K) V)
    [Module.Finite (𝓞 K) L] [Module.Projective (𝓞 K) L] : HermitianMetric K L where
  form σ := coreComap (N.form σ) (fibreMap σ L.subtype) (fibreMap_injective σ L.injective_subtype)
  form_conj σ x y := by
    rw [coreComap_inner, coreComap_inner, ← conjMap_fibreMap, ← conjMap_fibreMap, N.form_conj]
namespace FullLattice
variable (L : FullLattice K V)
instance : Module.Finite (𝓞 K) L.carrier := Module.Finite.iff_fg.mpr L.fg
instance : Module.Projective (𝓞 K) L.carrier :=
  haveI : Module.IsTorsionFree (𝓞 K) V := isTorsionFree_of_vectorSpace
  projective_of_isTorsionFree _
end FullLattice
def HermitianNorms.bundle (N : HermitianNorms K V) (L : FullLattice K V) : HermitianBundle K :=
  ⟨L.carrier, N.restrict L.carrier⟩
section Local
variable (v : HeightOneSpectrum (𝓞 K))
def toLocal : V →ₗ[K] v.adicCompletion K ⊗[K] V := TensorProduct.mk K (v.adicCompletion K) V 1
def localLattice (L : Submodule (𝓞 K) V) :
    Submodule (v.adicCompletionIntegers K) (v.adicCompletion K ⊗[K] V) :=
  Submodule.span _ (toLocal v '' (L : Set V))
def IsLocalLattice (N : Submodule (v.adicCompletionIntegers K) (v.adicCompletion K ⊗[K] V)) :
    Prop :=
  N.FG ∧ Submodule.span (v.adicCompletion K) (N : Set (v.adicCompletion K ⊗[K] V)) = ⊤
theorem toLocal_smul (a : 𝓞 K) (x : V) :
    toLocal v (a • x) = algebraMap (𝓞 K) (v.adicCompletionIntegers K) a • toLocal v x := by
  rw [← algebraMap_smul K a x, map_smul, ← algebraMap_smul (v.adicCompletion K)
    (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) (toLocal v x),
    ← algebraMap_smul (v.adicCompletion K) (algebraMap (𝓞 K) K a) (toLocal v x)]
  congr 1
def latticeOfLocal
    (N : ∀ v : HeightOneSpectrum (𝓞 K),
      Submodule (v.adicCompletionIntegers K) (v.adicCompletion K ⊗[K] V)) :
    Submodule (𝓞 K) V where
  carrier := {x | ∀ v, toLocal v x ∈ N v}
  add_mem' hx hy v := by rw [map_add]; exact (N v).add_mem (hx v) (hy v)
  zero_mem' v := by rw [map_zero]; exact (N v).zero_mem
  smul_mem' a x hx v := by rw [toLocal_smul]; exact (N v).smul_mem _ (hx v)
end Local
end
end GroundTheory.Heights₂.Heights


