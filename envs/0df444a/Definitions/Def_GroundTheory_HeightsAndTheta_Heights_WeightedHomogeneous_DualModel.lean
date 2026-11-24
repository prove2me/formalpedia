-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_DualModel
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_DualModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:12.467737+00:00
-- url     : https://prove2.me/theorems/299fdc92-7af8-4abc-a3d6-25758803c5b6
-- title:
--   Dual Model
-- statement:
--   Definitions and structural lemmas for Dual Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/DualModel.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
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
open MvPolynomial NumberField Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
def latticeDual {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) : Submodule (𝓞 K) (Fin m → K) where
  carrier := {φ | ∀ v ∈ L, φ ⬝ᵥ v ∈ Set.range (algebraMap (𝓞 K) K)}
  add_mem' := by
    intro φ ψ hφ hψ v hv
    obtain ⟨a, ha⟩ := hφ v hv
    obtain ⟨b, hb⟩ := hψ v hv
    exact ⟨a + b, by rw [map_add, ha, hb, add_dotProduct]⟩
  zero_mem' := fun v _ ↦ ⟨0, by rw [map_zero, zero_dotProduct]⟩
  smul_mem' := by
    intro c φ hφ v hv
    obtain ⟨a, ha⟩ := hφ v hv
    exact ⟨c * a, by rw [map_mul, ha, smul_dotProduct, Algebra.smul_def]⟩
structure IsDualBasis {m N : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) (φ : Fin (N + 1) → Fin m → K) : Prop where
  independent : LinearIndependent ℤ φ
  span_eq : Submodule.span ℤ (Set.range φ) = (latticeDual L).restrictScalars ℤ
def latticeForm {m : ℕ} (φ : Fin m → K) : MvPolynomial (Fin m) K := ∑ j, C (φ j) * X j
def latticeMap {m N : ℕ} (φ : Fin (N + 1) → Fin m → K) :
    MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ →+* MvPolynomial (Fin m) K :=
  eval₂Hom (Int.castRingHom _) fun v ↦ latticeForm (φ v.2)
def latticeIdeal {m N : ℕ} (φ : Fin (N + 1) → Fin m → K) :
    Ideal (MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ) :=
  RingHom.ker (latticeMap φ)
abbrev LatticeField (K : Type*) [Field K] (r : ℕ) : Type _ := FractionRing (MvPolynomial (Fin r) K)
def latticeCoord {r N : ℕ} (φ : Fin (N + 1) → Fin (r + 1) → K) :
    Coord (fun _ : Unit ↦ N) → LatticeField K r :=
  fun v ↦ algebraMap (MvPolynomial (Fin r) K) (LatticeField K r)
    (C (φ v.2 0) + ∑ j : Fin r, C (φ v.2 j.succ) * X j)
def latticePoint {R : Type*} [CommRing R] {m N : ℕ} (φ : Fin (N + 1) → Fin m → K) (σ : K →+* R)
    (w : Fin m → R) : Cone (fun _ : Unit ↦ N) R :=
  fun _ b ↦ ∑ j, σ (φ b j) * w j
def LatticeMetricAgrees {r N : ℕ} (φ : Fin (N + 1) → Fin (r + 1) → K) (F : HermLattice K (r + 1))
    (A : HermLine (fun _ : Unit ↦ N)) : Prop :=
  ∀ (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ), w ≠ 0 →
    A.metric (latticePoint φ σ w) = Real.sqrt (star w ⬝ᵥ (F.metric σ *ᵥ w)).re
def oneBlockForms {e r : ℕ} (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    Fin (oneBlockSize e r + 1) → Fin (r + 1) → K :=
  fun p ↦ Pi.single (oneBlockIndex e r p).2 ((om (oneBlockIndex e r p).1 : 𝓞 K) : K)
def ratDoubled (r : ℕ) : HermLattice ℚ (r + 1) where
  lattice := Submodule.span (𝓞 ℚ) (Set.range fun j : Fin (r + 1) ↦ (Pi.single j 2 : Fin (r + 1) → ℚ))
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq := by
    rw [Submodule.span_span_of_tower, eq_top_iff]
    intro v _
    have hv : v = ∑ j, (v j / 2) • (Pi.single j 2 : Fin (r + 1) → ℚ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  metric := fun _ ↦ 1
  posDef := fun _ ↦ Matrix.PosDef.one
  conj := fun _ ↦ by simp
end
end GroundTheory.Heights₂.Heights


