-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:13.107571+00:00
-- url     : https://prove2.me/theorems/5b512544-7c10-4d1b-b592-5ea61f66633f
-- title:
--   POne Block Model A
-- statement:
--   Definitions and structural lemmas for POne Block Model A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
namespace LatticeModel
variable {K : Type} [Field K] [NumberField K]
variable {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} {φ : Fin (N + 1) → Fin m → K}
theorem latticeForm_zero : latticeForm (0 : Fin m → K) = 0 := by
  simp [latticeForm]
theorem coeff_latticeForm (u : Fin m → K) (j : Fin m) :
    coeff (Finsupp.single j 1) (latticeForm u) = u j := by
  simp [latticeForm, coeff_sum, coeff_C_mul, coeff_X, Finsupp.single_left_inj]
theorem latticeForm_eq_zero_iff (u : Fin m → K) : latticeForm u = 0 ↔ u = 0 := by
  refine ⟨fun h ↦ funext fun j ↦ ?_, fun h ↦ h ▸ latticeForm_zero⟩
  rw [← coeff_latticeForm u j, h, coeff_zero, Pi.zero_apply]
theorem isHomogeneous_latticeForm (u : Fin m → K) : (latticeForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ ↦ isHomogeneous_C_mul_X _ _
theorem isHomogeneous_latticeMap (φ : Fin (N + 1) → Fin m → K) {f : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ}
    {d : ℕ} (hf : f.IsHomogeneous d) : (latticeMap φ f).IsHomogeneous d := by
  have h := hf.eval₂ (Int.castRingHom _) (fun v ↦ latticeForm (φ v.2))
    (fun a ↦ by rw [eq_intCast, ← map_intCast (C : K →+* MvPolynomial (Fin m) K)]; exact isHomogeneous_C _ _)
    (fun v ↦ isHomogeneous_latticeForm _)
  rwa [one_mul] at h
section Degrees
variable {R : Type*} [CommSemiring R]
theorem weight_coordDeg (s : Coord (fun _ : Unit ↦ N) →₀ ℕ) :
    Finsupp.weight (coordDeg fun _ : Unit ↦ N) s = fun _ ↦ s.degree := by
  funext u
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finsupp.degree]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  simp [coordDeg]
theorem weightedHomogeneousComponent_coordDeg (f : MvPolynomial (Coord fun _ : Unit ↦ N) R) (μ : Unit → ℕ) :
    weightedHomogeneousComponent (coordDeg fun _ : Unit ↦ N) μ f = homogeneousComponent (μ ()) f := by
  classical
  ext s
  rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent, weight_coordDeg]
  by_cases h : s.degree = μ ()
  · rw [if_pos (funext fun _ ↦ h), if_pos h]
  · rw [if_neg (fun h' ↦ h (congrFun h' ())), if_neg h]
end Degrees
theorem latticeMap_homogeneousComponent (φ : Fin (N + 1) → Fin m → K)
    (f : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) (d : ℕ) :
    latticeMap φ (homogeneousComponent d f) = homogeneousComponent d (latticeMap φ f) := by
  classical
  conv_rhs => rw [← sum_homogeneousComponent f]
  rw [map_sum, map_sum]
  simp_rw [homogeneousComponent_of_mem (isHomogeneous_latticeMap φ (homogeneousComponent_isHomogeneous _ f))]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]
def latticeVariety (φ : Fin (N + 1) → Fin m → K) (hφ : IsDualBasis L φ) :
    ArithVariety (fun _ : Unit ↦ N) where
  ideal := latticeIdeal φ
  isPrime := RingHom.ker_isPrime _
  homogeneous f hf μ := by
    rw [weightedHomogeneousComponent_coordDeg]
    refine RingHom.mem_ker.mpr ?_
    rw [latticeMap_homogeneousComponent, RingHom.mem_ker.mp hf, map_zero]
  relevant _ := ⟨0, fun h ↦ hφ.independent.ne_zero 0
    ((latticeForm_eq_zero_iff _).mp (by simpa [latticeMap] using RingHom.mem_ker.mp h))⟩
  horizontal a ha := by simpa [latticeMap] using RingHom.mem_ker.mp ha
variable {r : ℕ}
def genericVal (K : Type) [Field K] (r : ℕ) : Fin (r + 1) → LatticeField K r :=
  Fin.cases 1 fun j ↦ algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (X j)
def dehom (K : Type) [Field K] (r : ℕ) : MvPolynomial (Fin (r + 1)) K →+* LatticeField K r :=
  eval₂Hom (algebraMap K (LatticeField K r)) (genericVal K r)
end LatticeModel
end
end GroundTheory.Heights₂.Heights


