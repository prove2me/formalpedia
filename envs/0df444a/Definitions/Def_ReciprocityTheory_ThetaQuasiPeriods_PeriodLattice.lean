-- Prove2me | Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
-- name    : ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:24.894252+00:00
-- url     : https://prove2.me/theorems/e6e99d27-ec00-497b-b630-f49dd565c44f
-- title:
--   Period Lattice
-- statement:
--   Definitions and structural lemmas for Period Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/PeriodLattice.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
namespace ReciprocityTheory.PTheta
def eC (x : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)
variable {ι : Type*} [Fintype ι]
def SiegelH (ι : Type*) [Fintype ι] : Set (Matrix ι ι ℂ) :=
  {τ | τ.IsSymm ∧ (τ.map Complex.im).PosDef}
def ThetaDomain (ι : Type*) [Fintype ι] : Set (Matrix ι ι ℂ) :=
  {τ | (τ.map Complex.im + (τ.map Complex.im)ᵀ).PosDef}
def ofRealVec (a : ι → ℝ) : ι → ℂ := fun i => (a i : ℂ)
def ofIntVec (n : ι → ℤ) : ι → ℂ := fun i => (n i : ℂ)
theorem ofIntVec_add (n m : ι → ℤ) : ofIntVec (n + m) = ofIntVec n + ofIntVec m := by
  ext i; simp [ofIntVec]
theorem ofIntVec_neg (n : ι → ℤ) : ofIntVec (-n) = -ofIntVec n := by
  ext i; simp [ofIntVec]
theorem ofIntVec_zero : ofIntVec (0 : ι → ℤ) = 0 := by
  ext i; simp [ofIntVec]
def shiftVec (a : ι → ℝ) (l : ι → ℤ) : ι → ℂ := fun i => (l i : ℂ) + (a i : ℂ)
def thetaTerm (a b : ι → ℝ) (z : ι → ℂ) (τ : Matrix ι ι ℂ) (l : ι → ℤ) : ℂ :=
  eC (shiftVec a l ⬝ᵥ (τ *ᵥ shiftVec a l) / 2 + shiftVec a l ⬝ᵥ (z + ofRealVec b))
def theta (a b : ι → ℝ) (z : ι → ℂ) (τ : Matrix ι ι ℂ) : ℂ :=
  ∑' l : ι → ℤ, thetaTerm a b z τ l
def autFactor (a b : ι → ℝ) (τ : Matrix ι ι ℂ) (n n' : ι → ℤ) (z : ι → ℂ) : ℂ :=
  eC (ofRealVec a ⬝ᵥ ofIntVec n' - ofRealVec b ⬝ᵥ ofIntVec n) *
    eC (-(ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n)) / 2 - ofIntVec n ⬝ᵥ z)
def periodLattice (τ : Matrix ι ι ℂ) : AddSubgroup (ι → ℂ) where
  carrier := {w | ∃ n n' : ι → ℤ, w = τ *ᵥ ofIntVec n + ofIntVec n'}
  add_mem' := by
    rintro _ _ ⟨n, n', rfl⟩ ⟨m, m', rfl⟩
    refine ⟨n + m, n' + m', ?_⟩
    rw [ofIntVec_add, ofIntVec_add, Matrix.mulVec_add]; abel
  zero_mem' := ⟨0, 0, by rw [ofIntVec_zero, Matrix.mulVec_zero, add_zero]⟩
  neg_mem' := by
    rintro _ ⟨n, n', rfl⟩
    refine ⟨-n, -n', ?_⟩
    rw [ofIntVec_neg, ofIntVec_neg, Matrix.mulVec_neg]; abel
end ReciprocityTheory.PTheta


