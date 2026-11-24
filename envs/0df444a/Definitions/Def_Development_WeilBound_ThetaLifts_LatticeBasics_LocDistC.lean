-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC
-- name    : Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:53.4848+00:00
-- url     : https://prove2.me/theorems/80d62135-2815-4776-a235-5367ca1e344c
-- title:
--   Loc Dist C
-- statement:
--   Definitions and structural lemmas for Loc Dist C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistC.lean

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM Matrix
namespace GlobalTheory.ThK.Dbl.LD
variable {k : Type} [Field k] {n d : ℕ}
def blk (a : k) (b : Fin d → k) (h : Matrix (Fin d) (Fin d) k) : Matrix (Fin (d + 1)) (Fin (d + 1)) k :=
  Matrix.of (Fin.cons (Fin.cons a b) fun i => Fin.cons 0 (h i))
def chE (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k :=
  ((fun i => X i 0, fun j => X 0 j.succ / X 0 0), Matrix.of fun i j => X i.succ j.succ - X i.succ 0 * (X 0 j.succ / X 0 0))
def chR (y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k) : Matrix (Fin (n + 1)) (Fin (d + 1)) k :=
  Matrix.of (Fin.cons (Fin.cons (y.1.1 0) fun j => y.1.1 0 * y.1.2 j)
    fun i => Fin.cons (y.1.1 i.succ) fun j => y.1.1 i.succ * y.1.2 j + y.2 i j)
def Deg {m : Type} (X : Matrix m (Fin d) k) : Prop := ∃ v ≠ 0, X *ᵥ v = 0
theorem Deg.chE {X : Matrix (Fin (n + 1)) (Fin (d + 1)) k} (h : Deg X) (hX : X 0 0 ≠ 0) : Deg (chE X).2 := by
  obtain ⟨v, hv, h⟩ := h
  have hi : ∀ i, X i 0 * v 0 + ∑ j : Fin d, X i j.succ * v j.succ = 0 := fun i => by
    simpa [mulVec, dotProduct, Fin.sum_univ_succ] using congrFun h i
  refine ⟨fun j => v j.succ, fun h0 => hv ?_, ?_⟩
  · have h1 : ∀ j : Fin d, v j.succ = 0 := congrFun h0
    ext j
    refine Fin.cases ?_ h1 j
    simpa [h1, hX] using hi 0
  · ext i
    have : ∑ j : Fin d, X i.succ 0 * (X 0 j.succ / X 0 0) * v j.succ = X i.succ 0 / X 0 0 * ∑ j : Fin d, X 0 j.succ * v j.succ := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
    simp only [LD.chE, mulVec, dotProduct, of_apply, sub_mul, Finset.sum_sub_distrib, this, Pi.zero_apply,
      eq_neg_of_add_eq_zero_right (hi 0), eq_neg_of_add_eq_zero_right (hi i.succ)]
    field_simp; ring
variable [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]
def Eqv (c : k → ℂ) {m : Type} (l : (Matrix m (Fin d) k → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ h : Matrix (Fin d) (Fin d) k, h.det ≠ 0 → ∃ t : ℝ, 0 < t ∧ ∀ φ ∈ SB _, l (fun y => φ (y * h)) = c h.det * t * l φ
end GlobalTheory.ThK.Dbl.LD


