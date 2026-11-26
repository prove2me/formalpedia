-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothApprox
-- name    : Operator_Crouzeix_SmoothApprox
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:29:24.316193+00:00
-- url     : https://prove2.me/theorems/90f9ca65-c4d4-4ccb-8352-5188fb4d9dbc
-- title:
--   Smooth Approx
-- statement:
--   Definitions and structural lemmas for Smooth Approx, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothApprox.lean

import Mathlib.Analysis.Convex.Strict
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.CircleIntegral
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
structure SmoothJordanDomain where
  carrier : Set ℂ
  isOpen_carrier : IsOpen carrier
  strictConvex_carrier : StrictConvex ℝ carrier
  boundaryParam : ℝ → ℂ
  boundaryParam_periodic : Function.Periodic boundaryParam (2 * Real.pi)
  boundaryParam_contDiff : ContDiff ℝ ∞ boundaryParam
  boundaryParam_range : Set.range boundaryParam = frontier carrier
  boundaryParam_injOn : Set.InjOn boundaryParam (Set.Ico 0 (2 * Real.pi))
  boundaryParam_regular : ∀ t, deriv boundaryParam t ≠ 0
noncomputable def SmoothJordanDomain.ball (c : ℂ) (R : ℝ) (hR : 0 < R) :
    SmoothJordanDomain where
  carrier := Metric.ball c R
  isOpen_carrier := Metric.isOpen_ball
  strictConvex_carrier := (convex_ball c R).strictConvex_of_isOpen Metric.isOpen_ball
  boundaryParam := circleMap c R
  boundaryParam_periodic := periodic_circleMap c R
  boundaryParam_contDiff := contDiff_circleMap c R
  boundaryParam_range := by
    rw [range_circleMap, abs_of_pos hR, frontier_ball c hR.ne']
  boundaryParam_injOn := by
    apply injOn_circleMap_of_abs_sub_le' hR.ne'
    simp only [sub_zero]
    exact le_rfl
  boundaryParam_regular := fun _ => deriv_circleMap_ne_zero hR.ne'
noncomputable def smoothApproxRadius (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)
noncomputable def convexThickeningApprox (K : Set ℂ) (n : ℕ) : Set ℂ :=
  Metric.thickening (smoothApproxRadius n) K
theorem smoothApproxRadius_pos (n : ℕ) : 0 < smoothApproxRadius n := by
  unfold smoothApproxRadius
  positivity
theorem iInter_convexThickeningApprox (K : Set ℂ) (hK : IsClosed K) :
    (⋂ n, convexThickeningApprox K n) = K := by
  let radii : Set ℝ := Set.range smoothApproxRadius
  have hradii_pos : radii ⊆ Set.Ioi 0 := by
    rintro _ ⟨n, rfl⟩
    exact smoothApproxRadius_pos n
  have hradii_small : ∀ ε, 0 < ε → (radii ∩ Set.Ioc 0 ε).Nonempty := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨smoothApproxRadius n, ⟨⟨n, rfl⟩, ?_⟩⟩
    exact ⟨smoothApproxRadius_pos n, hn.le⟩
  have hclosure := Metric.closure_eq_iInter_thickening' K radii hradii_pos hradii_small
  rw [hK.closure_eq] at hclosure
  calc
    (⋂ n, convexThickeningApprox K n) =
        ⋂ δ ∈ radii, Metric.thickening δ K := by
      ext x
      simp only [Set.mem_iInter, convexThickeningApprox]
      constructor
      · intro hx δ hδ
        obtain ⟨n, rfl⟩ := hδ
        exact hx n
      · intro hx n
        exact hx (smoothApproxRadius n) ⟨n, rfl⟩
    _ = K := hclosure.symm
structure SmoothConvexApproximation (K : Set ℂ) where
  domain : ℕ → SmoothJordanDomain
  subset_domain : ∀ n, K ⊆ (domain n).carrier
  iInter_domain : (⋂ n, (domain n).carrier) = K
noncomputable def smoothClosedBallApproximation (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    SmoothConvexApproximation (Metric.closedBall c R) where
  domain n := SmoothJordanDomain.ball c (smoothApproxRadius n + R)
    (add_pos_of_pos_of_nonneg (smoothApproxRadius_pos n) hR)
  subset_domain n := by
    change Metric.closedBall c R ⊆ Metric.ball c (smoothApproxRadius n + R)
    apply Metric.closedBall_subset_ball
    linarith [smoothApproxRadius_pos n]
  iInter_domain := by
    have heq : ∀ n,
        (SmoothJordanDomain.ball c (smoothApproxRadius n + R)
          (add_pos_of_pos_of_nonneg (smoothApproxRadius_pos n) hR)).carrier =
          convexThickeningApprox (Metric.closedBall c R) n := by
      intro n
      change Metric.ball c (smoothApproxRadius n + R) =
        Metric.thickening (smoothApproxRadius n) (Metric.closedBall c R)
      exact (thickening_closedBall (smoothApproxRadius_pos n) hR c).symm
    simp_rw [heq]
    exact iInter_convexThickeningApprox _ Metric.isClosed_closedBall


