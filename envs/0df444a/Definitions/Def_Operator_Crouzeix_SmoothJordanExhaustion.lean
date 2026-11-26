-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
-- name    : Operator_Crouzeix_SmoothJordanExhaustion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:49:42.341844+00:00
-- url     : https://prove2.me/theorems/13254105-1b29-4318-8ecd-6361e65dc0b0
-- title:
--   Smooth Jordan Exhaustion
-- statement:
--   Definitions and structural lemmas for Smooth Jordan Exhaustion, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Theorems.Thm_closure_convexThickeningApprox_succ_subset
import Theorems.Thm_compactThickeningApprox_spec

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
structure StrictNestedSmoothJordanExhaustion (K : Set ℂ) where
  domain : ℕ → SmoothJordanDomain
  target_subset : ∀ n, K ⊆ (domain n).carrier
  isCompact_closure : ∀ n, IsCompact (closure (domain n).carrier)
  closure_succ_subset : ∀ n,
    closure (domain (n + 1)).carrier ⊆ (domain n).carrier
  iInter_closure : (⋂ n, closure (domain n).carrier) = K
noncomputable def StrictNestedSmoothJordanExhaustion.ofConvexThickening
    (K : Set ℂ) (hcompact : IsCompact K) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier = convexThickeningApprox K n) :
    StrictNestedSmoothJordanExhaustion K := by
  have hnonempty : K.Nonempty := by
    have hstage := (Omega 0).carrier_nonempty
    rw [hcarrier 0] at hstage
    unfold convexThickeningApprox at hstage
    apply (Metric.thickening_nonempty_iff_of_pos ?_).mp hstage
    unfold smoothApproxRadius
    positivity
  let hspec := compactThickeningApprox_spec K hcompact hnonempty
  refine
    { domain := Omega
      target_subset := ?_
      isCompact_closure := ?_
      closure_succ_subset := ?_
      iInter_closure := ?_ }
  · intro n
    rw [hcarrier n]
    apply Metric.self_subset_thickening
    unfold smoothApproxRadius
    positivity
  · intro n
    rw [hcarrier n]
    unfold convexThickeningApprox
    rw [closure_thickening]
    · exact hspec.2.1 n
    · unfold smoothApproxRadius
      positivity
  · intro n
    rw [hcarrier (n + 1), hcarrier n]
    exact closure_convexThickeningApprox_succ_subset K n
  · have heq : ∀ n, closure (Omega n).carrier =
        compactThickeningApprox K n := by
      intro n
      rw [hcarrier n]
      unfold convexThickeningApprox compactThickeningApprox
      rw [closure_thickening]
      unfold smoothApproxRadius
      positivity
    simp_rw [heq]
    exact hspec.2.2.2
noncomputable def StrictNestedSmoothJordanExhaustion.closedBall
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    StrictNestedSmoothJordanExhaustion (Metric.closedBall c R) := by
  let Omega := (smoothClosedBallApproximation c R hR).domain
  apply StrictNestedSmoothJordanExhaustion.ofConvexThickening
    (Metric.closedBall c R) (isCompact_closedBall c R) Omega
  intro n
  change Metric.ball c (smoothApproxRadius n + R) =
    Metric.thickening (smoothApproxRadius n) (Metric.closedBall c R)
  exact (thickening_closedBall (by
    unfold smoothApproxRadius
    positivity) hR c).symm
def SmoothJordanDomain.HasMergelyanPolynomialApproximation
    (Omega : SmoothJordanDomain) : Prop :=
  ∀ f : ℂ → ℂ, DiffContOnCl ℂ f Omega.carrier →
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn
        (fun j z ↦ Polynomial.eval z (q j)) f atTop
        (closure Omega.carrier)
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


