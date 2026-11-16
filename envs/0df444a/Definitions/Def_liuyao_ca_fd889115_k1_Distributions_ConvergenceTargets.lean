-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Distributions_ConvergenceTargets
-- name    : liuyao_ca_fd889115_k1_Distributions_ConvergenceTargets
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:58:13.137679+00:00
-- url     : https://prove2.me/theorems/48a664ec-ad9d-48dc-885c-757d90e004f8
-- title:
--   Computable analysis · ConvergenceTargets · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableDistributions/ConvergenceTargets.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_Goals

set_option autoImplicit true

/-! The test-action convergence targets for the opening textbook mission. -/

open ComputableAnalysis

namespace ComputableDistributions

def Distribution.PointwiseBounded {d : Nat} {S : TestFunctionSpace d}
    (u : Nat → Distribution S) : Prop :=
  ∀ φ, ∃ C : Rat, 0 ≤ C ∧ ∀ j,
    RealApproximationOrder.Small
      (RealApproximationOrder.parameter ((u j).action φ) ((u j).action_valid φ)) C

def Distribution.UniformBoxBound {d : Nat} {S : TestFunctionSpace d}
    (u : Nat → Distribution S) : Prop :=
  ∀ B : RationalBox d, ∃ order : Nat, ∃ C : Rat, 0 ≤ C ∧
    ∀ j φ, φ.SupportedInBox B → ∀ b : Rat, 0 ≤ b →
      φ.DerivativesBoundedBy order b →
      RealApproximationOrder.Small
        (RealApproximationOrder.parameter ((u j).action φ) ((u j).action_valid φ)) (C * b)

def Distribution.ConvergesOnTests {d : Nat} {S : TestFunctionSpace d}
    (u : Nat → Distribution S) (A : TestFunction d → RealCompute) : Prop :=
  ∀ φ, RawLimit.TendsTo (fun j => (u j).action φ) (A φ)

theorem Distribution.limit_equivalent {d : Nat} {S : TestFunctionSpace d}
    {u : Nat → Distribution S} {T U : Distribution S}
    (hT : Distribution.ConvergesOnTests u T.action)
    (hU : Distribution.ConvergesOnTests u U.action) : Distribution.Equivalent T U :=
  fun φ => RawLimit.unique (hT φ) (hU φ)

def DistributionLimitWithUniformBoundsTarget : Prop :=
  ∀ (d : Nat) (S : TestFunctionSpace d) (u : Nat → Distribution S)
    (A : TestFunction d → RealCompute),
    Distribution.UniformBoxBound u → Distribution.ConvergesOnTests u A →
    ∃ T : Distribution S, ∀ φ, (T.action φ).Equiv (A φ)

def DistributionUniformBoundednessTarget : Prop :=
  ∀ (d : Nat) (S : TestFunctionSpace d) (u : Nat → Distribution S),
    Distribution.PointwiseBounded u → Distribution.UniformBoxBound u

def DistributionConvergenceTarget : Prop :=
  ∀ (d : Nat) (S : TestFunctionSpace d) (u : Nat → Distribution S)
    (A : TestFunction d → RealCompute),
    Distribution.ConvergesOnTests u A →
    ∃ T : Distribution S, ∀ φ, (T.action φ).Equiv (A φ)

end ComputableDistributions


