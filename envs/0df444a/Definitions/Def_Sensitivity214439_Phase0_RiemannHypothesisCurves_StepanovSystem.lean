-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_StepanovSystem
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_StepanovSystem
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:36:24.732513+00:00
-- url     : https://prove2.me/theorems/e60a6b9f-2a19-4339-a7c5-acf81fa9bb77
-- title:
--   Linear multiplication, exact division, and Stepanov Hasse quotients
-- statement:
--   Define right multiplication by a fixed polynomial as a linear map. For a nonzero multiplier, define its inverse linear map on the range, giving exact polynomial division there. For nonzero f and natural numbers r and k, compose multiplication by f^r, the k-th Hasse derivative, and exact division by f^(r−k). The power-divisibility lemma ensures that this last division is defined for every input polynomial, producing the linear map p ↦ D^(k)(p f^r)/f^(r−k), with natural-number subtraction.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/StepanovSystem.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/StepanovSystem.lean lines 640–675; SHA256 8598e8f2f5a5feb4a726f52cf8cda87aea55e087771de3eb377b792d7c6081ff.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_HasseDerivatives
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring



















noncomputable def polyMulRightLinear (F : Type*) [Field F] (g : Polynomial F) :
    Polynomial F →ₗ[F] Polynomial F :=
{ toFun := fun p => p * g
  map_add' := by
    intro p q
    simp [add_mul]
  map_smul' := by
    intro a p
    simp }

noncomputable def polyDivRightLinear (F : Type*) [Field F] {g : Polynomial F} (hg : g ≠ 0) :
    (LinearMap.range (polyMulRightLinear (F:=F) g)) →ₗ[F] Polynomial F :=
  (LinearEquiv.ofInjective (polyMulRightLinear (F:=F) g)
      (fun _ _ => mul_right_cancel₀ hg)).symm.toLinearMap

noncomputable def stepanovHasseQuotMap
    (F : Type*) [Field F] {f : Polynomial F} (hf : f ≠ 0)
    (r k : ℕ) :
    Polynomial F →ₗ[F] Polynomial F := by
  let g : Polynomial F := f ^ (r - k)
  let mulG : Polynomial F →ₗ[F] Polynomial F := polyMulRightLinear (F := F) g
  let numMap : Polynomial F →ₗ[F] Polynomial F :=
    (Polynomial.hasseDeriv k).comp (polyMulRightLinear (F := F) (f ^ r))
  have hmem : ∀ p, numMap p ∈ LinearMap.range mulG := by
    intro p
    have hdiv :
        f ^ (r - k) ∣ hasseDerivOp F k (p * f ^ r) :=
      hasseDerivOp_mul_pow_dvd F k r p f
    obtain ⟨q, hq⟩ := hdiv
    refine ⟨q, ?_⟩
    have hq' : hasseDerivOp F k (p * f ^ r) = q * f ^ (r - k) := by
      simpa [mul_comm] using hq
    exact hq'.symm
  exact
    (polyDivRightLinear (F := F) (g := g) (pow_ne_zero _ hf)).comp
      (LinearMap.codRestrict (LinearMap.range mulG) numMap hmem)


