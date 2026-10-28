-- Prove2me | Definitions.Def_OAIQ4Kq008
-- name    : OAIQ4Kq008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T08:32:59.692723+00:00
-- url     : https://prove2.me/theorems/94b230e0-730d-47c2-afe1-de713739f000
-- title:
--   Definitions bundle OAIQ4Kq008 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kaplansky.kaplansky_quasitrace_counterexample`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 1 definition, 11 instances and 7 theorems. The definitions and types are `OAI.Kaplansky.spectralCornerHom`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: [`ComplexBundle_CoordinatesMetric`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/ComplexBundle/CoordinatesMetric.lean), [`ComplexBundle_LineStage`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/ComplexBundle/LineStage.lean), [`ComplexBundle_RealModel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/ComplexBundle/RealModel.lean), [`Cuntz_Monoid`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Cuntz/Monoid.lean), [`Cuntz_Quasitrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Cuntz/Quasitrace.lean), [`IntegralHomology_Simplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/IntegralHomology/Simplex.lean), [`IntegralHomology_SmallChains`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/IntegralHomology/SmallChains.lean), [`IntegralHomology_Thom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/IntegralHomology/Thom.lean), [`OrderedStates_RationalCone`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/OrderedStates/RationalCone.lean), [`Quasitrace_Extension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Quasitrace/Extension.lean).
--
--   **Imports.** It imports the bundles `OAIQ4Kq000`, `OAIQ4Kq001`, `OAIQ4Kq002`, `OAIQ4Kq003` and `OAIQ4Kq004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ4Kq010`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ4Kq000
import Definitions.Def_OAIQ4Kq001
import Definitions.Def_OAIQ4Kq002
import Definitions.Def_OAIQ4Kq003
import Definitions.Def_OAIQ4Kq004

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_RealModel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Real models of complex bundles and smooth finite line sums. -/

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky

section
variable {B F J : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] (C : VectorBundleCore ℂ B F J)

instance complexCoreRealFiberComplexModule (x : B) : Module ℂ ((complexCoreReal C).Fiber x) :=
  inferInstanceAs (Module ℂ F)

instance complexCoreRealFiberComplexVectorBundle : VectorBundle ℂ F (complexCoreReal C).Fiber :=
  inferInstanceAs (VectorBundle ℂ F C.Fiber)

end

end Kaplansky

end

open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky
variable {B F G J : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  (C : VectorBundleCore ℂ B F J) (e : F ≃L[ℂ] G)

instance changeModelFiberNorm (x : B) : NormedAddCommGroup ((changeModelCore C e).Fiber x) :=
  inferInstanceAs (NormedAddCommGroup G)
instance changeModelFiberNormedSpace (x : B) : NormedSpace ℂ ((changeModelCore C e).Fiber x) :=
  inferInstanceAs (NormedSpace ℂ G)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_CoordinatesMetric
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite-coordinate smooth bundles and their metrics. -/

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky
open ComplexGrassmann
variable {S ι : Type*} [Fintype S] [Fintype ι]

variable (K : ι → ℕ) (label : S → Option ι) (d : ℕ) (hd : Fintype.card S=d)

attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.finiteCoordinateHilbertInner

instance finiteCoordinateBundle_norm (P : ProjectiveProduct K) :
    NormedAddCommGroup (FiniteCoordinateBundle K label d hd P) := changeModelFiberNorm _ _ P
instance finiteCoordinateBundle_normedSpace (P : ProjectiveProduct K) :
    NormedSpace ℂ (FiniteCoordinateBundle K label d hd P) := changeModelFiberNormedSpace _ _ P

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_LineStage
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Doubling stages of line bundles and their Hilbert direct sums. -/

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

attribute [instance] LineStage.finiteSlot

end Kaplansky

end

namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} [Fintype ι] {K : ι → ℕ}

/-- The actual stage fibers have their finite-dimensional Hilbert-space
instances directly from the finite orthogonal sum model. -/
instance lineStage_finite (a : LineStage K) (y : ProjectiveProduct K) :
    FiniteDimensional ℂ (a.Fiber y) :=
  inferInstanceAs (FiniteDimensional ℂ (EuclideanSpace ℂ a.Slot))
instance lineStage_complete (a : LineStage K) (y : ProjectiveProduct K) :
    CompleteSpace (a.Fiber y) :=
  inferInstanceAs (CompleteSpace (EuclideanSpace ℂ a.Slot))

end Kaplansky

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Monoid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordered Cuntz monoid and compression by its order unit. -/

noncomputable section
open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A coisometry supported on the first half of the columns gives two
orthogonal isometries in the undoubled algebra. -/
theorem properlyInfinite_of_coisometry_half
    (Y : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) (hY : Y * star Y = 1)
    (hzero : ∀ i j, Y i (Sum.inr j) = 0) :
    ProperlyInfinite (CStarMatrix ι ι A) := by
  let s : CStarMatrix ι ι A := CStarMatrix.ofMatrix fun i j => star (Y (Sum.inl j) (Sum.inl i))
  let t : CStarMatrix ι ι A := CStarMatrix.ofMatrix fun i j => star (Y (Sum.inr j) (Sum.inl i))
  have hs (i j : ι) : s i j = star (Y (Sum.inl j) (Sum.inl i)) := rfl
  have ht (i j : ι) : t i j = star (Y (Sum.inr j) (Sum.inl i)) := rfl
  have he (i j : ι ⊕ ι) : (∑ k : ι, Y i (Sum.inl k) * star (Y j (Sum.inl k))) =
      if i = j then 1 else 0 := by
    have h := congrArg (fun M : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A => M i j) hY
    simpa [CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply, Fintype.sum_sum_type, hzero, Matrix.one_apply, CStarMatrix.one_apply] using h
  refine ⟨s, t, ?_, ?_, ?_⟩
  · ext i j
    simpa [hs, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply, Matrix.one_apply, CStarMatrix.one_apply] using he (Sum.inl i) (Sum.inl j)
  · ext i j
    simpa [ht, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply, Matrix.one_apply, CStarMatrix.one_apply] using he (Sum.inr i) (Sum.inr j)
  · ext i j
    simpa [hs, ht, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply] using he (Sum.inl i) (Sum.inr j)

/-- Invertible rectangular row Gram gives a genuine coisometry by inverse
square-root normalization. The zero column block is retained. -/
theorem properlyInfinite_of_invertible_rectangular_gram
    (v : Matrix (ι ⊕ ι) ι A)
    (hv : IsUnit (CStarMatrix.ofMatrix (v * v.conjTranspose))) :
    ProperlyInfinite (CStarMatrix ι ι A) := by
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℝ (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) :=
    CStarAlgebra.instNonnegSpectrumClass'
  let X : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A := CStarMatrix.ofMatrix (Matrix.fromCols v 0)
  let Q : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A := X * star X
  have hQ : Q = CStarMatrix.ofMatrix (v * v.conjTranspose) := by
    apply CStarMatrix.ext
    intro i j
    change (∑ k : ι ⊕ ι,
      (Sum.elim (v i) (fun _ => 0) k) * star (Sum.elim (v j) (fun _ => 0) k)) =
      ∑ k : ι, v i k * star (v j k)
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul,
      Finset.sum_const_zero, add_zero]
  have hpos : IsStrictlyPositive Q := (hQ.symm ▸ hv).isStrictlyPositive (mul_star_self_nonneg X)
  let L := Q ^ (-(1 / 2) : ℝ)
  have hL : star L = L := (CFC.rpow_nonneg (a := Q) (y := (-(1 / 2) : ℝ))).isSelfAdjoint.star_eq
  apply properlyInfinite_of_coisometry_half (L * X)
  · calc
      L * X * star (L * X) = L * Q * L := by simp only [star_mul, hL, Q, mul_assoc]
      _ = 1 := CFC.conjugate_rpow_neg_one_half Q hpos
  · intro i j
    have hX (k : ι ⊕ ι) : X k (Sum.inr j) = 0 := rfl
    simp only [CStarMatrix.mul_apply, hX, mul_zero, Finset.sum_const_zero]

/-- Approximate compression of a doubled identity already forces proper
infiniteness, using the radius-one invertibility criterion. -/
theorem properlyInfinite_of_cuntzLE_double_unit
    (h : CuntzLE (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) A) (1 : Matrix ι ι A)) :
    ProperlyInfinite (CStarMatrix ι ι A) := by
  obtain ⟨v, hv⟩ := (CuntzLE.iff_approx _ _).mp h 1 zero_lt_one
  simp only [Matrix.mul_one] at hv
  apply properlyInfinite_of_invertible_rectangular_gram v
  let Q := CStarMatrix.ofMatrix (v * v.conjTranspose)
  have hnorm : ‖1 - Q‖ < 1 := hv
  have hu := (Units.oneSub (1 - Q) hnorm).isUnit
  simpa only [Units.val_oneSub, sub_sub_cancel] using hu

theorem properlyInfinite_of_cuntzUnit_compression (k : ℕ)
    (h : (2*k) • cuntzUnit A 1 ≤ k • cuntzUnit A 1) :
    ProperlyInfinite (CStarMatrix (Fin k) (Fin k) A) := by
  rw [cuntzUnit_nsmul, cuntzUnit_nsmul] at h
  have hc : CuntzLE (1 : Matrix (Fin (2*k)) (Fin (2*k)) A) (1 : Matrix (Fin k) (Fin k) A) :=
    (cuntzClass_le _ _).mp h
  have hsum : CuntzLE (1 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) A)
      (1 : Matrix (Fin k) (Fin k) A) := by
    rw [two_mul] at hc
    have he := (cuntzEquivalent_submatrix_equiv
      (1 : Matrix (Fin (k+k)) (Fin (k+k)) A) finSumFinEquiv).1.trans hc
    simpa using he
  exact properlyInfinite_of_cuntzLE_double_unit hsum

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.OrderedStates_RationalCone
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Rational cones and extension of positive states on ordered groups. -/

namespace Kaplansky

section
open Set LinearMap
variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis

The Riesz extension declarations below are adapted from Mathlib.Analysis.Convex.Cone.Extension.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Convex/Cone/Extension.lean

This code has been modified.
-/

/-- M. **Riesz extension theorem**: given a convex cone `s` in a vector space `E`, a submodule `p`,
and a linear `f : p → ℝ`, assume that `f` is nonnegative on `p ∩ s` and `p + s = E`. Then
there exists a globally defined linear function `g : E → ℝ` that agrees with `f` on `p`,
and is nonnegative on `s`. -/
theorem rational_riesz_extension (s : PointedCone ℚ E) (f : E →ₗ.[ℚ] ℝ)
    (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) :
    ∃ g : E →ₗ[ℚ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x ∈ s, 0 ≤ g x := by
  rcases RationalRieszExtension.exists_top s f nonneg dense
    with ⟨⟨g_dom, g⟩, ⟨-, hfg⟩, rfl : g_dom = ⊤, hgs⟩
  refine ⟨g.comp (LinearMap.id.codRestrict ⊤ fun _ ↦ trivial), ?_, ?_⟩
  · exact fun x => (hfg rfl).symm
  · exact fun x hx => hgs ⟨x, _⟩ hx

end

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

/-- A normalized monotone real-valued additive state on an ordered group
with an order unit. Positive unit multiples must not be nonpositive.
Neither linear order nor unperforation of the group is assumed. -/
theorem orderedGroup_normalized_state (u : G) (hu : 0 ≤ u)
    (hn : ∀ n : ℕ, 0 < n → ¬ n • u ≤ 0)
    (hb : ∀ g : G, ∃ N : ℕ, -(N • u) ≤ g) :
    ∃ f : G →+ ℝ, Monotone f ∧ f u = 1 := by
  let v : DivisibleHull G := u
  have hv : v ≠ 0 := orderedGroupRationalCone_unit_ne_zero u hn
  let p : DivisibleHull G →ₗ.[ℚ] ℝ := LinearPMap.mkSpanSingleton v 1 hv
  have hp : ∀ x : p.domain, (x : DivisibleHull G) ∈ orderedGroupRationalCone → 0 ≤ p x := by
    rintro ⟨x,hx⟩ hxc
    obtain ⟨q,rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hq : 0 ≤ q := orderedGroupRationalCone_unit_scalar u hn hxc
    change 0 ≤ LinearPMap.mkSpanSingleton' v (1 : ℝ) _ ⟨q • v, _⟩
    rw [LinearPMap.mkSpanSingleton'_apply]
    simpa using (smul_nonneg hq (zero_le_one : (0 : ℝ) ≤ 1))
  have hd : ∀ y : DivisibleHull G, ∃ x : p.domain, (x : DivisibleHull G)+y ∈ orderedGroupRationalCone := by
    intro y
    obtain ⟨N,hN⟩ := orderedGroupRationalCone_cofinal u hu hb y
    exact ⟨⟨(N : ℚ) • v, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)⟩,hN⟩
  obtain ⟨g,hg,hpos⟩ := rational_riesz_extension orderedGroupRationalCone p hp hd
  let f : G →+ ℝ := g.toAddMonoidHom.comp (DivisibleHull.coeAddMonoidHom G)
  have hfpos : ∀ x : G, 0 ≤ x → 0 ≤ f x := by
    intro x hx
    exact hpos _ (orderedGroupRationalCone_coe hx)
  refine ⟨f,?_,?_⟩
  · intro a b hab
    have h := hfpos (b-a) (sub_nonneg.mpr hab)
    rwa [map_sub,sub_nonneg] at h
  · have he := hg ⟨v,Submodule.mem_span_singleton_self v⟩
    change g v = 1
    rw [he]
    exact LinearPMap.mkSpanSingleton_apply ℚ ℚ hv (1 : ℝ)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Quasitrace_Extension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix order and the normalization of genuine corner extensions. -/

section

noncomputable section
open scoped ComplexOrder BigOperators CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A n : Type*} [CStarAlgebra A] [Fintype n] [DecidableEq n]

theorem corner_nonneg (i : n) {a : A} (ha : 0 ≤ a) : 0 ≤ corner i a := by
  obtain ⟨x, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  rw [← corner_mul, ← corner_star]
  exact star_mul_self_nonneg _

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Quasitrace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Corner-compatible spectral quasitraces and nonunital abelian complex linearity. -/

open scoped Matrix CStarAlgebra ComplexStarModule ComplexOrder

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance] matrixRealFunctionalCalculus matrixNonUnitalRealFunctionalCalculus matrixNonnegSpectrum
variable {A : Type*} [CStarAlgebra A]

def spectralCornerHom {n : ℕ} (i : Fin n) : A →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) A where
  toFun := corner i
  map_zero' := corner_zero i
  map_add' := corner_add i
  map_mul' a b := (corner_mul i a b).symm
  map_smul' := corner_smul i
  map_star' a := (corner_star i a).symm

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_SmallChains
attribute [-instance] _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Simplicial gluing, small singular subcomplexes, and cover meshes. -/

open CategoryTheory Topology Filter
section
variable {P X : Type} [PseudoMetricSpace P] [CompactSpace P] [TopologicalSpace X]

open Simplicial
variable {X : Type} [TopologicalSpace X]

instance standardSimplexMetricSpace (Index : Type*) [Fintype Index] :
    MetricSpace (OAI.SStd ℝ Index) :=
  (OAI.SStd.isEmbedding_toFun_comp_weights ℝ Index).comapMetricSpace
    (fun simplex => (simplex.weights : Index → ℝ))

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_Simplex
attribute [-instance] _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Affine simplex chains, mesh geometry, and universal subdivision. -/

section
open CategoryTheory Limits AlgebraicTopology Simplicial Convexity

instance simplexMetricSpace {κ : Type} [Fintype κ] : MetricSpace (OAI.SStd ℝ κ) :=
  Topology.IsEmbedding.comapMetricSpace
    (fun point : OAI.SStd ℝ κ => (point.weights : κ → ℝ))
    (OAI.SStd.isEmbedding_toFun_comp_weights ℝ κ)

end

open CategoryTheory Limits AlgebraicTopology Simplicial Convexity

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_Thom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Thom spaces of line stages, disk collapse, quotient maps, and homology. -/

section
open Bundle Topology Set OnePoint

open ComplexGrassmann
variable {ι : Type} [Fintype ι] {K : ι → ℕ}

instance lineStageTotal_locallyCompactSpace (a : LineStage K) :
    LocallyCompactSpace (TotalSpace a.Model a.Fiber) :=
  ChartedSpace.locallyCompactSpace (ProjectiveProduct K × a.Model) _

end

open Bundle Topology CategoryTheory OnePoint

end Kaplansky

end

end OAI
end


