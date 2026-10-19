-- Prove2me | Definitions.Def_MazurTransfer_LineBundleGeometricDegreeZeroData
-- name    : MazurTransfer_LineBundleGeometricDegreeZeroData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:51:54.947639+00:00
-- url     : https://prove2.me/theorems/4b88e0cf-1a0e-4a73-8296-f50b20133be3
-- title:
--   Euler characteristic and geometric algebraic equivalence for actual curve line bundles over an arbitrary field
-- statement:
--   For a scheme X over a field k with a two-affine cover, define the Euler characteristic of a line bundle M by
--
--   $$\chi_k(M)=\dim_k H^0(X,M)-\dim_k H^1(X,M).$$
--
--   Geometric algebraic equivalence to zero means that the actual pullback of M is algebraically equivalent to zero over every algebraically closed field extension of k. These are the original constructors, with their complete types and values preserved; no closure hypothesis is imposed on k. The named downstream consumer is the Euler-characteristic criterion and geometric divisor presentations for the existing order-13 Picard family.
-- source:
--   Original MazurTheorem LineBundleGeometricDegreeZeroOverField curveEulerChar and GeometricallyAlgEquivZero constructors. Official Anthropic FLT relative Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original Euler-characteristic function and geometric
algebraic-equivalence predicate for an arbitrary field. Named downstream
consumer: geometric degree-zero Picard field-point divisor presentations.
Original MazurTheorem LineBundleGeometricDegreeZeroOverField constructors;
official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard
namespace MazurTransfer.LineBundleFieldComparison
noncomputable def curveEulerChar {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k)) (𝒱 : X.TwoAffineOpenCover) (M : X.Modules) : ℤ :=
  (Module.finrank k (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M).H1

/-- A geometric degree-zero condition, quantified over algebraically closed extensions.
It concerns the actual sheaf and actual base-change scheme, without a rational-point
parametrization of all closed points. -/
def GeometricallyAlgEquivZero {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
    IsAlgEquivZero (pullback.snd x (Scheme.TwoAffineOpenCover.specMap k K))
      ((Scheme.Modules.pullback (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k K))).obj M)


end MazurTransfer.LineBundleFieldComparison
#print axioms MazurTransfer.LineBundleFieldComparison.curveEulerChar
#print axioms MazurTransfer.LineBundleFieldComparison.GeometricallyAlgEquivZero


