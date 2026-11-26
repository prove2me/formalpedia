-- Prove2me | solution 1 for Auto.convexHull_subset_of_binary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:06:34.730663+00:00
-- url     : https://prove2.me/submissions/5ebe8410-6f7e-4bcc-a1e8-b673724e3232

module
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Definitions.Def_LeanNct_Auto_MultilinearInterpolation

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto
namespace Auto
theorem _root_.solution
    {E : Type*} [AddCommMonoid E] [Module ℝ E] {S G : Set E}
    (hS : S ⊆ G)
    (hbinary : ∀ x ∈ G, ∀ y ∈ G, ∀ a b : ℝ,
      0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ G) :
    convexHull ℝ S ⊆ G :=
  convexHull_min hS ((convex_iff_add_mem).2 hbinary)
end Auto
