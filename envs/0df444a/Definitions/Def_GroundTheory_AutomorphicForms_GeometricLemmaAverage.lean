-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
-- name    : GroundTheory_AutomorphicForms_GeometricLemmaAverage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:57.846104+00:00
-- url     : https://prove2.me/theorems/1c4e02f3-524a-4a17-a49e-6243f5653d00
-- title:
--   Geometric Lemma Average
-- statement:
--   Definitions and structural lemmas for Geometric Lemma Average, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Set
section Cosets
variable {α : Type*} [Group α] {W : Type*} [AddCommGroup W]
end Cosets
section Average
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
def rightStab (f : G → W) : Subgroup G where
  carrier := {g | ∀ x, f (x * g) = f x}
  mul_mem' {a b} ha hb x := by
    show f (x * (a * b)) = f x
    rw [← mul_assoc, hb, ha]
  one_mem' x := by
    show f (x * 1) = f x
    rw [mul_one]
  inv_mem' {a} ha x := by
    show f (x * a⁻¹) = f x
    have := ha (x * a⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm
def avgSub (K : Subgroup G) (S : Subgroup K) (f : G → W) (x : G) : W :=
  ((S.index : ℂ)⁻¹) • ∑ᶠ q : K ⧸ S, f (x * ((Quotient.out q : K) : G))
def avgOver (K : Subgroup G) (f : G → W) (x : G) : W :=
  avgSub K ((rightStab f).subgroupOf K) f x
variable {K : Subgroup G} {f : G → W}
abbrev AvgFinite (K : Subgroup G) (f : G → W) : Prop := (rightStab f).relIndex K ≠ 0
end Average
section Average2
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
  {K : Subgroup G} {f : G → W}
end Average2
section Topological
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W : Type*} [AddCommGroup W] [Module ℂ W]
end Topological
section Volume
variable {G : Type*} [Group G]
def relVol (K₀ K : Subgroup G) : ℝ := (K₀.relIndex K : ℝ) / (K.relIndex K₀)
end Volume
end Parabolic
end GroundTheory.Automorphic


