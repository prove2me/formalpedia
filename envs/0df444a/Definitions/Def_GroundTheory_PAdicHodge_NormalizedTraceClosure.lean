-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
-- name    : GroundTheory_PAdicHodge_NormalizedTraceClosure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:17.949414+00:00
-- url     : https://prove2.me/theorems/a6447577-13d4-45a4-94a9-a52c94c70db7
-- title:
--   Normalized Trace Closure
-- statement:
--   Definitions and structural lemmas for Normalized Trace Closure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceClosure.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.PAdicHodge
open UniformSpace Topology Filter Set
noncomputable section
variable {p : ℕ} [Fact p.Prime]
section Closure
variable (E : IntermediateField ℚ_[p] (PadicAlgCl p))
def closureInCp : Set ℂ_[p] :=
  closure (((↑) : PadicAlgCl p → ℂ_[p]) '' (E : Set (PadicAlgCl p)))
variable {E} in
theorem coe_mem_closureInCp {y : PadicAlgCl p} (hy : y ∈ E) : (y : ℂ_[p]) ∈ closureInCp E :=
  subset_closure ⟨y, hy, rfl⟩
def toClosureInCp (y : E) : closureInCp E :=
  ⟨((y : PadicAlgCl p) : ℂ_[p]), coe_mem_closureInCp y.2⟩
theorem isometry_toClosureInCp : Isometry (toClosureInCp E) :=
  Isometry.of_dist_eq fun x y => by
    change dist ((x : PadicAlgCl p) : ℂ_[p]) ((y : PadicAlgCl p) : ℂ_[p]) = dist x y
    rw [UniformSpace.Completion.dist_eq]
    rfl
theorem denseRange_toClosureInCp : DenseRange (toClosureInCp E) := by
  rw [DenseRange, Topology.IsInducing.subtypeVal.dense_iff]
  rintro ⟨x, hx⟩
  have : Subtype.val '' range (toClosureInCp E) =
      ((↑) : PadicAlgCl p → ℂ_[p]) '' (E : Set (PadicAlgCl p)) := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
  rw [this]
  exact hx
theorem isDenseInducing_toClosureInCp : IsDenseInducing (toClosureInCp E) :=
  (isometry_toClosureInCp E).isUniformInducing.isDenseInducing (denseRange_toClosureInCp E)
variable (R : PadicAlgCl p → PadicAlgCl p)
def extendOnClosure : closureInCp E → ℂ_[p] :=
  (isDenseInducing_toClosureInCp E).extend fun y : E => ((R y : PadicAlgCl p) : ℂ_[p])
open Classical in

def extendToClosure (x : ℂ_[p]) : ℂ_[p] :=
  if hx : x ∈ closureInCp E then extendOnClosure E R ⟨x, hx⟩ else 0
variable {E R}
section Bounded
variable {c : ℝ} (hadd : ∀ y ∈ E, ∀ z ∈ E, R (y + z) = R y + R z)
  (hbound : ∀ y ∈ E, ‖R y‖ ≤ c * ‖y‖)
include hadd
include hbound
section Projection
variable {k : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] k]
  (hkE : k ≤ E) (hmaps : ∀ y ∈ E, R y ∈ k) (hfix : ∀ a ∈ k, R a = a)
  (hmul : ∀ a ∈ k, ∀ y ∈ E, R (a * y) = a * R y)
end Projection
section Galois
variable {K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)}
omit hadd hbound in
variable (E R) in

def kernelInCp : Set ℂ_[p] :=
  closureInCp E ∩ extendToClosure E R ⁻¹' {0}
variable {k : IntermediateField ℚ_[p] (PadicAlgCl p)}
  (hkE : k ≤ E) (hmaps : ∀ y ∈ E, R y ∈ k) (hfix : ∀ a ∈ k, R a = a)
  (γ : Gal(PadicAlgCl p/K₀)) (hγ : ∀ y ∈ E, γ y ∈ E) (hγR : ∀ y ∈ E, R (γ y) = γ (R y))
  {C : ℝ} (hC : ∀ y ∈ E, R y = 0 → ‖y‖ ≤ C * ‖γ y - y‖)
include hkE hmaps hfix hC
end Galois
end Bounded
end Closure
end
end GroundTheory.PAdicHodge


