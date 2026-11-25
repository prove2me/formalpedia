-- Prove2me | Definitions.Def_BasicResults_John
-- name    : BasicResults_John
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:30:44.501234+00:00
-- url     : https://prove2.me/theorems/5f02fc09-c56d-4716-9233-c0bf5c3b274e
-- title:
--   John
-- statement:
--   Definitions and structural lemmas for John, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean

module
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_CompactConvexHull
public import Definitions.Def_BasicResults_JohnIngredients
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Seminorm
public import Mathlib.Topology.Order.Compact
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open scoped InnerProductSpace ComplexConjugate
open RCLike (re)
namespace John
variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}
def Feasible (p : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))) :
    Set (EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :=
  {T | ∀ u, p (T u) ≤ ‖u‖}
def Contact (q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))) :
    Set (EuclideanSpace 𝕜 (Fin k)) :=
  {u | ‖u‖ = 1 ∧ ∀ x, re ⟪x, u⟫_𝕜 ≤ q x}
noncomputable def rankOneSA (u : EuclideanSpace 𝕜 (Fin k)) :
    EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
  (innerSL 𝕜 u).smulRight u
section DualProjection
variable {W : Type u} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
end DualProjection
end John


