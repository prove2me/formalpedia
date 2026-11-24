-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:34.775466+00:00
-- url     : https://prove2.me/theorems/dfb8c8c5-432b-4100-b526-8cccf9a62d54
-- title:
--   Fibre St B
-- statement:
--   Definitions and structural lemmas for Fibre St B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}
structure Gen.Good (G : Gen x e) (w : Fin (D + 1) → ℂ) : Prop where
  w0 : w 0 ≠ 0
  ker : ∀ m, deh (x ∘ e) 0 m = 0 → deh w 0 m = 0
  dd : deh w 0 G.dd ≠ 0
  cc : deh w 0 G.cc ≠ 0
variable [DecidableEq ι] (G : Gen x e) {w : Fin (D + 1) → ℂ}
abbrev fib (x : ι → Ω) (e : Fin (D + 1) → ι) (w : Fin (D + 1) → ℂ) : Set (ι → ℂ) :=
  {z | z ∈ pts (coordIdeal ℤ x) ∧ ∀ k, z (e k) = w k}
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω}
  {e : Fin (D + 1) → ι} (G : Gen x e)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib


