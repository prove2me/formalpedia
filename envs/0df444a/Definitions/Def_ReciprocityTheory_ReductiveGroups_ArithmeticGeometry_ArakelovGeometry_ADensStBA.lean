-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStBA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStBA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:43.764444+00:00
-- url     : https://prove2.me/theorems/a10ed147-8648-4d21-a4ef-3e6c1c03f84c
-- title:
--   ADens St BA
-- statement:
--   Definitions and structural lemmas for ADens St BA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStBA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Topology
open scoped ComplexOrder
variable {κ : Type} [Fintype κ] {D : ℕ}
def evalConstSnd (w : ((k : Unit) → GlobalTheory κ k) → ℂ) : Ix κ → ℂ := fun p => w fun _ => p.2
def IsSheetParamB (P : Ideal (MRing (GlobalTheory κ)))
    (Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ))
    (U : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → Ix κ → ℂ) : Prop :=
  IsParam P U γ ∧ ∀ y ∈ U, Ψ (segre (ι := GlobalTheory κ) (γ y)) = Fin.cons 1 y
variable {P : Ideal (MRing (GlobalTheory κ))} {Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)}
  {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → Ix κ → ℂ}
def IsConeSetB (s : Set (Ix κ → ℂ)) : Prop :=
  ∀ (c : ℂ) (z : Ix κ → ℂ), c ≠ 0 → (c • z ∈ s ↔ z ∈ s)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


