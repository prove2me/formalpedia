-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:46.213785+00:00
-- url     : https://prove2.me/theorems/e0070974-f5c1-486e-8dd0-c9a00508277b
-- title:
--   Fibre St
-- statement:
--   Definitions and structural lemmas for Fibre St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
def prFib (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (w : Fin (D + 1) → ℂ) : Set (Ix κ → ℂ) :=
  {z | z ∈ pts (coordIdeal ℤ x) ∧ ∀ k, z (e k) = w k}
def IsDiscr (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (Δ : MvPolynomial (Fin (D + 1)) ℂ) : Prop :=
  Δ ≠ 0 ∧ ∀ w, eval w Δ ≠ 0 →
    (prFib x e w).Finite ∧ (prFib x e w).ncard = projDeg x e ∧
    (∀ z ∈ prFib x e w, ∃ (U : Set (Fin (D + 1) → ℂ)) (γ : (Fin (D + 1) → ℂ) → Ix κ → ℂ),
      IsOpen U ∧ w ∈ U ∧ DifferentiableOn ℂ γ U ∧ γ w = z ∧ ∀ w' ∈ U, γ w' ∈ prFib x e w') ∧
    ∀ (n : ℕ) (f : MvPolynomial (Ix κ) ℤ) (g : MvPolynomial (Fin (D + 1)) ℤ),
      f.IsHomogeneous n → g.IsHomogeneous n → aeval (x ∘ e) g = secTrace x e n (aeval x f) →
      eval w (map (Int.castRingHom ℂ) g) = ∑ᶠ z ∈ prFib x e w, eval z (map (Int.castRingHom ℂ) f)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


