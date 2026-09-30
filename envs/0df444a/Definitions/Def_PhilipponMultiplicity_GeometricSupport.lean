-- Prove2me | Definitions.Def_PhilipponMultiplicity_GeometricSupport
-- name    : PhilipponMultiplicity_GeometricSupport
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-23T20:32:36.379984+00:00
-- url     : https://prove2.me/theorems/42ab4c3a-87af-43f9-bfef-2a0e1ee9e730
-- title:
--   Geometric support — linear sections and bounded equations
-- statement:
--   Actual linear-subspace intersections, integer combinations of group generators, translation charts on finitely generated subgroups, and actual finite equations with a real degree bound.
--
--   Compiled, admission-free definition bundle. Theorems asserting its substantive properties remain open targets in the full-paper goal.
-- source:
--   Philippon 1986, §§2–5; 1987 corrections/addenda. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace PhilipponMultiplicity
universe u

def linearSlice {K : Type u} [Field K] (M : MultiProjectiveSpace K)
    (V : Set M.Point) (L : ∀ i : M.FactorIndex,
      Submodule K (Fin (M.ambientDimension i + 1) → K)) : Set M.Point :=
  {x ∈ V | ∀ i, (x i).rep ∈ L i}

def integerCombination {K : Type u} [Field K] {G : EmbeddedGroupProduct K}
    {m : ℕ} (γ : Fin m → G.Point) (σ : Fin m → ℤ) : G.Point :=
  ∑ i, (σ i) • γ i

/-- The translation hypothesis defining the original Masser–Wüstholz constant a. -/
def MWTranslationBound {K : Type u} [Field K] (G : EmbeddedGroupProduct K) (a : ℕ) : Prop :=
  ∀ Γ : Submodule ℤ G.Point, Γ.FG → ∀ g ∈ Γ,
    ∃ chart : PolynomialTranslationChart G g,
      (∀ x ∈ Γ, x ∈ chart.domain) ∧ ∀ i, chart.degree i ≤ a

/-- Actual homogeneous equations, with a real degree bound, cut out a subset of G. -/
def DefinedByEquations {K : Type u} [Field K] (G : EmbeddedGroupProduct K)
    (S : Set G.Point) (B : ℝ) : Prop :=
  ∃ equations : Finset G.CoordinateRing,
    (∀ P ∈ equations, ∃ D : G.FactorIndex → ℕ,
      G.ambient.IsHomogeneous P D ∧ ∀ i, (D i : ℝ) ≤ B) ∧
    S = {x | ∀ P ∈ equations, G.ambient.eval P (G.embedding x) = 0}

end PhilipponMultiplicity


