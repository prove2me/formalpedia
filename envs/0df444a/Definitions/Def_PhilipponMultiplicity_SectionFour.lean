-- Prove2me | Definitions.Def_PhilipponMultiplicity_SectionFour
-- name    : PhilipponMultiplicity_SectionFour
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-23T20:29:36.301712+00:00
-- url     : https://prove2.me/theorems/2f2f1d4b-9360-49c4-990e-497c6cb82e45
-- title:
--   Section 4 — translation charts and transverse coordinates
-- statement:
--   Actual locally closed subvarieties, polynomial translation charts/atlases, their degree bounds, and coordinate bases in the quotient by the actual tangent kernel.
--
--   Compiled, admission-free definition bundle. Theorems asserting its substantive properties remain open targets in the full-paper goal.
-- source:
--   Philippon 1986, §§2–5; 1987 corrections/addenda. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Differential

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u

/-- A subvariety of G, represented by an actual locally closed subset. -/
structure GroupSubvariety {K : Type u} [Field K] (G : EmbeddedGroupProduct K) where
  carrier : Set G.Point
  locallyClosed : @IsLocallyClosed _ G.zariskiTopology carrier

/-- Polynomial formulas for a translation, on one Zariski chart. -/
structure PolynomialTranslationChart {K : Type u} [Field K]
    (G : EmbeddedGroupProduct K) (g : G.Point) where
  domain : Set G.Point
  domain_open : @IsOpen _ G.zariskiTopology domain
  degree : G.FactorIndex → ℕ
  coordinates : G.ambient.Variable → G.CoordinateRing
  homogeneous : ∀ v, G.ambient.IsHomogeneous (coordinates v)
    (fun i => if i = v.1 then degree i else 0)
  represents : ∀ x ∈ domain, ∀ i : G.FactorIndex,
    ∃ h : (fun j => G.ambient.eval (coordinates ⟨i, j⟩) (G.embedding x)) ≠ 0,
      Projectivization.mk K
        (fun j => G.ambient.eval (coordinates ⟨i, j⟩) (G.embedding x)) h =
          G.embedding (g + x) i

structure PolynomialTranslationAtlas {K : Type u} [Field K]
    (G : EmbeddedGroupProduct K) (g : G.Point) where
  Index : Type u
  chart : Index → PolynomialTranslationChart G g
  covers : ∀ x : G.Point, ∃ a : Index, x ∈ (chart a).domain

/-- An embedding-dependent bound for actual translation formulas. -/
def TranslationDegreeBound {K : Type u} [Field K]
    (G : EmbeddedGroupProduct K) (c : G.FactorIndex → ℕ) : Prop :=
  ∀ g : G.Point, ∃ atlas : PolynomialTranslationAtlas G g,
    ∀ a : atlas.Index, ∀ i, (atlas.chart a).degree i ≤ c i

/-- Selected coordinate directions form a basis modulo the inverse image
of the subgroup tangent space. This records the reindexing on p. 377. -/
def IsTransverseCoordinateFamily {K : Type u} [NontriviallyNormedField K]
    {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension) : Prop :=
  let vectors := fun i =>
    (A.tangentKernel H.carrier).mkQ (Pi.single (directions i) 1)
  LinearIndependent K vectors ∧ Submodule.span K (Set.range vectors) = ⊤

end PhilipponMultiplicity


