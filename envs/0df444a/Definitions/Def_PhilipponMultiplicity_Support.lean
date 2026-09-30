-- Prove2me | Definitions.Def_PhilipponMultiplicity_Support
-- name    : PhilipponMultiplicity_Support
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-23T20:31:34.804463+00:00
-- url     : https://prove2.me/theorems/e0783158-6c69-4f5e-bb31-d61e8e268799
-- title:
--   Geometric support — reembeddings and projective closures
-- statement:
--   One-factor products, group isomorphisms regular in both directions, actual Zariski closures, and regular extensions of every translation.
--
--   Compiled, admission-free definition bundle. Theorems asserting its substantive properties remain open targets in the full-paper goal.
-- source:
--   Philippon 1986, §§2–5; 1987 corrections/addenda. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionFour
import Definitions.Def_PhilipponMultiplicity_SectionFive
import Definitions.Def_PhilipponMultiplicity_Corollaries

set_option autoImplicit false
open scoped BigOperators Topology
noncomputable section
namespace PhilipponMultiplicity
universe u

def singleGroupProduct {K : Type u} [Field K]
    (E : EmbeddedCommutativeGroup K) : EmbeddedGroupProduct K :=
  ⟨1, by omega, fun _ => E⟩

/-- An isomorphism of the actual groups, regular in both directions. -/
structure AlgebraicReembedding {K : Type u} [Field K]
    (E F : EmbeddedCommutativeGroup K) where
  equivalence : E.Point ≃+ F.Point
  regular : MultiProjectiveSpace.IsRegularAlong
    (projectiveSpace K E.ambientDimension) (projectiveSpace K F.ambientDimension)
    (fun x : E.Point => fun _ => x.val) (fun x => fun _ => (equivalence x).val)
  inverse_regular : MultiProjectiveSpace.IsRegularAlong
    (projectiveSpace K F.ambientDimension) (projectiveSpace K E.ambientDimension)
    (fun x : F.Point => fun _ => x.val) (fun x => fun _ => (equivalence.symm x).val)

def groupProjectiveClosure {K : Type u} [Field K] (G : EmbeddedGroupProduct K) :
    Set G.ambient.Point :=
  @closure _ G.ambient.zariskiTopology (Set.range G.embedding)

/-- Every translation extends to a regular map of the actual projective closure. -/
def TranslationsExtendToClosure {K : Type u} [Field K] (G : EmbeddedGroupProduct K) : Prop :=
  ∀ g : G.Point, ∃ f : G.ambient.Point → G.ambient.Point,
    (∀ x ∈ groupProjectiveClosure G, f x ∈ groupProjectiveClosure G) ∧
    G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => f x.val) ∧
    ∀ x : G.Point, f (G.embedding x) = G.embedding (g + x)

end PhilipponMultiplicity


