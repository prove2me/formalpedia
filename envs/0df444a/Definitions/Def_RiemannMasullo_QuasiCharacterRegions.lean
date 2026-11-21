-- Prove2me | Definitions.Def_RiemannMasullo_QuasiCharacterRegions
-- name    : RiemannMasullo_QuasiCharacterRegions
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-20T22:51:37.741372+00:00
-- url     : https://prove2.me/theorems/b0040457-6cbe-4cdf-873f-194c79ef4988
-- title:
--   Vertical strips and half-planes of quasi-characters
-- statement:
--   A relative strip is the preimage of a real set under the abscissa. A right half-plane is the open preimage of an upper ray, and a component strip additionally prescribes the restriction of the character to the kernel of the module.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/Ch03_IdelicZeta/Sec1.lean#L40-L152

import Mathlib
import Theorems.Thm_RiemannMasullo_continuous_quasiCharacterAbscissa
import Definitions.Def_RiemannMasullo_QuasiCharacterAbscissa

noncomputable section
namespace RiemannMasullo
open Function Topology
open scoped NNReal
variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)
local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)
def normOneRestriction : C(QuasiCharacter G, QuasiCharacter m.ker) :=
  let i : m.ker →ₜ* G := ⟨m.ker.subtype, continuous_subtype_val⟩
  ⟨fun c => c.comp i, i.continuous_comp_left⟩
def relativeVerticalStrip (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (I : Set ℝ) :
    Set (QuasiCharacter G) :=
  quasiCharacterAbscissa m hm hne ⁻¹' I
def relativeRightHalfPlane (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (a : ℝ) :
    TopologicalSpace.Opens (QuasiCharacter G) :=
  ⟨relativeVerticalStrip m hm hne (Set.Ioi a),
    isOpen_Ioi.preimage (continuous_quasiCharacterAbscissa m hm hne)⟩
def componentVerticalStrip (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (χ : PontryaginDual m.ker) (I : Set ℝ) : Set (QuasiCharacter G) :=
  relativeVerticalStrip m hm hne I ∩ {c | ∀ g : m.ker, normOneRestriction m c g = (χ g : ℂ)}
end RiemannMasullo


