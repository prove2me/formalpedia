-- Prove2me | Definitions.Def_RiemannMasullo_QuasiCharacterAbscissa
-- name    : RiemannMasullo_QuasiCharacterAbscissa
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-20T22:47:19.46872+00:00
-- url     : https://prove2.me/theorems/1860aba7-dc71-4f15-8eb9-eaf40addb729
-- title:
--   Quasi-characters, their abscissas and their duals
-- statement:
--   A quasi-character is a continuous complex-valued multiplicative character. Its abscissa is the ratio of the logarithm of its modulus to the logarithm of the group module at a chosen element of nonunit module. The dual is the module times the inverse character.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/Ch03_IdelicZeta/Sec1.lean#L30-L175

import Mathlib

noncomputable section
namespace RiemannMasullo
open Function Topology
open scoped NNReal
abbrev QuasiCharacter (G : Type*) [Group G] [TopologicalSpace G] := G →ₜ* ℂ
variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)

local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

def quasiCharacterAbscissa (_hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (c : QuasiCharacter G) : ℝ :=
  Real.log ‖c hne.choose‖ / Real.log (modℝ hne.choose)
def dualQuasiCharacter [IsTopologicalGroup G] (hm : Continuous m) (c : QuasiCharacter G) :
    QuasiCharacter G :=
  let n : QuasiCharacter G :=
    ⟨Complex.ofRealHom.toMonoidHom.comp (NNReal.toRealHom.toMonoidHom.comp
      ((Units.coeHom ℝ≥0).comp m)),
      Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (Units.continuous_val.comp hm))⟩
  n * c.comp (ContinuousMonoidHom.inv G)
end RiemannMasullo


