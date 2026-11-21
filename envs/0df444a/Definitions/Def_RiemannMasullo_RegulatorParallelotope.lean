-- Prove2me | Definitions.Def_RiemannMasullo_RegulatorParallelotope
-- name    : RiemannMasullo_RegulatorParallelotope
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-21T00:11:26.946265+00:00
-- url     : https://prove2.me/theorems/00d4c25d-8f04-4f22-8e3d-487904905526
-- title:
--   Half-open fundamental parallelotope of the unit regulator lattice
-- statement:
--   The real basis extending an integral basis of the regulator lattice determines its half-open fundamental parallelotope.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L179-L182

import Mathlib
set_option maxSynthPendingDepth 8
open scoped Classical
noncomputable section
namespace RiemannMasullo
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]
variable (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
def regulatorParallelotope : Set (logSpace F) :=
  ZSpan.fundamentalDomain ((b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F))

end RiemannMasullo


