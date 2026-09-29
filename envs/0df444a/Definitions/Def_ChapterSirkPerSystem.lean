-- Prove2me | Definitions.Def_ChapterSirkPerSystem
-- name    : ChapterSirkPerSystem
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T02:53:14.339981+00:00
-- url     : https://prove2.me/theorems/bab2aab4-a68e-4844-8165-2db662b26475
-- title:
--   ChapterSirkPerSystem
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SirkPerSystem`, source chapter `BookProof/ChapterSirkPerSystem.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkPerSystem.lean

import Mathlib
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH9
import Definitions.Def_ChapterSirkSpectralGeometry
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesHashimoto
import Definitions.Def_ChapterNavierStokesDiffHashimoto
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich

/-!
# Chapter SirkPerSystem — aggregation bundle

`BookProof.ChapterSirkPerSystem` has no definition material of its own (all 7 of
its declarations are node theorems); its theorem statements use names from the
upstream chapters listed above.  This bundle has no declarations of its own — it
only pulls those upstream `Definitions.Def_*` modules into scope so the
`Thm_BookProof_ChapterSirkPerSystem_*` stubs and their solutions compile against
`import Definitions.Def_ChapterSirkPerSystem`.
-/

noncomputable section

namespace BookProof.ChapterSirkPerSystem

end BookProof.ChapterSirkPerSystem


