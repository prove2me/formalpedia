-- Prove2me | Definitions.Def_OAIQ042S012
-- name    : OAIQ042S012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:45:55.915713+00:00
-- url     : https://prove2.me/theorems/f4ba66a4-e400-4cac-a275-5df8f577228e
-- title:
--   Definitions bundle OAIQ042S012 of the split of OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 12 definitions. The definitions and types are `OAI.CriticalStrip.Diagram.deletionProjection`, `OAI.CriticalStrip.Diagram.mergeProjection`, `OAI.CriticalStrip.Diagram.oneSourcePair`, `OAI.CriticalStrip.Diagram.rationalResidualCoefficient`, `OAI.CriticalStrip.Diagram.sourceTransfer`, `OAI.CriticalStrip.Diagram.splitProjection`, `OAI.CriticalStrip.Diagram.vacantBottomSourceExtension`, `OAI.CriticalStrip.HoneycombBranch.RibbonRectangle.boundary`, `OAI.CriticalStrip.HoneycombBranch.RibbonRectangle.gauge`, `OAI.CriticalStrip.HoneycombBranch.RibbonRectangle.graph`, `OAI.CriticalStrip.HoneycombBranch.RibbonRectangle.start`, `OAI.CriticalStrip.HoneycombBranch.RibbonRectangle.turnEdge`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/StripMass, in whole or in part: [`StripMass_ArchTrig`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/ArchTrig.lean), [`StripMass_NodalExchange`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/NodalExchange.lean), [`StripMass_RibbonLocal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/RibbonLocal.lean), [`StripMass_RibbonWalk`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/RibbonWalk.lean), [`StripMass_SplitGluing`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/SplitGluing.lean), [`StripMass_SplitProjection`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/SplitProjection.lean), [`StripMass_VacuumDegree`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/VacuumDegree.lean).
--
--   **Imports.** It imports the bundles `OAIQ042S005`, `OAIQ042S007`, `OAIQ042S008` and `OAIQ042S009` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ042S013`; the proofs of `OAI.CriticalStrip.HoneycombBranch.finite_split`, `OAI.CriticalStrip.HoneycombBranch.step_turn` and `OAI.CriticalStrip.HoneycombBranch.strip_turn`.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/StripMass at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ042S005
import Definitions.Def_OAIQ042S007
import Definitions.Def_OAIQ042S008
import Definitions.Def_OAIQ042S009

section
-- module Solutions.OAIQ042_SS.StripMass_NodalExchange
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section






open Finset
open scoped Classical



def rationalResidualCoefficient (n : ℕ) (p : Pairing (n+1)) : SpectralField n :=
  (rationalResidualPolynomial n p).coeff n

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_VacuumDegree
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram




noncomputable section
open scoped BigOperators Classical



def sourceTransfer {K : Type*} [CommRing K] {n : ℕ} (w : Fin n → Tile → K) :
    Matrix (SourcePairing n) (SourcePairing n) K :=
  fun q p => lastCoefficient w q.val p.val

end




end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SplitProjection
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators



def splitProjection {K : Type*} [CommRing K] {n m : ℕ}
    (f : Fin n ↪o Fin m) (a : Position m) (w : Weights K) :
    Matrix (Pairing n) (Pairing m) K :=
  (functionMatrix (K:=K) (Pairing.map f)).transpose * localR a w



def mergeProjection {n m : ℕ} (r : ℕ) (hr : r+2≤n+1) :
    Matrix (Pairing n) (Pairing (n+1)) (SpectralField m) :=
  splitProjection (Fin.succAboveOrderEmb ⟨r+1,by omega⟩)
    (PartialColumn.rowPosition r hr) (mergeWeights (constF m phase))



def deletionProjection {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    Matrix (Pairing n) (Pairing (n+2)) (SpectralField m) :=
  (twoVacancyInsertion (K:=SpectralField m) r hr).transpose *
    localR (PartialColumn.rowPosition r hr) deletionWeights

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SplitGluing
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

def vacantBottomSourceExtension {K : Type*} [Zero K] {n : ℕ}
    (v : SourcePairing n → K) (p : SourcePairing (n+1)) : K :=
  if h : p ∈ Set.range SourcePairing.padBottom then v (Classical.choose h) else 0

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ArchTrig
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

def oneSourcePair : SourcePairing 1 := ⟨twoPair,twoPair_occupied _⟩

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RibbonLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch





noncomputable section
open scoped Classical
open Diagram Diagram.TurnNetwork Diagram.TurnDisk
namespace RibbonRectangle
section Geometry

variable (L : ℤ) (M N : ℕ)

variable {L M N}

variable (L M N) (F : Vertex → Pairing 6)

variable {L M N F}

variable (hM : 1≤M) (hN : 1≤N) (F : Vertex → Pairing 6)

abbrev start := TurnRectangle.startPairing (M:=M) (N:=N) (up L N F)
abbrev graph := TurnRectangle.edges hM hN (start (L:=L) F) (up L N F) (down L N F)
abbrev turnEdge := TurnRectangle.turns hM hN (start (L:=L) F) (up L N F) (down L N F)
abbrev boundary := TurnRectangle.bdry hM hN (start (L:=L) F) (TurnRectangle.starterGauge M N)
  (up L N F) (down L N F) (M*N)

end Geometry






end RibbonRectangle
end





end CriticalStrip.HoneycombBranch

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RibbonWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch





noncomputable section
open scoped Classical
open Diagram Diagram.TurnNetwork Diagram.TurnDisk FiniteBranchTree
namespace RibbonRectangle

variable {L : ℤ} {M N : ℕ}

variable (hM : 1≤M) (hN : 1≤N) (F : Vertex → Pairing 6)

abbrev gauge := (TurnRectangle.box hM hN (start (L:=L) F) (TurnRectangle.starterGauge M N)
  (up L N F) (down L N F) (M*N)).gauge

end RibbonRectangle






end





end CriticalStrip.HoneycombBranch

end OAI
end


