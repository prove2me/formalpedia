-- Prove2me | Definitions.Def_OAIQ042S009
-- name    : OAIQ042S009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:42:39.898915+00:00
-- url     : https://prove2.me/theorems/c9eaf22e-6894-414a-8312-73b057214b2b
-- title:
--   Definitions bundle OAIQ042S009 of the split of OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 21 definitions and 1 theorem. The definitions and types are `OAI.CriticalStrip.Diagram.augmentedPhysicalWeights`, `OAI.CriticalStrip.Diagram.augmentedReversedWeights`, `OAI.CriticalStrip.Diagram.deformationWeights`, `OAI.CriticalStrip.Diagram.glueMatrix`, `OAI.CriticalStrip.Diagram.northNumerator`, `OAI.CriticalStrip.Diagram.reverseDeformationWeights`, `OAI.CriticalStrip.Diagram.sourceAugmentEmbedding`, `OAI.CriticalStrip.Diagram.sourceBlock`, `OAI.CriticalStrip.Diagram.sourceGlue`, `OAI.CriticalStrip.Diagram.transfer`, `OAI.CriticalStrip.Diagram.twoVacancyInsertion`, `OAI.CriticalStrip.Diagram.vacantProjection`, `OAI.CriticalStrip.Diagram.vacuumAugmentEmbedding`, `OAI.CriticalStrip.HoneycombBranch.RibbonRectangle.Matches`, `OAI.CriticalStrip.HoneycombBranch.RibbonRectangle.down`, `OAI.CriticalStrip.HoneycombBranch.RibbonRectangle.up`, `OAI.CriticalStrip.HoneycombBranch.ribbon`, `OAI.CriticalStrip.HoneycombConfiguration.equivWires`, `OAI.CriticalStrip.NorthHistory.Valid`, `OAI.CriticalStrip.NorthHistory.pairEquiv`, `OAI.CriticalStrip.TopArchConfiguration.equivArch`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/StripMass, in whole or in part: [`StripMass_DeformationWeights`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/DeformationWeights.lean), [`StripMass_HalfTurn`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/HalfTurn.lean), [`StripMass_HoneycombDictionary`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/HoneycombDictionary.lean), [`StripMass_NorthMass`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/NorthMass.lean), [`StripMass_NorthMerging`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/NorthMerging.lean), [`StripMass_PairingDiagrams`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/PairingDiagrams.lean), [`StripMass_ReversedConvergence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/ReversedConvergence.lean), [`StripMass_RibbonLocal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/RibbonLocal.lean), [`StripMass_SplitProjection`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/SplitProjection.lean), [`StripMass_VacuumClosure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/VacuumClosure.lean), [`StripMass_VacuumDegree`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/VacuumDegree.lean).
--
--   **Imports.** It imports the bundles `OAIQ042S002` and `OAIQ042S004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ042S012`.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/StripMass at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ042S002
import Definitions.Def_OAIQ042S004

section
-- module Solutions.OAIQ042_SS.StripMass_PairingDiagrams
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram
noncomputable section
open Finset


def transfer {n : ℕ} (u : Fin n → ℝ) : Matrix (Pairing n) (Pairing n) ℝ :=
  column (fun i => physicalWeights (3 * lambda - u i))



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_VacuumDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram




noncomputable section
open scoped BigOperators Classical



def northNumerator (n : ℕ) (p : SourcePairing n) : SpectralField n :=
  (rationalNodalPolynomial n p.val).coeff (n-1)

end




end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_VacuumClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators



def glueMatrix {K : Type*} [Zero K] [One K] {n : ℕ} (root : Fin n) :
    Matrix (Pairing n) (Pairing n) K :=
  fun p q => if Pairing.GluesAt root p q then 1 else 0







def sourceBlock {K : Type*} {n m : ℕ}
    (M : Matrix (Pairing (m+1)) (Pairing (n+1)) K) :
    Matrix (SourcePairing m) (SourcePairing n) K := fun p q => M p.val q.val



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NorthMerging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators


def sourceGlue {K : Type*} [CommRing K] (n : ℕ)
    (v w : SourcePairing n → K) : K :=
  v ⬝ᵥ (sourceBlock (glueMatrix (Fin.last n))).mulVec w

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SplitProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators



def vacantProjection {K : Type*} [Zero K] [One K] {n : ℕ} (b : Fin n) :
    Matrix (Pairing n) (Pairing n) K := Matrix.diagonal (fun p => if p.Occupied b then 0 else 1)


def twoVacancyInsertion {K : Type*} [CommRing K] {n : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    Matrix (Pairing (n+2)) (Pairing n) K :=
  functionMatrix (Pairing.map (Fin.succAboveOrderEmb (⟨r+1,by omega⟩ : Fin (n+2)))) *
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb (⟨r,by omega⟩ : Fin (n+1))))

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HoneycombDictionary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram Diagram.PathGraph

namespace HoneycombConfiguration
variable {N : ℕ} {b : BoundaryPort}



def equivWires (N : ℕ) (b : BoundaryPort) (hN : 1≤N) (hb : b ≠ .bottom 0) :
    HoneycombConfiguration N b ≃ WireConfiguration N (b.vertex N) where
  toFun D := D.toWire hN
  invFun D := ofWire D hN hb
  left_inv D := ofWire_toWire D hN hb
  right_inv D := toWire_ofWire D hN hb

end HoneycombConfiguration






end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DeformationWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open _root_.Matrix Set
open scoped BigOperators Classical


def augmentedPhysicalWeights (n : ℕ) : Fin (n+1) → Weights ℝ :=
  Fin.snoc (fun _ : Fin n=>physicalWeights (2*lambda)) northInjectionWeights

def deformationWeights (n : ℕ) (t : ℝ) : Fin (n+1+1) → Weights ℝ :=
  Fin.cons (physicalWeights (3*lambda-t)) (augmentedPhysicalWeights n)

end
end CriticalStrip.Diagram





namespace CriticalStrip.Diagram
noncomputable section
open _root_.Matrix
open scoped BigOperators Classical



def vacuumAugmentEmbedding (n : ℕ) : NonemptyPairing n ↪ NonemptyPairing (n+1) :=
  (Function.Embedding.trans (.inl) (sourceTopSplit n).toEmbedding)

def sourceAugmentEmbedding (n : ℕ) : SourcePairing n ↪ NonemptyPairing (n+1) :=
  (Function.Embedding.trans (.inr) (sourceTopSplit n).toEmbedding)

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ReversedConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open _root_.Matrix Set
open scoped BigOperators Classical

def augmentedReversedWeights (n : ℕ) : Fin (n+1) → Weights ℝ :=
  Fin.snoc (fun _ : Fin n=>physicalWeights lambda) northInjectionWeights

def reverseDeformationWeights (n : ℕ) (t : ℝ) : Fin (n+1+1) → Weights ℝ :=
  Fin.cons (physicalWeights t) (augmentedReversedWeights n)

end





end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HalfTurn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram

namespace TopArchConfiguration
variable {N : ℕ} {a b : ℤ}

@[simp] lemma toArch_ofArch (D : HoneycombConfiguration N (.bottom (b-a))) (hN : 1≤N) :
    (ofArch D hN).toArch hN=D := by
  apply HoneycombConfiguration.ext
  exact D.toHoneycombAssignment.turn_turn b

def equivArch (N : ℕ) (a b : ℤ) (hN : 1≤N) :
    TopArchConfiguration N a b ≃ HoneycombConfiguration N (.bottom (b-a)) where
  toFun D := D.toArch hN
  invFun D := ofArch D hN
  left_inv D := ofArch_toArch D hN
  right_inv D := toArch_ofArch D hN

end TopArchConfiguration
end
end CriticalStrip





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NorthMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram

namespace NorthHistory
variable {N m : ℕ}

def Valid (l r : Fin m → Configuration (N+1)) : Prop :=
  ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn l)≠0 ∧
  ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn r)≠0 ∧
  ∃p q : Pairing (N+1), ColumnChain.Runs (empty (N+1)) (List.ofFn l) p ∧
    ColumnChain.Runs (empty (N+1)) (List.ofFn r) q ∧ p.GluesAt (Fin.last N) q

def pairEquiv : NorthHistory N m ≃
    {lr : (Fin m → Configuration (N+1)) × (Fin m → Configuration (N+1)) // Valid lr.1 lr.2} where
  toFun h := ⟨(h.left,h.right),h.nzleft,h.nzright,h.realizes⟩
  invFun h := ⟨h.val.1,h.val.2,h.property.1,h.property.2.1,h.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end NorthHistory
end
end CriticalStrip





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

def up (t : ℕ) : Pairing 6 := F (L+((t/N:ℕ):ℤ),((t%N:ℕ):ℤ),true)
def down (t : ℕ) : Pairing 6 := F (L+((t/N:ℕ):ℤ),((t%N:ℕ):ℤ),false)

variable {L M N F}

variable (hM : 1≤M) (hN : 1≤N) (F : Vertex → Pairing 6)


def Matches : Prop := ∀ v p, Inside L M N v → Inside L M N (neighbor v p) → ∀ l : Fin 2,
  (F v).Occupied (lane v.2.2 p l) ↔ (F (neighbor v p)).Occupied (lane (!v.2.2) p (1-l))

end Geometry






end RibbonRectangle
end

 

 

noncomputable section
open scoped Classical
open Diagram FiniteBranchTree

 
def ribbon {s : State} {l : List Bool} (h : RibbonSimple s l) (v : Vertex) : Pairing 6 :=
  ⟨ribbonArcs v.2.2 (routes s l v),h v⟩

end
end CriticalStrip.HoneycombBranch

end OAI
end


