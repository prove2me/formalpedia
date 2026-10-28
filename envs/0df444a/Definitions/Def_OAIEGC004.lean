-- Prove2me | Definitions.Def_OAIEGC004
-- name    : OAIEGC004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T06:54:58.986986+00:00
-- url     : https://prove2.me/theorems/e6b37ca1-10d6-4978-955e-7f6b9c5c7c56
-- title:
--   Definitions bundle OAIEGC004 of the split of OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`, carved from OpenAI's openai/math development (OpenAI, *A finitely generated counterexample to the Eilenberg–Ganea conjecture*, OpenAI Math Release, September 23, 2026, result family 249, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 19 definitions and 10 theorems. The definitions and types are `OAI.EilenbergGanea.SeedChainCertificate.contraction`, `OAI.EilenbergGanea.SeedConnection.Related`, `OAI.EilenbergGanea.SeedConnection.circleLabel`, `OAI.EilenbergGanea.SeedConnection.connection`, `OAI.EilenbergGanea.SeedConnection.edgeLocal`, `OAI.EilenbergGanea.SeedConnection.faceLocal`, `OAI.EilenbergGanea.SeedConnection.radialLabel`, `OAI.EilenbergGanea.SeedConnection.rankFin`, `OAI.EilenbergGanea.SeedConnection.roseLoop`, `OAI.EilenbergGanea.SeedConnection.upLabel`, `OAI.EilenbergGanea.SourceTransport.seedWalk`, `OAI.EilenbergGanea.instLTSeedCell`, `OAI.EilenbergGanea.instLinearOrderSeedCell`, `OAI.EilenbergGanea.instLinearOrderSeedCell_1`, `OAI.EilenbergGanea.seedLetterUnit`, `OAI.EilenbergGanea.seedYUnit`, `OAI.EilenbergGanea.sourceLinkContraction`, `OAI.EilenbergGanea.sourceVertexOrder`, `OAI.SimplicialChains.TwoDimensionalIndices.contraction`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory, in whole or in part: [`Dimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/Dimension.lean), [`LevelTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/LevelTransport.lean), [`SeedConnection`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedConnection.lean), [`SeedContraction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedContraction.lean), [`SeedHolonomy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedHolonomy.lean), [`Simplicial_Chains`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicTopology/Simplicial/Chains.lean).
--
--   **Imports.** It imports the published bundle `Def_EilenbergGanea`; the bundles `OAIEGC002` and `OAIEGC003` of this split; the published statements `OAI.EilenbergGanea.SeedChainCertificate.bottom_identity` and `OAI.EilenbergGanea.SeedChainCertificate.corrected_identities`.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.EilenbergGanea.source_cohomologicalDimension`, `OAI.EilenbergGanea.source_hasClassifyingSpace_three`, `OAI.EilenbergGanea.source_main` and `OAI.EilenbergGanea.source_no_classifyingSpace_two`.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_EilenbergGanea
import Definitions.Def_OAIEGC002
import Definitions.Def_OAIEGC003
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_bottom_identity
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_corrected_identities

section
-- module Solutions.OAIEG.Simplicial_Chains
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace SimplicialChains
variable {V : Type*}

variable [LinearOrder V] (L : SimpleGraph V)

variable {L}

namespace TwoDimensionalIndices
variable {E T : Type*} [Fintype V] [Fintype E] [Fintype T]
variable (D : TwoDimensionalIndices (L := L) E T)

variable (root : V) (h₀ : (V → ℤ) →ₗ[ℤ] (E → ℤ))
    (h₁ : (E → ℤ) →ₗ[ℤ] (T → ℤ))

variable (d₁ : (E → ℤ) →ₗ[ℤ] (V → ℤ)) (d₂ : (T → ℤ) →ₗ[ℤ] (E → ℤ))
    (hd₁ : ∀ e, d₁ (Pi.single e 1) = Pi.single (D.edge e).2 1 - Pi.single (D.edge e).1 1)
    (hd₂ : ∀ t, d₂ (Pi.single t 1) = Pi.single (D.face t).1 1 -
      Pi.single (D.face t).2.1 1 + Pi.single (D.face t).2.2 1)

variable (hbottom : ∀ v, d₁ (h₀ (Pi.single v 1)) = Pi.single v 1 - Pi.single root 1)
    (hleft : ∀ t, h₁ (d₂ (Pi.single t 1)) = Pi.single t 1)
    (hmiddle : ∀ e, d₂ (h₁ (Pi.single e 1)) + h₀ (d₁ (Pi.single e 1)) = Pi.single e 1)

include hd₁ hbottom in
 theorem vertex_identity (v : V) :
    boundary (D.fill root h₀ h₁ (Finsupp.single [v] 1)) +
      D.fill root h₀ h₁ (boundaryTerm [v]) = Finsupp.single [v] 1 := by
  simp only [fill_single,one_smul,fillTerm]
  rw [D.boundary_include_edge d₁ hd₁,hbottom]
  simp [fillTerm,vList]

omit [Fintype V] in
include hd₂ hleft in
 theorem triangle_identity (t : T) :
    boundary (D.fill root h₀ h₁ (Finsupp.single (D.tList t) 1)) +
      D.fill root h₀ h₁ (boundaryTerm (D.tList t)) = Finsupp.single (D.tList t) 1 := by
  calc
    _ = boundary (D.fill root h₀ h₁ (includeVec D.tList (Pi.single t 1))) +
        D.fill root h₀ h₁ (boundary (includeVec D.tList (Pi.single t 1))) := by simp
    _ = includeVec D.tList (h₁ (d₂ (Pi.single t 1))) := by
      rw [D.fill_include_triangle,map_zero,zero_add,
        D.boundary_include_triangle d₂ hd₂,D.fill_include_edge]
    _ = _ := by rw [hleft,includeVec_single]

/-- All finite matrix certificate equations are used to obtain a genuine
augmented contraction of every actual clique of the graph. -/
def contraction : Contraction L where
  homotopy := D.fill root h₀ h₁
  degree := D.fill_degree root h₀ h₁
  identity := by
    intro w hw
    have hl := D.length_le w hw
    rcases w with _ | ⟨a,w⟩
    · simp [fillTerm]
    rcases w with _ | ⟨b,w⟩
    · exact D.vertex_identity root h₀ h₁ d₁ hd₁ hbottom a
    rcases w with _ | ⟨c,w⟩
    · have he : D.eList (D.edgeIndex a b) = [a,b] := by
        simp [eList,D.edge_complete a b hw]
      rw [← he]
      exact D.edge_identity root h₀ h₁ d₁ d₂ hd₁ hd₂ hmiddle _
    have hw' : w = [] := by
      have hh : w.length = 0 := by simp only [List.length_cons] at hl; omega
      exact List.length_eq_zero_iff.mp hh
    subst w
    have he : D.tList (D.triangleIndex a b c) = [a,b,c] := by
      simp [tList,D.triangle_complete a b c hw]
    rw [← he]
    exact D.triangle_identity root h₀ h₁ d₂ hd₂ hleft _

end TwoDimensionalIndices
end SimplicialChains



end

end OAI
end

section
-- module Solutions.OAIEG.SeedHolonomy
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

/-! Exact quaternion monodromy of the fixed presentation seed. -/
open scoped Quaternion
namespace EilenbergGanea

theorem seedY_normSq : Quaternion.normSq seedYQuaternion = 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  have hle : Real.sqrt (5 : ℝ) ≤ 3 := by nlinarith
  have hc := Real.sq_sqrt (show (0 : ℝ) ≤ (3 - Real.sqrt 5)/8 by positivity)
  rw [Quaternion.normSq_def']
  change seedGoldenReal ^ 2 + (1 / 2 : ℝ) ^ 2 + Real.sqrt ((3 - Real.sqrt 5)/8) ^ 2 + 0 ^ 2 = 1
  dsimp [seedGoldenReal]
  nlinarith

def seedYUnit : SeedSU2 := ⟨seedYQuaternion,by
  rw [Unitary.mem_iff,Quaternion.star_mul_self,Quaternion.self_mul_star,seedY_normSq]
  simp⟩

def seedLetterUnit : Bool → SeedSU2
  | false => seedXUnit
  | true => seedYUnit

end EilenbergGanea



end

end OAI
end

section
-- module Solutions.OAIEG.SeedConnection
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible _root_.OAI.EilenbergGanea.SeedEncoding.properFaceDecidable _root_.OAI.EilenbergGanea.SeedEncoding.seedAdjDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
namespace SeedConnection

def circleLabel (e : CircleEdge) : SeedSU2 := FreeGroup.lift seedLetterUnit (circleWord e)

def radialLabel (s : Sector) : SeedSU2 :=
  FreeGroup.lift seedLetterUnit ((boundaryWords s.1).take s.2.val).prod

def edgeLocal : SeedEdge → SeedVertex → SeedSU2
  | .inl e, v => if v = .inl (circleStart e) then 1 else circleLabel e
  | .inr s, v => if v = .inr s.1 then 1 else radialLabel s

def faceLocal (s : Sector) (v : SeedVertex) : SeedSU2 :=
  if v = .inr s.1 then 1 else
  if v = .inl (sectorStart s) then radialLabel s else radialLabel (nextSector s)

def upLabel : SeedCell → SeedCell → SeedSU2
  | .inl v, .inr (.inl e) => (edgeLocal e v)⁻¹
  | .inl v, .inr (.inr s) => (faceLocal s v)⁻¹
  | .inr (.inl e), .inr (.inr s) => (faceLocal s (edgeAnchor e))⁻¹
  | _, _ => 1

@[simp] theorem upLabel_diag (a : SeedCell) : upLabel a a = 1 := by
  rcases a with a | (a | a) <;> rfl

def Related (a b : SeedCell) : Prop := a = b ∨ seedGraph.Adj a b

def connection (a b : SeedCell) : SeedSU2 :=
  if cellRank a ≤ cellRank b then upLabel a b else (upLabel b a)⁻¹

@[simp] theorem connection_diag (a : SeedCell) : connection a a = 1 := by
  simp [connection]

def rankFin (a : SeedCell) : Fin 3 := ⟨cellRank a,by
  rcases a with a | (a | a) <;> norm_num [cellRank]⟩

/-- The subdivided x-circle in the exact 103-cell order graph. -/
def roseLoop : List SeedCell :=
  [.inl (.inl none), .inr (.inl (.inl (false,0))),
    .inl (.inl (some (false,0))), .inr (.inl (.inl (false,1))),
    .inl (.inl (some (false,1))), .inr (.inl (.inl (false,2))), .inl (.inl none)]

theorem roseLoop_edges : roseLoop.IsChain seedGraph.Adj := by
  simp [roseLoop,List.isChain_cons_cons,seedGraph,properFace,edgeVertices,circleStart,circleEnd]

end SeedConnection



end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.LevelTransport
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible _root_.OAI.EilenbergGanea.SeedEncoding.properFaceDecidable _root_.OAI.EilenbergGanea.SeedEncoding.seedAdjDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea

namespace SourceTransport
open LevelTransport AffineTransport

def seedWalk : seedGraph.Walk (.inl (.inl none)) (.inl (.inl none)) :=
  SimpleGraph.Walk.ofSupport SeedConnection.roseLoop
    (by simp [SeedConnection.roseLoop]) SeedConnection.roseLoop_edges

end SourceTransport
end EilenbergGanea



end

end OAI
end

section
-- module Solutions.OAIEG.SeedContraction
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

attribute [local instance] OAI.EilenbergGanea.SeedChainCertificate.instDecidableEqFinOfNatNat_solutions
attribute [local instance] OAI.EilenbergGanea.SeedChainCertificate.instDecidableEqFinOfNatNat_solutions_1
attribute [local instance] OAI.EilenbergGanea.SeedChainCertificate.instDecidableEqFinOfNatNat_solutions_2
/-- An augmented integral chain contraction of the actual103-vertex source
cell-order complex, not an assumed homology property of the seed. -/
noncomputable def contraction : SimplicialChains.Contraction graph :=
  indices.contraction 0 h₀ h₁' d₁ d₂
    (by simpa only [indices,fin_single] using d₁_single)
    (by simpa only [indices,fin_single] using d₂_single)
    (by simpa only [fin_single] using bottom_identity)
    (by simpa only [fin_single] using corrected_identities.1)
    (by simpa only [fin_single] using corrected_identities.2)

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

section
-- module Solutions.OAIEG.Dimension
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea.SeedEncoding
@[simp] theorem cellEquiv_symm_apply (i : Fin 103) : cellEquiv.symm i = cellAt i := rfl
end EilenbergGanea.SeedEncoding
namespace EilenbergGanea
noncomputable abbrev sourceVertexOrder : LinearOrder SeedCell :=
  LinearOrder.lift' SeedEncoding.cellEquiv SeedEncoding.cellEquiv.injective
local instance instLinearOrderSeedCell : LinearOrder SeedCell := sourceVertexOrder
local instance instLTSeedCell : LT SeedCell := sourceVertexOrder.toLT

@[simp] theorem sourceVertexOrder_lt (a b : SeedCell) :
    a < b ↔ SeedEncoding.cellEquiv a < SeedEncoding.cellEquiv b := Iff.rfl

theorem source_valid_to_index (w : List SeedCell) (hw : SimplicialChains.Valid seedGraph w) :
    SimplicialChains.Valid SeedChainCertificate.graph (w.map SeedEncoding.cellEquiv) := by
  constructor
  · rw [List.pairwise_map]
    exact hw.1
  · rw [List.pairwise_map]
    simpa only [SeedChainCertificate.graph,SimpleGraph.comap_adj,
      ← SeedEncoding.cellEquiv_symm_apply,Equiv.symm_apply_apply] using hw.2

theorem index_valid_to_source (w : List (Fin 103))
    (hw : SimplicialChains.Valid SeedChainCertificate.graph w) :
    SimplicialChains.Valid seedGraph (w.map SeedEncoding.cellEquiv.symm) := by
  constructor
  · rw [List.pairwise_map]
    simpa only [sourceVertexOrder_lt,Equiv.apply_symm_apply] using hw.1
  · rw [List.pairwise_map]
    exact hw.2

/-- Relabeling uses the original seed graph and merely chooses an order on its
vertices for the signed integral chain convention. -/
noncomputable def sourceLinkContraction (K : SimplicialChains.Contraction SeedChainCertificate.graph) :
    SimplicialChains.Contraction seedGraph :=
  K.reindex SeedEncoding.cellEquiv.symm (index_valid_to_source) (source_valid_to_index)

end EilenbergGanea

namespace EilenbergGanea
local instance instLinearOrderSeedCell_1 : LinearOrder SeedCell := sourceVertexOrder

end EilenbergGanea



end

end OAI
end


