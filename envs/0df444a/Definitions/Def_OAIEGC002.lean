-- Prove2me | Definitions.Def_OAIEGC002
-- name    : OAIEGC002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T04:57:59.861434+00:00
-- url     : https://prove2.me/theorems/00e7352a-07fb-4162-9496-37cef580ee52
-- title:
--   Definitions bundle OAIEGC002 of the split of OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`, carved from OpenAI's openai/math development (OpenAI, *A finitely generated counterexample to the Eilenberg–Ganea conjecture*, OpenAI Math Release, September 23, 2026, result family 249, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 499 declarations of OpenAI's Lean: 7 definitions and 492 theorems. The definitions and types are `OAI.EilenbergGanea.SeedChainCertificate.edgeIndex`, `OAI.EilenbergGanea.SeedChainCertificate.edgeLookupCodes`, `OAI.EilenbergGanea.SeedChainCertificate.indices`, `OAI.EilenbergGanea.SeedChainCertificate.triangleIndex`, `OAI.EilenbergGanea.SeedChainCertificate.triangleLookupCodes`, `OAI.EilenbergGanea.TraceWords.CubeDescents.signedPreorder`, `OAI.EilenbergGanea.seedYQuaternion`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory, in whole or in part: [`Cubical_ArtinChains`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicTopology/Cubical/ArtinChains.lean), [`SeedChains`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedChains.lean), [`SeedHolonomy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedHolonomy.lean), [`Simplicial_Chains`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicTopology/Simplicial/Chains.lean).
--
--   **Imports.** It imports the published bundle `Def_EilenbergGanea`; the bundle `OAIEGC001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIEGC004`.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_EilenbergGanea
import Definitions.Def_OAIEGC001

section
-- module Solutions.OAIEG.Cubical_ArtinChains
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.TraceWords.CubeDescents
open CubicalChains CubicalChains.Reorientation
variable {V : Type*} (L : SimpleGraph V) [Fintype V] [Nonempty V] [LinearOrder V]
attribute [local instance] OAI.EilenbergGanea.TraceWords.CubeDescents.signedLexOrder
local instance signedPreorder : Preorder (Letter V) := signedLexOrder.toPartialOrder.toPreorder

end EilenbergGanea.TraceWords.CubeDescents


end

end OAI
end

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

theorem fill_include_vertex (c : V → ℤ) :
    D.fill root h₀ h₁ (includeVec vList c) = includeVec D.eList (h₀ c) := by
  have hh : (D.fill root h₀ h₁).comp (includeVec vList) = (includeVec D.eList).comp h₀ := by
    apply map_ext_single
    intro i
    simp [fillTerm,vList]
    congr 2
    funext v
    simp [Pi.single_apply]
  exact LinearMap.congr_fun hh c

omit [Fintype V] in
theorem fill_include_edge (c : E → ℤ) :
    D.fill root h₀ h₁ (includeVec D.eList c) = includeVec D.tList (h₁ c) := by
  have hh : (D.fill root h₀ h₁).comp (includeVec D.eList) = (includeVec D.tList).comp h₁ := by
    apply map_ext_single
    intro i
    simp [fillTerm,eList,D.edge_inverse]
  exact LinearMap.congr_fun hh c

omit [Fintype V] in
theorem fill_include_triangle (c : T → ℤ) :
    D.fill root h₀ h₁ (includeVec D.tList c) = 0 := by
  have hh : (D.fill root h₀ h₁).comp (includeVec D.tList) = 0 := by
    apply map_ext_single
    intro i
    simp [fillTerm,tList]
  exact LinearMap.congr_fun hh c

variable (d₁ : (E → ℤ) →ₗ[ℤ] (V → ℤ)) (d₂ : (T → ℤ) →ₗ[ℤ] (E → ℤ))
    (hd₁ : ∀ e, d₁ (Pi.single e 1) = Pi.single (D.edge e).2 1 - Pi.single (D.edge e).1 1)
    (hd₂ : ∀ t, d₂ (Pi.single t 1) = Pi.single (D.face t).1 1 -
      Pi.single (D.face t).2.1 1 + Pi.single (D.face t).2.2 1)

omit [Fintype T] in
include hd₁ in
theorem boundary_include_edge (c : E → ℤ) :
    boundary (includeVec D.eList c) = includeVec vList (d₁ c) := by
  have hh : boundary.comp (includeVec D.eList) = (includeVec vList).comp d₁ := by
    apply map_ext_single
    intro e
    simp [hd₁,eList,vList]
  exact LinearMap.congr_fun hh c

omit [Fintype V] in
include hd₂ in
theorem boundary_include_triangle (c : T → ℤ) :
    boundary (includeVec D.tList c) = includeVec D.eList (d₂ c) := by
  have hh : boundary.comp (includeVec D.tList) = (includeVec D.eList).comp d₂ := by
    apply map_ext_single
    intro t
    obtain ⟨h₁,h₂,h₃⟩ := D.face_edge t
    simp [hd₂,tList,eList,h₁,h₂,h₃,map_sub]
    abel
  exact LinearMap.congr_fun hh c

variable (hbottom : ∀ v, d₁ (h₀ (Pi.single v 1)) = Pi.single v 1 - Pi.single root 1)
    (hleft : ∀ t, h₁ (d₂ (Pi.single t 1)) = Pi.single t 1)
    (hmiddle : ∀ e, d₂ (h₁ (Pi.single e 1)) + h₀ (d₁ (Pi.single e 1)) = Pi.single e 1)

include hd₁ hd₂ hmiddle in
 theorem edge_identity (e : E) :
    boundary (D.fill root h₀ h₁ (Finsupp.single (D.eList e) 1)) +
      D.fill root h₀ h₁ (boundaryTerm (D.eList e)) = Finsupp.single (D.eList e) 1 := by
  calc
    _ = boundary (D.fill root h₀ h₁ (includeVec D.eList (Pi.single e 1))) +
        D.fill root h₀ h₁ (boundary (includeVec D.eList (Pi.single e 1))) := by simp
    _ = includeVec D.eList (d₂ (h₁ (Pi.single e 1))) +
        includeVec D.eList (h₀ (d₁ (Pi.single e 1))) := by
      rw [D.fill_include_edge,D.boundary_include_triangle d₂ hd₂,
        D.boundary_include_edge d₁ hd₁,D.fill_include_vertex]
    _ = _ := by rw [← map_add,hmiddle,includeVec_single]

end TwoDimensionalIndices
end SimplicialChains



end

end OAI
end

section
-- module Solutions.OAIEG.SeedChains
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
namespace SeedEncoding

theorem adjacency_certificate : ∀ a b : Fin 103,
    seedGraph.Adj (cellAt a) (cellAt b) ↔ indexedAdj a b := by decide +kernel

end SeedEncoding
end EilenbergGanea
namespace EilenbergGanea.SeedChainCertificate
def edgeLookupCodes : List ℕ := [edgeLookupCodes_0,edgeLookupCodes_1,edgeLookupCodes_2,edgeLookupCodes_3,edgeLookupCodes_4,edgeLookupCodes_5,edgeLookupCodes_6].flatten
def triangleLookupCodes : List ℕ := [triangleLookupCodes_0,triangleLookupCodes_1,triangleLookupCodes_2,triangleLookupCodes_3,triangleLookupCodes_4,triangleLookupCodes_5,triangleLookupCodes_6,triangleLookupCodes_7,triangleLookupCodes_8,triangleLookupCodes_9,triangleLookupCodes_10,triangleLookupCodes_11,triangleLookupCodes_12,triangleLookupCodes_13,triangleLookupCodes_14,triangleLookupCodes_15,triangleLookupCodes_16,triangleLookupCodes_17,triangleLookupCodes_18,triangleLookupCodes_19,triangleLookupCodes_20,triangleLookupCodes_21,triangleLookupCodes_22,triangleLookupCodes_23].flatten
def edgeIndex (a b : Fin 103) : Fin 372 :=
  ⟨((edgeLookupCodes.getD a.val 0 >>> (10*b.val)) % 1024) % 372,
    Nat.mod_lt _ (by decide)⟩
def triangleIndex (e : Fin 372) (c : Fin 103) : Fin 270 :=
  ⟨((triangleLookupCodes.getD e.val 0 >>> (9*c.val)) % 512) % 270,
    Nat.mod_lt _ (by decide)⟩
theorem edge_complete_0 : ∀ b : Fin 103,
    0 < b → SeedEncoding.indexedAdj 0 b →
      edge (edgeIndex 0 b) = (0,b) := by decide +kernel
theorem edge_complete_1 : ∀ b : Fin 103,
    1 < b → SeedEncoding.indexedAdj 1 b →
      edge (edgeIndex 1 b) = (1,b) := by decide +kernel
theorem edge_complete_2 : ∀ b : Fin 103,
    2 < b → SeedEncoding.indexedAdj 2 b →
      edge (edgeIndex 2 b) = (2,b) := by decide +kernel
theorem edge_complete_3 : ∀ b : Fin 103,
    3 < b → SeedEncoding.indexedAdj 3 b →
      edge (edgeIndex 3 b) = (3,b) := by decide +kernel
theorem edge_complete_4 : ∀ b : Fin 103,
    4 < b → SeedEncoding.indexedAdj 4 b →
      edge (edgeIndex 4 b) = (4,b) := by decide +kernel
theorem edge_complete_5 : ∀ b : Fin 103,
    5 < b → SeedEncoding.indexedAdj 5 b →
      edge (edgeIndex 5 b) = (5,b) := by decide +kernel
theorem edge_complete_6 : ∀ b : Fin 103,
    6 < b → SeedEncoding.indexedAdj 6 b →
      edge (edgeIndex 6 b) = (6,b) := by decide +kernel
theorem edge_complete_7 : ∀ b : Fin 103,
    7 < b → SeedEncoding.indexedAdj 7 b →
      edge (edgeIndex 7 b) = (7,b) := by decide +kernel
theorem edge_complete_8 : ∀ b : Fin 103,
    8 < b → SeedEncoding.indexedAdj 8 b →
      edge (edgeIndex 8 b) = (8,b) := by decide +kernel
theorem edge_complete_9 : ∀ b : Fin 103,
    9 < b → SeedEncoding.indexedAdj 9 b →
      edge (edgeIndex 9 b) = (9,b) := by decide +kernel
theorem edge_complete_10 : ∀ b : Fin 103,
    10 < b → SeedEncoding.indexedAdj 10 b →
      edge (edgeIndex 10 b) = (10,b) := by decide +kernel
theorem edge_complete_11 : ∀ b : Fin 103,
    11 < b → SeedEncoding.indexedAdj 11 b →
      edge (edgeIndex 11 b) = (11,b) := by decide +kernel
theorem edge_complete_12 : ∀ b : Fin 103,
    12 < b → SeedEncoding.indexedAdj 12 b →
      edge (edgeIndex 12 b) = (12,b) := by decide +kernel
theorem edge_complete_13 : ∀ b : Fin 103,
    13 < b → SeedEncoding.indexedAdj 13 b →
      edge (edgeIndex 13 b) = (13,b) := by decide +kernel
theorem edge_complete_14 : ∀ b : Fin 103,
    14 < b → SeedEncoding.indexedAdj 14 b →
      edge (edgeIndex 14 b) = (14,b) := by decide +kernel
theorem edge_complete_15 : ∀ b : Fin 103,
    15 < b → SeedEncoding.indexedAdj 15 b →
      edge (edgeIndex 15 b) = (15,b) := by decide +kernel
theorem edge_complete_16 : ∀ b : Fin 103,
    16 < b → SeedEncoding.indexedAdj 16 b →
      edge (edgeIndex 16 b) = (16,b) := by decide +kernel
theorem edge_complete_17 : ∀ b : Fin 103,
    17 < b → SeedEncoding.indexedAdj 17 b →
      edge (edgeIndex 17 b) = (17,b) := by decide +kernel
theorem edge_complete_18 : ∀ b : Fin 103,
    18 < b → SeedEncoding.indexedAdj 18 b →
      edge (edgeIndex 18 b) = (18,b) := by decide +kernel
theorem edge_complete_19 : ∀ b : Fin 103,
    19 < b → SeedEncoding.indexedAdj 19 b →
      edge (edgeIndex 19 b) = (19,b) := by decide +kernel
theorem edge_complete_20 : ∀ b : Fin 103,
    20 < b → SeedEncoding.indexedAdj 20 b →
      edge (edgeIndex 20 b) = (20,b) := by decide +kernel
theorem edge_complete_21 : ∀ b : Fin 103,
    21 < b → SeedEncoding.indexedAdj 21 b →
      edge (edgeIndex 21 b) = (21,b) := by decide +kernel
theorem edge_complete_22 : ∀ b : Fin 103,
    22 < b → SeedEncoding.indexedAdj 22 b →
      edge (edgeIndex 22 b) = (22,b) := by decide +kernel
theorem edge_complete_23 : ∀ b : Fin 103,
    23 < b → SeedEncoding.indexedAdj 23 b →
      edge (edgeIndex 23 b) = (23,b) := by decide +kernel
theorem edge_complete_24 : ∀ b : Fin 103,
    24 < b → SeedEncoding.indexedAdj 24 b →
      edge (edgeIndex 24 b) = (24,b) := by decide +kernel
theorem edge_complete_25 : ∀ b : Fin 103,
    25 < b → SeedEncoding.indexedAdj 25 b →
      edge (edgeIndex 25 b) = (25,b) := by decide +kernel
theorem edge_complete_26 : ∀ b : Fin 103,
    26 < b → SeedEncoding.indexedAdj 26 b →
      edge (edgeIndex 26 b) = (26,b) := by decide +kernel
theorem edge_complete_27 : ∀ b : Fin 103,
    27 < b → SeedEncoding.indexedAdj 27 b →
      edge (edgeIndex 27 b) = (27,b) := by decide +kernel
theorem edge_complete_28 : ∀ b : Fin 103,
    28 < b → SeedEncoding.indexedAdj 28 b →
      edge (edgeIndex 28 b) = (28,b) := by decide +kernel
theorem edge_complete_29 : ∀ b : Fin 103,
    29 < b → SeedEncoding.indexedAdj 29 b →
      edge (edgeIndex 29 b) = (29,b) := by decide +kernel
theorem edge_complete_30 : ∀ b : Fin 103,
    30 < b → SeedEncoding.indexedAdj 30 b →
      edge (edgeIndex 30 b) = (30,b) := by decide +kernel
theorem edge_complete_31 : ∀ b : Fin 103,
    31 < b → SeedEncoding.indexedAdj 31 b →
      edge (edgeIndex 31 b) = (31,b) := by decide +kernel
theorem edge_complete_32 : ∀ b : Fin 103,
    32 < b → SeedEncoding.indexedAdj 32 b →
      edge (edgeIndex 32 b) = (32,b) := by decide +kernel
theorem edge_complete_33 : ∀ b : Fin 103,
    33 < b → SeedEncoding.indexedAdj 33 b →
      edge (edgeIndex 33 b) = (33,b) := by decide +kernel
theorem edge_complete_34 : ∀ b : Fin 103,
    34 < b → SeedEncoding.indexedAdj 34 b →
      edge (edgeIndex 34 b) = (34,b) := by decide +kernel
theorem edge_complete_35 : ∀ b : Fin 103,
    35 < b → SeedEncoding.indexedAdj 35 b →
      edge (edgeIndex 35 b) = (35,b) := by decide +kernel
theorem edge_complete_36 : ∀ b : Fin 103,
    36 < b → SeedEncoding.indexedAdj 36 b →
      edge (edgeIndex 36 b) = (36,b) := by decide +kernel
theorem edge_complete_37 : ∀ b : Fin 103,
    37 < b → SeedEncoding.indexedAdj 37 b →
      edge (edgeIndex 37 b) = (37,b) := by decide +kernel
theorem edge_complete_38 : ∀ b : Fin 103,
    38 < b → SeedEncoding.indexedAdj 38 b →
      edge (edgeIndex 38 b) = (38,b) := by decide +kernel
theorem edge_complete_39 : ∀ b : Fin 103,
    39 < b → SeedEncoding.indexedAdj 39 b →
      edge (edgeIndex 39 b) = (39,b) := by decide +kernel
theorem edge_complete_40 : ∀ b : Fin 103,
    40 < b → SeedEncoding.indexedAdj 40 b →
      edge (edgeIndex 40 b) = (40,b) := by decide +kernel
theorem edge_complete_41 : ∀ b : Fin 103,
    41 < b → SeedEncoding.indexedAdj 41 b →
      edge (edgeIndex 41 b) = (41,b) := by decide +kernel
theorem edge_complete_42 : ∀ b : Fin 103,
    42 < b → SeedEncoding.indexedAdj 42 b →
      edge (edgeIndex 42 b) = (42,b) := by decide +kernel
theorem edge_complete_43 : ∀ b : Fin 103,
    43 < b → SeedEncoding.indexedAdj 43 b →
      edge (edgeIndex 43 b) = (43,b) := by decide +kernel
theorem edge_complete_44 : ∀ b : Fin 103,
    44 < b → SeedEncoding.indexedAdj 44 b →
      edge (edgeIndex 44 b) = (44,b) := by decide +kernel
theorem edge_complete_45 : ∀ b : Fin 103,
    45 < b → SeedEncoding.indexedAdj 45 b →
      edge (edgeIndex 45 b) = (45,b) := by decide +kernel
theorem edge_complete_46 : ∀ b : Fin 103,
    46 < b → SeedEncoding.indexedAdj 46 b →
      edge (edgeIndex 46 b) = (46,b) := by decide +kernel
theorem edge_complete_47 : ∀ b : Fin 103,
    47 < b → SeedEncoding.indexedAdj 47 b →
      edge (edgeIndex 47 b) = (47,b) := by decide +kernel
theorem edge_complete_48 : ∀ b : Fin 103,
    48 < b → SeedEncoding.indexedAdj 48 b →
      edge (edgeIndex 48 b) = (48,b) := by decide +kernel
theorem edge_complete_49 : ∀ b : Fin 103,
    49 < b → SeedEncoding.indexedAdj 49 b →
      edge (edgeIndex 49 b) = (49,b) := by decide +kernel
theorem edge_complete_50 : ∀ b : Fin 103,
    50 < b → SeedEncoding.indexedAdj 50 b →
      edge (edgeIndex 50 b) = (50,b) := by decide +kernel
theorem edge_complete_51 : ∀ b : Fin 103,
    51 < b → SeedEncoding.indexedAdj 51 b →
      edge (edgeIndex 51 b) = (51,b) := by decide +kernel
theorem edge_complete_52 : ∀ b : Fin 103,
    52 < b → SeedEncoding.indexedAdj 52 b →
      edge (edgeIndex 52 b) = (52,b) := by decide +kernel
theorem edge_complete_53 : ∀ b : Fin 103,
    53 < b → SeedEncoding.indexedAdj 53 b →
      edge (edgeIndex 53 b) = (53,b) := by decide +kernel
theorem edge_complete_54 : ∀ b : Fin 103,
    54 < b → SeedEncoding.indexedAdj 54 b →
      edge (edgeIndex 54 b) = (54,b) := by decide +kernel
theorem edge_complete_55 : ∀ b : Fin 103,
    55 < b → SeedEncoding.indexedAdj 55 b →
      edge (edgeIndex 55 b) = (55,b) := by decide +kernel
theorem edge_complete_56 : ∀ b : Fin 103,
    56 < b → SeedEncoding.indexedAdj 56 b →
      edge (edgeIndex 56 b) = (56,b) := by decide +kernel
theorem edge_complete_57 : ∀ b : Fin 103,
    57 < b → SeedEncoding.indexedAdj 57 b →
      edge (edgeIndex 57 b) = (57,b) := by decide +kernel
theorem edge_complete_58 : ∀ b : Fin 103,
    58 < b → SeedEncoding.indexedAdj 58 b →
      edge (edgeIndex 58 b) = (58,b) := by decide +kernel
theorem edge_complete_59 : ∀ b : Fin 103,
    59 < b → SeedEncoding.indexedAdj 59 b →
      edge (edgeIndex 59 b) = (59,b) := by decide +kernel
theorem edge_complete_60 : ∀ b : Fin 103,
    60 < b → SeedEncoding.indexedAdj 60 b →
      edge (edgeIndex 60 b) = (60,b) := by decide +kernel
theorem edge_complete_61 : ∀ b : Fin 103,
    61 < b → SeedEncoding.indexedAdj 61 b →
      edge (edgeIndex 61 b) = (61,b) := by decide +kernel
theorem edge_complete_62 : ∀ b : Fin 103,
    62 < b → SeedEncoding.indexedAdj 62 b →
      edge (edgeIndex 62 b) = (62,b) := by decide +kernel
theorem edge_complete_63 : ∀ b : Fin 103,
    63 < b → SeedEncoding.indexedAdj 63 b →
      edge (edgeIndex 63 b) = (63,b) := by decide +kernel
theorem edge_complete_64 : ∀ b : Fin 103,
    64 < b → SeedEncoding.indexedAdj 64 b →
      edge (edgeIndex 64 b) = (64,b) := by decide +kernel
theorem edge_complete_65 : ∀ b : Fin 103,
    65 < b → SeedEncoding.indexedAdj 65 b →
      edge (edgeIndex 65 b) = (65,b) := by decide +kernel
theorem edge_complete_66 : ∀ b : Fin 103,
    66 < b → SeedEncoding.indexedAdj 66 b →
      edge (edgeIndex 66 b) = (66,b) := by decide +kernel
theorem edge_complete_67 : ∀ b : Fin 103,
    67 < b → SeedEncoding.indexedAdj 67 b →
      edge (edgeIndex 67 b) = (67,b) := by decide +kernel
theorem edge_complete_68 : ∀ b : Fin 103,
    68 < b → SeedEncoding.indexedAdj 68 b →
      edge (edgeIndex 68 b) = (68,b) := by decide +kernel
theorem edge_complete_69 : ∀ b : Fin 103,
    69 < b → SeedEncoding.indexedAdj 69 b →
      edge (edgeIndex 69 b) = (69,b) := by decide +kernel
theorem edge_complete_70 : ∀ b : Fin 103,
    70 < b → SeedEncoding.indexedAdj 70 b →
      edge (edgeIndex 70 b) = (70,b) := by decide +kernel
theorem edge_complete_71 : ∀ b : Fin 103,
    71 < b → SeedEncoding.indexedAdj 71 b →
      edge (edgeIndex 71 b) = (71,b) := by decide +kernel
theorem edge_complete_72 : ∀ b : Fin 103,
    72 < b → SeedEncoding.indexedAdj 72 b →
      edge (edgeIndex 72 b) = (72,b) := by decide +kernel
theorem edge_complete_73 : ∀ b : Fin 103,
    73 < b → SeedEncoding.indexedAdj 73 b →
      edge (edgeIndex 73 b) = (73,b) := by decide +kernel
theorem edge_complete_74 : ∀ b : Fin 103,
    74 < b → SeedEncoding.indexedAdj 74 b →
      edge (edgeIndex 74 b) = (74,b) := by decide +kernel
theorem edge_complete_75 : ∀ b : Fin 103,
    75 < b → SeedEncoding.indexedAdj 75 b →
      edge (edgeIndex 75 b) = (75,b) := by decide +kernel
theorem edge_complete_76 : ∀ b : Fin 103,
    76 < b → SeedEncoding.indexedAdj 76 b →
      edge (edgeIndex 76 b) = (76,b) := by decide +kernel
theorem edge_complete_77 : ∀ b : Fin 103,
    77 < b → SeedEncoding.indexedAdj 77 b →
      edge (edgeIndex 77 b) = (77,b) := by decide +kernel
theorem edge_complete_78 : ∀ b : Fin 103,
    78 < b → SeedEncoding.indexedAdj 78 b →
      edge (edgeIndex 78 b) = (78,b) := by decide +kernel
theorem edge_complete_79 : ∀ b : Fin 103,
    79 < b → SeedEncoding.indexedAdj 79 b →
      edge (edgeIndex 79 b) = (79,b) := by decide +kernel
theorem edge_complete_80 : ∀ b : Fin 103,
    80 < b → SeedEncoding.indexedAdj 80 b →
      edge (edgeIndex 80 b) = (80,b) := by decide +kernel
theorem edge_complete_81 : ∀ b : Fin 103,
    81 < b → SeedEncoding.indexedAdj 81 b →
      edge (edgeIndex 81 b) = (81,b) := by decide +kernel
theorem edge_complete_82 : ∀ b : Fin 103,
    82 < b → SeedEncoding.indexedAdj 82 b →
      edge (edgeIndex 82 b) = (82,b) := by decide +kernel
theorem edge_complete_83 : ∀ b : Fin 103,
    83 < b → SeedEncoding.indexedAdj 83 b →
      edge (edgeIndex 83 b) = (83,b) := by decide +kernel
theorem edge_complete_84 : ∀ b : Fin 103,
    84 < b → SeedEncoding.indexedAdj 84 b →
      edge (edgeIndex 84 b) = (84,b) := by decide +kernel
theorem edge_complete_85 : ∀ b : Fin 103,
    85 < b → SeedEncoding.indexedAdj 85 b →
      edge (edgeIndex 85 b) = (85,b) := by decide +kernel
theorem edge_complete_86 : ∀ b : Fin 103,
    86 < b → SeedEncoding.indexedAdj 86 b →
      edge (edgeIndex 86 b) = (86,b) := by decide +kernel
theorem edge_complete_87 : ∀ b : Fin 103,
    87 < b → SeedEncoding.indexedAdj 87 b →
      edge (edgeIndex 87 b) = (87,b) := by decide +kernel
theorem edge_complete_88 : ∀ b : Fin 103,
    88 < b → SeedEncoding.indexedAdj 88 b →
      edge (edgeIndex 88 b) = (88,b) := by decide +kernel
theorem edge_complete_89 : ∀ b : Fin 103,
    89 < b → SeedEncoding.indexedAdj 89 b →
      edge (edgeIndex 89 b) = (89,b) := by decide +kernel
theorem edge_complete_90 : ∀ b : Fin 103,
    90 < b → SeedEncoding.indexedAdj 90 b →
      edge (edgeIndex 90 b) = (90,b) := by decide +kernel
theorem edge_complete_91 : ∀ b : Fin 103,
    91 < b → SeedEncoding.indexedAdj 91 b →
      edge (edgeIndex 91 b) = (91,b) := by decide +kernel
theorem edge_complete_92 : ∀ b : Fin 103,
    92 < b → SeedEncoding.indexedAdj 92 b →
      edge (edgeIndex 92 b) = (92,b) := by decide +kernel
theorem edge_complete_93 : ∀ b : Fin 103,
    93 < b → SeedEncoding.indexedAdj 93 b →
      edge (edgeIndex 93 b) = (93,b) := by decide +kernel
theorem edge_complete_94 : ∀ b : Fin 103,
    94 < b → SeedEncoding.indexedAdj 94 b →
      edge (edgeIndex 94 b) = (94,b) := by decide +kernel
theorem edge_complete_95 : ∀ b : Fin 103,
    95 < b → SeedEncoding.indexedAdj 95 b →
      edge (edgeIndex 95 b) = (95,b) := by decide +kernel
theorem edge_complete_96 : ∀ b : Fin 103,
    96 < b → SeedEncoding.indexedAdj 96 b →
      edge (edgeIndex 96 b) = (96,b) := by decide +kernel
theorem edge_complete_97 : ∀ b : Fin 103,
    97 < b → SeedEncoding.indexedAdj 97 b →
      edge (edgeIndex 97 b) = (97,b) := by decide +kernel
theorem edge_complete_98 : ∀ b : Fin 103,
    98 < b → SeedEncoding.indexedAdj 98 b →
      edge (edgeIndex 98 b) = (98,b) := by decide +kernel
theorem edge_complete_99 : ∀ b : Fin 103,
    99 < b → SeedEncoding.indexedAdj 99 b →
      edge (edgeIndex 99 b) = (99,b) := by decide +kernel
theorem edge_complete_100 : ∀ b : Fin 103,
    100 < b → SeedEncoding.indexedAdj 100 b →
      edge (edgeIndex 100 b) = (100,b) := by decide +kernel
theorem edge_complete_101 : ∀ b : Fin 103,
    101 < b → SeedEncoding.indexedAdj 101 b →
      edge (edgeIndex 101 b) = (101,b) := by decide +kernel
theorem edge_complete_102 : ∀ b : Fin 103,
    102 < b → SeedEncoding.indexedAdj 102 b →
      edge (edgeIndex 102 b) = (102,b) := by decide +kernel
theorem triangle_complete_0 : ∀ c : Fin 103,
    (edge 0).2 < c → SeedEncoding.indexedAdj (edge 0).1 c →
    SeedEncoding.indexedAdj (edge 0).2 c →
      triangle (triangleIndex 0 c) = ((edge 0).1,(edge 0).2,c) := by decide +kernel
theorem triangle_complete_1 : ∀ c : Fin 103,
    (edge 1).2 < c → SeedEncoding.indexedAdj (edge 1).1 c →
    SeedEncoding.indexedAdj (edge 1).2 c →
      triangle (triangleIndex 1 c) = ((edge 1).1,(edge 1).2,c) := by decide +kernel
theorem triangle_complete_2 : ∀ c : Fin 103,
    (edge 2).2 < c → SeedEncoding.indexedAdj (edge 2).1 c →
    SeedEncoding.indexedAdj (edge 2).2 c →
      triangle (triangleIndex 2 c) = ((edge 2).1,(edge 2).2,c) := by decide +kernel
theorem triangle_complete_3 : ∀ c : Fin 103,
    (edge 3).2 < c → SeedEncoding.indexedAdj (edge 3).1 c →
    SeedEncoding.indexedAdj (edge 3).2 c →
      triangle (triangleIndex 3 c) = ((edge 3).1,(edge 3).2,c) := by decide +kernel
theorem triangle_complete_4 : ∀ c : Fin 103,
    (edge 4).2 < c → SeedEncoding.indexedAdj (edge 4).1 c →
    SeedEncoding.indexedAdj (edge 4).2 c →
      triangle (triangleIndex 4 c) = ((edge 4).1,(edge 4).2,c) := by decide +kernel
theorem triangle_complete_5 : ∀ c : Fin 103,
    (edge 5).2 < c → SeedEncoding.indexedAdj (edge 5).1 c →
    SeedEncoding.indexedAdj (edge 5).2 c →
      triangle (triangleIndex 5 c) = ((edge 5).1,(edge 5).2,c) := by decide +kernel
theorem triangle_complete_6 : ∀ c : Fin 103,
    (edge 6).2 < c → SeedEncoding.indexedAdj (edge 6).1 c →
    SeedEncoding.indexedAdj (edge 6).2 c →
      triangle (triangleIndex 6 c) = ((edge 6).1,(edge 6).2,c) := by decide +kernel
theorem triangle_complete_7 : ∀ c : Fin 103,
    (edge 7).2 < c → SeedEncoding.indexedAdj (edge 7).1 c →
    SeedEncoding.indexedAdj (edge 7).2 c →
      triangle (triangleIndex 7 c) = ((edge 7).1,(edge 7).2,c) := by decide +kernel
theorem triangle_complete_8 : ∀ c : Fin 103,
    (edge 8).2 < c → SeedEncoding.indexedAdj (edge 8).1 c →
    SeedEncoding.indexedAdj (edge 8).2 c →
      triangle (triangleIndex 8 c) = ((edge 8).1,(edge 8).2,c) := by decide +kernel
theorem triangle_complete_9 : ∀ c : Fin 103,
    (edge 9).2 < c → SeedEncoding.indexedAdj (edge 9).1 c →
    SeedEncoding.indexedAdj (edge 9).2 c →
      triangle (triangleIndex 9 c) = ((edge 9).1,(edge 9).2,c) := by decide +kernel
theorem triangle_complete_10 : ∀ c : Fin 103,
    (edge 10).2 < c → SeedEncoding.indexedAdj (edge 10).1 c →
    SeedEncoding.indexedAdj (edge 10).2 c →
      triangle (triangleIndex 10 c) = ((edge 10).1,(edge 10).2,c) := by decide +kernel
theorem triangle_complete_11 : ∀ c : Fin 103,
    (edge 11).2 < c → SeedEncoding.indexedAdj (edge 11).1 c →
    SeedEncoding.indexedAdj (edge 11).2 c →
      triangle (triangleIndex 11 c) = ((edge 11).1,(edge 11).2,c) := by decide +kernel
theorem triangle_complete_12 : ∀ c : Fin 103,
    (edge 12).2 < c → SeedEncoding.indexedAdj (edge 12).1 c →
    SeedEncoding.indexedAdj (edge 12).2 c →
      triangle (triangleIndex 12 c) = ((edge 12).1,(edge 12).2,c) := by decide +kernel
theorem triangle_complete_13 : ∀ c : Fin 103,
    (edge 13).2 < c → SeedEncoding.indexedAdj (edge 13).1 c →
    SeedEncoding.indexedAdj (edge 13).2 c →
      triangle (triangleIndex 13 c) = ((edge 13).1,(edge 13).2,c) := by decide +kernel
theorem triangle_complete_14 : ∀ c : Fin 103,
    (edge 14).2 < c → SeedEncoding.indexedAdj (edge 14).1 c →
    SeedEncoding.indexedAdj (edge 14).2 c →
      triangle (triangleIndex 14 c) = ((edge 14).1,(edge 14).2,c) := by decide +kernel
theorem triangle_complete_15 : ∀ c : Fin 103,
    (edge 15).2 < c → SeedEncoding.indexedAdj (edge 15).1 c →
    SeedEncoding.indexedAdj (edge 15).2 c →
      triangle (triangleIndex 15 c) = ((edge 15).1,(edge 15).2,c) := by decide +kernel
theorem triangle_complete_16 : ∀ c : Fin 103,
    (edge 16).2 < c → SeedEncoding.indexedAdj (edge 16).1 c →
    SeedEncoding.indexedAdj (edge 16).2 c →
      triangle (triangleIndex 16 c) = ((edge 16).1,(edge 16).2,c) := by decide +kernel
theorem triangle_complete_17 : ∀ c : Fin 103,
    (edge 17).2 < c → SeedEncoding.indexedAdj (edge 17).1 c →
    SeedEncoding.indexedAdj (edge 17).2 c →
      triangle (triangleIndex 17 c) = ((edge 17).1,(edge 17).2,c) := by decide +kernel
theorem triangle_complete_18 : ∀ c : Fin 103,
    (edge 18).2 < c → SeedEncoding.indexedAdj (edge 18).1 c →
    SeedEncoding.indexedAdj (edge 18).2 c →
      triangle (triangleIndex 18 c) = ((edge 18).1,(edge 18).2,c) := by decide +kernel
theorem triangle_complete_19 : ∀ c : Fin 103,
    (edge 19).2 < c → SeedEncoding.indexedAdj (edge 19).1 c →
    SeedEncoding.indexedAdj (edge 19).2 c →
      triangle (triangleIndex 19 c) = ((edge 19).1,(edge 19).2,c) := by decide +kernel
theorem triangle_complete_20 : ∀ c : Fin 103,
    (edge 20).2 < c → SeedEncoding.indexedAdj (edge 20).1 c →
    SeedEncoding.indexedAdj (edge 20).2 c →
      triangle (triangleIndex 20 c) = ((edge 20).1,(edge 20).2,c) := by decide +kernel
theorem triangle_complete_21 : ∀ c : Fin 103,
    (edge 21).2 < c → SeedEncoding.indexedAdj (edge 21).1 c →
    SeedEncoding.indexedAdj (edge 21).2 c →
      triangle (triangleIndex 21 c) = ((edge 21).1,(edge 21).2,c) := by decide +kernel
theorem triangle_complete_22 : ∀ c : Fin 103,
    (edge 22).2 < c → SeedEncoding.indexedAdj (edge 22).1 c →
    SeedEncoding.indexedAdj (edge 22).2 c →
      triangle (triangleIndex 22 c) = ((edge 22).1,(edge 22).2,c) := by decide +kernel
theorem triangle_complete_23 : ∀ c : Fin 103,
    (edge 23).2 < c → SeedEncoding.indexedAdj (edge 23).1 c →
    SeedEncoding.indexedAdj (edge 23).2 c →
      triangle (triangleIndex 23 c) = ((edge 23).1,(edge 23).2,c) := by decide +kernel
theorem triangle_complete_24 : ∀ c : Fin 103,
    (edge 24).2 < c → SeedEncoding.indexedAdj (edge 24).1 c →
    SeedEncoding.indexedAdj (edge 24).2 c →
      triangle (triangleIndex 24 c) = ((edge 24).1,(edge 24).2,c) := by decide +kernel
theorem triangle_complete_25 : ∀ c : Fin 103,
    (edge 25).2 < c → SeedEncoding.indexedAdj (edge 25).1 c →
    SeedEncoding.indexedAdj (edge 25).2 c →
      triangle (triangleIndex 25 c) = ((edge 25).1,(edge 25).2,c) := by decide +kernel
theorem triangle_complete_26 : ∀ c : Fin 103,
    (edge 26).2 < c → SeedEncoding.indexedAdj (edge 26).1 c →
    SeedEncoding.indexedAdj (edge 26).2 c →
      triangle (triangleIndex 26 c) = ((edge 26).1,(edge 26).2,c) := by decide +kernel
theorem triangle_complete_27 : ∀ c : Fin 103,
    (edge 27).2 < c → SeedEncoding.indexedAdj (edge 27).1 c →
    SeedEncoding.indexedAdj (edge 27).2 c →
      triangle (triangleIndex 27 c) = ((edge 27).1,(edge 27).2,c) := by decide +kernel
theorem triangle_complete_28 : ∀ c : Fin 103,
    (edge 28).2 < c → SeedEncoding.indexedAdj (edge 28).1 c →
    SeedEncoding.indexedAdj (edge 28).2 c →
      triangle (triangleIndex 28 c) = ((edge 28).1,(edge 28).2,c) := by decide +kernel
theorem triangle_complete_29 : ∀ c : Fin 103,
    (edge 29).2 < c → SeedEncoding.indexedAdj (edge 29).1 c →
    SeedEncoding.indexedAdj (edge 29).2 c →
      triangle (triangleIndex 29 c) = ((edge 29).1,(edge 29).2,c) := by decide +kernel
theorem triangle_complete_30 : ∀ c : Fin 103,
    (edge 30).2 < c → SeedEncoding.indexedAdj (edge 30).1 c →
    SeedEncoding.indexedAdj (edge 30).2 c →
      triangle (triangleIndex 30 c) = ((edge 30).1,(edge 30).2,c) := by decide +kernel
theorem triangle_complete_31 : ∀ c : Fin 103,
    (edge 31).2 < c → SeedEncoding.indexedAdj (edge 31).1 c →
    SeedEncoding.indexedAdj (edge 31).2 c →
      triangle (triangleIndex 31 c) = ((edge 31).1,(edge 31).2,c) := by decide +kernel
theorem triangle_complete_32 : ∀ c : Fin 103,
    (edge 32).2 < c → SeedEncoding.indexedAdj (edge 32).1 c →
    SeedEncoding.indexedAdj (edge 32).2 c →
      triangle (triangleIndex 32 c) = ((edge 32).1,(edge 32).2,c) := by decide +kernel
theorem triangle_complete_33 : ∀ c : Fin 103,
    (edge 33).2 < c → SeedEncoding.indexedAdj (edge 33).1 c →
    SeedEncoding.indexedAdj (edge 33).2 c →
      triangle (triangleIndex 33 c) = ((edge 33).1,(edge 33).2,c) := by decide +kernel
theorem triangle_complete_34 : ∀ c : Fin 103,
    (edge 34).2 < c → SeedEncoding.indexedAdj (edge 34).1 c →
    SeedEncoding.indexedAdj (edge 34).2 c →
      triangle (triangleIndex 34 c) = ((edge 34).1,(edge 34).2,c) := by decide +kernel
theorem triangle_complete_35 : ∀ c : Fin 103,
    (edge 35).2 < c → SeedEncoding.indexedAdj (edge 35).1 c →
    SeedEncoding.indexedAdj (edge 35).2 c →
      triangle (triangleIndex 35 c) = ((edge 35).1,(edge 35).2,c) := by decide +kernel
theorem triangle_complete_36 : ∀ c : Fin 103,
    (edge 36).2 < c → SeedEncoding.indexedAdj (edge 36).1 c →
    SeedEncoding.indexedAdj (edge 36).2 c →
      triangle (triangleIndex 36 c) = ((edge 36).1,(edge 36).2,c) := by decide +kernel
theorem triangle_complete_37 : ∀ c : Fin 103,
    (edge 37).2 < c → SeedEncoding.indexedAdj (edge 37).1 c →
    SeedEncoding.indexedAdj (edge 37).2 c →
      triangle (triangleIndex 37 c) = ((edge 37).1,(edge 37).2,c) := by decide +kernel
theorem triangle_complete_38 : ∀ c : Fin 103,
    (edge 38).2 < c → SeedEncoding.indexedAdj (edge 38).1 c →
    SeedEncoding.indexedAdj (edge 38).2 c →
      triangle (triangleIndex 38 c) = ((edge 38).1,(edge 38).2,c) := by decide +kernel
theorem triangle_complete_39 : ∀ c : Fin 103,
    (edge 39).2 < c → SeedEncoding.indexedAdj (edge 39).1 c →
    SeedEncoding.indexedAdj (edge 39).2 c →
      triangle (triangleIndex 39 c) = ((edge 39).1,(edge 39).2,c) := by decide +kernel
theorem triangle_complete_40 : ∀ c : Fin 103,
    (edge 40).2 < c → SeedEncoding.indexedAdj (edge 40).1 c →
    SeedEncoding.indexedAdj (edge 40).2 c →
      triangle (triangleIndex 40 c) = ((edge 40).1,(edge 40).2,c) := by decide +kernel
theorem triangle_complete_41 : ∀ c : Fin 103,
    (edge 41).2 < c → SeedEncoding.indexedAdj (edge 41).1 c →
    SeedEncoding.indexedAdj (edge 41).2 c →
      triangle (triangleIndex 41 c) = ((edge 41).1,(edge 41).2,c) := by decide +kernel
theorem triangle_complete_42 : ∀ c : Fin 103,
    (edge 42).2 < c → SeedEncoding.indexedAdj (edge 42).1 c →
    SeedEncoding.indexedAdj (edge 42).2 c →
      triangle (triangleIndex 42 c) = ((edge 42).1,(edge 42).2,c) := by decide +kernel
theorem triangle_complete_43 : ∀ c : Fin 103,
    (edge 43).2 < c → SeedEncoding.indexedAdj (edge 43).1 c →
    SeedEncoding.indexedAdj (edge 43).2 c →
      triangle (triangleIndex 43 c) = ((edge 43).1,(edge 43).2,c) := by decide +kernel
theorem triangle_complete_44 : ∀ c : Fin 103,
    (edge 44).2 < c → SeedEncoding.indexedAdj (edge 44).1 c →
    SeedEncoding.indexedAdj (edge 44).2 c →
      triangle (triangleIndex 44 c) = ((edge 44).1,(edge 44).2,c) := by decide +kernel
theorem triangle_complete_45 : ∀ c : Fin 103,
    (edge 45).2 < c → SeedEncoding.indexedAdj (edge 45).1 c →
    SeedEncoding.indexedAdj (edge 45).2 c →
      triangle (triangleIndex 45 c) = ((edge 45).1,(edge 45).2,c) := by decide +kernel
theorem triangle_complete_46 : ∀ c : Fin 103,
    (edge 46).2 < c → SeedEncoding.indexedAdj (edge 46).1 c →
    SeedEncoding.indexedAdj (edge 46).2 c →
      triangle (triangleIndex 46 c) = ((edge 46).1,(edge 46).2,c) := by decide +kernel
theorem triangle_complete_47 : ∀ c : Fin 103,
    (edge 47).2 < c → SeedEncoding.indexedAdj (edge 47).1 c →
    SeedEncoding.indexedAdj (edge 47).2 c →
      triangle (triangleIndex 47 c) = ((edge 47).1,(edge 47).2,c) := by decide +kernel
theorem triangle_complete_48 : ∀ c : Fin 103,
    (edge 48).2 < c → SeedEncoding.indexedAdj (edge 48).1 c →
    SeedEncoding.indexedAdj (edge 48).2 c →
      triangle (triangleIndex 48 c) = ((edge 48).1,(edge 48).2,c) := by decide +kernel
theorem triangle_complete_49 : ∀ c : Fin 103,
    (edge 49).2 < c → SeedEncoding.indexedAdj (edge 49).1 c →
    SeedEncoding.indexedAdj (edge 49).2 c →
      triangle (triangleIndex 49 c) = ((edge 49).1,(edge 49).2,c) := by decide +kernel
theorem triangle_complete_50 : ∀ c : Fin 103,
    (edge 50).2 < c → SeedEncoding.indexedAdj (edge 50).1 c →
    SeedEncoding.indexedAdj (edge 50).2 c →
      triangle (triangleIndex 50 c) = ((edge 50).1,(edge 50).2,c) := by decide +kernel
theorem triangle_complete_51 : ∀ c : Fin 103,
    (edge 51).2 < c → SeedEncoding.indexedAdj (edge 51).1 c →
    SeedEncoding.indexedAdj (edge 51).2 c →
      triangle (triangleIndex 51 c) = ((edge 51).1,(edge 51).2,c) := by decide +kernel
theorem triangle_complete_52 : ∀ c : Fin 103,
    (edge 52).2 < c → SeedEncoding.indexedAdj (edge 52).1 c →
    SeedEncoding.indexedAdj (edge 52).2 c →
      triangle (triangleIndex 52 c) = ((edge 52).1,(edge 52).2,c) := by decide +kernel
theorem triangle_complete_53 : ∀ c : Fin 103,
    (edge 53).2 < c → SeedEncoding.indexedAdj (edge 53).1 c →
    SeedEncoding.indexedAdj (edge 53).2 c →
      triangle (triangleIndex 53 c) = ((edge 53).1,(edge 53).2,c) := by decide +kernel
theorem triangle_complete_54 : ∀ c : Fin 103,
    (edge 54).2 < c → SeedEncoding.indexedAdj (edge 54).1 c →
    SeedEncoding.indexedAdj (edge 54).2 c →
      triangle (triangleIndex 54 c) = ((edge 54).1,(edge 54).2,c) := by decide +kernel
theorem triangle_complete_55 : ∀ c : Fin 103,
    (edge 55).2 < c → SeedEncoding.indexedAdj (edge 55).1 c →
    SeedEncoding.indexedAdj (edge 55).2 c →
      triangle (triangleIndex 55 c) = ((edge 55).1,(edge 55).2,c) := by decide +kernel
theorem triangle_complete_56 : ∀ c : Fin 103,
    (edge 56).2 < c → SeedEncoding.indexedAdj (edge 56).1 c →
    SeedEncoding.indexedAdj (edge 56).2 c →
      triangle (triangleIndex 56 c) = ((edge 56).1,(edge 56).2,c) := by decide +kernel
theorem triangle_complete_57 : ∀ c : Fin 103,
    (edge 57).2 < c → SeedEncoding.indexedAdj (edge 57).1 c →
    SeedEncoding.indexedAdj (edge 57).2 c →
      triangle (triangleIndex 57 c) = ((edge 57).1,(edge 57).2,c) := by decide +kernel
theorem triangle_complete_58 : ∀ c : Fin 103,
    (edge 58).2 < c → SeedEncoding.indexedAdj (edge 58).1 c →
    SeedEncoding.indexedAdj (edge 58).2 c →
      triangle (triangleIndex 58 c) = ((edge 58).1,(edge 58).2,c) := by decide +kernel
theorem triangle_complete_59 : ∀ c : Fin 103,
    (edge 59).2 < c → SeedEncoding.indexedAdj (edge 59).1 c →
    SeedEncoding.indexedAdj (edge 59).2 c →
      triangle (triangleIndex 59 c) = ((edge 59).1,(edge 59).2,c) := by decide +kernel
theorem triangle_complete_60 : ∀ c : Fin 103,
    (edge 60).2 < c → SeedEncoding.indexedAdj (edge 60).1 c →
    SeedEncoding.indexedAdj (edge 60).2 c →
      triangle (triangleIndex 60 c) = ((edge 60).1,(edge 60).2,c) := by decide +kernel
theorem triangle_complete_61 : ∀ c : Fin 103,
    (edge 61).2 < c → SeedEncoding.indexedAdj (edge 61).1 c →
    SeedEncoding.indexedAdj (edge 61).2 c →
      triangle (triangleIndex 61 c) = ((edge 61).1,(edge 61).2,c) := by decide +kernel
theorem triangle_complete_62 : ∀ c : Fin 103,
    (edge 62).2 < c → SeedEncoding.indexedAdj (edge 62).1 c →
    SeedEncoding.indexedAdj (edge 62).2 c →
      triangle (triangleIndex 62 c) = ((edge 62).1,(edge 62).2,c) := by decide +kernel
theorem triangle_complete_63 : ∀ c : Fin 103,
    (edge 63).2 < c → SeedEncoding.indexedAdj (edge 63).1 c →
    SeedEncoding.indexedAdj (edge 63).2 c →
      triangle (triangleIndex 63 c) = ((edge 63).1,(edge 63).2,c) := by decide +kernel
theorem triangle_complete_64 : ∀ c : Fin 103,
    (edge 64).2 < c → SeedEncoding.indexedAdj (edge 64).1 c →
    SeedEncoding.indexedAdj (edge 64).2 c →
      triangle (triangleIndex 64 c) = ((edge 64).1,(edge 64).2,c) := by decide +kernel
theorem triangle_complete_65 : ∀ c : Fin 103,
    (edge 65).2 < c → SeedEncoding.indexedAdj (edge 65).1 c →
    SeedEncoding.indexedAdj (edge 65).2 c →
      triangle (triangleIndex 65 c) = ((edge 65).1,(edge 65).2,c) := by decide +kernel
theorem triangle_complete_66 : ∀ c : Fin 103,
    (edge 66).2 < c → SeedEncoding.indexedAdj (edge 66).1 c →
    SeedEncoding.indexedAdj (edge 66).2 c →
      triangle (triangleIndex 66 c) = ((edge 66).1,(edge 66).2,c) := by decide +kernel
theorem triangle_complete_67 : ∀ c : Fin 103,
    (edge 67).2 < c → SeedEncoding.indexedAdj (edge 67).1 c →
    SeedEncoding.indexedAdj (edge 67).2 c →
      triangle (triangleIndex 67 c) = ((edge 67).1,(edge 67).2,c) := by decide +kernel
theorem triangle_complete_68 : ∀ c : Fin 103,
    (edge 68).2 < c → SeedEncoding.indexedAdj (edge 68).1 c →
    SeedEncoding.indexedAdj (edge 68).2 c →
      triangle (triangleIndex 68 c) = ((edge 68).1,(edge 68).2,c) := by decide +kernel
theorem triangle_complete_69 : ∀ c : Fin 103,
    (edge 69).2 < c → SeedEncoding.indexedAdj (edge 69).1 c →
    SeedEncoding.indexedAdj (edge 69).2 c →
      triangle (triangleIndex 69 c) = ((edge 69).1,(edge 69).2,c) := by decide +kernel
theorem triangle_complete_70 : ∀ c : Fin 103,
    (edge 70).2 < c → SeedEncoding.indexedAdj (edge 70).1 c →
    SeedEncoding.indexedAdj (edge 70).2 c →
      triangle (triangleIndex 70 c) = ((edge 70).1,(edge 70).2,c) := by decide +kernel
theorem triangle_complete_71 : ∀ c : Fin 103,
    (edge 71).2 < c → SeedEncoding.indexedAdj (edge 71).1 c →
    SeedEncoding.indexedAdj (edge 71).2 c →
      triangle (triangleIndex 71 c) = ((edge 71).1,(edge 71).2,c) := by decide +kernel
theorem triangle_complete_72 : ∀ c : Fin 103,
    (edge 72).2 < c → SeedEncoding.indexedAdj (edge 72).1 c →
    SeedEncoding.indexedAdj (edge 72).2 c →
      triangle (triangleIndex 72 c) = ((edge 72).1,(edge 72).2,c) := by decide +kernel
theorem triangle_complete_73 : ∀ c : Fin 103,
    (edge 73).2 < c → SeedEncoding.indexedAdj (edge 73).1 c →
    SeedEncoding.indexedAdj (edge 73).2 c →
      triangle (triangleIndex 73 c) = ((edge 73).1,(edge 73).2,c) := by decide +kernel
theorem triangle_complete_74 : ∀ c : Fin 103,
    (edge 74).2 < c → SeedEncoding.indexedAdj (edge 74).1 c →
    SeedEncoding.indexedAdj (edge 74).2 c →
      triangle (triangleIndex 74 c) = ((edge 74).1,(edge 74).2,c) := by decide +kernel
theorem triangle_complete_75 : ∀ c : Fin 103,
    (edge 75).2 < c → SeedEncoding.indexedAdj (edge 75).1 c →
    SeedEncoding.indexedAdj (edge 75).2 c →
      triangle (triangleIndex 75 c) = ((edge 75).1,(edge 75).2,c) := by decide +kernel
theorem triangle_complete_76 : ∀ c : Fin 103,
    (edge 76).2 < c → SeedEncoding.indexedAdj (edge 76).1 c →
    SeedEncoding.indexedAdj (edge 76).2 c →
      triangle (triangleIndex 76 c) = ((edge 76).1,(edge 76).2,c) := by decide +kernel
theorem triangle_complete_77 : ∀ c : Fin 103,
    (edge 77).2 < c → SeedEncoding.indexedAdj (edge 77).1 c →
    SeedEncoding.indexedAdj (edge 77).2 c →
      triangle (triangleIndex 77 c) = ((edge 77).1,(edge 77).2,c) := by decide +kernel
theorem triangle_complete_78 : ∀ c : Fin 103,
    (edge 78).2 < c → SeedEncoding.indexedAdj (edge 78).1 c →
    SeedEncoding.indexedAdj (edge 78).2 c →
      triangle (triangleIndex 78 c) = ((edge 78).1,(edge 78).2,c) := by decide +kernel
theorem triangle_complete_79 : ∀ c : Fin 103,
    (edge 79).2 < c → SeedEncoding.indexedAdj (edge 79).1 c →
    SeedEncoding.indexedAdj (edge 79).2 c →
      triangle (triangleIndex 79 c) = ((edge 79).1,(edge 79).2,c) := by decide +kernel
theorem triangle_complete_80 : ∀ c : Fin 103,
    (edge 80).2 < c → SeedEncoding.indexedAdj (edge 80).1 c →
    SeedEncoding.indexedAdj (edge 80).2 c →
      triangle (triangleIndex 80 c) = ((edge 80).1,(edge 80).2,c) := by decide +kernel
theorem triangle_complete_81 : ∀ c : Fin 103,
    (edge 81).2 < c → SeedEncoding.indexedAdj (edge 81).1 c →
    SeedEncoding.indexedAdj (edge 81).2 c →
      triangle (triangleIndex 81 c) = ((edge 81).1,(edge 81).2,c) := by decide +kernel
theorem triangle_complete_82 : ∀ c : Fin 103,
    (edge 82).2 < c → SeedEncoding.indexedAdj (edge 82).1 c →
    SeedEncoding.indexedAdj (edge 82).2 c →
      triangle (triangleIndex 82 c) = ((edge 82).1,(edge 82).2,c) := by decide +kernel
theorem triangle_complete_83 : ∀ c : Fin 103,
    (edge 83).2 < c → SeedEncoding.indexedAdj (edge 83).1 c →
    SeedEncoding.indexedAdj (edge 83).2 c →
      triangle (triangleIndex 83 c) = ((edge 83).1,(edge 83).2,c) := by decide +kernel
theorem triangle_complete_84 : ∀ c : Fin 103,
    (edge 84).2 < c → SeedEncoding.indexedAdj (edge 84).1 c →
    SeedEncoding.indexedAdj (edge 84).2 c →
      triangle (triangleIndex 84 c) = ((edge 84).1,(edge 84).2,c) := by decide +kernel
theorem triangle_complete_85 : ∀ c : Fin 103,
    (edge 85).2 < c → SeedEncoding.indexedAdj (edge 85).1 c →
    SeedEncoding.indexedAdj (edge 85).2 c →
      triangle (triangleIndex 85 c) = ((edge 85).1,(edge 85).2,c) := by decide +kernel
theorem triangle_complete_86 : ∀ c : Fin 103,
    (edge 86).2 < c → SeedEncoding.indexedAdj (edge 86).1 c →
    SeedEncoding.indexedAdj (edge 86).2 c →
      triangle (triangleIndex 86 c) = ((edge 86).1,(edge 86).2,c) := by decide +kernel
theorem triangle_complete_87 : ∀ c : Fin 103,
    (edge 87).2 < c → SeedEncoding.indexedAdj (edge 87).1 c →
    SeedEncoding.indexedAdj (edge 87).2 c →
      triangle (triangleIndex 87 c) = ((edge 87).1,(edge 87).2,c) := by decide +kernel
theorem triangle_complete_88 : ∀ c : Fin 103,
    (edge 88).2 < c → SeedEncoding.indexedAdj (edge 88).1 c →
    SeedEncoding.indexedAdj (edge 88).2 c →
      triangle (triangleIndex 88 c) = ((edge 88).1,(edge 88).2,c) := by decide +kernel
theorem triangle_complete_89 : ∀ c : Fin 103,
    (edge 89).2 < c → SeedEncoding.indexedAdj (edge 89).1 c →
    SeedEncoding.indexedAdj (edge 89).2 c →
      triangle (triangleIndex 89 c) = ((edge 89).1,(edge 89).2,c) := by decide +kernel
theorem triangle_complete_90 : ∀ c : Fin 103,
    (edge 90).2 < c → SeedEncoding.indexedAdj (edge 90).1 c →
    SeedEncoding.indexedAdj (edge 90).2 c →
      triangle (triangleIndex 90 c) = ((edge 90).1,(edge 90).2,c) := by decide +kernel
theorem triangle_complete_91 : ∀ c : Fin 103,
    (edge 91).2 < c → SeedEncoding.indexedAdj (edge 91).1 c →
    SeedEncoding.indexedAdj (edge 91).2 c →
      triangle (triangleIndex 91 c) = ((edge 91).1,(edge 91).2,c) := by decide +kernel
theorem triangle_complete_92 : ∀ c : Fin 103,
    (edge 92).2 < c → SeedEncoding.indexedAdj (edge 92).1 c →
    SeedEncoding.indexedAdj (edge 92).2 c →
      triangle (triangleIndex 92 c) = ((edge 92).1,(edge 92).2,c) := by decide +kernel
theorem triangle_complete_93 : ∀ c : Fin 103,
    (edge 93).2 < c → SeedEncoding.indexedAdj (edge 93).1 c →
    SeedEncoding.indexedAdj (edge 93).2 c →
      triangle (triangleIndex 93 c) = ((edge 93).1,(edge 93).2,c) := by decide +kernel
theorem triangle_complete_94 : ∀ c : Fin 103,
    (edge 94).2 < c → SeedEncoding.indexedAdj (edge 94).1 c →
    SeedEncoding.indexedAdj (edge 94).2 c →
      triangle (triangleIndex 94 c) = ((edge 94).1,(edge 94).2,c) := by decide +kernel
theorem triangle_complete_95 : ∀ c : Fin 103,
    (edge 95).2 < c → SeedEncoding.indexedAdj (edge 95).1 c →
    SeedEncoding.indexedAdj (edge 95).2 c →
      triangle (triangleIndex 95 c) = ((edge 95).1,(edge 95).2,c) := by decide +kernel
theorem triangle_complete_96 : ∀ c : Fin 103,
    (edge 96).2 < c → SeedEncoding.indexedAdj (edge 96).1 c →
    SeedEncoding.indexedAdj (edge 96).2 c →
      triangle (triangleIndex 96 c) = ((edge 96).1,(edge 96).2,c) := by decide +kernel
theorem triangle_complete_97 : ∀ c : Fin 103,
    (edge 97).2 < c → SeedEncoding.indexedAdj (edge 97).1 c →
    SeedEncoding.indexedAdj (edge 97).2 c →
      triangle (triangleIndex 97 c) = ((edge 97).1,(edge 97).2,c) := by decide +kernel
theorem triangle_complete_98 : ∀ c : Fin 103,
    (edge 98).2 < c → SeedEncoding.indexedAdj (edge 98).1 c →
    SeedEncoding.indexedAdj (edge 98).2 c →
      triangle (triangleIndex 98 c) = ((edge 98).1,(edge 98).2,c) := by decide +kernel
theorem triangle_complete_99 : ∀ c : Fin 103,
    (edge 99).2 < c → SeedEncoding.indexedAdj (edge 99).1 c →
    SeedEncoding.indexedAdj (edge 99).2 c →
      triangle (triangleIndex 99 c) = ((edge 99).1,(edge 99).2,c) := by decide +kernel
theorem triangle_complete_100 : ∀ c : Fin 103,
    (edge 100).2 < c → SeedEncoding.indexedAdj (edge 100).1 c →
    SeedEncoding.indexedAdj (edge 100).2 c →
      triangle (triangleIndex 100 c) = ((edge 100).1,(edge 100).2,c) := by decide +kernel
theorem triangle_complete_101 : ∀ c : Fin 103,
    (edge 101).2 < c → SeedEncoding.indexedAdj (edge 101).1 c →
    SeedEncoding.indexedAdj (edge 101).2 c →
      triangle (triangleIndex 101 c) = ((edge 101).1,(edge 101).2,c) := by decide +kernel
theorem triangle_complete_102 : ∀ c : Fin 103,
    (edge 102).2 < c → SeedEncoding.indexedAdj (edge 102).1 c →
    SeedEncoding.indexedAdj (edge 102).2 c →
      triangle (triangleIndex 102 c) = ((edge 102).1,(edge 102).2,c) := by decide +kernel
theorem triangle_complete_103 : ∀ c : Fin 103,
    (edge 103).2 < c → SeedEncoding.indexedAdj (edge 103).1 c →
    SeedEncoding.indexedAdj (edge 103).2 c →
      triangle (triangleIndex 103 c) = ((edge 103).1,(edge 103).2,c) := by decide +kernel
theorem triangle_complete_104 : ∀ c : Fin 103,
    (edge 104).2 < c → SeedEncoding.indexedAdj (edge 104).1 c →
    SeedEncoding.indexedAdj (edge 104).2 c →
      triangle (triangleIndex 104 c) = ((edge 104).1,(edge 104).2,c) := by decide +kernel
theorem triangle_complete_105 : ∀ c : Fin 103,
    (edge 105).2 < c → SeedEncoding.indexedAdj (edge 105).1 c →
    SeedEncoding.indexedAdj (edge 105).2 c →
      triangle (triangleIndex 105 c) = ((edge 105).1,(edge 105).2,c) := by decide +kernel
theorem triangle_complete_106 : ∀ c : Fin 103,
    (edge 106).2 < c → SeedEncoding.indexedAdj (edge 106).1 c →
    SeedEncoding.indexedAdj (edge 106).2 c →
      triangle (triangleIndex 106 c) = ((edge 106).1,(edge 106).2,c) := by decide +kernel
theorem triangle_complete_107 : ∀ c : Fin 103,
    (edge 107).2 < c → SeedEncoding.indexedAdj (edge 107).1 c →
    SeedEncoding.indexedAdj (edge 107).2 c →
      triangle (triangleIndex 107 c) = ((edge 107).1,(edge 107).2,c) := by decide +kernel
theorem triangle_complete_108 : ∀ c : Fin 103,
    (edge 108).2 < c → SeedEncoding.indexedAdj (edge 108).1 c →
    SeedEncoding.indexedAdj (edge 108).2 c →
      triangle (triangleIndex 108 c) = ((edge 108).1,(edge 108).2,c) := by decide +kernel
theorem triangle_complete_109 : ∀ c : Fin 103,
    (edge 109).2 < c → SeedEncoding.indexedAdj (edge 109).1 c →
    SeedEncoding.indexedAdj (edge 109).2 c →
      triangle (triangleIndex 109 c) = ((edge 109).1,(edge 109).2,c) := by decide +kernel
theorem triangle_complete_110 : ∀ c : Fin 103,
    (edge 110).2 < c → SeedEncoding.indexedAdj (edge 110).1 c →
    SeedEncoding.indexedAdj (edge 110).2 c →
      triangle (triangleIndex 110 c) = ((edge 110).1,(edge 110).2,c) := by decide +kernel
theorem triangle_complete_111 : ∀ c : Fin 103,
    (edge 111).2 < c → SeedEncoding.indexedAdj (edge 111).1 c →
    SeedEncoding.indexedAdj (edge 111).2 c →
      triangle (triangleIndex 111 c) = ((edge 111).1,(edge 111).2,c) := by decide +kernel
theorem triangle_complete_112 : ∀ c : Fin 103,
    (edge 112).2 < c → SeedEncoding.indexedAdj (edge 112).1 c →
    SeedEncoding.indexedAdj (edge 112).2 c →
      triangle (triangleIndex 112 c) = ((edge 112).1,(edge 112).2,c) := by decide +kernel
theorem triangle_complete_113 : ∀ c : Fin 103,
    (edge 113).2 < c → SeedEncoding.indexedAdj (edge 113).1 c →
    SeedEncoding.indexedAdj (edge 113).2 c →
      triangle (triangleIndex 113 c) = ((edge 113).1,(edge 113).2,c) := by decide +kernel
theorem triangle_complete_114 : ∀ c : Fin 103,
    (edge 114).2 < c → SeedEncoding.indexedAdj (edge 114).1 c →
    SeedEncoding.indexedAdj (edge 114).2 c →
      triangle (triangleIndex 114 c) = ((edge 114).1,(edge 114).2,c) := by decide +kernel
theorem triangle_complete_115 : ∀ c : Fin 103,
    (edge 115).2 < c → SeedEncoding.indexedAdj (edge 115).1 c →
    SeedEncoding.indexedAdj (edge 115).2 c →
      triangle (triangleIndex 115 c) = ((edge 115).1,(edge 115).2,c) := by decide +kernel
theorem triangle_complete_116 : ∀ c : Fin 103,
    (edge 116).2 < c → SeedEncoding.indexedAdj (edge 116).1 c →
    SeedEncoding.indexedAdj (edge 116).2 c →
      triangle (triangleIndex 116 c) = ((edge 116).1,(edge 116).2,c) := by decide +kernel
theorem triangle_complete_117 : ∀ c : Fin 103,
    (edge 117).2 < c → SeedEncoding.indexedAdj (edge 117).1 c →
    SeedEncoding.indexedAdj (edge 117).2 c →
      triangle (triangleIndex 117 c) = ((edge 117).1,(edge 117).2,c) := by decide +kernel
theorem triangle_complete_118 : ∀ c : Fin 103,
    (edge 118).2 < c → SeedEncoding.indexedAdj (edge 118).1 c →
    SeedEncoding.indexedAdj (edge 118).2 c →
      triangle (triangleIndex 118 c) = ((edge 118).1,(edge 118).2,c) := by decide +kernel
theorem triangle_complete_119 : ∀ c : Fin 103,
    (edge 119).2 < c → SeedEncoding.indexedAdj (edge 119).1 c →
    SeedEncoding.indexedAdj (edge 119).2 c →
      triangle (triangleIndex 119 c) = ((edge 119).1,(edge 119).2,c) := by decide +kernel
theorem triangle_complete_120 : ∀ c : Fin 103,
    (edge 120).2 < c → SeedEncoding.indexedAdj (edge 120).1 c →
    SeedEncoding.indexedAdj (edge 120).2 c →
      triangle (triangleIndex 120 c) = ((edge 120).1,(edge 120).2,c) := by decide +kernel
theorem triangle_complete_121 : ∀ c : Fin 103,
    (edge 121).2 < c → SeedEncoding.indexedAdj (edge 121).1 c →
    SeedEncoding.indexedAdj (edge 121).2 c →
      triangle (triangleIndex 121 c) = ((edge 121).1,(edge 121).2,c) := by decide +kernel
theorem triangle_complete_122 : ∀ c : Fin 103,
    (edge 122).2 < c → SeedEncoding.indexedAdj (edge 122).1 c →
    SeedEncoding.indexedAdj (edge 122).2 c →
      triangle (triangleIndex 122 c) = ((edge 122).1,(edge 122).2,c) := by decide +kernel
theorem triangle_complete_123 : ∀ c : Fin 103,
    (edge 123).2 < c → SeedEncoding.indexedAdj (edge 123).1 c →
    SeedEncoding.indexedAdj (edge 123).2 c →
      triangle (triangleIndex 123 c) = ((edge 123).1,(edge 123).2,c) := by decide +kernel
theorem triangle_complete_124 : ∀ c : Fin 103,
    (edge 124).2 < c → SeedEncoding.indexedAdj (edge 124).1 c →
    SeedEncoding.indexedAdj (edge 124).2 c →
      triangle (triangleIndex 124 c) = ((edge 124).1,(edge 124).2,c) := by decide +kernel
theorem triangle_complete_125 : ∀ c : Fin 103,
    (edge 125).2 < c → SeedEncoding.indexedAdj (edge 125).1 c →
    SeedEncoding.indexedAdj (edge 125).2 c →
      triangle (triangleIndex 125 c) = ((edge 125).1,(edge 125).2,c) := by decide +kernel
theorem triangle_complete_126 : ∀ c : Fin 103,
    (edge 126).2 < c → SeedEncoding.indexedAdj (edge 126).1 c →
    SeedEncoding.indexedAdj (edge 126).2 c →
      triangle (triangleIndex 126 c) = ((edge 126).1,(edge 126).2,c) := by decide +kernel
theorem triangle_complete_127 : ∀ c : Fin 103,
    (edge 127).2 < c → SeedEncoding.indexedAdj (edge 127).1 c →
    SeedEncoding.indexedAdj (edge 127).2 c →
      triangle (triangleIndex 127 c) = ((edge 127).1,(edge 127).2,c) := by decide +kernel
theorem triangle_complete_128 : ∀ c : Fin 103,
    (edge 128).2 < c → SeedEncoding.indexedAdj (edge 128).1 c →
    SeedEncoding.indexedAdj (edge 128).2 c →
      triangle (triangleIndex 128 c) = ((edge 128).1,(edge 128).2,c) := by decide +kernel
theorem triangle_complete_129 : ∀ c : Fin 103,
    (edge 129).2 < c → SeedEncoding.indexedAdj (edge 129).1 c →
    SeedEncoding.indexedAdj (edge 129).2 c →
      triangle (triangleIndex 129 c) = ((edge 129).1,(edge 129).2,c) := by decide +kernel
theorem triangle_complete_130 : ∀ c : Fin 103,
    (edge 130).2 < c → SeedEncoding.indexedAdj (edge 130).1 c →
    SeedEncoding.indexedAdj (edge 130).2 c →
      triangle (triangleIndex 130 c) = ((edge 130).1,(edge 130).2,c) := by decide +kernel
theorem triangle_complete_131 : ∀ c : Fin 103,
    (edge 131).2 < c → SeedEncoding.indexedAdj (edge 131).1 c →
    SeedEncoding.indexedAdj (edge 131).2 c →
      triangle (triangleIndex 131 c) = ((edge 131).1,(edge 131).2,c) := by decide +kernel
theorem triangle_complete_132 : ∀ c : Fin 103,
    (edge 132).2 < c → SeedEncoding.indexedAdj (edge 132).1 c →
    SeedEncoding.indexedAdj (edge 132).2 c →
      triangle (triangleIndex 132 c) = ((edge 132).1,(edge 132).2,c) := by decide +kernel
theorem triangle_complete_133 : ∀ c : Fin 103,
    (edge 133).2 < c → SeedEncoding.indexedAdj (edge 133).1 c →
    SeedEncoding.indexedAdj (edge 133).2 c →
      triangle (triangleIndex 133 c) = ((edge 133).1,(edge 133).2,c) := by decide +kernel
theorem triangle_complete_134 : ∀ c : Fin 103,
    (edge 134).2 < c → SeedEncoding.indexedAdj (edge 134).1 c →
    SeedEncoding.indexedAdj (edge 134).2 c →
      triangle (triangleIndex 134 c) = ((edge 134).1,(edge 134).2,c) := by decide +kernel
theorem triangle_complete_135 : ∀ c : Fin 103,
    (edge 135).2 < c → SeedEncoding.indexedAdj (edge 135).1 c →
    SeedEncoding.indexedAdj (edge 135).2 c →
      triangle (triangleIndex 135 c) = ((edge 135).1,(edge 135).2,c) := by decide +kernel
theorem triangle_complete_136 : ∀ c : Fin 103,
    (edge 136).2 < c → SeedEncoding.indexedAdj (edge 136).1 c →
    SeedEncoding.indexedAdj (edge 136).2 c →
      triangle (triangleIndex 136 c) = ((edge 136).1,(edge 136).2,c) := by decide +kernel
theorem triangle_complete_137 : ∀ c : Fin 103,
    (edge 137).2 < c → SeedEncoding.indexedAdj (edge 137).1 c →
    SeedEncoding.indexedAdj (edge 137).2 c →
      triangle (triangleIndex 137 c) = ((edge 137).1,(edge 137).2,c) := by decide +kernel
theorem triangle_complete_138 : ∀ c : Fin 103,
    (edge 138).2 < c → SeedEncoding.indexedAdj (edge 138).1 c →
    SeedEncoding.indexedAdj (edge 138).2 c →
      triangle (triangleIndex 138 c) = ((edge 138).1,(edge 138).2,c) := by decide +kernel
theorem triangle_complete_139 : ∀ c : Fin 103,
    (edge 139).2 < c → SeedEncoding.indexedAdj (edge 139).1 c →
    SeedEncoding.indexedAdj (edge 139).2 c →
      triangle (triangleIndex 139 c) = ((edge 139).1,(edge 139).2,c) := by decide +kernel
theorem triangle_complete_140 : ∀ c : Fin 103,
    (edge 140).2 < c → SeedEncoding.indexedAdj (edge 140).1 c →
    SeedEncoding.indexedAdj (edge 140).2 c →
      triangle (triangleIndex 140 c) = ((edge 140).1,(edge 140).2,c) := by decide +kernel
theorem triangle_complete_141 : ∀ c : Fin 103,
    (edge 141).2 < c → SeedEncoding.indexedAdj (edge 141).1 c →
    SeedEncoding.indexedAdj (edge 141).2 c →
      triangle (triangleIndex 141 c) = ((edge 141).1,(edge 141).2,c) := by decide +kernel
theorem triangle_complete_142 : ∀ c : Fin 103,
    (edge 142).2 < c → SeedEncoding.indexedAdj (edge 142).1 c →
    SeedEncoding.indexedAdj (edge 142).2 c →
      triangle (triangleIndex 142 c) = ((edge 142).1,(edge 142).2,c) := by decide +kernel
theorem triangle_complete_143 : ∀ c : Fin 103,
    (edge 143).2 < c → SeedEncoding.indexedAdj (edge 143).1 c →
    SeedEncoding.indexedAdj (edge 143).2 c →
      triangle (triangleIndex 143 c) = ((edge 143).1,(edge 143).2,c) := by decide +kernel
theorem triangle_complete_144 : ∀ c : Fin 103,
    (edge 144).2 < c → SeedEncoding.indexedAdj (edge 144).1 c →
    SeedEncoding.indexedAdj (edge 144).2 c →
      triangle (triangleIndex 144 c) = ((edge 144).1,(edge 144).2,c) := by decide +kernel
theorem triangle_complete_145 : ∀ c : Fin 103,
    (edge 145).2 < c → SeedEncoding.indexedAdj (edge 145).1 c →
    SeedEncoding.indexedAdj (edge 145).2 c →
      triangle (triangleIndex 145 c) = ((edge 145).1,(edge 145).2,c) := by decide +kernel
theorem triangle_complete_146 : ∀ c : Fin 103,
    (edge 146).2 < c → SeedEncoding.indexedAdj (edge 146).1 c →
    SeedEncoding.indexedAdj (edge 146).2 c →
      triangle (triangleIndex 146 c) = ((edge 146).1,(edge 146).2,c) := by decide +kernel
theorem triangle_complete_147 : ∀ c : Fin 103,
    (edge 147).2 < c → SeedEncoding.indexedAdj (edge 147).1 c →
    SeedEncoding.indexedAdj (edge 147).2 c →
      triangle (triangleIndex 147 c) = ((edge 147).1,(edge 147).2,c) := by decide +kernel
theorem triangle_complete_148 : ∀ c : Fin 103,
    (edge 148).2 < c → SeedEncoding.indexedAdj (edge 148).1 c →
    SeedEncoding.indexedAdj (edge 148).2 c →
      triangle (triangleIndex 148 c) = ((edge 148).1,(edge 148).2,c) := by decide +kernel
theorem triangle_complete_149 : ∀ c : Fin 103,
    (edge 149).2 < c → SeedEncoding.indexedAdj (edge 149).1 c →
    SeedEncoding.indexedAdj (edge 149).2 c →
      triangle (triangleIndex 149 c) = ((edge 149).1,(edge 149).2,c) := by decide +kernel
theorem triangle_complete_150 : ∀ c : Fin 103,
    (edge 150).2 < c → SeedEncoding.indexedAdj (edge 150).1 c →
    SeedEncoding.indexedAdj (edge 150).2 c →
      triangle (triangleIndex 150 c) = ((edge 150).1,(edge 150).2,c) := by decide +kernel
theorem triangle_complete_151 : ∀ c : Fin 103,
    (edge 151).2 < c → SeedEncoding.indexedAdj (edge 151).1 c →
    SeedEncoding.indexedAdj (edge 151).2 c →
      triangle (triangleIndex 151 c) = ((edge 151).1,(edge 151).2,c) := by decide +kernel
theorem triangle_complete_152 : ∀ c : Fin 103,
    (edge 152).2 < c → SeedEncoding.indexedAdj (edge 152).1 c →
    SeedEncoding.indexedAdj (edge 152).2 c →
      triangle (triangleIndex 152 c) = ((edge 152).1,(edge 152).2,c) := by decide +kernel
theorem triangle_complete_153 : ∀ c : Fin 103,
    (edge 153).2 < c → SeedEncoding.indexedAdj (edge 153).1 c →
    SeedEncoding.indexedAdj (edge 153).2 c →
      triangle (triangleIndex 153 c) = ((edge 153).1,(edge 153).2,c) := by decide +kernel
theorem triangle_complete_154 : ∀ c : Fin 103,
    (edge 154).2 < c → SeedEncoding.indexedAdj (edge 154).1 c →
    SeedEncoding.indexedAdj (edge 154).2 c →
      triangle (triangleIndex 154 c) = ((edge 154).1,(edge 154).2,c) := by decide +kernel
theorem triangle_complete_155 : ∀ c : Fin 103,
    (edge 155).2 < c → SeedEncoding.indexedAdj (edge 155).1 c →
    SeedEncoding.indexedAdj (edge 155).2 c →
      triangle (triangleIndex 155 c) = ((edge 155).1,(edge 155).2,c) := by decide +kernel
theorem triangle_complete_156 : ∀ c : Fin 103,
    (edge 156).2 < c → SeedEncoding.indexedAdj (edge 156).1 c →
    SeedEncoding.indexedAdj (edge 156).2 c →
      triangle (triangleIndex 156 c) = ((edge 156).1,(edge 156).2,c) := by decide +kernel
theorem triangle_complete_157 : ∀ c : Fin 103,
    (edge 157).2 < c → SeedEncoding.indexedAdj (edge 157).1 c →
    SeedEncoding.indexedAdj (edge 157).2 c →
      triangle (triangleIndex 157 c) = ((edge 157).1,(edge 157).2,c) := by decide +kernel
theorem triangle_complete_158 : ∀ c : Fin 103,
    (edge 158).2 < c → SeedEncoding.indexedAdj (edge 158).1 c →
    SeedEncoding.indexedAdj (edge 158).2 c →
      triangle (triangleIndex 158 c) = ((edge 158).1,(edge 158).2,c) := by decide +kernel
theorem triangle_complete_159 : ∀ c : Fin 103,
    (edge 159).2 < c → SeedEncoding.indexedAdj (edge 159).1 c →
    SeedEncoding.indexedAdj (edge 159).2 c →
      triangle (triangleIndex 159 c) = ((edge 159).1,(edge 159).2,c) := by decide +kernel
theorem triangle_complete_160 : ∀ c : Fin 103,
    (edge 160).2 < c → SeedEncoding.indexedAdj (edge 160).1 c →
    SeedEncoding.indexedAdj (edge 160).2 c →
      triangle (triangleIndex 160 c) = ((edge 160).1,(edge 160).2,c) := by decide +kernel
theorem triangle_complete_161 : ∀ c : Fin 103,
    (edge 161).2 < c → SeedEncoding.indexedAdj (edge 161).1 c →
    SeedEncoding.indexedAdj (edge 161).2 c →
      triangle (triangleIndex 161 c) = ((edge 161).1,(edge 161).2,c) := by decide +kernel
theorem triangle_complete_162 : ∀ c : Fin 103,
    (edge 162).2 < c → SeedEncoding.indexedAdj (edge 162).1 c →
    SeedEncoding.indexedAdj (edge 162).2 c →
      triangle (triangleIndex 162 c) = ((edge 162).1,(edge 162).2,c) := by decide +kernel
theorem triangle_complete_163 : ∀ c : Fin 103,
    (edge 163).2 < c → SeedEncoding.indexedAdj (edge 163).1 c →
    SeedEncoding.indexedAdj (edge 163).2 c →
      triangle (triangleIndex 163 c) = ((edge 163).1,(edge 163).2,c) := by decide +kernel
theorem triangle_complete_164 : ∀ c : Fin 103,
    (edge 164).2 < c → SeedEncoding.indexedAdj (edge 164).1 c →
    SeedEncoding.indexedAdj (edge 164).2 c →
      triangle (triangleIndex 164 c) = ((edge 164).1,(edge 164).2,c) := by decide +kernel
theorem triangle_complete_165 : ∀ c : Fin 103,
    (edge 165).2 < c → SeedEncoding.indexedAdj (edge 165).1 c →
    SeedEncoding.indexedAdj (edge 165).2 c →
      triangle (triangleIndex 165 c) = ((edge 165).1,(edge 165).2,c) := by decide +kernel
theorem triangle_complete_166 : ∀ c : Fin 103,
    (edge 166).2 < c → SeedEncoding.indexedAdj (edge 166).1 c →
    SeedEncoding.indexedAdj (edge 166).2 c →
      triangle (triangleIndex 166 c) = ((edge 166).1,(edge 166).2,c) := by decide +kernel
theorem triangle_complete_167 : ∀ c : Fin 103,
    (edge 167).2 < c → SeedEncoding.indexedAdj (edge 167).1 c →
    SeedEncoding.indexedAdj (edge 167).2 c →
      triangle (triangleIndex 167 c) = ((edge 167).1,(edge 167).2,c) := by decide +kernel
theorem triangle_complete_168 : ∀ c : Fin 103,
    (edge 168).2 < c → SeedEncoding.indexedAdj (edge 168).1 c →
    SeedEncoding.indexedAdj (edge 168).2 c →
      triangle (triangleIndex 168 c) = ((edge 168).1,(edge 168).2,c) := by decide +kernel
theorem triangle_complete_169 : ∀ c : Fin 103,
    (edge 169).2 < c → SeedEncoding.indexedAdj (edge 169).1 c →
    SeedEncoding.indexedAdj (edge 169).2 c →
      triangle (triangleIndex 169 c) = ((edge 169).1,(edge 169).2,c) := by decide +kernel
theorem triangle_complete_170 : ∀ c : Fin 103,
    (edge 170).2 < c → SeedEncoding.indexedAdj (edge 170).1 c →
    SeedEncoding.indexedAdj (edge 170).2 c →
      triangle (triangleIndex 170 c) = ((edge 170).1,(edge 170).2,c) := by decide +kernel
theorem triangle_complete_171 : ∀ c : Fin 103,
    (edge 171).2 < c → SeedEncoding.indexedAdj (edge 171).1 c →
    SeedEncoding.indexedAdj (edge 171).2 c →
      triangle (triangleIndex 171 c) = ((edge 171).1,(edge 171).2,c) := by decide +kernel
theorem triangle_complete_172 : ∀ c : Fin 103,
    (edge 172).2 < c → SeedEncoding.indexedAdj (edge 172).1 c →
    SeedEncoding.indexedAdj (edge 172).2 c →
      triangle (triangleIndex 172 c) = ((edge 172).1,(edge 172).2,c) := by decide +kernel
theorem triangle_complete_173 : ∀ c : Fin 103,
    (edge 173).2 < c → SeedEncoding.indexedAdj (edge 173).1 c →
    SeedEncoding.indexedAdj (edge 173).2 c →
      triangle (triangleIndex 173 c) = ((edge 173).1,(edge 173).2,c) := by decide +kernel
theorem triangle_complete_174 : ∀ c : Fin 103,
    (edge 174).2 < c → SeedEncoding.indexedAdj (edge 174).1 c →
    SeedEncoding.indexedAdj (edge 174).2 c →
      triangle (triangleIndex 174 c) = ((edge 174).1,(edge 174).2,c) := by decide +kernel
theorem triangle_complete_175 : ∀ c : Fin 103,
    (edge 175).2 < c → SeedEncoding.indexedAdj (edge 175).1 c →
    SeedEncoding.indexedAdj (edge 175).2 c →
      triangle (triangleIndex 175 c) = ((edge 175).1,(edge 175).2,c) := by decide +kernel
theorem triangle_complete_176 : ∀ c : Fin 103,
    (edge 176).2 < c → SeedEncoding.indexedAdj (edge 176).1 c →
    SeedEncoding.indexedAdj (edge 176).2 c →
      triangle (triangleIndex 176 c) = ((edge 176).1,(edge 176).2,c) := by decide +kernel
theorem triangle_complete_177 : ∀ c : Fin 103,
    (edge 177).2 < c → SeedEncoding.indexedAdj (edge 177).1 c →
    SeedEncoding.indexedAdj (edge 177).2 c →
      triangle (triangleIndex 177 c) = ((edge 177).1,(edge 177).2,c) := by decide +kernel
theorem triangle_complete_178 : ∀ c : Fin 103,
    (edge 178).2 < c → SeedEncoding.indexedAdj (edge 178).1 c →
    SeedEncoding.indexedAdj (edge 178).2 c →
      triangle (triangleIndex 178 c) = ((edge 178).1,(edge 178).2,c) := by decide +kernel
theorem triangle_complete_179 : ∀ c : Fin 103,
    (edge 179).2 < c → SeedEncoding.indexedAdj (edge 179).1 c →
    SeedEncoding.indexedAdj (edge 179).2 c →
      triangle (triangleIndex 179 c) = ((edge 179).1,(edge 179).2,c) := by decide +kernel
theorem triangle_complete_180 : ∀ c : Fin 103,
    (edge 180).2 < c → SeedEncoding.indexedAdj (edge 180).1 c →
    SeedEncoding.indexedAdj (edge 180).2 c →
      triangle (triangleIndex 180 c) = ((edge 180).1,(edge 180).2,c) := by decide +kernel
theorem triangle_complete_181 : ∀ c : Fin 103,
    (edge 181).2 < c → SeedEncoding.indexedAdj (edge 181).1 c →
    SeedEncoding.indexedAdj (edge 181).2 c →
      triangle (triangleIndex 181 c) = ((edge 181).1,(edge 181).2,c) := by decide +kernel
theorem triangle_complete_182 : ∀ c : Fin 103,
    (edge 182).2 < c → SeedEncoding.indexedAdj (edge 182).1 c →
    SeedEncoding.indexedAdj (edge 182).2 c →
      triangle (triangleIndex 182 c) = ((edge 182).1,(edge 182).2,c) := by decide +kernel
theorem triangle_complete_183 : ∀ c : Fin 103,
    (edge 183).2 < c → SeedEncoding.indexedAdj (edge 183).1 c →
    SeedEncoding.indexedAdj (edge 183).2 c →
      triangle (triangleIndex 183 c) = ((edge 183).1,(edge 183).2,c) := by decide +kernel
theorem triangle_complete_184 : ∀ c : Fin 103,
    (edge 184).2 < c → SeedEncoding.indexedAdj (edge 184).1 c →
    SeedEncoding.indexedAdj (edge 184).2 c →
      triangle (triangleIndex 184 c) = ((edge 184).1,(edge 184).2,c) := by decide +kernel
theorem triangle_complete_185 : ∀ c : Fin 103,
    (edge 185).2 < c → SeedEncoding.indexedAdj (edge 185).1 c →
    SeedEncoding.indexedAdj (edge 185).2 c →
      triangle (triangleIndex 185 c) = ((edge 185).1,(edge 185).2,c) := by decide +kernel
theorem triangle_complete_186 : ∀ c : Fin 103,
    (edge 186).2 < c → SeedEncoding.indexedAdj (edge 186).1 c →
    SeedEncoding.indexedAdj (edge 186).2 c →
      triangle (triangleIndex 186 c) = ((edge 186).1,(edge 186).2,c) := by decide +kernel
theorem triangle_complete_187 : ∀ c : Fin 103,
    (edge 187).2 < c → SeedEncoding.indexedAdj (edge 187).1 c →
    SeedEncoding.indexedAdj (edge 187).2 c →
      triangle (triangleIndex 187 c) = ((edge 187).1,(edge 187).2,c) := by decide +kernel
theorem triangle_complete_188 : ∀ c : Fin 103,
    (edge 188).2 < c → SeedEncoding.indexedAdj (edge 188).1 c →
    SeedEncoding.indexedAdj (edge 188).2 c →
      triangle (triangleIndex 188 c) = ((edge 188).1,(edge 188).2,c) := by decide +kernel
theorem triangle_complete_189 : ∀ c : Fin 103,
    (edge 189).2 < c → SeedEncoding.indexedAdj (edge 189).1 c →
    SeedEncoding.indexedAdj (edge 189).2 c →
      triangle (triangleIndex 189 c) = ((edge 189).1,(edge 189).2,c) := by decide +kernel
theorem triangle_complete_190 : ∀ c : Fin 103,
    (edge 190).2 < c → SeedEncoding.indexedAdj (edge 190).1 c →
    SeedEncoding.indexedAdj (edge 190).2 c →
      triangle (triangleIndex 190 c) = ((edge 190).1,(edge 190).2,c) := by decide +kernel
theorem triangle_complete_191 : ∀ c : Fin 103,
    (edge 191).2 < c → SeedEncoding.indexedAdj (edge 191).1 c →
    SeedEncoding.indexedAdj (edge 191).2 c →
      triangle (triangleIndex 191 c) = ((edge 191).1,(edge 191).2,c) := by decide +kernel
theorem triangle_complete_192 : ∀ c : Fin 103,
    (edge 192).2 < c → SeedEncoding.indexedAdj (edge 192).1 c →
    SeedEncoding.indexedAdj (edge 192).2 c →
      triangle (triangleIndex 192 c) = ((edge 192).1,(edge 192).2,c) := by decide +kernel
theorem triangle_complete_193 : ∀ c : Fin 103,
    (edge 193).2 < c → SeedEncoding.indexedAdj (edge 193).1 c →
    SeedEncoding.indexedAdj (edge 193).2 c →
      triangle (triangleIndex 193 c) = ((edge 193).1,(edge 193).2,c) := by decide +kernel
theorem triangle_complete_194 : ∀ c : Fin 103,
    (edge 194).2 < c → SeedEncoding.indexedAdj (edge 194).1 c →
    SeedEncoding.indexedAdj (edge 194).2 c →
      triangle (triangleIndex 194 c) = ((edge 194).1,(edge 194).2,c) := by decide +kernel
theorem triangle_complete_195 : ∀ c : Fin 103,
    (edge 195).2 < c → SeedEncoding.indexedAdj (edge 195).1 c →
    SeedEncoding.indexedAdj (edge 195).2 c →
      triangle (triangleIndex 195 c) = ((edge 195).1,(edge 195).2,c) := by decide +kernel
theorem triangle_complete_196 : ∀ c : Fin 103,
    (edge 196).2 < c → SeedEncoding.indexedAdj (edge 196).1 c →
    SeedEncoding.indexedAdj (edge 196).2 c →
      triangle (triangleIndex 196 c) = ((edge 196).1,(edge 196).2,c) := by decide +kernel
theorem triangle_complete_197 : ∀ c : Fin 103,
    (edge 197).2 < c → SeedEncoding.indexedAdj (edge 197).1 c →
    SeedEncoding.indexedAdj (edge 197).2 c →
      triangle (triangleIndex 197 c) = ((edge 197).1,(edge 197).2,c) := by decide +kernel
theorem triangle_complete_198 : ∀ c : Fin 103,
    (edge 198).2 < c → SeedEncoding.indexedAdj (edge 198).1 c →
    SeedEncoding.indexedAdj (edge 198).2 c →
      triangle (triangleIndex 198 c) = ((edge 198).1,(edge 198).2,c) := by decide +kernel
theorem triangle_complete_199 : ∀ c : Fin 103,
    (edge 199).2 < c → SeedEncoding.indexedAdj (edge 199).1 c →
    SeedEncoding.indexedAdj (edge 199).2 c →
      triangle (triangleIndex 199 c) = ((edge 199).1,(edge 199).2,c) := by decide +kernel
theorem triangle_complete_200 : ∀ c : Fin 103,
    (edge 200).2 < c → SeedEncoding.indexedAdj (edge 200).1 c →
    SeedEncoding.indexedAdj (edge 200).2 c →
      triangle (triangleIndex 200 c) = ((edge 200).1,(edge 200).2,c) := by decide +kernel
theorem triangle_complete_201 : ∀ c : Fin 103,
    (edge 201).2 < c → SeedEncoding.indexedAdj (edge 201).1 c →
    SeedEncoding.indexedAdj (edge 201).2 c →
      triangle (triangleIndex 201 c) = ((edge 201).1,(edge 201).2,c) := by decide +kernel
theorem triangle_complete_202 : ∀ c : Fin 103,
    (edge 202).2 < c → SeedEncoding.indexedAdj (edge 202).1 c →
    SeedEncoding.indexedAdj (edge 202).2 c →
      triangle (triangleIndex 202 c) = ((edge 202).1,(edge 202).2,c) := by decide +kernel
theorem triangle_complete_203 : ∀ c : Fin 103,
    (edge 203).2 < c → SeedEncoding.indexedAdj (edge 203).1 c →
    SeedEncoding.indexedAdj (edge 203).2 c →
      triangle (triangleIndex 203 c) = ((edge 203).1,(edge 203).2,c) := by decide +kernel
theorem triangle_complete_204 : ∀ c : Fin 103,
    (edge 204).2 < c → SeedEncoding.indexedAdj (edge 204).1 c →
    SeedEncoding.indexedAdj (edge 204).2 c →
      triangle (triangleIndex 204 c) = ((edge 204).1,(edge 204).2,c) := by decide +kernel
theorem triangle_complete_205 : ∀ c : Fin 103,
    (edge 205).2 < c → SeedEncoding.indexedAdj (edge 205).1 c →
    SeedEncoding.indexedAdj (edge 205).2 c →
      triangle (triangleIndex 205 c) = ((edge 205).1,(edge 205).2,c) := by decide +kernel
theorem triangle_complete_206 : ∀ c : Fin 103,
    (edge 206).2 < c → SeedEncoding.indexedAdj (edge 206).1 c →
    SeedEncoding.indexedAdj (edge 206).2 c →
      triangle (triangleIndex 206 c) = ((edge 206).1,(edge 206).2,c) := by decide +kernel
theorem triangle_complete_207 : ∀ c : Fin 103,
    (edge 207).2 < c → SeedEncoding.indexedAdj (edge 207).1 c →
    SeedEncoding.indexedAdj (edge 207).2 c →
      triangle (triangleIndex 207 c) = ((edge 207).1,(edge 207).2,c) := by decide +kernel
theorem triangle_complete_208 : ∀ c : Fin 103,
    (edge 208).2 < c → SeedEncoding.indexedAdj (edge 208).1 c →
    SeedEncoding.indexedAdj (edge 208).2 c →
      triangle (triangleIndex 208 c) = ((edge 208).1,(edge 208).2,c) := by decide +kernel
theorem triangle_complete_209 : ∀ c : Fin 103,
    (edge 209).2 < c → SeedEncoding.indexedAdj (edge 209).1 c →
    SeedEncoding.indexedAdj (edge 209).2 c →
      triangle (triangleIndex 209 c) = ((edge 209).1,(edge 209).2,c) := by decide +kernel
theorem triangle_complete_210 : ∀ c : Fin 103,
    (edge 210).2 < c → SeedEncoding.indexedAdj (edge 210).1 c →
    SeedEncoding.indexedAdj (edge 210).2 c →
      triangle (triangleIndex 210 c) = ((edge 210).1,(edge 210).2,c) := by decide +kernel
theorem triangle_complete_211 : ∀ c : Fin 103,
    (edge 211).2 < c → SeedEncoding.indexedAdj (edge 211).1 c →
    SeedEncoding.indexedAdj (edge 211).2 c →
      triangle (triangleIndex 211 c) = ((edge 211).1,(edge 211).2,c) := by decide +kernel
theorem triangle_complete_212 : ∀ c : Fin 103,
    (edge 212).2 < c → SeedEncoding.indexedAdj (edge 212).1 c →
    SeedEncoding.indexedAdj (edge 212).2 c →
      triangle (triangleIndex 212 c) = ((edge 212).1,(edge 212).2,c) := by decide +kernel
theorem triangle_complete_213 : ∀ c : Fin 103,
    (edge 213).2 < c → SeedEncoding.indexedAdj (edge 213).1 c →
    SeedEncoding.indexedAdj (edge 213).2 c →
      triangle (triangleIndex 213 c) = ((edge 213).1,(edge 213).2,c) := by decide +kernel
theorem triangle_complete_214 : ∀ c : Fin 103,
    (edge 214).2 < c → SeedEncoding.indexedAdj (edge 214).1 c →
    SeedEncoding.indexedAdj (edge 214).2 c →
      triangle (triangleIndex 214 c) = ((edge 214).1,(edge 214).2,c) := by decide +kernel
theorem triangle_complete_215 : ∀ c : Fin 103,
    (edge 215).2 < c → SeedEncoding.indexedAdj (edge 215).1 c →
    SeedEncoding.indexedAdj (edge 215).2 c →
      triangle (triangleIndex 215 c) = ((edge 215).1,(edge 215).2,c) := by decide +kernel
theorem triangle_complete_216 : ∀ c : Fin 103,
    (edge 216).2 < c → SeedEncoding.indexedAdj (edge 216).1 c →
    SeedEncoding.indexedAdj (edge 216).2 c →
      triangle (triangleIndex 216 c) = ((edge 216).1,(edge 216).2,c) := by decide +kernel
theorem triangle_complete_217 : ∀ c : Fin 103,
    (edge 217).2 < c → SeedEncoding.indexedAdj (edge 217).1 c →
    SeedEncoding.indexedAdj (edge 217).2 c →
      triangle (triangleIndex 217 c) = ((edge 217).1,(edge 217).2,c) := by decide +kernel
theorem triangle_complete_218 : ∀ c : Fin 103,
    (edge 218).2 < c → SeedEncoding.indexedAdj (edge 218).1 c →
    SeedEncoding.indexedAdj (edge 218).2 c →
      triangle (triangleIndex 218 c) = ((edge 218).1,(edge 218).2,c) := by decide +kernel
theorem triangle_complete_219 : ∀ c : Fin 103,
    (edge 219).2 < c → SeedEncoding.indexedAdj (edge 219).1 c →
    SeedEncoding.indexedAdj (edge 219).2 c →
      triangle (triangleIndex 219 c) = ((edge 219).1,(edge 219).2,c) := by decide +kernel
theorem triangle_complete_220 : ∀ c : Fin 103,
    (edge 220).2 < c → SeedEncoding.indexedAdj (edge 220).1 c →
    SeedEncoding.indexedAdj (edge 220).2 c →
      triangle (triangleIndex 220 c) = ((edge 220).1,(edge 220).2,c) := by decide +kernel
theorem triangle_complete_221 : ∀ c : Fin 103,
    (edge 221).2 < c → SeedEncoding.indexedAdj (edge 221).1 c →
    SeedEncoding.indexedAdj (edge 221).2 c →
      triangle (triangleIndex 221 c) = ((edge 221).1,(edge 221).2,c) := by decide +kernel
theorem triangle_complete_222 : ∀ c : Fin 103,
    (edge 222).2 < c → SeedEncoding.indexedAdj (edge 222).1 c →
    SeedEncoding.indexedAdj (edge 222).2 c →
      triangle (triangleIndex 222 c) = ((edge 222).1,(edge 222).2,c) := by decide +kernel
theorem triangle_complete_223 : ∀ c : Fin 103,
    (edge 223).2 < c → SeedEncoding.indexedAdj (edge 223).1 c →
    SeedEncoding.indexedAdj (edge 223).2 c →
      triangle (triangleIndex 223 c) = ((edge 223).1,(edge 223).2,c) := by decide +kernel
theorem triangle_complete_224 : ∀ c : Fin 103,
    (edge 224).2 < c → SeedEncoding.indexedAdj (edge 224).1 c →
    SeedEncoding.indexedAdj (edge 224).2 c →
      triangle (triangleIndex 224 c) = ((edge 224).1,(edge 224).2,c) := by decide +kernel
theorem triangle_complete_225 : ∀ c : Fin 103,
    (edge 225).2 < c → SeedEncoding.indexedAdj (edge 225).1 c →
    SeedEncoding.indexedAdj (edge 225).2 c →
      triangle (triangleIndex 225 c) = ((edge 225).1,(edge 225).2,c) := by decide +kernel
theorem triangle_complete_226 : ∀ c : Fin 103,
    (edge 226).2 < c → SeedEncoding.indexedAdj (edge 226).1 c →
    SeedEncoding.indexedAdj (edge 226).2 c →
      triangle (triangleIndex 226 c) = ((edge 226).1,(edge 226).2,c) := by decide +kernel
theorem triangle_complete_227 : ∀ c : Fin 103,
    (edge 227).2 < c → SeedEncoding.indexedAdj (edge 227).1 c →
    SeedEncoding.indexedAdj (edge 227).2 c →
      triangle (triangleIndex 227 c) = ((edge 227).1,(edge 227).2,c) := by decide +kernel
theorem triangle_complete_228 : ∀ c : Fin 103,
    (edge 228).2 < c → SeedEncoding.indexedAdj (edge 228).1 c →
    SeedEncoding.indexedAdj (edge 228).2 c →
      triangle (triangleIndex 228 c) = ((edge 228).1,(edge 228).2,c) := by decide +kernel
theorem triangle_complete_229 : ∀ c : Fin 103,
    (edge 229).2 < c → SeedEncoding.indexedAdj (edge 229).1 c →
    SeedEncoding.indexedAdj (edge 229).2 c →
      triangle (triangleIndex 229 c) = ((edge 229).1,(edge 229).2,c) := by decide +kernel
theorem triangle_complete_230 : ∀ c : Fin 103,
    (edge 230).2 < c → SeedEncoding.indexedAdj (edge 230).1 c →
    SeedEncoding.indexedAdj (edge 230).2 c →
      triangle (triangleIndex 230 c) = ((edge 230).1,(edge 230).2,c) := by decide +kernel
theorem triangle_complete_231 : ∀ c : Fin 103,
    (edge 231).2 < c → SeedEncoding.indexedAdj (edge 231).1 c →
    SeedEncoding.indexedAdj (edge 231).2 c →
      triangle (triangleIndex 231 c) = ((edge 231).1,(edge 231).2,c) := by decide +kernel
theorem triangle_complete_232 : ∀ c : Fin 103,
    (edge 232).2 < c → SeedEncoding.indexedAdj (edge 232).1 c →
    SeedEncoding.indexedAdj (edge 232).2 c →
      triangle (triangleIndex 232 c) = ((edge 232).1,(edge 232).2,c) := by decide +kernel
theorem triangle_complete_233 : ∀ c : Fin 103,
    (edge 233).2 < c → SeedEncoding.indexedAdj (edge 233).1 c →
    SeedEncoding.indexedAdj (edge 233).2 c →
      triangle (triangleIndex 233 c) = ((edge 233).1,(edge 233).2,c) := by decide +kernel
theorem triangle_complete_234 : ∀ c : Fin 103,
    (edge 234).2 < c → SeedEncoding.indexedAdj (edge 234).1 c →
    SeedEncoding.indexedAdj (edge 234).2 c →
      triangle (triangleIndex 234 c) = ((edge 234).1,(edge 234).2,c) := by decide +kernel
theorem triangle_complete_235 : ∀ c : Fin 103,
    (edge 235).2 < c → SeedEncoding.indexedAdj (edge 235).1 c →
    SeedEncoding.indexedAdj (edge 235).2 c →
      triangle (triangleIndex 235 c) = ((edge 235).1,(edge 235).2,c) := by decide +kernel
theorem triangle_complete_236 : ∀ c : Fin 103,
    (edge 236).2 < c → SeedEncoding.indexedAdj (edge 236).1 c →
    SeedEncoding.indexedAdj (edge 236).2 c →
      triangle (triangleIndex 236 c) = ((edge 236).1,(edge 236).2,c) := by decide +kernel
theorem triangle_complete_237 : ∀ c : Fin 103,
    (edge 237).2 < c → SeedEncoding.indexedAdj (edge 237).1 c →
    SeedEncoding.indexedAdj (edge 237).2 c →
      triangle (triangleIndex 237 c) = ((edge 237).1,(edge 237).2,c) := by decide +kernel
theorem triangle_complete_238 : ∀ c : Fin 103,
    (edge 238).2 < c → SeedEncoding.indexedAdj (edge 238).1 c →
    SeedEncoding.indexedAdj (edge 238).2 c →
      triangle (triangleIndex 238 c) = ((edge 238).1,(edge 238).2,c) := by decide +kernel
theorem triangle_complete_239 : ∀ c : Fin 103,
    (edge 239).2 < c → SeedEncoding.indexedAdj (edge 239).1 c →
    SeedEncoding.indexedAdj (edge 239).2 c →
      triangle (triangleIndex 239 c) = ((edge 239).1,(edge 239).2,c) := by decide +kernel
theorem triangle_complete_240 : ∀ c : Fin 103,
    (edge 240).2 < c → SeedEncoding.indexedAdj (edge 240).1 c →
    SeedEncoding.indexedAdj (edge 240).2 c →
      triangle (triangleIndex 240 c) = ((edge 240).1,(edge 240).2,c) := by decide +kernel
theorem triangle_complete_241 : ∀ c : Fin 103,
    (edge 241).2 < c → SeedEncoding.indexedAdj (edge 241).1 c →
    SeedEncoding.indexedAdj (edge 241).2 c →
      triangle (triangleIndex 241 c) = ((edge 241).1,(edge 241).2,c) := by decide +kernel
theorem triangle_complete_242 : ∀ c : Fin 103,
    (edge 242).2 < c → SeedEncoding.indexedAdj (edge 242).1 c →
    SeedEncoding.indexedAdj (edge 242).2 c →
      triangle (triangleIndex 242 c) = ((edge 242).1,(edge 242).2,c) := by decide +kernel
theorem triangle_complete_243 : ∀ c : Fin 103,
    (edge 243).2 < c → SeedEncoding.indexedAdj (edge 243).1 c →
    SeedEncoding.indexedAdj (edge 243).2 c →
      triangle (triangleIndex 243 c) = ((edge 243).1,(edge 243).2,c) := by decide +kernel
theorem triangle_complete_244 : ∀ c : Fin 103,
    (edge 244).2 < c → SeedEncoding.indexedAdj (edge 244).1 c →
    SeedEncoding.indexedAdj (edge 244).2 c →
      triangle (triangleIndex 244 c) = ((edge 244).1,(edge 244).2,c) := by decide +kernel
theorem triangle_complete_245 : ∀ c : Fin 103,
    (edge 245).2 < c → SeedEncoding.indexedAdj (edge 245).1 c →
    SeedEncoding.indexedAdj (edge 245).2 c →
      triangle (triangleIndex 245 c) = ((edge 245).1,(edge 245).2,c) := by decide +kernel
theorem triangle_complete_246 : ∀ c : Fin 103,
    (edge 246).2 < c → SeedEncoding.indexedAdj (edge 246).1 c →
    SeedEncoding.indexedAdj (edge 246).2 c →
      triangle (triangleIndex 246 c) = ((edge 246).1,(edge 246).2,c) := by decide +kernel
theorem triangle_complete_247 : ∀ c : Fin 103,
    (edge 247).2 < c → SeedEncoding.indexedAdj (edge 247).1 c →
    SeedEncoding.indexedAdj (edge 247).2 c →
      triangle (triangleIndex 247 c) = ((edge 247).1,(edge 247).2,c) := by decide +kernel
theorem triangle_complete_248 : ∀ c : Fin 103,
    (edge 248).2 < c → SeedEncoding.indexedAdj (edge 248).1 c →
    SeedEncoding.indexedAdj (edge 248).2 c →
      triangle (triangleIndex 248 c) = ((edge 248).1,(edge 248).2,c) := by decide +kernel
theorem triangle_complete_249 : ∀ c : Fin 103,
    (edge 249).2 < c → SeedEncoding.indexedAdj (edge 249).1 c →
    SeedEncoding.indexedAdj (edge 249).2 c →
      triangle (triangleIndex 249 c) = ((edge 249).1,(edge 249).2,c) := by decide +kernel
theorem triangle_complete_250 : ∀ c : Fin 103,
    (edge 250).2 < c → SeedEncoding.indexedAdj (edge 250).1 c →
    SeedEncoding.indexedAdj (edge 250).2 c →
      triangle (triangleIndex 250 c) = ((edge 250).1,(edge 250).2,c) := by decide +kernel
theorem triangle_complete_251 : ∀ c : Fin 103,
    (edge 251).2 < c → SeedEncoding.indexedAdj (edge 251).1 c →
    SeedEncoding.indexedAdj (edge 251).2 c →
      triangle (triangleIndex 251 c) = ((edge 251).1,(edge 251).2,c) := by decide +kernel
theorem triangle_complete_252 : ∀ c : Fin 103,
    (edge 252).2 < c → SeedEncoding.indexedAdj (edge 252).1 c →
    SeedEncoding.indexedAdj (edge 252).2 c →
      triangle (triangleIndex 252 c) = ((edge 252).1,(edge 252).2,c) := by decide +kernel
theorem triangle_complete_253 : ∀ c : Fin 103,
    (edge 253).2 < c → SeedEncoding.indexedAdj (edge 253).1 c →
    SeedEncoding.indexedAdj (edge 253).2 c →
      triangle (triangleIndex 253 c) = ((edge 253).1,(edge 253).2,c) := by decide +kernel
theorem triangle_complete_254 : ∀ c : Fin 103,
    (edge 254).2 < c → SeedEncoding.indexedAdj (edge 254).1 c →
    SeedEncoding.indexedAdj (edge 254).2 c →
      triangle (triangleIndex 254 c) = ((edge 254).1,(edge 254).2,c) := by decide +kernel
theorem triangle_complete_255 : ∀ c : Fin 103,
    (edge 255).2 < c → SeedEncoding.indexedAdj (edge 255).1 c →
    SeedEncoding.indexedAdj (edge 255).2 c →
      triangle (triangleIndex 255 c) = ((edge 255).1,(edge 255).2,c) := by decide +kernel
theorem triangle_complete_256 : ∀ c : Fin 103,
    (edge 256).2 < c → SeedEncoding.indexedAdj (edge 256).1 c →
    SeedEncoding.indexedAdj (edge 256).2 c →
      triangle (triangleIndex 256 c) = ((edge 256).1,(edge 256).2,c) := by decide +kernel
theorem triangle_complete_257 : ∀ c : Fin 103,
    (edge 257).2 < c → SeedEncoding.indexedAdj (edge 257).1 c →
    SeedEncoding.indexedAdj (edge 257).2 c →
      triangle (triangleIndex 257 c) = ((edge 257).1,(edge 257).2,c) := by decide +kernel
theorem triangle_complete_258 : ∀ c : Fin 103,
    (edge 258).2 < c → SeedEncoding.indexedAdj (edge 258).1 c →
    SeedEncoding.indexedAdj (edge 258).2 c →
      triangle (triangleIndex 258 c) = ((edge 258).1,(edge 258).2,c) := by decide +kernel
theorem triangle_complete_259 : ∀ c : Fin 103,
    (edge 259).2 < c → SeedEncoding.indexedAdj (edge 259).1 c →
    SeedEncoding.indexedAdj (edge 259).2 c →
      triangle (triangleIndex 259 c) = ((edge 259).1,(edge 259).2,c) := by decide +kernel
theorem triangle_complete_260 : ∀ c : Fin 103,
    (edge 260).2 < c → SeedEncoding.indexedAdj (edge 260).1 c →
    SeedEncoding.indexedAdj (edge 260).2 c →
      triangle (triangleIndex 260 c) = ((edge 260).1,(edge 260).2,c) := by decide +kernel
theorem triangle_complete_261 : ∀ c : Fin 103,
    (edge 261).2 < c → SeedEncoding.indexedAdj (edge 261).1 c →
    SeedEncoding.indexedAdj (edge 261).2 c →
      triangle (triangleIndex 261 c) = ((edge 261).1,(edge 261).2,c) := by decide +kernel
theorem triangle_complete_262 : ∀ c : Fin 103,
    (edge 262).2 < c → SeedEncoding.indexedAdj (edge 262).1 c →
    SeedEncoding.indexedAdj (edge 262).2 c →
      triangle (triangleIndex 262 c) = ((edge 262).1,(edge 262).2,c) := by decide +kernel
theorem triangle_complete_263 : ∀ c : Fin 103,
    (edge 263).2 < c → SeedEncoding.indexedAdj (edge 263).1 c →
    SeedEncoding.indexedAdj (edge 263).2 c →
      triangle (triangleIndex 263 c) = ((edge 263).1,(edge 263).2,c) := by decide +kernel
theorem triangle_complete_264 : ∀ c : Fin 103,
    (edge 264).2 < c → SeedEncoding.indexedAdj (edge 264).1 c →
    SeedEncoding.indexedAdj (edge 264).2 c →
      triangle (triangleIndex 264 c) = ((edge 264).1,(edge 264).2,c) := by decide +kernel
theorem triangle_complete_265 : ∀ c : Fin 103,
    (edge 265).2 < c → SeedEncoding.indexedAdj (edge 265).1 c →
    SeedEncoding.indexedAdj (edge 265).2 c →
      triangle (triangleIndex 265 c) = ((edge 265).1,(edge 265).2,c) := by decide +kernel
theorem triangle_complete_266 : ∀ c : Fin 103,
    (edge 266).2 < c → SeedEncoding.indexedAdj (edge 266).1 c →
    SeedEncoding.indexedAdj (edge 266).2 c →
      triangle (triangleIndex 266 c) = ((edge 266).1,(edge 266).2,c) := by decide +kernel
theorem triangle_complete_267 : ∀ c : Fin 103,
    (edge 267).2 < c → SeedEncoding.indexedAdj (edge 267).1 c →
    SeedEncoding.indexedAdj (edge 267).2 c →
      triangle (triangleIndex 267 c) = ((edge 267).1,(edge 267).2,c) := by decide +kernel
theorem triangle_complete_268 : ∀ c : Fin 103,
    (edge 268).2 < c → SeedEncoding.indexedAdj (edge 268).1 c →
    SeedEncoding.indexedAdj (edge 268).2 c →
      triangle (triangleIndex 268 c) = ((edge 268).1,(edge 268).2,c) := by decide +kernel
theorem triangle_complete_269 : ∀ c : Fin 103,
    (edge 269).2 < c → SeedEncoding.indexedAdj (edge 269).1 c →
    SeedEncoding.indexedAdj (edge 269).2 c →
      triangle (triangleIndex 269 c) = ((edge 269).1,(edge 269).2,c) := by decide +kernel
theorem triangle_complete_270 : ∀ c : Fin 103,
    (edge 270).2 < c → SeedEncoding.indexedAdj (edge 270).1 c →
    SeedEncoding.indexedAdj (edge 270).2 c →
      triangle (triangleIndex 270 c) = ((edge 270).1,(edge 270).2,c) := by decide +kernel
theorem triangle_complete_271 : ∀ c : Fin 103,
    (edge 271).2 < c → SeedEncoding.indexedAdj (edge 271).1 c →
    SeedEncoding.indexedAdj (edge 271).2 c →
      triangle (triangleIndex 271 c) = ((edge 271).1,(edge 271).2,c) := by decide +kernel
theorem triangle_complete_272 : ∀ c : Fin 103,
    (edge 272).2 < c → SeedEncoding.indexedAdj (edge 272).1 c →
    SeedEncoding.indexedAdj (edge 272).2 c →
      triangle (triangleIndex 272 c) = ((edge 272).1,(edge 272).2,c) := by decide +kernel
theorem triangle_complete_273 : ∀ c : Fin 103,
    (edge 273).2 < c → SeedEncoding.indexedAdj (edge 273).1 c →
    SeedEncoding.indexedAdj (edge 273).2 c →
      triangle (triangleIndex 273 c) = ((edge 273).1,(edge 273).2,c) := by decide +kernel
theorem triangle_complete_274 : ∀ c : Fin 103,
    (edge 274).2 < c → SeedEncoding.indexedAdj (edge 274).1 c →
    SeedEncoding.indexedAdj (edge 274).2 c →
      triangle (triangleIndex 274 c) = ((edge 274).1,(edge 274).2,c) := by decide +kernel
theorem triangle_complete_275 : ∀ c : Fin 103,
    (edge 275).2 < c → SeedEncoding.indexedAdj (edge 275).1 c →
    SeedEncoding.indexedAdj (edge 275).2 c →
      triangle (triangleIndex 275 c) = ((edge 275).1,(edge 275).2,c) := by decide +kernel
theorem triangle_complete_276 : ∀ c : Fin 103,
    (edge 276).2 < c → SeedEncoding.indexedAdj (edge 276).1 c →
    SeedEncoding.indexedAdj (edge 276).2 c →
      triangle (triangleIndex 276 c) = ((edge 276).1,(edge 276).2,c) := by decide +kernel
theorem triangle_complete_277 : ∀ c : Fin 103,
    (edge 277).2 < c → SeedEncoding.indexedAdj (edge 277).1 c →
    SeedEncoding.indexedAdj (edge 277).2 c →
      triangle (triangleIndex 277 c) = ((edge 277).1,(edge 277).2,c) := by decide +kernel
theorem triangle_complete_278 : ∀ c : Fin 103,
    (edge 278).2 < c → SeedEncoding.indexedAdj (edge 278).1 c →
    SeedEncoding.indexedAdj (edge 278).2 c →
      triangle (triangleIndex 278 c) = ((edge 278).1,(edge 278).2,c) := by decide +kernel
theorem triangle_complete_279 : ∀ c : Fin 103,
    (edge 279).2 < c → SeedEncoding.indexedAdj (edge 279).1 c →
    SeedEncoding.indexedAdj (edge 279).2 c →
      triangle (triangleIndex 279 c) = ((edge 279).1,(edge 279).2,c) := by decide +kernel
theorem triangle_complete_280 : ∀ c : Fin 103,
    (edge 280).2 < c → SeedEncoding.indexedAdj (edge 280).1 c →
    SeedEncoding.indexedAdj (edge 280).2 c →
      triangle (triangleIndex 280 c) = ((edge 280).1,(edge 280).2,c) := by decide +kernel
theorem triangle_complete_281 : ∀ c : Fin 103,
    (edge 281).2 < c → SeedEncoding.indexedAdj (edge 281).1 c →
    SeedEncoding.indexedAdj (edge 281).2 c →
      triangle (triangleIndex 281 c) = ((edge 281).1,(edge 281).2,c) := by decide +kernel
theorem triangle_complete_282 : ∀ c : Fin 103,
    (edge 282).2 < c → SeedEncoding.indexedAdj (edge 282).1 c →
    SeedEncoding.indexedAdj (edge 282).2 c →
      triangle (triangleIndex 282 c) = ((edge 282).1,(edge 282).2,c) := by decide +kernel
theorem triangle_complete_283 : ∀ c : Fin 103,
    (edge 283).2 < c → SeedEncoding.indexedAdj (edge 283).1 c →
    SeedEncoding.indexedAdj (edge 283).2 c →
      triangle (triangleIndex 283 c) = ((edge 283).1,(edge 283).2,c) := by decide +kernel
theorem triangle_complete_284 : ∀ c : Fin 103,
    (edge 284).2 < c → SeedEncoding.indexedAdj (edge 284).1 c →
    SeedEncoding.indexedAdj (edge 284).2 c →
      triangle (triangleIndex 284 c) = ((edge 284).1,(edge 284).2,c) := by decide +kernel
theorem triangle_complete_285 : ∀ c : Fin 103,
    (edge 285).2 < c → SeedEncoding.indexedAdj (edge 285).1 c →
    SeedEncoding.indexedAdj (edge 285).2 c →
      triangle (triangleIndex 285 c) = ((edge 285).1,(edge 285).2,c) := by decide +kernel
theorem triangle_complete_286 : ∀ c : Fin 103,
    (edge 286).2 < c → SeedEncoding.indexedAdj (edge 286).1 c →
    SeedEncoding.indexedAdj (edge 286).2 c →
      triangle (triangleIndex 286 c) = ((edge 286).1,(edge 286).2,c) := by decide +kernel
theorem triangle_complete_287 : ∀ c : Fin 103,
    (edge 287).2 < c → SeedEncoding.indexedAdj (edge 287).1 c →
    SeedEncoding.indexedAdj (edge 287).2 c →
      triangle (triangleIndex 287 c) = ((edge 287).1,(edge 287).2,c) := by decide +kernel
theorem triangle_complete_288 : ∀ c : Fin 103,
    (edge 288).2 < c → SeedEncoding.indexedAdj (edge 288).1 c →
    SeedEncoding.indexedAdj (edge 288).2 c →
      triangle (triangleIndex 288 c) = ((edge 288).1,(edge 288).2,c) := by decide +kernel
theorem triangle_complete_289 : ∀ c : Fin 103,
    (edge 289).2 < c → SeedEncoding.indexedAdj (edge 289).1 c →
    SeedEncoding.indexedAdj (edge 289).2 c →
      triangle (triangleIndex 289 c) = ((edge 289).1,(edge 289).2,c) := by decide +kernel
theorem triangle_complete_290 : ∀ c : Fin 103,
    (edge 290).2 < c → SeedEncoding.indexedAdj (edge 290).1 c →
    SeedEncoding.indexedAdj (edge 290).2 c →
      triangle (triangleIndex 290 c) = ((edge 290).1,(edge 290).2,c) := by decide +kernel
theorem triangle_complete_291 : ∀ c : Fin 103,
    (edge 291).2 < c → SeedEncoding.indexedAdj (edge 291).1 c →
    SeedEncoding.indexedAdj (edge 291).2 c →
      triangle (triangleIndex 291 c) = ((edge 291).1,(edge 291).2,c) := by decide +kernel
theorem triangle_complete_292 : ∀ c : Fin 103,
    (edge 292).2 < c → SeedEncoding.indexedAdj (edge 292).1 c →
    SeedEncoding.indexedAdj (edge 292).2 c →
      triangle (triangleIndex 292 c) = ((edge 292).1,(edge 292).2,c) := by decide +kernel
theorem triangle_complete_293 : ∀ c : Fin 103,
    (edge 293).2 < c → SeedEncoding.indexedAdj (edge 293).1 c →
    SeedEncoding.indexedAdj (edge 293).2 c →
      triangle (triangleIndex 293 c) = ((edge 293).1,(edge 293).2,c) := by decide +kernel
theorem triangle_complete_294 : ∀ c : Fin 103,
    (edge 294).2 < c → SeedEncoding.indexedAdj (edge 294).1 c →
    SeedEncoding.indexedAdj (edge 294).2 c →
      triangle (triangleIndex 294 c) = ((edge 294).1,(edge 294).2,c) := by decide +kernel
theorem triangle_complete_295 : ∀ c : Fin 103,
    (edge 295).2 < c → SeedEncoding.indexedAdj (edge 295).1 c →
    SeedEncoding.indexedAdj (edge 295).2 c →
      triangle (triangleIndex 295 c) = ((edge 295).1,(edge 295).2,c) := by decide +kernel
theorem triangle_complete_296 : ∀ c : Fin 103,
    (edge 296).2 < c → SeedEncoding.indexedAdj (edge 296).1 c →
    SeedEncoding.indexedAdj (edge 296).2 c →
      triangle (triangleIndex 296 c) = ((edge 296).1,(edge 296).2,c) := by decide +kernel
theorem triangle_complete_297 : ∀ c : Fin 103,
    (edge 297).2 < c → SeedEncoding.indexedAdj (edge 297).1 c →
    SeedEncoding.indexedAdj (edge 297).2 c →
      triangle (triangleIndex 297 c) = ((edge 297).1,(edge 297).2,c) := by decide +kernel
theorem triangle_complete_298 : ∀ c : Fin 103,
    (edge 298).2 < c → SeedEncoding.indexedAdj (edge 298).1 c →
    SeedEncoding.indexedAdj (edge 298).2 c →
      triangle (triangleIndex 298 c) = ((edge 298).1,(edge 298).2,c) := by decide +kernel
theorem triangle_complete_299 : ∀ c : Fin 103,
    (edge 299).2 < c → SeedEncoding.indexedAdj (edge 299).1 c →
    SeedEncoding.indexedAdj (edge 299).2 c →
      triangle (triangleIndex 299 c) = ((edge 299).1,(edge 299).2,c) := by decide +kernel
theorem triangle_complete_300 : ∀ c : Fin 103,
    (edge 300).2 < c → SeedEncoding.indexedAdj (edge 300).1 c →
    SeedEncoding.indexedAdj (edge 300).2 c →
      triangle (triangleIndex 300 c) = ((edge 300).1,(edge 300).2,c) := by decide +kernel
theorem triangle_complete_301 : ∀ c : Fin 103,
    (edge 301).2 < c → SeedEncoding.indexedAdj (edge 301).1 c →
    SeedEncoding.indexedAdj (edge 301).2 c →
      triangle (triangleIndex 301 c) = ((edge 301).1,(edge 301).2,c) := by decide +kernel
theorem triangle_complete_302 : ∀ c : Fin 103,
    (edge 302).2 < c → SeedEncoding.indexedAdj (edge 302).1 c →
    SeedEncoding.indexedAdj (edge 302).2 c →
      triangle (triangleIndex 302 c) = ((edge 302).1,(edge 302).2,c) := by decide +kernel
theorem triangle_complete_303 : ∀ c : Fin 103,
    (edge 303).2 < c → SeedEncoding.indexedAdj (edge 303).1 c →
    SeedEncoding.indexedAdj (edge 303).2 c →
      triangle (triangleIndex 303 c) = ((edge 303).1,(edge 303).2,c) := by decide +kernel
theorem triangle_complete_304 : ∀ c : Fin 103,
    (edge 304).2 < c → SeedEncoding.indexedAdj (edge 304).1 c →
    SeedEncoding.indexedAdj (edge 304).2 c →
      triangle (triangleIndex 304 c) = ((edge 304).1,(edge 304).2,c) := by decide +kernel
theorem triangle_complete_305 : ∀ c : Fin 103,
    (edge 305).2 < c → SeedEncoding.indexedAdj (edge 305).1 c →
    SeedEncoding.indexedAdj (edge 305).2 c →
      triangle (triangleIndex 305 c) = ((edge 305).1,(edge 305).2,c) := by decide +kernel
theorem triangle_complete_306 : ∀ c : Fin 103,
    (edge 306).2 < c → SeedEncoding.indexedAdj (edge 306).1 c →
    SeedEncoding.indexedAdj (edge 306).2 c →
      triangle (triangleIndex 306 c) = ((edge 306).1,(edge 306).2,c) := by decide +kernel
theorem triangle_complete_307 : ∀ c : Fin 103,
    (edge 307).2 < c → SeedEncoding.indexedAdj (edge 307).1 c →
    SeedEncoding.indexedAdj (edge 307).2 c →
      triangle (triangleIndex 307 c) = ((edge 307).1,(edge 307).2,c) := by decide +kernel
theorem triangle_complete_308 : ∀ c : Fin 103,
    (edge 308).2 < c → SeedEncoding.indexedAdj (edge 308).1 c →
    SeedEncoding.indexedAdj (edge 308).2 c →
      triangle (triangleIndex 308 c) = ((edge 308).1,(edge 308).2,c) := by decide +kernel
theorem triangle_complete_309 : ∀ c : Fin 103,
    (edge 309).2 < c → SeedEncoding.indexedAdj (edge 309).1 c →
    SeedEncoding.indexedAdj (edge 309).2 c →
      triangle (triangleIndex 309 c) = ((edge 309).1,(edge 309).2,c) := by decide +kernel
theorem triangle_complete_310 : ∀ c : Fin 103,
    (edge 310).2 < c → SeedEncoding.indexedAdj (edge 310).1 c →
    SeedEncoding.indexedAdj (edge 310).2 c →
      triangle (triangleIndex 310 c) = ((edge 310).1,(edge 310).2,c) := by decide +kernel
theorem triangle_complete_311 : ∀ c : Fin 103,
    (edge 311).2 < c → SeedEncoding.indexedAdj (edge 311).1 c →
    SeedEncoding.indexedAdj (edge 311).2 c →
      triangle (triangleIndex 311 c) = ((edge 311).1,(edge 311).2,c) := by decide +kernel
theorem triangle_complete_312 : ∀ c : Fin 103,
    (edge 312).2 < c → SeedEncoding.indexedAdj (edge 312).1 c →
    SeedEncoding.indexedAdj (edge 312).2 c →
      triangle (triangleIndex 312 c) = ((edge 312).1,(edge 312).2,c) := by decide +kernel
theorem triangle_complete_313 : ∀ c : Fin 103,
    (edge 313).2 < c → SeedEncoding.indexedAdj (edge 313).1 c →
    SeedEncoding.indexedAdj (edge 313).2 c →
      triangle (triangleIndex 313 c) = ((edge 313).1,(edge 313).2,c) := by decide +kernel
theorem triangle_complete_314 : ∀ c : Fin 103,
    (edge 314).2 < c → SeedEncoding.indexedAdj (edge 314).1 c →
    SeedEncoding.indexedAdj (edge 314).2 c →
      triangle (triangleIndex 314 c) = ((edge 314).1,(edge 314).2,c) := by decide +kernel
theorem triangle_complete_315 : ∀ c : Fin 103,
    (edge 315).2 < c → SeedEncoding.indexedAdj (edge 315).1 c →
    SeedEncoding.indexedAdj (edge 315).2 c →
      triangle (triangleIndex 315 c) = ((edge 315).1,(edge 315).2,c) := by decide +kernel
theorem triangle_complete_316 : ∀ c : Fin 103,
    (edge 316).2 < c → SeedEncoding.indexedAdj (edge 316).1 c →
    SeedEncoding.indexedAdj (edge 316).2 c →
      triangle (triangleIndex 316 c) = ((edge 316).1,(edge 316).2,c) := by decide +kernel
theorem triangle_complete_317 : ∀ c : Fin 103,
    (edge 317).2 < c → SeedEncoding.indexedAdj (edge 317).1 c →
    SeedEncoding.indexedAdj (edge 317).2 c →
      triangle (triangleIndex 317 c) = ((edge 317).1,(edge 317).2,c) := by decide +kernel
theorem triangle_complete_318 : ∀ c : Fin 103,
    (edge 318).2 < c → SeedEncoding.indexedAdj (edge 318).1 c →
    SeedEncoding.indexedAdj (edge 318).2 c →
      triangle (triangleIndex 318 c) = ((edge 318).1,(edge 318).2,c) := by decide +kernel
theorem triangle_complete_319 : ∀ c : Fin 103,
    (edge 319).2 < c → SeedEncoding.indexedAdj (edge 319).1 c →
    SeedEncoding.indexedAdj (edge 319).2 c →
      triangle (triangleIndex 319 c) = ((edge 319).1,(edge 319).2,c) := by decide +kernel
theorem triangle_complete_320 : ∀ c : Fin 103,
    (edge 320).2 < c → SeedEncoding.indexedAdj (edge 320).1 c →
    SeedEncoding.indexedAdj (edge 320).2 c →
      triangle (triangleIndex 320 c) = ((edge 320).1,(edge 320).2,c) := by decide +kernel
theorem triangle_complete_321 : ∀ c : Fin 103,
    (edge 321).2 < c → SeedEncoding.indexedAdj (edge 321).1 c →
    SeedEncoding.indexedAdj (edge 321).2 c →
      triangle (triangleIndex 321 c) = ((edge 321).1,(edge 321).2,c) := by decide +kernel
theorem triangle_complete_322 : ∀ c : Fin 103,
    (edge 322).2 < c → SeedEncoding.indexedAdj (edge 322).1 c →
    SeedEncoding.indexedAdj (edge 322).2 c →
      triangle (triangleIndex 322 c) = ((edge 322).1,(edge 322).2,c) := by decide +kernel
theorem triangle_complete_323 : ∀ c : Fin 103,
    (edge 323).2 < c → SeedEncoding.indexedAdj (edge 323).1 c →
    SeedEncoding.indexedAdj (edge 323).2 c →
      triangle (triangleIndex 323 c) = ((edge 323).1,(edge 323).2,c) := by decide +kernel
theorem triangle_complete_324 : ∀ c : Fin 103,
    (edge 324).2 < c → SeedEncoding.indexedAdj (edge 324).1 c →
    SeedEncoding.indexedAdj (edge 324).2 c →
      triangle (triangleIndex 324 c) = ((edge 324).1,(edge 324).2,c) := by decide +kernel
theorem triangle_complete_325 : ∀ c : Fin 103,
    (edge 325).2 < c → SeedEncoding.indexedAdj (edge 325).1 c →
    SeedEncoding.indexedAdj (edge 325).2 c →
      triangle (triangleIndex 325 c) = ((edge 325).1,(edge 325).2,c) := by decide +kernel
theorem triangle_complete_326 : ∀ c : Fin 103,
    (edge 326).2 < c → SeedEncoding.indexedAdj (edge 326).1 c →
    SeedEncoding.indexedAdj (edge 326).2 c →
      triangle (triangleIndex 326 c) = ((edge 326).1,(edge 326).2,c) := by decide +kernel
theorem triangle_complete_327 : ∀ c : Fin 103,
    (edge 327).2 < c → SeedEncoding.indexedAdj (edge 327).1 c →
    SeedEncoding.indexedAdj (edge 327).2 c →
      triangle (triangleIndex 327 c) = ((edge 327).1,(edge 327).2,c) := by decide +kernel
theorem triangle_complete_328 : ∀ c : Fin 103,
    (edge 328).2 < c → SeedEncoding.indexedAdj (edge 328).1 c →
    SeedEncoding.indexedAdj (edge 328).2 c →
      triangle (triangleIndex 328 c) = ((edge 328).1,(edge 328).2,c) := by decide +kernel
theorem triangle_complete_329 : ∀ c : Fin 103,
    (edge 329).2 < c → SeedEncoding.indexedAdj (edge 329).1 c →
    SeedEncoding.indexedAdj (edge 329).2 c →
      triangle (triangleIndex 329 c) = ((edge 329).1,(edge 329).2,c) := by decide +kernel
theorem triangle_complete_330 : ∀ c : Fin 103,
    (edge 330).2 < c → SeedEncoding.indexedAdj (edge 330).1 c →
    SeedEncoding.indexedAdj (edge 330).2 c →
      triangle (triangleIndex 330 c) = ((edge 330).1,(edge 330).2,c) := by decide +kernel
theorem triangle_complete_331 : ∀ c : Fin 103,
    (edge 331).2 < c → SeedEncoding.indexedAdj (edge 331).1 c →
    SeedEncoding.indexedAdj (edge 331).2 c →
      triangle (triangleIndex 331 c) = ((edge 331).1,(edge 331).2,c) := by decide +kernel
theorem triangle_complete_332 : ∀ c : Fin 103,
    (edge 332).2 < c → SeedEncoding.indexedAdj (edge 332).1 c →
    SeedEncoding.indexedAdj (edge 332).2 c →
      triangle (triangleIndex 332 c) = ((edge 332).1,(edge 332).2,c) := by decide +kernel
theorem triangle_complete_333 : ∀ c : Fin 103,
    (edge 333).2 < c → SeedEncoding.indexedAdj (edge 333).1 c →
    SeedEncoding.indexedAdj (edge 333).2 c →
      triangle (triangleIndex 333 c) = ((edge 333).1,(edge 333).2,c) := by decide +kernel
theorem triangle_complete_334 : ∀ c : Fin 103,
    (edge 334).2 < c → SeedEncoding.indexedAdj (edge 334).1 c →
    SeedEncoding.indexedAdj (edge 334).2 c →
      triangle (triangleIndex 334 c) = ((edge 334).1,(edge 334).2,c) := by decide +kernel
theorem triangle_complete_335 : ∀ c : Fin 103,
    (edge 335).2 < c → SeedEncoding.indexedAdj (edge 335).1 c →
    SeedEncoding.indexedAdj (edge 335).2 c →
      triangle (triangleIndex 335 c) = ((edge 335).1,(edge 335).2,c) := by decide +kernel
theorem triangle_complete_336 : ∀ c : Fin 103,
    (edge 336).2 < c → SeedEncoding.indexedAdj (edge 336).1 c →
    SeedEncoding.indexedAdj (edge 336).2 c →
      triangle (triangleIndex 336 c) = ((edge 336).1,(edge 336).2,c) := by decide +kernel
theorem triangle_complete_337 : ∀ c : Fin 103,
    (edge 337).2 < c → SeedEncoding.indexedAdj (edge 337).1 c →
    SeedEncoding.indexedAdj (edge 337).2 c →
      triangle (triangleIndex 337 c) = ((edge 337).1,(edge 337).2,c) := by decide +kernel
theorem triangle_complete_338 : ∀ c : Fin 103,
    (edge 338).2 < c → SeedEncoding.indexedAdj (edge 338).1 c →
    SeedEncoding.indexedAdj (edge 338).2 c →
      triangle (triangleIndex 338 c) = ((edge 338).1,(edge 338).2,c) := by decide +kernel
theorem triangle_complete_339 : ∀ c : Fin 103,
    (edge 339).2 < c → SeedEncoding.indexedAdj (edge 339).1 c →
    SeedEncoding.indexedAdj (edge 339).2 c →
      triangle (triangleIndex 339 c) = ((edge 339).1,(edge 339).2,c) := by decide +kernel
theorem triangle_complete_340 : ∀ c : Fin 103,
    (edge 340).2 < c → SeedEncoding.indexedAdj (edge 340).1 c →
    SeedEncoding.indexedAdj (edge 340).2 c →
      triangle (triangleIndex 340 c) = ((edge 340).1,(edge 340).2,c) := by decide +kernel
theorem triangle_complete_341 : ∀ c : Fin 103,
    (edge 341).2 < c → SeedEncoding.indexedAdj (edge 341).1 c →
    SeedEncoding.indexedAdj (edge 341).2 c →
      triangle (triangleIndex 341 c) = ((edge 341).1,(edge 341).2,c) := by decide +kernel
theorem triangle_complete_342 : ∀ c : Fin 103,
    (edge 342).2 < c → SeedEncoding.indexedAdj (edge 342).1 c →
    SeedEncoding.indexedAdj (edge 342).2 c →
      triangle (triangleIndex 342 c) = ((edge 342).1,(edge 342).2,c) := by decide +kernel
theorem triangle_complete_343 : ∀ c : Fin 103,
    (edge 343).2 < c → SeedEncoding.indexedAdj (edge 343).1 c →
    SeedEncoding.indexedAdj (edge 343).2 c →
      triangle (triangleIndex 343 c) = ((edge 343).1,(edge 343).2,c) := by decide +kernel
theorem triangle_complete_344 : ∀ c : Fin 103,
    (edge 344).2 < c → SeedEncoding.indexedAdj (edge 344).1 c →
    SeedEncoding.indexedAdj (edge 344).2 c →
      triangle (triangleIndex 344 c) = ((edge 344).1,(edge 344).2,c) := by decide +kernel
theorem triangle_complete_345 : ∀ c : Fin 103,
    (edge 345).2 < c → SeedEncoding.indexedAdj (edge 345).1 c →
    SeedEncoding.indexedAdj (edge 345).2 c →
      triangle (triangleIndex 345 c) = ((edge 345).1,(edge 345).2,c) := by decide +kernel
theorem triangle_complete_346 : ∀ c : Fin 103,
    (edge 346).2 < c → SeedEncoding.indexedAdj (edge 346).1 c →
    SeedEncoding.indexedAdj (edge 346).2 c →
      triangle (triangleIndex 346 c) = ((edge 346).1,(edge 346).2,c) := by decide +kernel
theorem triangle_complete_347 : ∀ c : Fin 103,
    (edge 347).2 < c → SeedEncoding.indexedAdj (edge 347).1 c →
    SeedEncoding.indexedAdj (edge 347).2 c →
      triangle (triangleIndex 347 c) = ((edge 347).1,(edge 347).2,c) := by decide +kernel
theorem triangle_complete_348 : ∀ c : Fin 103,
    (edge 348).2 < c → SeedEncoding.indexedAdj (edge 348).1 c →
    SeedEncoding.indexedAdj (edge 348).2 c →
      triangle (triangleIndex 348 c) = ((edge 348).1,(edge 348).2,c) := by decide +kernel
theorem triangle_complete_349 : ∀ c : Fin 103,
    (edge 349).2 < c → SeedEncoding.indexedAdj (edge 349).1 c →
    SeedEncoding.indexedAdj (edge 349).2 c →
      triangle (triangleIndex 349 c) = ((edge 349).1,(edge 349).2,c) := by decide +kernel
theorem triangle_complete_350 : ∀ c : Fin 103,
    (edge 350).2 < c → SeedEncoding.indexedAdj (edge 350).1 c →
    SeedEncoding.indexedAdj (edge 350).2 c →
      triangle (triangleIndex 350 c) = ((edge 350).1,(edge 350).2,c) := by decide +kernel
theorem triangle_complete_351 : ∀ c : Fin 103,
    (edge 351).2 < c → SeedEncoding.indexedAdj (edge 351).1 c →
    SeedEncoding.indexedAdj (edge 351).2 c →
      triangle (triangleIndex 351 c) = ((edge 351).1,(edge 351).2,c) := by decide +kernel
theorem triangle_complete_352 : ∀ c : Fin 103,
    (edge 352).2 < c → SeedEncoding.indexedAdj (edge 352).1 c →
    SeedEncoding.indexedAdj (edge 352).2 c →
      triangle (triangleIndex 352 c) = ((edge 352).1,(edge 352).2,c) := by decide +kernel
theorem triangle_complete_353 : ∀ c : Fin 103,
    (edge 353).2 < c → SeedEncoding.indexedAdj (edge 353).1 c →
    SeedEncoding.indexedAdj (edge 353).2 c →
      triangle (triangleIndex 353 c) = ((edge 353).1,(edge 353).2,c) := by decide +kernel
theorem triangle_complete_354 : ∀ c : Fin 103,
    (edge 354).2 < c → SeedEncoding.indexedAdj (edge 354).1 c →
    SeedEncoding.indexedAdj (edge 354).2 c →
      triangle (triangleIndex 354 c) = ((edge 354).1,(edge 354).2,c) := by decide +kernel
theorem triangle_complete_355 : ∀ c : Fin 103,
    (edge 355).2 < c → SeedEncoding.indexedAdj (edge 355).1 c →
    SeedEncoding.indexedAdj (edge 355).2 c →
      triangle (triangleIndex 355 c) = ((edge 355).1,(edge 355).2,c) := by decide +kernel
theorem triangle_complete_356 : ∀ c : Fin 103,
    (edge 356).2 < c → SeedEncoding.indexedAdj (edge 356).1 c →
    SeedEncoding.indexedAdj (edge 356).2 c →
      triangle (triangleIndex 356 c) = ((edge 356).1,(edge 356).2,c) := by decide +kernel
theorem triangle_complete_357 : ∀ c : Fin 103,
    (edge 357).2 < c → SeedEncoding.indexedAdj (edge 357).1 c →
    SeedEncoding.indexedAdj (edge 357).2 c →
      triangle (triangleIndex 357 c) = ((edge 357).1,(edge 357).2,c) := by decide +kernel
theorem triangle_complete_358 : ∀ c : Fin 103,
    (edge 358).2 < c → SeedEncoding.indexedAdj (edge 358).1 c →
    SeedEncoding.indexedAdj (edge 358).2 c →
      triangle (triangleIndex 358 c) = ((edge 358).1,(edge 358).2,c) := by decide +kernel
theorem triangle_complete_359 : ∀ c : Fin 103,
    (edge 359).2 < c → SeedEncoding.indexedAdj (edge 359).1 c →
    SeedEncoding.indexedAdj (edge 359).2 c →
      triangle (triangleIndex 359 c) = ((edge 359).1,(edge 359).2,c) := by decide +kernel
theorem triangle_complete_360 : ∀ c : Fin 103,
    (edge 360).2 < c → SeedEncoding.indexedAdj (edge 360).1 c →
    SeedEncoding.indexedAdj (edge 360).2 c →
      triangle (triangleIndex 360 c) = ((edge 360).1,(edge 360).2,c) := by decide +kernel
theorem triangle_complete_361 : ∀ c : Fin 103,
    (edge 361).2 < c → SeedEncoding.indexedAdj (edge 361).1 c →
    SeedEncoding.indexedAdj (edge 361).2 c →
      triangle (triangleIndex 361 c) = ((edge 361).1,(edge 361).2,c) := by decide +kernel
theorem triangle_complete_362 : ∀ c : Fin 103,
    (edge 362).2 < c → SeedEncoding.indexedAdj (edge 362).1 c →
    SeedEncoding.indexedAdj (edge 362).2 c →
      triangle (triangleIndex 362 c) = ((edge 362).1,(edge 362).2,c) := by decide +kernel
theorem triangle_complete_363 : ∀ c : Fin 103,
    (edge 363).2 < c → SeedEncoding.indexedAdj (edge 363).1 c →
    SeedEncoding.indexedAdj (edge 363).2 c →
      triangle (triangleIndex 363 c) = ((edge 363).1,(edge 363).2,c) := by decide +kernel
theorem triangle_complete_364 : ∀ c : Fin 103,
    (edge 364).2 < c → SeedEncoding.indexedAdj (edge 364).1 c →
    SeedEncoding.indexedAdj (edge 364).2 c →
      triangle (triangleIndex 364 c) = ((edge 364).1,(edge 364).2,c) := by decide +kernel
theorem triangle_complete_365 : ∀ c : Fin 103,
    (edge 365).2 < c → SeedEncoding.indexedAdj (edge 365).1 c →
    SeedEncoding.indexedAdj (edge 365).2 c →
      triangle (triangleIndex 365 c) = ((edge 365).1,(edge 365).2,c) := by decide +kernel
theorem triangle_complete_366 : ∀ c : Fin 103,
    (edge 366).2 < c → SeedEncoding.indexedAdj (edge 366).1 c →
    SeedEncoding.indexedAdj (edge 366).2 c →
      triangle (triangleIndex 366 c) = ((edge 366).1,(edge 366).2,c) := by decide +kernel
theorem triangle_complete_367 : ∀ c : Fin 103,
    (edge 367).2 < c → SeedEncoding.indexedAdj (edge 367).1 c →
    SeedEncoding.indexedAdj (edge 367).2 c →
      triangle (triangleIndex 367 c) = ((edge 367).1,(edge 367).2,c) := by decide +kernel
theorem triangle_complete_368 : ∀ c : Fin 103,
    (edge 368).2 < c → SeedEncoding.indexedAdj (edge 368).1 c →
    SeedEncoding.indexedAdj (edge 368).2 c →
      triangle (triangleIndex 368 c) = ((edge 368).1,(edge 368).2,c) := by decide +kernel
theorem triangle_complete_369 : ∀ c : Fin 103,
    (edge 369).2 < c → SeedEncoding.indexedAdj (edge 369).1 c →
    SeedEncoding.indexedAdj (edge 369).2 c →
      triangle (triangleIndex 369 c) = ((edge 369).1,(edge 369).2,c) := by decide +kernel
theorem triangle_complete_370 : ∀ c : Fin 103,
    (edge 370).2 < c → SeedEncoding.indexedAdj (edge 370).1 c →
    SeedEncoding.indexedAdj (edge 370).2 c →
      triangle (triangleIndex 370 c) = ((edge 370).1,(edge 370).2,c) := by decide +kernel
theorem triangle_complete_371 : ∀ c : Fin 103,
    (edge 371).2 < c → SeedEncoding.indexedAdj (edge 371).1 c →
    SeedEncoding.indexedAdj (edge 371).2 c →
      triangle (triangleIndex 371 c) = ((edge 371).1,(edge 371).2,c) := by decide +kernel
theorem edge_valid : ∀ e : Fin 372,
    (edge e).1 < (edge e).2 ∧ SeedEncoding.indexedAdj (edge e).1 (edge e).2 := by decide +kernel

theorem edge_index_inverse : ∀ e : Fin 372, edgeIndex (edge e).1 (edge e).2 = e := by decide +kernel

theorem triangle_valid : ∀ t : Fin 270,
    (triangle t).1 < (triangle t).2.1 ∧ (triangle t).2.1 < (triangle t).2.2 ∧
    SeedEncoding.indexedAdj (triangle t).1 (triangle t).2.1 ∧
    SeedEncoding.indexedAdj (triangle t).1 (triangle t).2.2 ∧
    SeedEncoding.indexedAdj (triangle t).2.1 (triangle t).2.2 := by decide +kernel

theorem edge_complete (a b : Fin 103) : a < b → SeedEncoding.indexedAdj a b →
    edge (edgeIndex a b) = (a,b) := by
  fin_cases a
  · exact edge_complete_0 b
  · exact edge_complete_1 b
  · exact edge_complete_2 b
  · exact edge_complete_3 b
  · exact edge_complete_4 b
  · exact edge_complete_5 b
  · exact edge_complete_6 b
  · exact edge_complete_7 b
  · exact edge_complete_8 b
  · exact edge_complete_9 b
  · exact edge_complete_10 b
  · exact edge_complete_11 b
  · exact edge_complete_12 b
  · exact edge_complete_13 b
  · exact edge_complete_14 b
  · exact edge_complete_15 b
  · exact edge_complete_16 b
  · exact edge_complete_17 b
  · exact edge_complete_18 b
  · exact edge_complete_19 b
  · exact edge_complete_20 b
  · exact edge_complete_21 b
  · exact edge_complete_22 b
  · exact edge_complete_23 b
  · exact edge_complete_24 b
  · exact edge_complete_25 b
  · exact edge_complete_26 b
  · exact edge_complete_27 b
  · exact edge_complete_28 b
  · exact edge_complete_29 b
  · exact edge_complete_30 b
  · exact edge_complete_31 b
  · exact edge_complete_32 b
  · exact edge_complete_33 b
  · exact edge_complete_34 b
  · exact edge_complete_35 b
  · exact edge_complete_36 b
  · exact edge_complete_37 b
  · exact edge_complete_38 b
  · exact edge_complete_39 b
  · exact edge_complete_40 b
  · exact edge_complete_41 b
  · exact edge_complete_42 b
  · exact edge_complete_43 b
  · exact edge_complete_44 b
  · exact edge_complete_45 b
  · exact edge_complete_46 b
  · exact edge_complete_47 b
  · exact edge_complete_48 b
  · exact edge_complete_49 b
  · exact edge_complete_50 b
  · exact edge_complete_51 b
  · exact edge_complete_52 b
  · exact edge_complete_53 b
  · exact edge_complete_54 b
  · exact edge_complete_55 b
  · exact edge_complete_56 b
  · exact edge_complete_57 b
  · exact edge_complete_58 b
  · exact edge_complete_59 b
  · exact edge_complete_60 b
  · exact edge_complete_61 b
  · exact edge_complete_62 b
  · exact edge_complete_63 b
  · exact edge_complete_64 b
  · exact edge_complete_65 b
  · exact edge_complete_66 b
  · exact edge_complete_67 b
  · exact edge_complete_68 b
  · exact edge_complete_69 b
  · exact edge_complete_70 b
  · exact edge_complete_71 b
  · exact edge_complete_72 b
  · exact edge_complete_73 b
  · exact edge_complete_74 b
  · exact edge_complete_75 b
  · exact edge_complete_76 b
  · exact edge_complete_77 b
  · exact edge_complete_78 b
  · exact edge_complete_79 b
  · exact edge_complete_80 b
  · exact edge_complete_81 b
  · exact edge_complete_82 b
  · exact edge_complete_83 b
  · exact edge_complete_84 b
  · exact edge_complete_85 b
  · exact edge_complete_86 b
  · exact edge_complete_87 b
  · exact edge_complete_88 b
  · exact edge_complete_89 b
  · exact edge_complete_90 b
  · exact edge_complete_91 b
  · exact edge_complete_92 b
  · exact edge_complete_93 b
  · exact edge_complete_94 b
  · exact edge_complete_95 b
  · exact edge_complete_96 b
  · exact edge_complete_97 b
  · exact edge_complete_98 b
  · exact edge_complete_99 b
  · exact edge_complete_100 b
  · exact edge_complete_101 b
  · exact edge_complete_102 b
theorem triangle_complete (e : Fin 372) (c : Fin 103) :
    (edge e).2 < c → SeedEncoding.indexedAdj (edge e).1 c →
    SeedEncoding.indexedAdj (edge e).2 c →
      triangle (triangleIndex e c) = ((edge e).1,(edge e).2,c) := by
  fin_cases e
  · exact triangle_complete_0 c
  · exact triangle_complete_1 c
  · exact triangle_complete_2 c
  · exact triangle_complete_3 c
  · exact triangle_complete_4 c
  · exact triangle_complete_5 c
  · exact triangle_complete_6 c
  · exact triangle_complete_7 c
  · exact triangle_complete_8 c
  · exact triangle_complete_9 c
  · exact triangle_complete_10 c
  · exact triangle_complete_11 c
  · exact triangle_complete_12 c
  · exact triangle_complete_13 c
  · exact triangle_complete_14 c
  · exact triangle_complete_15 c
  · exact triangle_complete_16 c
  · exact triangle_complete_17 c
  · exact triangle_complete_18 c
  · exact triangle_complete_19 c
  · exact triangle_complete_20 c
  · exact triangle_complete_21 c
  · exact triangle_complete_22 c
  · exact triangle_complete_23 c
  · exact triangle_complete_24 c
  · exact triangle_complete_25 c
  · exact triangle_complete_26 c
  · exact triangle_complete_27 c
  · exact triangle_complete_28 c
  · exact triangle_complete_29 c
  · exact triangle_complete_30 c
  · exact triangle_complete_31 c
  · exact triangle_complete_32 c
  · exact triangle_complete_33 c
  · exact triangle_complete_34 c
  · exact triangle_complete_35 c
  · exact triangle_complete_36 c
  · exact triangle_complete_37 c
  · exact triangle_complete_38 c
  · exact triangle_complete_39 c
  · exact triangle_complete_40 c
  · exact triangle_complete_41 c
  · exact triangle_complete_42 c
  · exact triangle_complete_43 c
  · exact triangle_complete_44 c
  · exact triangle_complete_45 c
  · exact triangle_complete_46 c
  · exact triangle_complete_47 c
  · exact triangle_complete_48 c
  · exact triangle_complete_49 c
  · exact triangle_complete_50 c
  · exact triangle_complete_51 c
  · exact triangle_complete_52 c
  · exact triangle_complete_53 c
  · exact triangle_complete_54 c
  · exact triangle_complete_55 c
  · exact triangle_complete_56 c
  · exact triangle_complete_57 c
  · exact triangle_complete_58 c
  · exact triangle_complete_59 c
  · exact triangle_complete_60 c
  · exact triangle_complete_61 c
  · exact triangle_complete_62 c
  · exact triangle_complete_63 c
  · exact triangle_complete_64 c
  · exact triangle_complete_65 c
  · exact triangle_complete_66 c
  · exact triangle_complete_67 c
  · exact triangle_complete_68 c
  · exact triangle_complete_69 c
  · exact triangle_complete_70 c
  · exact triangle_complete_71 c
  · exact triangle_complete_72 c
  · exact triangle_complete_73 c
  · exact triangle_complete_74 c
  · exact triangle_complete_75 c
  · exact triangle_complete_76 c
  · exact triangle_complete_77 c
  · exact triangle_complete_78 c
  · exact triangle_complete_79 c
  · exact triangle_complete_80 c
  · exact triangle_complete_81 c
  · exact triangle_complete_82 c
  · exact triangle_complete_83 c
  · exact triangle_complete_84 c
  · exact triangle_complete_85 c
  · exact triangle_complete_86 c
  · exact triangle_complete_87 c
  · exact triangle_complete_88 c
  · exact triangle_complete_89 c
  · exact triangle_complete_90 c
  · exact triangle_complete_91 c
  · exact triangle_complete_92 c
  · exact triangle_complete_93 c
  · exact triangle_complete_94 c
  · exact triangle_complete_95 c
  · exact triangle_complete_96 c
  · exact triangle_complete_97 c
  · exact triangle_complete_98 c
  · exact triangle_complete_99 c
  · exact triangle_complete_100 c
  · exact triangle_complete_101 c
  · exact triangle_complete_102 c
  · exact triangle_complete_103 c
  · exact triangle_complete_104 c
  · exact triangle_complete_105 c
  · exact triangle_complete_106 c
  · exact triangle_complete_107 c
  · exact triangle_complete_108 c
  · exact triangle_complete_109 c
  · exact triangle_complete_110 c
  · exact triangle_complete_111 c
  · exact triangle_complete_112 c
  · exact triangle_complete_113 c
  · exact triangle_complete_114 c
  · exact triangle_complete_115 c
  · exact triangle_complete_116 c
  · exact triangle_complete_117 c
  · exact triangle_complete_118 c
  · exact triangle_complete_119 c
  · exact triangle_complete_120 c
  · exact triangle_complete_121 c
  · exact triangle_complete_122 c
  · exact triangle_complete_123 c
  · exact triangle_complete_124 c
  · exact triangle_complete_125 c
  · exact triangle_complete_126 c
  · exact triangle_complete_127 c
  · exact triangle_complete_128 c
  · exact triangle_complete_129 c
  · exact triangle_complete_130 c
  · exact triangle_complete_131 c
  · exact triangle_complete_132 c
  · exact triangle_complete_133 c
  · exact triangle_complete_134 c
  · exact triangle_complete_135 c
  · exact triangle_complete_136 c
  · exact triangle_complete_137 c
  · exact triangle_complete_138 c
  · exact triangle_complete_139 c
  · exact triangle_complete_140 c
  · exact triangle_complete_141 c
  · exact triangle_complete_142 c
  · exact triangle_complete_143 c
  · exact triangle_complete_144 c
  · exact triangle_complete_145 c
  · exact triangle_complete_146 c
  · exact triangle_complete_147 c
  · exact triangle_complete_148 c
  · exact triangle_complete_149 c
  · exact triangle_complete_150 c
  · exact triangle_complete_151 c
  · exact triangle_complete_152 c
  · exact triangle_complete_153 c
  · exact triangle_complete_154 c
  · exact triangle_complete_155 c
  · exact triangle_complete_156 c
  · exact triangle_complete_157 c
  · exact triangle_complete_158 c
  · exact triangle_complete_159 c
  · exact triangle_complete_160 c
  · exact triangle_complete_161 c
  · exact triangle_complete_162 c
  · exact triangle_complete_163 c
  · exact triangle_complete_164 c
  · exact triangle_complete_165 c
  · exact triangle_complete_166 c
  · exact triangle_complete_167 c
  · exact triangle_complete_168 c
  · exact triangle_complete_169 c
  · exact triangle_complete_170 c
  · exact triangle_complete_171 c
  · exact triangle_complete_172 c
  · exact triangle_complete_173 c
  · exact triangle_complete_174 c
  · exact triangle_complete_175 c
  · exact triangle_complete_176 c
  · exact triangle_complete_177 c
  · exact triangle_complete_178 c
  · exact triangle_complete_179 c
  · exact triangle_complete_180 c
  · exact triangle_complete_181 c
  · exact triangle_complete_182 c
  · exact triangle_complete_183 c
  · exact triangle_complete_184 c
  · exact triangle_complete_185 c
  · exact triangle_complete_186 c
  · exact triangle_complete_187 c
  · exact triangle_complete_188 c
  · exact triangle_complete_189 c
  · exact triangle_complete_190 c
  · exact triangle_complete_191 c
  · exact triangle_complete_192 c
  · exact triangle_complete_193 c
  · exact triangle_complete_194 c
  · exact triangle_complete_195 c
  · exact triangle_complete_196 c
  · exact triangle_complete_197 c
  · exact triangle_complete_198 c
  · exact triangle_complete_199 c
  · exact triangle_complete_200 c
  · exact triangle_complete_201 c
  · exact triangle_complete_202 c
  · exact triangle_complete_203 c
  · exact triangle_complete_204 c
  · exact triangle_complete_205 c
  · exact triangle_complete_206 c
  · exact triangle_complete_207 c
  · exact triangle_complete_208 c
  · exact triangle_complete_209 c
  · exact triangle_complete_210 c
  · exact triangle_complete_211 c
  · exact triangle_complete_212 c
  · exact triangle_complete_213 c
  · exact triangle_complete_214 c
  · exact triangle_complete_215 c
  · exact triangle_complete_216 c
  · exact triangle_complete_217 c
  · exact triangle_complete_218 c
  · exact triangle_complete_219 c
  · exact triangle_complete_220 c
  · exact triangle_complete_221 c
  · exact triangle_complete_222 c
  · exact triangle_complete_223 c
  · exact triangle_complete_224 c
  · exact triangle_complete_225 c
  · exact triangle_complete_226 c
  · exact triangle_complete_227 c
  · exact triangle_complete_228 c
  · exact triangle_complete_229 c
  · exact triangle_complete_230 c
  · exact triangle_complete_231 c
  · exact triangle_complete_232 c
  · exact triangle_complete_233 c
  · exact triangle_complete_234 c
  · exact triangle_complete_235 c
  · exact triangle_complete_236 c
  · exact triangle_complete_237 c
  · exact triangle_complete_238 c
  · exact triangle_complete_239 c
  · exact triangle_complete_240 c
  · exact triangle_complete_241 c
  · exact triangle_complete_242 c
  · exact triangle_complete_243 c
  · exact triangle_complete_244 c
  · exact triangle_complete_245 c
  · exact triangle_complete_246 c
  · exact triangle_complete_247 c
  · exact triangle_complete_248 c
  · exact triangle_complete_249 c
  · exact triangle_complete_250 c
  · exact triangle_complete_251 c
  · exact triangle_complete_252 c
  · exact triangle_complete_253 c
  · exact triangle_complete_254 c
  · exact triangle_complete_255 c
  · exact triangle_complete_256 c
  · exact triangle_complete_257 c
  · exact triangle_complete_258 c
  · exact triangle_complete_259 c
  · exact triangle_complete_260 c
  · exact triangle_complete_261 c
  · exact triangle_complete_262 c
  · exact triangle_complete_263 c
  · exact triangle_complete_264 c
  · exact triangle_complete_265 c
  · exact triangle_complete_266 c
  · exact triangle_complete_267 c
  · exact triangle_complete_268 c
  · exact triangle_complete_269 c
  · exact triangle_complete_270 c
  · exact triangle_complete_271 c
  · exact triangle_complete_272 c
  · exact triangle_complete_273 c
  · exact triangle_complete_274 c
  · exact triangle_complete_275 c
  · exact triangle_complete_276 c
  · exact triangle_complete_277 c
  · exact triangle_complete_278 c
  · exact triangle_complete_279 c
  · exact triangle_complete_280 c
  · exact triangle_complete_281 c
  · exact triangle_complete_282 c
  · exact triangle_complete_283 c
  · exact triangle_complete_284 c
  · exact triangle_complete_285 c
  · exact triangle_complete_286 c
  · exact triangle_complete_287 c
  · exact triangle_complete_288 c
  · exact triangle_complete_289 c
  · exact triangle_complete_290 c
  · exact triangle_complete_291 c
  · exact triangle_complete_292 c
  · exact triangle_complete_293 c
  · exact triangle_complete_294 c
  · exact triangle_complete_295 c
  · exact triangle_complete_296 c
  · exact triangle_complete_297 c
  · exact triangle_complete_298 c
  · exact triangle_complete_299 c
  · exact triangle_complete_300 c
  · exact triangle_complete_301 c
  · exact triangle_complete_302 c
  · exact triangle_complete_303 c
  · exact triangle_complete_304 c
  · exact triangle_complete_305 c
  · exact triangle_complete_306 c
  · exact triangle_complete_307 c
  · exact triangle_complete_308 c
  · exact triangle_complete_309 c
  · exact triangle_complete_310 c
  · exact triangle_complete_311 c
  · exact triangle_complete_312 c
  · exact triangle_complete_313 c
  · exact triangle_complete_314 c
  · exact triangle_complete_315 c
  · exact triangle_complete_316 c
  · exact triangle_complete_317 c
  · exact triangle_complete_318 c
  · exact triangle_complete_319 c
  · exact triangle_complete_320 c
  · exact triangle_complete_321 c
  · exact triangle_complete_322 c
  · exact triangle_complete_323 c
  · exact triangle_complete_324 c
  · exact triangle_complete_325 c
  · exact triangle_complete_326 c
  · exact triangle_complete_327 c
  · exact triangle_complete_328 c
  · exact triangle_complete_329 c
  · exact triangle_complete_330 c
  · exact triangle_complete_331 c
  · exact triangle_complete_332 c
  · exact triangle_complete_333 c
  · exact triangle_complete_334 c
  · exact triangle_complete_335 c
  · exact triangle_complete_336 c
  · exact triangle_complete_337 c
  · exact triangle_complete_338 c
  · exact triangle_complete_339 c
  · exact triangle_complete_340 c
  · exact triangle_complete_341 c
  · exact triangle_complete_342 c
  · exact triangle_complete_343 c
  · exact triangle_complete_344 c
  · exact triangle_complete_345 c
  · exact triangle_complete_346 c
  · exact triangle_complete_347 c
  · exact triangle_complete_348 c
  · exact triangle_complete_349 c
  · exact triangle_complete_350 c
  · exact triangle_complete_351 c
  · exact triangle_complete_352 c
  · exact triangle_complete_353 c
  · exact triangle_complete_354 c
  · exact triangle_complete_355 c
  · exact triangle_complete_356 c
  · exact triangle_complete_357 c
  · exact triangle_complete_358 c
  · exact triangle_complete_359 c
  · exact triangle_complete_360 c
  · exact triangle_complete_361 c
  · exact triangle_complete_362 c
  · exact triangle_complete_363 c
  · exact triangle_complete_364 c
  · exact triangle_complete_365 c
  · exact triangle_complete_366 c
  · exact triangle_complete_367 c
  · exact triangle_complete_368 c
  · exact triangle_complete_369 c
  · exact triangle_complete_370 c
  · exact triangle_complete_371 c
 theorem sorted_adj_rank : ∀ a b : Fin 103, a < b → SeedEncoding.indexedAdj a b →
    rankIndex a < rankIndex b := by decide +kernel
end EilenbergGanea.SeedChainCertificate
namespace EilenbergGanea.SeedChainCertificate
open SimplicialChains

@[simp] theorem graph_adj (a b : Fin 103) : graph.Adj a b ↔ SeedEncoding.indexedAdj a b :=
  SeedEncoding.adjacency_certificate a b

 theorem valid_pair_iff (a b : Fin 103) :
    Valid graph [a,b] ↔ a < b ∧ SeedEncoding.indexedAdj a b := by simp [Valid]
 theorem valid_triple_iff (a b c : Fin 103) :
    Valid graph [a,b,c] ↔ a < b ∧ b < c ∧ SeedEncoding.indexedAdj a b ∧
      SeedEncoding.indexedAdj a c ∧ SeedEncoding.indexedAdj b c := by
  simp [Valid]
  constructor
  · rintro ⟨⟨⟨hab,_⟩,hbc⟩,⟨⟨h₁,h₂⟩,h₃⟩⟩
    exact ⟨hab,hbc,h₁,h₂,h₃⟩
  · rintro ⟨hab,hbc,h₁,h₂,h₃⟩
    exact ⟨⟨⟨hab,hab.trans hbc⟩,hbc⟩,⟨⟨h₁,h₂⟩,h₃⟩⟩

 theorem valid_length_le (w : List (Fin 103)) (hw : Valid graph w) : w.length ≤ 3 := by
  have hp : w.Pairwise (fun a b => rankIndex a < rankIndex b) := by
    have hh := hw.1.and hw.2
    exact hh.imp (fun {a b} h => sorted_adj_rank a b h.1 ((graph_adj a b).mp h.2))
  have hn : (w.map rankIndex).Nodup := by
    apply List.nodup_iff_pairwise_ne.mpr
    rw [List.pairwise_map]
    exact hp.imp (fun {_ _} h => ne_of_lt h)
  have he := hn.length_le_card
  simpa using he

 def indices : TwoDimensionalIndices (L := graph) (Fin 372) (Fin 270) where
  edge := edge
  triangle := triangle
  face := triangleEdges
  edgeIndex := edgeIndex
  triangleIndex := fun a b c => triangleIndex (edgeIndex a b) c
  edge_valid := fun e => (valid_pair_iff _ _).mpr (edge_valid e)
  triangle_valid := fun t => (valid_triple_iff _ _ _).mpr (triangle_valid t)
  edge_inverse := edge_index_inverse
  edge_complete := fun a b h => edge_complete a b ((valid_pair_iff a b).mp h).1
    ((valid_pair_iff a b).mp h).2
  triangle_complete := by
    intro a b c h
    obtain ⟨hab,hbc,h₁,h₂,h₃⟩ := (valid_triple_iff a b c).mp h
    have he := edge_complete a b hab h₁
    have ht := triangle_complete (edgeIndex a b) c
    rw [he] at ht
    exact ht hbc h₂ h₃
  face_edge := triangle_edges_valid
  length_le := valid_length_le

end EilenbergGanea.SeedChainCertificate


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

def seedYQuaternion : ℍ :=
  ⟨seedGoldenReal,1/2,Real.sqrt ((3 - Real.sqrt 5)/8),0⟩

end EilenbergGanea



end

end OAI
end


