-- Prove2me | Definitions.Def_OAIQ18Pg010
-- name    : OAIQ18Pg010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T16:03:26.257586+00:00
-- url     : https://prove2.me/theorems/cc248a81-7a1c-49bc-8a9a-be6dd5116bbf
-- title:
--   Definitions bundle OAIQ18Pg010 of the split of OpenAI, An infinite finitely presented periodic group
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SourceBurnside.thm_main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented periodic group*, OpenAI Math Release, September 23, 2026, result family 247, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 144 declarations of OpenAI's Lean: 52 definitions, 2 inductive types or structures, 1 instance and 89 theorems. The definitions and types are `OAI.SourceBurnside.FiniteTable.Rigid.Layout`, `OAI.SourceBurnside.FiniteTable.Rigid.colors`, `OAI.SourceBurnside.FiniteTable.Rigid.decoded`, `OAI.SourceBurnside.FiniteTable.Rigid.encoded`, `OAI.SourceBurnside.FiniteTable.Rigid.palOffset`, `OAI.SourceBurnside.FiniteTable.Rigid.paletteView`, `OAI.SourceBurnside.FiniteTable.Rigid.regionBlock`, `OAI.SourceBurnside.FiniteTable.Rigid.shape`, `OAI.SourceBurnside.FiniteTable.Rigid.viewCell`, `OAI.SourceBurnside.FiniteTable.UnaryAt`, `OAI.SourceBurnside.Kernel.BlockFactor`, `OAI.SourceBurnside.Kernel.BlockFactor.Bounded`, `OAI.SourceBurnside.Kernel.bandStrip`, `OAI.SourceBurnside.Kernel.rootWord`, `OAI.SourceBurnside.Kernel.truncatedProduct`, `OAI.SourceBurnside.Kernel.wrapFactors`, `OAI.SourceBurnside.Kernel.wrappedProduct`, `OAI.SourceBurnside.SourceMachine.templateData`, `OAI.SourceBurnside.Stability.ElementaryRanks.next`, `OAI.SourceBurnside.Stability.ElementaryRanks.representation`, `OAI.SourceBurnside.Stability.ElementaryRanks.root`, `OAI.SourceBurnside.Stability.FrameStabilizer.A`, `OAI.SourceBurnside.Stability.FrameStabilizer.b`, `OAI.SourceBurnside.Stability.FrameStabilizer.characterK`, `OAI.SourceBurnside.Stability.FrameStabilizer.characterP`, `OAI.SourceBurnside.Stability.FrameStabilizer.characterS`, `OAI.SourceBurnside.Stability.FrameStabilizer.instMulActionSubtypeUnitsMatrixSumMemSubgroupGIndex_1`, `OAI.SourceBurnside.Stability.H2FrameEdge.augmentation`, `OAI.SourceBurnside.Stability.H2FrameEdge.chains`, `OAI.SourceBurnside.Stability.RationalExtension.factor`, `OAI.SourceBurnside.Stability.SingletonFrameEdge.blockHom`, `OAI.SourceBurnside.Stability.SingletonFrameEdge.lift`, `OAI.SourceBurnside.Stability.SmallPresentation.K1`, `OAI.SourceBurnside.Stability.SmallPresentation.K1equivalence`, `OAI.SourceBurnside.Stability.SmallPresentation.K1map`, `OAI.SourceBurnside.Stability.SmallPresentation.collapse`, `OAI.SourceBurnside.Stability.SmallPresentation.collapseGroup`, `OAI.SourceBurnside.Stability.SmallPresentation.cosetData`, `OAI.SourceBurnside.Stability.SmallPresentation.elementaryGroup`, `OAI.SourceBurnside.Stability.SmallPresentation.equivalence` and 14 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/PeriodicGroups, in whole or in part: `PeriodicGroups_Frames_AcyclicFrameEdge`, `PeriodicGroups_Frames_ElementaryFrames`, `PeriodicGroups_Frames_ExteriorComplex`, `PeriodicGroups_Homology_FiniteNormalHomology`, `PeriodicGroups_Homology_LocallyFiniteActions`, `PeriodicGroups_Homology_RelativeHomology`, `PeriodicGroups_Matrices_ElementaryGenerators`, `PeriodicGroups_Presentation_FinitePresentation`, `PeriodicGroups_Presentation_MatrixStabilizers`, `PeriodicGroups_Presentation_SmallFaithful`, `PeriodicGroups_Presentation_SmallSwapActions`, `PeriodicGroups_Rules_ConnectedWords`, `PeriodicGroups_Rules_DataWords`, `PeriodicGroups_Rules_GeometricRelations`, `PeriodicGroups_Rules_TableEncoding`, `PeriodicGroups_Rules_TemplateHierarchy`, `PeriodicGroups_Rules_WordRewriting`, `PeriodicGroups_Steinberg_BandFactorization`, `PeriodicGroups_Steinberg_DiagonalActions`, `PeriodicGroups_Steinberg_MatrixUnits`, `PeriodicGroups_Steinberg_RankActions`.
--
--   **Imports.** It imports the published bundle `Def_PeriodicGroup`; the bundles `OAIQ18Pg000`, `OAIQ18Pg001`, `OAIQ18Pg005`, `OAIQ18Pg007` and `OAIQ18Pg008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ18Pg012` and `OAIQ18Pg013`.
-- source:
--   OpenAI, An infinite finitely presented periodic group, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 247; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/PeriodicGroups at commit adc7f12

import Mathlib
import Definitions.Def_PeriodicGroup
import Definitions.Def_OAIQ18Pg000
import Definitions.Def_OAIQ18Pg001
import Definitions.Def_OAIQ18Pg005
import Definitions.Def_OAIQ18Pg007
import Definitions.Def_OAIQ18Pg008

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Frames_ExteriorComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.Frames
noncomputable section
open Classical Module

variable (V : Type*)

variable {V}

variable [LinearOrder V]

variable {F W : Type*} [DivisionRing F] [AddCommGroup W] [Module F W]

variable (ρ : V → W) (C : ConeSupply (F := F) ρ 10)

theorem twoCycle_bounds [FiniteDimensional F W]
    (hρ : Submodule.span F (Set.range ρ) = ⊤) (hrank : 10 < Module.finrank F W)
    {z : Ambient V} (hz : z ∈ chains (F := F) ρ Set.univ 3) (hcycle : boundary V z = 0) :
    ∃ w ∈ chains (F := F) ρ Set.univ 4, boundary V w = z := by
  let D := coneSupply ρ hρ 10 hrank
  refine ⟨homotopy2 ρ D z, homotopy2_mem ρ D hz, ?_⟩
  rw [boundary_homotopy2 ρ D hz, hcycle, map_zero, sub_zero]

theorem cycles_bound_upToThree [FiniteDimensional F W]
    (hρ : Submodule.span F (Set.range ρ) = ⊤) (hrank : 10 < Module.finrank F W)
    (k : ℕ) (hk : k ≤ 3) {z : Ambient V}
    (hz : z ∈ chains (F := F) ρ Set.univ k) (hcycle : boundary V z = 0) :
    ∃ w ∈ chains (F := F) ρ Set.univ (k+1), boundary V w = z := by
  let D := coneSupply ρ hρ 10 hrank
  interval_cases k
  · exact degreeZero_lift ρ D hz
  · refine ⟨homotopy0 ρ D z, homotopy0_mem_univ ρ D hz, ?_⟩
    rw [boundary_homotopy0 ρ D hz, hcycle, mul_zero, sub_zero]
  · refine ⟨homotopy1 ρ D z, homotopy1_mem_univ ρ D hz, ?_⟩
    rw [boundary_homotopy1 ρ D hz, hcycle, map_zero, sub_zero]
  · exact twoCycle_bounds ρ hρ hrank hz hcycle

end
end SourceBurnside.Stability.Frames

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Frames_AcyclicFrameEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SourceBurnside.Stability.Frames
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits Module
variable {V : Type} [LinearOrder V] (G : Type) [Group G] [MulAction G V]
variable {F W : Type} [DivisionRing F] [AddCommGroup W] [Module F W]
variable (ρ : V → W)
variable (hind : ∀(g : G) (s : Set V), LinearIndepOn F ρ s →
  LinearIndepOn F ρ ((g • ·) '' s))

lemma repComplex_exact [FiniteDimensional F W]
    (hρ : Submodule.span F (Set.range ρ) = ⊤) (hrank : 10 < Module.finrank F W)
    (k : ℕ) (hk : k ≤ 2) :
    ((repComplex G ρ hind).sc' (k+2) (k+1) k).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℚ G) (ModuleCat ℚ))).mp
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
  intro x hx
  change ((repComplex G ρ hind).d (k+1) k).hom x = 0 at hx
  rw [repComplex_d] at hx
  have hz : boundary V x.val = 0 := congrArg Subtype.val hx
  obtain ⟨y,hy,hdy⟩ := cycles_bound_upToThree ρ hρ hrank (k+1) (by omega) x.property hz
  refine ⟨⟨y,hy⟩,?_⟩
  change ((repComplex G ρ hind).d ((k+1)+1) (k+1)).hom ⟨y,hy⟩ = x
  rw [repComplex_d]
  exact Subtype.ext hdy

lemma differentialRep_epi [FiniteDimensional F W]
    (hρ : Submodule.span F (Set.range ρ) = ⊤) (hrank : 10 < Module.finrank F W) :
    Epi (differentialRep G ρ hind 0) := by
  apply (Rep.epi_iff_surjective _).mpr
  intro x
  obtain ⟨y,hy,hdy⟩ := degreeZero_lift ρ (coneSupply ρ hρ 10 hrank) x.property
  exact ⟨⟨y,hy⟩,Subtype.ext hdy⟩

end

end SourceBurnside.Stability.Frames

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_RelativeHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SourceBurnside.Stability
noncomputable section
open Classical
namespace RationalExtension
open RationalBar
variable {X G : Type} [Group X] [Group G] (S : RationalExtension X G)

@[simp] lemma projection_section (g : G) : S.rightHom (S.chosenSection g)=g :=
  S.toGroupExtension.surjInvRightHom.rightInverse_rightHom g

def factor (g h : G) : ℚ :=
  (S.kernelEquiv.symm ⟨S.chosenSection g*S.chosenSection h*(S.chosenSection (g*h))⁻¹,by
    simp only [MonoidHom.mem_ker,map_mul,map_inv,projection_section,mul_inv_cancel]⟩).toAdd

end RationalExtension
end
end SourceBurnside.Stability

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_TableEncoding
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest _root_.OAI.SourceBurnside.FiniteTable.instDecidableCellCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.FiniteTable.Codec
open LocalSyntax

lemma unaryZero_encode {h : ℕ} (hh : 4≤h) (S : Schedule (2^h)) (d : ℕ) (a : Cell (2^h)) :
    unaryZero (by omega) S d (encode a) ↔ UnaryZero S d a := by
  simp [unaryZero,decode_encode hh]

end SourceBurnside.FiniteTable.Codec

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_ConnectedWords
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton

variable {q N : ℕ}

variable [NeZero q]

structure UnaryAt (S : Schedule q) (f g : Fin N → Cell q) (i : Fin N) : Prop where
  off : ∀ h, h≠i → f h=g h
  edge : Unary S (f i) (g i)

end SourceBurnside.FiniteTable
end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_WordRewriting
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

lemma canonicalCell_pair (a b : Fin d → ZMod 2) (p r : Position q)
    (h : Skeleton.Structural (canonicalCell a p).skeleton (canonicalCell b r).skeleton) :
    Pair (canonicalCell a p) (canonicalCell b r) := by
  refine ⟨⟨h,Or.inl ⟨?_,?_⟩⟩, ?_⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · simp [CheckerPair,canonicalCell,Palette.LastOK]

lemma canonicalBlock_pair_chain (bits : Fin d → ZMod 2) :
    (canonicalBlock (q:=q) bits).IsChain Pair := by
  have hc : ((List.finRange q).map (fun p => canonicalCell bits (.core p))).IsChain Pair := by
    rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.length_map,List.length_finRange] at hi
    simp only [List.getElem_map,List.getElem_finRange]
    apply canonicalCell_pair bits bits
    rfl
  have hp : ((List.finRange q).map (fun p => canonicalCell bits (.palette p))).IsChain Pair := by
    rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.getElem_map,List.getElem_finRange]
    apply canonicalCell_pair bits bits
    trivial
  apply (hc.append hp ?_).append (List.isChain_singleton _) ?_
  · intro a ha b hb
    rw [List.getLast?_map,finRange_last] at ha
    rw [List.head?_map,finRange_head] at hb
    simp only [Option.map_some,Option.mem_def,Option.some.injEq] at ha hb
    subst a; subst b
    apply canonicalCell_pair bits bits
    change q-1+1=q
    have := NeZero.pos q
    omega
  · intro a ha b hb
    simp only [List.getLast?_append,List.getLast?_map,finRange_last,
      Option.map_some,Option.or_some,Option.mem_def,Option.some.injEq] at ha
    simp only [List.head?_cons,Option.mem_def,Option.some.injEq] at hb
    subst a; subst b
    apply canonicalCell_pair bits bits
    trivial

lemma canonicalBlock_head (bits : Fin d → ZMod 2) :
    (canonicalBlock (q:=q) bits).head? = some (canonicalCell bits (.core 0)) := by
  simp [canonicalBlock,List.head?_append,List.head?_map,finRange_head]

lemma canonicalBlock_last (bits : Fin d → ZMod 2) :
    (canonicalBlock (q:=q) bits).getLast? = some (canonicalCell bits .stop) := by
  simp [canonicalBlock,List.getLast?_append]

lemma encodeWord_pair_chain (w : List (Fin d → ZMod 2)) :
    (encodeWord (q:=q) w).IsChain Pair := by
  induction w with
  | nil => simp [encodeWord]
  | cons b w ih =>
    change (canonicalBlock b ++ encodeWord w).IsChain Pair
    apply (canonicalBlock_pair_chain b).append ih
    intro a ha c hc
    rw [canonicalBlock_last] at ha
    simp only [Option.mem_def,Option.some.injEq] at ha
    subst a
    cases w with
    | nil => simp [encodeWord] at hc
    | cons b' w =>
      have he : (encodeWord (b'::w)).head? = some (canonicalCell b' (.core (0 : Fin q))) := by
        change (canonicalBlock b' ++ encodeWord w).head? = _
        rw [List.head?_append,canonicalBlock_head]
        rfl
      rw [he] at hc
      simp only [Option.mem_def,Option.some.injEq] at hc
      subst c
      exact canonicalCell_pair b b' .stop (.core 0) rfl

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_GeometricRelations
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable

open LocalSyntax LocalSyntax.Skeleton
namespace Rigid
variable {q d n : ℕ} [NeZero q]

def shape (i : Fin (width q)) : Shape q := match position i with
  | .core p => .core p | .palette _ => .palette | .stop => .stop

omit [NeZero q] in
lemma position_core_iff (i : Fin (width q)) (p : Fin q) :
    position i=.core p ↔ i.val=p.val := by
  unfold position
  split_ifs with hi hp
  · simp only [Position.core.injEq,Fin.ext_iff]
  · simp only [false_iff]
    intro he; have := p.isLt; omega
  · simp only [false_iff]
    intro he; have := p.isLt; omega
omit [NeZero q] in
lemma position_stop_iff (i : Fin (width q)) : position i=.stop ↔ i.val=2*q := by
  have := i.isLt
  unfold width at this
  unfold position
  split_ifs <;> simp_all only [false_iff,true_iff] <;> omega
omit [NeZero q] in
lemma shape_stop_iff (i : Fin (width q)) : shape i=.stop ↔ i.val=2*q := by
  rw [←position_stop_iff]
  cases hp : position i <;> simp [shape,hp]

def encoded (u : Fin n → Fin d → ZMod 2) (i : Fin (n*width q)) : Cell q :=
  canonicalCell (u (block i)) (position (coord i))

lemma encoded_cell (u : Fin n → Fin d → ZMod 2) (b : Fin n) (p : Fin (width q)) :
    encoded u (cell b p)=canonicalCell (u b) (position p) := by
  simp [encoded,block_cell,coord_cell]

def Layout (f : Fin (n*width q) → Cell q) : Prop := ∀i, (f i).shape=shape (coord i)

noncomputable def decoded (hd : d≤q) (f : Fin (n*width q) → Cell q) :
    Fin n → Fin d → ZMod 2 := fun b p => Committed.value f (core b (p.castLE hd))

omit [NeZero q] in
lemma layout_stop_iff {f : Fin (n*width q) → Cell q} (hf : Layout f)
    (i : Fin (n*width q)) : (f i).pos=.stop ↔ i.val%width q=2*q := by
  rw [←Cell.shape_stop_iff,hf,shape_stop_iff]
  rfl

section Component
variable {S : Schedule q} {f : Fin (n*width q) → Cell q} (hl : Layout f)
  (hs : Syntax S d (List.ofFn f)) (i : Fin (n*width q)) (hi : (f i).marker=.full)
include hl hs hi

lemma component_block_counter (j : Fin (Component.size f i)) :
    (f (Component.offset f i j)).metadata.block.val+(block (Component.left f i)).val=
      (block (Component.offset f i j)).val := by
  generalize he : j.val=t
  induction t generalizing j with
  | zero =>
    have ho : Component.offset f i j=Component.left f i := by apply Fin.ext; simp [Component.offset,he]
    rw [ho]
    have hh := (Component.first f i (Verification.coherent_of_syntax S hs)
      (exterior_of_syntax hs) (Or.inr hi)).1
    simp only [Cell.metadata] at *
    omega
  | succ t ih =>
    let p : Fin (Component.size f i) := ⟨t,by have := j.isLt; omega⟩
    have hpj : p.val+1=j.val := by dsimp [p]; omega
    have ih' := ih p rfl
    have hj := Component.offset_adjacent f i p j hpj
    have hb := block_next hj
    have hh := (Component.offset_internal f i (Verification.coherent_of_syntax S hs)
      p j hpj).2.2.1
    change (if (f (Component.offset f i p)).pos=.stop then
      (f (Component.offset f i p)).metadata.block.val+1=(f (Component.offset f i j)).metadata.block.val
      else (f (Component.offset f i p)).metadata.block.val=(f (Component.offset f i j)).metadata.block.val) at hh
    by_cases hp : (f (Component.offset f i p)).pos=.stop
    · rw [ite_eq_left hp] at hh
      rw [ite_eq_left ((layout_stop_iff hl _).mp hp)] at hb
      change (f (Component.offset f i p)).metadata.block.val+1=
        (f (Component.offset f i j)).metadata.block.val at hh
      omega
    · rw [ite_eq_right hp] at hh
      rw [ite_eq_right (by simpa only [←layout_stop_iff hl _] using hp)] at hb
      change (f (Component.offset f i p)).metadata.block.val=
        (f (Component.offset f i j)).metadata.block.val at hh
      omega

lemma component_last_block : (block (Component.right f i)).val=
    (block (Component.left f i)).val+(f i).metadata.arity.val := by
  obtain ⟨j,hj⟩ := Component.offset_surjective f i (Component.connected_right f i)
  have hh := component_block_counter hl hs i hi j
  rw [hj] at hh
  have hs' := (Component.last f i (Verification.coherent_of_syntax S hs)
    (exterior_of_syntax hs) hi).1
  have ht := SameRegion.task (Verification.coherent_of_syntax S hs)
    (Component.connected_right f i)
  have ha := congrArg (fun t : Task => t.arity.val) ht
  change (f i).metadata.arity.val=(f (Component.right f i)).metadata.arity.val at ha
  change (f (Component.right f i)).metadata.block.val=(f (Component.right f i)).metadata.arity.val at hs'
  omega

noncomputable def regionBlock (b : Fin ((f i).metadata.arity.val+1)) : Fin n :=
  ⟨(block (Component.left f i)).val+b.val,by
    have hh := component_last_block hl hs i hi
    have hb := b.isLt
    have hr := (block (Component.right f i)).isLt
    omega⟩

end Component

end Rigid
end SourceBurnside.FiniteTable

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_DataWords
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable

section
open LocalSyntax LocalSyntax.Skeleton
variable {q d n : ℕ} [NeZero q]
namespace Rigid

def colors (f : Fin (n*width q) → Cell q) (b : Fin n) : List (Fin q) :=
  List.ofFn (fun p => (f (palCell b p)).color)

lemma position_palette_iff (i : Fin (width q)) :
    (∃x, position i=.palette x) ↔ q ≤ i.val ∧ i.val < 2*q := by
  unfold position
  split_ifs <;> simp_all; omega

lemma layout_palette_iff {f : Fin (n*width q) → Cell q} (hl : Layout f)
    (i : Fin (n*width q)) : (f i).isPalette ↔ q ≤ i.val%width q ∧ i.val%width q < 2*q := by
  have hshape : (f i).isPalette ↔ (f i).shape=.palette := by
    cases he : (f i).pos <;> simp [Cell.shape,Cell.isPalette,he]
  rw [hshape,hl]
  have he : shape (coord i)=.palette ↔ ∃x,position (coord i)=.palette x := by
    cases he : position (coord i) <;> simp [shape,he]
  rw [he,position_palette_iff]
  rfl

noncomputable def palOffset {f : Fin (n*width q) → Cell q} (hl : Layout f)
    (i : Fin (n*width q)) (hi : (f i).isPalette) : Fin q :=
  ⟨i.val%width q-q,by have := (layout_palette_iff hl i).mp hi; omega⟩

def viewCell (f : Fin (n*width q) → Cell q) (b : Fin n) (p : Fin q) : Palette.Cell (Fin q) Unit :=
  ⟨(f (palCell b p)).color,(f (palCell b p)).checker,()⟩

def paletteView (f : Fin (n*width q) → Cell q) (b : Fin n) := List.ofFn (viewCell f b)

end Rigid
end

open LocalSyntax LocalSyntax.Skeleton
end SourceBurnside.FiniteTable

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_TemplateHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q]
namespace Rigid

omit [NeZero q] in
lemma adjacent_blocks {n : ℕ} (i j : Fin (n*width q)) (hij : i.val+1=j.val) :
    if position (coord i)=.stop then (block i).val+1=(block j).val
    else (block i).val=(block j).val := by
  have hdiv := Nat.div_add_mod i.val (width q)
  rw [Nat.mul_comm] at hdiv
  have hm := Nat.mod_lt i.val (width_pos (q:=q))
  split_ifs with hi
  · have hr := (position_stop_iff (coord i)).mp hi
    have hj : j.val=((block i).val+1)*width q := by
      dsimp [coord] at hr
      dsimp [block]
      rw [Nat.add_mul,Nat.one_mul]
      have hrw : i.val%width q+1=width q := by change i.val%width q+1=2*q+1;omega
      omega
    simp [block,hj,ne_of_gt width_pos]
  · have hr : i.val%width q≠2*q := by
      simpa only [position_stop_iff,coord] using hi
    have hb : i.val%width q+1<width q := by
      change i.val%width q+1<2*q+1
      change i.val%width q<2*q+1 at hm
      omega
    have hj : j.val=(block i).val*width q+(i.val%width q+1) := by
      dsimp [block]
      omega
    rw [show (block j).val=j.val/width q from rfl,hj,Nat.add_comm,
      Nat.add_mul_div_right _ _ width_pos,Nat.div_eq_of_lt hb]
    simp

namespace Template
variable (task : Task) (u : Bool → Fin (task.arity.val+1) → Fin d → ZMod 2)
    (cert : Fin q → ZMod 2)

lemma first_iff (i : Fin ((task.arity.val+1)*width q)) :
    (cell task u cert i).skeleton.first ↔ i.val=0 := by
  change ((block i).val=0 ∧ ∃p,position (coord i)=.core p ∧ p.val=0) ↔ _
  simp only [position_core_iff]
  constructor
  · rintro ⟨hb,p,hp,hp0⟩
    have he := Nat.div_add_mod i.val (width q)
    change i.val/width q=0 at hb
    change i.val%width q=p.val at hp
    rw [hb,hp,hp0] at he
    simpa using he.symm
  · intro hi
    refine ⟨?_,0,?_,rfl⟩ <;> simp [block,coord,hi]

lemma last_iff (i : Fin ((task.arity.val+1)*width q)) :
    (cell task u cert i).skeleton.last ↔ i.val+1=(task.arity.val+1)*width q := by
  change ((block i).val=task.arity.val ∧ position (coord i)=.stop) ↔ _
  simp only [position_stop_iff]
  have he := Nat.div_add_mod i.val (width q)
  have hm := (coord i).isLt
  change i.val%width q<2*q+1 at hm
  constructor
  · rintro ⟨hb,hp⟩
    change i.val/width q=task.arity.val at hb
    change i.val%width q=2*q at hp
    rw [hb,hp] at he
    dsimp [width] at he ⊢
    nlinarith
  · intro hi
    have hic : i.val=task.arity.val*width q+2*q := by
      dsimp [width] at hi ⊢
      nlinarith
    constructor
    · change i.val/width q=task.arity.val
      rw [hic,Nat.add_comm,Nat.add_mul_div_right _ _ width_pos,
        Nat.div_eq_of_lt (by dsimp [width];omega)]
      simp
    · change i.val%width q=2*q
      simp only [hic,Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod]
      exact Nat.mod_eq_of_lt (by dsimp [width];omega)

lemma payload_format (i : Fin ((task.arity.val+1)*width q)) :
    (cell task u cert i).PayloadFormat d := by
  unfold Cell.PayloadFormat Cell.isPalette Cell.isCore
  rw [pos]
  constructor
  · intro; rfl
  constructor
  · intro p hp hd
    funext s
    simp [cell,hp,Nat.not_lt_of_ge hd]
  · intro hi
    cases hp : position (coord i) with
    | core p => exact (hi ⟨p,hp⟩).elim
    | palette c => simp [cell,hp]; rfl
    | stop => simp [cell,hp]; rfl

end Template
end Rigid
end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q]

namespace Rigid.Template
variable (task : Task) (u : Bool → Fin (task.arity.val+1) → Fin d → ZMod 2)
    (cert : Fin q → ZMod 2)

lemma idle_cell (s : Bool) (i : Fin ((task.arity.val+1)*width q)) :
    (cell task u cert i).idle s=encoded (u s) i := by
  unfold encoded
  cases hp : position (coord i) <;>
    simp [Cell.idle,cell,canonicalCell,Cell.pos,hp]

end Rigid.Template
end SourceBurnside.FiniteTable

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable
variable {q d h D : ℕ} [NeZero q]
def templateData (task : Task) (u : Bool → Fin (task.arity.val+1) → Fin d → Bool) : DataAddress q → Bool :=
  fun a => if hb : a.2.1.val<task.arity.val+1 then
    if hp : a.2.2.val<d then u a.1 ⟨a.2.1.val,hb⟩ ⟨a.2.2.val,hp⟩ else false
    else false
omit [NeZero q] in
lemma candidate_template (task : Task) (u : Bool → Fin (task.arity.val+1) → Codec.Raw h)
    (hd : 10000*h≤q) (hl : task.arity.val+1≤10) (s : Bool) :
    List.ofFn (candidateWord (l:=task.arity.val+1) (templateData (q:=q) task u) hd hl s)=List.ofFn (u s) := by
  congr 1
  funext b p
  simp [candidateWord,templateData,b.isLt,p.isLt]
end
end SourceBurnside.SourceMachine

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable

namespace MachineHierarchy
variable {D : ℕ} {hD : 2≤D} (A : MachineHierarchy D hD)
lemma next_large {h : ℕ} (hh : A.threshold≤h) : A.threshold≤D*h := by nlinarith [A.threshold_four]
end MachineHierarchy
end
end SourceBurnside.SourceMachine

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_BandFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
def bandStrip (w : ℕ) (h : 2*w ≤ N) : Subgroup (Steinberg (n*N) R) :=
  Strip (highBand w) (lowBand w) (bands_disjoint w h)
structure BlockFactor (n N : ℕ) (R : Type*) where
  position : Root n
  main : Matrix (Fin N) (Fin N) R
  correction : Matrix (Fin N) (Fin N) R
def wrappedProduct (l : List (BlockFactor n N R)) : Steinberg (n*N) R :=
  (l.map (fun x=>blockRoot x.position (x.main+x.correction))).prod
def truncatedProduct (l : List (BlockFactor n N R)) : Steinberg (n*N) R :=
  (l.map (fun x=>blockRoot x.position x.main)).prod
def BlockFactor.Bounded (d : ℕ) (x : BlockFactor n N R) : Prop :=
  (∀s t,x.main s t≠0→t.val ≤ s.val+d) ∧
  (∀s t,x.correction s t≠0→N ≤ s.val+d ∧ t.val<d)

end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
def rootWord (l : List (Root n×R)) : Steinberg n R := (l.map (fun pa=>Steinberg.x pa.1 pa.2)).prod
variable [Algebra (ZMod 2) R]
def wrapFactors (l : List (Root n×Polynomial R)) : List (BlockFactor n N R) :=
  l.map (fun pa=>⟨pa.1,matrixEval (truncatedShift N (ZMod 2)) pa.2,
    matrixEval (cyclicShift N (ZMod 2)) pa.2-matrixEval (truncatedShift N (ZMod 2)) pa.2⟩)
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {N : ℕ}

lemma numerical_matrix_lift (P : Matrix (Fin N) (Fin N) (ZMod 2)) (hP : P.det≠0) :
    ∃g : Steinberg N (ZMod 2),(Elementary.representation g).val=P := by
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun A=>∃g : Steinberg N (ZMod 2),(Elementary.representation g).val=A) P hP
  · intro D hD
    have he : D=fun _=>1 := by
      funext i
      have hprod : ∏j,D j≠0 := by simpa using hD
      have hi := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ _)
      have hc : ∀a : ZMod 2,a≠0→a=1 := by decide
      exact hc (D i) hi
    exact ⟨1,by simp [he]⟩
  · intro t
    refine ⟨Steinberg.x ⟨t.i,t.j,t.hij⟩ t.c,?_⟩
    rw [Elementary.representation_x]
    rfl
  · intro A B hA hB hg hk
    obtain ⟨g,rfl⟩:=hg
    obtain ⟨k,rfl⟩:=hk
    exact ⟨g*k,by simp⟩
end
end SourceBurnside.Kernel

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_MatrixUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n m : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
lemma numerical_lift (P : (Matrix (Fin m) (Fin m) (ZMod 2))ˣ) :
    ∃b : Steinberg m R,Elementary.representation b=numericUnits (R:=R) P := by
  obtain ⟨b,hb⟩ := numerical_matrix_lift P.val (Matrix.isUnits_det_units P).ne_zero
  refine ⟨Steinberg.map (algebraMap (ZMod 2) R) b,?_⟩
  have hb' : Elementary.representation b=P := Units.ext hb
  have he := DFunLike.congr_fun (Elementary.representation_map (n:=m) (algebraMap (ZMod 2) R)) b
  simpa only [MonoidHom.comp_apply,hb',numericUnits] using he
end
end SourceBurnside.Kernel

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Matrices_ElementaryGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.LinearAlgebra
noncomputable section
open Classical Matrix
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
variable (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
include hI

open MatrixGenerators

omit hI [Algebra (ZMod 2) R] in
lemma representation_mem_generated {n : ℕ} (g : Steinberg n R) :
    Elementary.representation g ∈ generated := by
  have H : (⊤ : Subgroup (Steinberg n R)) ≤
      (generated (ι := Fin n) (R := R)).comap Elementary.representation := by
    rw [← Steinberg.closure_range_x]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨⟨p,a⟩, rfl⟩
    change Elementary.representation (Steinberg.x p a) ∈ generated
    rw [Elementary.representation_x]
    exact elementary_mem p.row p.col p.ne a
  exact H (Subgroup.mem_top g)

theorem full_matrix_generated (n : ℕ) (U : (Matrix (Fin n) (Fin n) R)ˣ) :
    U ∈ generated := by
  let red : (Matrix (Fin n) (Fin n) R)ˣ →* (Matrix (Fin n) (Fin n) (ZMod 2))ˣ :=
    Units.map ε.toRingHom.mapMatrix.toMonoidHom
  let N : (Matrix (Fin n) (Fin n) R)ˣ := Kernel.numericUnits (red U)
  obtain ⟨g, hg⟩ := Kernel.numerical_lift (R := R) (red U)
  have hN : red N = red U := by
    apply Units.ext
    ext i j
    simp [red, N, Kernel.numericUnits]
  have hid : ε.toRingHom.mapMatrix (N⁻¹*U).val = 1 := by
    have hh : red (N⁻¹*U) = 1 := by rw [map_mul, map_inv, hN, inv_mul_cancel]
    exact congrArg Units.val hh
  have hgen := identity_residue_generated ε hI n (N⁻¹*U) hid
  have hngen : N ∈ generated := by
    change Kernel.numericUnits (red U) ∈ generated
    rw [← hg]
    exact representation_mem_generated g
  have hh := Subgroup.mul_mem _ hngen hgen
  simpa only [mul_inv_cancel_left] using hh

theorem all_matrix_generated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : (Matrix ι ι R)ˣ) : U ∈ generated := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hh := relabel_mem e (full_matrix_generated ε hI _ (relabel e.symm U))
  simpa only [relabel_symm_apply] using hh

end
end SourceBurnside.Stability.LinearAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Presentation_FinitePresentation
attribute [-instance] _root_.OAI.SourceBurnside.Stability.SmallPresentation.columnAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
open Classical MatrixGenerators
variable {R : Type*} [Ring R]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma evaluate_surjective [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)
    (hI : MatrixNilKernel ε.toRingHom) : Function.Surjective (evaluate (ι := ι) (R := R)) := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  intro U _
  have hU := LinearAlgebra.all_matrix_generated ε hI U
  apply (show generated ≤ evaluate.range from ?_) hU
  apply (Subgroup.closure_le _).mpr
  rintro g (⟨i,j,h,a,rfl⟩ | ⟨i,u,rfl⟩)
  · exact ⟨gen (.root i j h a), evaluate_gen _⟩
  · exact ⟨gen (.diag i u), evaluate_gen _⟩

end
end SourceBurnside.Stability.SmallPresentation

end
section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators

end
end SourceBurnside.Stability.SmallPresentation

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Presentation_MatrixStabilizers
attribute [-instance] _root_.OAI.SourceBurnside.Stability.SmallPresentation.columnAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.MatrixGenerators
noncomputable section
open Classical Matrix
variable {R ι κ : Type*} [Ring R] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma block_mem_of_generators [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)
    (hI : MatrixNilKernel ε.toRingHom) {P : Subgroup (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ}
    (he : ∀i j h a, elementary (Sum.inl i) (Sum.inl j) (Sum.inl_injective.ne h) a ∈ P)
    (hd : ∀i u, singleDiagonal (Sum.inl i) u ∈ P) (U : (Matrix ι ι R)ˣ) :
    blockInclusion U ∈ P := by
  have hU := LinearAlgebra.all_matrix_generated ε hI U
  apply (show generated ≤ P.comap blockInclusion from ?_) hU
  apply (Subgroup.closure_le _).mpr
  rintro g (⟨i,j,h,a,rfl⟩ | ⟨i,u,rfl⟩)
  · change blockInclusion (elementary i j h a) ∈ P
    rw [blockInclusion_elementary]
    exact he i j h a
  · change blockInclusion (singleDiagonal i u) ∈ P
    rw [blockInclusion_singleDiagonal]
    exact hd _ _

lemma rightFixer_generated [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)
    (hI : MatrixNilKernel ε.toRingHom) {P : Subgroup (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ}
    (he : ∀i j h a, elementary (Sum.inl i) (Sum.inl j) (Sum.inl_injective.ne h) a ∈ P)
    (hd : ∀i u, singleDiagonal (Sum.inl i) u ∈ P)
    (hr : ∀i j a, elementary (Sum.inr i) (Sum.inl j) Sum.inr_ne_inl a ∈ P) :
    rightFixer ≤ P := by
  intro U hU
  change (⟨U,hU⟩ : rightFixer).val ∈ P
  rw [rightFixer_decomposition]
  exact P.mul_mem (block_mem_of_generators ε hI he hd _) (rectangleLower_mem hr _)

lemma fixer_generated [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)
    (hI : MatrixNilKernel ε.toRingHom) (S : Finset ι) {P : Subgroup (Matrix ι ι R)ˣ}
    (he : ∀i j h a, j ∉ S → elementary i j h a ∈ P)
    (hd : ∀i u, i ∉ S → singleDiagonal i u ∈ P) : fixer S ≤ P := by
  intro U hU
  have hh : relabel (splitEquiv S) (relabel (splitEquiv S).symm U) ∈ P := by
    apply (rightFixer_generated ε hI (P := P.comap (relabel (splitEquiv S))) ?_ ?_ ?_)
      (relabel_fixer_right S hU)
    · intro i j h a
      change relabel (splitEquiv S) (elementary (Sum.inl i) (Sum.inl j) _ a) ∈ P
      rw [relabel_elementary]
      exact he i.val j.val (Subtype.coe_injective.ne h) a j.property
    · intro i u
      change relabel (splitEquiv S) (singleDiagonal (Sum.inl i) u) ∈ P
      rw [relabel_singleDiagonal]
      exact hd i.val u i.property
    · intro i j a
      change relabel (splitEquiv S) (elementary (Sum.inr i) (Sum.inl j) _ a) ∈ P
      rw [relabel_elementary]
      exact he i.val j.val (fun h => j.property (h ▸ i.property)) a j.property
  simpa only [LinearAlgebra.relabel_symm_apply] using hh

end
end SourceBurnside.Stability.MatrixGenerators

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

lemma evaluate_parabolic [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)
    (hI : MatrixNilKernel ε.toRingHom) (t : ι) : (parabolic (R := R) t).map evaluate = fixer {t} := by
  apply le_antisymm (evaluate_parabolic_le t)
  apply fixer_generated ε hI
  · intro i j h a hj
    exact ⟨root i j h a,root_mem_parabolic t i j h a (by simpa using hj),evaluate_root _ _ _ _⟩
  · intro i u hi
    exact ⟨diag i u,diag_mem_parabolic t i u (by simpa using hi),evaluate_diag _ _⟩

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators

end
end SourceBurnside.Stability.SmallPresentation

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Presentation_SmallSwapActions
attribute [-instance] _root_.OAI.SourceBurnside.Stability.SmallPresentation.columnAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

lemma evaluate_fixingGroup [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)
    (hI : MatrixNilKernel ε.toRingHom) (S : Finset ι) : (fixingGroup (R := R) S).map evaluate = fixer S := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    apply (Subgroup.closure_le _).mpr
    rintro x (⟨i,j,h,a,hj,rfl⟩ | ⟨i,u,hi,rfl⟩)
    · change evaluate (root i j h a) ∈ fixer S
      rw [evaluate_root]; exact elementary_mem_fixer _ _ _ _ _ hj
    · change evaluate (diag i u) ∈ fixer S
      rw [evaluate_diag]; exact singleDiagonal_mem_fixer _ _ _ hi
  · apply fixer_generated ε hI
    · intro i j h a hj
      exact ⟨root i j h a,Subgroup.subset_closure (Or.inl ⟨i,j,h,a,hj,rfl⟩),evaluate_root _ _ _ _⟩
    · intro i u hi
      exact ⟨diag i u,Subgroup.subset_closure (Or.inr ⟨i,u,hi,rfl⟩),evaluate_diag _ _⟩

lemma swap_normalizes_double_fixer [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)
    (hI : MatrixNilKernel ε.toRingHom) (t a : ι) (hta : t≠a)
    (ih : Function.Injective (evaluate (ι := {i // i∈Finset.univ.erase t}) (R := R)))
    {g : Group (ι := ι) (R := R)} (hg : g∈parabolic t) (he : evaluate g∈fixer {t,a}) :
    (swap t a hta)⁻¹*g*swap t a hta∈parabolic t := by
  rw [←evaluate_fixingGroup ε hI] at he
  obtain ⟨q,hq,hqg⟩ := he
  have hqg' : q=g := parabolic_faithful t ih (fixingGroup_le_parabolic {t,a} t (by simp) hq) hg hqg
  subst g
  have hh := swap_conjugate_fixingGroup_le t a hta hq
  change swap t a hta * q * (swap t a hta)⁻¹ ∈ parabolic t at hh
  simpa only [swap_inv] using hh

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.ColumnFrames
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
open scoped Matrix

end
end SourceBurnside.Stability.ColumnFrames

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Presentation_SmallFaithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Algebra (ZMod 2) R] [Fintype ι] [DecidableEq ι]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

variable (hI : MatrixNilKernel ε.toRingHom)

def cosetData (o a b : ι) (hoa : o≠a) (hob : o≠b) (hab : a≠b)
    (ih : Function.Injective (evaluate (ι := {i // i∈Finset.univ.erase o}) (R := R))) :
    CosetTransport.Data (H := Group (ι := ι) (R := R)) (F := ZMod 2) (ColumnFrames.rho (ι := ι) ε) where
  P := parabolic o
  o := ColumnFrames.standard ε o
  a := ColumnFrames.standard ε a
  b := ColumnFrames.standard ε b
  s := swap o a hoa
  t := swap a b hab
  fix _ hg := parabolic_fix ε o hg
  sa := by simpa only [Equiv.swap_apply_left] using swap_smul ε o a hoa o
  ss := swap_square o a hoa
  sb := by simpa only [Equiv.swap_apply_of_ne_of_ne hob.symm hab.symm] using swap_smul ε o a hoa b
  tm := swap_mem_parabolic o a b hab hoa.symm hob.symm
  ta := by simpa only [Equiv.swap_apply_left] using swap_smul ε a b hab a
  braid := swap_braid o a b hoa hob hab
  base := ColumnFrames.standard_triangle ε o a b
  oa := ColumnFrames.standard_edge ε o a hoa
  edge_map g u v h := ColumnFrames.edge_map ε (evaluate g) u v h
  tri_map g u v w h := ColumnFrames.triangle_map ε (evaluate g) u v w h
  edge_trans v hv := by
    obtain ⟨U,hU,he⟩ := ColumnFrames.edge_transitive ε hI o a hoa v hv
    rw [←evaluate_parabolic ε hI] at hU
    obtain ⟨p,hp,rfl⟩ := hU
    exact ⟨p,hp,he⟩
  tri_trans v w h₁ h₂ h₃ h := by
    obtain ⟨U,hU,hv,hw⟩ := ColumnFrames.triangle_transitive ε hI o a b hoa hob hab v w h₁ h₂ h₃ h
    rw [←evaluate_parabolic ε hI] at hU
    obtain ⟨p,hp,rfl⟩ := hU
    exact ⟨p,hp,hv,hw⟩
  qnorm g hg ha := by
    apply swap_normalizes_double_fixer ε hI o a hoa ih hg
    rw [ColumnFrames.mem_fixer_iff_standard ε]
    intro k hk
    rcases Finset.mem_insert.mp hk with hko | hk
    · simpa only [hko,column_smul] using parabolic_fix ε o hg
    · have hka : k=a := by simpa using hk
      subst k
      exact ha
  generates := parabolic_swap_generates o a hoa

include ε hI in
lemma evaluate_injective_step (hι : 5 < Fintype.card ι) (o a b : ι)
    (hoa : o≠a) (hob : o≠b) (hab : a≠b)
    (ih : Function.Injective (evaluate (ι := {i // i∈Finset.univ.erase o}) (R := R))) :
    Function.Injective (evaluate (ι := ι) (R := R)) := by
  let D := cosetData ε hI o a b hoa hob hab ih
  have hinj := CosetTransport.point_injective (ColumnFrames.rho ε) D
    (fun v => v.property) (ColumnFrames.cones ε hι)
  apply (MonoidHom.ker_eq_bot_iff evaluate).mp
  apply le_antisymm _ bot_le
  intro g hg
  have he : evaluate g=1 := hg
  have hp : CosetTransport.point (ColumnFrames.rho ε) D (QuotientGroup.mk g) =
      CosetTransport.point (ColumnFrames.rho ε) D (QuotientGroup.mk 1) := by
    simp only [CosetTransport.point_mk,column_smul,he,map_one]
  have hcos := hinj hp
  have hmem : g∈parabolic o := by
    change g∈D.P
    have hh := QuotientGroup.eq.mp hcos.symm
    simpa only [inv_one,one_mul] using hh
  exact parabolic_kernel_trivial o ih hmem he

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical
universe u v
variable {R : Type u} [Ring R] [Algebra (ZMod 2) R]

theorem evaluate_injective (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
    (ι : Type v) [Fintype ι] [DecidableEq ι] : Function.Injective (evaluate (ι := ι) (R := R)) := by
  suffices h : ∀n : ℕ, ∀(κ : Type v) [Fintype κ] [DecidableEq κ],
      Fintype.card κ=n → Function.Injective (evaluate (ι := κ) (R := R)) from h _ ι rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro κ _ _ hn
    by_cases hs : Fintype.card κ ≤ 5
    · exact evaluate_injective_small hs
    · have hb : 5 < Fintype.card κ := by omega
      obtain ⟨j⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 3) (β := κ) (by simpa using (by omega : 3 ≤ Fintype.card κ))
      apply evaluate_injective_step ε hI hb (j 0) (j 1) (j 2)
        (j.injective.ne (by decide)) (j.injective.ne (by decide)) (j.injective.ne (by decide))
      apply ih (Fintype.card {i : κ // i∈Finset.univ.erase (j 0)}) ?_ _ rfl
      rw [←hn]
      exact Fintype.card_subtype_lt (x := j 0) (Finset.notMem_erase _ _)

def equivalence (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
    (ι : Type v) [Fintype ι] [DecidableEq ι] : Group (ι := ι) (R := R) ≃* (Matrix ι ι R)ˣ :=
  MulEquiv.ofBijective evaluate ⟨evaluate_injective ε hI ι,evaluate_surjective ε hI⟩

@[simp] lemma equivalence_apply (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
    (ι : Type v) [Fintype ι] [DecidableEq ι] (g : Group (ι := ι) (R := R)) :
    equivalence ε hI ι g = evaluate g := rfl

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι κ : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

def elementaryGroup : Subgroup (Group (ι := ι) (R := R)) :=
  Subgroup.closure {g | ∃i j h a, g = root i j h a}

lemma root_mem_elementary (i j : ι) (h : i≠j) (a : R) :
    root i j h a ∈ elementaryGroup := Subgroup.subset_closure ⟨i,j,h,a,rfl⟩

lemma diag_normalizes_elementary (i : ι) (u : Rˣ) :
    diag i u ∈ Subgroup.normalizer (elementaryGroup (ι := ι) (R := R) : Set _) := by
  have hh (u : Rˣ) : elementaryGroup ≤
      elementaryGroup.comap (MulAut.conj (diag i u)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨t,j,h,b,rfl⟩
    change diag i u * root t j h b * (diag i u)⁻¹ ∈ elementaryGroup
    rw [diag_conjugate_root]
    exact root_mem_elementary _ _ _ _
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    exact hh u hx
  · intro hx
    have he := hh u⁻¹ hx
    change diag i u⁻¹ * (diag i u * x * (diag i u)⁻¹) * (diag i u⁻¹)⁻¹ ∈ elementaryGroup at he
    simpa only [diag_inv,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,
      inv_mul_cancel,mul_one] using he

instance elementary_normal : (elementaryGroup (ι := ι) (R := R)).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← supported_gen_all]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨g,rfl⟩
  cases g with
  | root i j h a => exact elementaryGroup.le_normalizer (root_mem_elementary i j h a)
  | diag i u => exact diag_normalizes_elementary i u

abbrev K1 := Group (ι := ι) (R := R) ⧸ elementaryGroup

def toK1 : Group (ι := ι) (R := R) →* K1 (ι := ι) (R := R) :=
  QuotientGroup.mk' elementaryGroup

@[simp] lemma toK1_root (i j : ι) (h : i≠j) (a : R) : toK1 (root i j h a) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (root_mem_elementary i j h a)

@[simp] lemma diag_one (i : ι) : diag i (1 : Rˣ) = 1 := by
  apply local_faithful {i} (by simp)
    (diag_mem_local _ _ _ (by simp)) (localGroup _).one_mem
  simp [MatrixGenerators.singleDiagonal]

variable [Algebra (ZMod 2) R]

@[simp] lemma toK1_swap (i j : ι) (h : i≠j) : toK1 (swap (R := R) i j h) = 1 := by
  simp [swap,minus_one_unit]

lemma toK1_diag_eq (i j : ι) (u : Rˣ) : toK1 (diag i u) = toK1 (diag j u) := by
  by_cases h : i=j
  · subst j; rfl
  have he := congrArg (toK1 (R := R)) (swap_conjugate_diag i j h i u)
  simpa using he

variable [Fintype κ] [DecidableEq κ]

omit [Algebra (ZMod 2) R] in
lemma elementary_inclusion (e : ι ↪ κ) : elementaryGroup (R := R) ≤
    elementaryGroup.comap (inclusion e) := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨i,j,h,a,rfl⟩
  change inclusion e (root i j h a) ∈ elementaryGroup
  change inclusion e (gen (.root i j h a)) ∈ elementaryGroup
  rw [inclusion_gen]
  exact root_mem_elementary _ _ _ _

def K1map (e : ι ↪ κ) : K1 (ι := ι) (R := R) →* K1 (ι := κ) (R := R) :=
  QuotientGroup.map _ _ (inclusion e) (elementary_inclusion e)

omit [Algebra (ZMod 2) R] in
@[simp] lemma K1map_mk (e : ι ↪ κ) (g : Group (ι := ι) (R := R)) :
    K1map e (toK1 g) = toK1 (inclusion e g) := rfl

omit [Fintype ι] [Algebra (ZMod 2) R] in
lemma supported_range (S : Finset ι) : supported (R := R) S ≤
    (FreeGroup.map (Generator.map (Function.Embedding.subtype (·∈S)))).range := by
  apply (Subgroup.closure_le _).mpr
  rintro w ⟨g,hg,rfl⟩
  cases g with
  | root i j h a =>
    obtain ⟨hi,hj⟩ := Finset.insert_subset_iff.mp hg
    have hj := Finset.singleton_subset_iff.mp hj
    refine ⟨FreeGroup.of (.root ⟨i,hi⟩ ⟨j,hj⟩ (fun he => h (congrArg Subtype.val he)) a),?_⟩
    rw [FreeGroup.map.of]
    rfl
  | diag i u =>
    refine ⟨FreeGroup.of (.diag ⟨i,Finset.singleton_subset_iff.mp hg⟩ u),?_⟩
    rw [FreeGroup.map.of]
    rfl

def unitWord (i : κ) : FreeGroup (Generator ι R) →* K1 (ι := κ) (R := R) :=
  FreeGroup.lift fun g => match g with
    | .root _ _ _ _ => 1
    | .diag _ u => toK1 (diag i u)

lemma unitWord_map (i : κ) (e : ι ↪ κ) : unitWord (R := R) i =
    (toK1.comp (inclusion e)).comp (PresentedGroup.mk relations) := by
  apply FreeGroup.ext_hom
  intro g
  cases g with
  | root a b h r =>
    change 1 = toK1 (inclusion e (gen (.root a b h r)))
    rw [inclusion_gen]
    exact (toK1_root _ _ _ _).symm
  | diag a u =>
    change toK1 (diag i u) = toK1 (inclusion e (gen (.diag a u)))
    rw [inclusion_gen]
    exact toK1_diag_eq _ _ _

lemma unitWord_relation (i : κ) (hκ : 5 ≤ Fintype.card κ)
    (w : FreeGroup (Generator ι R)) (hw : w ∈ relations) : unitWord (R := R) i w = 1 := by
  obtain ⟨S,hS,hwS⟩ := hw.2
  obtain ⟨v,hv⟩ := supported_range S hwS
  let eS := Function.Embedding.subtype (·∈S)
  have hvmat : matrixWord v = 1 := by
    apply embed_injective eS
    rw [map_one]
    have hh := congrArg matrixWord hv
    rw [← MonoidHom.comp_apply,matrixWord_map,MonoidHom.comp_apply,hw.1] at hh
    exact hh
  have hvr : v∈relations := ⟨hvmat,Finset.univ,by simpa using hS,by rw [supported_univ]; trivial⟩
  obtain ⟨j⟩ := Function.Embedding.nonempty_of_card_le
    (α := {x : ι // x∈S}) (β := κ) (by simpa using hS.trans hκ)
  have he : (unitWord (R := R) i).comp (FreeGroup.map (Generator.map eS)) =
      unitWord (R := R) (ι := {x : ι // x∈S}) i := by
    apply FreeGroup.ext_hom
    intro g
    cases g <;> rfl
  rw [← hv, ← MonoidHom.comp_apply, he, unitWord_map i j]
  change toK1 (inclusion j (PresentedGroup.mk relations v)) = 1
  rw [PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure hvr),map_one,map_one]

def collapseGroup (i : κ) (hκ : 5 ≤ Fintype.card κ) :
    Group (ι := ι) (R := R) →* K1 (ι := κ) (R := R) :=
  PresentedGroup.toGroup (unitWord_relation i hκ)

@[simp] lemma collapseGroup_root (i : κ) (hκ : 5 ≤ Fintype.card κ)
    (a b : ι) (h : a≠b) (r : R) : collapseGroup i hκ (root a b h r) = 1 :=
  PresentedGroup.toGroup.of _

@[simp] lemma collapseGroup_diag (i : κ) (hκ : 5 ≤ Fintype.card κ)
    (a : ι) (u : Rˣ) : collapseGroup i hκ (diag a u) = toK1 (diag i u) :=
  PresentedGroup.toGroup.of _

lemma collapseGroup_kills (i : κ) (hκ : 5 ≤ Fintype.card κ) :
    elementaryGroup (ι := ι) (R := R) ≤ (collapseGroup i hκ).ker := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨a,b,h,r,rfl⟩
  exact collapseGroup_root i hκ a b h r

def collapse (i : κ) (hκ : 5 ≤ Fintype.card κ) :
    K1 (ι := ι) (R := R) →* K1 (ι := κ) (R := R) :=
  QuotientGroup.lift _ (collapseGroup i hκ) (collapseGroup_kills i hκ)

@[simp] lemma collapse_mk (i : κ) (hκ : 5 ≤ Fintype.card κ)
    (g : Group (ι := ι) (R := R)) : collapse i hκ (toK1 g) = collapseGroup i hκ g := rfl

lemma collapse_left (e : ι ↪ κ) (i : ι) (hι : 5 ≤ Fintype.card ι) :
    (collapse (R := R) i hι).comp (K1map e) = MonoidHom.id _ := by
  apply QuotientGroup.monoidHom_ext
  change (collapseGroup i hι).comp (inclusion e) = toK1
  apply PresentedGroup.ext
  intro g
  cases g with
  | root a b h r =>
    change collapseGroup i hι (inclusion e (gen (.root a b h r))) = toK1 (root a b h r)
    rw [inclusion_gen]
    exact (collapseGroup_root _ _ _ _ _ _).trans (toK1_root _ _ _ _).symm
  | diag a u =>
    change collapseGroup i hι (inclusion e (gen (.diag a u))) = toK1 (diag a u)
    rw [inclusion_gen]
    exact (collapseGroup_diag _ _ _ _).trans (toK1_diag_eq _ _ _)

lemma collapse_right (e : ι ↪ κ) (i : ι) (hι : 5 ≤ Fintype.card ι) :
    (K1map (R := R) e).comp (collapse i hι) = MonoidHom.id _ := by
  apply QuotientGroup.monoidHom_ext
  change (K1map e).comp (collapseGroup i hι) = toK1
  apply PresentedGroup.ext
  intro g
  cases g with
  | root a b h r =>
    change K1map e (collapseGroup i hι (root a b h r)) = toK1 (root a b h r)
    simp
  | diag a u =>
    change K1map e (collapseGroup i hι (diag a u)) = toK1 (diag a u)
    rw [collapseGroup_diag,K1map_mk]
    change toK1 (inclusion e (gen (.diag i u))) = _
    rw [inclusion_gen]
    exact toK1_diag_eq _ _ _

def K1equivalence (e : ι ↪ κ) (hι : 5 ≤ Fintype.card ι) :
    K1 (ι := ι) (R := R) ≃* K1 (ι := κ) (R := R) := by
  have hnon : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let i := Classical.choice hnon
  exact
    { toFun := K1map e
      invFun := collapse i hι
      left_inv := DFunLike.congr_fun (collapse_left e i hι)
      right_inv := DFunLike.congr_fun (collapse_right e i hι)
      map_mul' := (K1map e).map_mul }

end
end SourceBurnside.Stability.SmallPresentation

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_DiagonalActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.SteinbergAction
noncomputable section
open Classical Steinberg MatrixGenerators
variable {n : ℕ} {R : Type*} [Ring R]

def scaleHom (u : Fin n → Rˣ) : Steinberg n R →* Steinberg n R :=
  Steinberg.lift (fun p a => x p ((u p.row).val*a*(u p.col).inv))
    (by intro p a b; simp only [mul_add,add_mul,x_add])
    (by intro p q h₁ h₂ a b; exact x_commute p q h₁ h₂ _ _)
    (by
      intro i j k hij hjk hik a b
      rw [x_mul i j k hij hjk hik]
      congr 1
      calc (u i).val*a*(u j).inv*((u j).val*b*(u k).inv) =
          (u i).val*a*((u j).inv*(u j).val)*b*(u k).inv := by noncomm_ring
           _ = (u i).val*(a*b)*(u k).inv := by rw [(u j).inv_val]; noncomm_ring)

@[simp] lemma scaleHom_x (u : Fin n → Rˣ) (p : Root n) (a : R) :
    scaleHom u (x p a) = x p ((u p.row).val*a*(u p.col).inv) :=
  Steinberg.lift_x _ _ _ _ _ _

lemma scaleHom_one : scaleHom (fun _ : Fin n => (1 : Rˣ)) = MonoidHom.id _ := by
  apply Steinberg.hom_ext
  intro p a
  simp

lemma scaleHom_mul (u v : Fin n → Rˣ) :
    scaleHom (fun i => u i*v i) = (scaleHom u).comp (scaleHom v) := by
  apply Steinberg.hom_ext
  intro p a
  simp only [MonoidHom.comp_apply,scaleHom_x,Units.val_mul]
  congr 1
  noncomm_ring

def scale (u : Fin n → Rˣ) : MulAut (Steinberg n R) where
  toFun := scaleHom u
  invFun := scaleHom (fun i => (u i)⁻¹)
  left_inv g := by
    have hh := DFunLike.congr_fun (scaleHom_mul (fun i => (u i)⁻¹) u) g
    simpa only [inv_mul_cancel,scaleHom_one,MonoidHom.id_apply,MonoidHom.comp_apply] using hh.symm
  right_inv g := by
    have hh := DFunLike.congr_fun (scaleHom_mul u (fun i => (u i)⁻¹)) g
    simpa only [mul_inv_cancel,scaleHom_one,MonoidHom.id_apply,MonoidHom.comp_apply] using hh.symm
  map_mul' := (scaleHom u).map_mul

@[simp] lemma scale_apply (u : Fin n → Rˣ) (g : Steinberg n R) : scale u g = scaleHom u g := rfl
@[simp] lemma scale_x (u : Fin n → Rˣ) (p : Root n) (a : R) :
    scale u (x p a) = x p ((u p.row).val*a*(u p.col).inv) := scaleHom_x u p a

lemma elementary_eq_e (p : Root n) (a : R) : elementary p.row p.col p.ne a = Elementary.e p a := by
  apply Units.ext
  rfl

end
end SourceBurnside.Stability.SteinbergAction

end
section
namespace SourceBurnside.Stability.SteinbergAction
noncomputable section
open Classical Steinberg MatrixGenerators
variable {n : ℕ} {R : Type*} [Ring R]

abbrev GLGenerator := SmallPresentation.Generator (Fin n) R

def generatorAction : GLGenerator (n := n) (R := R) → MulAut (Steinberg n R)
  | .root i j h a => MulAut.conj (x ⟨i,j,h⟩ a)
  | .diag i u => scale (fun j => if j=i then u else 1)

def wordAction : FreeGroup (GLGenerator (n := n) (R := R)) →* MulAut (Steinberg n R) :=
  FreeGroup.lift generatorAction

@[simp] lemma wordAction_of (s : GLGenerator (n := n) (R := R)) :
    wordAction (FreeGroup.of s) = generatorAction s := FreeGroup.lift_apply_of

end
end SourceBurnside.Stability.SteinbergAction

end
section
namespace SourceBurnside.Stability.MatrixK1
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι κ : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

lemma evaluate_elementary : SmallPresentation.elementaryGroup.map
    (SmallPresentation.evaluate (ι := ι) (R := R)) = E := by
  rw [SmallPresentation.elementaryGroup,MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨x,⟨i,j,h,a,rfl⟩,rfl⟩
    exact ⟨i,j,h,a,SmallPresentation.evaluate_root _ _ _ _⟩
  · rintro ⟨i,j,h,a,rfl⟩
    exact ⟨SmallPresentation.root i j h a,⟨i,j,h,a,rfl⟩,
      SmallPresentation.evaluate_root _ _ _ _⟩

variable [Algebra (ZMod 2) R]
variable (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
include ε hI

lemma evaluate_mem_iff (g : SmallPresentation.Group (ι := ι) (R := R)) :
    SmallPresentation.evaluate g ∈ E ↔ g ∈ SmallPresentation.elementaryGroup := by
  rw [←evaluate_elementary]
  constructor
  · rintro ⟨x,hx,he⟩
    exact SmallPresentation.evaluate_injective ε hI ι he ▸ hx
  · intro hg; exact ⟨g,hg,rfl⟩

variable [Fintype κ] [DecidableEq κ]

lemma embed_mem_iff (e : ι ↪ κ) (hι : 5≤Fintype.card ι) (g : (Matrix ι ι R)ˣ) :
    embed e g ∈ E ↔ g∈E := by
  obtain ⟨x,rfl⟩ := SmallPresentation.evaluate_surjective ε hI g
  rw [←SmallPresentation.evaluate_inclusion_apply,evaluate_mem_iff ε hI,evaluate_mem_iff ε hI]
  constructor
  · intro hx
    have hh : SmallPresentation.K1map e (SmallPresentation.toK1 x) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hx
    have hinj := (SmallPresentation.K1equivalence (R := R) e hι).injective
    have hq : SmallPresentation.toK1 x = 1 := hinj (hh.trans (map_one _).symm)
    exact (QuotientGroup.eq_one_iff _).mp hq
  · intro hx
    exact SmallPresentation.elementary_inclusion (R := R) e hx

end
end SourceBurnside.Stability.MatrixK1

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Frames_ElementaryFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability.MatrixK1
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι κ : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

lemma representation_range (n : ℕ) :
    (Elementary.representation (n := n) (R := R)).range = E := by
  apply le_antisymm
  · rintro g ⟨u,rfl⟩
    have h : (⊤ : Subgroup (Steinberg n R)) ≤ E.comap Elementary.representation := by
      rw [←Steinberg.closure_range_x]
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨⟨p,a⟩,rfl⟩
      change Elementary.representation (Steinberg.x p a) ∈ E
      rw [Elementary.representation_x,←SteinbergAction.elementary_eq_e]
      exact elementary_mem _ _ _ _
    exact h (Subgroup.mem_top u)
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨i,j,h,a,rfl⟩
    exact ⟨Steinberg.x ⟨i,j,h⟩ a,(Elementary.representation_x _ _).trans
      (SteinbergAction.elementary_eq_e ⟨i,j,h⟩ a).symm⟩

variable [Algebra (ZMod 2) R]
lemma permutation_mem (p : Equiv.Perm ι) : permutation (R := R) p ∈ E := by
  induction p using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul p i j h ih =>
    rw [map_mul]
    apply E.mul_mem _ ih
    rw [←SmallPresentation.evaluate_swap i j h,←evaluate_elementary]
    exact ⟨SmallPresentation.swap i j h,
      (QuotientGroup.eq_one_iff _).mp (SmallPresentation.toK1_swap i j h),rfl⟩

variable [Fintype κ] [DecidableEq κ]

omit [Algebra (ZMod 2) R] in
lemma block_mem {U : (Matrix ι ι R)ˣ} (hU : U∈E) : (blockInclusion (κ := κ) U) ∈ E := by
  rw [←embed_sumInl]
  have he : E (R := R) (ι := ι) ≤ (E (R := R) (ι := ι ⊕ κ)).comap (embed (Function.Embedding.inl (β := κ))) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨i,j,h,a,rfl⟩
    change embed _ (elementary i j h a) ∈ E
    rw [embed_elementary]
    exact elementary_mem _ _ _ _
  exact he hU

omit [Algebra (ZMod 2) R] in
lemma rectangle_mem (A : κ × ι → Multiplicative R) : rectangleLower A ∈ E :=
  rectangleLower_mem (fun _ _ _ => elementary_mem _ _ _ _) A

variable (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)

include ε hI in
lemma block_mem_iff (hι : 5≤Fintype.card ι) (U : (Matrix ι ι R)ˣ) :
    blockInclusion (κ := κ) U ∈ E ↔ U∈E := by
  rw [←embed_sumInl]
  exact embed_mem_iff ε hI _ hι U

end SourceBurnside.Stability.MatrixK1

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_LocallyFiniteActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability.UnorderedStabilizer
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators MatrixK1
open scoped Pointwise
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

def rightEquiv : κ ≃ Set.range (rightVertex (ι := ι) (κ := κ) ε) :=
  Equiv.ofInjective _ (rightVertex_injective ε)

def perm : K (ι := ι) (κ := κ) ε →* Equiv.Perm κ where
  toFun U := (rightEquiv (ι := ι) (κ := κ) ε).trans
    ((MulAction.toPermHom (K (ι := ι) (κ := κ) ε)
      (Set.range (rightVertex (ι := ι) (κ := κ) ε))) U) |>.trans (rightEquiv (ι := ι) (κ := κ) ε).symm
  map_one' := by ext j; simp
  map_mul' U V := by ext j; simp [Equiv.trans_apply, mul_smul]

lemma perm_spec (U : K (ι := ι) (κ := κ) ε) (j : κ) :
    U.val.val • rightVertex (ι := ι) ε j = rightVertex (ι := ι) ε (perm ε U j) := by
  change (U • (rightEquiv (ι := ι) (κ := κ) ε j)).val = _
  exact ((congrArg Subtype.val ((rightEquiv (ι := ι) (κ := κ) ε).apply_symm_apply (U • rightEquiv (ι := ι) (κ := κ) ε j)))).symm

omit [Algebra (ZMod 2) R] in
lemma permRight_eq (p : Equiv.Perm κ) :
    permRight (R := R) (ι := ι) p = permutation (Equiv.sumCongr (Equiv.refl ι) p) := rfl

lemma permRight_smul (p : Equiv.Perm κ) (j : κ) :
    permRight (R := R) (ι := ι) p • rightVertex (ι := ι) ε j = rightVertex (ι := ι) ε (p j) := by
  apply Subtype.ext
  change permutation (Equiv.sumCongr (Equiv.refl ι) p) •
      (Pi.single (Sum.inr j) 1 : ι ⊕ κ → R) = Pi.single (Sum.inr (p j)) 1
  exact permutation_smul_single _ _

def fixedPart (U : K (ι := ι) (κ := κ) ε) : rightFixer (ι := ι) (κ := κ) (R := R) :=
  ⟨U.val.val * permRight ((perm ε U)⁻¹), by
    simp only [rightFixer,Subgroup.mem_iInf,MulAction.mem_stabilizer_iff]
    intro j
    have h : (U.val.val * permRight ((perm ε U)⁻¹)) • rightVertex (ι := ι) ε j = rightVertex (ι := ι) ε j := by
      rw [mul_smul,permRight_smul,perm_spec]
      simp
    exact congrArg Subtype.val h⟩

def topBlock (U : K (ι := ι) (κ := κ) ε) : (Matrix ι ι R)ˣ :=
  rightProjection (fixedPart ε U)

lemma topBlock_entry (U : K (ι := ι) (κ := κ) ε) (i j : ι) :
    (topBlock ε U).val i j = U.val.val.val (Sum.inl i) (Sum.inl j) := by
  change (U.val.val.val * (permRight (R := R) (ι := ι) ((perm ε U)⁻¹)).val) (Sum.inl i) (Sum.inl j) = _
  rw [permRight_eq,mul_permutation]
  rfl

lemma shape (U : K (ι := ι) (κ := κ) ε) :
    U.val.val.val = Matrix.fromBlocks (topBlock ε U).val 0
      (U.val.val.val.submatrix Sum.inr Sum.inl) (permutation (perm ε U)).val := by
  ext i j
  cases j with
  | inl j => cases i with
    | inl i => exact (topBlock_entry ε U i j).symm
    | inr i => rfl
  | inr j =>
    have h := congrArg (fun v : ColumnFrames.Vertex (ι := ι ⊕ κ) ε => v.val i) (perm_spec ε U j)
    change Matrix.mulVec U.val.val.val (Pi.single (Sum.inr j) 1) i =
      (Pi.single (Sum.inr (perm ε U j)) (1 : R) : ι ⊕ κ → R) i at h
    rw [Matrix.mulVec_single_one] at h
    cases i with
    | inl i => simpa [Matrix.fromBlocks,Pi.single_apply] using h
    | inr i => simpa [Matrix.fromBlocks,Pi.single_apply,permutation_entry,eq_comm,Equiv.eq_symm_apply] using h

def projectionGL : K (ι := ι) (κ := κ) ε →* (Matrix ι ι R)ˣ where
  toFun := topBlock ε
  map_one' := by
    apply Units.ext
    ext i j
    simpa [Matrix.one_apply] using topBlock_entry ε 1 i j
  map_mul' U V := by
    apply Units.ext
    ext i j
    rw [topBlock_entry]
    change (U.val.val.val*V.val.val.val) (Sum.inl i) (Sum.inl j) = _
    rw [shape ε U,shape ε V,Matrix.fromBlocks_multiply]
    simp

variable (hI : MatrixNilKernel ε.toRingHom) (hι : 5 ≤ Fintype.card ι)

lemma section_mem (A : E (R := R) (ι := ι)) (p : Equiv.Perm κ) :
    (⟨blockInclusion A.val * permRight p,
      E.mul_mem (block_mem A.property) (permutation_mem _)⟩ : E (R := R) (ι := ι ⊕ κ)) ∈ K ε := by
  rw [MulAction.mem_stabilizer_iff]
  ext v
  constructor
  · rintro ⟨w,⟨j,rfl⟩,rfl⟩
    have he : (blockInclusion A.val * permRight p) • rightVertex (ι := ι) ε j = rightVertex (ι := ι) ε (p j) := by
      rw [mul_smul,permRight_smul]
      apply Subtype.ext
      exact block_smul_right A.val (p j)
    exact ⟨p j,he.symm⟩
  · rintro ⟨j,rfl⟩
    refine ⟨rightVertex ε (p⁻¹ j),⟨p⁻¹ j,rfl⟩,?_⟩
    change (blockInclusion A.val * permRight p) • rightVertex ε (p⁻¹ j) = _
    rw [mul_smul,permRight_smul]
    change blockInclusion A.val • rightVertex (ι := ι) ε (p (p.symm j)) = _
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact block_smul_right A.val j

def sectionElement (A : E (R := R) (ι := ι)) (p : Equiv.Perm κ) : K (ι := ι) (κ := κ) ε :=
  ⟨⟨blockInclusion A.val * permRight p,
      E.mul_mem (block_mem A.property) (permutation_mem _)⟩,section_mem ε A p⟩

lemma section_perm (A : E (R := R) (ι := ι)) (p : Equiv.Perm κ) :
    perm ε (sectionElement ε A p) = p := by
  ext j
  apply rightVertex_injective (ι := ι) (κ := κ) ε
  rw [←perm_spec]
  change (blockInclusion A.val * permRight p) • rightVertex ε j = _
  rw [mul_smul,permRight_smul]
  apply Subtype.ext
  exact block_smul_right A.val (p j)

end SourceBurnside.Stability.UnorderedStabilizer

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_FiniteNormalHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability

attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical CategoryTheory CategoryTheory.Limits Module MatrixK1 MatrixGenerators
open scoped Pointwise
namespace FrameStabilizer
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2)
variable [LinearOrder (ColumnFrames.Vertex (ι := ι ⊕ κ) ε)]

abbrev A := Frames.chainRep (G (R := R) (ι := ι) (κ := κ)) (ρ := rho (ι := ι) (κ := κ) ε)
  (independent_action ε) (Fintype.card κ)
abbrev b := Frames.frameBasis (F := ZMod 2) (rho (ι := ι) (κ := κ) ε) (Fintype.card κ)

attribute [local instance] OAI.SourceBurnside.Stability.FrameStabilizer.instMulActionSubtypeUnitsMatrixSumMemSubgroupGIndex
lemma monomial (g : G (R := R) (ι := ι) (κ := κ)) (x : index (ι := ι) (κ := κ) ε) :
    ∃c : ℚˣ, (A ε).ρ g (b ε x) = c.val • b ε (g • x) :=
  Frames.frame_action_monomial (rho ε) (G (R := R) (ι := ι) (κ := κ)) (independent_action ε) _ g x

abbrev characterS := MonomialInduction.character (base (ι := ι) (κ := κ) ε) (A ε) (b ε) (monomial ε)
def characterK : UnorderedStabilizer.K (ι := ι) (κ := κ) ε →* ℚˣ :=
  (characterS ε).comp (stabilizerEquiv (ι := ι) (κ := κ) ε).symm.toMonoidHom

lemma characterK_spec (s : UnorderedStabilizer.K (ι := ι) (κ := κ) ε) :
    Frames.labelMap (s.val • ·) (Frames.basis (base (ι := ι) (κ := κ) ε).val) =
      (characterK ε s).val • Frames.basis (base (ι := ι) (κ := κ) ε).val := by
  have h := MonomialInduction.character_spec (base (ι := ι) (κ := κ) ε) (A ε) (b ε) (monomial ε)
    ((stabilizerEquiv (ι := ι) (κ := κ) ε).symm s)
  have hh := congrArg Subtype.val h
  change Frames.labelMap (s.val • ·) (b ε (base (ι := ι) (κ := κ) ε)).val =
    (characterK ε s).val • (b ε (base (ι := ι) (κ := κ) ε)).val at hh
  simpa only [Frames.frameBasis_val] using hh

lemma perm_kernel_character : (UnorderedStabilizer.perm (ι := ι) (κ := κ) ε).ker ≤ (characterK ε).ker := by
  intro s hs
  apply MonoidHom.mem_ker.mpr
  apply Units.ext
  apply MonomialInduction.smul_basis_injective (base (ι := ι) (κ := κ) ε) (A ε) (b ε)
  dsimp only
  apply Subtype.ext
  change (characterK ε s).val • (b ε (base (ι := ι) (κ := κ) ε)).val = (1 : ℚ) • (b ε (base (ι := ι) (κ := κ) ε)).val
  rw [Frames.frameBasis_val,←characterK_spec,one_smul]
  apply Frames.labelMap_basis_fixed
  intro v hv
  obtain ⟨j,rfl⟩ := (base_coe (ι := ι) (κ := κ) ε ▸ (show v∈((base (ι := ι) (κ := κ) ε).val : Set (V (ι := ι) (κ := κ) ε)) from hv))
  have he := UnorderedStabilizer.perm_spec ε s j
  rw [MonoidHom.mem_ker.mp hs] at he
  exact he

end FrameStabilizer
end SourceBurnside.Stability

namespace SourceBurnside.Stability.FrameStabilizer
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical CategoryTheory CategoryTheory.Limits Module MatrixK1 MatrixGenerators
open scoped Pointwise
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2)
variable [LinearOrder (ColumnFrames.Vertex (ι := ι ⊕ κ) ε)]

local instance instMulActionSubtypeUnitsMatrixSumMemSubgroupGIndex_1 : MulAction (G (R := R) (ι := ι) (κ := κ)) (index (ι := ι) (κ := κ) ε) :=
  Frames.indexAction (rho ε) (G (R := R) (ι := ι) (κ := κ)) (independent_action ε) (Fintype.card κ)

def characterP : Equiv.Perm κ →* ℚˣ :=
  (UnorderedStabilizer.perm (ι := ι) (κ := κ) ε).liftOfRightInverseAux
    (UnorderedStabilizer.sectionElement ε 1)
    (UnorderedStabilizer.section_perm ε 1) (characterK ε) (perm_kernel_character ε)

lemma characterP_comp : (characterP (ι := ι) (κ := κ) ε).comp (UnorderedStabilizer.perm (ι := ι) ε) = characterK (ι := ι) (κ := κ) ε := by
  apply MonoidHom.ext
  intro s
  exact (UnorderedStabilizer.perm (ι := ι) (κ := κ) ε).liftOfRightInverseAux_comp_apply
    (UnorderedStabilizer.sectionElement ε 1) (UnorderedStabilizer.section_perm ε 1)
    (characterK ε) (perm_kernel_character ε) s

lemma characterP_swap (i j : κ) (hij : i≠j) :
    characterP (ι := ι) ε (Equiv.swap i j) = -1 := by
  let s := UnorderedStabilizer.sectionElement (ι := ι) ε 1 (Equiv.swap i j)
  change characterK ε s = -1
  apply Units.ext
  apply MonomialInduction.smul_basis_injective (base (ι := ι) (κ := κ) ε) (A ε) (b ε)
  dsimp only
  apply Subtype.ext
  change (characterK ε s).val • (b ε (base (ι := ι) (κ := κ) ε)).val =
    (-1 : ℚ) • (b ε (base (ι := ι) (κ := κ) ε)).val
  rw [Frames.frameBasis_val,←characterK_spec,neg_one_smul]
  apply Frames.labelMap_basis_transposition (s.val • ·) (base (ι := ι) (κ := κ) ε).val
    (right (ι := ι) (κ := κ) ε i) (right (ι := ι) (κ := κ) ε j)
  · change right (ι := ι) (κ := κ) ε i ∈ ((base (ι := ι) (κ := κ) ε).val : Set (V (ι := ι) (κ := κ) ε))
    rw [base_coe]; exact ⟨i,rfl⟩
  · change right (ι := ι) (κ := κ) ε j ∈ ((base (ι := ι) (κ := κ) ε).val : Set (V (ι := ι) (κ := κ) ε))
    rw [base_coe]; exact ⟨j,rfl⟩
  · exact (UnorderedStabilizer.rightVertex_injective ε).ne hij
  · change s.val.val • right (ι := ι) (κ := κ) ε i = right (ι := ι) (κ := κ) ε j
    simpa only [s,UnorderedStabilizer.section_perm,Equiv.swap_apply_left] using
      UnorderedStabilizer.perm_spec ε s i
  · change s.val.val • right (ι := ι) (κ := κ) ε j = right (ι := ι) (κ := κ) ε i
    simpa only [s,UnorderedStabilizer.section_perm,Equiv.swap_apply_right] using
      UnorderedStabilizer.perm_spec ε s j
  · intro v hv hvi hvj
    have hv' : v∈Set.range (right (ι := ι) (κ := κ) ε) := by
      rw [←base_coe]; exact hv
    obtain ⟨l,rfl⟩ := hv'
    have hli : l≠i := fun he => hvi (congrArg (right (ι := ι) (κ := κ) ε) he)
    have hlj : l≠j := fun he => hvj (congrArg (right (ι := ι) (κ := κ) ε) he)
    change s.val.val • right (ι := ι) (κ := κ) ε l = right (ι := ι) (κ := κ) ε l
    simpa only [s,UnorderedStabilizer.section_perm,Equiv.swap_apply_of_ne_of_ne hli hlj] using
      UnorderedStabilizer.perm_spec ε s l

end SourceBurnside.Stability.FrameStabilizer

namespace SourceBurnside.Stability
open Classical CategoryTheory CategoryTheory.Limits MatrixK1
namespace H2FrameEdge
variable {R Ω : Type} [Ring R] [Algebra (ZMod 2) R] [Fintype Ω] [DecidableEq Ω]
variable (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
variable [LinearOrder (ColumnFrames.Vertex (ι := Ω) ε)]

abbrev chains (k : ℕ) := Frames.chainRep (E (R := R) (ι := Ω)) (ρ := ColumnFrames.rho ε)
  (ColumnRelabel.independent_action ε) k

def augmentation : chains (Ω := Ω) ε 1 ⟶ Rep.trivial ℚ (E (R := R) (ι := Ω)) ℚ :=
  Frames.differentialRep (E (R := R)) (ColumnFrames.rho ε) (ColumnRelabel.independent_action ε) 0 ≫
    (Frames.degreeZeroIso (E (R := R)) (ColumnFrames.rho ε) (ColumnRelabel.independent_action ε)).hom

end H2FrameEdge
end SourceBurnside.Stability

namespace SourceBurnside.Stability.UnorderedStabilizer
open Classical MatrixGenerators MatrixK1 CategoryTheory
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

def complementary : E (R := R) (ι := ι) →* K (ι := ι) (κ := κ) ε where
  toFun A := sectionElement ε A 1
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change blockInclusion 1 * permRight 1 = 1
    simp
  map_mul' A B := by
    apply Subtype.ext
    apply Subtype.ext
    change blockInclusion (A.val*B.val) * permRight 1 =
      (blockInclusion A.val * permRight 1) * (blockInclusion B.val * permRight 1)
    simp

end SourceBurnside.Stability.UnorderedStabilizer

namespace SourceBurnside.Stability
open Classical CategoryTheory MatrixGenerators MatrixK1 Representation

namespace SingletonFrameEdge
variable {R ι : Type} [Ring R] [Algebra (ZMod 2) R] [Fintype ι] [DecidableEq ι]
variable (ε : R →ₐ[ZMod 2] ZMod 2)
variable [LinearOrder (ColumnFrames.Vertex (ι := ι ⊕ Fin 1) ε)]
local notation "G" => E (R := R) (ι := ι ⊕ Fin 1)
local notation "x₀" => FrameStabilizer.base (ι := ι) (κ := Fin 1) ε
local notation "S" => MulAction.stabilizer G x₀

lemma base_singleton : (x₀).val = {FrameStabilizer.right (ι := ι) ε (0 : Fin 1)} := by
  simp [FrameStabilizer.base,Finset.univ_unique]

attribute [local instance] OAI.SourceBurnside.Stability.SingletonFrameEdge.instMulActionSubtypeUnitsMatrixSumFinOfNatNatMemSubgroupEIndex
def lift : E (R := R) (ι := ι) →* S :=
  (FrameStabilizer.stabilizerEquiv (ι := ι) (κ := Fin 1) ε).symm.toMonoidHom.comp
    (UnorderedStabilizer.complementary ε)

def blockHom : E (R := R) (ι := ι) →* G := (S).subtype.comp (lift (ι := ι) ε)

end SingletonFrameEdge
end SourceBurnside.Stability

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_RankActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability.ElementaryRanks
open Classical CategoryTheory MatrixGenerators MatrixK1
variable {R : Type} [Ring R]

def representation {n : ℕ} : Steinberg n R →* Group (R := R) n :=
  Elementary.representation.codRestrict _ (fun u => by
    change Elementary.representation u ∈ E
    rw [←representation_range (R := R) n]
    exact ⟨u,rfl⟩)

@[simp] lemma representation_val {n : ℕ} (u : Steinberg n R) :
    (representation u).val = Elementary.representation u := rfl

def root {n : ℕ} (p : Root n) (a : R) : Group (R := R) n := representation (Steinberg.x p a)
@[simp] lemma root_val {n : ℕ} (p : Root n) (a : R) :
    (root p a).val=elementary p.row p.col p.ne a := by
  simp only [root,representation_val,Elementary.representation_x,SteinbergAction.elementary_eq_e]

variable [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)

def next (n : ℕ) : Group (R := R) n →* Group (R := R) (n+1) :=
  letI : LinearOrder (ColumnFrames.Vertex (ι := Fin n ⊕ Fin 1) ε) := linearOrderOfSTO WellOrderingRel
  (ColumnRelabel.elementaryEquiv (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n+1))).toMonoidHom.comp
    (SingletonFrameEdge.blockHom ε)

end SourceBurnside.Stability.ElementaryRanks

end

end OAI
end


