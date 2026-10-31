-- Prove2me | Definitions.Def_OAIQ023F001
-- name    : OAIQ023F001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:40:01.757855+00:00
-- url     : https://prove2.me/theorems/d065323c-c2c6-41c8-8991-a0d0858f1d28
-- title:
--   Definitions bundle OAIQ023F001 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 345 declarations of OpenAI's Lean: 162 definitions, 5 inductive types or structures, 17 instances and 161 theorems. The definitions and types are `OAI.DerivedBar.IterateSupport.instHasDerivedCategoryModuleCat_solutions`, `OAI.DerivedBar.IterateSupport.instHasDerivedCategoryModuleCat_solutions_2`, `OAI.DerivedBar.IterateSupport.integerIterateExtinctionHasDerivedCategory`, `OAI.DerivedBar.Multibar.Blocks`, `OAI.DerivedBar.Multibar.Indexed.Shape`, `OAI.DerivedBar.Multibar.Indexed.blockDegreeEquiv`, `OAI.DerivedBar.Multibar.Indexed.blocksOfShape`, `OAI.DerivedBar.Multibar.Indexed.castShape`, `OAI.DerivedBar.Multibar.Indexed.instDecidableEqShape`, `OAI.DerivedBar.Multibar.Indexed.outerTensor`, `OAI.DerivedBar.Multibar.Indexed.shapeOfBlocks`, `OAI.DerivedBar.Multibar.Indexed.shapeOfList`, `OAI.DerivedBar.Multibar.Indexed.tensor`, `OAI.DerivedBar.Multibar.Indexed.toList`, `OAI.DerivedBar.Multibar.count`, `OAI.DerivedBar.Multibar.leadingBase`, `OAI.DerivedBar.Multibar.parse`, `OAI.DerivedBar.Multibar.parseOfCount`, `OAI.DerivedBar.Multibar.pattern`, `OAI.DerivedBar.Multibar.patternTerm`, `OAI.DerivedBar.Multibar.total`, `OAI.DerivedBar.ParityBridge.countRetractsInflatedModule`, `OAI.DerivedBar.ParityBridge.indexedAssemblyComparisonShapeDecidableEq`, `OAI.DerivedBar.ParityBridge.inflatedModule`, `OAI.DerivedBar.ParityBridge.instDecidableEqIndex`, `OAI.DerivedBar.ParityBridge.instHasDerivedCategoryModuleCat_solutions`, `OAI.DerivedBar.ParityBridge.instHasDerivedCategoryModuleCat_solutions_3`, `OAI.DerivedBar.ParityBridge.instHasDerivedCategoryModuleCat_solutions_4`, `OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions`, `OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_1`, `OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_10`, `OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_11`, `OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_12`, `OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_15`, `OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_16`, `OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_2`, `OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_6`, `OAI.DerivedBar.ParityBridge.integerCountInflatedModule`, `OAI.DerivedBar.ParityBridge.integerCountRestrictionInflatedModule`, `OAI.DerivedBar.ParityBridge.leadingBarSuffixInflatedModule` and 127 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bar_BlockCoordinateGenerators`, `Finitistic_Bar_BlockIndexEquiv`, `Finitistic_Bar_ChainSplitting`, `Finitistic_Bar_CountHomologyDetection`, `Finitistic_Bar_CountRetracts`, `Finitistic_Bar_CountTorBounds`, `Finitistic_Bar_DerivedCountShift`, `Finitistic_Bar_DirectSumCoproduct`, `Finitistic_Bar_FiniteSumSupport`, `Finitistic_Bar_GlobalIndexedComparison`, `Finitistic_Bar_IndexedAssemblyComparison`, `Finitistic_Bar_IndexedPatternEmbedding`, `Finitistic_Bar_InflatedParityFaces`, `Finitistic_Bar_IntegerCountObject`, `Finitistic_Bar_IntegerCountRestriction`, `Finitistic_Bar_IntegerCountShift`, `Finitistic_Bar_IntegerDerivedMultibar`, `Finitistic_Bar_LeadingBarSuffix`, `Finitistic_Bar_LeadingSupportedComparison`, `Finitistic_Bar_LeadingTotalComparison`, `Finitistic_Bar_LiteralMultibarCoordinates`, `Finitistic_Bar_ModuleBlockIndex`, `Finitistic_Bar_ModuleMultibarCoordinates`, `Finitistic_Bar_MultibarBlocks`, `Finitistic_Bar_MultibarDecomposition`, `Finitistic_Bar_MultibarIndex`, `Finitistic_Bar_MultibarSigns`, `Finitistic_Bar_PatternTensorCoherence`, `Finitistic_Bar_ProjectiveTail`, `Finitistic_Bar_RecursiveBlockIndex`, `Finitistic_Bar_RecursivePrefixInclusions`, `Finitistic_Bar_RecursiveSuffixDifferential`, `Finitistic_Bar_RecursiveSuffixEmbedding`, `Finitistic_Bar_RecursiveSuffixFaces`, `Finitistic_Bar_RecursiveSuffixInduction`, `Finitistic_Bar_RecursiveSuffixTotal`, `Finitistic_Bar_RecursiveTotalDifferential`, `Finitistic_Bar_RecursiveTotalFlatten`, `Finitistic_Bar_SignedBlockModel`, `Finitistic_Bar_Splitting`, `Finitistic_Bar_StrictSupportExtension`, `Finitistic_Bar_SuffixNaturality`, `Finitistic_Bar_TotalMap`, `Finitistic_Bar_Weight`, `Finitistic_Bimodule_BimoduleVertex`, `Finitistic_Encoding_ArrowBasisIso`, `Finitistic_Encoding_DirectedBound`, `Finitistic_Encoding_QuadraticEncoding`, `Finitistic_Encoding_ThreeVertexAlgebra`, `Finitistic_Iteration_BinomialBiproduct`, `Finitistic_Iteration_BinomialIndex`, `Finitistic_Iteration_BinomialIteration`, `Finitistic_Iteration_IntegerIterateAmplitude`, `Finitistic_Iteration_IntegerIterateExtinction`, `Finitistic_Iteration_IntegerIterateSupport`, `Finitistic_Localization_AdditiveSplitImage`, `Finitistic_Localization_NativeArrowBridge`, `Finitistic_Localization_SplitComponentExact`, `Finitistic_Ordinary_OrdinaryFiniteColumnComplex`, `Finitistic_Rectification_ColumnComplex`, `Finitistic_Rectification_ColumnFinite`, `Finitistic_Rectification_CornerProjection`, `Finitistic_Rectification_DiagramAssembly`, `Finitistic_Rectification_ExactProducts`, `Finitistic_Rectification_ExternalTensor`, `Finitistic_Rectification_InducedColumns`, `Finitistic_Rectification_InducedDiagram`, `Finitistic_Rectification_RectificationTotal`, `Finitistic_Rectification_SourceFiltrationComplex`, `Finitistic_Rectification_SourceFiltrationReal`, `Finitistic_Rectification_TensorComplex`, `Finitistic_Rectification_TotalExact`, `Finitistic_Rectification_TotalFunctorial`, `Finitistic_Rectification_VertexFunctor`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F005`, `OAIQ023F006`, `OAIQ023F007`, `OAIQ023F008` and `OAIQ023F009`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ023_Fin.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TotalMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
noncomputable section
namespace DerivedBar
universe u
variable {D : Type u} [Ring D]
local notation "c" => ComplexShape.down ℕ

/-- Each diagonal of a first-quadrant total complex is finite. -/
instance finiteTotalDiagonal (n : ℕ) : Finite ((ComplexShape.π c c c) ⁻¹' {n}) := by
  apply Finite.of_injective (fun p => (⟨p.val.1, show p.val.1 < n+1 by
    have := p.property; change p.val.1+p.val.2=n at this; omega⟩ : Fin (n+1)))
  intro a b h
  apply Subtype.ext
  have hab := congrArg Fin.val h
  change a.val.1=b.val.1 at hab
  have ha := a.property
  have hb := b.property
  change a.val.1+a.val.2=n at ha
  change b.val.1+b.val.2=n at hb
  exact Prod.ext hab (by omega)

noncomputable instance fintypeTotalDiagonal (n : ℕ) :
    Fintype ((ComplexShape.π c c c) ⁻¹' {n}) := Fintype.ofFinite _

variable (G : ModuleCat.{u} D ⥤ ModuleCat.{u} D) [G.Additive]
variable (K : HomologicalComplex₂ (ModuleCat.{u} D) c c)

abbrev mapBicomplex : HomologicalComplex₂ (ModuleCat.{u} D) c c :=
  ((G.mapHomologicalComplex c).mapHomologicalComplex c).obj K

/-- Maps out of the image of a total term, using only a finite coproduct. -/
def totalMapDesc {n : ℕ} {Y : ModuleCat.{u} D}
    (f : ∀ i q (_ : i+q=n), G.obj ((K.X i).X q) ⟶ Y) :
    G.obj ((K.total c).X n) ⟶ Y :=
  (isColimitOfPreserves G (K.toGradedObject.isColimitCofanMapObj
    (ComplexShape.π c c c) n)).desc
    { pt := Y
      ι := Discrete.natTrans (fun j => f j.as.val.1 j.as.val.2 j.as.property) }

@[reassoc (attr := simp)]
theorem ι_totalMapDesc {n : ℕ} {Y : ModuleCat.{u} D}
    (f : ∀ i q (_ : i+q=n), G.obj ((K.X i).X q) ⟶ Y)
    (i q : ℕ) (h : i+q=n) :
    G.map (K.ιTotal c i q n h) ≫ totalMapDesc G K f = f i q h := by
  exact (isColimitOfPreserves G (K.toGradedObject.isColimitCofanMapObj
    (ComplexShape.π c c c) n)).fac _ ⟨⟨⟨i,q⟩,h⟩⟩

theorem totalMap_hom_ext {n : ℕ} {Y : ModuleCat.{u} D}
    {f g : G.obj ((K.total c).X n) ⟶ Y}
    (h : ∀ i q (hi : i+q=n),
      G.map (K.ιTotal c i q n hi) ≫ f = G.map (K.ιTotal c i q n hi) ≫ g) : f=g := by
  apply IsColimit.hom_ext
    (isColimitOfPreserves G (K.toGradedObject.isColimitCofanMapObj
      (ComplexShape.π c c c) n))
  rintro ⟨⟨⟨i,q⟩,hi⟩⟩
  exact h i q hi

/-- Additive functors commute with each finite diagonal sum. -/
def totalMapIsoX (n : ℕ) :
    G.obj ((K.total c).X n) ≅ ((mapBicomplex G K).total c).X n where
  hom := totalMapDesc G K (fun i q h => (mapBicomplex G K).ιTotal c i q n h)
  inv := (mapBicomplex G K).totalDesc (fun i q h => G.map (K.ιTotal c i q n h))
  hom_inv_id := by apply totalMap_hom_ext G K; intros; simp
  inv_hom_id := by apply HomologicalComplex₂.total.hom_ext; intros; simp

@[reassoc (attr := simp)]
theorem ι_totalMapIsoX_inv (i q n : ℕ) (h : i+q=n) :
    (mapBicomplex G K).ιTotal c i q n h ≫ (totalMapIsoX G K n).inv =
      G.map (K.ιTotal c i q n h) := by
  simp [totalMapIsoX]

theorem ιTotalOrZero_totalMapIsoX_inv (i q n : ℕ) :
    (mapBicomplex G K).ιTotalOrZero c i q n ≫ (totalMapIsoX G K n).inv =
      G.map (K.ιTotalOrZero c i q n) := by
  by_cases h : i+q=n
  · rw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h,
      HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h, ι_totalMapIsoX_inv]
  · rw [HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h,
      HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h, zero_comp, G.map_zero]

theorem d₁_totalMapIsoX_inv (i q n : ℕ) :
    (mapBicomplex G K).d₁ c i q n ≫ (totalMapIsoX G K n).inv =
      G.map (K.d₁ c i q n) := by
  by_cases h : (c).Rel i ((c).next i)
  · rw [HomologicalComplex₂.d₁_eq' _ _ h, HomologicalComplex₂.d₁_eq' _ _ h]
    simp only [Units.smul_def, zsmul_comp, Category.assoc,
      ιTotalOrZero_totalMapIsoX_inv, Units.smul_def, G.map_zsmul, G.map_comp]
    rfl
  · rw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ h,
      HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ h, zero_comp, G.map_zero]

theorem d₂_totalMapIsoX_inv (i q n : ℕ) :
    (mapBicomplex G K).d₂ c i q n ≫ (totalMapIsoX G K n).inv =
      G.map (K.d₂ c i q n) := by
  by_cases h : (c).Rel q ((c).next q)
  · rw [HomologicalComplex₂.d₂_eq' _ _ _ h, HomologicalComplex₂.d₂_eq' _ _ _ h]
    simp only [Units.smul_def, zsmul_comp, Category.assoc,
      ιTotalOrZero_totalMapIsoX_inv, Units.smul_def, G.map_zsmul, G.map_comp]
    rfl
  · rw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h,
      HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h, zero_comp, G.map_zero]

/-- Additive functors commute with first-quadrant totalization as chain complexes,
with the actual horizontal and signed vertical differential. -/
def totalMapIso : (G.mapHomologicalComplex c).obj (K.total c) ≅
    (mapBicomplex G K).total c :=
  (HomologicalComplex.Hom.isoOfComponents (fun n => (totalMapIsoX G K n).symm)
    (by
      intro i j hij
      apply HomologicalComplex₂.total.hom_ext
      intro a b h
      change (mapBicomplex G K).ιTotal c a b i h ≫ (totalMapIsoX G K i).inv ≫
          G.map ((K.total c).d i j) =
        (mapBicomplex G K).ιTotal c a b i h ≫
          ((mapBicomplex G K).total c).d i j ≫ (totalMapIsoX G K j).inv
      rw [ι_totalMapIsoX_inv_assoc, ← G.map_comp]
      simp only [HomologicalComplex₂.total_d, comp_add, add_comp,
        HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
        HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc,
        G.map_add, d₁_totalMapIsoX_inv, d₂_totalMapIsoX_inv])).symm
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveTotalFlatten
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open scoped DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
universe u
variable {D : Type u} [Ring D]
local notation "c" => ComplexShape.down ℕ

abbrev Diagonal (n : ℕ) := {p : ℕ × ℕ // p.1+p.2=n}

/-- Every index records every bar length and the final input degree. -/
def Index : ℕ → ℕ → Type
  | 0, _ => Unit
  | r+1, n => (p : Diagonal n) × Index r p.val.2

instance indexFinite (r n : ℕ) : Finite (Index r n) := by
  induction r generalizing n with
  | zero => exact inferInstanceAs (Finite Unit)
  | succ r ih =>
    have : Finite (Diagonal n) := DerivedBar.finiteTotalDiagonal n
    have (degree : ℕ) : Finite (Index r degree) := ih degree
    exact inferInstanceAs (Finite ((p : Diagonal n) × Index r p.val.2))

local instance instDecidableEqIndex (r n : ℕ) : DecidableEq (Index r n) := Classical.decEq _

variable (B : ℕ → ModuleCat.{u} D ⥤ ChainComplex (ModuleCat.{u} D) ℕ)
  [∀ r, (B r).Additive]

abbrev degreeFunctor (r i : ℕ) : ModuleCat.{u} D ⥤ ModuleCat.{u} D :=
  B r ⋙ HomologicalComplex.eval _ c i

variable (Z : ChainComplex (ModuleCat.{u} D) ℕ)

def bicomplex (r : ℕ) (W : ChainComplex (ModuleCat.{u} D) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} D) c c :=
  HomologicalComplex₂.flip (((B r).mapHomologicalComplex c).obj W)

/-- Successively totalize the given module-to-chain functors. -/
def iter : ℕ → ChainComplex (ModuleCat.{u} D) ℕ
  | 0 => Z
  | r+1 => (bicomplex B r (iter r)).total c

/-- Literal nested terms, before any coproducts are taken. -/
def summand : (r n : ℕ) → Index r n → ModuleCat.{u} D
  | 0, n, _ => Z.X n
  | r+1, _, ⟨p,t⟩ => (degreeFunctor B r p.val.1).obj (summand r p.val.2 t)

/-- Insert a literal nested term into the actual recursive total. -/
def inclusion : (r n : ℕ) → (t : Index r n) → summand B Z r n t ⟶ (iter B Z r).X n
  | 0, _, _ => 𝟙 _
  | r+1, n, ⟨p,t⟩ =>
    (degreeFunctor B r p.val.1).map (inclusion r p.val.2 t) ≫
      (bicomplex B r (iter B Z r)).ιTotal c p.val.1 p.val.2 n p.property

/-- A map out of an additive image of the recursive total is specified on all
literal nested terms. Only finite diagonal coproducts are distributed. -/
def desc : (r : ℕ) → (G : ModuleCat.{u} D ⥤ ModuleCat.{u} D) → [G.Additive] →
    {n : ℕ} → {Y : ModuleCat.{u} D} →
    (∀ t : Index r n, G.obj (summand B Z r n t) ⟶ Y) →
    (G.obj ((iter B Z r).X n) ⟶ Y)
  | 0, _, _, _, _, f => f ()
  | r+1, G, _, _, _, f => totalMapDesc G (bicomplex B r (iter B Z r))
      (fun i q h => desc r (degreeFunctor B r i ⋙ G) (fun t => f ⟨⟨⟨i,q⟩,h⟩,t⟩))

@[reassoc (attr := simp)]
theorem inclusion_desc (r : ℕ) (G : ModuleCat.{u} D ⥤ ModuleCat.{u} D) [G.Additive]
    {n : ℕ} {Y : ModuleCat.{u} D}
    (f : ∀ t : Index r n, G.obj (summand B Z r n t) ⟶ Y) (t : Index r n) :
    G.map (inclusion B Z r n t) ≫ desc B Z r G f = f t := by
  induction r generalizing G n with
  | zero =>
    cases t
    change G.map (𝟙 (Z.X n)) ≫ f () = f ()
    erw [G.map_id, Category.id_comp]
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
    simp only [inclusion, desc]
    erw [Functor.map_comp, Category.assoc, ι_totalMapDesc]
    exact ih (degreeFunctor B r i ⋙ G) _ t

theorem hom_ext (r : ℕ) (G : ModuleCat.{u} D ⥤ ModuleCat.{u} D) [G.Additive]
    {n : ℕ} {Y : ModuleCat.{u} D}
    {f g : G.obj ((iter B Z r).X n) ⟶ Y}
    (h : ∀ t : Index r n, G.map (inclusion B Z r n t) ≫ f =
      G.map (inclusion B Z r n t) ≫ g) : f=g := by
  induction r generalizing G n with
  | zero =>
    have hh := h ()
    change G.map (𝟙 (Z.X n)) ≫ f = G.map (𝟙 (Z.X n)) ≫ g at hh
    erw [G.map_id, Category.id_comp, Category.id_comp] at hh
    exact hh
  | succ r ih =>
    apply totalMap_hom_ext G (bicomplex B r (iter B Z r))
    intro i q hq
    apply ih (degreeFunctor B r i ⋙ G)
    intro t
    have hh := h ⟨⟨⟨i,q⟩,hq⟩,t⟩
    dsimp only [inclusion] at hh
    erw [Functor.map_comp] at hh
    simpa only [Category.assoc, Functor.comp_map] using! hh

/-- Actual degreewise flattening into an ordinary direct sum of nested tensors.
The universal property is proved for the recursive totals, not assumed. -/
def flattenIso (r n : ℕ) (G : ModuleCat.{u} D ⥤ ModuleCat.{u} D) [G.Additive] :
    G.obj ((iter B Z r).X n) ≅
      ModuleCat.of D (⨁ t : Index r n, G.obj (summand B Z r n t)) where
  hom := desc B Z r G (fun t => ModuleCat.ofHom (DirectSum.lof D (Index r n) (fun t => G.obj (summand B Z r n t)) t))
  inv := ModuleCat.ofHom (DirectSum.toModule D _ _
    (fun t => (G.map (inclusion B Z r n t)).hom))
  hom_inv_id := by
    apply hom_ext B Z r G
    intro t
    simp only [inclusion_desc_assoc, Category.comp_id]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      DirectSum.toModule_lof]
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro t
    apply LinearMap.ext
    intro v
    have h := congrArg (fun f => f.hom v)
      (inclusion_desc B Z r G
        (fun t => ModuleCat.ofHom (DirectSum.lof D (Index r n) (fun t => G.obj (summand B Z r n t)) t)) t)
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      DirectSum.toModule_lof, ModuleCat.hom_id, LinearMap.id_apply] using h
end DerivedBar.RecursiveTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveTotalDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open scoped DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
universe u
variable {D : Type u} [Ring D]
local notation "c" => ComplexShape.down ℕ
local instance instDecidableEqIndex_1 (r n : ℕ) : DecidableEq (Index r n) := Classical.decEq _

section Sums
variable {I : Type} [Finite I] [DecidableEq I] (V : I → ModuleCat.{u} D)
  (G : ModuleCat.{u} D ⥤ ModuleCat.{u} D) [G.Additive]

/-- Distribution over a finite direct sum, defined by its coproduct property. -/
def sumDesc {Y : ModuleCat.{u} D} (f : ∀ t, G.obj (V t) ⟶ Y) :
    G.obj (ModuleCat.of D (⨁ t, V t)) ⟶ Y :=
  (isColimitOfPreserves G (ModuleCat.coproductCoconeIsColimit V)).desc
    { pt := Y
      ι := Discrete.natTrans (fun t => f t.as) }

@[reassoc (attr := simp)]
theorem lof_sumDesc {Y : ModuleCat.{u} D} (f : ∀ t, G.obj (V t) ⟶ Y) (t : I) :
    G.map (ModuleCat.ofHom (DirectSum.lof D I (fun t => V t) t)) ≫
      sumDesc V G f = f t :=
  (isColimitOfPreserves G (ModuleCat.coproductCoconeIsColimit V)).fac _ ⟨t⟩

theorem sum_hom_ext {Y : ModuleCat.{u} D}
    {f g : G.obj (ModuleCat.of D (⨁ t, V t)) ⟶ Y}
    (h : ∀ t, G.map (ModuleCat.ofHom (DirectSum.lof D I (fun t => V t) t)) ≫ f =
      G.map (ModuleCat.ofHom (DirectSum.lof D I (fun t => V t) t)) ≫ g) : f=g := by
  apply (isColimitOfPreserves G (ModuleCat.coproductCoconeIsColimit V)).hom_ext
  rintro ⟨t⟩
  exact h t
end Sums

variable (B : ℕ → ModuleCat.{u} D ⥤ ChainComplex (ModuleCat.{u} D) ℕ)
  [∀ r, (B r).Additive] (Z : ChainComplex (ModuleCat.{u} D) ℕ)

abbrev flat (r n : ℕ) : ModuleCat.{u} D :=
  ModuleCat.of D (⨁ t : Index r n, summand B Z r n t)

def lof (r n : ℕ) (t : Index r n) : summand B Z r n t ⟶ flat B Z r n :=
  ModuleCat.ofHom (DirectSum.lof D (Index r n) (fun t => summand B Z r n t) t)

abbrev assemble (r n : ℕ) : flat B Z r n ⟶ (iter B Z r).X n :=
  (flattenIso B Z r n (𝟭 _)).inv

@[reassoc (attr := simp)]
theorem lof_assemble (r n : ℕ) (t : Index r n) :
    lof B Z r n t ≫ assemble B Z r n = inclusion B Z r n t := by
  apply (cancel_mono (flattenIso B Z r n (𝟭 _)).hom).mp
  change lof B Z r n t ≫ (flattenIso B Z r n (𝟭 _)).inv ≫ _ = _
  rw [Iso.inv_hom_id, Category.comp_id]
  exact (inclusion_desc B Z r (𝟭 _)
    (fun t => ModuleCat.ofHom (DirectSum.lof D (Index r n)
      (fun t => (𝟭 (ModuleCat D)).obj (summand B Z r n t)) t)) t).symm

/-- The horizontal face in a literal outer block; there is no face at length zero. -/
def horizontal (r n i q : ℕ) (h : i+q=n+1) (t : Index r q) :
    (degreeFunctor B r i).obj (summand B Z r q t) ⟶ flat B Z (r+1) n :=
  match i with
  | 0 => 0
  | i+1 => ((B r).obj (summand B Z r q t)).d (i+1) i ≫
      lof B Z (r+1) n ⟨⟨⟨i,q⟩,by omega⟩,t⟩

/-- The vertical face applies the already defined inner differential, with
exactly the totalization sign (-1)^i, then distributes the resulting finite sum. -/
def vertical (r n i q : ℕ) (h : i+q=n+1) (t : Index r q)
    (d : ∀ q, flat B Z r (q+1) ⟶ flat B Z r q) :
    (degreeFunctor B r i).obj (summand B Z r q t) ⟶ flat B Z (r+1) n :=
  match q with
  | 0 => 0
  | q+1 => ((-1 : ℤˣ)^i) •
      ((degreeFunctor B r i).map (lof B Z r (q+1) t ≫ d q) ≫
        sumDesc (summand B Z r q) (degreeFunctor B r i)
          (fun s => lof B Z (r+1) n ⟨⟨⟨i,q⟩,by omega⟩,s⟩))

/-- Independently recursive differential on the flattened direct sum. Its
construction uses only the original functor differentials, finite-sum distribution,
and the previously constructed inner differential, never the total differential. -/
def differential : (r n : ℕ) → flat B Z r (n+1) ⟶ flat B Z r n
  | 0, n => ModuleCat.ofHom (DirectSum.toModule D _ _
      (fun _ => (Z.d (n+1) n ≫ lof B Z 0 n ()).hom))
  | r+1, n => ModuleCat.ofHom (DirectSum.toModule D _ _
      (fun t => (horizontal B Z r n t.1.val.1 t.1.val.2 t.1.property t.2 +
        vertical B Z r n t.1.val.1 t.1.val.2 t.1.property t.2
          (differential r)).hom))

@[reassoc (attr := simp)]
theorem lof_differential_succ (r n i q : ℕ) (h : i+q=n+1) (t : Index r q) :
    lof B Z (r+1) (n+1) ⟨⟨⟨i,q⟩,h⟩,t⟩ ≫ differential B Z (r+1) n =
      horizontal B Z r n i q h t + vertical B Z r n i q h t (differential B Z r) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  simp only [lof, differential, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.comp_apply]
  erw [DirectSum.toModule_lof]
  rfl

@[reassoc (attr := simp)]
theorem sumDesc_assemble (r n i q : ℕ) (h : i+q=n) :
    sumDesc (summand B Z r q) (degreeFunctor B r i)
      (fun s => lof B Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,s⟩) ≫ assemble B Z (r+1) n =
    (degreeFunctor B r i).map (assemble B Z r q) ≫
      (bicomplex B r (iter B Z r)).ιTotal c i q n h := by
  apply sum_hom_ext
  intro t
  erw [lof_sumDesc_assoc, lof_assemble]
  erw [← Category.assoc, ← Functor.map_comp]
  change _ = (degreeFunctor B r i).map (lof B Z r q t ≫ assemble B Z r q) ≫ _
  rw [lof_assemble]
  rfl

/-- The horizontal face agrees with the actual total on every nested tensor. -/
theorem horizontal_assemble (r n i q : ℕ) (h : i+q=n+1) (t : Index r q) :
    horizontal B Z r n i q h t ≫ assemble B Z (r+1) n =
      (degreeFunctor B r i).map (inclusion B Z r q t) ≫
        (bicomplex B r (iter B Z r)).d₁ c i q n := by
  cases i with
  | zero =>
    erw [horizontal, zero_comp, HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by simp), comp_zero]
    rfl
  | succ i =>
    erw [horizontal, Category.assoc, lof_assemble,
      HomologicalComplex₂.d₁_eq _ _ (by rfl : (c).Rel (i+1) i) q n (by change i+q=n; omega)]
    change _ = _ ≫ ((1 : ℤˣ) • _)
    erw [one_smul]
    change ((B r).obj (summand B Z r q t)).d (i+1) i ≫
        (degreeFunctor B r i).map (inclusion B Z r q t) ≫ _ =
      (degreeFunctor B r (i+1)).map (inclusion B Z r q t) ≫
        ((B r).obj ((iter B Z r).X q)).d (i+1) i ≫ _
    exact (((B r).map (inclusion B Z r q t)).comm_assoc (i+1) i
      ((bicomplex B r (iter B Z r)).ιTotal c i q n (by change i+q=n; omega))).symm

/-- The signed vertical face agrees with the actual total whenever the inner
comparison has been proved; the induction below discharges that premise. -/
theorem vertical_assemble (r n i q : ℕ) (h : i+q=n+1) (t : Index r q)
    (ih : ∀ q, differential B Z r q ≫ assemble B Z r q =
      assemble B Z r (q+1) ≫ (iter B Z r).d (q+1) q) :
    vertical B Z r n i q h t (differential B Z r) ≫ assemble B Z (r+1) n =
      (degreeFunctor B r i).map (inclusion B Z r q t) ≫
        (bicomplex B r (iter B Z r)).d₂ c i q n := by
  cases q with
  | zero =>
    erw [vertical, zero_comp, HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by simp), comp_zero]
    rfl
  | succ q =>
    erw [vertical, HomologicalComplex₂.d₂_eq _ _ i (by rfl : (c).Rel (q+1) q) n
      (by change i+q=n; omega)]
    change _ = _ ≫ (((-1 : ℤˣ)^i) • _)
    erw [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc,
      sumDesc_assemble]
    congr 1
    erw [← Category.assoc, ← Functor.map_comp, Category.assoc, ih,
      ← Category.assoc, lof_assemble, Functor.map_comp, Category.assoc]

theorem differential_assemble (r n : ℕ) :
    differential B Z r n ≫ assemble B Z r n =
      assemble B Z r (n+1) ≫ (iter B Z r).d (n+1) n := by
  induction r generalizing n with
  | zero =>
    apply sum_hom_ext (summand B Z 0 (n+1)) (𝟭 _)
    intro t
    cases t
    have hf : lof B Z 0 (n+1) () ≫ differential B Z 0 n =
        Z.d (n+1) n ≫ lof B Z 0 n () := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      simp only [lof, differential, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearMap.comp_apply]
      erw [DirectSum.toModule_lof]
      rfl
    change lof B Z 0 (n+1) () ≫ _ = lof B Z 0 (n+1) () ≫ _
    erw [← Category.assoc, hf, Category.assoc, lof_assemble, lof_assemble_assoc]
    simp only [inclusion, iter]
    exact Category.comp_id _
  | succ r ih =>
    apply sum_hom_ext (summand B Z (r+1) (n+1)) (𝟭 _)
    rintro ⟨⟨⟨i,q⟩,h⟩,t⟩
    change lof B Z (r+1) (n+1) _ ≫ _ = lof B Z (r+1) (n+1) _ ≫ _
    erw [lof_differential_succ_assoc, add_comp, horizontal_assemble,
      vertical_assemble B Z r n i q h t ih, lof_assemble_assoc]
    simp only [inclusion, iter, HomologicalComplex₂.total_d, comp_add]
    erw [Category.assoc, Category.assoc, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rfl

/-- Square-zero is a consequence of the proved differential comparison. -/
theorem differential_sq (r n : ℕ) :
    differential B Z r (n+1) ≫ differential B Z r n = 0 := by
  apply (cancel_mono (assemble B Z r n)).mp
  rw [Category.assoc, differential_assemble, ← Category.assoc,
    differential_assemble, Category.assoc, HomologicalComplex.d_comp_d,
    comp_zero, zero_comp]

/-- The direct sum with its independently recursive signed differential. -/
def flatComplex (r : ℕ) : ChainComplex (ModuleCat.{u} D) ℕ :=
  ChainComplex.of (flat B Z r) (differential B Z r) (differential_sq B Z r)

/-- An actual chain isomorphism flattening every recursive total, with both
horizontal and signed vertical differential verified on literal summands. -/
def flattenChainIso (r : ℕ) : flatComplex B Z r ≅ iter B Z r :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (flattenIso B Z r n (𝟭 _)).symm)
    (by
      intro i j hij
      change j+1=i at hij
      subst i
      change assemble B Z r (j+1) ≫ (iter B Z r).d (j+1) j =
        (flatComplex B Z r).d (j+1) j ≫ assemble B Z r j
      simpa only [flatComplex, ChainComplex.of_d] using
        (differential_assemble B Z r j).symm)
end DerivedBar.RecursiveTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_FiniteSumSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
universe u
variable {D : Type u} [Ring D]
variable {I : Type} [Finite I] [DecidableEq I] (V : I → ModuleCat.{u} D)
  (P : I → Prop) [DecidablePred P]

/-- Omitting zero summands is an isomorphism of ordinary direct sums. -/
def supportIso (hzero : ∀ i, ¬P i → IsZero (V i)) :
    ModuleCat.of D (⨁ i, V i) ≅ ModuleCat.of D (⨁ i : {i // P i}, V i.val) where
  hom := ModuleCat.ofHom (DirectSum.toModule D _ _ (fun i =>
    if h : P i then DirectSum.lof D {i // P i} (fun i => V i.val) ⟨i,h⟩ else 0))
  inv := ModuleCat.ofHom (DirectSum.toModule D _ _
    (fun i => DirectSum.lof D I (fun i => V i) i.val))
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro v
    by_cases h : P i
    · simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearMap.comp_apply, DirectSum.toModule_lof, dite_eq_left h,
        ModuleCat.hom_id, LinearMap.id_apply]
    · have hz : (𝟙 (V i)) = 0 := (hzero i h).eq_of_src _ _
      have hv : v=0 := congrArg (fun f : V i ⟶ V i => f.hom v) hz
      subst v
      simp
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro v
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.comp_apply, DirectSum.toModule_lof, dite_eq_left i.property,
      ModuleCat.hom_id, LinearMap.id_apply]
end DerivedBar.RecursiveTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_Weight
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar
namespace SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

theorem map_span_mem {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (g : V →ₗ[k] W) (s : Set V) (t : Submodule k W)
    (h : ∀ v ∈ s, g v ∈ t) {v : V} (hv : v ∈ Submodule.span k s) : g v ∈ t := by
  have hle : Submodule.span k s ≤ t.comap g := Submodule.span_le.mpr h
  exact hle hv

end SquareZero
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_Splitting
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar.SquareZero
universe u

theorem internal_of_projections {R V : Type u} [Ring R] [AddCommGroup V] [Module R V]
    (S : ℕ → Submodule R V) (p : ℕ → Module.End R V)
    (hself : ∀ r v, v ∈ S r → p r v = v)
    (hother : ∀ r s, r ≠ s → ∀ v, v ∈ S s → p r v = 0)
    (htop : iSup S = ⊤) : DirectSum.IsInternal S := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top _ htop
  intro r
  rw [Submodule.disjoint_def]
  intro v hv hrest
  have hle : (⨆ (s : ℕ) (_ : s ≠ r), S s) ≤ (p r).ker := by
    refine iSup_le fun s => iSup_le fun hs => ?_
    intro w hw
    exact hother r s (Ne.symm hs) w hw
  have hz := hle hrest
  change p r v = 0 at hz
  rwa [hself r v hv] at hz

end DerivedBar.SquareZero

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_MultibarSigns
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct TrivSqZeroExt
noncomputable section

namespace DerivedBar.SquareZero
universe u

theorem sign_square {k : Type u} [Field k] (r : ℕ) :
    (-1 : k)^r * (-1 : k)^r = 1 := by
  rw [← mul_pow]
  simp

end DerivedBar.SquareZero

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_MultibarBlocks
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct TrivSqZeroExt
noncomputable section

namespace DerivedBar.Multibar
universe u

/-- `false` records a D slot, `true` an X slot. The leading D is separate. -/
def count : List Bool → ℕ
  | [] => 0
  | false :: p => count p
  | true :: p => count p + 1

/-- The r+1 block lengths, with no empty-list ambiguity at r=0. -/
def Blocks : ℕ → Type
  | 0 => ℕ
  | r+1 => ℕ × Blocks r

def total : (r : ℕ) → Blocks r → ℕ
  | 0, i => i
  | r+1, (i, tail) => i + total r tail

def pattern : (r : ℕ) → Blocks r → List Bool
  | 0, i => List.replicate i false
  | r+1, (i, tail) => List.replicate i false ++ true :: pattern r tail

@[simp] theorem count_bases (i : ℕ) (p : List Bool) :
    count (List.replicate i false ++ p) = count p := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [List.replicate_succ, count] using ih

@[simp] theorem count_pattern (r : ℕ) (b : Blocks r) : count (pattern r b) = r := by
  induction r with
  | zero => simpa [pattern, count] using count_bases b []
  | succ r ih =>
    rcases b with ⟨i, tail⟩
    simp [pattern, count, ih]

/-- The actual word length agrees with source cohomological degree -r-Σiⱼ. -/
@[simp] theorem length_pattern (r : ℕ) (b : Blocks r) :
    (pattern r b).length = r + total r b := by
  induction r with
  | zero =>
    change ℕ at b
    simp [pattern, total]
  | succ r ih =>
    rcases b with ⟨i, tail⟩
    simp only [pattern, List.length_append, List.length_replicate, List.length_cons, ih, total]
    omega

variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

/-- Genuine iterated tensors over k for a prescribed D/X pattern, ending in N.
No ordinary tensor over D is used in these bar terms. -/
@[reducible] def patternTerm : List Bool → ModuleCat k
  | [] => ModuleCat.of k N
  | false :: p => ModuleCat.of k (D ⊗[k] patternTerm p)
  | true :: p => ModuleCat.of k (X ⊗[k] patternTerm p)

end DerivedBar.Multibar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_PatternTensorCoherence
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct
open scoped TensorProduct
noncomputable section
namespace DerivedBar.Multibar
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N] [Module D N] [IsScalarTower k D N]

/-- The exterior D action on a literal pattern is the action on its first slot. -/
@[reducible] instance patternModule : (p : List Bool) → Module D (patternTerm k D X N p)
  | [] => inferInstanceAs (Module D N)
  | false :: p => inferInstanceAs (Module D (D ⊗[k] patternTerm k D X N p))
  | true :: p => inferInstanceAs (Module D (X ⊗[k] patternTerm k D X N p))

instance patternTower : (p : List Bool) → IsScalarTower k D (patternTerm k D X N p)
  | [] => inferInstanceAs (IsScalarTower k D N)
  | false :: p => inferInstanceAs (IsScalarTower k D (D ⊗[k] patternTerm k D X N p))
  | true :: p => inferInstanceAs (IsScalarTower k D (X ⊗[k] patternTerm k D X N p))

end DerivedBar.Multibar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_MultibarIndex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace DerivedBar.Multibar


/-- Raise the first block length. -/
def leadingBase : (r : ℕ) → Blocks r → Blocks r
  | 0, i => Nat.succ i
  | _+1, (i, tail) => (i+1, tail)

@[simp] theorem pattern_leadingBase (r : ℕ) (b : Blocks r) :
    pattern r (leadingBase r b) = false :: pattern r b := by
  cases r with
  | zero => exact List.replicate_succ
  | succ r => rcases b with ⟨i, tail⟩
              simp [leadingBase, pattern, List.replicate_succ]

/-- Parse any word into its unique consecutive D blocks. -/
def parse : (p : List Bool) → Blocks (count p)
  | [] => (0 : ℕ)
  | false :: p => leadingBase (count p) (parse p)
  | true :: p => (0, parse p)

/-- Every D/X word has a block-length description, including zero-length blocks. -/
@[simp] theorem pattern_parse (p : List Bool) : pattern (count p) (parse p) = p := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    cases b <;> simp [parse, count, pattern, ih]

end DerivedBar.Multibar

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_MultibarDecomposition
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct TrivSqZeroExt
noncomputable section

namespace DerivedBar.Multibar.Indexed
universe u

/-- A D/X pattern with length and X-count in its type, avoiding any degree casts. -/
inductive Shape : ℕ → ℕ → Type
  | nil : Shape 0 0
  | base {n r : ℕ} : Shape n r → Shape (n+1) r
  | ideal {n r : ℕ} : Shape n r → Shape (n+1) (r+1)

local instance instDecidableEqShape (n r : ℕ) : DecidableEq (Shape n r) := Classical.decEq _

def toList : {n r : ℕ} → Shape n r → List Bool
  | _, _, .nil => []
  | _, _, .base p => false :: toList p
  | _, _, .ideal p => true :: toList p

@[simp] theorem length_toList {n r : ℕ} (p : Shape n r) : (toList p).length = n := by
  induction p <;> simp_all [toList]

@[simp] theorem count_toList {n r : ℕ} (p : Shape n r) : count (toList p) = r := by
  induction p <;> simp_all [toList, count]

variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

@[reducible] def tensor : {n r : ℕ} → Shape n r → ModuleCat k
  | _, _, .nil => ModuleCat.of k N
  | _, _, .base p => ModuleCat.of k (D ⊗[k] tensor p)
  | _, _, .ideal p => ModuleCat.of k (X ⊗[k] tensor p)

abbrev outerTensor {n r : ℕ} (p : Shape n r) := D ⊗[k] tensor k D X N p

end DerivedBar.Multibar.Indexed

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_SignedBlockModel
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct TrivSqZeroExt CategoryTheory
noncomputable section

namespace DerivedBar.Multibar.Indexed
universe u

/-- The degree-indexed shapes faithfully record their D/X words. -/
theorem toList_injective {n r : ℕ} : Function.Injective (@toList n r) := by
  intro p
  induction p with
  | nil => intro q h; cases q; rfl
  | base p ih =>
    intro q h
    cases q with
    | base q => exact congrArg Shape.base (ih (List.cons.inj h).2)
    | ideal q => exact Bool.noConfusion (List.cons.inj h).1
  | ideal p ih =>
    intro q h
    cases q with
    | base q => exact Bool.noConfusion (List.cons.inj h).1
    | ideal q => exact congrArg Shape.ideal (ih (List.cons.inj h).2)

/-- The block direct sum is finite in every degree, without any completion. -/
instance shape_finite (n r : ℕ) : Finite (Shape n r) :=
  @Finite.of_injective (Shape n r) (List.Vector Bool n) _ (fun p => (⟨toList p, length_toList p⟩ : List.Vector Bool n))
    (fun _ _ h => toList_injective (congrArg Subtype.val h))

variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

omit [Module D X] [Module Dᵐᵒᵖ X] [SMulCommClass D Dᵐᵒᵖ X]
  [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X] in
/-- The indexed tensor is exactly the earlier literal D/X pattern tensor. -/
theorem tensor_toList {n r : ℕ} (p : Shape n r) :
    tensor k D X N p = patternTerm k D X N (toList p) := by
  induction p with
  | nil => rfl
  | base p ih => exact congrArg (fun V : ModuleCat k => ModuleCat.of k (D ⊗[k] V)) ih
  | ideal p ih => exact congrArg (fun V : ModuleCat k => ModuleCat.of k (X ⊗[k] V)) ih

end DerivedBar.Multibar.Indexed

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_BlockIndexEquiv
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace DerivedBar.Multibar

/-- The first X uniquely determines the length of the preceding D block. -/
theorem base_run_injective (i j : ℕ) (p q : List Bool)
    (h : List.replicate i false ++ true :: p = List.replicate j false ++ true :: q) :
    i=j ∧ p=q := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => simpa using h
    | succ j => simp [List.replicate_succ] at h
  | succ i ih =>
    cases j with
    | zero => simp [List.replicate_succ] at h
    | succ j =>
      have ht : List.replicate i false ++ true :: p = List.replicate j false ++ true :: q := by
        simpa only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] using h
      obtain ⟨hij,hpq⟩ := ih j ht
      exact ⟨congrArg Nat.succ hij,hpq⟩

/-- Consecutive block lengths have a unique literal D/X word. -/
theorem pattern_injective (r : ℕ) : Function.Injective (pattern r) := by
  induction r with
  | zero =>
    intro i j h
    change List.replicate i false = List.replicate j false at h
    exact List.length_replicate.symm.trans ((congrArg List.length h).trans List.length_replicate)
  | succ r ih =>
    rintro ⟨i,p⟩ ⟨j,q⟩ h
    obtain ⟨hij,hpq⟩ := base_run_injective i j (pattern r p) (pattern r q) h
    exact Prod.ext hij (ih hpq)

/-- Parse a word of a specified count without changing its block data. -/
def parseOfCount (r : ℕ) (p : List Bool) (h : count p=r) : Blocks r := h ▸ parse p

@[simp] theorem pattern_parseOfCount (r : ℕ) (p : List Bool) (h : count p=r) :
    pattern r (parseOfCount r p h) = p := by
  subst r
  exact pattern_parse p

@[simp] theorem parseOfCount_pattern (r : ℕ) (b : Blocks r) :
    parseOfCount r (pattern r b) (count_pattern r b) = b := by
  apply pattern_injective r
  simp

namespace Indexed

def shapeOfList : (p : List Bool) → Shape p.length (count p)
  | [] => .nil
  | false :: p => .base (shapeOfList p)
  | true :: p => .ideal (shapeOfList p)

@[simp] theorem toList_shapeOfList (p : List Bool) : toList (shapeOfList p) = p := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    cases b with
    | false => exact congrArg (false :: ·) ih
    | true => exact congrArg (true :: ·) ih

def castShape {n m r s : ℕ} (hn : n=m) (hr : r=s) (p : Shape n r) : Shape m s := hn ▸ hr ▸ p

@[simp] theorem toList_castShape {n m r s : ℕ} (hn : n=m) (hr : r=s) (p : Shape n r) :
    toList (castShape hn hr p) = toList p := by
  subst m s
  rfl

/-- Construct the degree-indexed tensor shape of a tuple of block lengths. -/
def shapeOfBlocks (r : ℕ) (b : Blocks r) : Shape (r+total r b) r :=
  castShape (length_pattern r b) (count_pattern r b) (shapeOfList (pattern r b))

@[simp] theorem toList_shapeOfBlocks (r : ℕ) (b : Blocks r) :
    toList (shapeOfBlocks r b) = pattern r b := by
  simp [shapeOfBlocks]

def blocksOfShape {n r : ℕ} (p : Shape n r) : Blocks r :=
  parseOfCount r (toList p) (count_toList p)

@[simp] theorem pattern_blocksOfShape {n r : ℕ} (p : Shape n r) :
    pattern r (blocksOfShape p) = toList p := by simp [blocksOfShape]

theorem total_blocksOfShape {n r : ℕ} (p : Shape n r) : r+total r (blocksOfShape p)=n := by
  have h := length_pattern r (blocksOfShape p)
  rw [pattern_blocksOfShape, length_toList] at h
  exact h.symm

/-- Reindex the finite block-length diagonal by the existing tensor shapes.
The shift by r occurs in the degree, not in a hidden tensor-power replacement. -/
def blockDegreeEquiv (r m : ℕ) : {b : Blocks r // total r b=m} ≃ Shape (r+m) r where
  toFun b := castShape (congrArg (r+·) b.property) rfl (shapeOfBlocks r b.val)
  invFun p := ⟨blocksOfShape p, by have := total_blocksOfShape p; omega⟩
  left_inv b := by
    apply Subtype.ext
    apply pattern_injective r
    simp
  right_inv p := by
    apply toList_injective
    simp
end Indexed
end DerivedBar.Multibar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveBlockIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace DerivedBar.RecursiveTotal
open DerivedBar.Multibar

def castIndex {r n m : ℕ} (h : n=m) (t : Index r n) : Index r m := h ▸ t

end DerivedBar.RecursiveTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LiteralMultibarCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
open DerivedBar.Multibar
universe u

/-- The final input degree, separated from all bar lengths. -/
def inputDegree : (r : ℕ) → {n : ℕ} → Index r n → ℕ
  | 0, n, _ => n
  | r+1, _, ⟨_,t⟩ => inputDegree r t

/-- The literal slots from the X bars, ordered outside to inside. -/
def innerPattern : (r : ℕ) → {n : ℕ} → Index r n → List Bool
  | 0, _, _ => []
  | r+1, _, ⟨p,t⟩ => true :: (List.replicate p.val.1 false ++ innerPattern r t)

@[simp] theorem count_innerPattern (r n : ℕ) (t : Index r n) :
    count (innerPattern r t) = r := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
    simp [innerPattern, count, ih]

theorem length_innerPattern (r n : ℕ) (t : Index r n) :
    (innerPattern r t).length + inputDegree r t = r+n := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
    have ht := ih q t
    simp only [innerPattern, inputDegree, List.length_cons, List.length_append,
      List.length_replicate]
    omega

/-- Leading internal D slots; the exterior D coefficient is kept separate. -/
def leadingPattern (r n : ℕ) (t : Index (r+1) n) : List Bool :=
  List.replicate t.1.val.1 false ++ innerPattern r t.2

@[simp] theorem count_leadingPattern (r n : ℕ) (t : Index (r+1) n) :
    count (leadingPattern r n t) = r := by
  simp [leadingPattern]

theorem length_leadingPattern (r n : ℕ) (t : Index (r+1) n) :
    (leadingPattern r n t).length + inputDegree (r+1) t = r+n := by
  rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
  have ht := length_innerPattern r q t
  simp only [leadingPattern, inputDegree, List.length_append, List.length_replicate]
  omega

end DerivedBar.RecursiveTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_ModuleBlockIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace DerivedBar.RecursiveTotal
open DerivedBar.Multibar

/-- Remove the zero input degree from the list of bar lengths. -/
def moduleBlocks : (r : ℕ) → {n : ℕ} → (t : Index (r+1) n) → Blocks r
  | 0, _, ⟨p,_⟩ => p.val.1
  | r+1, _, ⟨p,t⟩ => (p.val.1, moduleBlocks r t)

theorem total_moduleBlocks (r n : ℕ) (t : Index (r+1) n) :
    total r (moduleBlocks r t) + inputDegree (r+1) t = n := by
  induction r generalizing n with
  | zero => rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩; exact h
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
    have ht := ih q t
    change i + total r (moduleBlocks r t) + inputDegree (r+1) t = n
    omega

theorem pattern_moduleBlocks (r n : ℕ) (t : Index (r+1) n) :
    pattern r (moduleBlocks r t) = leadingPattern r n t := by
  induction r generalizing n with
  | zero =>
    rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
    simp [moduleBlocks, pattern, leadingPattern, innerPattern]
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
    change List.replicate i false ++ true :: pattern r (moduleBlocks r t) = _
    rw [ih q t]
    rfl

/-- The recursive total index attached to a block tuple, with input degree zero. -/
def moduleIndex : (r : ℕ) → (b : Blocks r) → Index (r+1) (total r b)
  | 0, i => ⟨⟨⟨i,0⟩,by exact Nat.add_zero i⟩,()⟩
  | r+1, (i,b) => ⟨⟨⟨i,total r b⟩,rfl⟩,moduleIndex r b⟩

@[simp] theorem inputDegree_moduleIndex (r : ℕ) (b : Blocks r) :
    inputDegree (r+1) (moduleIndex r b) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih => rcases b with ⟨i,b⟩; exact ih b

@[simp] theorem moduleBlocks_moduleIndex (r : ℕ) (b : Blocks r) :
    moduleBlocks r (moduleIndex r b) = b := by
  induction r with
  | zero => rfl
  | succ r ih => rcases b with ⟨i,b⟩; change (i,moduleBlocks r (moduleIndex r b)) = _; rw [ih]

@[simp] theorem inputDegree_castIndex {r n m : ℕ} (h : n=m) (t : Index r n) :
    inputDegree r (castIndex h t) = inputDegree r t := by subst m; rfl

@[simp] theorem moduleBlocks_castIndex {r n m : ℕ} (h : n=m) (t : Index (r+1) n) :
    moduleBlocks r (castIndex h t) = moduleBlocks r t := by subst m; rfl

/-- All indices are recovered from the blocks and input degree; no quotient of
block tensors or identification of distinct patterns is introduced. -/
theorem moduleBlocks_injective (r n : ℕ) (t s : Index (r+1) n)
    (ht : inputDegree (r+1) t=0) (hs : inputDegree (r+1) s=0)
    (h : moduleBlocks r t=moduleBlocks r s) : t=s := by
  induction r generalizing n with
  | zero =>
    rcases t with ⟨⟨⟨i,q⟩,hq⟩,t⟩
    rcases s with ⟨⟨⟨j,p⟩,hp⟩,s⟩
    change q=0 at ht
    change p=0 at hs
    subst q p
    have hij : i=j := by omega
    subst j
    cases t; cases s; rfl
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,hq⟩,t⟩
    rcases s with ⟨⟨⟨j,p⟩,hp⟩,s⟩
    change (i,moduleBlocks r t) = (j,moduleBlocks r s) at h
    have hij := congrArg Prod.fst h
    dsimp at hij
    subst j
    have hqp : q=p := by omega
    subst p
    have hts := ih q t s ht hs (congrArg Prod.snd h)
    subst s
    rfl

/-- Exact module-input indexing by the manuscript's tuples of r+1 block lengths. -/
def moduleBlockEquiv (r n : ℕ) :
    {t : Index (r+1) n // inputDegree (r+1) t=0} ≃
      {b : Blocks r // total r b=n} where
  toFun t := ⟨moduleBlocks r t.val, by
    have h := total_moduleBlocks r n t.val
    rw [t.property, Nat.add_zero] at h
    exact h⟩
  invFun b := ⟨castIndex b.property (moduleIndex r b.val), by simp⟩
  left_inv t := by
    apply Subtype.ext
    apply moduleBlocks_injective r n _ _ (by simp) t.property
    simp
  right_inv b := by apply Subtype.ext; simp

/-- Exact full-degree shape index, including the shift by the number of X slots. -/
def moduleShapeEquiv (r n : ℕ) :
    {t : Index (r+1) n // inputDegree (r+1) t=0} ≃
      Multibar.Indexed.Shape (r+n) r :=
  (moduleBlockEquiv r n).trans (Multibar.Indexed.blockDegreeEquiv r n)
end DerivedBar.RecursiveTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_ModuleMultibarCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
open DerivedBar.Multibar
universe u
local instance instDecidableEqIndex_2 (r n : ℕ) : DecidableEq (Index r n) := Classical.decEq _

local instance instDecidableEqShape_r734b14_1 (r n : ℕ) : DecidableEq (Multibar.Indexed.Shape r n) := Classical.decEq _
/-- The supported index change preserves the literal D/X word. -/
theorem moduleShape_toList (r n : ℕ)
    (t : {t : Index (r+1) n // inputDegree (r+1) t=0}) :
    Multibar.Indexed.toList (moduleShapeEquiv r n t) = leadingPattern r n t.val := by
  simp [moduleShapeEquiv, moduleBlockEquiv, Multibar.Indexed.blockDegreeEquiv,
    pattern_moduleBlocks]

section General
variable {D : Type u} [Ring D]

local instance instDecidableEqShape_r734b14_2 (r n : ℕ) : DecidableEq (Multibar.Indexed.Shape r n) := Classical.decEq _
/-- A zero input term remains zero through every additive bar degree functor. -/
theorem summand_isZero
    (B : ℕ → ModuleCat.{u} D ⥤ ChainComplex (ModuleCat.{u} D) ℕ)
    [∀ r, (B r).Additive] (Z : ChainComplex (ModuleCat.{u} D) ℕ)
    (r n : ℕ) (t : Index r n) (h : IsZero (Z.X (inputDegree r t))) :
    IsZero (summand B Z r n t) := by
  induction r generalizing n with
  | zero => exact h
  | succ r ih =>
    rcases t with ⟨p,t⟩
    exact Functor.map_isZero (degreeFunctor B r p.val.1) (ih p.val.2 t h)

end General
end DerivedBar.RecursiveTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_BlockCoordinateGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
universe u
section Congr
variable {D : Type u} [Ring D]
variable {I : Type} [DecidableEq I] (V W : I → ModuleCat.{u} D)
  (e : ∀ i, V i ≅ W i)

theorem congrLinearEquiv_symm_lof (i : I) (v : W i) :
    (DirectSum.congrLinearEquiv (fun i => (e i).toLinearEquiv)).symm
      (DirectSum.lof D I (fun i => W i) i v) =
    DirectSum.lof D I (fun i => V i) i ((e i).inv.hom v) := by
  change DirectSum.lmap (fun i => (e i).toLinearEquiv.symm.toLinearMap)
    (DirectSum.lof D I (fun i => W i) i v) = _
  rw [DirectSum.lmap_lof]
  rfl
end Congr

variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local instance instDecidableEqIndex_3 (r n : ℕ) : DecidableEq (Index r n) := Classical.decEq _
local instance instDecidableEqShape_1 (r n : ℕ) : DecidableEq (Multibar.Indexed.Shape r n) := Classical.decEq _

end DerivedBar.RecursiveTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_ChainSplitting
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar
universe u

/-- The direct sum of module chain complexes, with the componentwise actual differential. -/
def directSumComplex {R : Type u} [Ring R] (C : ℕ → ChainComplex (ModuleCat R) ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (⨁ r, (C r).X n))
    (fun n => ModuleCat.ofHom (DirectSum.lmap (fun r => ((C r).d (n+1) n).hom)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply DFinsupp.ext
      intro r
      exact LinearMap.congr_fun
        (ModuleCat.hom_ext_iff.mp ((C r).d_comp_d (n+1+1) (n+1) n)) (z r))

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_InflatedParityFaces
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N] [Module D N] [IsScalarTower k D N]
local notation "A" => TrivSqZeroExt D X

/-- The original D module is inflated by the actual projection, without a new action hypothesis. -/
@[instance_reducible] def inflatedModule : Module A N := Module.compHom N
  { toFun := fun a => a.fst
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_SuffixNaturality
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

variable (M : Type u) [AddCommGroup M] [Module k M] [Module D M]
  [IsScalarTower k D M]
variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]

variable (W : Type u) [AddCommGroup W] [Module k W] [Module D W] [IsScalarTower k D W]

/-- Mathlib's unit-valued totalization sign is exactly the field-valued sign. -/
theorem totalSign_smul (n : ℕ) (v : M) :
    ((-1 : ℤˣ)^n) • v = (-1 : k)^n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hu : (-1 : ℤˣ) • v = -v := by
      change (-1 : ℤ) • v = -v
      exact neg_one_zsmul v
    simpa only [pow_succ, mul_smul, hu, neg_one_smul, smul_neg] using congrArg Neg.neg ih
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance instDecidableEqIndex (r n : ℕ) : DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)

theorem toModule_of_scalar {I : Type} [DecidableEq I]
    (V : I → Type u) [∀ t, AddCommGroup (V t)] [∀ t, Module k (V t)]
    (W : Type u) [AddCommGroup W] [Module k W]
    (f : ∀ t, V t →ₗ[k] W) (t : I) (v : V t) :
    DirectSum.toModule k I W f (DirectSum.of V t v) = f t v :=
  DirectSum.toModule_lof (M := V) (N := W) (φ := f) k t v

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local instance instDecidableEqIndex_1_r734b14_1 (r n : ℕ) : DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
local instance instModuleTrivSqZeroExtCarrier_solutions : Module A N := inflatedModule D X N
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingBarSuffix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local instance leadingBarSuffixInflatedModule : Module A N := inflatedModule D X N
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local instance recursiveSuffixDifferentialIndexDecidableEq_r734b14_1 (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
local instance recursiveSuffixDifferentialInflatedModule : Module A N := inflatedModule D X N
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local instance recursiveSuffixInductionIndexDecidableEq_r734b14_1 (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
local instance instModuleTrivSqZeroExtCarrier_solutions_1 : Module A N := inflatedModule D X N
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixTotal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local instance recursiveSuffixTotalIndexDecidableEq_r734b14_1 (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
local instance instModuleTrivSqZeroExtCarrier_solutions_2 : Module A N := inflatedModule D X N
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingTotalComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local instance instModuleTrivSqZeroExtCarrier_solutions_6 : Module A N := inflatedModule D X N
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IndexedPatternEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X

local instance indexedPatternEmbeddingIndexDecidableEq_r734b14_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
theorem eqToHom_tensor_tmul (L : Type u) [AddCommGroup L] [Module k L]
    (V W : ModuleCat.{u} k) (h : V=W) (x : L) (v : V) :
    (eqToHom (congrArg (fun T : ModuleCat k => ModuleCat.of k (L ⊗[k] T)) h)).hom (x ⊗ₜ[k] v) =
      x ⊗ₜ[k] (eqToHom h).hom v := by
  subst W
  rfl

theorem eqToHom_outer_tmul (V W : ModuleCat.{u} k) (h : V=W) (d : D) (v : V) :
    (eqToHom (congrArg (fun T : ModuleCat k => ModuleCat.of D (D ⊗[k] T)) h)).hom (d ⊗ₜ[k] v) =
      d ⊗ₜ[k] (eqToHom h).hom v := by
  subst W
  rfl

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursivePrefixInclusions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace DerivedBar.ParityBridge
universe u
local notation "c" => ComplexShape.down ℕ
section General
variable {D : Type u} [Ring D]

theorem hom_square_of_heq {U U' V V' : ModuleCat.{u} D} (hU : U=U') (hV : V=V')
    (f : U ⟶ V) (g : U' ⟶ V') (h : HEq f g) :
    f ≫ eqToHom hV = eqToHom hU ≫ g := by
  subst U'; subst V'
  cases h
  simp

theorem hom_heq_of_square {U V V' : ModuleCat.{u} D} (hV : V=V')
    (f : U ⟶ V) (g : U ⟶ V') (h : f ≫ eqToHom hV=g) : HEq f g := by
  subst V'
  simpa using h

theorem barInclusionStep_heq
    (G G' : ModuleCat.{u} D ⥤ ChainComplex (ModuleCat.{u} D) ℕ) [G.Additive] [G'.Additive]
    (hG : G=G')
    {U U' : ModuleCat.{u} D} {V V' : ChainComplex (ModuleCat.{u} D) ℕ}
    (hU : U=U') (hV : V=V') (i q n : ℕ) (h : i+q=n)
    (f : U ⟶ V.X q) (g : U' ⟶ V'.X q) (hf : HEq f g) :
    HEq ((G ⋙ HomologicalComplex.eval _ c i).map f ≫
      (RecursiveTotal.bicomplex (fun _ => G) 0 V).ιTotal c i q n h)
      ((G' ⋙ HomologicalComplex.eval _ c i).map g ≫
        (RecursiveTotal.bicomplex (fun _ => G') 0 V').ιTotal c i q n h) := by
  subst G'; subst U'; subst V'
  cases hf
  rfl

end General

open DerivedBar.RecursiveTotal
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingSupportedComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal

theorem mapIso_trans_congr {R : Type*} [Ring R]
    (F : ModuleCat R ⥤ ModuleCat R) {U V W Z T : ModuleCat R}
    (e : U ≅ V) (f : V ≅ W) (g : W ≅ Z)
    (j : F.obj Z ≅ T) (j' : F.obj W ≅ T) (h : F.mapIso g ≪≫ j = j') :
    F.mapIso (e ≪≫ (f ≪≫ g)) ≪≫ j = F.mapIso (e ≪≫ f) ≪≫ j' := by
  simpa only [Functor.mapIso_trans, Iso.trans_assoc] using
    congrArg (fun t => F.mapIso (e ≪≫ f) ≪≫ t) h

universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X

local instance leadingSupportedComparisonIndexDecidableEq_r734b14_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
theorem iso_mpr_source {U U' V : ModuleCat.{u} D} (h : U=U') (e : U' ≅ V) :
    Eq.mpr (congrArg (fun W : ModuleCat D => W ≅ V) h) e = eqToIso h ≪≫ e := by
  subst U'
  simp

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IndexedAssemblyComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal

theorem assembly_eq {C : Type*} [Category C] {A B V W U T : C}
    {l : A ⟶ B} {e : B ⟶ V} {f : V ⟶ W} {i : A ⟶ U}
    {s : U ⟶ V} {a : U ⟶ T} {b : T ⟶ W} {t : A ⟶ W} {u : B ⟶ W}
    (h₁ : l ≫ e = i ≫ s) (h₂ : s ≫ f = a ≫ b)
    (h₃ : i ≫ a ≫ b = t) (h₄ : l ≫ u = t) : l ≫ e ≫ f = l ≫ u := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, h₃, h₄]

universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X

local instance indexedAssemblyComparisonShapeDecidableEq (n r : ℕ) :
    DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_GlobalIndexedComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local instance globalIndexedComparisonIndexDecidableEq_r734b14_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance instModuleTrivSqZeroExtCarrier_solutions_10 : Module A N := inflatedModule D X N

@[reassoc] theorem eqToHom_chain_d {Y W : ChainComplex (ModuleCat.{u} D) ℕ}
    (h : Y=W) (i j : ℕ) :
    Y.d i j ≫ eqToHom (congrArg (fun T => T.X j) h) =
      eqToHom (congrArg (fun T => T.X i) h) ≫ W.d i j := by
  subst W
  simp

theorem conjugated_differential_comp {C : Type*} [Category C]
    {S₁ S₀ T₁ T₀ V₁ V₀ : C} (a : T₁ ⟶ S₁) (b : S₀ ⟶ T₀)
    (d : S₁ ⟶ S₀) (δ : V₁ ⟶ V₀) (s₁ : T₁ ⟶ V₁) (s₀ : T₀ ⟶ V₀)
    (f₁ : S₁ ⟶ V₁) (f₀ : S₀ ⟶ V₀)
    (h₀ : f₀ = b ≫ s₀) (h₁ : a ≫ f₁ = s₁) (hd : f₁ ≫ δ = d ≫ f₀) :
    (a ≫ d ≫ b) ≫ s₀ = s₁ ≫ δ := by
  rw [Category.assoc, Category.assoc, ← h₀, ← hd, ← Category.assoc, h₁]

theorem inflated_ideal_zero (x : X) (v : N) : (inr x : A) • v=0 := by
  change (0:D) • v=0
  exact zero_smul D v

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IntegerDerivedMultibar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
namespace DerivedBar
universe u
variable (D : Type u) [Ring D]

/-- Choose mathlib's constructed localization, rather than postulating a derived category. -/
local instance instHasDerivedCategoryModuleCat_solutions : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)

/-- Nonnegative homological degree n is genuine integer cochain degree -n;
positive cochain degrees are extended by zero. -/
abbrev integerExtension : ChainComplex (ModuleCat.{u} D) ℕ ⥤
    CochainComplex (ModuleCat.{u} D) ℤ :=
  ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} D)

/-- The actual integer derived-category value of a nonnegative chain complex. -/
def integerQ : ChainComplex (ModuleCat.{u} D) ℕ ⥤ DerivedCategory (ModuleCat.{u} D) :=
  integerExtension D ⋙ DerivedCategory.Q

/-- Exact homology-degree comparison for the integer construction. -/
def integerExtensionHomologyIso (Z : ChainComplex (ModuleCat.{u} D) ℕ) (n : ℕ) :
    ((integerExtension D).obj Z).homology (-(n : ℤ)) ≅ Z.homology n :=
  Z.extendHomologyIso ComplexShape.embeddingDownNat rfl

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_StrictSupportExtension
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
namespace DerivedBar
universe u v w w'
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type w} {ι' : Type w'} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (e : c.Embedding c') [e.IsRelIff] (K : HomologicalComplex C c')
  [K.IsStrictlySupported e]

/-- Actual component isomorphisms for extension after restriction of a complex
which is already zero outside the index embedding. -/
def supportedExtensionXIso (j : ι') : ((K.restriction e).extend e).X j ≅ K.X j := by
  classical
  exact if h : ∃ i, e.f i=j then
    (K.restriction e).extendXIso e h.choose_spec ≪≫ K.restrictionXIso e h.choose_spec
  else
    ((K.restriction e).isZero_extend_X e j (not_exists.mp h)).iso
      (K.isZero_X_of_isStrictlySupported e j (not_exists.mp h))

theorem supportedExtensionXIso_image (i : ι) (j : ι') (hi : e.f i=j) :
    supportedExtensionXIso e K j =
      (K.restriction e).extendXIso e hi ≪≫ K.restrictionXIso e hi := by
  classical
  unfold supportedExtensionXIso
  split_ifs with h
  · have hh : h.choose=i := e.injective_f (h.choose_spec.trans hi.symm)
    subst i
    rfl
  · exact (h ⟨i,hi⟩).elim

/-- The genuine chain isomorphism, including all boundary differentials. -/
def strictSupportExtensionIso : (K.restriction e).extend e ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (supportedExtensionXIso e K) (by
    intro i' j' hij
    classical
    by_cases hi : ∃ i, e.f i=i'
    · by_cases hj : ∃ j, e.f j=j'
      · obtain ⟨i,hi⟩ := hi
        obtain ⟨j,hj⟩ := hj
        rw [supportedExtensionXIso_image e K i i' hi, supportedExtensionXIso_image e K j j' hj,
          extend_d_eq _ e hi hj, restriction_d_eq _ e hi hj]
        simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
      · exact (K.isZero_X_of_isStrictlySupported e j' (not_exists.mp hj)).eq_of_tgt _ _
    · exact ((K.restriction e).isZero_extend_X e i' (not_exists.mp hi)).eq_of_src _ _)
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IntegerCountRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt HomologicalComplex
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local instance integerCountRestrictionIndexDecidableEq_r734b14_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance integerCountRestrictionShapeDecidableEq_r734b14_1 (n r : ℕ) :
    DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
local instance integerCountRestrictionInflatedModule : Module A N := inflatedModule D X N

theorem units_hom_apply (V W : ModuleCat.{u} D) (s : ℤˣ) (f : V ⟶ W) (v : V) :
    (s • f).hom v = s • f.hom v := by
  change ((s:ℤ) • f).hom v = (s:ℤ) • f.hom v
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IntegerCountShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local instance instDecidableEqIndex_3_r734b14_1 (r n : ℕ) : DecidableEq (Index r n) := Classical.decEq _
local instance instDecidableEqShape_r734b14_3 (n r : ℕ) : DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
local instance instModuleTrivSqZeroExtCarrier_solutions_11 : Module A N := inflatedModule D X N
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_DerivedCountShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local instance derivedCountShiftIndexDecidableEq_r734b14_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance derivedCountShiftShapeDecidableEq_r734b14_1 (n r : ℕ) :
    DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
local instance instModuleTrivSqZeroExtCarrier_solutions_12 : Module A N := inflatedModule D X N

local instance instHasDerivedCategoryModuleCat_solutions : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_DirectSumCoproduct
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped DirectSum
noncomputable section
namespace DerivedBar
universe u
variable (D : Type u) [Ring D]

/-- The canonical summand map into the already constructed chain direct sum. -/
def directSumComplexInclusion (S : ℕ → ChainComplex (ModuleCat.{u} D) ℕ) (r : ℕ) :
    S r ⟶ directSumComplex S where
  f n := ModuleCat.ofHom (DirectSum.lof D ℕ (fun s => (S s).X n) r)
  comm' i j hij := by
    change j+1=i at hij
    subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    simp only [directSumComplex, ChainComplex.of_d, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom]
    change DirectSum.lmap (fun r => ((S r).d (j+1) j).hom)
      (DirectSum.lof D ℕ (fun s => (S s).X (j+1)) r v) =
        DirectSum.lof D ℕ (fun s => (S s).X j) r (((S r).d (j+1) j).hom v)
    exact DirectSum.lmap_lof _ _ _

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_CountRetracts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex TrivSqZeroExt
open scoped DirectSum
noncomputable section
namespace DerivedBar
universe u
variable (D : Type u) [Ring D]

/-- Projection from the original chain direct sum to its r-th complex. -/
def directSumComplexProjection (S : ℕ → ChainComplex (ModuleCat.{u} D) ℕ) (r : ℕ) :
    directSumComplex S ⟶ S r where
  f n := ModuleCat.ofHom (DirectSum.component D ℕ (fun s => (S s).X n) r)
  comm' i j hij := by
    change j+1=i at hij
    subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    simp only [directSumComplex, ChainComplex.of_d, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom]
    rfl

@[simp] theorem directSumComplex_inclusion_projection
    (S : ℕ → ChainComplex (ModuleCat.{u} D) ℕ) (r : ℕ) :
    directSumComplexInclusion D S r ≫ directSumComplexProjection D S r = 𝟙 (S r) := by
  ext degree value
  change DirectSum.component D ℕ (fun summand => (S summand).X degree) r
    (DirectSum.lof D ℕ (fun summand => (S summand).X degree) r value) = value
  exact DirectSum.component.lof_self D (M := fun summand => (S summand).X degree) r value

end DerivedBar
namespace DerivedBar.ParityBridge

universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local instance countRetractsInflatedModule : Module A N := inflatedModule D X N
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_CountHomologyDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex TrivSqZeroExt
noncomputable section
namespace DerivedBar
universe u v w z

variable (D : Type u) [Ring D]
local instance countHomologyDetectionHasDerivedCategory :
    HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)

/-- Exact comparison of integer derived homology and the original chain degree. -/
def integerQHomologyIso (K : ChainComplex (ModuleCat.{u} D) ℕ) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} D) (-(n:ℤ))).obj ((integerQ D).obj K) ≅
      K.homology n :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} D) (-(n:ℤ))).app
    ((integerExtension D).obj K) ≪≫ integerExtensionHomologyIso D K n
end DerivedBar
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local instance instModuleTrivSqZeroExtCarrier_solutions_15 : Module A N := inflatedModule D X N
local instance instHasDerivedCategoryModuleCat_solutions_3 : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_CountTorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TrivSqZeroExt
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local instance instModuleTrivSqZeroExtCarrier_solutions_16 : Module A N := inflatedModule D X N
local instance instHasDerivedCategoryModuleCat_solutions_4 : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IntegerCountObject
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local instance integerCountIndexDecidableEq_r734b14_1 (r n : ℕ) : DecidableEq (Index r n) :=
  Classical.decEq _
local instance integerCountShapeDecidableEq_r734b14_1 (n r : ℕ) :
    DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
local instance integerCountInflatedModule : Module A N := inflatedModule D X N
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_ProjectiveTail
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace DerivedBar.ProjectiveTail
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : ChainComplex C ℕ)

abbrev cyclesSequence (i : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles (i+1)) (K.toCycles (i+1) i) (by
    rw [← cancel_mono (K.iCycles i), Category.assoc, K.toCycles_i,
      K.iCycles_d, zero_comp])

def cyclesSequenceKernel (i : ℕ) :
    IsLimit (KernelFork.ofι (cyclesSequence K i).f (cyclesSequence K i).zero) := by
  refine isLimitAux _ (fun s => K.liftCycles s.ι i (by simp) ?_) ?_ ?_
  · calc
      s.ι ≫ K.d (i+1) i = (s.ι ≫ K.toCycles (i+1) i) ≫ K.iCycles i := by simp only [Category.assoc, K.toCycles_i]
      _ = 0 := by rw [show s.ι ≫ K.toCycles (i+1) i = 0 from s.condition]; simp
  · intro s
    exact K.liftCycles_i _ _ _ _
  · intro s m hm
    apply (cancel_mono (K.iCycles (i+1))).mp
    exact hm.trans (K.liftCycles_i _ _ _ _).symm

end DerivedBar.ProjectiveTail

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ExternalTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct


noncomputable section
namespace ExternalTensor

variable (k B M N : Type*) [Field k] [Ring B] [Algebra k B]
  [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
  [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N] [IsScalarTower k Bᵐᵒᵖ N]

def leftAction : B →ₐ[k] Module.End k (M ⊗[k] N) :=
  (Module.End.rTensorAlgHom k M N).comp (Algebra.lsmul k k M)

def rightAction : Bᵐᵒᵖ →ₐ[k] Module.End k (M ⊗[k] N) :=
  (Module.End.lTensorAlgHom k N M).comp (Algebra.lsmul k k N)

omit [Module Bᵐᵒᵖ N] [IsScalarTower k Bᵐᵒᵖ N] in
@[simp] theorem leftAction_tmul (b : B) (m : M) (n : N) :
    leftAction k B M N b (m ⊗ₜ[k] n) = (b • m) ⊗ₜ[k] n := rfl

omit [Module B M] [IsScalarTower k B M] in
@[simp] theorem rightAction_tmul (b : Bᵐᵒᵖ) (m : M) (n : N) :
    rightAction k B M N b (m ⊗ₜ[k] n) = m ⊗ₜ[k] (b • n) := rfl

theorem actions_commute (b : B) (c : Bᵐᵒᵖ) :
    Commute (leftAction k B M N b) (rightAction k B M N c) := by
  apply TensorProduct.ext
  ext m n
  rfl

/-- The genuine enveloping algebra representation; the right action is encoded by Bᵐᵒᵖ. -/
def action : (B ⊗[k] Bᵐᵒᵖ) →ₐ[k] Module.End k (M ⊗[k] N) :=
  Algebra.TensorProduct.lift (leftAction k B M N) (rightAction k B M N)
    (actions_commute k B M N)

@[instance_reducible] def bimodule : Module (B ⊗[k] Bᵐᵒᵖ) (M ⊗[k] N) :=
  Module.compHom (M ⊗[k] N) (action k B M N).toRingHom

@[instance_reducible] def rightModule : Module Bᵐᵒᵖ (M ⊗[k] N) :=
  Module.compHom (M ⊗[k] N) (rightAction k B M N).toRingHom

attribute [local instance] bimodule rightModule

@[simp] theorem smul_tmul (b : B) (c : Bᵐᵒᵖ) (m : M) (n : N) :
    (b ⊗ₜ[k] c) • (m ⊗ₜ[k] n) = (b • m) ⊗ₜ[k] (c • n) := rfl

omit [Module B M] [IsScalarTower k B M] in
@[simp] theorem right_smul_tmul (c : Bᵐᵒᵖ) (m : M) (n : N) :
    c • (m ⊗ₜ[k] n) = m ⊗ₜ[k] (c • n) := rfl


theorem finiteDimensional [FiniteDimensional k M] [FiniteDimensional k N] :
    FiniteDimensional k (M ⊗[k] N) :=
  Module.Finite.equiv
    (TensorProduct.equivFinsuppOfBasisLeft (Module.finBasis k M)).symm


instance rightScalarTower : IsScalarTower k Bᵐᵒᵖ (M ⊗[k] N) where
  smul_assoc r c x := by
    change rightAction k B M N (r • c) x = r • rightAction k B M N c x
    rw [map_smul]
    rfl

instance envelopingScalarTower : IsScalarTower k (B ⊗[k] Bᵐᵒᵖ) (M ⊗[k] N) where
  smul_assoc r a x := by
    change action k B M N (r • a) x = r • action k B M N a x
    rw [map_smul]
    rfl

end ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_InducedColumns
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
noncomputable section

namespace ExternalTensor

attribute [local instance] bimodule rightModule

variable (k B : Type*) [Field k] [Ring B] [Algebra k B]

/-- The actual principal left ideal B e, the image of right multiplication by e. -/
def leftIdeal (e : B) : Submodule B B := (LinearMap.mulRight B e).range

@[simp] theorem mem_leftIdeal (e x : B) : x ∈ leftIdeal B e ↔ ∃ b : B, b * e = x :=
  Iff.rfl

theorem leftIdeal_finiteDimensional [FiniteDimensional k B] (e : B) :
    FiniteDimensional k (leftIdeal B e) :=
  FiniteDimensional.of_injective ((leftIdeal B e).subtype.restrictScalars k)
    Subtype.val_injective

attribute [local instance] leftIdeal_finiteDimensional

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module Bᵐᵒᵖ N] [IsScalarTower k Bᵐᵒᵖ N]

/-- The induced column in Section 4, with its external actions. -/
abbrev Column (e : B) := (leftIdeal B e) ⊗[k] N

theorem column_finiteDimensional [FiniteDimensional k B] (e : B)
    [Module.Finite Bᵐᵒᵖ N] : FiniteDimensional k (Column k B N e) := by
  let : Module.Finite k N := Module.Finite.trans Bᵐᵒᵖ N
  exact finiteDimensional k (leftIdeal B e) N


/-- The distinguished generator e of the principal left ideal. -/
def generator (e : B) : leftIdeal B e := ⟨e, ⟨1, one_mul e⟩⟩

/-- The right-linear insertion used in the vertex maps iota_i. -/
def columnInclusion (e : B) : N →ₗ[Bᵐᵒᵖ] Column k B N e where
  toFun n := generator B e ⊗ₜ[k] n
  map_add' first second := TensorProduct.tmul_add _ first second
  map_smul' c n := (right_smul_tmul k B (leftIdeal B e) N c (generator B e) n).symm

@[simp] theorem columnInclusion_apply (e : B) (n : N) :
    columnInclusion k B N e n = generator B e ⊗ₜ[k] n := rfl

variable {B}
/-- Right multiplication by a path a: i→j maps B e_j to B e_i.
Only the relation a e_i = a is needed for membership in the target ideal. -/
def pathMap (ei ej a : B) (ha : a * ei = a) :
    leftIdeal B ej →ₗ[B] leftIdeal B ei where
  toFun c := ⟨c.val * a, ⟨c.val * a, by simp [LinearMap.mulRight_apply, mul_assoc, ha]⟩⟩
  map_add' c d := Subtype.ext (add_mul c.val d.val a)
  map_smul' b c := Subtype.ext (mul_assoc b c.val a)

@[simp] theorem pathMap_apply (ei ej a : B) (ha : a * ei = a) (c : leftIdeal B ej) :
    (pathMap ei ej a ha c : B) = (c : B) * a := rfl

end ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ColumnComplex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

instance rightModuleK (N : ModuleCat.{u} Bᵐᵒᵖ) : Module k N :=
  Module.compHom N (algebraMap k Bᵐᵒᵖ)
instance rightModuleTower (N : ModuleCat.{u} Bᵐᵒᵖ) : IsScalarTower k Bᵐᵒᵖ N where
  smul_assoc r b n := by
    change (r • b) • n = (algebraMap k Bᵐᵒᵖ r) • (b • n)
    rw [Algebra.smul_def, mul_smul]
attribute [local instance] ExternalTensor.bimodule ExternalTensor.rightModule

abbrev Enveloping := B ⊗[k] Bᵐᵒᵖ
abbrev RightComplex := CochainComplex (ModuleCat.{u} Bᵐᵒᵖ) ℤ
abbrev BiComplex := CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ

@[simp] theorem sum_hom {S : Type*} [Ring S] {X Y : ModuleCat S}
    {I : Type} (s : Finset I) (f : I → (X ⟶ Y)) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom :=
  map_sum ModuleCat.homAddEquiv f s

theorem sum_smul_component_apply {R : Type u} [Ring R] [Algebra k R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} {I J : Type} [Fintype I] [Fintype J]
    (r : I → J → k) (f : I → J → (K ⟶ L)) (n : ℤ) (x : K.X n) :
    ((∑ i, ∑ j, r i j • f i j).f n).hom x =
      ∑ i, ∑ j, algebraMap k R (r i j) • ((f i j).f n).hom x := by
  have eval_sum {I : Type} (s : Finset I) (g : I → (K ⟶ L)) :
      (∑ i ∈ s, g i).f n = ∑ i ∈ s, (g i).f n :=
    map_sum (Hom.fAddMonoidHom n) g s
  simp only [eval_sum, smul_f_apply, ModuleCat.hom_sum,
    ModuleCat.hom_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_DirectedBound
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
open TensorProduct
namespace LittleFinitistic.DirectedBound
universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {n : ℕ}

/-- The displayed algebraic hypotheses of Section 3, Lemma directed-bound.
The field and algebra are unital; zero idempotents are allowed by the source. -/
structure DirectedSystem (k A : Type u) [Field k] [Ring A] [Algebra k A] (n : ℕ) where
  e : Fin n → A
  idem : ∀ i, e i * e i = e i
  orthogonal : ∀ i j, i ≠ j → e i * e j = 0
  complete : ∑ i, e i = 1
  diagonal : ∀ i a, ∃ c : k, e i * a * e i = c • e i
  directed : ∀ i j, j < i → ∀ a, e j * a * e i = 0

namespace DirectedSystem
variable (D : DirectedSystem k A n)
variable (M : Type v) [AddCommGroup M] [Module A M] [Module k M]
  [IsScalarTower k A M]

/-- Evaluation of the free induced module. -/
def evaluation (_D : DirectedSystem k A n) : A ⊗[k] M →ₗ[A] M := AlgebraTensorModule.lift
  { toFun := fun a =>
      { toFun := fun m => a • m
        map_add' := smul_add a
        map_smul' := fun c m => smul_comm a c m }
    map_add' := fun a b => by ext m; exact add_smul a b m
    map_smul' := fun a b => by ext m; exact mul_smul a b m }

@[simp] theorem evaluation_tmul (a : A) (m : M) :
    evaluation M D (a ⊗ₜ[k] m) = a • m := rfl

/-- One summand of the separable diagonal projection. -/
def vertexProjection (i : Fin n) : A ⊗[k] M →ₗ[A] A ⊗[k] M :=
  AlgebraTensorModule.lift
    { toFun := fun a =>
        { toFun := fun m => (a * D.e i) ⊗ₜ[k] (D.e i • m)
          map_add' := fun x y => by simp [smul_add, tmul_add]
          map_smul' := fun c m => by
            simp only [RingHom.id_apply, smul_comm (D.e i) c, tmul_smul] }
      map_add' := fun a b => by ext m; simp [add_mul, add_tmul]
      map_smul' := fun a b => by
        ext m
        change ((a * b) * D.e i) ⊗ₜ[k] (D.e i • m) =
          a • ((b * D.e i) ⊗ₜ[k] (D.e i • m))
        rw [smul_tmul', smul_eq_mul, mul_assoc] }

@[simp] theorem vertexProjection_tmul (i : Fin n) (a : A) (m : M) :
    D.vertexProjection M i (a ⊗ₜ[k] m) = (a * D.e i) ⊗ₜ[k] (D.e i • m) := rfl

def projection : A ⊗[k] M →ₗ[A] A ⊗[k] M := ∑ i, D.vertexProjection M i

@[simp] theorem projection_tmul (a : A) (m : M) :
    D.projection M (a ⊗ₜ[k] m) = ∑ i, (a * D.e i) ⊗ₜ[k] (D.e i • m) := by
  simp [projection]


open CategoryTheory

end DirectedSystem

open CategoryTheory
end LittleFinitistic.DirectedBound

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_ThreeVertexAlgebra
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic
universe u v
variable {k V W U : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]

/-- Coordinates by the six possible path endpoints: three vertices,
0-to-1 arrows, 1-to-2 arrows, and length-two paths modulo relations. -/
abbrev ThreeVertexAlgebra (_μ : W →ₗ[k] V →ₗ[k] U) := k × k × k × V × W × U

namespace ThreeVertexAlgebra
variable (μ : W →ₗ[k] V →ₗ[k] U)

instance instAddCommGroup : AddCommGroup (ThreeVertexAlgebra μ) :=
  inferInstanceAs (AddCommGroup (k × k × k × V × W × U))
instance instModule : Module k (ThreeVertexAlgebra μ) :=
  inferInstanceAs (Module k (k × k × k × V × W × U))

@[simp] theorem zero_eq : (0 : ThreeVertexAlgebra μ) = (0, 0, 0, 0, 0, 0) := rfl
@[simp] theorem add_eq (x y : ThreeVertexAlgebra μ) :
    x + y = (x.1+y.1, x.2.1+y.2.1, x.2.2.1+y.2.2.1,
      x.2.2.2.1+y.2.2.2.1, x.2.2.2.2.1+y.2.2.2.2.1,
      x.2.2.2.2.2+y.2.2.2.2.2) := rfl
@[simp] theorem smul_eq (c : k) (x : ThreeVertexAlgebra μ) :
    c • x = (c*x.1, c*x.2.1, c*x.2.2.1,
      c • x.2.2.2.1, c • x.2.2.2.2.1, c • x.2.2.2.2.2) := rfl

def mul (x y : ThreeVertexAlgebra μ) : ThreeVertexAlgebra μ :=
  (x.1 * y.1, x.2.1 * y.2.1, x.2.2.1 * y.2.2.1,
   y.1 • x.2.2.2.1 + x.2.1 • y.2.2.2.1,
   y.2.1 • x.2.2.2.2.1 + x.2.2.1 • y.2.2.2.2.1,
   y.1 • x.2.2.2.2.2 + μ x.2.2.2.2.1 y.2.2.2.1 + x.2.2.1 • y.2.2.2.2.2)

def unit : ThreeVertexAlgebra μ := (1, 1, 1, 0, 0, 0)

@[ext] theorem ext (x y : ThreeVertexAlgebra μ)
    (h0 : x.1 = y.1) (h1 : x.2.1 = y.2.1) (h2 : x.2.2.1 = y.2.2.1)
    (hv : x.2.2.2.1 = y.2.2.2.1) (hw : x.2.2.2.2.1 = y.2.2.2.2.1)
    (hu : x.2.2.2.2.2 = y.2.2.2.2.2) : x = y :=
  Prod.ext h0 (Prod.ext h1 (Prod.ext h2 (Prod.ext hv (Prod.ext hw hu))))

instance instRing : Ring (ThreeVertexAlgebra μ) where
  __ := (inferInstance : AddCommGroup (ThreeVertexAlgebra μ))
  mul := mul μ
  one := unit μ
  mul_assoc x y z := by
    change mul μ (mul μ x y) z = mul μ x (mul μ y z)
    apply Prod.ext <;> dsimp [mul]
    · ring
    apply Prod.ext
    · ring
    apply Prod.ext
    · ring
    apply Prod.ext
    · simp only [smul_add, smul_smul]; module
    apply Prod.ext
    · simp only [smul_add, smul_smul]; module
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_add, smul_smul]; module
  one_mul x := by
    change mul μ (unit μ) x = x
    apply Prod.ext <;> dsimp [mul, unit]
    · simp
    apply Prod.ext
    · simp
    apply Prod.ext
    · simp
    apply Prod.ext
    · simp
    apply Prod.ext <;> simp
  mul_one x := by
    change mul μ x (unit μ) = x
    apply Prod.ext <;> dsimp [mul, unit]
    · simp
    apply Prod.ext
    · simp
    apply Prod.ext
    · simp
    apply Prod.ext
    · simp
    apply Prod.ext <;> simp
  left_distrib x y z := by
    change mul μ x (y + z) = mul μ x y + mul μ x z
    rw [add_eq μ (mul μ x y) (mul μ x z), add_eq μ y z]
    ext <;> simp [mul, mul_add, smul_add, add_smul, map_add] <;> abel
  right_distrib x y z := by
    change mul μ (x + y) z = mul μ x z + mul μ y z
    rw [add_eq μ (mul μ x z) (mul μ y z), add_eq μ x y]
    ext <;> simp [mul, add_mul, smul_add, add_smul, map_add] <;> abel
  zero_mul x := by
    change (mul μ 0 x : k × k × k × V × W × U) = 0
    ext <;> simp [mul]
  mul_zero x := by
    change (mul μ x 0 : k × k × k × V × W × U) = 0
    ext <;> simp [mul]


@[simp] theorem mul_eq (x y : ThreeVertexAlgebra μ) : x * y = mul μ x y := rfl
@[simp] theorem one_eq : (1 : ThreeVertexAlgebra μ) = unit μ := rfl

instance instAlgebra : Algebra k (ThreeVertexAlgebra μ) where
  algebraMap :=
    { toFun := fun c => (c, c, c, 0, 0, 0)
      map_zero' := (zero_eq μ).symm
      map_one' := rfl
      map_add' := fun a b => by
        change ((a+b, a+b, a+b, 0, 0, 0) : ThreeVertexAlgebra μ) =
          (a, a, a, 0, 0, 0) + (b, b, b, 0, 0, 0)
        rw [add_eq μ]
        simp
      map_mul' := fun a b => by
        change ((a*b, a*b, a*b, 0, 0, 0) : ThreeVertexAlgebra μ) =
          mul μ (a, a, a, 0, 0, 0) (b, b, b, 0, 0, 0)
        simp [mul] }
  commutes' c x := by
    change mul μ (c, c, c, 0, 0, 0) x = mul μ x (c, c, c, 0, 0, 0)
    ext <;> simp [mul, mul_comm]
  smul_def' c x := by
    change c • x = mul μ (c, c, c, 0, 0, 0) x
    rw [smul_eq μ]
    simp [mul]

/-- The three vertex idempotents, in the manuscript's order. -/
def vertex : Fin 3 → ThreeVertexAlgebra μ
  | ⟨0, _⟩ => (1, 0, 0, 0, 0, 0)
  | ⟨1, _⟩ => (0, 1, 0, 0, 0, 0)
  | ⟨2, _⟩ => (0, 0, 1, 0, 0, 0)

def directedSystem : DirectedBound.DirectedSystem k (ThreeVertexAlgebra μ) 3 where
  e := vertex μ
  idem i := by fin_cases i <;> ext <;> simp [vertex, mul]
  orthogonal i j hij := by
    fin_cases i <;> fin_cases j <;> simp_all [vertex, mul]
  complete := by
    simp [Fin.sum_univ_succ, vertex, unit, add_eq μ]
  diagonal i a := by
    fin_cases i
    · exact ⟨a.1, by ext <;> simp [vertex, mul, smul_eq μ]⟩
    · exact ⟨a.2.1, by ext <;> simp [vertex, mul, smul_eq μ]⟩
    · exact ⟨a.2.2.1, by ext <;> simp [vertex, mul, smul_eq μ]⟩
  directed i j hij a := by
    fin_cases i <;> fin_cases j <;> simp_all [vertex, mul]

open CategoryTheory
end ThreeVertexAlgebra
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_QuadraticEncoding
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {d t : ℕ}

abbrev Arrows (k : Type u) (d : ℕ) := Fin (d + 1) → k
end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_CornerProjection
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace LittleFinitistic.CornerProjection
open ThreeVertexAlgebra
universe u
variable {k V W U : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)

theorem videm (i : Fin 3) : vertex μ i * vertex μ i = vertex μ i :=
  (directedSystem μ).idem i

end LittleFinitistic.CornerProjection

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.VertexFunctor
universe u
variable {A B : Type u} [Ring A] [Ring B]
variable (β : B →+* A) (e : A) (he : e*e=e) (hc : ∀ b, e*β b=β b*e)

abbrev restricted (M : ModuleCat.{u} A) := (ModuleCat.restrictScalars β).obj M

/-- The original vertex action is linear for the commuting right restriction. -/
def action (M : ModuleCat.{u} A) : restricted β M →ₗ[B] restricted β M where
  toFun m := e • (m : M)
  map_add' x y := smul_add _ _ _
  map_smul' b m := by
    change e • (β b • (m : M)) = β b • (e • (m : M))
    rw [← mul_smul,← mul_smul,hc]

def fixed (M : ModuleCat.{u} A) : Submodule B (restricted β M) :=
  (action β e hc M - LinearMap.id).ker

@[simp] theorem mem_fixed (M : ModuleCat.{u} A) (m : restricted β M) :
    m ∈ fixed β e hc M ↔ e • (m : M) = m := by
  simp [fixed,action,sub_eq_zero]

/-- The genuine projection onto the vertex component. -/
def projection (M : ModuleCat.{u} A) : restricted β M →ₗ[B] fixed β e hc M :=
  (action β e hc M).codRestrict _ (by
    intro m
    rw [mem_fixed]
    change e • (e • (m : M)) = e • (m : M)
    rw [← mul_smul,he])

/-- Module maps restrict to the actual vertex fixed submodules. -/
def map {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    fixed β e hc M →ₗ[B] fixed β e hc N where
  toFun m := ⟨f.hom m.val,by
    apply (mem_fixed β e hc N _).2
    have hm := (mem_fixed β e hc M m.val).1 m.property
    exact (f.hom.map_smul e (m.val : M)).symm.trans (congrArg f.hom hm)⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' b x := by
    apply Subtype.ext
    change f.hom (β b • (x.val : M)) = β b • f.hom x.val
    exact f.hom.map_smul _ _

/-- The actual vertex-component functor; it retains the original right action. -/
def functor : ModuleCat.{u} A ⥤ ModuleCat.{u} B where
  obj M := ModuleCat.of B (fixed β e hc M)
  map f := ModuleCat.ofHom (map β e hc f)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

instance additive : (functor β e hc).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

include he in
/-- Applying a vertex component preserves actual short exact sequences. -/
theorem map_shortExact (S : ShortComplex (ModuleCat.{u} A)) (hS : S.ShortExact) :
    (S.map (functor β e hc)).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro x
    constructor
    · intro hx
      have hx' : S.g.hom x.val = 0 := congrArg Subtype.val hx
      obtain ⟨y,hy⟩ := (ShortComplex.moduleCat_exact_iff S).1 hS.exact x.val hx'
      refine ⟨projection β e he hc S.X₁ y,?_⟩
      apply Subtype.ext
      change S.f.hom (e • y) = x.val
      rw [S.f.hom.map_smul,hy]
      exact (mem_fixed β e hc S.X₂ x.val).1 x.property
    · rintro ⟨y,rfl⟩
      apply Subtype.ext
      exact S.moduleCat_zero_apply y.val
  · intro x y h
    apply Subtype.ext
    apply hS.moduleCat_injective_f
    exact congrArg Subtype.val h
  · intro z
    obtain ⟨y,hy⟩ := hS.moduleCat_surjective_g z.val
    refine ⟨projection β e he hc S.X₂ y,?_⟩
    apply Subtype.ext
    change S.g.hom (e • y) = z.val
    rw [S.g.hom.map_smul,hy]
    exact (mem_fixed β e hc S.X₃ z.val).1 z.property
end LittleFinitistic.VertexFunctor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleVertex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.BimoduleVertex

section
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

abbrev restriction : Bᵐᵒᵖ →+* B ⊗[k] Bᵐᵒᵖ :=
  Algebra.TensorProduct.includeRight.toRingHom
abbrev vertex (e : B) : B ⊗[k] Bᵐᵒᵖ := e ⊗ₜ[k] 1

theorem vertex_idempotent (e : B) (he : e*e=e) :
    vertex k B e * vertex k B e = vertex k B e := by
  simp [vertex,Algebra.TensorProduct.tmul_mul_tmul,he]

theorem vertex_commute (e : B) (b : Bᵐᵒᵖ) :
    vertex k B e * restriction k B b = restriction k B b * vertex k B e := by
  simp [vertex,restriction,Algebra.TensorProduct.tmul_mul_tmul]

/-- The original left vertex action, with the right B-module structure retained. -/
abbrev functor (e : B) : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ) ⥤ ModuleCat.{u} Bᵐᵒᵖ :=
  VertexFunctor.functor (restriction k B) (vertex k B e) (vertex_commute k B e)

theorem map_shortExact (e : B) (he : e*e=e)
    (S : ShortComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ))) (hS : S.ShortExact) :
    (S.map (functor k B e)).ShortExact :=
  VertexFunctor.map_shortExact _ _ (vertex_idempotent k B e he) _ S hS

end
universe u
attribute [local instance] ExternalTensor.Section4.rightModuleK
  ExternalTensor.rightModule ExternalTensor.bimodule

end LittleFinitistic.BimoduleVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_RectificationTotal
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.RectificationTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex HomComplex

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
variable {L₀ L₁ L₂ : CochainComplex C ℤ} (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁)
  (h : Homotopy (q ≫ p) 0)

/-- The relation null-homotopy extends p over the first cone. -/
noncomputable def rectifyingMap : mappingCone q ⟶ L₀ :=
  mappingCone.desc q (Cochain.ofHomotopy h) p (by simp [δ_ofHomotopy])

/-- A genuine cochain complex rectifying a three-column homotopy diagram.
The cone convention fixes all differential signs; the three-column term
isomorphism is given below. -/
noncomputable def total : CochainComplex C ℤ := mappingCone (rectifyingMap p q h)

/-- The total complex has exactly the three finite columns. -/
noncomputable def termIso (i : ℤ) :
    (total p q h).X i ≅ (L₂.X (i+2) ⊞ L₁.X (i+1)) ⊞ L₀.X i :=
  homotopyCofiber.XIsoBiprod (rectifyingMap p q h) i (i+1) (by simp) ≪≫
    biprod.mapIso (homotopyCofiber.XIsoBiprod q (i+1) (i+2) (by simp; omega)) (Iso.refl _)

@[simp] theorem total_isZero (i : ℤ) :
    IsZero ((total p q h).X i) ↔
      (IsZero (L₂.X (i+2)) ∧ IsZero (L₁.X (i+1))) ∧ IsZero (L₀.X i) := by
  rw [(termIso p q h i).isZero_iff,biprod_isZero_iff,biprod_isZero_iff]

/-- The original zero column includes by an actual chain map. -/
noncomputable def inclusion : L₀ ⟶ total p q h := mappingCone.inr (rectifyingMap p q h)

/-- The first-column boundary vanishes by a specified chain homotopy in the total.
For the induced B-arrow columns this is exactly the arrow compatibility homotopy. -/
noncomputable def boundaryHomotopy : Homotopy (p ≫ inclusion p q h) 0 := by
  let f := rectifyingMap p q h
  let H : Homotopy (f ≫ mappingCone.inr f) 0 :=
    (Cochain.equivHomotopy _ _).symm ⟨mappingCone.inl f,by simp⟩
  have H' := H.compLeft (mappingCone.inr q)
  have heq : mappingCone.inr q ≫ f = p := mappingCone.inr_desc _ _ _ _
  rw [← Category.assoc,heq,CategoryTheory.Limits.comp_zero] at H'
  exact H'

end LittleFinitistic.RectificationTotal

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_TensorComplex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace LittleFinitistic.TensorComplex
attribute [local instance] ExternalTensor.rightModule
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

abbrev ScalarModule (N : ModuleCat.{u} Bᵐᵒᵖ) :=
  (ModuleCat.restrictScalars (algebraMap k Bᵐᵒᵖ)).obj N

instance scalarTower (N : ModuleCat.{u} Bᵐᵒᵖ) :
    IsScalarTower k Bᵐᵒᵖ (ScalarModule k B N) where
  smul_assoc c b n := by
    change (c • b) • (n : N) = algebraMap k Bᵐᵒᵖ c • (b • (n : N))
    rw [Algebra.smul_def,mul_smul]

end LittleFinitistic.TensorComplex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_ArrowBasisIso
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.ArrowBasisIso
universe u
variable (k : Type u) [Field k] (d : ℕ)

abbrev family : Fin (d+1) → ModuleCat.{u} k := fun _ => ModuleCat.of k k

end LittleFinitistic.ArrowBasisIso

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Iteration_BinomialBiproduct
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace ExternalTensor.Binomial
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]

/-- Distribute a finite biproduct of binary biproducts and retain the two branch labels. -/
def biproductBiprod {I : Type} [Fintype I] (f g : I → C) :
    (⨁ fun i => f i ⊞ g i) ≅ ⨁ (Sum.elim f g) where
  hom := biproduct.desc fun i => biprod.desc
    (biproduct.ι (Sum.elim f g) (Sum.inl i)) (biproduct.ι (Sum.elim f g) (Sum.inr i))
  inv := biproduct.desc fun x => match x with
    | .inl i => biprod.inl ≫ biproduct.ι (fun i => f i ⊞ g i) i
    | .inr i => biprod.inr ≫ biproduct.ι (fun i => f i ⊞ g i) i
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro i
    apply biprod.hom_ext'
    · simp only [biproduct.ι_desc_assoc, Category.comp_id]
      erw [biprod.inl_desc_assoc, biproduct.ι_desc]
      rfl
    · simp only [biproduct.ι_desc_assoc, Category.comp_id]
      erw [biprod.inr_desc_assoc, biproduct.ι_desc]
      rfl
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro x
    cases x <;> erw [biproduct.ι_desc_assoc]
    · erw [Category.assoc, biproduct.ι_desc]
      erw [biprod.inl_desc, Category.comp_id]
    · erw [Category.assoc, biproduct.ι_desc]
      erw [biprod.inr_desc, Category.comp_id]

variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]

/-- Shift a binary splitting, using the actual shift functors and their addition isomorphism. -/
def splitShift (Phi : C ⥤ C) [Phi.Additive] [Phi.CommShift ℤ]
    (X Z : C) (b d t : ℤ) (split : Phi.obj X ≅ Z⟦b⟧ ⊞ Z⟦b+d⟧) :
    Phi.obj (X⟦t⟧) ≅ Z⟦b+t⟧ ⊞ Z⟦b+d+t⟧ :=
  (Phi.commShiftIso t).app X ≪≫ (shiftFunctor C t).mapIso split ≪≫
    (shiftFunctor C t).mapBiprod _ _ ≪≫
    biprod.mapIso (shiftAdd Z b t).symm (shiftAdd Z (b+d) t).symm
end ExternalTensor.Binomial

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Iteration_BinomialIndex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace ExternalTensor.Binomial

/-- A branch records the choices of the two summands during iteration. -/
def Branch : ℕ → Type
  | 0 => Unit
  | n + 1 => Branch n ⊕ Branch n

instance branchFintype : (n : ℕ) → Fintype (Branch n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => letI := branchFintype n; inferInstanceAs (Fintype (Branch n ⊕ Branch n))

def weight : {n : ℕ} → Branch n → ℕ
  | 0, _ => 0
  | _ + 1, .inl x => weight x
  | _ + 1, .inr x => weight x + 1

theorem weight_le : ∀ {n : ℕ} (x : Branch n), weight x ≤ n
  | 0, _ => Nat.le_refl _
  | _n + 1, .inl x => Nat.le_succ_of_le (weight_le x)
  | _n + 1, .inr x => Nat.succ_le_succ (weight_le x)

/-- The left branch has weight zero exactly when the old branch does. -/
def zeroFiber (n : ℕ) : {x : Branch (n+1) // weight x = 0} ≃
    {x : Branch n // weight x = 0} where
  toFun x := match x with
    | ⟨.inl x, h⟩ => ⟨x, h⟩
    | ⟨.inr x, h⟩ => False.elim (Nat.noConfusion h)
  invFun x := ⟨.inl x.val, x.property⟩
  left_inv x := by
    rcases x with ⟨x | x, h⟩
    · rfl
    · exact False.elim (Nat.noConfusion h)
  right_inv x := rfl

/-- The two disjoint ways to achieve weight q+1 give Pascal's recurrence. -/
def succFiber (n q : ℕ) : {x : Branch (n+1) // weight x = q+1} ≃
    ({x : Branch n // weight x = q+1} ⊕ {x : Branch n // weight x = q}) where
  toFun x := match x with
    | ⟨.inl x, h⟩ => .inl ⟨x, h⟩
    | ⟨.inr x, h⟩ => .inr ⟨x, Nat.succ.inj h⟩
  invFun x := match x with
    | .inl x => ⟨.inl x.val, x.property⟩
    | .inr x => ⟨.inr x.val, congrArg Nat.succ x.property⟩
  left_inv x := by rcases x with ⟨x | x, h⟩ <;> rfl
  right_inv x := by cases x <;> rfl

theorem card_weight (n q : ℕ) :
    Fintype.card {x : Branch n // weight x = q} = Nat.choose n q := by
  classical
  induction n generalizing q with
  | zero =>
    cases q with
    | zero =>
      let : Unique {x : Branch 0 // weight x = 0} :=
        ⟨⟨⟨(), rfl⟩⟩, fun x => by rcases x with ⟨⟨⟩, h⟩; rfl⟩
      simp
    | succ q =>
      let : IsEmpty {x : Branch 0 // weight x = q+1} :=
        ⟨fun x => Nat.noConfusion x.property⟩
      simp
  | succ n ih =>
    cases q with
    | zero => rw [Fintype.card_congr (zeroFiber n), ih]; simp
    | succ q => rw [Fintype.card_congr (succFiber n q), Fintype.card_sum, ih, ih,
        Nat.choose_succ_succ, Nat.add_comm]

def degree {n : ℕ} (x : Branch n) : Fin (n+1) := ⟨weight x, Nat.lt_succ_of_le (weight_le x)⟩

def degreeFiber (n : ℕ) (q : Fin (n+1)) :
    {x : Branch n // degree x = q} ≃ {x : Branch n // weight x = q.val} :=
  Equiv.subtypeEquivRight (fun _ => Fin.ext_iff)

def fiberFin (n : ℕ) (q : Fin (n+1)) :
    {x : Branch n // degree x = q} ≃ Fin (Nat.choose n q.val) := by
  classical
  exact Fintype.equivFinOfCardEq ((Fintype.card_congr (degreeFiber n q)).trans (card_weight n q))

/-- Group branches by their weight, with the binomial coefficient as the exact fiber size. -/
def groupEquiv (n : ℕ) : Branch n ≃ Σ q : Fin (n+1), Fin (Nat.choose n q.val) :=
  (Equiv.sigmaFiberEquiv (@degree n)).symm.trans (Equiv.sigmaCongrRight (fiberFin n))

@[simp] theorem groupEquiv_fst (n : ℕ) (x : Branch n) :
    (groupEquiv n x).1 = degree x := rfl
end ExternalTensor.Binomial

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Iteration_BinomialIteration
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace ExternalTensor.Binomial
universe v u w
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
variable {S : Type w} (Phi : C ⥤ C) [Phi.Additive] [Phi.CommShift ℤ]
variable (M : S → C) (H : S → S) (b d : ℤ)

/-- Apply the splitting independently at each object; no naturality in S is present. -/
def branchIteration (split : ∀ Y, Phi.obj (M Y) ≅ (M (H Y))⟦b⟧ ⊞ (M (H Y))⟦b+d⟧)
    (j : ℕ) (Y : S) :
    (Phi.obj^[j]) (M Y) ≅
      ⨁ fun x : Branch j => (M ((H^[j]) Y))⟦(j : ℤ)*b + d*(weight x : ℤ)⟧ := by
  induction j with
  | zero =>
    letI : Unique (Branch 0) := inferInstanceAs (Unique Unit)
    simpa only [Function.iterate_zero_apply, Nat.cast_zero, zero_mul, mul_zero, zero_add, weight] using
      (shiftZero ℤ (M Y)).symm ≪≫
        (biproductUniqueIso (fun _ : Branch 0 => (M Y)⟦(0 : ℤ)⟧)).symm
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    refine Phi.mapIso ih ≪≫ Phi.mapBiproduct _ ≪≫ ?_
    let X := M ((H^[j+1]) Y)
    let f : Branch j → C := fun x => X⟦((j+1 : ℕ) : ℤ)*b + d*(weight x : ℤ)⟧
    let g : Branch j → C := fun x => X⟦((j+1 : ℕ) : ℤ)*b + d*((weight x+1 : ℕ) : ℤ)⟧
    have step (x : Branch j) :
        Phi.obj ((M ((H^[j]) Y))⟦(j : ℤ)*b+d*(weight x : ℤ)⟧) ≅ f x ⊞ g x := by
      simpa only [f, g, X, Function.iterate_succ_apply', Nat.cast_add, Nat.cast_one,
        add_mul, mul_add, mul_one, one_mul, add_assoc, add_left_comm, add_comm] using
        splitShift Phi (M ((H^[j]) Y)) (M (H ((H^[j]) Y))) b d
          ((j : ℤ)*b+d*(weight x : ℤ)) (split ((H^[j]) Y))
    refine biproduct.mapIso step ≪≫ biproductBiprod f g ≪≫ biproduct.mapIso (J := Branch j ⊕ Branch j)
      (f := Sum.elim f g)
      (g := fun x : Branch j ⊕ Branch j =>
        (M ((H^[j+1]) Y))⟦((j+1 : ℕ) : ℤ)*b + d*(weight (n := j+1) x : ℤ)⟧) ?_
    intro x
    cases x with
    | inl x => exact Iso.refl _
    | inr x => exact Iso.refl _

/-- The manuscript's repeated finite biproduct, including the multiplicity index. -/
def binomialObject (j : ℕ) (X : C) : C :=
  ⨁ fun q : Fin (j+1) => ⨁ fun _ : Fin (Nat.choose j q.val) =>
    X⟦(j : ℤ)*b + d*(q.val : ℤ)⟧

/-- Regroup by weight using the proved fiber cardinality, not an assumed decomposition. -/
def groupBiproduct (j : ℕ) (X : C) :
    (⨁ fun x : Branch j => X⟦(j : ℤ)*b + d*(weight x : ℤ)⟧) ≅
      binomialObject b d j X :=
  biproduct.whiskerEquiv
    (f := fun x : Branch j => X⟦(j : ℤ)*b + d*(weight x : ℤ)⟧)
    (g := fun p : Σ q : Fin (j+1), Fin (Nat.choose j q.val) =>
      X⟦(j : ℤ)*b + d*(p.1.val : ℤ)⟧)
    (groupEquiv j) (fun _ => Iso.refl _) ≪≫
    (biproductBiproductIso (fun q : Fin (j+1) => Fin (Nat.choose j q.val))
      (fun q _ => X⟦(j : ℤ)*b + d*(q.val : ℤ)⟧)).symm

/-- Categorical binomial iteration with a common shift offset. -/
def binomialIteration (split : ∀ Y, Phi.obj (M Y) ≅ (M (H Y))⟦b⟧ ⊞ (M (H Y))⟦b+d⟧)
    (j : ℕ) (Y : S) :
    (Phi.obj^[j]) (M Y) ≅ binomialObject b d j (M ((H^[j]) Y)) :=
  branchIteration Phi M H b d split j Y ≪≫ groupBiproduct b d j _

end ExternalTensor.Binomial

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Iteration_IntegerIterateSupport
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace DerivedBar.IterateSupport
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance instHasDerivedCategoryModuleCat_solutions : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)
end DerivedBar.IterateSupport

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Iteration_IntegerIterateAmplitude
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace DerivedBar.IterateSupport
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [IsScalarTower k D X]
local instance instHasDerivedCategoryModuleCat_solutions_2 : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)
end DerivedBar.IterateSupport

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Iteration_IntegerIterateExtinction
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex ZeroObject
namespace DerivedBar.IterateSupport
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance integerIterateExtinctionHasDerivedCategory : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)

end DerivedBar.IterateSupport

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_AdditiveSplitImage
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.AdditiveSplitImage
universe u v
variable {C : Type*} [Category C]
variable {R : Type u} [Ring R]
variable (F : C ⥤ ModuleCat.{v} R)
variable {V M : C} (i : V ⟶ M) (p : M ⟶ V) (hip : i ≫ p = 𝟙 V)

def fixed : Submodule R (F.obj M) := ((F.map (p ≫ i)).hom - LinearMap.id).ker

@[simp] theorem mem_fixed (x : F.obj M) : x ∈ fixed F i p ↔ (F.map (p ≫ i)).hom x = x := by
  simp [fixed,sub_eq_zero]

def forward : F.obj V →ₗ[R] fixed F i p :=
  (F.map i).hom.codRestrict _ (by
    intro x
    rw [mem_fixed]
    have he : F.map i ≫ F.map (p ≫ i) = F.map i := by
      rw [← F.map_comp,← Category.assoc,hip,Category.id_comp]
    exact congrArg (fun a : F.obj V ⟶ F.obj M => a.hom x) he)

def inverse : fixed F i p →ₗ[R] F.obj V :=
  (F.map p).hom.comp (fixed F i p).subtype

/-- Any additive module-valued functor preserves the actual image of a split idempotent. -/
def equiv : F.obj V ≃ₗ[R] fixed F i p where
  __ := forward F i p hip
  invFun := inverse F i p
  left_inv x := by
    have he : F.map i ≫ F.map p = 𝟙 (F.obj V) := by rw [← F.map_comp,hip,F.map_id]
    exact congrArg (fun a : F.obj V ⟶ F.obj V => a.hom x) he
  right_inv x := by
    apply Subtype.ext
    change (F.map i).hom ((F.map p).hom x.val) = x.val
    rw [show (F.map i).hom ((F.map p).hom x.val) = (F.map (p ≫ i)).hom x.val from
      congrArg (fun a : F.obj M ⟶ F.obj M => a.hom x.val) (F.map_comp p i).symm]
    exact (mem_fixed F i p x.val).1 x.property

@[simp] theorem equiv_apply_val (x : F.obj V) : (equiv F i p hip x).val = (F.map i).hom x := rfl
@[simp] theorem equiv_symm_apply (x : fixed F i p) : (equiv F i p hip).symm x = (F.map p).hom x.val := rfl
end LittleFinitistic.AdditiveSplitImage

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_DiagramAssembly
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
namespace ExternalTensor.Section4
universe u
variable {k : Type u} [Field k]
variable {C : Type u} [Category C] [Preadditive C] [Linear k C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]

/-- The concrete column/map interface. No composite or null-homotopy is assumed.
The three equations are path naturality, the algebra relations, and the chosen
relation homotopies after column induction. -/
structure AssemblyData where
  V₀ : C
  V₁ : C
  V₂ : C
  U : A → C
  V : J → C
  W : R → C
  pa₀ : ∀ a, U a ⟶ V₀
  pa₁ : ∀ a, U a ⟶ V₁
  pb₁ : ∀ b, V b ⟶ V₁
  pb₂ : ∀ b, V b ⟶ V₂
  qa : ∀ relation arrow, J → (W relation ⟶ U arrow)
  qb : ∀ relation, A → ∀ arrow, W relation ⟶ V arrow
  rel : ∀ r, W r ⟶ V₂
  middle : ∀ r a b, qa r a b ≫ pa₁ a = qb r a b ≫ pb₁ b
  first : ∀ r, ∑ a, ∑ b, qa r a b ≫ pa₀ a = 0
  last : ∀ r, ∑ a, ∑ b, qb r a b ≫ pb₂ b = rel r

namespace AssemblyData
variable (s : AssemblyData (C := C) (A := A) (J := J) (R := R))
abbrev L₀ := s.V₀ ⊞ (s.V₁ ⊞ s.V₂)
abbrev L₁ := (⨁ s.U) ⊞ (⨁ s.V)
abbrev L₂ := ⨁ s.W
abbrev in₀ : s.V₀ ⟶ s.L₀ := biprod.inl
abbrev in₁ : s.V₁ ⟶ s.L₀ := biprod.inl ≫ biprod.inr
abbrev in₂ : s.V₂ ⟶ s.L₀ := biprod.inr ≫ biprod.inr

def p : s.L₁ ⟶ s.L₀ :=
  biprod.desc
    (biproduct.desc fun a => s.pa₀ a ≫ s.in₀ - s.pa₁ a ≫ s.in₁)
    (biproduct.desc fun b => s.pb₁ b ≫ s.in₁ - s.pb₂ b ≫ s.in₂)

def q : s.L₂ ⟶ s.L₁ :=
  biproduct.desc fun r => ∑ a, ∑ b,
    (s.qa r a b ≫ biproduct.ι s.U a ≫ biprod.inl +
     s.qb r a b ≫ biproduct.ι s.V b ≫ biprod.inr)

/-- The complete cancellation in Section 4, including the minus sign. -/
theorem composite : s.q ≫ s.p =
    -(biproduct.desc fun r => s.rel r ≫ s.in₂) := by
  apply biproduct.hom_ext'
  intro r
  simp only [q, biproduct.ι_desc_assoc, Preadditive.comp_neg,
    biproduct.ι_desc]
  simp only [Preadditive.sum_comp, Preadditive.add_comp, Category.assoc, p,
    biprod.inl_desc, biprod.inr_desc, biproduct.ι_desc, Preadditive.comp_sub,
    ]
  simp only [← Category.assoc, s.middle]
  simp only [Category.assoc]
  have cancel (a : A) (b : J) :
      s.qa r a b ≫ s.pa₀ a ≫ s.in₀ - s.qb r a b ≫ s.pb₁ b ≫ s.in₁ +
      (s.qb r a b ≫ s.pb₁ b ≫ s.in₁ - s.qb r a b ≫ s.pb₂ b ≫ s.in₂) =
      s.qa r a b ≫ s.pa₀ a ≫ s.in₀ - s.qb r a b ≫ s.pb₂ b ≫ s.in₂ := by abel
  simp_rw [cancel, Finset.sum_sub_distrib]
  have hf := congrArg (fun z => z ≫ s.in₀) (s.first r)
  have hl := congrArg (fun z => z ≫ s.in₂) (s.last r)
  simp only [Preadditive.sum_comp, Category.assoc, zero_comp] at hf hl
  rw [hf, hl]
  simp

/-- A componentwise specified finite sum of homotopies. -/
def sumHomotopy {E : Type*} [Category E] [Preadditive E]
    {X Y : CochainComplex E ℤ} {I : Type} [Fintype I]
    (f : I → (X ⟶ Y)) (H : ∀ i, Homotopy (f i) 0) :
    Homotopy (∑ i, f i) 0 where
  hom n m := ∑ i, (H i).hom n m
  zero n m h := by simp [fun i => (H i).zero n m h]
  comm n := by
    change Hom.fAddMonoidHom n (∑ i, f i) = _
    rw [map_sum]
    change (∑ i, (f i).f n) = _
    calc
      _ = ∑ i, (dNext n (H i).hom + prevD n (H i).hom + (0 : X ⟶ Y).f n) :=
        Finset.sum_congr rfl (fun i _ => (H i).comm n)
      _ = _ := by
        simp [dNext, prevD, Preadditive.comp_sum, Preadditive.sum_comp,
          Finset.sum_add_distrib]
end AssemblyData
end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_InducedDiagram
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

def framedMapHomotopy {C E : Type*} [Category C] [Preadditive C]
    [Category E] [Preadditive E] (G : C ⥤ E) [G.Additive]
    {X Y : CochainComplex C ℤ} {P Q : CochainComplex E ℤ}
    (f : X ⟶ Y) (H : Homotopy f 0)
    (a : P ⟶ (G.mapHomologicalComplex (.up ℤ)).obj X)
    (b : (G.mapHomologicalComplex (.up ℤ)).obj Y ⟶ Q) :
    Homotopy (a ≫ (G.mapHomologicalComplex (.up ℤ)).map f ≫ b) 0 where
  hom i j := a.f i ≫ G.map (H.hom i j) ≫ b.f j
  zero i j hij := by
    have h0 : H.hom i j = 0 := H.zero i j hij
    rw [h0, G.map_zero]
    erw [zero_comp]
    exact comp_zero
  comm i := by
    have h := H.comm i
    have ha := a.comm
    have hb := b.comm
    simp only [dNext, prevD, AddMonoidHom.mk'_apply] at h ⊢
    simp only [Functor.mapHomologicalComplex_obj_d] at ha hb
    have main : ∀ (a' : ∀ i, P.X i ⟶ G.obj (X.X i)) (b' : ∀ i, G.obj (Y.X i) ⟶ Q.X i),
        (∀ i j, a' i ≫ G.map (X.d i j) = P.d i j ≫ a' j) →
        (∀ i j, b' i ≫ Q.d i j = G.map (Y.d i j) ≫ b' j) →
        a' i ≫ G.map (f.f i) ≫ b' i =
          P.d i ((ComplexShape.up ℤ).next i) ≫ a' ((ComplexShape.up ℤ).next i) ≫
            G.map (H.hom ((ComplexShape.up ℤ).next i) i) ≫ b' i +
          (a' i ≫ G.map (H.hom i ((ComplexShape.up ℤ).prev i)) ≫
            b' ((ComplexShape.up ℤ).prev i)) ≫ Q.d ((ComplexShape.up ℤ).prev i) i := by
      intro a' b' ha hb
      have z : (0 : X ⟶ Y).f i = 0 := rfl
      rw [h, z, add_zero, G.map_add, G.map_comp, G.map_comp]
      simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
      rw [reassoc_of% (ha i _), ← hb]
    have z0 : (0 : P ⟶ Q).f i = 0 := rfl
    rw [z0, add_zero]
    exact main (fun i => a.f i) (fun i => b.f i) ha hb

variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]

/-- Only the finite quadratic diagram data used in the column calculation.
These equations hold for Section 3's arrows in e_j B e_i and relation basis.
No independence of relations is needed for the stronger assembly statement. -/
structure Quadratic where
  e₀ : B
  e₁ : B
  e₂ : B
  a : A → B
  b : J → B
  ha : ∀ i, a i * e₀ = a i
  hb : ∀ j, b j * e₁ = b j
  coeff : R → A → J → k
  relation : ∀ r, ∑ i, ∑ j, coeff r i j • (b j * a i) = 0

end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_NativeArrowBridge
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory HomologicalComplex
open scoped TensorProduct
noncomputable section
namespace ExternalTensor.Section4.ArrowVertex.NativeBridge
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

variable {k B}
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))

abbrev nativeVertex (e : B) :=
  (LittleFinitistic.BimoduleVertex.functor k B e).mapHomologicalComplex (ComplexShape.up ℤ)

end ExternalTensor.Section4.ArrowVertex.NativeBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ExactProducts
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.RectificationTotal
variable {A B C A' B' C' : Type*} [Zero C] [Zero C']
variable {f : A → B} {g : B → C} {f' : A' → B'} {g' : B' → C'}

/-- Exact pairs remain exact under the concrete binary product of maps. -/
theorem exact_prod (h : Function.Exact f g) (h' : Function.Exact f' g') :
    Function.Exact (Prod.map f f') (Prod.map g g') := by
  rintro ⟨x, x'⟩
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (h x).mp (congrArg Prod.fst hx)
    obtain ⟨y', hy'⟩ := (h' x').mp (congrArg Prod.snd hx)
    exact ⟨(y,y'), Prod.ext hy hy'⟩
  · rintro ⟨⟨y,y'⟩, hy⟩
    rw [← hy]
    exact Prod.ext (h.apply_apply_eq_zero y) (h'.apply_apply_eq_zero y')

/-- Short exactness is also preserved by the concrete binary product. -/
theorem shortExact_prod (h : Function.Exact f g) (h' : Function.Exact f' g')
    (hf : Function.Injective f) (hf' : Function.Injective f')
    (hg : Function.Surjective g) (hg' : Function.Surjective g') :
    Function.Injective (Prod.map f f') ∧
      Function.Exact (Prod.map f f') (Prod.map g g') ∧
      Function.Surjective (Prod.map g g') := by
  refine ⟨?_, exact_prod h h', ?_⟩
  · intro x y hxy
    exact Prod.ext (hf (congrArg Prod.fst hxy)) (hf' (congrArg Prod.snd hxy))
  · rintro ⟨z,z'⟩
    obtain ⟨x,hx⟩ := hg z
    obtain ⟨x',hx'⟩ := hg' z'
    exact ⟨(x,x'),Prod.ext hx hx'⟩

variable {X Y Z X' Y' Z' : Type*} [Zero Z] [Zero Z']
variable (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z') (eZzero : eZ 0 = 0)
variable {f : X → Y} {g : Y → Z} {f' : X' → Y'} {g' : Y' → Z'}
variable (commF : ∀ x, eY (f x) = f' (eX x))
variable (commG : ∀ y, eZ (g y) = g' (eY y))

include eX eY eZ eZzero commF commG

theorem exact_transport (h : Function.Exact f' g') : Function.Exact f g := by
  intro y
  constructor
  · intro hy
    obtain ⟨x',hx'⟩ := (h (eY y)).mp (by rw [← commG, hy, eZzero])
    refine ⟨eX.symm x', eY.injective ?_⟩
    rw [commF, eX.apply_symm_apply, hx']
  · rintro ⟨x,rfl⟩
    apply eZ.injective
    rw [commG, commF, h.apply_apply_eq_zero, eZzero]

theorem shortExact_transport (hf : Function.Injective f') (h : Function.Exact f' g')
    (hg : Function.Surjective g') :
    Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g := by
  refine ⟨?_, exact_transport eX eY eZ eZzero commF commG h, ?_⟩
  · intro x y hxy
    apply eX.injective
    apply hf
    rw [← commF, ← commF, hxy]
  · intro z
    obtain ⟨y',hy'⟩ := hg (eZ z)
    refine ⟨eY.symm y',eZ.injective ?_⟩
    rw [commG, eY.apply_symm_apply, hy']
end LittleFinitistic.RectificationTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_TotalFunctorial
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex
noncomputable section
namespace LittleFinitistic.RectificationTotal
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
theorem biprodMap_comp {U V W X Y Z : C} (f : U ⟶ W) (g : V ⟶ X)
    (f' : W ⟶ Y) (g' : X ⟶ Z) :
    biprod.map f g ≫ biprod.map f' g' = biprod.map (f ≫ f') (g ≫ g') := by
  apply biprod.hom_ext <;> simp

variable {A B A' B' A'' B'' : CochainComplex C ℤ}

/-- A strictly commuting square induces the ordinary diagonal map of cones. -/
def coneMap (q : A ⟶ B) (q' : A' ⟶ B') (u : A ⟶ A') (v : B ⟶ B')
    (w : u ≫ q' = q ≫ v) : mappingCone q ⟶ mappingCone q' :=
  homotopyCofiber.mapArrowHom q q' (fun j => ⟨j-1, by simp⟩)
    (Arrow.homMk u v w)

@[reassoc (attr := simp)]
theorem coneMap_inl (q : A ⟶ B) (q' : A' ⟶ B') (u : A ⟶ A') (v : B ⟶ B')
    (w : u ≫ q' = q ≫ v) (i j : ℤ) (hij : i + (-1) = j) :
    (mappingCone.inl q).v i j hij ≫ (coneMap q q' u v w).f j =
      u.f i ≫ (mappingCone.inl q').v i j hij := by
  dsimp [coneMap, homotopyCofiber.mapArrowHom, mappingCone.inl]
  erw [homotopyCofiber.inlX_desc_f]
  simp
  congr 1
  exact homotopyCofiber.inrCompHomotopy_hom q' _ i j (by change j+1=i; omega)

@[reassoc (attr := simp)]
theorem coneMap_inr (q : A ⟶ B) (q' : A' ⟶ B') (u : A ⟶ A') (v : B ⟶ B')
    (w : u ≫ q' = q ≫ v) (i : ℤ) :
    (mappingCone.inr q).f i ≫ (coneMap q q' u v w).f i =
      v.f i ≫ (mappingCone.inr q').f i := by
  dsimp [coneMap, homotopyCofiber.mapArrowHom, mappingCone.inr]
  exact homotopyCofiber.inrX_desc_f _ _ _ _

@[reassoc (attr := simp)]
theorem cone_inl_termIso (q : A ⟶ B) (i j : ℤ) (hij : i+1=j) :
    (mappingCone.inl q).v j i (by omega) ≫ (homotopyCofiber.XIsoBiprod q i j hij).hom =
      biprod.inl :=
  homotopyCofiber.inlX_XIsoBiprod_hom _ _ _ _

@[reassoc (attr := simp)]
theorem cone_inr_termIso (q : A ⟶ B) (i j : ℤ) (hij : i+1=j) :
    (mappingCone.inr q).f i ≫ (homotopyCofiber.XIsoBiprod q i j hij).hom =
      biprod.inr :=
  homotopyCofiber.inrX_XIsoBiprod_hom _ _ _ _

/-- On terms the cone map is exactly the sum of the two supplied maps. -/
theorem coneMap_term (q : A ⟶ B) (q' : A' ⟶ B') (u : A ⟶ A') (v : B ⟶ B')
    (w : u ≫ q' = q ≫ v) (i j : ℤ) (hij : i+1=j) :
    (coneMap q q' u v w).f i ≫ (homotopyCofiber.XIsoBiprod q' i j hij).hom =
      (homotopyCofiber.XIsoBiprod q i j hij).hom ≫ biprod.map (u.f j) (v.f i) := by
  apply mappingCone.ext_from q j i hij
  · erw [coneMap_inl_assoc, cone_inl_termIso, ← Category.assoc, cone_inl_termIso,
      biprod.inl_map]
  · erw [coneMap_inr_assoc, cone_inr_termIso, ← Category.assoc, cone_inr_termIso,
      biprod.inr_map]

@[simp]
theorem coneMap_id (q : A ⟶ B) : coneMap q q (𝟙 A) (𝟙 B) (by simp) = 𝟙 _ := by
  change homotopyCofiber.mapArrowHom q q _ (𝟙 _) = 𝟙 _
  exact homotopyCofiber.mapArrowHom_id _ _

theorem coneMap_comp (q : A ⟶ B) (q' : A' ⟶ B') (q'' : A'' ⟶ B'')
    (u : A ⟶ A') (v : B ⟶ B') (w : u ≫ q' = q ≫ v)
    (u' : A' ⟶ A'') (v' : B' ⟶ B'') (w' : u' ≫ q'' = q' ≫ v') :
    coneMap q q'' (u ≫ u') (v ≫ v') (by rw [Category.assoc, w', ← Category.assoc, w, Category.assoc]) =
      coneMap q q' u v w ≫ coneMap q' q'' u' v' w' := by
  exact homotopyCofiber.mapArrowHom_comp _ _ _ _ (Arrow.homMk u v w) (Arrow.homMk u' v' w')

variable {L₀ L₁ L₂ M₀ M₁ M₂ N₀ N₁ N₂ : CochainComplex C ℤ}
variable {p : L₁ ⟶ L₀} {q : L₂ ⟶ L₁} {h : Homotopy (q ≫ p) 0}
variable {p' : M₁ ⟶ M₀} {q' : M₂ ⟶ M₁} {h' : Homotopy (q' ≫ p') 0}

/-- Morphisms preserve both degree-zero maps and the specified relation
homotopy, which is part of the three-column input data. -/
structure MapData (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁) (h : Homotopy (q ≫ p) 0)
    (p' : M₁ ⟶ M₀) (q' : M₂ ⟶ M₁) (h' : Homotopy (q' ≫ p') 0) where
  f₀ : L₀ ⟶ M₀
  f₁ : L₁ ⟶ M₁
  f₂ : L₂ ⟶ M₂
  commP : f₁ ≫ p' = p ≫ f₀
  commQ : f₂ ≫ q' = q ≫ f₁
  commH : ∀ i j, f₂.f i ≫ h'.hom i j = h.hom i j ≫ f₀.f j

namespace MapData
variable (a : MapData p q h p' q' h')

def inner : mappingCone q ⟶ mappingCone q' := coneMap q q' a.f₂ a.f₁ a.commQ

theorem rectifyingMap_naturality : a.inner ≫ rectifyingMap p' q' h' =
    rectifyingMap p q h ≫ a.f₀ := by
  ext n
  apply mappingCone.ext_from q (n+1) n rfl
  · simp only [comp_f, inner, coneMap_inl_assoc, rectifyingMap, mappingCone.inl_v_desc_f_assoc,
      mappingCone.inl_v_desc_f]
    exact a.commH (n+1) n
  · simp only [comp_f, inner, coneMap_inr_assoc, rectifyingMap,
      mappingCone.inr_f_desc_f_assoc, mappingCone.inr_f_desc_f]
    exact congrArg (fun f => f.f n) a.commP

/-- The induced chain map of the native primary's actual iterated-cone total. -/
def totalMap : total p q h ⟶ total p' q' h' :=
  coneMap (rectifyingMap p q h) (rectifyingMap p' q' h') a.inner a.f₀
    a.rectifyingMap_naturality

/-- The zero-column inclusion is preserved by the actual induced total map. -/
@[reassoc]
theorem inclusion_totalMap : inclusion p q h ≫ a.totalMap =
    a.f₀ ≫ inclusion p' q' h' := by
  ext n
  exact coneMap_inr _ _ _ _ _ n

/-- The induced total map is the actual diagonal triple under the native
term decomposition, including both cohomological shifts. -/
theorem totalMap_term (n : ℤ) :
    a.totalMap.f n ≫ (termIso p' q' h' n).hom =
      (termIso p q h n).hom ≫
        biprod.map (biprod.map (a.f₂.f (n+2)) (a.f₁.f (n+1))) (a.f₀.f n) := by
  unfold totalMap termIso
  erw [Iso.trans_hom, Iso.trans_hom, biprod.mapIso_hom, biprod.mapIso_hom, Iso.refl_hom, Iso.refl_hom]
  erw [← Category.assoc, coneMap_term]
  erw [Category.assoc, Category.assoc, biprodMap_comp, biprodMap_comp,
    Category.comp_id, Category.id_comp]
  congr 2
  exact coneMap_term q q' a.f₂ a.f₁ a.commQ (n+1) (n+2) (by omega)

end MapData
end LittleFinitistic.RectificationTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_TotalExact
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
noncomputable section
namespace LittleFinitistic.RectificationTotal
universe u
variable {S : Type u} [Ring S]

/-- The canonical binary sum/product identification respects the supplied maps. -/
theorem prodIso_naturality {X Y X' Y' : ModuleCat.{u} S} (f : X ⟶ X') (g : Y ⟶ Y') :
    biprod.map f g ≫ (ModuleCat.biprodIsoProd X' Y').hom =
      (ModuleCat.biprodIsoProd X Y).hom ≫ ModuleCat.ofHom (f.hom.prodMap g.hom) := by
  apply (cancel_epi (ModuleCat.biprodIsoProd X Y).inv).1
  apply (cancel_mono (ModuleCat.biprodIsoProd X' Y').inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, ModuleCat.biprodIsoProd_inv_comp_fst]
    rw [← Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst]
    rfl
  · simp only [Category.assoc, biprod.map_snd, ModuleCat.biprodIsoProd_inv_comp_snd]
    rw [← Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd]
    rfl

variable {L₀ L₁ L₂ M₀ M₁ M₂ N₀ N₁ N₂ : CochainComplex (ModuleCat.{u} S) ℤ}
variable {p : L₁ ⟶ L₀} {q : L₂ ⟶ L₁} {h : Homotopy (q ≫ p) 0}
variable {p' : M₁ ⟶ M₀} {q' : M₂ ⟶ M₁} {h' : Homotopy (q' ≫ p') 0}
variable {p'' : N₁ ⟶ N₀} {q'' : N₂ ⟶ N₁} {h'' : Homotopy (q'' ≫ p'') 0}

/-- The native total's term as the actual product of the three input modules. -/
def totalTermIso (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁) (h : Homotopy (q ≫ p) 0) (n : ℤ) :
    (total p q h).X n ≅ ModuleCat.of S ((L₂.X (n+2) × L₁.X (n+1)) × L₀.X n) :=
  termIso p q h n ≪≫
    biprod.mapIso (ModuleCat.biprodIsoProd _ _) (Iso.refl _) ≪≫
    ModuleCat.biprodIsoProd _ _

namespace MapData
variable (a : MapData p q h p' q' h')

/-- The explicit total map acts componentwise in the concrete term product. -/
theorem totalMap_product (n : ℤ) :
    a.totalMap.f n ≫ (totalTermIso p' q' h' n).hom =
      (totalTermIso p q h n).hom ≫ ModuleCat.ofHom
        (((a.f₂.f (n+2)).hom.prodMap (a.f₁.f (n+1)).hom).prodMap (a.f₀.f n).hom) := by
  have hb :
      biprod.map (biprod.map (a.f₂.f (n+2)) (a.f₁.f (n+1))) (a.f₀.f n) ≫
        biprod.map (ModuleCat.biprodIsoProd (M₂.X (n+2)) (M₁.X (n+1))).hom (𝟙 (M₀.X n)) =
      biprod.map (ModuleCat.biprodIsoProd (L₂.X (n+2)) (L₁.X (n+1))).hom (𝟙 (L₀.X n)) ≫
        biprod.map (ModuleCat.ofHom ((a.f₂.f (n+2)).hom.prodMap (a.f₁.f (n+1)).hom)) (a.f₀.f n) := by
    rw [biprodMap_comp, biprodMap_comp, Category.comp_id, Category.id_comp,
      prodIso_naturality]
  dsimp only [totalTermIso, Iso.trans_hom, biprod.mapIso_hom, Iso.refl_hom]
  rw [← Category.assoc, a.totalMap_term]
  simp only [Category.assoc]
  erw [biprod.mapIso_hom, biprod.mapIso_hom, Iso.refl_hom, Iso.refl_hom]
  rw [reassoc_of% hb]
  rw [prodIso_naturality]

/-- A short exact triple of column maps induces short exactness of the actual
supplied total maps, retaining the inclusion and quotient maps themselves. -/
theorem totalMap_shortExact (b : MapData p' q' h' p'' q'' h'')
    (ex₀ : ∀ n, Function.Exact (a.f₀.f n) (b.f₀.f n))
    (ex₁ : ∀ n, Function.Exact (a.f₁.f n) (b.f₁.f n))
    (ex₂ : ∀ n, Function.Exact (a.f₂.f n) (b.f₂.f n))
    (inj₀ : ∀ n, Function.Injective (a.f₀.f n))
    (inj₁ : ∀ n, Function.Injective (a.f₁.f n))
    (inj₂ : ∀ n, Function.Injective (a.f₂.f n))
    (surj₀ : ∀ n, Function.Surjective (b.f₀.f n))
    (surj₁ : ∀ n, Function.Surjective (b.f₁.f n))
    (surj₂ : ∀ n, Function.Surjective (b.f₂.f n)) (n : ℤ) :
    Function.Injective (a.totalMap.f n) ∧
      Function.Exact (a.totalMap.f n) (b.totalMap.f n) ∧
      Function.Surjective (b.totalMap.f n) := by
  let inner := shortExact_prod (ex₂ (n+2)) (ex₁ (n+1))
    (inj₂ (n+2)) (inj₁ (n+1)) (surj₂ (n+2)) (surj₁ (n+1))
  let all := shortExact_prod inner.2.1 (ex₀ n) inner.1 (inj₀ n) inner.2.2 (surj₀ n)
  apply shortExact_transport (totalTermIso p q h n).toLinearEquiv.toEquiv
    (totalTermIso p' q' h' n).toLinearEquiv.toEquiv
    (totalTermIso p'' q'' h'' n).toLinearEquiv.toEquiv (by simp)
    (fun x => congrArg (fun f => f x) (a.totalMap_product n))
    (fun x => congrArg (fun f => f x) (b.totalMap_product n)) all.1 all.2.1 all.2.2
end MapData
end LittleFinitistic.RectificationTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SplitComponentExact
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration
universe u
variable {S : Type u} [Ring S]
variable {X Y Z : CochainComplex (ModuleCat.{u} S) ℤ}

/-- A specified degreewise splitting proves exactness for its original maps. -/
theorem component_shortExact (i : X ⟶ Y) (q : Y ⟶ Z)
    (r : Y ⟶ X) (s : Z ⟶ Y)
    (hi : i ≫ r = 𝟙 _) (hq : s ≫ q = 𝟙 _)
    (hz : i ≫ q = 0) (hs : r ≫ i + q ≫ s = 𝟙 _) (n : ℤ) :
    Function.Injective (i.f n) ∧ Function.Exact (i.f n) (q.f n) ∧
      Function.Surjective (q.f n) := by
  have hi' (x : X.X n) : r.f n (i.f n x) = x :=
    congrArg (fun a : X ⟶ X => a.f n x) hi
  have hq' (z : Z.X n) : q.f n (s.f n z) = z :=
    congrArg (fun a : Z ⟶ Z => a.f n z) hq
  have hz' (x : X.X n) : q.f n (i.f n x) = 0 :=
    congrArg (fun a : X ⟶ Z => a.f n x) hz
  have hs' (y : Y.X n) : i.f n (r.f n y) + s.f n (q.f n y) = y :=
    congrArg (fun a : Y ⟶ Y => a.f n y) hs
  refine ⟨?_, ?_, ?_⟩
  · intro x y he
    simpa only [hi'] using congrArg (r.f n) he
  · intro y
    constructor
    · intro hy
      exact ⟨r.f n y, by simpa [hy] using hs' y⟩
    · rintro ⟨x, rfl⟩
      exact hz' x
  · intro z
    exact ⟨s.f n z, hq' z⟩

variable (X Y : CochainComplex (ModuleCat.{u} S) ℤ)
theorem inr_fst_shortExact (n : ℤ) :
    Function.Injective ((biprod.inr : Y ⟶ X ⊞ Y).f n) ∧
    Function.Exact ((biprod.inr : Y ⟶ X ⊞ Y).f n)
      ((biprod.fst : X ⊞ Y ⟶ X).f n) ∧
    Function.Surjective ((biprod.fst : X ⊞ Y ⟶ X).f n) := by
  apply component_shortExact _ _ biprod.snd biprod.inl (by simp) (by simp) (by simp)
  simp [add_comm]

theorem zero_id_shortExact (Z : CochainComplex (ModuleCat.{u} S) ℤ)
    (hZ : ∀ n, Subsingleton (Z.X n)) (n : ℤ) :
    Function.Injective ((0 : Z ⟶ X).f n) ∧
    Function.Exact ((0 : Z ⟶ X).f n) ((𝟙 X : X ⟶ X).f n) ∧
      Function.Surjective ((𝟙 X : X ⟶ X).f n) := by
  let := hZ n
  refine ⟨fun _ _ _ => Subsingleton.elim _ _, ?_, fun x => ⟨x, rfl⟩⟩
  intro x
  constructor
  · intro hx
    exact ⟨0, hx.symm⟩
  · rintro ⟨z, rfl⟩
    rfl
end ExternalTensor.Section4.SourceFiltration

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFiniteColumnComplex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.FiniteColumnComplex
universe u
variable {R : Type u} [Ring R] {l : ℕ}
variable (K : Fin l → CochainComplex (ModuleCat.{u} R) ℤ)

abbrev term (n : ℤ) := ∀ i, (K i).X n

end LittleFinitistic.FiniteColumnComplex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ColumnFinite
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
attribute [local instance] ExternalTensor.bimodule ExternalTensor.rightModule

theorem finite_of_iso {X Y : ModuleCat.{u} k} (e : X ≅ Y)
    (hY : FiniteDimensional k Y) : FiniteDimensional k X := by
  let := hY
  exact FiniteDimensional.of_injective e.hom.hom e.toLinearEquiv.injective

end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SourceFiltrationReal
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (t : AssemblyData (C := BiComplex k B) (A := A) (J := J) (R := R))

@[reassoc (attr := simp)]
theorem inr_prod {S : Type u} [Ring S] (X Y : ModuleCat.{u} S) :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫ (ModuleCat.biprodIsoProd X Y).hom =
      ModuleCat.ofHom (LinearMap.inr S X Y) := by
  apply (cancel_mono (ModuleCat.biprodIsoProd X Y).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply biprod.hom_ext
  · simp only [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst, biprod.inr_fst]
    rfl
  · simp only [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd, biprod.inr_snd]
    rfl

end ExternalTensor.Section4.SourceFiltration

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SourceFiltrationComplex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.ModuleComplexExact
universe u
variable {S : Type u} [Ring S]
variable {X Y Z : CochainComplex (ModuleCat.{u} S) ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem comp_zero (h : ∀ n, Function.Exact (f.f n) (g.f n)) : f ≫ g = 0 := by
  ext n x
  exact (h n).apply_apply_eq_zero x

def sequence (h : ∀ n, Function.Exact (f.f n) (g.f n)) :
    ShortComplex (CochainComplex (ModuleCat.{u} S) ℤ) := .mk f g (comp_zero f g h)

theorem shortExact (h : ∀ n, Function.Injective (f.f n) ∧
    Function.Exact (f.f n) (g.f n) ∧ Function.Surjective (g.f n)) :
    (sequence f g (fun n => (h n).2.1)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact ModuleCat.shortComplex_shortExact _ (h n).2.1 (h n).1 (h n).2.2
end LittleFinitistic.ModuleComplexExact

end

end OAI
end


