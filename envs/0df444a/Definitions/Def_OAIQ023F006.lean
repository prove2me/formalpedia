-- Prove2me | Definitions.Def_OAIQ023F006
-- name    : OAIQ023F006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:44:03.472637+00:00
-- url     : https://prove2.me/theorems/bca5376c-ab76-4c27-9d8c-f1cc85ceceeb
-- title:
--   Definitions bundle OAIQ023F006 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 122 declarations of OpenAI's Lean: 64 definitions, 8 instances and 50 theorems. The definitions and types are `OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions`, `OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_1`, `OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_2`, `OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_3`, `OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_4`, `OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_5`, `OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_6`, `OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_7`, `OAI.DerivedBar.ParityBridge.leadingBarSuffixScalarModule`, `OAI.DerivedBar.ParityBridge.recursiveSuffixDifferentialScalarModule`, `OAI.DerivedBar.ParityBridge.recursiveSuffixSumsScalarModule`, `OAI.DerivedBar.ParityBridge.supportedInnerCoordinatesScalarModule`, `OAI.DerivedBar.RecursiveTotal.instModuleCarrier_solutions_3`, `OAI.DerivedBar.SquareZero.slotParity`, `OAI.ExternalTensor.Section4.ArrowVertex.NativeBridge.nativeCompatibility01`, `OAI.ExternalTensor.Section4.ArrowVertex.NativeBridge.originalIota`, `OAI.ExternalTensor.Section4.ArrowVertex.actualP`, `OAI.ExternalTensor.Section4.ArrowVertex.arrow`, `OAI.ExternalTensor.Section4.ArrowVertex.arrowComplex`, `OAI.ExternalTensor.Section4.ArrowVertex.compatibility`, `OAI.ExternalTensor.Section4.ArrowVertex.compatibility01`, `OAI.ExternalTensor.Section4.ArrowVertex.compatibility12`, `OAI.ExternalTensor.Section4.ArrowVertex.diagonal`, `OAI.ExternalTensor.Section4.ArrowVertex.diagonalComplex`, `OAI.ExternalTensor.Section4.ArrowVertex.iota`, `OAI.ExternalTensor.Section4.ArrowVertex.iota0`, `OAI.ExternalTensor.Section4.ArrowVertex.iota1`, `OAI.ExternalTensor.Section4.ArrowVertex.iota2`, `OAI.ExternalTensor.Section4.ArrowVertex.left`, `OAI.ExternalTensor.Section4.ArrowVertex.space`, `OAI.ExternalTensor.Section4.ArrowVertex.vertex`, `OAI.ExternalTensor.Section4.ArrowVertex.vertexComplex`, `OAI.ExternalTensor.Section4.L0Prime`, `OAI.ExternalTensor.Section4.L1Prime`, `OAI.ExternalTensor.Section4.L2Prime`, `OAI.ExternalTensor.Section4.SourceFiltration.Exactness.F1`, `OAI.ExternalTensor.Section4.SourceFiltration.Exactness.G0`, `OAI.ExternalTensor.Section4.SourceFiltration.Exactness.data`, `OAI.ExternalTensor.Section4.SourceFiltration.F1₀`, `OAI.ExternalTensor.Section4.SourceFiltration.F1₁` and 24 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bar_Bar`, `Finitistic_Bar_BlockCoordinateGenerators`, `Finitistic_Bar_ExplicitSignedDifferential`, `Finitistic_Bar_FiniteBarResolution`, `Finitistic_Bar_LeadingBarSuffix`, `Finitistic_Bar_LeadingTotalComparison`, `Finitistic_Bar_LeadingTotalDifferential`, `Finitistic_Bar_LeadingTotalEmbedding`, `Finitistic_Bar_RecursiveSuffixCoefficient`, `Finitistic_Bar_RecursiveSuffixDifferential`, `Finitistic_Bar_RecursiveSuffixEmbedding`, `Finitistic_Bar_RecursiveSuffixFaces`, `Finitistic_Bar_RecursiveSuffixInduction`, `Finitistic_Bar_RecursiveSuffixSums`, `Finitistic_Bar_RecursiveSuffixTotal`, `Finitistic_Bar_SupportedInnerCoordinates`, `Finitistic_Encoding_ArrowBasisIso`, `Finitistic_Localization_NativeArrowBridge`, `Finitistic_Rectification_ArrowCompatibility`, `Finitistic_Rectification_ArrowVertex`, `Finitistic_Rectification_ColumnComplex`, `Finitistic_Rectification_ColumnProperties`, `Finitistic_Rectification_CornerProjection`, `Finitistic_Rectification_ExternalTensor`, `Finitistic_Rectification_FiltrationExactness`, `Finitistic_Rectification_InducedColumns`, `Finitistic_Rectification_InducedDiagram`, `Finitistic_Rectification_InducedRectification`, `Finitistic_Rectification_SourceFiltration`.
--
--   **Imports.** It imports the bundles `OAIQ023F000` and `OAIQ023F001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F010`, `OAIQ023F011`, `OAIQ023F012` and `OAIQ023F013`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F000
import Definitions.Def_OAIQ023F001

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_Bar
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct
open TensorProduct
noncomputable section
namespace DerivedBar
universe u
variable (k A N : Type u) [Field k] [Ring A] [Algebra k A]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]


open CategoryTheory CategoryTheory.Limits

/-- Every unaugmented bar term is free as a left A-module, even for noncommutative A. -/
instance term_free (n : ℕ) : Module.Free A (term k A N (n+1)) :=
  Module.Free.of_basis (Algebra.TensorProduct.basis A (Module.Free.chooseBasis k (term k A N n)))

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_BlockCoordinateGenerators
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
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

variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance instModuleCarrier_solutions_3 (N : ModuleCat.{u} D) : Module k N := BimoduleTensor.scalarModule k D N
end DerivedBar.RecursiveTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_ExplicitSignedDifferential
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct
noncomputable section
namespace DerivedBar.SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
  [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
local notation "A" => TrivSqZeroExt D X

/-- The parity operator is +1 on a D slot and -1 on an X slot. -/
def slotParity : Module.End k A := baseProjection k D X - idealProjection k D X

@[simp] theorem slotParity_base (d : D) : slotParity k D X (inl d) = inl d := by
  simp [slotParity]

@[simp] theorem slotParity_ideal (x : X) : slotParity k D X (inr x) = -inr x := by
  simp [slotParity]

end DerivedBar.SquareZero

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_FiniteBarResolution
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace DerivedBar
universe u
variable (k A N : Type u) [Field k] [Ring A] [Algebra k A]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  [FiniteDimensional k A] [FiniteDimensional k N]

/-- Every absolute bar word remains finite dimensional over the base field. -/
instance term_finiteDimensional : (n : ℕ) → FiniteDimensional k (term k A N n)
  | 0 => inferInstanceAs (FiniteDimensional k N)
  | n+1 => by
    let := term_finiteDimensional n
    exact inferInstanceAs (FiniteDimensional k (A ⊗[k] term k A N n))

instance term_finite (n : ℕ) : Module.Finite A (term k A N n) :=
  Module.Finite.of_restrictScalars_finite k A (term k A N n)

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixEmbedding
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
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
local instance instModuleCarrier_solutions (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance instIsScalarTowerCarrier_solutions (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixFaces
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
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
local instance instModuleCarrier_solutions_1 (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance instIsScalarTowerCarrier_solutions_1 (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local instance instDecidableEqIndex_1_r1b3fd1_1 (r n : ℕ) : DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingBarSuffix
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
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
local instance leadingBarSuffixScalarModule (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance leadingBarSuffixScalarTower (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
attribute [local instance] OAI.DerivedBar.ParityBridge.leadingBarSuffixInflatedModule
local instance leadingBarSuffixInflatedTower : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixSums
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance recursiveSuffixSumsScalarModule (V : ModuleCat.{u} D) : Module k V :=
  BimoduleTensor.scalarModule k D V
local instance recursiveSuffixSumsScalarTower (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat.{u} D)

local instance recursiveSuffixSumsIndexDecidableEq_r1b3fd1_1 (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
/-- Finite coproduct extensionality also holds for k-linear maps out of a D bar. -/
theorem sum_hom_ext_scalar {I : Type} [Finite I] [DecidableEq I]
    (V : I → ModuleCat.{u} D) (G : ModuleCat.{u} D ⥤ ModuleCat.{u} D) [G.Additive]
    (W : ModuleCat.{u} k)
    {f g : G.obj (ModuleCat.of D (⨁ t, V t)) →ₗ[k] W}
    (h : ∀ t, f.comp ((G.map (ModuleCat.ofHom (DirectSum.lof D I (fun t => V t) t))).hom.restrictScalars k) =
      g.comp ((G.map (ModuleCat.ofHom (DirectSum.lof D I (fun t => V t) t))).hom.restrictScalars k)) :
    f=g := by
  let : Fintype I := Fintype.ofFinite I
  let R := ModuleCat.restrictScalars (algebraMap k D)
  have he : (ModuleCat.ofHom f : R.obj (G.obj (ModuleCat.of D (⨁ t, V t))) ⟶ W) =
      ModuleCat.ofHom g := by
    apply (isColimitOfPreserves (G ⋙ R) (ModuleCat.coproductCoconeIsColimit V)).hom_ext
    rintro ⟨t⟩
    exact ModuleCat.hom_ext (h t)
  exact congrArg ModuleCat.Hom.hom he

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixDifferential
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
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
local instance recursiveSuffixDifferentialScalarModule (V : ModuleCat.{u} D) : Module k V :=
  BimoduleTensor.scalarModule k D V
local instance recursiveSuffixDifferentialScalarTower (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local instance recursiveSuffixDifferentialIndexDecidableEq_r1b3fd1_1 (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.recursiveSuffixDifferentialInflatedModule
local instance recursiveSuffixDifferentialInflatedScalarTower : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixInduction
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
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
local instance instModuleCarrier_solutions_2 (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance instIsScalarTowerCarrier_solutions_2 (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local instance recursiveSuffixInductionIndexDecidableEq_r1b3fd1_1 (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_1
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_1 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixTotal
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
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
local instance instModuleCarrier_solutions_3 (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance instIsScalarTowerCarrier_solutions_3 (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local instance recursiveSuffixTotalIndexDecidableEq_r1b3fd1_1 (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_2
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_2 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixCoefficient
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
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
local instance instModuleCarrier_solutions_4 (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance instIsScalarTowerCarrier_solutions_4 (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingTotalEmbedding
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
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
local instance instModuleCarrier_solutions_5 (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingTotalDifferential
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
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
local instance instModuleCarrier_solutions_6 (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance instIsScalarTowerCarrier_solutions_6 (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingTotalComparison
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
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
local instance instModuleCarrier_solutions_7 (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance instIsScalarTowerCarrier_solutions_7 (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_6
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_6 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_SupportedInnerCoordinates
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
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
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance supportedInnerCoordinatesScalarModule (V : ModuleCat.{u} D) : Module k V :=
  BimoduleTensor.scalarModule k D V
local instance supportedInnerCoordinatesScalarTower (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ExternalTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
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

attribute [local instance] bimodule rightModule

variable {k B M N}
variable {M' N' : Type*}
  [AddCommGroup M'] [Module k M'] [Module B M'] [IsScalarTower k B M']
  [AddCommGroup N'] [Module k N'] [Module Bᵐᵒᵖ N'] [IsScalarTower k Bᵐᵒᵖ N']

/-- Tensor of a left-module map and a right-module map is enveloping-linear. -/
def map (f : M →ₗ[B] M') (g : N →ₗ[Bᵐᵒᵖ] N') :
    (M ⊗[k] N) →ₗ[B ⊗[k] Bᵐᵒᵖ] (M' ⊗[k] N') where
  __ := (TensorProduct.map (f.restrictScalars k) (g.restrictScalars k)).toAddMonoidHom
  map_smul' a x := by
    induction a using OAI.tensorInductionOn with
    | tmul b c =>
      induction x using OAI.tensorInductionOn with
      | tmul m n => simp [smul_tmul]
      | add x y hx hy => simp_all [smul_add]
    | add a b ha hb => simp_all [add_smul]

@[simp] theorem map_tmul (f : M →ₗ[B] M') (g : N →ₗ[Bᵐᵒᵖ] N') (m : M) (n : N) :
    map (k := k) f g (m ⊗ₜ[k] n) = f m ⊗ₜ[k] g n := rfl

@[simp] theorem map_id :
    map (k := k) (LinearMap.id : M →ₗ[B] M) (LinearMap.id : N →ₗ[Bᵐᵒᵖ] N) =
      LinearMap.id := by
  ext x
  induction x using OAI.tensorInductionOn with
  | tmul m n => rfl
  | add x y hx hy => simp_all

variable {M'' N'' : Type*}
  [AddCommGroup M''] [Module k M''] [Module B M''] [IsScalarTower k B M'']
  [AddCommGroup N''] [Module k N''] [Module Bᵐᵒᵖ N''] [IsScalarTower k Bᵐᵒᵖ N'']

theorem map_comp (f : M →ₗ[B] M') (f' : M' →ₗ[B] M'')
    (g : N →ₗ[Bᵐᵒᵖ] N') (g' : N' →ₗ[Bᵐᵒᵖ] N'') :
    map (k := k) (f'.comp f) (g'.comp g) = (map (k := k) f' g').comp (map (k := k) f g) := by
  ext x
  induction x using OAI.tensorInductionOn with
  | tmul m n => rfl
  | add x y hx hy => simp_all


theorem map_add_right (f : M →ₗ[B] M') (g g' : N →ₗ[Bᵐᵒᵖ] N') :
    map (k := k) f (g + g') = map (k := k) f g + map (k := k) f g' := by
  ext x
  induction x using OAI.tensorInductionOn with
  | tmul m n => simp [TensorProduct.tmul_add]
  | add x y hx hy => simp_all [add_add_add_comm]


theorem map_smul_right (r : k) (f : M →ₗ[B] M') (g : N →ₗ[Bᵐᵒᵖ] N') :
    map (k := k) f (r • g) = r • map (k := k) f g := by
  ext x
  induction x using OAI.tensorInductionOn with
  | tmul m n => simp [TensorProduct.tmul_smul]
  | add x y hx hy => simp_all [smul_add]

end ExternalTensor

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

/-- The adjacent arrow space is precisely the direct sum of its scalar arrow columns. -/
def iso : (⨁ family k d) ≅ ModuleCat.of k (QuadraticEncoding.Arrows k d) :=
  ModuleCat.biproductIsoPi (family k d)

end LittleFinitistic.ArrowBasisIso

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_InducedColumns
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
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

attribute [local instance] leftIdeal_finiteDimensional

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module Bᵐᵒᵖ N] [IsScalarTower k Bᵐᵒᵖ N]

variable {B}

variable {N}
/-- The path-multiplication component c tensor n ↦ ca tensor n of the rectification maps. -/
def columnPath (ei ej a : B) (ha : a * ei = a) :
    Column k B N ej →ₗ[B ⊗[k] Bᵐᵒᵖ] Column k B N ei :=
  map (k := k) (pathMap ei ej a ha) LinearMap.id

@[simp] theorem columnPath_tmul (ei ej a : B) (ha : a * ei = a)
    (c : leftIdeal B ej) (n : N) :
    columnPath k ei ej a ha (c ⊗ₜ[k] n) = (pathMap ei ej a ha c) ⊗ₜ[k] n := rfl

variable {N' : Type*} [AddCommGroup N'] [Module k N']
  [Module Bᵐᵒᵖ N'] [IsScalarTower k Bᵐᵒᵖ N']

/-- The differential or relation-homotopy component c tensor n ↦ c tensor f(n). -/
def columnMap (e : B) (f : N →ₗ[Bᵐᵒᵖ] N') :
    Column k B N e →ₗ[B ⊗[k] Bᵐᵒᵖ] Column k B N' e :=
  map (k := k) LinearMap.id f

@[simp] theorem columnMap_tmul (e : B) (f : N →ₗ[Bᵐᵒᵖ] N')
    (c : leftIdeal B e) (n : N) :
    columnMap k e f (c ⊗ₜ[k] n) = c ⊗ₜ[k] f n := rfl
end ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ColumnComplex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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

/-- Induction by the actual left ideal Be, on right modules and maps. -/
def columnFunctor (e : B) : ModuleCat.{u} Bᵐᵒᵖ ⥤ ModuleCat.{u} (Enveloping k B) where
  obj N := ModuleCat.of _ (Column k B N e)
  map f := ModuleCat.ofHom (columnMap k e f.hom)
  map_id N := by apply ModuleCat.hom_ext; exact map_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    simpa [columnMap] using (map_comp (k := k) (LinearMap.id) (LinearMap.id) f.hom g.hom)
instance columnFunctor_additive (e : B) : (columnFunctor k B e).Additive where
  map_add := by intros; apply ModuleCat.hom_ext; exact map_add_right _ _ _

instance columnFunctor_linear (e : B) : (columnFunctor k B e).Linear k where
  map_smul f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ExternalTensor.map (k := k) LinearMap.id (r • f.hom) x =
      (algebraMap k (Enveloping k B) r) • (columnMap k e f.hom x)
    rw [map_smul_right]
    exact (IsScalarTower.algebraMap_smul (Enveloping k B) r _).symm

abbrev columnComplex (e : B) : RightComplex B ⥤ BiComplex k B :=
  (columnFunctor k B e).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Right multiplication on the left tensor factor, natural in the right module. -/
def pathNat (ei ej a : B) (ha : a * ei = a) :
    columnFunctor k B ej ⟶ columnFunctor k B ei where
  app N := ModuleCat.ofHom (columnPath k ei ej a ha)
  naturality {N N'} f := by
    apply ModuleCat.hom_ext
    ext x
    induction x using OAI.tensorInductionOn with
    | tmul c n => rfl
    | add x y hx hy =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

abbrev path (ei ej a : B) (ha : a * ei = a) (D : RightComplex B) :
    (columnComplex k B ej).obj D ⟶ (columnComplex k B ei).obj D :=
  ((pathNat k B ei ej a ha).mapHomologicalComplex (ComplexShape.up ℤ)).app D

@[reassoc] theorem path_naturality (ei ej a : B) (ha : a * ei = a)
    {D E : RightComplex B} (f : D ⟶ E) :
    (columnComplex k B ej).map f ≫ path k B ei ej a ha E =
      path k B ei ej a ha D ≫ (columnComplex k B ei).map f :=
  ((pathNat k B ei ej a ha).mapHomologicalComplex (ComplexShape.up ℤ)).naturality f

@[simp] theorem sum_f {C D : BiComplex k B} {I : Type} (s : Finset I)
    (f : I → (C ⟶ D)) (n : ℤ) : (∑ i ∈ s, f i).f n = ∑ i ∈ s, (f i).f n :=
  map_sum (Hom.fAddMonoidHom n) f s

/-- The vertex-zero component vanishes by the actual quadratic relation in B. -/
theorem paths_relation {A J : Type} [Fintype A] [Fintype J]
    (e₀ e₁ e₂ : B) (a : A → B) (b : J → B)
    (ha : ∀ i, a i * e₀ = a i) (hb : ∀ j, b j * e₁ = b j)
    (r : A → J → k) (hr : ∑ i, ∑ j, r i j • (b j * a i) = 0)
    (D : RightComplex B) :
    ∑ i, ∑ j, r i j • (path k B e₁ e₂ (b j) (hb j) D ≫
      path k B e₀ e₁ (a i) (ha i) D) = 0 := by
  apply Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using OAI.tensorInductionOn with
  | add x y hx hy =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
  | tmul c v =>
    erw [sum_smul_component_apply]
    change (∑ i, ∑ j, (algebraMap k (Enveloping k B) (r i j)) •
      ((pathMap e₀ e₁ (a i) (ha i) (pathMap e₁ e₂ (b j) (hb j) c)) ⊗ₜ[k] v)) = 0
    simp only [IsScalarTower.algebraMap_smul, TensorProduct.smul_tmul',
      ← TensorProduct.sum_tmul]
    have hz : (∑ i, ∑ j, r i j •
        pathMap e₀ e₁ (a i) (ha i) (pathMap e₁ e₂ (b j) (hb j) c)) = 0 := by
      apply Subtype.ext
      change ((leftIdeal B e₀).subtype.restrictScalars k)
        (∑ i, ∑ j, r i j • pathMap e₀ e₁ (a i) (ha i)
          (pathMap e₁ e₂ (b j) (hb j) c)) = 0
      simp only [map_sum, map_smul, LinearMap.restrictScalars_apply,
        Submodule.subtype_apply, pathMap_apply]
      calc
        _ = (c : B) * (∑ i, ∑ j, r i j • (b j * a i)) := by
          simp only [Finset.mul_sum, Algebra.mul_smul_comm, mul_assoc]
        _ = 0 := by rw [hr, mul_zero]
    rw [hz, TensorProduct.zero_tmul]
end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_CornerProjection
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
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

theorem ideal_right_fixed (j : Fin 3)
    (x : ExternalTensor.leftIdeal (ThreeVertexAlgebra μ) (vertex μ j)) :
    x.val * vertex μ j = x.val := by
  obtain ⟨b,hb⟩ := x.property
  change b * vertex μ j = x.val at hb
  rw [← hb,mul_assoc,videm]

/-- Left multiplication by e_i on the actual induced-column first factor B e_j. -/
def projection (i j : Fin 3) :
    ExternalTensor.leftIdeal (ThreeVertexAlgebra μ) (vertex μ j) →ₗ[k]
    ExternalTensor.leftIdeal (ThreeVertexAlgebra μ) (vertex μ j) where
  toFun x := ⟨vertex μ i * x.val,⟨vertex μ i * x.val,by
    change (vertex μ i * x.val) * vertex μ j = vertex μ i * x.val
    rw [mul_assoc,ideal_right_fixed]⟩⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' c x := Subtype.ext (mul_smul_comm _ _ _)

@[simp] theorem projection_apply (i j : Fin 3) (x) :
    ((projection μ i j) x).val = vertex μ i * x.val := rfl

end LittleFinitistic.CornerProjection

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
instance biFiniteBiproducts : HasFiniteBiproducts (BiComplex k B) :=
  HasFiniteBiproducts.of_hasFiniteProducts
instance biBinaryBiproducts : HasBinaryBiproducts (BiComplex k B) :=
  HasBinaryBiproducts.of_hasBinaryProducts

variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]

variable {k B}
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))

/-- The actual finite relation evaluated on the chosen chain maps. -/
def relationMap (r : R) : D₀ ⟶ D₂ := ∑ a, ∑ b, s.coeff r a b • (f a ≫ g b)

/-- All columns and components are induced from actual modules, paths and maps. -/
def inducedData : AssemblyData (C := BiComplex k B) (A := A) (J := J) (R := R) where
  V₀ := (columnComplex k B s.e₀).obj D₀
  V₁ := (columnComplex k B s.e₁).obj D₁
  V₂ := (columnComplex k B s.e₂).obj D₂
  U _ := (columnComplex k B s.e₁).obj D₀
  V _ := (columnComplex k B s.e₂).obj D₁
  W _ := (columnComplex k B s.e₂).obj D₀
  pa₀ a := path k B s.e₀ s.e₁ (s.a a) (s.ha a) D₀
  pa₁ a := (columnComplex k B s.e₁).map (f a)
  pb₁ b := path k B s.e₁ s.e₂ (s.b b) (s.hb b) D₁
  pb₂ b := (columnComplex k B s.e₂).map (g b)
  qa r a b := s.coeff r a b • path k B s.e₁ s.e₂ (s.b b) (s.hb b) D₀
  qb r a b := s.coeff r a b • (columnComplex k B s.e₂).map (f a)
  rel r := (columnComplex k B s.e₂).map (relationMap s D₀ D₁ D₂ f g r)
  middle r a b := by simp [Linear.smul_comp]
  first r := by
    simpa only [Linear.smul_comp] using
      paths_relation k B s.e₀ s.e₁ s.e₂ s.a s.b s.ha s.hb (s.coeff r) (s.relation r) D₀
  last r := by
    simp only [Linear.smul_comp, relationMap, Functor.map_sum, Functor.map_smul,
      Functor.map_comp]

abbrev L0Prime := (inducedData s D₀ D₁ D₂ f g).L₀
abbrev L1Prime := (inducedData s D₀ D₁ D₂ f g).L₁
abbrev L2Prime := (inducedData s D₀ D₁ D₂ f g).L₂
abbrev p := (inducedData s D₀ D₁ D₂ f g).p
abbrev q := (inducedData s D₀ D₁ D₂ f g).q

omit [Fintype R] in
@[reassoc] theorem p_arrow01 (a : A) :
    biproduct.ι (inducedData s D₀ D₁ D₂ f g).U a ≫ biprod.inl ≫
      p s D₀ D₁ D₂ f g =
    path k B s.e₀ s.e₁ (s.a a) (s.ha a) D₀ ≫ (inducedData s D₀ D₁ D₂ f g).in₀ -
      (columnComplex k B s.e₁).map (f a) ≫ (inducedData s D₀ D₁ D₂ f g).in₁ := by
  simp only [p, AssemblyData.p, biprod.inl_desc, biproduct.ι_desc]
  rfl

omit [Fintype R] in
@[reassoc] theorem p_arrow12 (b : J) :
    biproduct.ι (inducedData s D₀ D₁ D₂ f g).V b ≫ biprod.inr ≫
      p s D₀ D₁ D₂ f g =
    path k B s.e₁ s.e₂ (s.b b) (s.hb b) D₁ ≫ (inducedData s D₀ D₁ D₂ f g).in₁ -
      (columnComplex k B s.e₂).map (g b) ≫ (inducedData s D₀ D₁ D₂ f g).in₂ := by
  simp only [p, AssemblyData.p, biprod.inr_desc, biproduct.ι_desc]
  rfl

variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

/-- Positive degree-minus-one h of the manuscript, packaged with its equation. -/
def positiveHomotopy :
    Homotopy (biproduct.desc fun r =>
      (inducedData s D₀ D₁ D₂ f g).rel r ≫ (inducedData s D₀ D₁ D₂ f g).in₂) 0 := by
  classical
  let t := inducedData s D₀ D₁ D₂ f g
  let F (r : R) := biproduct.π t.W r ≫ t.rel r ≫ t.in₂
  let hh (r : R) : Homotopy (F r) 0 :=
    framedMapHomotopy (columnFunctor k B s.e₂) (relationMap s D₀ D₁ D₂ f g r)
      (H r) (biproduct.π t.W r) t.in₂
  have hs := AssemblyData.sumHomotopy F hh
  have heq : (∑ r, F r) = biproduct.desc (fun r => t.rel r ≫ t.in₂) := by
    exact biproduct.desc_eq.symm
  refine { hom := hs.hom, zero := hs.zero, comm := ?_ }
  intro i
  rw [← heq]
  exact hs.comm i

/-- The sign-correct null-homotopy required by RectificationTotal.total. -/
def nullHomotopy : Homotopy (q s D₀ D₁ D₂ f g ≫ p s D₀ D₁ D₂ f g) 0 := by
  rw [AssemblyData.composite]
  simpa using (positiveHomotopy s D₀ D₁ D₂ f g H).smul (-1 : k)

end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ColumnProperties
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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

/-- Restrict genuine bimodules to right B-modules. -/
def forgetRight : ModuleCat.{u} (Enveloping k B) ⥤ ModuleCat.{u} Bᵐᵒᵖ :=
  ModuleCat.restrictScalars (Algebra.TensorProduct.includeRight :
    Bᵐᵒᵖ →ₐ[k] Enveloping k B).toRingHom

end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ArrowVertex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4.ArrowVertex
attribute [local instance] ExternalTensor.bimodule ExternalTensor.rightModule
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

/-- Left multiplication on a bimodule, regarded as a right-linear map. -/
def left (a : B) (N : ModuleCat.{u} (Enveloping k B)) :
    (forgetRight k B).obj N →ₗ[Bᵐᵒᵖ] (forgetRight k B).obj N where
  toFun x := (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (show N from x)
  map_add' x y := smul_add (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) (show N from x) (show N from y)
  map_smul' c x := by
    change (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • ((1 ⊗ₜ[k] c : Enveloping k B) • (show N from x)) =
      (1 ⊗ₜ[k] c : Enveloping k B) • ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (show N from x))
    erw [← mul_smul, ← mul_smul]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

@[simp] theorem left_mul (a b : B) (N : ModuleCat.{u} (Enveloping k B))
    (x : (forgetRight k B).obj N) : left k B (a * b) N x = left k B a N (left k B b N x) := by
  change ((a * b) ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (show N from x) =
    (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (show N from x))
  erw [← mul_smul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

@[simp] theorem map_left {N N' : ModuleCat.{u} (Enveloping k B)}
    (f : N ⟶ N') (a : B) (x : (forgetRight k B).obj N) :
    (forgetRight k B).map f (left k B a N x) =
      left k B a N' ((forgetRight k B).map f x) := f.hom.map_smul _ _

/-- The actual fixed submodule eN, for an idempotent e. -/
def space (e : B) (N : ModuleCat.{u} (Enveloping k B)) :
    Submodule Bᵐᵒᵖ ((forgetRight k B).obj N) :=
  LinearMap.ker (left k B e N - LinearMap.id)

@[simp] theorem mem_space (e : B) (N : ModuleCat.{u} (Enveloping k B))
    (x : (forgetRight k B).obj N) : x ∈ space k B e N ↔ left k B e N x = x := by
  simp [space, LinearMap.mem_ker, sub_eq_zero]

/-- Vertex restriction retains the original elements, rather than chosen coordinates. -/
def vertex (e : B) : ModuleCat.{u} (Enveloping k B) ⥤ ModuleCat.{u} Bᵐᵒᵖ where
  obj N := ModuleCat.of _ (space k B e N)
  map f := ModuleCat.ofHom
    { toFun x := ⟨(forgetRight k B).map f x.val, by
        rw [mem_space, ← map_left, (mem_space k B e _ _).1 x.property]⟩
      map_add' x y := Subtype.ext (map_add _ _ _)
      map_smul' c x := Subtype.ext (map_smul _ _ _) }
  map_id N := by ext x; rfl
  map_comp f g := by ext x; rfl
instance vertex_additive (e : B) : (vertex k B e).Additive where
  map_add := by intros; ext x; rfl

abbrev vertexComplex (e : B) : BiComplex k B ⥤ RightComplex B :=
  (vertex k B e).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The intervertex map is precisely left multiplication by a. -/
def arrow (ei ej a : B) (hja : ej * a = a) : vertex k B ei ⟶ vertex k B ej where
  app N := ModuleCat.ofHom
    { toFun x := ⟨left k B a N x.val, by
        rw [mem_space, ← left_mul, hja]⟩
      map_add' x y := Subtype.ext (map_add _ _ _)
      map_smul' c x := Subtype.ext (map_smul _ _ _) }
  naturality {N N'} f := by ext x; apply Subtype.ext; exact (map_left k B f a x.val).symm

abbrev arrowComplex (ei ej a : B) (hja : ej * a = a) (P : BiComplex k B) :
    (vertexComplex k B ei).obj P ⟶ (vertexComplex k B ej).obj P :=
  ((arrow k B ei ej a hja).mapHomologicalComplex (ComplexShape.up ℤ)).app P

@[simp] theorem arrow_original (ei ej a : B) (hja : ej * a = a)
    (P : BiComplex k B) (n : ℤ) (x : ((vertexComplex k B ei).obj P).X n) :
    (((arrowComplex k B ei ej a hja P).f n) x).val =
      (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (show P.X n from x.val) := rfl

/-- Composition uses multiplication in B in the original arrow order. -/
@[reassoc] theorem arrow_comp (ei ej el a b : B) (hja : ej * a = a)
    (hlb : el * b = b) (hlba : el * (b * a) = b * a) (P : BiComplex k B) :
    arrowComplex k B ei ej a hja P ≫ arrowComplex k B ej el b hlb P =
      arrowComplex k B ei el (b * a) hlba P := by
  ext n x
  apply Subtype.ext
  exact (left_mul k B b a (P.X n) x.val).symm

/-- The trivial path acts as the identity on its vertex. -/
@[simp] theorem arrow_id (e : B) (he : e * e = e) (P : BiComplex k B) :
    arrowComplex k B e e e he P = 𝟙 ((vertexComplex k B e).obj P) := by
  ext n x
  apply Subtype.ext
  exact (mem_space k B e (P.X n) x.val).1 x.property

/-- The original diagonal tensor e tensor n in its actual fixed submodule. -/
def diagonal (e : B) (he : e * e = e) :
    𝟭 (ModuleCat.{u} Bᵐᵒᵖ) ⟶ columnFunctor k B e ⋙ vertex k B e where
  app N := ModuleCat.ofHom
    { toFun n := ⟨generator B e ⊗ₜ[k] n, by
        erw [mem_space]
        change (e • generator B e) ⊗ₜ[k] ((1 : Bᵐᵒᵖ) • n) = generator B e ⊗ₜ[k] n
        rw [one_smul]
        congr 1
        exact Subtype.ext he⟩
      map_add' x y := Subtype.ext (TensorProduct.tmul_add _ _ _)
      map_smul' c x := by
        apply Subtype.ext
        change generator B e ⊗ₜ[k] (c • x) =
          (1 ⊗ₜ[k] c : Enveloping k B) • (generator B e ⊗ₜ[k] x)
        rw [ExternalTensor.smul_tmul, one_smul] }
  naturality {N N'} f := by ext x; rfl

/-- Original insertion into a single induced column, degree by degree. -/
def diagonalComplex (e : B) (he : e * e = e) (D : RightComplex B) :
    D ⟶ (vertexComplex k B e).obj ((columnComplex k B e).obj D) where
  f n := (diagonal k B e he).app (D.X n)
  comm' i j _hij := (diagonal k B e he).naturality (D.d i j)

@[reassoc] theorem diagonal_naturality (e : B) (he : e * e = e)
    {D E : RightComplex B} (f : D ⟶ E) :
    f ≫ diagonalComplex k B e he E = diagonalComplex k B e he D ≫
      (vertexComplex k B e).map ((columnComplex k B e).map f) := by
  ext n x
  rfl

/-- Right multiplication in p at e_j agrees with left arrow action at e_i. -/
@[reassoc] theorem diagonal_path (ei ej a : B) (hei : ei * ei = ei)
    (hej : ej * ej = ej) (hai : a * ei = a) (hja : ej * a = a)
    (D : RightComplex B) :
    diagonalComplex k B ej hej D ≫ (vertexComplex k B ej).map (path k B ei ej a hai D) =
      diagonalComplex k B ei hei D ≫
        arrowComplex k B ei ej a hja ((columnComplex k B ei).obj D) := by
  ext n x
  apply Subtype.ext
  change (pathMap ei ej a hai (generator B ej)) ⊗ₜ[k] x =
    (a • generator B ei) ⊗ₜ[k] ((1 : Bᵐᵒᵖ) • x)
  rw [one_smul]
  congr 1
  apply Subtype.ext
  exact hja.trans hai.symm

@[reassoc] theorem arrow_naturality (ei ej a : B) (hja : ej * a = a)
    {P Q : BiComplex k B} (f : P ⟶ Q) :
    (vertexComplex k B ei).map f ≫ arrowComplex k B ei ej a hja Q =
      arrowComplex k B ei ej a hja P ≫ (vertexComplex k B ej).map f :=
  ((arrow k B ei ej a hja).mapHomologicalComplex (ComplexShape.up ℤ)).naturality f
end ExternalTensor.Section4.ArrowVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ArrowCompatibility
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.LittleFinitistic.CornerProjection.projection_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4.ArrowVertex
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- Original insertion through the zero-column inclusion of the actual total. -/
def iota {L₀ L₁ L₂ : BiComplex k B} (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁)
    (h : Homotopy (q ≫ p) 0) (e : B) (he : e * e = e)
    (D : RightComplex B) (t : (columnComplex k B e).obj D ⟶ L₀) :
    D ⟶ (vertexComplex k B e).obj (LittleFinitistic.RectificationTotal.total p q h) :=
  diagonalComplex k B e he D ≫ (vertexComplex k B e).map
    (t ≫ LittleFinitistic.RectificationTotal.inclusion p q h)

/-- The insertion has exactly the manuscript's diagonal tensor, before any coordinates. -/
@[simp] theorem iota_original {L₀ L₁ L₂ : BiComplex k B}
    (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁) (h : Homotopy (q ≫ p) 0)
    (e : B) (he : e * e = e) (D : RightComplex B)
    (t : (columnComplex k B e).obj D ⟶ L₀) (n : ℤ) (x : D.X n) :
    (((iota p q h e he D t).f n) x).val =
      ((t ≫ LittleFinitistic.RectificationTotal.inclusion p q h).f n)
        (generator B e ⊗ₜ[k] x) := rfl

/-- The original p-boundary produces compatibility in the actual target vertex. -/
def compatibility {L₀ L₁ L₂ : BiComplex k B} (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁)
    (h : Homotopy (q ≫ p) 0) (ei ej a : B) (hei : ei * ei = ei)
    (hej : ej * ej = ej) (hai : a * ei = a) (hja : ej * a = a)
    {D E : RightComplex B} (f : D ⟶ E)
    (t : (columnComplex k B ei).obj D ⟶ L₀)
    (u : (columnComplex k B ej).obj E ⟶ L₀)
    (w : (columnComplex k B ej).obj D ⟶ L₁)
    (hw : w ≫ p = path k B ei ej a hai D ≫ t - (columnComplex k B ej).map f ≫ u) :
    Homotopy
      (iota p q h ei hei D t ≫ arrowComplex k B ei ej a hja
        (LittleFinitistic.RectificationTotal.total p q h))
      (f ≫ iota p q h ej hej E u) := by
  let inc := LittleFinitistic.RectificationTotal.inclusion p q h
  let F := vertexComplex k B ej
  have hb := (LittleFinitistic.RectificationTotal.boundaryHomotopy p q h).compLeft w
  have hh := ((vertex k B ej).mapHomotopy hb).compLeft (diagonalComplex k B ej hej D)
  have heq : diagonalComplex k B ej hej D ≫ F.map (w ≫ p ≫ inc) =
      iota p q h ei hei D t ≫ arrowComplex k B ei ej a hja
        (LittleFinitistic.RectificationTotal.total p q h) -
        f ≫ iota p q h ej hej E u := by
    rw [← Category.assoc w p inc, hw, Preadditive.sub_comp, Functor.map_sub,
      Preadditive.comp_sub]
    apply congrArg₂ (fun x y => x - y)
    · change diagonalComplex k B ej hej D ≫
          (vertexComplex k B ej).map ((path k B ei ej a hai D ≫ t) ≫ inc) = _
      rw [Category.assoc, Functor.map_comp, ← Category.assoc,
        diagonal_path k B ei ej a hei hej hai hja D, Category.assoc,
        ← arrow_naturality]
      rfl
    · change diagonalComplex k B ej hej D ≫
          (vertexComplex k B ej).map (((columnComplex k B ej).map f ≫ u) ≫ inc) = _
      rw [Category.assoc, Functor.map_comp, ← Category.assoc, ← diagonal_naturality]
      rfl
  refine Homotopy.equivSubZero.symm ?_
  change Homotopy (diagonalComplex k B ej hej D ≫ F.map (w ≫ p ≫ inc))
    (diagonalComplex k B ej hej D ≫ F.map (w ≫ 0)) at hh
  rw [comp_zero, Functor.map_zero, comp_zero, heq] at hh
  exact hh

variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

abbrev actualP : BiComplex k B := LittleFinitistic.RectificationTotal.total
  (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g) (nullHomotopy s D₀ D₁ D₂ f g H)

abbrev iota0 (he : s.e₀ * s.e₀ = s.e₀) :=
  iota (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g) (nullHomotopy s D₀ D₁ D₂ f g H)
    s.e₀ he D₀ (inducedData s D₀ D₁ D₂ f g).in₀
abbrev iota1 (he : s.e₁ * s.e₁ = s.e₁) :=
  iota (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g) (nullHomotopy s D₀ D₁ D₂ f g H)
    s.e₁ he D₁ (inducedData s D₀ D₁ D₂ f g).in₁
abbrev iota2 (he : s.e₂ * s.e₂ = s.e₂) :=
  iota (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g) (nullHomotopy s D₀ D₁ D₂ f g H)
    s.e₂ he D₂ (inducedData s D₀ D₁ D₂ f g).in₂

/-- Compatibility of the actual original vertex-zero insertion with every 0-to-1 arrow. -/
def compatibility01 (h₀ : s.e₀ * s.e₀ = s.e₀) (h₁ : s.e₁ * s.e₁ = s.e₁)
    (a : A) (ha : s.e₁ * s.a a = s.a a) :
    Homotopy (iota0 s D₀ D₁ D₂ f g H h₀ ≫
      arrowComplex k B s.e₀ s.e₁ (s.a a) ha (actualP s D₀ D₁ D₂ f g H))
      (f a ≫ iota1 s D₀ D₁ D₂ f g H h₁) :=
  compatibility _ _ _ _ _ _ h₀ h₁ (s.ha a) ha (f a) _ _
    (biproduct.ι (inducedData s D₀ D₁ D₂ f g).U a ≫ biprod.inl)
    (p_arrow01 s D₀ D₁ D₂ f g a)

/-- Compatibility of the actual original vertex-one insertion with every 1-to-2 arrow. -/
def compatibility12 (h₁ : s.e₁ * s.e₁ = s.e₁) (h₂ : s.e₂ * s.e₂ = s.e₂)
    (b : J) (hb : s.e₂ * s.b b = s.b b) :
    Homotopy (iota1 s D₀ D₁ D₂ f g H h₁ ≫
      arrowComplex k B s.e₁ s.e₂ (s.b b) hb (actualP s D₀ D₁ D₂ f g H))
      (g b ≫ iota2 s D₀ D₁ D₂ f g H h₂) :=
  compatibility _ _ _ _ _ _ h₁ h₂ (s.hb b) hb (g b) _ _
    (biproduct.ι (inducedData s D₀ D₁ D₂ f g).V b ≫ biprod.inr)
    (p_arrow12 s D₀ D₁ D₂ f g b)
end ExternalTensor.Section4.ArrowVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_InducedRectification
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.InducedRectification
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

/-- The actual three-column induced bimodule complex of Section 4. -/
def total : BiComplex k B :=
  RectificationTotal.total (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g)
    (nullHomotopy s D₀ D₁ D₂ f g H)

/-- The entire zero column has its original chain inclusion. -/
def inclusion : L0Prime s D₀ D₁ D₂ f g ⟶ total s D₀ D₁ D₂ f g H :=
  RectificationTotal.inclusion _ _ _

end LittleFinitistic.InducedRectification

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_NativeArrowBridge
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule
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
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

/-- The direct original insertion in the native P and native fixed-submodule functor. -/
def originalIota (e : B) (he : e * e = e) (D : RightComplex B)
    (t : (columnComplex k B e).obj D ⟶ L0Prime s D₀ D₁ D₂ f g) :
    D ⟶ (nativeVertex e).obj (LittleFinitistic.InducedRectification.total s D₀ D₁ D₂ f g H) :=
  diagonalComplex k B e he D ≫ (nativeVertex e).map t ≫
    (nativeVertex e).map (LittleFinitistic.InducedRectification.inclusion s D₀ D₁ D₂ f g H)

/-- No comparison hypothesis is needed to identify the proved insertion with native maps. -/
theorem iota_eq_original (e : B) (he : e * e = e) (D : RightComplex B)
    (t : (columnComplex k B e).obj D ⟶ L0Prime s D₀ D₁ D₂ f g) :
    iota (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g)
      (nullHomotopy s D₀ D₁ D₂ f g H) e he D t =
      originalIota s D₀ D₁ D₂ f g H e he D t := by
  simp only [iota, originalIota, Functor.map_comp]
  rfl

/-- The native original diagonal map is determined by its tensor formula. -/
theorem diagonal_eq_of_original (e : B) (he : e * e = e) (D : RightComplex B)
    (j : D ⟶ (nativeVertex e).obj ((columnComplex k B e).obj D))
    (hj : ∀ n x, ((j.f n) x).val = generator B e ⊗ₜ[k] x) :
    j = diagonalComplex k B e he D := by
  ext n x
  apply Subtype.ext
  exact hj n x

/-- Actual arrow-01 compatibility with the native P, vertex functors and inclusions. -/
def nativeCompatibility01 (h₀ : s.e₀ * s.e₀ = s.e₀) (h₁ : s.e₁ * s.e₁ = s.e₁)
    (a : A) (ha : s.e₁ * s.a a = s.a a) :
    Homotopy
      (originalIota s D₀ D₁ D₂ f g H s.e₀ h₀ D₀ (inducedData s D₀ D₁ D₂ f g).in₀ ≫
        arrowComplex k B s.e₀ s.e₁ (s.a a) ha
          (LittleFinitistic.InducedRectification.total s D₀ D₁ D₂ f g H))
      (f a ≫ originalIota s D₀ D₁ D₂ f g H s.e₁ h₁ D₁
        (inducedData s D₀ D₁ D₂ f g).in₁) := by
  have ht := compatibility01 s D₀ D₁ D₂ f g H h₀ h₁ a ha
  dsimp only [iota0, iota1] at ht
  erw [iota_eq_original s D₀ D₁ D₂ f g H,
    iota_eq_original s D₀ D₁ D₂ f g H] at ht
  exact ht

end ExternalTensor.Section4.ArrowVertex.NativeBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SourceFiltration
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (t : AssemblyData (C := BiComplex k B) (A := A) (J := J) (R := R))

/-- Source at least one: the actual D1 and D2 vertex terms and D1 arrow terms. -/
abbrev F1₀ := t.V₁ ⊞ t.V₂
abbrev F1₁ := ⨁ t.V
def Z : BiComplex k B where
  X _ := ModuleCat.of _ PUnit
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

def p1 : F1₁ t ⟶ F1₀ t :=
  biproduct.desc fun b => t.pb₁ b ≫ biprod.inl - t.pb₂ b ≫ biprod.inr

def h1 : Homotopy ((0 : Z ⟶ F1₁ t) ≫ p1 t) 0 where
  hom _ _ := 0
  zero _ _ _ := rfl
  comm _ := by simp [dNext, prevD]

/-- Source zero quotient: retain precisely the path-multiplication terms. -/
def p0 : (⨁ t.U) ⟶ t.V₀ := biproduct.desc t.pa₀

def q0 : t.L₂ ⟶ (⨁ t.U) :=
  biproduct.desc fun r => ∑ a, ∑ b, t.qa r a b ≫ biproduct.ι t.U a

theorem q0_p0 : q0 t ≫ p0 t = 0 := by
  apply biproduct.hom_ext'
  intro r
  simpa [q0, p0, Preadditive.sum_comp] using t.first r

def h0 : Homotopy (q0 t ≫ p0 t) 0 where
  hom _ _ := 0
  zero _ _ _ := rfl
  comm n := by rw [q0_p0]; simp [dNext, prevD]

omit [Fintype R] in
@[reassoc] theorem in_p : (biprod.inr : F1₁ t ⟶ t.L₁) ≫ t.p =
    p1 t ≫ (biprod.inr : F1₀ t ⟶ t.L₀) := by
  apply biproduct.hom_ext'
  intro b
  simp [AssemblyData.p, p1, AssemblyData.in₁, AssemblyData.in₂,
    Preadditive.sub_comp]

omit [Fintype R] in
@[reassoc] theorem p_out : t.p ≫ (biprod.fst : t.L₀ ⟶ t.V₀) =
    (biprod.fst : t.L₁ ⟶ ⨁ t.U) ≫ p0 t := by
  apply biprod.hom_ext' <;> apply biproduct.hom_ext' <;> intro a <;>
    simp [AssemblyData.p, p0, AssemblyData.in₀, AssemblyData.in₁,
      AssemblyData.in₂, Preadditive.sub_comp]

@[reassoc] theorem q_out : t.q ≫ (biprod.fst : t.L₁ ⟶ ⨁ t.U) = q0 t := by
  apply biproduct.hom_ext'
  intro r
  simp [AssemblyData.q, q0, Preadditive.sum_comp, Preadditive.add_comp]

end ExternalTensor.Section4.SourceFiltration

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_FiltrationExactness
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration.Exactness
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

abbrev data := inducedData s D₀ D₁ D₂ f g
abbrev F1 := total (p1 (data s D₀ D₁ D₂ f g)) 0 (h1 (data s D₀ D₁ D₂ f g))
abbrev G0 := total (p0 (data s D₀ D₁ D₂ f g)) (q0 (data s D₀ D₁ D₂ f g))
  (h0 (data s D₀ D₁ D₂ f g))
end ExternalTensor.Section4.SourceFiltration.Exactness

end

end OAI
end


