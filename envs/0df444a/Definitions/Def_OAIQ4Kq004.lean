-- Prove2me | Definitions.Def_OAIQ4Kq004
-- name    : OAIQ4Kq004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T08:30:36.272191+00:00
-- url     : https://prove2.me/theorems/8926e8a8-232b-4925-97f4-7181ebb04f65
-- title:
--   Definitions bundle OAIQ4Kq004 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kaplansky.kaplansky_quasitrace_counterexample`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 88 declarations of OpenAI's Lean: 40 definitions, 4 instances and 44 theorems. The definitions and types are `OAI.Kaplansky.affineAvoidanceChart`, `OAI.Kaplansky.centeredChartHomeomorph`, `OAI.Kaplansky.chartBaseMap`, `OAI.Kaplansky.closedSubalgebraLE`, `OAI.Kaplansky.closedSubalgebraPreorder`, `OAI.Kaplansky.cokernelBiprodIso`, `OAI.Kaplansky.complexDiagonalHomotopy`, `OAI.Kaplansky.complexDiagonalMap`, `OAI.Kaplansky.complexLineCoordinateUnit`, `OAI.Kaplansky.continuousLinearEquivPuncturedHomeomorph`, `OAI.Kaplansky.continuousLinearEquivSphereHomotopyEquiv`, `OAI.Kaplansky.contractibleProductProjection`, `OAI.Kaplansky.cstarMatrixFlatten`, `OAI.Kaplansky.defectA`, `OAI.Kaplansky.defectAEntries`, `OAI.Kaplansky.defectB`, `OAI.Kaplansky.defectBEntries`, `OAI.Kaplansky.diagonal`, `OAI.Kaplansky.euclideanSpherePole`, `OAI.Kaplansky.firstCoordinateSubspaceHomeomorph`, `OAI.Kaplansky.intersectionSubtypeSwap`, `OAI.Kaplansky.kernelShortComplex`, `OAI.Kaplansky.kernelShortComplexInclusion`, `OAI.Kaplansky.leftSquare`, `OAI.Kaplansky.lineFrameEquiv`, `OAI.Kaplansky.linearIsometrySphereHomeomorph`, `OAI.Kaplansky.orderedGroupRationalCone`, `OAI.Kaplansky.partialSum`, `OAI.Kaplansky.productSubspaceHomeomorph`, `OAI.Kaplansky.puncturedVectorSphereHomotopyEquiv`, `OAI.Kaplansky.quotientShortComplex`, `OAI.Kaplansky.quotientShortComplexProjection`, `OAI.Kaplansky.quotientSnakeInput`, `OAI.Kaplansky.rightSquare`, `OAI.Kaplansky.signedCoordinateHalfspace`, `OAI.Kaplansky.sphereEquatorEuclideanHomeomorph`, `OAI.Kaplansky.spherePlaneOverlapRealHomeomorph`, `OAI.Kaplansky.spherePoleHomeomorph`, `OAI.Kaplansky.spherePoleOverlapHomeomorph`, `OAI.Kaplansky.spherePoleOverlapHomotopyEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: `BundleTests_Twisted`, `ComplexBundle_Pullback`, `ComplexBundle_Tensor`, `IntegralHomology_AffineAvoidance`, `IntegralHomology_Connected`, `IntegralHomology_Excision`, `IntegralHomology_HyperplaneFiber`, `IntegralHomology_MayerVietoris`, `IntegralHomology_Product`, `IntegralHomology_ProductCover`, `IntegralHomology_ProjectiveLocal`, `IntegralHomology_Quotient`, `IntegralHomology_SmallExcision`, `IntegralHomology_Sphere`, `Kaplansky_Products`, `OrderedStates_RationalCone`, `OrderedStates_Semigroup`, `Quasitrace_Defect`, `Quasitrace_Extension`, `Quasitrace_Infiniteness`, `Quasitrace_Matrix`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ4Kq007` and `OAIQ4Kq008`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ4_Kq.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Tensor line bundles, metrics, and finite frames. -/

section
open Bundle Topology
namespace Kaplansky

variable {B J : Type} [TopologicalSpace B]
  (C : VectorBundleCore ℂ B ℂ J) (u : ∀ b, C.Fiber b)
  (hu : ∀ b, u b ≠ 0)

/-- Coordinates relative to an actual nowhere-zero line section. -/
def lineFrameEquiv (b : B) : C.Fiber b ≃ₗ[ℂ] ℂ where
  toFun z := (show ℂ from z) / (show ℂ from u b)
  invFun z := z * (show ℂ from u b)
  left_inv z := by
    change ((show ℂ from z) / (show ℂ from u b)) * (show ℂ from u b) = (show ℂ from z)
    exact div_mul_cancel₀ _ (hu b)
  right_inv z := by
    change (z * (show ℂ from u b)) / (show ℂ from u b) = z
    exact mul_div_cancel_right₀ _ (hu b)
  map_add' z w := add_div _ _ _
  map_smul' c z := by change (c*(show ℂ from z))/_ = c*((show ℂ from z)/_); ring

end Kaplansky

end

open Bundle Topology
open scoped InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_Quotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Short exact quotient complexes and biproduct cokernels. -/

section
open CategoryTheory Limits
variable {C : Type*} [Category* C] [Abelian C]
  {S T : ShortComplex C} (f : S ⟶ T)

/-- Componentwise cokernels, with the actual induced maps. -/
def quotientShortComplex : ShortComplex C where
  f := cokernel.map f.τ₁ f.τ₂ S.f T.f f.comm₁₂
  g := cokernel.map f.τ₂ f.τ₃ S.g T.g f.comm₂₃
  zero := by
    apply (cancel_epi (cokernel.π f.τ₁)).mp
    simp [Category.assoc]

def quotientShortComplexProjection : T ⟶ quotientShortComplex f where
  τ₁ := cokernel.π f.τ₁
  τ₂ := cokernel.π f.τ₂
  τ₃ := cokernel.π f.τ₃
  comm₁₂ := by simp [quotientShortComplex]
  comm₂₃ := by simp [quotientShortComplex]

def kernelShortComplex : ShortComplex C where
  f := kernel.map f.τ₁ f.τ₂ S.f T.f f.comm₁₂
  g := kernel.map f.τ₂ f.τ₃ S.g T.g f.comm₂₃
  zero := by
    apply (cancel_mono (kernel.ι f.τ₃)).mp
    simp [Category.assoc]

def kernelShortComplexInclusion : kernelShortComplex f ⟶ S where
  τ₁ := kernel.ι f.τ₁
  τ₂ := kernel.ι f.τ₂
  τ₃ := kernel.ι f.τ₃
  comm₁₂ := by simp [kernelShortComplex]
  comm₂₃ := by simp [kernelShortComplex]

def quotientSnakeInput (hS : S.ShortExact) (hT : T.ShortExact) :
    ShortComplex.SnakeInput C where
  L₀ := kernelShortComplex f
  L₁ := S
  L₂ := T
  L₃ := quotientShortComplex f
  v₀₁ := kernelShortComplexInclusion f
  v₁₂ := f
  v₂₃ := quotientShortComplexProjection f
  w₀₂ := by ext <;> exact kernel.condition _
  w₁₃ := by ext <;> exact cokernel.condition _
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ <;>
      apply (KernelFork.isLimitMapConeEquiv _ _).2 <;>
      exact kernelIsKernel _
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ <;>
      apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2 <;>
      exact cokernelIsCokernel _
  L₁_exact := hS.exact
  epi_L₁_g := hS.epi_g
  L₂_exact := hT.exact
  mono_L₂_f := hT.mono_f

/-- Quotienting two short exact rows by an injective map on their right
terms gives a short exact row. This is the algebraic relative gluing step. -/
theorem quotientShortComplex_shortExact (hS : S.ShortExact) (hT : T.ShortExact)
    [Mono f.τ₃] : (quotientShortComplex f).ShortExact := by
  let D := quotientSnakeInput f hS hT
  have hzero : D.δ = 0 := (isZero_kernel_of_mono f.τ₃).eq_of_src _ _
  have hm : Mono (quotientShortComplex f).f :=
    (D.L₂'.exact_iff_mono hzero).mp D.L₂'_exact
  have he : Epi (quotientShortComplex f).g := by
    have hc : Epi (T.g ≫ cokernel.π f.τ₃) :=
      epi_comp' hT.epi_g (coequalizer.π_epi (f := f.τ₃) (g := 0))
    exact @epi_of_epi_fac _ _ _ _ _ _ _ _ hc (show cokernel.π f.τ₂ ≫ (quotientShortComplex f).g =
      T.g ≫ cokernel.π f.τ₃ by simp [quotientShortComplex])
  exact { exact := D.L₃_exact }

end

open CategoryTheory Limits
section
variable {C : Type*} [Category* C] [Abelian C]
  {A B X Y : C} (f : A ⟶ X) (g : B ⟶ Y)

/-- The quotient of a direct sum is the direct sum of the actual quotients. -/
def cokernelBiprodIso : cokernel (biprod.map f g) ≅ cokernel f ⊞ cokernel g where
  hom := cokernel.desc _ (biprod.map (cokernel.π f) (cokernel.π g)) (by
    ext <;> simp)
  inv := biprod.desc
    (cokernel.desc f (biprod.inl ≫ cokernel.π (biprod.map f g)) (by
      rw [← biprod.inl_map_assoc, cokernel.condition]; simp))
    (cokernel.desc g (biprod.inr ≫ cokernel.π (biprod.map f g)) (by
      rw [← biprod.inr_map_assoc, cokernel.condition]; simp))
  hom_inv_id := by
    apply (cancel_epi (cokernel.π (biprod.map f g))).mp
    ext <;> simp
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply (cancel_epi (cokernel.π f)).mp
      simp [Category.assoc]
    · apply (cancel_epi (cokernel.π g)).mp
      simp [Category.assoc]

@[reassoc (attr := simp)]
theorem cokernelBiprodIso_projection :
    cokernel.π (biprod.map f g) ≫ (cokernelBiprodIso f g).hom =
      biprod.map (cokernel.π f) (cokernel.π g) := by simp [cokernelBiprodIso]

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_SmallExcision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Small relative excision, Mayer-Vietoris, and naturality. -/

section
open CategoryTheory Limits HomologicalComplex
variable {X : Type} [TopologicalSpace X] (U V : Set X)

theorem homology_biprod_isZero (C D : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (hC : IsZero (C.homology n)) (hD : IsZero (D.homology n)) :
    IsZero ((C ⊞ D).homology n) := by
  let F := homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n
  have hfst : F.map (biprod.fst : C ⊞ D ⟶ C) = 0 := hC.eq_of_tgt _ _
  have hsnd : F.map (biprod.snd : C ⊞ D ⟶ D) = 0 := hD.eq_of_tgt _ _
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 (F.obj (C ⊞ D)) = 0
  rw [← F.map_id, ← biprod.total, F.map_add, F.map_comp, F.map_comp,
    hfst, hsnd, zero_comp, zero_comp, add_zero]

end

open CategoryTheory Limits

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_MayerVietoris
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Relative Mayer-Vietoris comparison, exactness, and gluing. -/

section
open CategoryTheory Limits HomologicalComplex

theorem comp_zero_of_iso {C : Type*} [Category* C] [HasZeroMorphisms C]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (f' : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃)
    (hf : e₁.hom ≫ f' = f ≫ e₂.hom) (hg : e₂.hom ≫ g' = g ≫ e₃.hom)
    (h : f ≫ g = 0) : f' ≫ g' = 0 := by
  apply (cancel_epi e₁.hom).mp
  rw [← Category.assoc, hf, Category.assoc, hg, ← Category.assoc, h, zero_comp, comp_zero]

section
local instance instPreservesBinaryBiproductsHomologicalComplexNatModuleCatIntDownHomologyFunctor_solutions (n : ℕ) : PreservesBinaryBiproducts
    (homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _
variable {X : Type} [TopologicalSpace X]

/-- The same intersection subspace, in the opposite order of its subtypes. -/
def intersectionSubtypeSwap (U A : Set X) :
    (Subtype.val ⁻¹' U : Set A) ≃ₜ (Subtype.val ⁻¹' A : Set U) where
  toFun z := ⟨⟨z.1.1,z.2⟩,z.1.2⟩
  invFun z := ⟨⟨z.1.1,z.2⟩,z.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

end

section
local instance instPreservesBinaryBiproductsHomologicalComplexNatModuleCatIntDownHomologyFunctor_solutions_1 (n : ℕ) : PreservesBinaryBiproducts
    (homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

end

end

open CategoryTheory Limits HomologicalComplex

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Pullback line bundles and their continuous chart identifications. -/

open Bundle Topology
namespace Kaplansky
variable {B A S : Type} [TopologicalSpace B] [TopologicalSpace A]
  [Fintype S] {J : S → Type}
  (C : ∀ s, VectorBundleCore ℂ B ℂ (J s)) (U : Set B) (e : U ≃ₜ A)

def chartBaseMap : C(A,B) :=
  ⟨fun a => (e.symm a).val, continuous_subtype_val.comp e.symm.continuous⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_Excision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Excision for chart-small chains, open covers, and open embeddings. -/

open CategoryTheory Limits HomologicalComplex
section
variable {X : Type} [TopologicalSpace X] [T1Space X]

/-- Center an arbitrary full vector-space chart at the point under study. -/
def centeredChartHomeomorph {E : Type} [NormedAddCommGroup E]
    (U : Set X) (x : X) (hx : x ∈ U) (e : U ≃ₜ E) : U ≃ₜ E :=
  e.trans (Homeomorph.addRight (-e ⟨x,hx⟩))

omit [T1Space X] in
theorem centeredChartHomeomorph_center {E : Type} [NormedAddCommGroup E]
    (U : Set X) (x : X) (hx : x ∈ U) (e : U ≃ₜ E) :
    centeredChartHomeomorph U x hx e ⟨x,hx⟩ = 0 := by
  simp [centeredChartHomeomorph]

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_Product
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Product-pair homology, pair homotopies, and diagonal normalization. -/

section
open CategoryTheory Limits ContinuousMap
variable {B V : Type} [TopologicalSpace B] [TopologicalSpace V]

/-- Projection from a product with an actually contractible base, keeping
the projection itself as the forward map. -/
def contractibleProductProjection [ContractibleSpace B] (V : Type) [TopologicalSpace V] :
    B × V ≃ₕ V := by
  let e := Classical.choice (ContractibleSpace.hequiv_unit B)
  exact (e.prodCongr (ContinuousMap.HomotopyEquiv.refl V)).trans
    (Homeomorph.uniqueProd Unit V).toHomotopyEquiv

/-- The punctured trivial-bundle subspace really is the product of the
base and the punctured model. -/
def productSubspaceHomeomorph (W : Set V) :
    ({z : B × V | z.2 ∈ W} : Set (B × V)) ≃ₜ B × W where
  toFun z := (z.1.1, ⟨z.1.2, z.2⟩)
  invFun z := ⟨(z.1, z.2.1), z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

end

section
open CategoryTheory ContinuousMap
open scoped unitInterval
variable {ι : Type}

/-- Complex diagonal coordinate change with every multiplier invertible. -/
def complexDiagonalMap (a : ι → ℂˣ) : C((ι → ℂ),(ι → ℂ)) :=
  ⟨fun v i => (a i : ℂ) * v i, continuous_pi (fun i => continuous_const.mul (continuous_apply i))⟩

theorem complexDiagonalMap_nonzero (a : ι → ℂˣ) :
    Set.MapsTo (complexDiagonalMap a) ({0}ᶜ : Set (ι → ℂ)) {0}ᶜ := by
  intro v hv he
  apply hv
  funext i
  have h : (a i : ℂ) * v i = 0 := congrFun he i
  exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero (a i))

/-- A path through complex units supplies a genuine nonzero-preserving
homotopy to the identity; no determinant-to-degree assertion is assumed. -/
def complexDiagonalHomotopy (a : ι → ℂˣ) :
    Homotopy (complexDiagonalMap a) (ContinuousMap.id (ι → ℂ)) := by
  let γ : Path a (fun _ => (1 : ℂˣ)) :=
    Classical.choice (PathConnectedSpace.joined a (fun _ => (1 : ℂˣ)))
  exact
    { toFun := fun z i => (γ z.1 i : ℂ) * z.2 i
      continuous_toFun := continuous_pi (fun i =>
        (Units.continuous_val.comp ((continuous_apply i).comp
          (γ.continuous.comp continuous_fst))).mul ((continuous_apply i).comp continuous_snd))
      map_zero_left := fun v => by ext i; simp [complexDiagonalMap]
      map_one_left := fun v => by ext i; simp }

theorem complexDiagonalHomotopy_nonzero (a : ι → ℂˣ) :
    ∀ t : I, ∀ v ∈ ({0}ᶜ : Set (ι → ℂ)), complexDiagonalHomotopy a (t,v) ∈ ({0}ᶜ : Set (ι → ℂ)) := by
  intro t v hv
  exact complexDiagonalMap_nonzero _ hv

end

open CategoryTheory ContinuousMap
section
variable {B ι : Type} [TopologicalSpace B]

/-- The unit comparing two genuine complex coordinates on a line. -/
def complexLineCoordinateUnit {L : Type} [AddCommGroup L] [Module ℂ L]
    (e f : L ≃ₗ[ℂ] ℂ) : ℂˣ :=
  Units.mk0 (f (e.symm 1)) (by
    intro h
    have he := f.injective (h.trans (map_zero f).symm)
    have hz := congrArg e he
    simp at hz)

theorem complexLineCoordinate_change {L : Type} [AddCommGroup L] [Module ℂ L]
    (e f : L ≃ₗ[ℂ] ℂ) (z : ℂ) :
    f (e.symm z) = (complexLineCoordinateUnit e f : ℂ) * z := by
  have h : e.symm z = z • e.symm 1 := by
    rw [← map_smul]
    simp
  rw [h, map_smul]
  change z * f (e.symm 1) = f (e.symm 1) * z
  exact mul_comm _ _

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_Connected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Connected-cover homology, degree-zero components, and degree-one generators. -/

section
open CategoryTheory Limits HomologicalComplex

section

theorem additiveFunctor_biprod_detect_zero
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X Y : C} [HasBinaryBiproduct X Y]
    {T : D} (f : T ⟶ F.obj (X ⊞ Y))
    (h₁ : f ≫ F.map biprod.fst = 0) (h₂ : f ≫ F.map biprod.snd = 0) : f = 0 := by
  have he := congrArg (fun g : X ⊞ Y ⟶ X ⊞ Y => f ≫ F.map g)
    (biprod.total (X := X) (Y := Y))
  simp only [Functor.map_add, Functor.map_comp, Preadditive.comp_add,
    ← Category.assoc] at he
  erw [F.map_id, Category.comp_id] at he
  rw [h₁, h₂, zero_comp, zero_comp, add_zero] at he
  exact he.symm

/-- Homology of a biproduct is jointly detected by its two projections. -/
theorem homology_biprod_detect_zero {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    {T : ModuleCat.{0} ℤ} (n : ℕ) (f : T ⟶ (C ⊞ D).homology n)
    (h₁ : f ≫ homologyMap biprod.fst n = 0)
    (h₂ : f ≫ homologyMap biprod.snd n = 0) : f = 0 := by
  exact additiveFunctor_biprod_detect_zero
    (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n) f h₁ h₂

end

end

open CategoryTheory Limits

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_Sphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Suspension homology and integral top generators of spheres. -/

section
open CategoryTheory ContinuousMap

/-- Radial normalization gives a genuine homotopy equivalence of the
punctured vector space with its unit sphere. -/
def puncturedVectorSphereHomotopyEquiv (V : Type)
    [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ({0}ᶜ : Set V) ≃ₕ Metric.sphere (0 : V) 1 := by
  letI : ContractibleSpace (Set.Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, by norm_num⟩
  let e := Classical.choice (ContractibleSpace.hequiv_unit (Set.Ioi (0 : ℝ)))
  exact (homeomorphUnitSphereProd V).toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl _).prodCongr e).trans
      (Homeomorph.prodUnique _ Unit).toHomotopyEquiv)

end

section
open Metric ContinuousMap
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The sphere with one pole removed is the actual orthogonal hyperplane. -/
def spherePoleHomeomorph (v : sphere (0 : E) 1) :
    ({v}ᶜ : Set (sphere (0 : E) 1)) ≃ₜ (ℝ ∙ (v : E))ᗮ :=
  (stereographic (norm_eq_of_mem_sphere v)).toHomeomorphSourceTarget.trans
    (Homeomorph.Set.univ _)

@[simp] theorem spherePoleHomeomorph_apply (v : sphere (0 : E) 1)
    (x : ({v}ᶜ : Set (sphere (0 : E) 1))) :
    spherePoleHomeomorph v x = stereographic (norm_eq_of_mem_sphere v) x.val := rfl

theorem sphere_pole_ne_neg (v : sphere (0 : E) 1) : v ≠ -v := by
  intro h
  have h' : (v : E) = -(v : E) := congrArg Subtype.val h
  have hz : (v : E) = 0 := by
    have : (2 : ℝ) • (v : E) = 0 := by rw [two_smul]; exact (congrArg (fun x : E => x + (v : E)) h').trans (neg_add_cancel _)
    exact (smul_eq_zero.mp this).resolve_left (by norm_num)
  have := norm_eq_of_mem_sphere v
  simp [hz] at this

theorem sphere_poles_open_cover (v : sphere (0 : E) 1) :
    IsOpen ({v}ᶜ : Set (sphere (0 : E) 1)) ∧
    IsOpen ({-v}ᶜ : Set (sphere (0 : E) 1)) ∧
    ({v}ᶜ : Set (sphere (0 : E) 1)) ∪ {-v}ᶜ = Set.univ := by
  refine ⟨isOpen_compl_singleton, isOpen_compl_singleton, ?_⟩
  ext x
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases h : x = v
  · exact Or.inr (h ▸ sphere_pole_ne_neg v)
  · exact Or.inl h

theorem spherePole_contractible (v : sphere (0 : E) 1) :
    ContractibleSpace ({v}ᶜ : Set (sphere (0 : E) 1)) :=
  (spherePoleHomeomorph v).contractibleSpace

/-- Stereographic projection identifies the overlap of the two pole charts
with the punctured orthogonal hyperplane. -/
def spherePoleOverlapHomeomorph (v : sphere (0 : E) 1) :
    ↥(({v}ᶜ : Set (sphere (0 : E) 1)) ∩ {-v}ᶜ) ≃ₜ
      ({0}ᶜ : Set (ℝ ∙ (v : E))ᗮ) := by
  let e := spherePoleHomeomorph v
  let s : ({v}ᶜ : Set (sphere (0 : E) 1)) :=
    ⟨-v, by simpa using (sphere_pole_ne_neg v).symm⟩
  have hs : e s = 0 := stereographic_apply_neg v
  let e' : ({s}ᶜ : Set ({v}ᶜ : Set (sphere (0 : E) 1))) ≃ₜ
      ({0}ᶜ : Set (ℝ ∙ (v : E))ᗮ) := e.subtype (fun x => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        rw [← hs, e.injective.eq_iff])
  refine Homeomorph.trans ?_ e'
  exact
    { toFun := fun x => ⟨⟨x.val, x.property.1⟩, by
        intro h
        exact x.property.2 (congrArg Subtype.val h)⟩
      invFun := fun x => ⟨x.val.val, x.val.property, by
        intro h
        exact x.property (Subtype.ext h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

/-- The overlap of opposite pole charts is homotopy equivalent to the equator. -/
def spherePoleOverlapHomotopyEquiv (v : sphere (0 : E) 1) :
    ↥(({v}ᶜ : Set (sphere (0 : E) 1)) ∩ {-v}ᶜ) ≃ₕ
      sphere (0 : (ℝ ∙ (v : E))ᗮ) 1 :=
  (spherePoleOverlapHomeomorph v).toHomotopyEquiv.trans
    (puncturedVectorSphereHomotopyEquiv _)

end

section
open CategoryTheory Metric

section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Restriction of a real linear isometry equivalence to actual unit spheres. -/
def linearIsometrySphereHomeomorph {F : Type} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (e : E ≃ₗᵢ[ℝ] F) :
    sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1 :=
  e.toHomeomorph.subtype (fun x => by simp)

/-- The equator has the expected Euclidean dimension. -/
def sphereEquatorEuclideanHomeomorph (d : ℕ) [Fact (Module.finrank ℝ E = d+1)]
    (v : sphere (0 : E) 1) :
    sphere (0 : (ℝ ∙ (v : E))ᗮ) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
  linearIsometrySphereHomeomorph
    (OrthonormalBasis.fromOrthogonalSpanSingleton d
      (show (v : E) ≠ 0 by
        intro h
        have := norm_eq_of_mem_sphere v
        simp [h] at this)).repr

end

/-- Nonzero vectors transport under an actual continuous linear equivalence. -/
def continuousLinearEquivPuncturedHomeomorph {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) :
    ({0}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set F) :=
  e.toHomeomorph.subtype (fun x => by simp)

/-- In a real plane, the overlap of the two pole charts is the punctured real line. -/
def spherePlaneOverlapRealHomeomorph {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 1+1)]
    (v : sphere (0 : E) 1) :
    ↥(({v}ᶜ : Set (sphere (0 : E) 1)) ∩ {-v}ᶜ) ≃ₜ ({0}ᶜ : Set ℝ) :=
  (spherePoleOverlapHomeomorph v).trans (continuousLinearEquivPuncturedHomeomorph
    ((OrthonormalBasis.fromOrthogonalSpanSingleton 1
      (show (v : E) ≠ 0 by
        intro h
        have := norm_eq_of_mem_sphere v
        simp [h] at this)).repr.toContinuousLinearEquiv.trans
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ))))

/-- The signs lie in different path components of the actual punctured real line. -/
theorem puncturedReal_not_joined :
    ¬ Joined (⟨-1, by simp⟩ : ({0}ᶜ : Set ℝ)) ⟨1, by simp⟩ := by
  rintro ⟨p⟩
  have hc : Continuous (fun t => (p t : ℝ)) := continuous_subtype_val.comp p.continuous
  have hz : (0 : ℝ) ∈ Set.range (fun t => (p t : ℝ)) :=
    intermediate_value_univ 0 1 hc (by simp)
  obtain ⟨t, ht⟩ := hz
  exact (p t).property ht

/-- The punctured real line has exactly its negative and positive path components. -/
theorem puncturedReal_two_components (x : ({0}ᶜ : Set ℝ)) :
    Joined x (⟨-1, by simp⟩ : ({0}ᶜ : Set ℝ)) ∨ Joined x ⟨1, by simp⟩ := by
  have hx : (x : ℝ) ≠ 0 := x.property
  rcases lt_or_gt_of_ne hx with hx | hx
  · left
    have h := ((convex_Iio (0 : ℝ)).isPathConnected ⟨-1, by norm_num⟩).joinedIn
      (x : ℝ) hx (-1) (by norm_num)
    exact (h.mono (by intro y hy; exact ne_of_lt hy)).joined_subtype
  · right
    have h := ((convex_Ioi (0 : ℝ)).isPathConnected ⟨1, by norm_num⟩).joinedIn
      (x : ℝ) hx 1 (by norm_num)
    exact (h.mono (by intro y hy; exact ne_of_gt hy)).joined_subtype

/-- A fixed unit vector used to make the recursive sphere calculation a definition. -/
def euclideanSpherePole (n : ℕ) : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 :=
  ⟨Classical.choose ((NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin (n+1)))
      (x := 0) (r := 1)).mpr (by norm_num)),
    Classical.choose_spec ((NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin (n+1)))
      (x := 0) (r := 1)).mpr (by norm_num))⟩

end

section
open CategoryTheory Metric ContinuousMap

def continuousLinearEquivSphereHomotopyEquiv {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) :
    sphere (0 : E) 1 ≃ₕ sphere (0 : F) 1 :=
  (puncturedVectorSphereHomotopyEquiv E).symm.trans
    ((continuousLinearEquivPuncturedHomeomorph e).toHomotopyEquiv.trans
      (puncturedVectorSphereHomotopyEquiv F))

end

open CategoryTheory Limits Metric

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_ProjectiveLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Nonzero local classes and local homology of projective spaces and products. -/

section
open CategoryTheory
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- Real dimension of the actual complex graph-coordinate space. -/
theorem canonicalCoordinateSpace_real_finrank :
    Module.finrank ℝ ((Σ i, Fin (K i)) → ℂ) = 2 * (∑ i, K i) := by
  rw [finrank_real_of_complex]
  simp [Fintype.card_sigma, Nat.mul_comm]

end

section
open CategoryTheory Limits

section

/-- Punctured finite-dimensional real coordinate spaces of dimension at least
two are path connected, with their actual norm topology. -/
theorem puncturedVector_pathConnected_of_finrank (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hd : 2 ≤ Module.finrank ℝ E) : PathConnectedSpace ({0}ᶜ : Set E) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_compl_singleton_of_one_lt_rank
  rw [← Module.finrank_eq_rank]
  exact_mod_cast (show 1 < Module.finrank ℝ E by omega)

end

end

open CategoryTheory Limits

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_HyperplaneFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Hyperplane bundle charts, local-global comparison, and fiber normalization. -/

section
open Bundle Topology CategoryTheory Limits
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

def firstCoordinateSubspaceHomeomorph {B V : Type} [TopologicalSpace B]
    [TopologicalSpace V] (W : Set B) :
    ({z : B × V | z.1 ∈ W} : Set (B × V)) ≃ₜ W × V where
  toFun z := (⟨z.1.1,z.2⟩,z.1.2)
  invFun z := ⟨(z.1.1,z.2),z.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
    (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

end

open Bundle Topology CategoryTheory Limits

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_ProductCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Product-pair fiber normalization, punctured products, and overlap generators. -/

section
open Set
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite signed halfspace cover, using actual continuous linear coordinates. -/
def signedCoordinateHalfspace (i : Fin (Module.finrank ℝ E) × Bool) : Set E :=
  if i.2 then {x | 0 < (Module.finBasis ℝ E).equivFunL x i.1}
  else {x | (Module.finBasis ℝ E).equivFunL x i.1 < 0}

theorem signedCoordinateHalfspace_open (i : Fin (Module.finrank ℝ E) × Bool) :
    IsOpen (signedCoordinateHalfspace i) := by
  have hc := (continuous_apply i.1).comp (Module.finBasis ℝ E).equivFunL.continuous
  cases h : i.2 <;> simp only [signedCoordinateHalfspace, h, Bool.false_eq_true,
    ↓reduceIte] <;> first | exact isOpen_lt hc continuous_const | exact isOpen_lt continuous_const hc

theorem signedCoordinateHalfspace_convex (i : Fin (Module.finrank ℝ E) × Bool) :
    Convex ℝ (signedCoordinateHalfspace i) := by
  let l : E →ₗ[ℝ] ℝ := (LinearMap.proj i.1).comp
    (Module.finBasis ℝ E).equivFunL.toLinearMap
  cases h : i.2
  · simpa [signedCoordinateHalfspace, h, l, Set.preimage, Function.comp_def, Function.eval] using
      (convex_Iio (0 : ℝ)).linear_preimage l
  · simpa [signedCoordinateHalfspace, h, l, Set.preimage, Function.comp_def, Function.eval] using
      (convex_Ioi (0 : ℝ)).linear_preimage l

/-- The signed coordinate halfspaces cover exactly the punctured space. -/
theorem signedCoordinateHalfspaces_cover :
    (⋃ i : Fin (Module.finrank ℝ E) × Bool, signedCoordinateHalfspace i) = ({0}ᶜ : Set E) := by
  ext x
  simp only [mem_iUnion, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨i,b⟩,hi⟩ rfl
    cases b <;> simp [signedCoordinateHalfspace] at hi
  · intro hx
    have he : ∃ i, (Module.finBasis ℝ E).equivFunL x i ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hx
      apply (Module.finBasis ℝ E).equivFunL.injective
      ext i
      simpa using hn i
    obtain ⟨i,hi⟩ := he
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact ⟨(i,false), hi⟩
    · exact ⟨(i,true), hi⟩

end

open Bundle Topology CategoryTheory Limits

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_AffineAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Affine-avoidance covers and convex product-pair homology. -/

section
open Set
variable {E F J : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype J]

/-- A finite chart chooses a nonzero signed real coordinate for each image. -/
def affineAvoidanceChart (l : J → E →L[ℝ] F) (c : J → F)
    (s : J → Fin (Module.finrank ℝ F) × Bool) : Set E :=
  ⋂ j, (fun x => l j x + c j) ⁻¹' signedCoordinateHalfspace (s j)

theorem affineAvoidanceChart_open (l : J → E →L[ℝ] F) (c : J → F)
    (s : J → Fin (Module.finrank ℝ F) × Bool) : IsOpen (affineAvoidanceChart l c s) :=
  isOpen_iInter_of_finite (fun j => (signedCoordinateHalfspace_open (s j)).preimage ((l j).continuous.add continuous_const))

omit [Fintype J] in
theorem affineAvoidanceChart_convex (l : J → E →L[ℝ] F) (c : J → F)
    (s : J → Fin (Module.finrank ℝ F) × Bool) : Convex ℝ (affineAvoidanceChart l c s) :=
  convex_iInter (fun j => ((signedCoordinateHalfspace_convex (s j)).translate_preimage_left (c j)).linear_preimage (l j).toLinearMap)

end

open CategoryTheory Limits Set

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Twisted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Twisted hyperplane bundles, zeros, graph coordinates, and frame sections. -/

section
open Bundle Topology
namespace Kaplansky

theorem div_linearEquiv_inverse_one (L : ℂ ≃ₗ[ℂ] ℂ) (z : ℂ) :
    z / L.symm 1 = L z := by
  have hn : L.symm 1 ≠ 0 := fun hz => one_ne_zero (L.symm.map_eq_zero_iff.mp hz)
  apply (div_eq_iff hn).mpr
  have he := L.symm.map_smul (L z) (1 : ℂ)
  change L.symm (L z * 1) = L z * L.symm 1 at he
  simpa only [mul_one, L.symm_apply_apply] using he

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_Products
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded C-star products and the generated separable unital algebra. -/

noncomputable section
open scoped BigOperators
namespace Kaplansky
attribute [local instance 2000] CStarAlgebra.spectralOrder
attribute [local instance] CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

local instance (priority := 2000) closedSubalgebraLE (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] : LE S := (CStarAlgebra.spectralOrder S).toLE

local instance (priority := 2000) closedSubalgebraPreorder (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] : Preorder S := (CStarAlgebra.spectralOrder S).toPreorder

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.OrderedStates_RationalCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Rational cones and extension of positive states on ordered groups. -/

namespace Kaplansky

section
variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

/-- Positive fractions in the rational hull. A positive numerator may be
chosen after multiplying numerator and denominator; no unperforation of G
is assumed. -/
def orderedGroupRationalCone : PointedCone ℚ (DivisibleHull G) where
  carrier := {x | ∃ g : G, ∃ d : ℕ+, 0 ≤ g ∧ DivisibleHull.mk g d = x}
  zero_mem' := ⟨0,1,le_rfl,by simp⟩
  add_mem' := by
    rintro _ _ ⟨g,d,hg,rfl⟩ ⟨h,e,hh,rfl⟩
    exact ⟨e.val • g+d.val • h,d*e,
      add_nonneg (nsmul_nonneg hg _) (nsmul_nonneg hh _),DivisibleHull.mk_add_mk.symm⟩
  smul_mem' := by
    rintro ⟨q,hq⟩ _ ⟨g,d,hg,rfl⟩
    refine ⟨q.num • g,⟨q.den,q.den_pos⟩*d,?_,?_⟩
    · exact zsmul_nonneg hg (Rat.num_nonneg.mpr hq)
    · exact (DivisibleHull.qsmul_mk q g d).symm

theorem orderedGroupRationalCone_coe {g : G} (hg : 0 ≤ g) :
    (g : DivisibleHull G) ∈ orderedGroupRationalCone := ⟨g,1,hg,rfl⟩

/-- A unit with no nonpositive positive multiple stays outside the
negative of the rational cone, even if the group has torsion elsewhere. -/
theorem orderedGroupRationalCone_neg_unit (u : G)
    (hu : ∀ n : ℕ, 0 < n → ¬ n • u ≤ 0) :
    -(u : DivisibleHull G) ∉ orderedGroupRationalCone := by
  rintro ⟨g,d,hg,he⟩
  change DivisibleHull.mk g d = -DivisibleHull.mk u 1 at he
  rw [DivisibleHull.neg_mk] at he
  obtain ⟨k,hk⟩ := DivisibleHull.mk_eq_mk.mp he
  simp only [PNat.val_ofNat, one_nsmul, smul_neg, smul_smul] at hk
  have hp : 0 ≤ -((k.val*d.val) • u) := by
    rw [← hk]
    exact nsmul_nonneg hg _
  exact hu (k.val*d.val) (Nat.mul_pos k.pos d.pos) (neg_nonneg.mp hp)

theorem orderedGroupRationalCone_unit_ne_zero (u : G)
    (hu : ∀ n : ℕ, 0 < n → ¬ n • u ≤ 0) : (u : DivisibleHull G) ≠ 0 := by
  intro h
  apply orderedGroupRationalCone_neg_unit u hu
  rw [h, neg_zero]
  exact (orderedGroupRationalCone (G := G)).zero_mem

/-- Nonnegativity along the rational unit ray is reflected in its scalar. -/
theorem orderedGroupRationalCone_unit_scalar (u : G)
    (hu : ∀ n : ℕ, 0 < n → ¬ n • u ≤ 0) {q : ℚ}
    (hq : q • (u : DivisibleHull G) ∈ orderedGroupRationalCone) : 0 ≤ q := by
  by_contra h
  have hn : q < 0 := lt_of_not_ge h
  have hp : 0 < -q⁻¹ := neg_pos.mpr (inv_neg''.mpr hn)
  have hc := (orderedGroupRationalCone (G := G)).smul_mem hp.le hq
  rw [smul_smul, neg_mul, inv_mul_cancel₀ hn.ne, neg_one_smul] at hc
  exact orderedGroupRationalCone_neg_unit u hu hc

/-- An order unit in G dominates every rational fraction after passage
to the cone. The dominating vector is an integer multiple of the unit. -/
theorem orderedGroupRationalCone_cofinal (u : G) (hu : 0 ≤ u)
    (hb : ∀ g : G, ∃ N : ℕ, -(N • u) ≤ g) (x : DivisibleHull G) :
    ∃ N : ℕ, (N : ℚ) • (u : DivisibleHull G) + x ∈ orderedGroupRationalCone := by
  induction x using DivisibleHull.ind with | mk g d =>
  obtain ⟨N,hN⟩ := hb g
  refine ⟨N, ?_⟩
  have hunit : N • u ≤ d.val • (N • u) := by
    simpa only [one_nsmul] using
      nsmul_le_nsmul_left (nsmul_nonneg hu N) (Nat.one_le_iff_ne_zero.mpr d.ne_zero)
  have hnon : 0 ≤ d.val • (N • u)+g := by
    have h := (neg_le_neg hunit).trans hN
    simpa only [add_comm] using neg_le_iff_add_nonneg.mp h
  refine ⟨d.val • (N • u)+g,d,hnon,?_⟩
  rw [Nat.cast_smul_eq_nsmul ℚ N, DivisibleHull.coe, DivisibleHull.nsmul_mk,
    DivisibleHull.mk_add_mk]
  simp

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.OrderedStates_Semigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Catalytic orders, ordered group completion, and normalized semigroup states. -/

namespace Kaplansky

section
variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

/-- An order compression of successive multiples iterates without any
cancellation assumption. -/
theorem nsmul_compression_iterate (u : S) (m : ℕ)
    (h : (m+1) • u ≤ m • u) : ∀ k : ℕ, (m+k) • u ≤ m • u := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        (m+(k+1)) • u = (m+k) • u + u := by simp only [← Nat.add_assoc, add_nsmul, one_nsmul]
        _ ≤ m • u + u := add_le_add ih le_rfl
        _ = (m+1) • u := by simp only [add_nsmul, one_nsmul]
        _ ≤ m • u := h

/-- The ordered-semigroup arithmetic used in MR Theorem 2.3: if a larger
multiple of the unit is below a smaller one, some positive multiple is
properly infinite in the semigroup sense. No Cuntz correspondence is assumed. -/
theorem nsmul_compression_doubles (u : S) (hu : 0 ≤ u) {m n : ℕ}
    (hmn : m < n) (h : n • u ≤ m • u) :
    ∃ k : ℕ, 0 < k ∧ (2*k) • u ≤ k • u := by
  have hstep : (m+1) • u ≤ m • u :=
    (nsmul_le_nsmul_left hu (by omega)).trans h
  by_cases hm : m = 0
  · subst m
    have hu0 : u ≤ 0 := by simpa only [Nat.zero_add, one_nsmul, zero_nsmul] using hstep
    refine ⟨1,by omega,?_⟩
    simpa only [Nat.mul_one, two_nsmul, one_nsmul, add_zero] using add_le_add le_rfl hu0
  · refine ⟨m,by omega,?_⟩
    simpa [Nat.two_mul] using nsmul_compression_iterate u m hstep m

/-- Absence of a properly infinite positive multiple makes the ordinary
natural multiples of the unit order-reflecting. This is the first
semigroup step toward quasitrace existence, not that existence theorem. -/
theorem nsmul_unit_order_iff (u : S) (hu : 0 ≤ u)
    (hfinite : ∀ k : ℕ, 0 < k → ¬ (2*k) • u ≤ k • u) (m n : ℕ) :
    m • u ≤ n • u ↔ m ≤ n := by
  constructor
  · intro h
    by_contra hmn
    obtain ⟨k,hk,hk'⟩ := nsmul_compression_doubles u hu (by omega : n < m) h
    exact hfinite k hk hk'
  · exact nsmul_le_nsmul_left hu

end

section
variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

/-- A common summand can be retained while a comparison is iterated.
There is no cancellation assumption on the monoid. -/
theorem catalytic_nsmul_le {a b c : S} (h : a + c ≤ b + c) (k : ℕ) :
    k • a + c ≤ k • b + c := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (k+1) • a + c = a + (k • a + c) := by simp only [add_nsmul, one_nsmul]; ac_rfl
      _ ≤ a + (k • b + c) := add_le_add le_rfl ih
      _ = k • b + (a + c) := by ac_rfl
      _ ≤ k • b + (b + c) := add_le_add le_rfl h
      _ = (k+1) • b + c := by simp only [add_nsmul, one_nsmul, add_assoc]

/-- A bounded nonnegative common summand cannot hide a compression of
unit multiples when every positive multiple fails to be properly infinite. -/
theorem catalytic_unit_order_iff (u : S) (hu : 0 ≤ u)
    (hf : ∀ k : ℕ, 0 < k → ¬ (2*k) • u ≤ k • u)
    {c : S} (hc : 0 ≤ c) (hcu : ∃ N : ℕ, c ≤ N • u) (m n : ℕ) :
    m • u + c ≤ n • u + c ↔ m ≤ n := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := hcu
    have hi := catalytic_nsmul_le h (N+1)
    have hcomp : ((N+1)*m) • u ≤ ((N+1)*n+N) • u := by
      calc
        ((N+1)*m) • u ≤ ((N+1)*m) • u + c := le_add_of_nonneg_right hc
        _ ≤ ((N+1)*n) • u + c := by simpa only [← mul_nsmul, Nat.mul_comm] using hi
        _ ≤ ((N+1)*n) • u + N • u := add_le_add le_rfl hN
        _ = ((N+1)*n+N) • u := (add_nsmul _ _ _).symm
    have hn := (nsmul_unit_order_iff u hu hf _ _).mp hcomp
    by_contra hmn
    have hmn' : n+1 ≤ m := by omega
    have hmul := Nat.mul_le_mul_left (N+1) hmn'
    simp only [Nat.mul_add, Nat.mul_one] at hmul
    omega
  · intro h
    exact add_le_add (nsmul_le_nsmul_left hu h) le_rfl

/-- Stabilization by an arbitrary common summand preserves the natural
order on the unit if every element is nonnegative and bounded by a unit multiple. -/
theorem stabilized_unit_order_iff (u : S) (hu : 0 ≤ u)
    (hf : ∀ k : ℕ, 0 < k → ¬ (2*k) • u ≤ k • u)
    (hpos : ∀ c : S, 0 ≤ c) (hbound : ∀ c : S, ∃ N : ℕ, c ≤ N • u)
    (m n : ℕ) :
    (∃ c : S, m • u + c ≤ n • u + c) ↔ m ≤ n := by
  constructor
  · rintro ⟨c, hc⟩
    exact (catalytic_unit_order_iff u hu hf (hpos c) (hbound c) m n).mp hc
  · intro h
    exact ⟨0, by simpa using nsmul_le_nsmul_left hu h⟩

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Quasitrace_Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner-compatible two-quasitraces on the usual CStarMatrix algebra and the fixed-pair counterexample proposition. -/

section

noncomputable section
open scoped BigOperators
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A n : Type*} [CStarAlgebra A] [Fintype n] [DecidableEq n]

def diagonal (a : n → A) : CStarMatrix n n A := CStarMatrix.ofMatrix (Matrix.diagonal a)

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Quasitrace_Extension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix order and the normalization of genuine corner extensions. -/

section

noncomputable section
open scoped ComplexOrder BigOperators CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A n : Type*} [CStarAlgebra A] [Fintype n] [DecidableEq n]

omit [Fintype n] in
@[simp] theorem diagonal_add (a b : n → A) :
    diagonal (a+b) = diagonal a + diagonal b := by
  change Matrix.diagonal (a+b) = Matrix.diagonal a + Matrix.diagonal b
  exact (Matrix.diagonal_add a b).symm
omit [Fintype n] in
@[simp] theorem diagonal_sub (a b : n → A) :
    diagonal (a-b) = diagonal a - diagonal b := by
  change Matrix.diagonal (a-b) = Matrix.diagonal a - Matrix.diagonal b
  exact (Matrix.diagonal_sub a b).symm
omit [Fintype n] in
@[simp] theorem diagonal_one : diagonal (fun _ : n => (1 : A)) = 1 := by
  change Matrix.diagonal (fun _ : n => (1 : A)) = 1
  rfl

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Quasitrace_Defect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed positive contraction pair and its uniform real additivity defect. -/

section

noncomputable section
open scoped BigOperators ComplexOrder CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

def partialSum (f : ℕ → A) (i : ℕ) : A := ∑ j ∈ Finset.range i, f j
@[simp] theorem partialSum_zero (f : ℕ → A) : partialSum f 0 = 0 := by simp [partialSum]

def leftSquare (x : ℕ → A) (i : ℕ) : A := star (x i) * x i
def rightSquare (x : ℕ → A) (i : ℕ) : A := x i * star (x i)

def defectAEntries (x : ℕ → A) (N : ℕ) : Fin N ⊕ Fin N → A :=
  Sum.elim (fun i => partialSum (leftSquare x) i.val)
    (fun i => 1 - partialSum (rightSquare x) i.val)
def defectBEntries (x : ℕ → A) (N : ℕ) : Fin N ⊕ Fin N → A :=
  Sum.elim (fun i => leftSquare x i.val) (fun i => 1 - rightSquare x i.val)
def defectA (x : ℕ → A) (N : ℕ) := diagonal (defectAEntries x N)
def defectB (x : ℕ → A) (N : ℕ) := diagonal (defectBEntries x N)

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Quasitrace_Infiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Proper infiniteness, isometry columns, and C-star matrix amplification. -/

open scoped ComplexOrder CStarAlgebra BigOperators
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

variable {m : ℕ}

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable (A) (m n : Type*) [Fintype m] [Fintype n]

/-- Flatten the two genuine C*-matrix levels into one product-indexed
matrix algebra, preserving multiplication, star, and complex scalars. -/
def cstarMatrixFlatten : CStarMatrix m m (CStarMatrix n n A) ≃⋆ₐ[ℂ]
    CStarMatrix (m × n) (m × n) A where
  toFun X := CStarMatrix.ofMatrix (fun i j => X i.1 j.1 i.2 j.2)
  invFun X := CStarMatrix.ofMatrix (fun i j => CStarMatrix.ofMatrix (fun a b => X (i,a) (j,b)))
  left_inv X := rfl
  right_inv X := rfl
  map_add' X Y := rfl
  map_smul' c X := rfl
  map_star' X := rfl
  map_mul' X Y := by
    ext i j
    simp only [CStarMatrix.mul_apply,
      Fintype.sum_prod_type]
    calc
      _ = ∑ k : m, (X i.1 k * Y k j.1) i.2 j.2 :=
        Matrix.sum_apply i.2 j.2 Finset.univ (fun k => (show Matrix n n A from X i.1 k * Y k j.1))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rfl

end Kaplansky

end

end OAI
end


