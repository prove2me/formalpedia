-- Prove2me | Definitions.Def_OAIQ15Sf004
-- name    : OAIQ15Sf004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:21:24.080542+00:00
-- url     : https://prove2.me/theorems/ba894af9-3527-42a3-9e9f-a4b0904667db
-- title:
--   Definitions bundle OAIQ15Sf004 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 145 declarations of OpenAI's Lean: 58 definitions, 2 inductive types or structures, 10 instances and 75 theorems. The definitions and types are `OAI.Kaplansky.complexLineCoordinateUnit`, `OAI.Kaplansky.contractibleProductProjection`, `OAI.Kaplansky.coordinateFunctional`, `OAI.Kaplansky.firstCoordinateSubspaceHomeomorph`, `OAI.Kaplansky.groupingByLabel`, `OAI.Kaplansky.intersectionSubtypeSwap`, `OAI.Kaplansky.kernelShortComplex`, `OAI.Kaplansky.kernelShortComplexInclusion`, `OAI.Kaplansky.labelFiberProdEquiv`, `OAI.Kaplansky.labelFiberSigmaEquiv`, `OAI.Kaplansky.lineFrameEquiv`, `OAI.Kaplansky.orderedGroupRationalCone`, `OAI.Kaplansky.productSubspaceHomeomorph`, `OAI.Kaplansky.properIsometryColumns`, `OAI.Kaplansky.quotientShortComplex`, `OAI.Kaplansky.quotientShortComplexProjection`, `OAI.Kaplansky.quotientSnakeInput`, `OAI.Kaplansky.suffixReverseEquiv`, `OAI.Kaplansky.tensorLineCore`, `OAI.Kaplansky.tensorLinePair`, `OAI.KaplanskyConsequences.ClosedStarIdeal.Quotient`, `OAI.KaplanskyConsequences.ClosedStarIdeal.comap`, `OAI.KaplanskyConsequences.ClosedStarIdeal.mkStarAlgHom`, `OAI.KaplanskyConsequences.ClosedStarIdeal.quotientMap`, `OAI.KaplanskyConsequences.ClosedStarIdeal.ringCon`, `OAI.KaplanskyConsequences.ClosedStarIdeal.submodule`, `OAI.KaplanskyConsequences.DenseUnits`, `OAI.KaplanskyConsequences.IsPartialIsometry`, `OAI.KaplanskyConsequences.Mat`, `OAI.KaplanskyConsequences.PolarScalar.cut`, `OAI.KaplanskyConsequences.PolarScalar.invCut`, `OAI.KaplanskyConsequences.QuasiValue`, `OAI.KaplanskyConsequences.QuasiValue.FaithfulQuotient`, `OAI.KaplanskyConsequences.QuasiValue.IsNull`, `OAI.KaplanskyConsequences.QuasiValue.StarTerm`, `OAI.KaplanskyConsequences.QuasiValue.StarTerm.eval`, `OAI.KaplanskyConsequences.QuasiValue.nullIdeal`, `OAI.KaplanskyConsequences.QuasiValue.polarCut`, `OAI.KaplanskyConsequences.QuasiValue.q`, `OAI.KaplanskyConsequences.QuasiValue.quotQ` and 20 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: `BundleTests_Retained`, `ComplexBundle_Hyperplane`, `ComplexBundle_Tensor`, `IntegralHomology_HyperplaneFiber`, `IntegralHomology_MayerVietoris`, `IntegralHomology_Product`, `IntegralHomology_ProjectiveLocal`, `IntegralHomology_Quotient`, `Kaplansky_Quotient_ClosedStarQuotient`, `Kaplansky_Quotient_MaximalClosedIdeal`, `Kaplansky_Quotient_NullIdeal`, `Kaplansky_Regular_FreeFamily`, `Kaplansky_Regular_FreeNormal`, `Kaplansky_Regular_FreeWord`, `Kaplansky_Regular_ReducedPolynomials`, `Kaplansky_Regular_ReducedTrace`, `Kaplansky_Regular_RegularOperators`, `Kaplansky_Ultrapower_ApproxPolar`, `Kaplansky_Ultrapower_Construction`, `Kaplansky_Ultrapower_DenseUnits`, `Kaplansky_Ultrapower_PartialIsometry`, `Kaplansky_Ultrapower_PolarScalar`, `Kaplansky_Ultrapower_QuasiFinite`, `Kaplansky_Ultrapower_QuasiNull`, `Kaplansky_Ultrapower_QuasiValue`, `Kaplansky_Ultrapower_Quotient`, `Kaplansky_Ultrapower_UltraSaturation`, `OrderedStates_RationalCone`, `Quasitrace_Infiniteness`.
--
--   **Imports.** It imports the published bundle `Def_KaplanskyStableFiniteness`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ15Sf008` and `OAIQ15Sf009`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness

section
-- module Solutions.OAIQ15_Sf.BundleTests_Retained
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Retained bundle labels, positive multiplicities, regrouping, and complement rank. -/

section
open scoped BigOperators
namespace Kaplansky

def labelFiberProdEquiv {A B C : Type*} (f : B → C) (c : C) :
    {p : A×B // f p.2=c} ≃ A×{b : B // f b=c} where
  toFun p := (p.1.1,⟨p.1.2,p.2⟩)
  invFun p := ⟨(p.1,p.2.1),p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def labelFiberSigmaEquiv {J C : Type*} {A : J → Type*} (f : ∀ j, A j → C) (c : C) :
    {p : Σ j, A j // f p.1 p.2=c} ≃ Σ j, {a : A j // f j a=c} where
  toFun p := ⟨p.1.1,⟨p.1.2,p.2⟩⟩
  invFun p := ⟨⟨p.1,p.2.1⟩,p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem labelFiberProd_card {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    (f : B → C) (c : C) :
    Fintype.card {p : A×B // f p.2=c} = Fintype.card A * Fintype.card {b : B // f b=c} := by
  rw [Fintype.card_congr (labelFiberProdEquiv (A := A) f c),Fintype.card_prod]

theorem labelFiberSigma_card {J C : Type*} [Fintype J] [DecidableEq C] {A : J → Type*} [∀ j, Fintype (A j)]
    (f : ∀ j, A j → C) (c : C) :
    Fintype.card {p : Σ j, A j // f p.1 p.2=c} = ∑ j, Fintype.card {a : A j // f j a=c} := by
  rw [Fintype.card_congr (labelFiberSigmaEquiv f c),Fintype.card_sigma]

theorem constantLabelFiber_card {A C : Type*} [Fintype A] [DecidableEq C] (c d : C) :
    Fintype.card (Subtype (fun _ : A => c=d)) = if c=d then Fintype.card A else 0 := by
  by_cases h : c=d <;> simp [h]

end Kaplansky

end

section
open scoped BigOperators
namespace Kaplansky

def suffixReverseEquiv {R : ℕ} (i : Fin R) :
    {j : Fin (R+1) // i.val<j.val} ≃ Fin (R-i.val) where
  toFun j := ⟨R-j.1.val,by have h := j.2; have h' := j.1.isLt; omega⟩
  invFun t := ⟨⟨R-t.val,by omega⟩,by change i.val<R-t.val; omega⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    dsimp
    have h := j.1.isLt
    omega
  right_inv t := by
    apply Fin.ext
    dsimp
    omega

end Kaplansky

end

section
open Bundle Topology
open scoped BigOperators
namespace Kaplansky

def groupingByLabel {S I : Type*} (label : S → I) :
    S ≃ Σ i, {s : S // label s=i} where
  toFun s := ⟨label s,⟨s,rfl⟩⟩
  invFun p := p.2.1
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨i,s,h⟩ := p
    subst i
    rfl

end Kaplansky

end

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Hyperplane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Hyperplane sections, dual evaluation, graph coordinates, and their zero. -/

section
open Bundle Topology
open scoped InnerProductSpace
namespace Kaplansky
variable {d : ℕ}

def coordinateFunctional (i : Fin d) : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ℂ :=
  (LinearMap.proj i).comp (EuclideanSpace.equiv (Fin d) ℂ).toLinearEquiv.toLinearMap

@[simp] theorem coordinateFunctional_apply (i : Fin d) (v : EuclideanSpace ℂ (Fin d)) :
    coordinateFunctional i v=v i := rfl

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Tensor
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

section

theorem complexLineMap_scalar (L : ℂ →L[ℂ] ℂ) (z : ℂ) : L z = z * L 1 := by
  have h := L.map_smul z (1 : ℂ)
  simpa using h

variable {B J K : Type*} [TopologicalSpace B]
  (C : VectorBundleCore ℂ B ℂ J) (D : VectorBundleCore ℂ B ℂ K)

/-- Tensor product of two actual line cores. Its transition functions
are the products of the two line transition functions. -/
def tensorLineCore : VectorBundleCore ℂ B ℂ (J × K) where
  baseSet i := C.baseSet i.1 ∩ D.baseSet i.2
  isOpen_baseSet i := (C.isOpen_baseSet i.1).inter (D.isOpen_baseSet i.2)
  indexAt x := (C.indexAt x,D.indexAt x)
  mem_baseSet_at x := ⟨C.mem_baseSet_at x,D.mem_baseSet_at x⟩
  coordChange i j x := (C.coordChange i.1 j.1 x 1 * D.coordChange i.2 j.2 x 1) •
    ContinuousLinearMap.id ℂ ℂ
  coordChange_self i x hx z := by
    rw [C.coordChange_self i.1 x hx.1, D.coordChange_self i.2 x hx.2]
    simp
  continuousOn_coordChange i j := by
    have hc := ((C.continuousOn_coordChange i.1 j.1).mono
      (fun x (hx : x ∈ (C.baseSet i.1 ∩ D.baseSet i.2) ∩ (C.baseSet j.1 ∩ D.baseSet j.2)) =>
        ⟨hx.1.1,hx.2.1⟩)).clm_apply (continuousOn_const (c := (1 : ℂ)))
    have hd := ((D.continuousOn_coordChange i.2 j.2).mono
      (fun x (hx : x ∈ (C.baseSet i.1 ∩ D.baseSet i.2) ∩ (C.baseSet j.1 ∩ D.baseSet j.2)) =>
        ⟨hx.1.2,hx.2.2⟩)).clm_apply (continuousOn_const (c := (1 : ℂ)))
    exact (hc.mul hd).smul continuousOn_const
  coordChange_comp i j k x hx z := by
    have hc := C.coordChange_comp i.1 j.1 k.1 x
      ⟨⟨hx.1.1.1,hx.1.2.1⟩,hx.2.1⟩ (1 : ℂ)
    have hd := D.coordChange_comp i.2 j.2 k.2 x
      ⟨⟨hx.1.1.2,hx.1.2.2⟩,hx.2.2⟩ (1 : ℂ)
    rw [complexLineMap_scalar] at hc hd
    change (C.coordChange j.1 k.1 x 1 * D.coordChange j.2 k.2 x 1) *
        ((C.coordChange i.1 j.1 x 1 * D.coordChange i.2 j.2 x 1) * z) =
      (C.coordChange i.1 k.1 x 1 * D.coordChange i.2 k.2 x 1) * z
    rw [← hc, ← hd]
    ring

/-- Multiplication in core fibers is the tensor pairing. This formula
is compatible with every tensor-product chart. -/
def tensorLinePair (x : B) (v : C.Fiber x) (w : D.Fiber x) : (tensorLineCore C D).Fiber x :=
  (show ℂ from v) * (show ℂ from w)

theorem tensorLinePair_chart (i : J × K) (x : B) (v : C.Fiber x) (w : D.Fiber x) :
    ((tensorLineCore C D).localTriv i ⟨x,tensorLinePair C D x v w⟩).2 =
      (C.localTriv i.1 ⟨x,v⟩).2 * (D.localTriv i.2 ⟨x,w⟩).2 := by
  change ℂ at v w
  change (C.coordChange (C.indexAt x) i.1 x 1 * D.coordChange (D.indexAt x) i.2 x 1) *
    ((show ℂ from v) * (show ℂ from w)) =
    C.coordChange (C.indexAt x) i.1 x v * D.coordChange (D.indexAt x) i.2 x w
  rw [complexLineMap_scalar (C.coordChange (C.indexAt x) i.1 x) v,
    complexLineMap_scalar (D.coordChange (D.indexAt x) i.2 x) w]
  ring

/-- Products of continuous sections are continuous in the tensor
bundle topology; the chart compatibility, not fiberwise continuity alone,
establishes the statement. -/
theorem continuous_tensorLinePair_section (s : ∀ x, C.Fiber x) (t : ∀ x, D.Fiber x)
    (hs : Continuous (fun x => TotalSpace.mk' ℂ x (s x)))
    (ht : Continuous (fun x => TotalSpace.mk' ℂ x (t x))) :
    Continuous (fun x => TotalSpace.mk' ℂ x (tensorLinePair C D x (s x) (t x))) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [FiberBundle.continuousAt_section]
  have hc := (FiberBundle.continuousAt_section ℂ x).mp hs.continuousAt
  have hd := (FiberBundle.continuousAt_section ℂ x).mp ht.continuousAt
  apply (hc.mul hd).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y =>
    tensorLinePair_chart C D ((C.indexAt x),(D.indexAt x)) y (s y) (t y))

theorem tensorLinePair_ne_zero (x : B) (v : C.Fiber x) (w : D.Fiber x)
    (hv : v ≠ 0) (hw : w ≠ 0) : tensorLinePair C D x v w ≠ 0 := by
  change (show ℂ from v) * (show ℂ from w) ≠ 0
  exact mul_ne_zero hv hw

end

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

theorem lineFrameEquiv_chart (b : B) (z : C.Fiber b) (i : J) (hi : b ∈ C.baseSet i) :
    lineFrameEquiv C u hu b z =
      (C.localTriv i ⟨b,z⟩).2 / (C.localTriv i ⟨b,u b⟩).2 := by
  have hc : C.coordChange (C.indexAt b) i b 1 ≠ 0 := by
    intro hz
    have he := C.coordChange_comp (C.indexAt b) i (C.indexAt b) b
      ⟨⟨C.mem_baseSet_at b,hi⟩,C.mem_baseSet_at b⟩ 1
    rw [hz, map_zero, C.coordChange_self _ _ (C.mem_baseSet_at b)] at he
    exact zero_ne_one he
  change (show ℂ from z) / (show ℂ from u b) =
    C.coordChange (C.indexAt b) i b z / C.coordChange (C.indexAt b) i b (u b)
  rw [complexLineMap_scalar (C.coordChange (C.indexAt b) i b) z,
    complexLineMap_scalar (C.coordChange (C.indexAt b) i b) (u b)]
  exact (mul_div_mul_right _ _ hc).symm

end Kaplansky

end

open Bundle Topology
open scoped InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Quotient
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

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_MayerVietoris
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
-- module Solutions.OAIQ15_Sf.IntegralHomology_Product
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

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_ProjectiveLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Nonzero local classes and local homology of projective spaces and products. -/

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
-- module Solutions.OAIQ15_Sf.IntegralHomology_HyperplaneFiber
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
-- module Solutions.OAIQ15_Sf.Quasitrace_Infiniteness
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

def properIsometryColumns (s t : CStarMatrix (Fin m) (Fin m) A) :
    CStarMatrix (Fin m) (Fin (m+m)) A :=
  CStarMatrix.ofMatrix (fun row col =>
    Matrix.fromCols (CStarMatrix.ofMatrix.symm s) (CStarMatrix.ofMatrix.symm t) row
      ((finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m+m)).symm col))

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.OrderedStates_RationalCone
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

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Quotient_ClosedStarQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace KaplanskyConsequences
open scoped ComplexOrder
open Metric Topology
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

namespace ClosedStarIdeal
variable {A : Type*} [CStarAlgebra A] (I : ClosedStarIdeal A)

abbrev submodule : Submodule ℂ A := I.toNonUnitalStarSubalgebra.toSubmodule
instance instIsClosedCoeSubmoduleComplexSubmodule : IsClosed (I.submodule : Set A) := I.closed
instance instIsClosedCoeNonUnitalStarSubalgebraComplex : IsClosed (I.toNonUnitalStarSubalgebra : Set A) := I.closed

def ringCon : RingCon A where
  toSetoid := I.submodule.quotientRel
  add' := by
    intro a b c d hab hcd
    rw [Submodule.quotientRel_def] at *
    simpa only [add_sub_add_comm] using I.submodule.add_mem hab hcd
  mul' := by
    intro a b c d hab hcd
    rw [Submodule.quotientRel_def] at *
    have h := I.submodule.add_mem (I.mul_mem_right (a-b) c hab) (I.mul_mem_left b (c-d) hcd)
    convert h using 1; noncomm_ring

abbrev Quotient := A ⧸ I.submodule

instance instRingQuotient : Ring I.Quotient := inferInstanceAs (Ring I.ringCon.Quotient)

def quotientMap : A →+* I.Quotient := I.ringCon.mk'

@[simp] lemma mk_apply (a : A) : I.quotientMap a = I.submodule.mkQ a := rfl
lemma mk_surjective : Function.Surjective I.quotientMap := RingCon.mk'_surjective I.ringCon
@[simp] lemma mk_eq_zero (a : A) : I.quotientMap a = 0 ↔ a ∈ I.submodule :=
  Submodule.Quotient.mk_eq_zero I.submodule

instance instAlgebraComplexQuotient : Algebra ℂ I.Quotient := Algebra.ofModule
  (fun r x y => by
    induction x using Submodule.Quotient.induction_on with | H a =>
      induction y using Submodule.Quotient.induction_on with | H b =>
        exact congrArg (Submodule.Quotient.mk (p := I.submodule)) (smul_mul_assoc r a b))
  (fun r x y => by
    induction x using Submodule.Quotient.induction_on with | H a =>
      induction y using Submodule.Quotient.induction_on with | H b =>
        exact congrArg (Submodule.Quotient.mk (p := I.submodule)) (mul_smul_comm r a b))

instance instStarQuotient : Star I.Quotient where
  star := Quotient.map' star fun a b h => by
    rw [Submodule.quotientRel_def] at *
    change star a - star b ∈ I.toNonUnitalStarSubalgebra
    rw [← star_sub]
    exact I.toNonUnitalStarSubalgebra.star_mem' h

@[simp] lemma mk_star (a : A) : I.quotientMap (star a) = star (I.quotientMap a) := rfl

instance instStarRingQuotient : StarRing I.Quotient where
  star_involutive := by
    intro x; obtain ⟨a, rfl⟩ := I.mk_surjective x
    exact congrArg I.quotientMap (star_star a)
  star_mul := by
    intro x y; obtain ⟨a, rfl⟩ := I.mk_surjective x; obtain ⟨b, rfl⟩ := I.mk_surjective y
    change I.quotientMap (star (a*b)) = I.quotientMap (star b * star a)
    rw [star_mul]
  star_add := by
    intro x y; obtain ⟨a, rfl⟩ := I.mk_surjective x; obtain ⟨b, rfl⟩ := I.mk_surjective y
    change I.quotientMap (star (a+b)) = I.quotientMap (star a + star b)
    rw [star_add]

instance instStarModuleComplexQuotient : StarModule ℂ I.Quotient where
  star_smul := by
    intro r x; obtain ⟨a, rfl⟩ := I.mk_surjective x
    exact congrArg I.quotientMap (star_smul r a)

def mkStarAlgHom : A →⋆ₐ[ℂ] I.Quotient where
  __ := I.quotientMap
  commutes' r := by
    change I.quotientMap (algebraMap ℂ A r) = I.quotientMap (r • (1 : A))
    rw [Algebra.algebraMap_eq_smul_one]
  map_star' := I.mk_star

lemma norm_mk_le (a : A) : ‖I.quotientMap a‖ ≤ ‖a‖ := Submodule.Quotient.norm_mk_le I.submodule a

lemma norm_mk_lt (x : I.Quotient) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, I.quotientMap a = x ∧ ‖a‖ < ‖x‖ + ε := Submodule.Quotient.norm_mk_lt x hε

instance instNormedRingQuotient : NormedRing I.Quotient where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε => by
    have := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, Metric.mem_ball, and_imp, Prod.forall, Prod.exists] at this
    rcases this with ⟨ε₁, ε₂, ⟨h₁, h₂⟩, h⟩
    obtain ⟨a, rfl, ha⟩ := I.norm_mk_lt x h₁
    obtain ⟨b, rfl, hb⟩ := I.norm_mk_lt y h₂
    simp only [Real.dist_eq, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [I.norm_mk_le a]⟩
      ⟨by linarith, by linarith [I.norm_mk_le b]⟩
    calc
      _ = ‖I.quotientMap (a*b)‖ := by rw [map_mul]
      _ ≤ ‖a‖ * ‖b‖ := (I.norm_mk_le (a*b)).trans (norm_mul_le a b)
      _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le

instance instNormedAlgebraComplexQuotient : NormedAlgebra ℂ I.Quotient :=
  { Submodule.Quotient.normedSpace I.submodule ℂ, (inferInstance : Algebra ℂ I.Quotient) with }

instance instNormedStarGroupQuotient : NormedStarGroup I.Quotient where
  norm_star_le x := le_of_forall_pos_le_add fun ε hε => by
    obtain ⟨a, rfl, ha⟩ := I.norm_mk_lt x hε
    calc
      ‖star (I.quotientMap a)‖ = ‖I.quotientMap (star a)‖ := rfl
      _ ≤ ‖star a‖ := I.norm_mk_le (star a)
      _ = ‖a‖ := norm_star a
      _ ≤ _ := ha.le

end ClosedStarIdeal
end KaplanskyConsequences
end
end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Quotient_MaximalClosedIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences
open Topology
open scoped CStarAlgebra
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

namespace ClosedStarIdeal

def comap (I : ClosedStarIdeal B) (f : A →⋆ₐ[ℂ] B) : ClosedStarIdeal A where
  __ := I.toNonUnitalStarSubalgebra.comap f.toNonUnitalStarAlgHom
  mul_mem_left := by
    intro a b hb
    change f (a*b) ∈ I.toNonUnitalStarSubalgebra
    rw [map_mul]
    exact I.mul_mem_left _ _ hb
  mul_mem_right := by
    intro a b ha
    change f (a*b) ∈ I.toNonUnitalStarSubalgebra
    rw [map_mul]
    exact I.mul_mem_right _ _ ha
  closed := by
    change IsClosed (f ⁻¹' (I.toNonUnitalStarSubalgebra : Set B))
    exact I.closed.preimage (map_continuous f)

end ClosedStarIdeal

end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Quotient_NullIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


namespace KaplanskyConsequences
open scoped Matrix CStarAlgebra ComplexOrder
open Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
abbrev Mat (A : Type*) (n : ℕ) := CStarMatrix (Fin n) (Fin n) A

local instance matRealCFC (n : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ (Mat A n) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance matNonnegSpectrum (n : ℕ) : NonnegSpectrumClass ℝ (Mat A n) :=
  CStarAlgebra.instNonnegSpectrumClass

namespace SpectralKernel

lemma mat_sum_apply {m n ι : Type*} (s : Finset ι) (f : ι → CStarMatrix m n A)
    (i : m) (j : n) : (∑ k ∈ s, f k) i j = ∑ k ∈ s, f k i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert, ha, ih]

lemma gram_nonneg {m n : Type*} [Fintype m] [Fintype n] (x : Matrix m n A) :
    0 ≤ CStarMatrix.ofMatrix (x.conjTranspose*x) := by
  classical
  by_cases hn : Nonempty n
  · let i₀ : n := Classical.choice hn
    let y (k : m) : CStarMatrix n n A := CStarMatrix.ofMatrix fun i j => if i = i₀ then x k j else 0
    have he : CStarMatrix.ofMatrix (x.conjTranspose*x) = ∑ k, star (y k)*y k := by
      ext i j
      simp only [CStarMatrix.ofMatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        mat_sum_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply]
      apply Finset.sum_congr rfl
      intro k hk
      change star (x k i) * x k j =
        ∑ l, star (if l = i₀ then x k i else 0) * (if l = i₀ then x k j else 0)
      simp
    rw [he]
    exact Finset.sum_nonneg fun k _ => star_mul_self_nonneg _
  · have : IsEmpty n := not_nonempty_iff.mp hn
    have he : CStarMatrix.ofMatrix (x.conjTranspose*x) = 0 := by ext i; exact isEmptyElim i
    rw [he]

end SpectralKernel
end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_FreeFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular



abbrev FZ := FreeGroup ℤ

def shift : FZ ≃* FZ := FreeGroup.freeGroupCongr (Equiv.addRight 1)

def action : F2 →* Equiv.Perm FZ :=
  FreeGroup.lift (fun i => if i = 0 then shift.toEquiv else Equiv.mulLeft (FreeGroup.of 0))

def a : F2 := FreeGroup.of 0
def b : F2 := FreeGroup.of 1

def freeGen : ℕ → F2
  | 0 => b
  | n+1 => a * freeGen n * a⁻¹

@[simp] lemma action_a : action a = shift.toEquiv := by simp [action,a]
@[simp] lemma action_b : action b = Equiv.mulLeft (FreeGroup.of 0) := by simp [action,b]
@[simp] lemma shift_of (n : ℤ) : shift (FreeGroup.of n) = FreeGroup.of (n+1) := by
  simp [shift,FreeGroup.freeGroupCongr]

def coordinate (w : F2) : FZ := action w 1

def Prefix (i : ℤ) (sign : Bool) (w : FZ) : Prop :=
  ∃ t, w.toWord = (i,sign)::t


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_FreeNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

attribute [local instance] Classical.decEq Classical.propDecidable

def translate (n : ℤ) : FZ ≃* FZ := FreeGroup.freeGroupCongr (Equiv.addRight n)
@[simp] lemma translate_of (n i : ℤ) : translate n (FreeGroup.of i) = FreeGroup.of (i+n) := by
  simp [translate,FreeGroup.freeGroupCongr]

def height : F2 →* Multiplicative ℤ := FreeGroup.lift (fun i => Multiplicative.ofAdd (if i=0 then 1 else 0))
def exponent (w : F2) : ℤ := (height w).toAdd
@[simp] lemma exponent_one : exponent 1 = 0 := by simp [exponent]
@[simp] lemma exponent_mul (w v : F2) : exponent (w*v) = exponent w + exponent v := by simp [exponent]
@[simp] lemma exponent_inv (w : F2) : exponent w⁻¹ = -exponent w := by simp [exponent]
@[simp] lemma exponent_a : exponent a = 1 := by simp [exponent,height,a]
@[simp] lemma exponent_b : exponent b = 0 := by simp [exponent,height,b]
@[simp] lemma coordinate_one : coordinate 1 = 1 := by simp [coordinate]
@[simp] lemma coordinate_a : coordinate a = 1 := by simp [coordinate]
@[simp] lemma coordinate_b : coordinate b = FreeGroup.of 0 := by simp [coordinate]
@[simp] lemma coordinate_a_inv : coordinate a⁻¹ = 1 := by simp [coordinate]
@[simp] lemma coordinate_b_inv : coordinate b⁻¹ = (FreeGroup.of 0)⁻¹ := by simp [coordinate]

def genZ (n : ℤ) : F2 := a^n*b*a^(-n)
def kernelMap : FZ →* F2 := FreeGroup.lift genZ
@[simp] lemma kernelMap_of (n : ℤ) : kernelMap (FreeGroup.of n) = genZ n := by simp [kernelMap]


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_FreeWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

attribute [local instance] Classical.decEq Classical.propDecidable

def Starts (n : ℤ) (v : FZ) : Prop := ∃ s, Prefix n s v


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_ReducedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped InnerProductSpace ComplexOrder BigOperators ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2200] Complex.partialOrder
variable {G : Type*}

def delta (g : G) : HilbertSum G ℂ := lp.single 2 g 1
@[simp] lemma delta_apply (g h : G) : delta g h = if h=g then 1 else 0 := by
  simp [delta,lp.single_apply,Pi.single_apply]
@[simp] lemma inner_delta (g : G) (x : HilbertSum G ℂ) : inner ℂ (delta g) x = x g := by
  simp [delta,lp.inner_single_left,RCLike.inner_apply]

@[simp] lemma inner_delta_right (g : G) (x : HilbertSum G ℂ) : inner ℂ x (delta g) = star (x g) := by
  simp [delta,lp.inner_single_right,RCLike.inner_apply]

variable [Group G]

def right (g : G) : HilbertSum G ℂ →L[ℂ] HilbertSum G ℂ :=
  (reindex (Equiv.mulRight g⁻¹)).toLinearIsometry.toContinuousLinearMap
@[simp] lemma right_apply (g h : G) (x : HilbertSum G ℂ) : right g x h = x (h*g) := by
  simp [right,reindex_apply]
lemma right_star (g : G) : star (right g) = right g⁻¹ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  simpa [right_apply,mul_assoc] using
    ((Equiv.mulRight g).tsum_eq (fun i => inner ℂ (x (i*g⁻¹)) (y i))).symm

lemma left_commute_right (g h : G) : Commute (left g) (right h) := by
  apply ContinuousLinearMap.ext; intro x; ext k
  simp [mul_assoc]

lemma algebra_commute_right (T : Algebra G) (g : G) : Commute T.val (right g) := by
  have hs : Algebra G ≤ StarSubalgebra.centralizer ℂ (Set.range (right (G:=G))) := by
    apply StarSubalgebra.topologicalClosure_minimal
    · apply StarAlgebra.adjoin_le
      rintro _ ⟨h,rfl⟩
      change left h ∈ StarSubalgebra.centralizer ℂ (Set.range (right (G:=G)))
      rw [StarSubalgebra.mem_centralizer_iff ℂ]
      rintro _ ⟨k,rfl⟩
      exact ⟨(left_commute_right h k).eq.symm, by rw [right_star]; exact (left_commute_right h k⁻¹).eq.symm⟩
    · exact Set.isClosed_centralizer _
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp (hs T.property)) _ ⟨g,rfl⟩).1.symm

lemma right_delta (g : G) : right g (delta 1) = delta g⁻¹ := by
  ext k
  simp only [right_apply,delta_apply]
  simp only [mul_eq_one_iff_eq_inv]

lemma algebra_delta (T : Algebra G) (g h : G) :
    T.val (delta g) h = T.val (delta 1) (h*g⁻¹) := by
  have he : delta g = right g⁻¹ (delta 1) := by simp [right_delta]
  rw [he]
  have hc := congrArg (fun S : HilbertSum G ℂ →L[ℂ] HilbertSum G ℂ => S (delta 1) h)
    (algebra_commute_right T g⁻¹).eq
  simpa only [mul_apply_eq_comp,right_apply] using hc

lemma algebra_star_delta (T : Algebra G) (g : G) :
    (star T).val (delta 1) g = star (T.val (delta 1) g⁻¹) := by
  rw [← inner_delta]
  change inner ℂ (delta g) (T.val.adjoint (delta 1)) = _
  rw [ContinuousLinearMap.adjoint_inner_right,inner_delta_right,algebra_delta,one_mul]


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_ReducedPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G]
abbrev Op (G : Type*) [Group G] := HilbertSum G ℂ →L[ℂ] HilbertSum G ℂ


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_RegularOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
variable {G H : Type*} [Group G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Group G] [CompleteSpace H] in
@[simp] lemma diagonal_apply (T : H →L[ℂ] H) (x : HilbertSum G H) (g : G) :
    diagonal T x g = T (x g) := rfl
omit [Group G] [CompleteSpace H] in
@[simp] lemma diagonal_one : diagonal (G:=G) (1 : H →L[ℂ] H) = 1 := by ext; rfl
omit [Group G] [CompleteSpace H] in
@[simp] lemma diagonal_mul (T S : H →L[ℂ] H) : diagonal (G:=G) (T*S) = diagonal T * diagonal S := by
  ext; rfl
omit [Group G] in
@[simp] lemma diagonal_star (T : H →L[ℂ] H) : diagonal (G:=G) (star T) = star (diagonal T) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr; intro g
  exact T.adjoint_inner_left _ _

def mask (P : G → Prop) [DecidablePred P] : HilbertSum G H →L[ℂ] HilbertSum G H :=
  lp.mapCLM 2 (fun g => if P g then 1 else 0) (by norm_num : (0:ℝ) ≤ 1)
    (fun g => by
      split_ifs
      · exact ContinuousLinearMap.norm_id_le
      · simp)
omit [Group G] [CompleteSpace H] in
@[simp] lemma mask_apply (P : G → Prop) [DecidablePred P] (x : HilbertSum G H) (g : G) :
    mask P x g = if P g then x g else 0 := by
  change (if P g then (1 : H →L[ℂ] H) else 0) (x g) = _
  split_ifs <;> rfl
omit [Group G] in
@[simp] lemma mask_star (P : G → Prop) [DecidablePred P] : star (mask (H:=H) P) = mask P := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr; intro g
  simp only [mask_apply]; split_ifs <;> simp
omit [Group G] [CompleteSpace H] in
@[simp] lemma mask_sq (P : G → Prop) [DecidablePred P] : mask (H:=H) P * mask P = mask P := by
  ext x g
  simp only [mul_apply_eq_comp,mask_apply]
  split_ifs <;> simp


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_PolarScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.PolarScalar


def invCut (r t : ℝ) : ℝ := (Real.sqrt (max t r))⁻¹
def cut (r t : ℝ) : ℝ := t / max t r


end KaplanskyConsequences.PolarScalar

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_QuasiValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences
open scoped ComplexOrder
open Kaplansky SpectralKernel
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

structure QuasiValue (A : Type*) [CStarAlgebra A] where
  val : A → ℝ
  zero : val 0=0
  one : val 1=1
  nonneg : ∀ ⦃a⦄, 0≤a → 0≤val a
  mono : ∀ ⦃a b⦄, 0≤a → a≤b → val a≤val b
  smul : ∀ (r:ℝ) a, val (r • a)=r*val a
  bound : ∀ a, |val a|≤‖a‖
  lipschitz_positive : ∀ ⦃a b⦄, 0≤a → 0≤b → |val a-val b|≤‖a-b‖
  square_swap : ∀ x, val (x*star x)=val (star x*x)
  weighted_add : ∀ ⦃a b⦄, 0≤a → 0≤b → ∀ (r:ℝ), r≠0 →
    val (a+b)≤(1+r^2)*val a+(1+r⁻¹^2)*val b
  add_commute : ∀ ⦃a b⦄, IsSelfAdjoint a → IsSelfAdjoint b → Commute a b →
    val (a+b)=val a+val b

namespace QuasiValue
variable {A : Type*} [CStarAlgebra A]

variable (V : QuasiValue A)
def q (x : A) : ℝ := V.val (star x*x)

@[simp] lemma q_zero : V.q 0=0 := by simp only [q,star_zero,zero_mul,V.zero]
@[simp] lemma q_star (x : A) : V.q (star x)=V.q x := by
  simp only [q,star_star,V.square_swap]

end QuasiValue
end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_ApproxPolar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
open PolarScalar
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

def polarCut (x : A) (r : ℝ) : A := x * cfc (invCut r) (star x*x)
def spectralCut (x : A) (r : ℝ) : A := cfc (cut r) (star x*x)


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_Construction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder ENNReal
open Filter Topology
open Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

lemma ultra_tendsto {ι : Type*} (u : Ultrafilter ι) (f : ι → ℝ) (C : ℝ)
    (h : ∀ i, |f i|≤C) : Tendsto f u (𝓝 (limUnder u f)) := by
  have hm : ((u.map f : Ultrafilter ℝ) : Filter ℝ) ≤ 𝓟 (Set.Icc (-C) C) := by
    apply le_principal_iff.mpr
    change ∀ᶠ i in (u : Filter ι), f i ∈ Set.Icc (-C) C
    exact Filter.Eventually.of_forall (fun i => abs_le.mp (h i))
  obtain ⟨x,_,hx⟩ := isCompact_Icc.ultrafilter_le_nhds (u.map f) hm
  exact tendsto_nhds_limUnder ⟨x,hx⟩


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_DenseUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def DenseUnits (A : Type*) [Monoid A] [TopologicalSpace A] : Prop := Dense {a : A | IsUnit a}


end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_PartialIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

def IsPartialIsometry (v : A) : Prop := v*star v*v=v

end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_QuasiNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] (V : QuasiValue A)

lemma val_add_of_zero {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hzero : V.val b = 0) : V.val (a+b) = V.val a := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hpos : 0 < V.val a+1 := by linarith [V.nonneg ha]
    let r := Real.sqrt (ε/(V.val a+1))
    have hr : 0 < r := Real.sqrt_pos.2 (div_pos hε hpos)
    have hrsq : r^2 = ε/(V.val a+1) := Real.sq_sqrt (le_of_lt (div_pos hε hpos))
    have hmul : r^2*(V.val a+1)=ε := by rw [hrsq]; exact div_mul_cancel₀ ε hpos.ne'
    have h := V.weighted_add ha hb r hr.ne'
    rw [hzero,mul_zero,add_zero] at h
    nlinarith [sq_nonneg r]
  · exact V.mono ha (le_add_of_nonneg_right hb)

abbrev IsNull (x : A) : Prop := V.val (star x*x) = 0

lemma null_zero  : IsNull V (0 : A) := by simp [IsNull,V.zero]

lemma null_star {x : A} (hx : IsNull V x) : IsNull V (star x) := by
  simpa only [IsNull,star_star,V.square_swap] using hx

lemma null_add {x y : A} (hx : IsNull V x) (hy : IsNull V y) :
    IsNull V (x+y) := by
  have hab : V.val (star x*x + star y*y) = 0 := by
    rw [val_add_of_zero V (star_mul_self_nonneg x) (star_mul_self_nonneg y) hy]
    exact hx
  have hle : star (x+y)*(x+y) ≤ (2 : ℝ) • (star x*x + star y*y) := by
    rw [← sub_nonneg]
    convert star_mul_self_nonneg (x-y) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [two_smul,star_sub,star_add]
    noncomm_ring
  apply le_antisymm _ (V.nonneg (star_mul_self_nonneg _))
  calc V.val (star (x+y)*(x+y)) ≤ V.val ((2:ℝ) • (star x*x + star y*y)) :=
        V.mono (star_mul_self_nonneg _) hle
    _ = 0 := by rw [V.smul,hab,mul_zero]

lemma null_smul {x : A} (hx : IsNull V x) (r : ℂ) :
    IsNull V (r • x) := by
  have h : star (r • x)*(r • x) = Complex.normSq r • (star x*x) := by
    rw [star_smul,smul_mul_assoc,mul_smul_comm,smul_smul]
    change ((starRingEnd ℂ) r * r) • (star x*x) = Complex.normSq r • (star x*x)
    rw [← Complex.normSq_eq_conj_mul_self]
    exact Complex.coe_smul _ _
  dsimp [IsNull]
  rw [h,V.smul,hx,mul_zero]

lemma null_mul_left {x : A} (hx : IsNull V x) (a : A) :
    IsNull V (a*x) := by
  have hle : star (a*x)*(a*x) ≤ ‖a‖^2 • (star x*x) := by
    have h := star_left_conjugate_le_conjugate
      (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := a)) x
    simpa only [star_mul,mul_assoc,Algebra.algebraMap_eq_smul_one,mul_smul_comm,
      smul_mul_assoc,one_mul] using h
  apply le_antisymm _ (V.nonneg (star_mul_self_nonneg _))
  calc V.val (star (a*x)*(a*x)) ≤ V.val (‖a‖^2 • (star x*x)) :=
        V.mono (star_mul_self_nonneg _) hle
    _ = 0 := by rw [V.smul,hx,mul_zero]

lemma null_mul_right {x : A} (hx : IsNull V x) (a : A) :
    IsNull V (x*a) := by
  simpa only [star_mul,star_star] using null_star V (null_mul_left V (null_star V hx) (star a))

lemma continuous_squareVal : Continuous (fun x : A => V.val (star x*x)) := by
  have hl : LipschitzWith 1 (fun x : {a : A // 0≤a} => V.val x) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [NNReal.coe_one,one_mul,Real.dist_eq,Subtype.dist_eq,dist_eq_norm,Real.norm_eq_abs] using
      V.lipschitz_positive a.property b.property
  have hc : Continuous (fun x : A => (⟨star x*x,star_mul_self_nonneg x⟩ : {a:A // 0≤a})) :=
    (continuous_star.mul continuous_id).subtype_mk _
  exact hl.continuous.comp hc

def nullIdeal  : ClosedStarIdeal (A) where
  carrier := {x | IsNull V x}
  zero_mem' := null_zero V
  add_mem' := null_add V
  smul_mem' := fun r _ hx => null_smul V hx r
  mul_mem' := fun _ hy => null_mul_left V hy _
  star_mem' := null_star V
  mul_mem_left := fun a _ hx => null_mul_left V hx a
  mul_mem_right := fun _ a hx => null_mul_right V hx a
  closed := isClosed_eq (continuous_squareVal V) continuous_const

lemma val_zero_of_null {a : A} (ha : 0 ≤ a) (hx : IsNull V a) :
    V.val a = 0 := by
  have hs : CFC.sqrt a ∈ (nullIdeal V).toNonUnitalStarSubalgebra := by
    rw [CFC.sqrt_eq_real_sqrt a ha]
    exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt hx
  change IsNull V (CFC.sqrt a) at hs
  simpa only [IsNull,(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self a ha] using hs

lemma null_posPart {a : A} (hx : IsNull V a) : IsNull V a⁺ := by
  change a⁺ ∈ (nullIdeal V).toNonUnitalStarSubalgebra
  exact cfcₙ_mem (𝕜' := ℂ) (fun t : ℝ => max t 0) hx

lemma val_eq_of_null_sub {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : IsNull V (a-b)) : V.val a = V.val b := by
  have haux {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : IsNull V (a-b)) :
      V.val a ≤ V.val b := by
    have hle : a ≤ b+(a-b)⁺ := by
      have hp := CFC.le_posPart (ha.isSelfAdjoint.sub hb.isSelfAdjoint)
      exact (sub_le_iff_le_add'.1 hp)
    calc V.val a ≤ V.val (b+(a-b)⁺) := V.mono ha hle
      _ = V.val b := val_add_of_zero V hb (CFC.posPart_nonneg _)
        (val_zero_of_null V (CFC.posPart_nonneg _) (null_posPart V hab))
  exact le_antisymm (haux ha hb hab) (haux hb ha (by
    have h := (nullIdeal V).submodule.neg_mem hab
    change IsNull V (-(a-b)) at h
    simpa only [neg_sub] using h))


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_QuasiFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] (V : QuasiValue A)

abbrev FaithfulQuotient := V.nullIdeal.Quotient
abbrev quotientHom : A →⋆ₐ[ℂ] V.FaithfulQuotient := V.nullIdeal.mkStarAlgHom


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_Quotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] (V : QuasiValue A)

lemma q_eq_of_null_sub {a b : A} (h : V.IsNull (a-b)) : V.q a=V.q b := by
  apply V.val_eq_of_null_sub (star_mul_self_nonneg _) (star_mul_self_nonneg _)
  have h₁ := V.null_mul_left h (star a)
  have h₂ := V.null_mul_right (V.null_star h) b
  convert V.null_add h₁ h₂ using 1
  all_goals try with_reducible_and_instances rfl
  simp only [star_sub]
  noncomm_ring

def quotQ : V.FaithfulQuotient → ℝ := Quotient.lift (s := V.nullIdeal.submodule.quotientRel) V.q (fun a b h =>
  V.q_eq_of_null_sub (by exact (Submodule.quotientRel_def V.nullIdeal.submodule).mp h))

@[simp] lemma quotQ_map (a : A) : V.quotQ (V.quotientHom a)=V.q a := rfl

@[simp] lemma quotQ_zero : V.quotQ 0=0 := V.q_zero
@[simp] lemma quotQ_one : V.quotQ 1=1 := by change V.val (star 1*1)=1; simpa using V.one

@[simp] lemma quotQ_star (x : V.FaithfulQuotient) : V.quotQ (star x)=V.quotQ x := by
  obtain ⟨a,rfl⟩ := V.nullIdeal.mk_surjective x
  exact V.q_star a


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_UltraSaturation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue
open Filter Topology
open scoped ComplexOrder ENNReal

inductive StarTerm (C : Type*) where
  | var : StarTerm C
  | const : C → StarTerm C
  | add : StarTerm C → StarTerm C → StarTerm C
  | mul : StarTerm C → StarTerm C → StarTerm C
  | neg : StarTerm C → StarTerm C
  | star : StarTerm C → StarTerm C
namespace StarTerm
variable {C D E : Type*}
def eval [Add D] [Mul D] [Neg D] [Star D] (c : C → D) (x : D) : StarTerm C → D
  | .var => x
  | .const a => c a
  | .add p q => eval c x p+eval c x q
  | .mul p q => eval c x p*eval c x q
  | .neg p => -eval c x p
  | .star p => Star.star (eval c x p)
end StarTerm

end KaplanskyConsequences.QuasiValue

end

end OAI
end


