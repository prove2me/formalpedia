-- Prove2me | Definitions.Def_OAIQ032L009
-- name    : OAIQ032L009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:44:41.54608+00:00
-- url     : https://prove2.me/theorems/8d967bd6-0b98-410a-9d52-f8e2ff9efbed
-- title:
--   Definitions bundle OAIQ032L009 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 34 declarations of OpenAI's Lean: 19 definitions, 4 instances and 11 theorems. The definitions and types are `OAI.Lech.ReesRoot.indexFinite`, `OAI.Lech.TensorPushout.aux`, `OAI.Lech.TensorPushout.instAlgebraTensorProduct_solutions`, `OAI.Lech.TensorTransport.reindex`, `OAI.Lech.TensorTwist.scalarEquiv`, `OAI.Lech.cokernelIsoOfShortExact`, `OAI.Lech.complementaryRetractEquiv`, `OAI.Lech.complexRankSum`, `OAI.Lech.discreteShortComplex`, `OAI.Lech.elementaryBackward`, `OAI.Lech.elementaryProjector`, `OAI.Lech.elementaryProjectorNull`, `OAI.Lech.precompLinear`, `OAI.Lech.quotientExtensionEquiv`, `OAI.Lech.quotientResidueEquiv`, `OAI.Lech.restrictionHomologyIso`, `OAI.Lech.sumPolynomial`, `OAI.Lech.tensorScalarExtensionObjIso`, `OAI.Lech.zeroHomologyCokernelIso`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_ContractibleRetract`, `Multiplicity_CyclicDutta`, `Multiplicity_ElementaryContractibleProjector`, `Multiplicity_FrobeniusComplexStage`, `Multiplicity_LechCokernelComp`, `Multiplicity_LechMapCochain`, `Multiplicity_MinimalComplexReduction`, `Multiplicity_NormalizedLengthTrivialRelation`, `Multiplicity_QuotientExtension`, `Multiplicity_QuotientShort`, `Multiplicity_RootFibreCech`, `Multiplicity_ScalarExtensionComplexCompare`, `Multiplicity_ScalarExtensionHomotopy`, `Multiplicity_ScalarHomologyError`, `Multiplicity_SeparableOrderNormalizedLength`, `Multiplicity_TensorCoefficientFibre`, `Multiplicity_TensorPushout`, `Multiplicity_TensorRingTwist`, `Multiplicity_TotalGhostRowHom`, `Multiplicity_ZeroHomologyScalarExtension`.
--
--   **Imports.** It imports the published bundle `Def_DuttaDomain`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L017` and `OAIQ032L018`; the statement `OAI.Lech.nonminimal_complex_reduction`; the proofs of `OAI.Lech.CharP.dutta_lower_bound_infinite_perfect`, `OAI.Lech.MinimalReduction.exists_minimal_reduction`, `OAI.Lech.MinimalReduction.shifted_colength_limit`, `OAI.Lech.Normalization.parameter_frobenius_multiplicity_enn`, `OAI.Lech.Normalization.parameter_multiplicity_pos`, `OAI.Lech.Primary.multiplicity_nonneg`, `OAI.Lech.PrimeFiltration.Factors.multiplicity_self` and `OAI.Lech.nonminimal_complex_reduction`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_DuttaDomain

section
-- module Solutions.OAIQ032_LECH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechCokernelComp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]



noncomputable def cokernelIsoOfShortExact {S : ShortComplex C} (hS : S.ShortExact) :
    cokernel S.f ≅ S.X₃ :=
  (cokernelIsCokernel S.f).coconePointUniqueUpToIso hS.gIsCokernel

end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TotalGhostRowHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra


namespace Lech
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

def precompLinear {M N P : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) : (N →ₗ[R] P) →ₗ[R] (M →ₗ[R] P) where
  toFun g := g.comp f
  map_add' g h := by ext; rfl
  map_smul' r g := by ext; rfl

end Lech
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechMapCochain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex


namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
  {J : Type w} [Category J]

variable {ι : Type w}
 
def discreteShortComplex (S : ι → ShortComplex C) : ShortComplex (Discrete ι ⥤ C) where
  X₁ := Discrete.functor (fun i => (S i).X₁)
  X₂ := Discrete.functor (fun i => (S i).X₂)
  X₃ := Discrete.functor (fun i => (S i).X₃)
  f := Discrete.natTrans (fun i => (S i.as).f)
  g := Discrete.natTrans (fun i => (S i.as).g)
  zero := by ext i; exact (S i.as).zero

end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NormalizedLengthTrivialRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum

open TensorProduct


namespace Lech.TensorTransport
variable {A B P M : Type*} [CommRing A] [CommRing B] [CommRing P]
  [Algebra A B] [Algebra B P] [Algebra A P] [IsScalarTower A B P]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

 

def reindex (h : Function.Surjective (algebraMap A B)) :
    P ⊗[A] M ≃ₗ[P] P ⊗[B] M := by
  let : TensorProduct.CompatibleSMul A B P M :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective P M h
  exact TensorProduct.equivOfCompatibleSMul B A P P M

end Lech.TensorTransport


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorPushout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open TensorProduct
namespace Lech.TensorPushout
variable (A P E N : Type*) [CommRing A] [CommRing P] [CommRing E]
  [Algebra A P] [Algebra A E] [AddCommGroup N]
  [Module A N] [Module E N] [IsScalarTower A E N]

local instance instAlgebraTensorProduct_solutions : Algebra E (P ⊗[A] E) := Algebra.TensorProduct.rightAlgebra

def aux : (P ⊗[A] E) ⊗[E] N ≃ₗ[A] P ⊗[A] N :=
  ((TensorProduct.congr (Algebra.TensorProduct.commRight A E P).symm.toLinearEquiv
    (LinearEquiv.refl E N)).restrictScalars A).trans
  (((AlgebraTensorModule.rightComm E A E E P N).restrictScalars A).trans
    ((TensorProduct.congr ((TensorProduct.lid E N).restrictScalars A)
      (LinearEquiv.refl A P)).trans (TensorProduct.comm A N P)))

lemma aux_tmul (p : P) (e : E) (n : N) :
    aux A P E N ((p ⊗ₜ[A] e) ⊗ₜ[E] n) = p ⊗ₜ[A] (e • n) := rfl

end Lech.TensorPushout

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SeparableOrderNormalizedLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech
open Polynomial Filter
open scoped BigOperators

noncomputable def sumPolynomial (p : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ p.support, Polynomial.C (p.coeff j / (j + 1 : ℚ)) *
    (Polynomial.bernoulli (j + 1) - Polynomial.C (_root_.bernoulli (j + 1)))

end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorRingTwist
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ChangeOfRings
namespace Lech.TensorTwist
open CategoryTheory
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
universe u
variable {D C C' : Type u} [CommRing D] [CommRing C] [CommRing C']

def scalarEquiv (f : D →+* C) (e : C ≃+* C') :
    (ModuleCat.restrictScalars f).obj (ModuleCat.of C C) ≃ₗ[D]
      (ModuleCat.restrictScalars ((e : C →+* C').comp f)).obj (ModuleCat.of C' C') where
  __ := e.toAddEquiv
  map_smul' d c := by
    exact e.map_mul (f d) c

end Lech.TensorTwist

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_QuotientExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace Lech
universe u
variable {D C : Type u} [CommRing D] [CommRing C]

def quotientExtensionEquiv (f : D →+* C) (I : Ideal D) :
    (ModuleCat.extendScalars f).obj (ModuleCat.of D (D ⧸ I)) ≃ₗ[C] C ⧸ I.map f := by
  letI : Algebra D C := f.toAlgebra
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I).symm.toLinearEquiv

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ContractibleRetract
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R]


def complementaryRetractEquiv
    {F G K : ModuleCat.{u} R} (i : G ⟶ F) (r : F ⟶ G) (a : K ⟶ F) (b : F ⟶ K)
    (hir : i ≫ r = 𝟙 G) (hab : a ≫ b = 𝟙 K)
    (hs : r ≫ i + b ≫ a = 𝟙 F) (hib : i ≫ b = 0) (har : a ≫ r = 0) :
    F ≃ₗ[R] (G × K) :=
  LinearEquiv.ofLinearMap (r.hom.prod b.hom) (i.hom.coprod a.hom)
    (by
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · have h1 := congrArg (fun f : G ⟶ G => f x.1) hir
        have h2 := congrArg (fun f : K ⟶ G => f x.2) har
        simpa using congrArg₂ (·+·) h1 h2
      · have h1 := congrArg (fun f : G ⟶ K => f x.1) hib
        have h2 := congrArg (fun f : K ⟶ K => f x.2) hab
        simpa using congrArg₂ (·+·) h1 h2)
    (by apply LinearMap.ext; intro x; exact congrArg (fun f : F ⟶ F => f x) hs)
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarExtensionHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped TensorProduct ChangeOfRings
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

lemma extendScalars_map_smul (φ : R →+* S) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (x : R) :
    (ModuleCat.extendScalars φ).map (x • f) =
      φ x • (ModuleCat.extendScalars φ).map f := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  let := φ.toAlgebra
  change (1:S) ⊗ₜ[R] (x • f m) = φ x • ((1:S) ⊗ₜ[R] (f m))
  rw [TensorProduct.tmul_smul]
  rfl

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarHomologyError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped Pointwise
namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma scalar_range_eq (M : Type u) [AddCommGroup M] [Module R M] (g : R) :
    (LinearMap.lsmul R M g).range = Ideal.span {g} • (⊤ : Submodule R M) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  simp only [LinearMap.mem_range,LinearMap.lsmul_apply,
    Submodule.mem_smul_pointwise_iff_exists,Submodule.mem_top,true_and]

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusComplexStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ENNReal

namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
def restrictionHomologyIso (f : R →+* S)
    (F : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    (((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj F).homology i ≅
      (ModuleCat.restrictScalars f).obj (F.homology i) :=
  (F.sc i).mapHomologyIso (ModuleCat.restrictScalars f)

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ZeroHomologyScalarExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def zeroHomologyCokernelIso (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hzero : F.d 0 1 = 0) : F.homology 0 ≅ cokernel (F.d (-1) 0) :=
  F.homologyIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫
    (F.sc' (-1) 0 1).asIsoHomologyι hzero ≪≫ (F.sc' (-1) 0 1).opcyclesIsoCokernel

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarExtensionComplexCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

def tensorScalarExtensionObjIso (M : ModuleCat.{u} R) :
    ModuleCat.of R (M ⊗[R] S) ≅
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj M) := by
  let N := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let c : S ≃ₗ[R] N :=
    { __ := (AddEquiv.refl S)
      map_smul' r x := Algebra.smul_def r x }
  letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun r x => rfl)
  let e : N ⊗[R] M ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj M) :=
    { __ := (AddEquiv.refl (N ⊗[R] M))
      map_smul' r x := by
        change N ⊗[R] M at x
        change r • x = algebraMap R S r • x
        exact (IsScalarTower.algebraMap_smul S r x).symm }
  exact ((TensorProduct.comm R M S).trans
    ((TensorProduct.congr c (LinearEquiv.refl R M)).trans e)).toModuleIso

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ElementaryContractibleProjector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex HomComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R]
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
variable (t : F.X (i+1) ⟶ F.X i)

def elementaryBackward (a b : ℤ) (h : (ComplexShape.up ℤ).Rel b a) : F.X a ⟶ F.X b :=
  (Cochain.single t (-1)).v a b (by change b+1=a at h; omega)

def elementaryProjector : F ⟶ F := Homotopy.nullHomotopicMap' (elementaryBackward F i t)

def elementaryProjectorNull : Homotopy (elementaryProjector F i t) 0 :=
  Homotopy.nullHomotopy' (elementaryBackward F i t)

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_MinimalComplexReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

def complexRankSum (F : CochainComplex (ModuleCat.{u} R) ℤ) : ℕ :=
  ∑ j ∈ Finset.range (dimension R+1),Module.finrank R (F.X (-(j:ℤ)))

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorCoefficientFibre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open scoped TensorProduct
universe u
variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
  (I : Ideal R) (q : A →ₗ[A] M) (hq : Function.Surjective q)
  (hker : (q.restrictScalars R).ker = I • (⊤ : Submodule R A))
  (V : Type u) [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]

lemma map_ideal_smul_top {N P : Type u}
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (e : N ≃ₗ[R] P) :
    Submodule.map e.toLinearMap (I • (⊤ : Submodule R N)) = I • (⊤ : Submodule R P) := by
  rw [Submodule.map_smul'',Submodule.map_top,LinearMap.range_eq_top.mpr e.surjective]



end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootFibreCech
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra
local instance indexFinite (s : Finset (Fin (n+1))) : Fintype (PLift s.Nonempty) := Fintype.ofFinite _

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_QuotientShort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex IsLocalRing
open scoped TensorProduct
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
local instance quotient_local (P : Ideal R) [P.IsPrime] : IsLocalRing (R ⧸ P) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
local instance quotient_localHom (P : Ideal R) [P.IsPrime] : IsLocalHom (Ideal.Quotient.mk P) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

omit [IsNoetherianRing R] in
lemma quotient_residue_surjective [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] :
    Function.Surjective (algebraMap (ResidueField R) (ResidueField (R ⧸ P))) := by
  intro x
  obtain ⟨a,rfl⟩ := residue_surjective x
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨residue R b,rfl⟩

def quotientResidueEquiv (P : Ideal R) [P.IsPrime] :
    ResidueField R ≃+* ResidueField (R ⧸ P) :=
  RingEquiv.ofBijective (algebraMap _ _)
    ⟨RingHom.injective _,quotient_residue_surjective P⟩

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CyclicDutta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing
open scoped Topology TensorProduct
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
attribute [local instance] quotient_local quotient_localHom
local instance duttaQuotientCharP (p : ℕ) [Fact p.Prime] [CharP R p]
    (P : Ideal R) [P.IsPrime] : CharP (R ⧸ P) p :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    have h := congrArg (Ideal.Quotient.mk P) (CharP.cast_eq_zero R p)
    simpa only [map_natCast,map_zero] using h)
end Lech

end

end OAI
end


