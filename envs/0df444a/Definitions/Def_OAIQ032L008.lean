-- Prove2me | Definitions.Def_OAIQ032L008
-- name    : OAIQ032L008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:44:29.043749+00:00
-- url     : https://prove2.me/theorems/c6098328-4db3-41b6-a942-6147461ee53e
-- title:
--   Definitions bundle OAIQ032L008 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 81 declarations of OpenAI's Lean: 30 definitions, 1 inductive type or structure, 9 instances and 41 theorems. The definitions and types are `OAI.Lech.ReesRoot.nonemptyFinite`, `OAI.Lech.ResidueCompletion.coefficient`, `OAI.Lech.ResidueExtension`, `OAI.Lech.ResidueGenerators.coefficient`, `OAI.Lech.ResidueGenerators.map`, `OAI.Lech.ResidueTensor.fiberEquiv`, `OAI.Lech.RestrictedPolynomialCech.grade`, `OAI.Lech.RootTower.exponentQuotient`, `OAI.Lech.RootTower.exponentRemainder`, `OAI.Lech.RootTower.extract`, `OAI.Lech.RootTower.perfectOf`, `OAI.Lech.RootTower.remainderExponent`, `OAI.Lech.SeparableOrder.order`, `OAI.Lech.SeparableOrder.toField`, `OAI.Lech.SignedCech.twistIndex`, `OAI.Lech.SignedFraction.fraction`, `OAI.Lech.SignedFraction.multiply`, `OAI.Lech.SignedFraction.order`, `OAI.Lech.SignedFraction.piece`, `OAI.Lech.TensorGenerator.baseGenerators`, `OAI.Lech.TensorIdeal.imageLift`, `OAI.Lech.TensorIdeal.kernelSquareEquiv`, `OAI.Lech.TensorIdeal.tensorBasisEquiv`, `OAI.Lech.TensorIdeal.tensorHomologyBasisIso`, `OAI.Lech.TensorIdeal.tensorHomologyIso`, `OAI.Lech.TensorIdeal.unitMap`, `OAI.Lech.TensorTotal.Right.degreeSequenceFamily`, `OAI.Lech.TensorTotal.functor`, `OAI.Lech.TotalGhost.towerPath`, `OAI.Lech.baseChangeFunctor`, `OAI.Lech.cochainOfMap`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_AlgebraicResidueTensor`, `Multiplicity_BicomplexImageLift`, `Multiplicity_CechCartierZRange`, `Multiplicity_CompleteResidueExtension`, `Multiplicity_FibreSquare`, `Multiplicity_FiniteFreeTensorCohomology`, `Multiplicity_FrobeniusIntermediatePowerMap`, `Multiplicity_GradedChartCochains`, `Multiplicity_LechCokernelComp`, `Multiplicity_LechLevel`, `Multiplicity_LechMapCochain`, `Multiplicity_ReesRegular`, `Multiplicity_ReesRootLayerCech`, `Multiplicity_ResidueExtension`, `Multiplicity_RootTowerLengthEq`, `Multiplicity_RootTowerRemainderExponent`, `Multiplicity_RootTowerRootWeight`, `Multiplicity_RootUlrichNaturality`, `Multiplicity_SignedCechBicRow`, `Multiplicity_SourceGradedCechHomology`, `Multiplicity_TensorGeneratorBound`, `Multiplicity_TotalGhostRowHom`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L015`, `OAIQ032L016`, `OAIQ032L017` and `OAIQ032L018`; the statements `OAI.Lech.FilteredCech.positive_homology_powerTorsion`, `OAI.Lech.SourceGraded.acyclicity_finite_torsion`, `OAI.Lech.SourceGraded.exists_uniform_geometric_stableImage` and `OAI.Lech.complex_estimate_allModule`; the proofs of `OAI.Lech.SeparableOrder.frobenius_homology_tendsto_zero`, `OAI.Lech.TensorGenerator.length_le`, `OAI.Lech.TensorGenerator.scalar_cokernel_le` and `OAI.Lech.exists_frobenius_tensor_transfer`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AlgebraicResidueTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open IsLocalRing TensorProduct
namespace Lech.ResidueTensor
variable (k R K : Type*) [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
  [Field K] [Algebra k K]
  (hres : Function.Bijective (algebraMap k (ResidueField R)))

 
def fiberEquiv : ((R ⊗[k] K) ⧸ ((maximalIdeal R).map (algebraMap R (R ⊗[k] K)))) ≃ₐ[k] K :=
  (Algebra.TensorProduct.quotientTensorEquiv (R:=k) k K R (maximalIdeal R)).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.ofBijective (Algebra.ofId k (ResidueField R)) hres).symm
      (AlgEquiv.refl : K ≃ₐ[k] K)).trans (Algebra.TensorProduct.lid k K))

@[simp] lemma fiberEquiv_includeRight (b : K) :
    fiberEquiv k R K hres (Ideal.Quotient.mk _
      (Algebra.TensorProduct.includeRight (R:=k) (A:=R) b))=b := by
  change ((AlgEquiv.ofBijective (Algebra.ofId k (ResidueField R)) hres).symm
    (Ideal.Quotient.mk (maximalIdeal R) 1)) • b=b
  simp
  exact (congrArg (· • b)
    (map_one (AlgEquiv.ofBijective (Algebra.ofId k (ResidueField R)) hres).symm)).trans
      (one_smul k b)

include hres
lemma residue_surjective [IsLocalRing (R ⊗[k] K)] (hmap : maximalIdeal (R ⊗[k] K)=
    (maximalIdeal R).map (algebraMap R (R ⊗[k] K)))
    :
    Function.Surjective ((residue (R ⊗[k] K)).comp
      (Algebra.TensorProduct.includeRight (R:=k) (A:=R)).toRingHom) := by
  intro x
  obtain ⟨t,rfl⟩ := IsLocalRing.residue_surjective x
  refine ⟨fiberEquiv k R K hres (Ideal.Quotient.mk _ t),?_⟩
  change Ideal.Quotient.mk (maximalIdeal (R ⊗[k] K)) _=Ideal.Quotient.mk _ t
  rw [hmap]
  apply (fiberEquiv k R K hres).injective
  exact fiberEquiv_includeRight k R K hres _

include hres
lemma maximal_map : ((maximalIdeal R).map (algebraMap R (R ⊗[k] K))).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ ((fiberEquiv k R K hres).toMulEquiv.isField (Field.toIsField K))

variable [Algebra.IsAlgebraic k K]
lemma isLocal : IsLocalRing (R ⊗[k] K) := by
  let T := R ⊗[k] K
  let m := (maximalIdeal R).map (algebraMap R T)
  have hm := maximal_map k R K hres
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨m,hm,?_⟩
  intro Q hQ
  let : Q.IsMaximal := hQ
  let : Algebra.IsIntegral k K := inferInstance
  let : Algebra.IsIntegral R T := inferInstance
  have hcomap := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R:=R) Q
  have hle : m ≤ Q := Ideal.map_le_iff_le_comap.mpr (eq_maximalIdeal hcomap).symm.le
  exact (hm.eq_of_le hQ.ne_top hle).symm

lemma maximalIdeal_eq_map :
    let : IsLocalRing (R ⊗[k] K) := isLocal k R K hres
    maximalIdeal (R ⊗[k] K)=(maximalIdeal R).map (algebraMap R (R ⊗[k] K)) := by
  let : IsLocalRing (R ⊗[k] K) := isLocal k R K hres
  exact (eq_maximalIdeal (maximal_map k R K hres)).symm

end Lech.ResidueTensor

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechLevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

open CategoryTheory
namespace Lech
universe u
variable {R : Type u} [CommRing R] {I : Ideal R}

namespace ResidueGenerators
variable {M : Type u} [AddCommGroup M] [Module R M]
    (hM : I ≤ Module.annihilator R M)

noncomputable def coefficient (m : M) : (R ⧸ I) →ₗ[R] M :=
  I.liftQ (LinearMap.toSpanSingleton R M m) (by
    intro r hr
    exact Module.mem_annihilator.mp (hM hr) m)

@[simp] lemma coefficient_mk (m : M) (r : R) :
    coefficient hM m (Ideal.Quotient.mk I r) = r • m := rfl

variable {ι : Type} [Fintype ι]
noncomputable def map (v : ι → M) : (ι → R ⧸ I) →ₗ[R] M :=
  (Finsupp.lsum R (fun i => coefficient hM (v i))).comp
    (Finsupp.linearEquivFunOnFinite R (R ⧸ I) ι).symm.toLinearMap

end ResidueGenerators
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedChartCochains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.RestrictedPolynomialCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev grade (h n : ℕ) : Submodule R (MvPolynomial (Fin h) S) :=
  (MvPolynomial.homogeneousSubmodule (Fin h) S n).restrictScalars R


end Lech.RestrictedPolynomialCech


end

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
open CategoryTheory
universe u
variable {R : Type u} [CommRing R]
lemma linearMap_sum_smul {A B ι : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] [Fintype ι]
    (f : A →ₗ[R] B) (r : ι → R) (x : ι → A) (y : ι → B)
    (hy : ∀ i, f (x i)=y i) : f (∑ i, r i • x i)=∑ i, r i • y i := by
  simp only [map_sum,map_smul,hy]

 

def cochainOfMap {X Y : ℕ → ModuleCat.{u} R}
    {dX : ∀ n, X n ⟶ X (n+1)} {dY : ∀ n, Y n ⟶ Y (n+1)}
    {hX : ∀ n, dX n ≫ dX (n+1)=0} {hY : ∀ n, dY n ≫ dY (n+1)=0}
    (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n (x : X n), (dY n).hom ((f n).hom x)=(f (n+1)).hom ((dX n).hom x)) :
    CochainComplex.of X dX hX ⟶ CochainComplex.of Y dY hY :=
  CochainComplex.ofHom f (fun n => by
    change f n ≫ CochainComplex.of.d Y dY n (n+1)=CochainComplex.of.d X dX n (n+1) ≫ f (n+1)
    rw [CochainComplex.of_d,CochainComplex.of_d]
    apply ModuleCat.hom_ext
    exact LinearMap.ext (hf n))
end Lech


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]

 
def functor (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  (curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.flip.obj K

end Lech.TensorTotal
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


namespace Lech.TotalGhost
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
open HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]


def towerPath {C : Type*} [Category C] {X : ℕ → C} (f : ∀ n, X (n+1) ⟶ X n) : ∀ n, X n ⟶ X 0
  | 0 => 𝟙 _
  | n+1 => f n ≫ towerPath f n

end Lech.TotalGhost


open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace Lech
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

 
noncomputable def baseChangeFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} S where
  obj M := ModuleCat.of S (S ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.baseChange S)
  map_id _ := by apply ModuleCat.hom_ext; simp
  map_comp _ _ := by apply ModuleCat.hom_ext; exact LinearMap.baseChange_comp _ _

instance baseChangeFunctor_additive : (baseChangeFunctor R S).Additive where
  map_add := by intros; apply ModuleCat.hom_ext; exact LinearMap.baseChange_add _ _


end Lech

open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
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


namespace Lech.TensorTotal.Right
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]
  (K : CochainComplex (ModuleCat.{u} R) ℤ)

 
def degreeSequenceFamily (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (i : ℤ) (pq : {pq : ℤ×ℤ // pq.1+pq.2=i}) : ShortComplex (ModuleCat.{u} R) :=
  (S.map (eval (ModuleCat.{u} R) (.up ℤ) pq.1.2)).map
    ((curriedTensor (ModuleCat.{u} R)).obj (K.X pq.1.1))

end Lech.TensorTotal.Right
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SourceGradedCechHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

lemma component_iso_square_p1 {C : Type*} [Category C]
    {X Y A B D E : C} (eA : A ≅ B) (eD : D ≅ E)
    (a : X ⟶ A) (b : Y ⟶ D) (h : X ⟶ Y) (f : B ⟶ E) (g : A ⟶ D)
    (hg : g = eA.hom ≫ f ≫ eD.inv) (ha : h ≫ b = a ≫ g) :
    (a ≫ eA.hom) ≫ f = h ≫ (b ≫ eD.hom) := by
  rw [← Category.assoc h b, ha, Category.assoc, hg]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators


namespace Lech.SignedFraction
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (w : R) (d : ℕ)

 
def order (t : ℤ) (n : ℕ) : ℕ := ((n*d:ℕ)+t).toNat

@[simp] lemma order_nat (t n : ℕ) : order d (t:ℤ) n=n*d+t := by
  simp only [order, ←Nat.cast_add, Int.toNat_natCast]

lemma order_add_le (t : ℤ) (n k : ℕ) : order d t (k+n) ≤ k*d+order d t n := by
  dsimp only [order]
  push_cast
  have he : ((k:ℤ)+(n:ℤ))*(d:ℤ)+t=(k*d:ℕ)+(n*d:ℕ)+t := by push_cast; ring
  rw [he]
  omega

 
def fraction (t : ℤ) (n : ℕ) : ↥(I^(order d t n)) →ₗ[R] Localization.Away w where
  toFun a := Localization.mk (a:R) (⟨w^n,n,rfl⟩ : Submonoid.powers w)
  map_add' _ _ := (Localization.add_mk_self _ _ _).symm
  map_smul' _ _ := (Localization.smul_mk _ _ _).symm

def piece (t : ℤ) : Submodule R (Localization.Away w) :=
  ⨆ n : ℕ, LinearMap.range (fraction I w d t n)

lemma fraction_mem (t : ℤ) (n : ℕ) (a : ↥(I^(order d t n))) :
    fraction I w d t n a ∈ piece I w d t :=
  Submodule.mem_iSup_of_mem n ⟨a,rfl⟩

variable (hw : w∈I^d)
include hw
lemma raise_fraction (t : ℤ) (n k : ℕ) (a : ↥(I^(order d t n))) :
    ∃ b : ↥(I^(order d t (k+n))), fraction I w d t (k+n) b=fraction I w d t n a := by
  have hp : w^k∈I^(k*d) := by
    simpa only [pow_mul,mul_comm k d] using Ideal.pow_mem_pow hw k
  have hb : w^k*(a:R)∈I^(order d t (k+n)) := by
    apply Ideal.pow_le_pow_right (order_add_le d t n k)
    rw [pow_add]
    exact Ideal.mul_mem_mul hp a.property
  refine ⟨⟨w^k*(a:R),hb⟩,?_⟩
  dsimp only [fraction,LinearMap.coe_mk,AddHom.coe_mk]
  rw [Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [Submonoid.coe_one,one_mul,pow_add]
  ring

lemma range_mono (t : ℤ) : Monotone (fun n : ℕ => LinearMap.range (fraction I w d t n)) := by
  intro n m hnm x hx
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le' hnm
  exact raise_fraction I w d hw t n k a

lemma exists_fraction (t : ℤ) (x : piece I w d t) :
    ∃ (n : ℕ) (a : ↥(I^(order d t n))), fraction I w d t n a=(x:Localization.Away w) := by
  have hx := x.property
  change x.val∈(⨆ n,LinearMap.range (fraction I w d t n)) at hx
  rw [Submodule.mem_iSup_of_directed _ (range_mono I w d hw t).directed_le] at hx
  exact hx
omit hw

lemma antitone : Antitone (piece I w d) := by
  intro s t hst
  apply iSup_le
  intro n
  rintro _ ⟨a,rfl⟩
  have he : order d s n≤order d t n := by unfold order; omega
  exact fraction_mem I w d s n ⟨a.val,Ideal.pow_le_pow_right he a.property⟩
end Lech.SignedFraction


namespace Lech.SignedFraction
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)



variable {w z c : R} {d k : ℕ}
  (hw : w∈I^d) (hc : c∈I^k) (hwc : z*c=w) (hdk : k+1=d)

include hdk in
lemma order_divide_le (t : ℤ) (m n : ℕ) :
    order d t (n+m) ≤ m*k+order d (t+(m:ℤ)) n := by
  dsimp only [order]
  have he : ((n+m)*d:ℕ)+t=(m*k:ℕ)+((n*d:ℕ)+(t+(m:ℤ))) := by
    rw [←hdk]
    push_cast
    ring
  rw [he]
  omega

end Lech.SignedFraction


namespace Lech.SignedFraction
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  {w v c : R} {d e k : ℕ} (hw : w ∈ I^d) (hc : c ∈ I^k)
  (hwc : w*c=v) (hdeg : d+k=e)

include hdeg in
lemma order_restrict_le (t : ℤ) (n : ℕ) : order e t n ≤ order d t n+n*k := by
  dsimp only [order]
  have he : ((n*e:ℕ):ℤ)+t=((n*d:ℕ):ℤ)+t+((n*k:ℕ):ℤ) := by
    rw [←hdeg]
    push_cast
    ring
  rw [he]
  omega

end Lech.SignedFraction


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SignedCechBicRow
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
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℕ)
  (H : ∀ i, Homotopy (z i ^ m • 𝟙 F) 0)


def twistIndex (t : ℤ) (m : ℕ) : ℕ → ℤ
  | 0 => t
  | n+1 => twistIndex t m n+(m:ℤ)

lemma twistIndex_eq (t : ℤ) (m N : ℕ) : twistIndex t m N=t+(m*N:ℕ) := by
  induction N with
  | zero => simp [twistIndex]
  | succ N ih =>
    rw [twistIndex,ih,Nat.mul_succ,Nat.cast_add,add_assoc]

lemma twistIndex_le (t : ℤ) (m N : ℕ) : t ≤ twistIndex t m N := by
  rw [twistIndex_eq]
  omega

end Lech.SignedCech


namespace Lech.SignedFraction
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (w : R) (d : ℕ)

lemma order_mul_le (t : ℤ) (M n : ℕ) : order d (t+(M:ℤ)) n ≤ M+order d t n := by
  unfold order
  omega

variable (hw : w∈I^d)
include hw
lemma smul_mem_shift (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) (x : piece I w d t) :
    a • x.val ∈ piece I w d (t+(M:ℤ)) := by
  obtain ⟨n,b,hb⟩ := exists_fraction I w d hw t x
  have hab : a*(b:R) ∈ I^(order d (t+(M:ℤ)) n) := by
    apply Ideal.pow_le_pow_right (order_mul_le d t M n)
    rw [pow_add]
    exact Ideal.mul_mem_mul ha b.property
  rw [←hb]
  change a • Localization.mk (b:R) (⟨w^n,n,rfl⟩ : Submonoid.powers w) ∈ _
  rw [Localization.smul_mk]
  exact fraction_mem I w d (t+(M:ℤ)) n ⟨a*(b:R),hab⟩

 
def multiply (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) :
    piece I w d t →ₗ[R] piece I w d (t+(M:ℤ)) where
  toFun x := ⟨a • x.val,smul_mem_shift I w d hw t M a ha x⟩
  map_add' _ _ := Subtype.ext (smul_add _ _ _)
  map_smul' _ _ := Subtype.ext (smul_comm _ _ _)

end Lech.SignedFraction


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_BicomplexImageLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.TensorIdeal
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] {M N T : ModuleCat.{u} R}
  (f : M ⟶ N) (hf : Function.Injective f.hom) (g : T ⟶ N) (hr : g.hom.range≤f.hom.range)
def imageLift : T ⟶ M := ModuleCat.ofHom
  ((LinearEquiv.ofInjective f.hom hf).symm.toLinearMap.comp
    (g.hom.codRestrict f.hom.range (fun x => hr (LinearMap.mem_range_self _ x))))
end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FibreSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory
open scoped TensorProduct
universe u
section Quotient
variable {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (I : Ideal R)

def kernelSquareEquiv {P Q : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (f : M →ₗ[R] N) (g : P →ₗ[R] Q)
    (e : M ≃ₗ[R] P) (e' : N ≃ₗ[R] Q) (h : ∀ x,e' (f x)=g (e x)) :
    f.ker ≃ₗ[R] g.ker :=
  e.ofSubmodules _ _ (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext x
    change f (e.symm x)=0 ↔ g x=0
    calc
      _ ↔ e' (f (e.symm x))=0 := (map_eq_zero_iff _ e'.injective).symm
      _ ↔ g x=0 := by rw [h,e.apply_symm_apply])

end Quotient

section Square
variable {R A B C D : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [AddCommGroup C] [Module A C] [Module R C] [IsScalarTower R A C]
  [AddCommGroup D] [Module A D] [Module R D] [IsScalarTower R A D]
  (I : Ideal R) (a : A →ₗ[A] C) (b : B →ₗ[A] D) (g : C →ₗ[A] D)
  (ha : Function.Surjective a) (hb : Function.Surjective b)
  (hka : (a.restrictScalars R).ker = I • (⊤ : Submodule R A))
  (hkb : (b.restrictScalars R).ker = I • (⊤ : Submodule R B))
  (hsq : b 1=g (a 1))
  (V : Type u) [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]

abbrev unitMap : V →ₗ[R] B ⊗[A] V := (TensorProduct.mk A B V 1).restrictScalars R

end Square
end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra

include hz in
lemma product_mem (s : Finset (Fin (n+1))) : (∏ j ∈ s, z j) ∈ I^s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
      rw [Finset.prod_insert hjs,Finset.card_insert_of_notMem hjs,pow_succ']
      exact Ideal.mul_mem_mul (hz j) ih

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechCartierZRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] (J : Ideal R)
  {M N M' N' : ModuleCat.{u} R} (f : M ⟶ N) (g : M' ⟶ N')
  (e : M' ≅ M) (e' : N' ≅ N)
lemma range_of_square (hsq : g ≫ e'.hom=e.hom ≫ f)
    (hf : f.hom.range=J • (⊤ : Submodule R N)) :
    g.hom.range=J • (⊤ : Submodule R N') := by
  apply Submodule.map_injective_of_injective ((ModuleCat.mono_iff_injective e'.hom).mp inferInstance)
  rw [←LinearMap.range_comp]
  have he : e'.hom.hom.comp g.hom=f.hom.comp e.hom.hom := congrArg ModuleCat.Hom.hom hsq
  rw [he,LinearMap.range_comp,(LinearMap.range_eq_top.mpr
    ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance)),Submodule.map_top,hf,
    Submodule.map_smul'',Submodule.map_top,(LinearMap.range_eq_top.mpr
      ((ModuleCat.epi_iff_surjective e'.hom).mp inferInstance))]

end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerRemainderExponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
namespace Lech.RootTower
variable {σ R : Type*} [Fintype σ] [CommRing R] (q : ℕ) [NeZero q]

def remainderExponent (r : σ → Fin q) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (r i : ℕ))

omit [NeZero q] in
@[simp] lemma remainderExponent_apply (r : σ → Fin q) (i : σ) :
    remainderExponent q r i = (r i : ℕ) := by
  simp [remainderExponent]

def exponentRemainder (d : σ →₀ ℕ) : σ → Fin q :=
  fun i => ⟨d i % q, Nat.mod_lt _ (NeZero.pos q)⟩

def exponentQuotient (d : σ →₀ ℕ) : σ →₀ ℕ :=
  d.mapRange (fun n => n / q) (Nat.zero_div q)

lemma exponent_split (d : σ →₀ ℕ) :
    q • exponentQuotient q d + remainderExponent q (exponentRemainder q d) = d := by
  ext i
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    exponentQuotient, Finsupp.mapRange_apply, remainderExponent_apply, exponentRemainder]
  exact Nat.div_add_mod (d i) q

@[simp] lemma exponentRemainder_split (d : σ →₀ ℕ) (r : σ → Fin q) :
    exponentRemainder q (q • d + remainderExponent q r) = r := by
  funext i
  apply Fin.ext
  simp [exponentRemainder, Nat.add_mod, Nat.mod_eq_of_lt (r i).isLt]

@[simp] lemma exponentQuotient_split (d : σ →₀ ℕ) (r : σ → Fin q) :
    exponentQuotient q (q • d + remainderExponent q r) = d := by
  ext i
  simp [exponentQuotient, Nat.mul_add_div (NeZero.pos q),
    Nat.div_eq_of_lt (r i).isLt]

lemma coeff_expansion_monomial_eq_zero (f : MvPowerSeries σ R)
    (d : σ →₀ ℕ) (r : σ → Fin q) (hr : r ≠ exponentRemainder q d) :
    coeff d (expand q (NeZero.ne q) f * monomial (remainderExponent q r) 1) = 0 := by
  rw [coeff_mul_monomial]
  split_ifs with hle
  · rw [mul_one]
    by_contra hf
    have hs : d - remainderExponent q r ∈ (expand q (NeZero.ne q) f).support := hf
    rw [support_expand] at hs
    obtain ⟨a, _, ha⟩ := hs
    change q • a = d - remainderExponent q r at ha
    have hd : d = q • a + remainderExponent q r := by
      rw [ha, tsub_add_cancel_of_le hle]
    exact hr (by rw [hd, exponentRemainder_split])
  · rfl

lemma coeff_expansion_monomial_split (f : MvPowerSeries σ R)
    (d : σ →₀ ℕ) (r : σ → Fin q) :
    coeff (q • d + remainderExponent q r)
      (expand q (NeZero.ne q) f * monomial (remainderExponent q r) 1) = coeff d f := by
  rw [coeff_add_mul_monomial, coeff_expand_smul, mul_one]

 
def extract (r : σ → Fin q) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun d => coeff (q • d + remainderExponent q r) f

lemma sum_expansion_extract (f : MvPowerSeries σ R) :
    (∑ r : σ → Fin q, expand q (NeZero.ne q) (extract q r f) *
      monomial (remainderExponent q r) 1) = f := by
  ext d
  simp only [map_sum]
  rw [Finset.sum_eq_single (exponentRemainder q d)]
  · conv_lhs => arg 1; rw [← exponent_split q d]
    rw [coeff_expansion_monomial_split]
    change coeff (q • exponentQuotient q d + remainderExponent q (exponentRemainder q d)) f = _
    rw [exponent_split]
  · intro r _ hr
    exact coeff_expansion_monomial_eq_zero q (extract q r f) d r hr
  · simp

lemma coeff_sum_expansion (f : (σ → Fin q) → MvPowerSeries σ R)
    (d : σ →₀ ℕ) (r : σ → Fin q) :
    coeff (q • d + remainderExponent q r)
      (∑ t, expand q (NeZero.ne q) (f t) * monomial (remainderExponent q t) 1) =
      coeff d (f r) := by
  simp only [map_sum]
  rw [Finset.sum_eq_single r]
  · exact coeff_expansion_monomial_split q (f r) d r
  · intro t _ ht
    apply coeff_expansion_monomial_eq_zero
    simpa using ht
  · simp


omit [Fintype σ] in
lemma expansion_local : IsLocalHom (expand (σ := σ) (R := R) q (NeZero.ne q)).toRingHom := by
  constructor
  intro f hf
  rw [isUnit_iff_constantCoeff] at hf ⊢
  change IsUnit (constantCoeff (expand q (NeZero.ne q) f)) at hf
  simpa only [constantCoeff_expand] using hf

omit [Fintype σ] in
lemma map_bijective_of_bijective {S : Type*} [CommRing S]
    (f : R →+* S) (hf : Function.Bijective f) :
    Function.Bijective (MvPowerSeries.map (σ := σ) f) := by
  constructor
  · intro x y h
    ext d
    apply hf.1
    exact congrArg (coeff d) h
  · intro x
    choose y hy using fun d => hf.2 (coeff d x)
    refine ⟨y, ?_⟩
    ext d
    exact hy d

end Lech.RootTower

open scoped TensorProduct
open IsLocalRing
namespace Lech.RootTower

variable {R S ι : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)] [Fintype ι]

lemma fiber_length_of_basis (b : Module.Basis ι R S)
    (hres : Function.Surjective (ResidueField.map (algebraMap R S))) :
    Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) = Fintype.card ι := by
  let Q := S ⧸ (maximalIdeal R).map (algebraMap R S)
  have hr : Module.length (ResidueField R) (ResidueField S) = 1 := by
    rw [Module.length_eq_of_surjective (R := ResidueField S) (M := ResidueField S) hres]
    simp
  have hlen := IsLocalRing.length_restrictScalars R S Q
  rw [hr, mul_one] at hlen
  rw [← hlen]
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).toLinearEquiv
  rw [(e.restrictScalars R).length_eq]
  change Module.length R (S ⊗[R] ResidueField R) = _
  rw [(TensorProduct.comm R S (ResidueField R)).length_eq]
  let b' := b.baseChange (ResidueField R)
  have he := b'.repr.length_eq
  rw [Module.length_eq_of_surjective (R := ResidueField R) (M := ResidueField R ⊗[R] S)
    (residue_surjective (R := R)), he]
  simp [Module.length_finsupp, ENat.card]

end Lech.RootTower

open MvPowerSeries IsLocalRing
namespace Lech.RootTower
variable {σ k : Type*} [Fintype σ] [Field k]

omit [Fintype σ] in
lemma residue_eq_constant (f : MvPowerSeries σ k) :
    residue (MvPowerSeries σ k) f = residue (MvPowerSeries σ k) (C (constantCoeff f)) := by
  apply Ideal.Quotient.eq.mpr
  rw [mem_maximalIdeal]
  change ¬ IsUnit (f - C (constantCoeff f))
  rw [isUnit_iff_constantCoeff]
  simp

end Lech.RootTower


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsReduced A] (p : ℕ) [Fact p.Prime] [CharP A p]


omit [IsReduced A] in
lemma iterateFrobenius_local (n : ℕ) : IsLocalHom (iterateFrobenius A p n) where
  map_nonunit x hx := by
    rw [iterateFrobenius_def] at hx
    exact (isUnit_pow_iff (pow_ne_zero n (Nat.Prime.ne_zero Fact.out))).mp hx

end Lech.RootTower


namespace Lech.RootTower

lemma self_length_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  let f : R →ₛₗ[e.toRingHom] S :=
    { toAddHom := e.toAddMonoidHom, map_smul' := fun r x => e.map_mul r x }
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)

lemma quotient_length_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (J : Ideal S) (h : J = I.map e) :
    Module.length R (R ⧸ I) = Module.length S (S ⧸ J) := by
  rw [Module.length_eq_of_surjective (R := R ⧸ I) (Ideal.Quotient.mk_surjective),
    Module.length_eq_of_surjective (R := S ⧸ J) (Ideal.Quotient.mk_surjective)]
  exact self_length_ringEquiv (Ideal.quotientEquiv I J e h)



open IsLocalRing

end Lech.RootTower
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerRootWeight
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
namespace Lech.RootTower
lemma root_weight_mul (p d n m : ℕ) (hp : 0 < p) (h : n ≤ m) :
    ((p : ℝ≥0∞) ^ (m*d))⁻¹ * (p : ℝ≥0∞) ^ ((m-n)*d) =
      ((p : ℝ≥0∞) ^ (n*d))⁻¹ := by
  have hs : m*d = (m-n)*d + n*d := by rw [← Nat.add_mul, Nat.sub_add_cancel h]
  have hz : (p : ℝ≥0∞) ^ ((m-n)*d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne')
  have ht : (p : ℝ≥0∞) ^ ((m-n)*d) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  rw [hs, pow_add, ENNReal.mul_inv (Or.inl hz) (Or.inl ht), mul_right_comm, ENNReal.inv_mul_cancel hz ht, one_mul]
end Lech.RootTower

open scoped ENNReal TensorProduct Classical DirectSum
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerLengthEq
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


namespace Lech.RootTower
open Module
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]

instance perfectBaseAlgebra : Algebra K (PerfectClosure L p) :=
  ((PerfectClosure.of L p).comp (algebraMap K L)).toAlgebra

instance perfectBaseTower : IsScalarTower K L (PerfectClosure L p) :=
  IsScalarTower.of_algebraMap_eq' rfl

def perfectOf : L →ₐ[K] PerfectClosure L p where
  __ := PerfectClosure.of L p
  commutes' _ := rfl

end Lech.RootTower


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsDomain A] (L : Type*) [Field L] [Algebra A L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP L p]

instance perfectOriginalAlgebra : Algebra A (PerfectClosure L p) :=
  ((PerfectClosure.of L p).comp (algebraMap A L)).toAlgebra
instance perfectOriginalTower : IsScalarTower A L (PerfectClosure L p) :=
  IsScalarTower.of_algebraMap_eq' rfl

end Lech.RootTower


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusIntermediatePowerMap
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
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct


namespace Lech.SeparableOrder
variable (A D K L : Type*) [CommRing A] [CommRing D] [IsDomain D]
  [Field K] [Field L] [Algebra A D] [Algebra A K] [Algebra A L]
  [Algebra K L] [Algebra D L] [IsScalarTower A K L] [IsScalarTower A D L]

 

def order : Subalgebra A D :=
  ((separableClosure K L).toSubalgebra.restrictScalars A).comap
    (IsScalarTower.toAlgHom A D L)

instance orderFinite [IsNoetherianRing A] [Module.Finite A D] :
    Module.Finite A (order A D K L) := by
  change Module.Finite A (order A D K L).toSubmodule
  infer_instance

 
def toField : order A D K L →ₐ[A] separableClosure K L where
  toFun x := ⟨algebraMap D L x, x.2⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_mul' x y := by apply Subtype.ext; exact map_mul _ _ _
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  commutes' a := by
    apply Subtype.ext
    exact (IsScalarTower.algebraMap_apply A D L a).symm

instance orderFieldAlgebra : Algebra (order A D K L) (separableClosure K L) :=
  (toField A D K L).toRingHom.toAlgebra

instance orderFieldTower : IsScalarTower A (order A D K L) (separableClosure K L) :=
  IsScalarTower.of_algebraMap_eq' (toField A D K L).comp_algebraMap.symm

instance orderFieldAmbientTower :
    IsScalarTower (order A D K L) (separableClosure K L) L :=
  IsScalarTower.of_algebraMap_eq' rfl

end Lech.SeparableOrder


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CompleteResidueExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open IsLocalRing TensorProduct
namespace Lech.ResidueCompletion
variable {T K : Type*} [CommRing T] [IsLocalRing T] [Field K]

def coefficient (φ : K →+* T) : K →+* AdicCompletion (maximalIdeal T) T :=
  (algebraMap T (AdicCompletion (maximalIdeal T) T)).comp φ

lemma coefficient_surjective (fg : (maximalIdeal T).FG) (φ : K →+* T)
    (hφ : Function.Surjective ((residue T).comp φ)) :
    letI := AdicCompletion.isLocalRing_of_fg fg
    Function.Surjective ((residue (AdicCompletion (maximalIdeal T) T)).comp (coefficient φ)) := by
  let := AdicCompletion.isLocalRing_of_fg fg
  let := AdicCompletion.algebraMap_isLocalHom_of_fg fg
  intro x
  obtain ⟨y,rfl⟩ := (AdicCompletion.residueField_map_bijective_of_fg fg).2 x
  obtain ⟨k,rfl⟩ := hφ y
  refine ⟨k,?_⟩
  exact (ResidueField.map_residue _ _).symm

end Lech.ResidueCompletion

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteFreeTensorCohomology
attribute [-instance] _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (P M : ModuleCat.{u} R) (b : ℕ)
  (B : Module.Basis (Fin b) R P)

def tensorBasisEquiv : (P ⊗[R] M) ≃ₗ[R] (Fin b → M) :=
  TensorProduct.congr B.equivFun (LinearEquiv.refl R M) ≪≫ₗ
    TensorProduct.piLeft R M (fun _ : Fin b => R) ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R M)

variable {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{u} R) c)
  [Module.Flat R P]

def tensorHomologyIso (q : ι) :
    ((((curriedTensor (ModuleCat.{u} R)).obj P).mapHomologicalComplex c).obj K).homology q ≅
      ModuleCat.of R (P ⊗[R] K.homology q) :=
  (K.sc q).mapHomologyIso ((curriedTensor (ModuleCat.{u} R)).obj P)

def tensorHomologyBasisIso (q : ι) :
    ((((curriedTensor (ModuleCat.{u} R)).obj P).mapHomologicalComplex c).obj K).homology q ≅
      ModuleCat.of R (Fin b → K.homology q) :=
  tensorHomologyIso P K q ≪≫ (tensorBasisEquiv P (K.homology q) b B).toModuleIso

end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootLayerCech
attribute [-instance] _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra
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

local instance nonemptyFinite (s : Finset (Fin (n+1))) :
    Fintype (PLift s.Nonempty) := Fintype.ofFinite _

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ResidueExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open IsLocalRing TensorProduct
namespace Lech
universe u
structure ResidueExtension (R : Type u) [CommRing R] [IsLocalRing R] where
  S : Type u
  commRing : CommRing S
  localRing : IsLocalRing S
  noetherian : IsNoetherianRing S
  algebra : Algebra R S
  flat : Module.Flat R S
  complete : IsAdicComplete (maximalIdeal S) S
  maximal_map : (maximalIdeal R).map (algebraMap R S)=maximalIdeal S
  algClosed : IsAlgClosed (ResidueField S)
attribute [instance] ResidueExtension.commRing ResidueExtension.localRing
  ResidueExtension.noetherian ResidueExtension.algebra ResidueExtension.flat
  ResidueExtension.complete ResidueExtension.algClosed

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootUlrichNaturality
attribute [-instance] _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace Lech
universe u v w w' z
lemma basis_coordinates_semilinear {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    {M : Type w} {N : Type w'} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
    {ι : Type z} [Fintype ι] (b : Module.Basis ι A M) (c : Module.Basis ι B N)
    (φ : A →+* B) (f : M →ₛₗ[φ] N) (hb : ∀ i,f (b i)=c i) (x : M) :
    c.equivFun (f x)=fun i => φ (b.equivFun x i) := by
  classical
  apply c.equivFun.symm.injective
  rw [LinearEquiv.symm_apply_apply,Module.Basis.equivFun_symm_apply]
  conv_lhs => rw [←b.sum_repr x,map_sum]
  simp only [map_smulₛₗ,hb,Module.Basis.equivFun_apply]
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorGeneratorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
namespace Lech.TensorGenerator
variable {D M : Type*} [CommRing D] [AddCommGroup M] [Module D M]

variable {b : ℕ} (f : (Fin b → D) →ₗ[D] M)
  (B : Type*) [CommRing B] [Algebra D B]

def baseGenerators : (Fin b → B) →ₗ[B] B ⊗[D] M :=
  (f.baseChange B).comp (((Pi.basisFun D (Fin b)).baseChange B).equivFun.symm.toLinearMap)

end Lech.TensorGenerator

end

end OAI
end


