-- Prove2me | Definitions.Def_OAIQ032L006
-- name    : OAIQ032L006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:43:51.377703+00:00
-- url     : https://prove2.me/theorems/dd522f50-c444-45de-8d4d-3303f4c59e71
-- title:
--   Definitions bundle OAIQ032L006 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 126 declarations of OpenAI's Lean: 49 definitions, 3 inductive types or structures, 2 instances and 72 theorems. The definitions and types are `OAI.Lech.Koszul.nullScalarIdeal`, `OAI.Lech.Koszul.restrictScalarsHomologyIso`, `OAI.Lech.Koszul.scalarPowerHomotopy`, `OAI.Lech.Koszul.singleModule`, `OAI.Lech.LineBasisExtension.coefficients`, `OAI.Lech.LineBasisExtension.coordinates`, `OAI.Lech.LineBasisExtension.extend`, `OAI.Lech.LineBasisExtension.included`, `OAI.Lech.LineBasisExtension.transition`, `OAI.Lech.LinearNormalization.linearChange`, `OAI.Lech.LocalizationImageCover.localMap`, `OAI.Lech.MonomialSpanning.Bounded`, `OAI.Lech.MonomialSpanning.boundedEquivTotal`, `OAI.Lech.MonomialSpanning.boundedSigmaEquiv`, `OAI.Lech.MonomialSpanning.exponent`, `OAI.Lech.MonomialSpanning.monic`, `OAI.Lech.NormalizedLength.Tower`, `OAI.Lech.NormalizedLength.Tower.finiteLength`, `OAI.Lech.NormalizedLength.Tower.length`, `OAI.Lech.NormalizedLength.Tower.stage`, `OAI.Lech.Numerical.GoodRoots`, `OAI.Lech.Numerical.H`, `OAI.Lech.Numerical.P`, `OAI.Lech.Numerical.Ps`, `OAI.Lech.Numerical.bound`, `OAI.Lech.Numerical.layer`, `OAI.Lech.Numerical.normalizedLayer`, `OAI.Lech.Numerical.roundedRoot`, `OAI.Lech.Numerical.ρ`, `OAI.Lech.PartialLaurent.indicator`, `OAI.Lech.PartialLaurent.polyGrade`, `OAI.Lech.PartialLaurent.polynomialDenominator`, `OAI.Lech.PartialLaurent.totalDegreeNat`, `OAI.Lech.PowerSeries.divide`, `OAI.Lech.PowerSeries.pick`, `OAI.Lech.Primary.colength`, `OAI.Lech.Primary.multiplicity`, `OAI.Lech.Primary.normalizedColength`, `OAI.Lech.PrimeFiltration.Above`, `OAI.Lech.PrimeFiltration.Factors` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_AlternatingCechPost`, `Multiplicity_ExactSequenceTransport`, `Multiplicity_FrobeniusComplexStage`, `Multiplicity_FrobeniusTensorStage`, `Multiplicity_GradedLineBasisHasBasis`, `Multiplicity_IdealGradedLengthPiece`, `Multiplicity_KoszulConeFunctor`, `Multiplicity_KoszulHomologyMap`, `Multiplicity_LechBoundedEquiv`, `Multiplicity_LechFactorizationMap`, `Multiplicity_LechLevel`, `Multiplicity_LechNatTrans`, `Multiplicity_LechSignedUnit`, `Multiplicity_LechTorsionOf`, `Multiplicity_LinearNormalization`, `Multiplicity_NumericalSupport`, `Multiplicity_PartialLaurentTotalDegree`, `Multiplicity_PerfectDomainStagesTensorTo`, `Multiplicity_PowerSeriesFlatVariables`, `Multiplicity_PrimeFiltrationSupport`, `Multiplicity_PrincipalCoverRegularRegularMap`, `Multiplicity_ReesRootLayers`, `Multiplicity_RootChartAtlasGlobalCoefficient`, `Multiplicity_RootCoactionT`, `Multiplicity_RootStageQuotient`, `Multiplicity_RootTowerLengthEq`, `Multiplicity_RootTowerRemainderExponent`, `Multiplicity_RootTowerRootWeight`, `Multiplicity_RootUlrichModule`, `Multiplicity_SubalgebraStageFromBase`, `Multiplicity_TowerRestrictedLength`, `Multiplicity_TwistedLocalizationPieceMap`.
--
--   **Imports.** It imports the published bundle `Def_DuttaDomain`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L014`, `OAIQ032L015` and `OAIQ032L016`; the statements `OAI.Lech.CharP.normalized_perfection_module_finite`, `OAI.Lech.CharP.perfection_complex_value`, `OAI.Lech.MinimalReduction.exists_minimal_reduction`, `OAI.Lech.Normalization.parameter_frobenius_multiplicity_enn`, `OAI.Lech.Normalization.parameter_multiplicity_pos`, `OAI.Lech.Primary.multiplicity_nonneg`, `OAI.Lech.PrimeFiltration.Factors.euler_self`, `OAI.Lech.PrimeFiltration.Factors.multiplicity_self`, `OAI.Lech.TensorConductor.length_tendsto`, `OAI.Lech.TensorGenerator.length_le`, `OAI.Lech.TensorGenerator.scalar_cokernel_le` and `OAI.Lech.shortComplex_nullScalar_radical`; the proofs of `OAI.Lech.CharP.dutta_limit_from_perfection`, `OAI.Lech.CharP.dutta_lower_bound_infinite_perfect`, `OAI.Lech.CharP.perfection_complex_value`, `OAI.Lech.LinearNormalization.exists_linear_normalization`, `OAI_Lech_ReesRoot_rootTotal_euler_nonnegative`, `OAI.Lech.TensorGenerator.length_le`, `OAI.Lech.TensorGenerator.scalar_cokernel_le`, `OAI_Lech_complex_estimate_basis`, `OAI.Lech.dutta_algClosed` and `OAI.Lech.shortComplex_nullScalar_radical`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_DuttaDomain

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
variable {R : Type u} [CommRing R]

namespace MonomialSpanning
variable {h : ℕ} (z : Fin h → R)

noncomputable def monic (d : Fin h →₀ ℕ) : R :=
  MvPolynomial.eval z (MvPolynomial.monomial d 1)

lemma span_monic_degree (n : ℕ) :
    Ideal.span (Set.range z) ^ n =
      Ideal.span (monic z '' {d : Fin h →₀ ℕ | d.degree = n}) := by
  have hm : Ideal.map (MvPolynomial.eval z) (MvPolynomial.idealOfVars (Fin h) R) =
      Ideal.span (Set.range z) := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
    congr 1
    ext i
    simp [Function.comp_def]
  rw [← hm, ← Ideal.map_pow, MvPolynomial.pow_idealOfVars_eq_span, Ideal.map_span,
    ← Set.image_comp]
  rfl

lemma monic_mem_power {n : ℕ} {d : Fin h →₀ ℕ} (hd : d.degree = n) :
    monic z d ∈ Ideal.span (Set.range z) ^ n := by
  rw [span_monic_degree]
  exact Ideal.subset_span ⟨d, hd, rfl⟩


def Bounded (h a n : ℕ) := {e : Fin h → Fin a // ∑ i, (e i : ℕ) = n}

noncomputable instance boundedFintype (a n : ℕ) : Fintype (Bounded h a n) := by
  classical
  unfold Bounded
  infer_instance

noncomputable def exponent {a n : ℕ} (e : Bounded h a n) : Fin h →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (e.val i : ℕ))

@[simp] lemma exponent_apply {a n : ℕ} (e : Bounded h a n) (i : Fin h) :
    exponent e i = (e.val i : ℕ) := by simp [exponent]

lemma exponent_degree {a n : ℕ} (e : Bounded h a n) : (exponent e).degree = n := by
  rw [Finsupp.degree_eq_sum]
  simpa only [exponent_apply] using e.property

end MonomialSpanning



namespace MonomialSpanning
variable {h : ℕ} (z : Fin h → R)

lemma bounded_degree_le (a : ℕ) (e : Fin h → Fin a) :
    ∑ i, (e i : ℕ) ≤ h * a := by
  calc
    ∑ i, (e i : ℕ) ≤ ∑ _i : Fin h, a :=
      Finset.sum_le_sum fun i _ => (e i).isLt.le
    _ = h * a := by simp

noncomputable def boundedSigmaEquiv (h a : ℕ) :
    (Σ n : Fin (h*a+1), Bounded h a n) ≃ (Fin h → Fin a) where
  toFun e := e.2.val
  invFun e := ⟨⟨∑ i, (e i : ℕ), Nat.lt_succ_of_le (bounded_degree_le a e)⟩, ⟨e, rfl⟩⟩
  left_inv e := by
    rcases e with ⟨⟨n, hn⟩, ⟨e, he⟩⟩
    change ∑ i, (e i : ℕ) = n at he
    subst n
    rfl
  right_inv _ := rfl

end MonomialSpanning
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechBoundedEquiv
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
variable {R : Type u} [CommRing R]
namespace MonomialSpanning

noncomputable def boundedEquivTotal (h a n : ℕ) (hn : n < a) :
    Bounded h a n ≃ {e : Fin h → ℕ // ∑ i, e i = n} where
  toFun e := ⟨fun i => (e.val i : ℕ), e.property⟩
  invFun e := ⟨fun i => ⟨e.val i, by
    have hi : e.val i ≤ ∑ j, e.val j := Finset.single_le_sum
      (fun j _ => Nat.zero_le (e.val j)) (Finset.mem_univ i)
    exact (hi.trans_eq e.property).trans_lt hn⟩, e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end MonomialSpanning
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechTorsionOf
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


namespace Lech.PartialLaurent
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))

def indicator : Fin h → ℕ := fun i => if i ∈ s then 1 else 0
end Lech.PartialLaurent

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PartialLaurentTotalDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
namespace Lech.PartialLaurent
open AddMonoidAlgebra HomogeneousLocalization
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))
def totalDegreeNat : (Fin h → ℕ) →+ ℕ where
  toFun a := ∑ i,a i
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]
abbrev polyGrade := gradeBy R (totalDegreeNat (h := h))
lemma total_indicator : totalDegreeNat (indicator s) = s.card := by
  classical
  simp [totalDegreeNat,indicator]
end Lech.PartialLaurent


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TwistedLocalizationPieceMap
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


namespace Lech.PartialLaurent
open AddMonoidAlgebra SetLike
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))
attribute [local instance] MvPolynomial.gradedAlgebra

def polynomialDenominator : MvPolynomial (Fin h) R := ∏ i ∈ s, MvPolynomial.X i

end Lech.PartialLaurent


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AlternatingCechPost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators

open scoped Classical


namespace Lech.ProductLinearChart
open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Fin n → Bool)
abbrev Ring := MvPolynomial (Fin n) R

def a (i : Fin n) : Ring R n := if σ i then 1 else MvPolynomial.X i
def b (i : Fin n) : Ring R n := if σ i then MvPolynomial.X i else 1

def product : (Ring R n)[X] := ∏ i : Fin n,(C (a R n σ i)*Polynomial.X+C (b R n σ i))

end Lech.ProductLinearChart


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ExactSequenceTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace Lech.ModuleSequence
universe u v w w' w'' z z' z''
variable {A : Type u} [CommRing A]
  {M : Type v} {N : Type w} {P : Type w'}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module A M] [Module A N] [Module A P]

lemma transport {M' : Type z} {N' : Type z'} {P' : Type z''}
    [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
    [Module A M'] [Module A N'] [Module A P']
    (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (f' : M' →ₗ[A] N') (g' : N' →ₗ[A] P')
    (eM : M ≃ₗ[A] M') (eN : N ≃ₗ[A] N') (eP : P ≃ₗ[A] P')
    (hf : eN.toLinearMap.comp f=f'.comp eM.toLinearMap)
    (hg : eP.toLinearMap.comp g=g'.comp eN.toLinearMap)
    (hi : Function.Injective f) (he : Function.Exact f g) (hs : Function.Surjective g) :
    Function.Injective f' ∧ Function.Exact f' g' ∧ Function.Surjective g' := by
  have hf' (x : M) : eN (f x)=f' (eM x) := DFunLike.congr_fun hf x
  have hg' (x : N) : eP (g x)=g' (eN x) := DFunLike.congr_fun hg x
  refine ⟨?_,?_,?_⟩
  · intro x y h
    obtain ⟨x,rfl⟩ := eM.surjective x
    obtain ⟨y,rfl⟩ := eM.surjective y
    apply congrArg eM
    apply hi
    apply eN.injective
    rw [hf',hf']
    exact h
  · exact (Function.Exact.iff_of_ladder_linearEquiv hf.symm hg.symm).mpr he
  · intro y
    obtain ⟨y,rfl⟩ := eP.surjective y
    obtain ⟨x,rfl⟩ := hs y
    exact ⟨eN x,(hg' x).symm⟩

lemma baseChange (B : Type z) [CommRing B] [Algebra A B] [Module.Flat A P]
    (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hi : Function.Injective f) (he : Function.Exact f g) (hs : Function.Surjective g) :
    Function.Injective (f.baseChange B) ∧ Function.Exact (f.baseChange B) (g.baseChange B) ∧
      Function.Surjective (g.baseChange B) :=
  ⟨LinearMap.lTensor_injective_of_exact_of_flat g hs f hi he B,
    lTensor_exact B he hs,LinearMap.lTensor_surjective B hs⟩
end Lech.ModuleSequence

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrincipalCoverRegularRegularMap
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
open scoped BigOperators
open scoped Classical
namespace Lech.PrincipalCoverRegular
universe u v
variable {R : Type u} [CommRing R] {ι : Type v}
lemma regular_map {M : Submonoid R} {S : Type*} [CommRing S] [Algebra R S] [IsLocalization M S]
    {x : R} (hx : IsRegular x) : IsRegular (algebraMap R S x) :=
  isRegular_iff_mem_nonZeroDivisors.mpr (IsLocalization.nonZeroDivisors_le_comap M S hx.mem_nonZeroDivisors)


end Lech.PrincipalCoverRegular


namespace Lech.ProductSourceCover
open scoped BigOperators
universe u
abbrev Exponent (n : ℕ) := Fin n →₀ ℤ
abbrev LaurentModule (R : Type u) [Zero R] (n : ℕ) := Exponent n →₀ R
end Lech.ProductSourceCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootCoactionT
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
open scoped BigOperators
open scoped Classical


namespace Lech.ModuleDescent
open scoped TensorProduct
open TensorProduct
universe u v w
variable {A : Type u} {B : Type v} {M : Type w}
  [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]

 
lemma finitePresentation [Module.FaithfullyFlat A B]
    [Module.FinitePresentation B (B ⊗[A] M)] : Module.FinitePresentation A M := by
  let : Module.Finite A M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  obtain ⟨n,p,hp⟩ := (Submodule.fg_iff_exists_fin_linearMap (N := (⊤ : Submodule A M))).mp
    (Module.Finite.fg_top (R := A) (M := M))
  have hsurj : Function.Surjective p := LinearMap.range_eq_top.mp hp
  let pB := AlgebraTensorModule.lTensor B B p
  have hpB : Function.Surjective pB :=
    (Module.FaithfullyFlat.lTensor_surjective_iff_surjective A B p).mpr hsurj
  have hkB : (LinearMap.ker pB).FG := Module.FinitePresentation.fg_ker pB hpB
  let : Module.Finite B (LinearMap.ker pB) := Module.Finite.of_fg hkB
  let : Module.Finite B (B ⊗[A] LinearMap.ker p) :=
    Module.Finite.equiv (LinearMap.tensorKerEquiv B B p).symm
  let : Module.Finite A (LinearMap.ker p) :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  exact Module.finitePresentation_of_surjective p hsurj (Module.Finite.iff_fg.mp inferInstance)
end Lech.ModuleDescent


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

open scoped TensorProduct
open IsLocalRing

open MvPowerSeries IsLocalRing


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsReduced A] (p : ℕ) [Fact p.Prime] [CharP A p]

 
def rootMap (n : ℕ) : A →+* PerfectClosure A p where
  toFun x := PerfectClosure.mk A p (n, x)
  map_one' := by simpa using (PerfectClosure.natCast A p n 1).symm
  map_zero' := PerfectClosure.mk_zero_right A p n
  map_mul' x y := by
    rw [PerfectClosure.mk_mul_mk, PerfectClosure.eq_iff]
    simp only [← coe_iterateFrobenius, map_mul]
    simp only [coe_iterateFrobenius, ← Function.iterate_add_apply]
  map_add' x y := by
    rw [PerfectClosure.mk_add_mk, PerfectClosure.eq_iff]
    simp only [← coe_iterateFrobenius, map_add]
    simp only [coe_iterateFrobenius, ← Function.iterate_add_apply]

lemma rootMap_transition (n m : ℕ) (h : n ≤ m) (x : A) :
    rootMap A p m (iterateFrobenius A p (m-n) x) = rootMap A p n x := by
  have hh := PerfectClosure.R.sound A p (m-n) n x
    (iterateFrobenius A p (m-n) x) (by rw [coe_iterateFrobenius])
  simpa only [Nat.sub_add_cancel h, rootMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] using hh.symm

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

open scoped ENNReal TensorProduct Classical DirectSum
namespace Lech.NormalizedLength

section BaseChange
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Module.Flat R S] [AddCommGroup M] [Module R M] [Module S M]
  [IsScalarTower R S M]

lemma length_span_le_baseChange (s : Set M) :
    Module.length S (Submodule.span S s) ≤
      Module.length R (Submodule.span R s) *
        Module.length S (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
  let f := (Submodule.span R s).subtype.liftBaseChange S
  have hf : f.range = Submodule.span S s := by
    rw [LinearMap.range_liftBaseChange, Submodule.range_subtype,
      Submodule.span_span_of_tower]
  rw [← IsLocalRing.length_baseChange R S (Submodule.span R s), ← hf]
  exact Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict

end BaseChange

 

structure Tower (L : Type*) [CommRing L] where
  ring : ℕ → Subring L
  mono : Monotone ring
  localRing : ∀ n, IsLocalRing (ring n)
  noetherian : ∀ n, IsNoetherianRing (ring n)
  exhaustive : ∀ x : L, ∃ n, x ∈ ring n
  weight : ℕ → ℝ≥0∞
  weight_ne_zero : ∀ n, weight n ≠ 0
  weight_ne_top : ∀ n, weight n ≠ ⊤
  local_inclusion : ∀ n m (h : n ≤ m), IsLocalHom (Subring.inclusion (mono h))
  flat : ∀ n m (h : n ≤ m),
    let : Algebra (ring n) (ring m) := (Subring.inclusion (mono h)).toAlgebra
    Module.Flat (ring n) (ring m)
  weight_mul_fiber : ∀ n m (h : n ≤ m),
    let : IsLocalRing (ring n) := localRing n
    weight m * (Module.length (ring m)
      ((ring m) ⧸ (IsLocalRing.maximalIdeal (ring n)).map
        (Subring.inclusion (mono h)))).toENNReal = weight n

namespace Tower
variable {L : Type*} [CommRing L] (T : Tower L)
attribute [instance] localRing noetherian

variable {M N : Type*} [AddCommGroup M] [Module L M]
  [AddCommGroup N] [Module L N]

 
noncomputable def stage (s : Finset M) (n : ℕ) : ℝ≥0∞ :=
  T.weight n * (Module.length (T.ring n) (Submodule.span (T.ring n) (s : Set M))).toENNReal

 
noncomputable def finiteLength (s : Finset M) : ℝ≥0∞ := ⨅ n, T.stage s n

 
noncomputable def length (M : Type*) [AddCommGroup M] [Module L M] : ℝ≥0∞ :=
  ⨆ s : Finset M, T.finiteLength s

lemma span_mono_stage {s : Set M} {n m : ℕ} (h : n ≤ m) :
    (Submodule.span (T.ring n) s : Set M) ⊆ Submodule.span (T.ring m) s := by
  let : Algebra (T.ring n) (T.ring m) := (Subring.inclusion (T.mono h)).toAlgebra
  let : IsScalarTower (T.ring n) (T.ring m) M :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact Submodule.span_le_restrictScalars (T.ring n) (T.ring m) s

lemma stage_antitone (s : Finset M) : Antitone (T.stage s) := by
  intro n m h
  let : Algebra (T.ring n) (T.ring m) := (Subring.inclusion (T.mono h)).toAlgebra
  let : IsScalarTower (T.ring n) (T.ring m) M :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsLocalHom (algebraMap (T.ring n) (T.ring m)) := T.local_inclusion n m h
  let : Module.Flat (T.ring n) (T.ring m) := T.flat n m h
  have hh := ENat.toENNReal_mono
    (length_span_le_baseChange (R := T.ring n) (S := T.ring m) (s : Set M))
  calc
    T.stage s m ≤ T.weight m *
        ((Module.length (T.ring n) (Submodule.span (T.ring n) (s : Set M))).toENNReal *
        (Module.length (T.ring m) ((T.ring m) ⧸
          (IsLocalRing.maximalIdeal (T.ring n)).map
            (Subring.inclusion (T.mono h)))).toENNReal) := by
      rw [ENat.toENNReal_mul] at hh
      exact mul_le_mul_right hh (T.weight m)
    _ = T.stage s n := by
      rw [mul_left_comm, T.weight_mul_fiber n m h]
      rw [mul_comm]
      rfl

lemma finiteLength_le_stage (s : Finset M) (n : ℕ) : T.finiteLength s ≤ T.stage s n :=
  iInf_le _ _

lemma finiteLength_le_length (s : Finset M) : T.finiteLength s ≤ T.length M := le_iSup _ s

lemma stage_image_le (f : M →ₗ[L] N) (s : Finset M) (n : ℕ) :
    T.stage (s.image f) n ≤ T.stage s n := by
  classical
  let g := (f.restrictScalars (T.ring n)).domRestrict
    (Submodule.span (T.ring n) (s : Set M))
  have hg : g.range = Submodule.span (T.ring n) (s.image f : Set N) := by
    rw [LinearMap.range_domRestrict, Submodule.map_span]
    simp
  unfold stage
  apply mul_le_mul_right
  apply ENat.toENNReal_mono
  rw [← hg]
  exact Module.length_le_of_surjective g.rangeRestrict g.surjective_rangeRestrict

lemma stage_image_eq (f : M →ₗ[L] N) (hf : Function.Injective f)
    (s : Finset M) (n : ℕ) : T.stage (s.image f) n = T.stage s n := by
  classical
  have h := (Submodule.equivMapOfInjective (f.restrictScalars (T.ring n)) hf
    (Submodule.span (T.ring n) (s : Set M))).length_eq
  rw [Submodule.map_span] at h
  unfold stage
  rw [Finset.coe_image]
  exact congrArg (fun a : ℕ∞ => T.weight n * a.toENNReal) h.symm

lemma finiteLength_image_le (f : M →ₗ[L] N) (s : Finset M) :
    T.finiteLength (s.image f) ≤ T.finiteLength s :=
  iInf_mono fun n => T.stage_image_le f s n

lemma finiteLength_image_eq (f : M →ₗ[L] N) (hf : Function.Injective f) (s : Finset M) :
    T.finiteLength (s.image f) = T.finiteLength s := by
  unfold finiteLength
  simp_rw [T.stage_image_eq f hf]

lemma length_le_of_injective (f : M →ₗ[L] N) (hf : Function.Injective f) :
    T.length M ≤ T.length N := by
  classical
  apply iSup_le
  intro s
  rw [← T.finiteLength_image_eq f hf s]
  exact T.finiteLength_le_length _

lemma length_le_of_surjective (f : M →ₗ[L] N) (hf : Function.Surjective f) :
    T.length N ≤ T.length M := by
  classical
  apply iSup_le
  intro t
  let s := t.image (Function.surjInv hf)
  have hs : s.image f = t := by
    ext x
    simp only [s, Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [Function.surjInv_eq hf] using hz
    · intro hx
      exact ⟨Function.surjInv hf x, ⟨x, hx, rfl⟩, Function.surjInv_eq hf x⟩
  rw [← hs]
  exact (T.finiteLength_image_le f s).trans (T.finiteLength_le_length s)

lemma length_eq_of_equiv (e : M ≃ₗ[L] N) : T.length M = T.length N :=
  le_antisymm (T.length_le_of_injective e e.injective)
    (T.length_le_of_injective e.symm e.symm.injective)

lemma stage_zero [Subsingleton M] (s : Finset M) (n : ℕ) : T.stage s n = 0 := by
  simp [stage, Module.length_eq_zero]

lemma length_zero [Subsingleton M] : T.length M = 0 := by
  simp [length, finiteLength, T.stage_zero]

variable {P : Type*} [AddCommGroup P] [Module L P]

lemma stage_add_le (f : N →ₗ[L] M) (g : M →ₗ[L] P)
    (hf : Function.Injective f) (hfg : ∀ x, g (f x) = 0)
    (s : Finset N) (t : Finset M) (n : ℕ) :
    T.stage s n + T.stage (t.image g) n ≤ T.stage (s.image f ∪ t) n := by
  let R := T.ring n
  let u := s.image f ∪ t
  let X := Submodule.span R (u : Set M)
  let Y := Submodule.span R (s : Set N)
  let G : X →ₗ[R] P := (g.restrictScalars R).domRestrict X
  have hY : ∀ x : N, x ∈ Y → f x ∈ X := by
    intro x hx
    have hh : Y.map (f.restrictScalars R) ≤ X := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro y ⟨z, hz, rfl⟩
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    exact hh ⟨x, hx, rfl⟩
  let F₀ : Y →ₗ[R] X := ((f.restrictScalars R).domRestrict Y).codRestrict X
    (fun x => hY x x.property)
  let F : Y →ₗ[R] G.ker := F₀.codRestrict G.ker (fun x => hfg x)
  have hF : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    apply hf
    exact congrArg (fun z : G.ker => ((z : X) : M)) h
  have ht : Submodule.span R (t.image g : Set P) ≤ G.range := by
    apply Submodule.span_le.mpr
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨⟨x, Submodule.subset_span (Finset.mem_union_right _ hx)⟩, rfl⟩
  have he : Module.length R X = Module.length R G.ker + Module.length R G.range := by
    exact Module.length_eq_add_of_exact G.ker.subtype G.rangeRestrict
      (Submodule.subtype_injective _) G.surjective_rangeRestrict
      (by rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict])
  have hb : Module.length R Y + Module.length R (Submodule.span R (t.image g : Set P)) ≤
      Module.length R X := by
    rw [he]
    exact add_le_add (Module.length_le_of_injective F hF)
      (Module.length_le_of_injective (Submodule.inclusion ht) (Submodule.inclusion_injective ht))
  have hb' := mul_le_mul_right (ENat.toENNReal_mono hb) (T.weight n)
  simpa only [stage, ENat.toENNReal_add, mul_add] using hb'

lemma finiteLength_add_le (f : N →ₗ[L] M) (g : M →ₗ[L] P)
    (hf : Function.Injective f) (hfg : ∀ x, g (f x) = 0)
    (s : Finset N) (t : Finset M) :
    T.finiteLength s + T.finiteLength (t.image g) ≤ T.finiteLength (s.image f ∪ t) := by
  unfold finiteLength
  rw [ENNReal.iInf_add_iInf (fun i j => ⟨max i j,
    add_le_add (T.stage_antitone s (le_max_left i j))
      (T.stage_antitone (t.image g) (le_max_right i j))⟩)]
  exact iInf_mono fun n => T.stage_add_le f g hf hfg s t n

lemma length_add_le (f : N →ₗ[L] M) (g : M →ₗ[L] P)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : ∀ x, g (f x) = 0) : T.length N + T.length P ≤ T.length M := by
  unfold length
  rw [ENNReal.iSup_add]
  apply iSup_le
  intro s
  rw [ENNReal.add_iSup]
  apply iSup_le
  intro t
  let u := t.image (Function.surjInv hg)
  have hu : u.image g = t := by
    simp only [u, Finset.image_image]
    simp only [Function.comp_def, Function.surjInv_eq hg, Finset.image_id']
  rw [← hu]
  exact (T.finiteLength_add_le f g hf hfg s u).trans (T.finiteLength_le_length _)

 

lemma stage_le_add_kernel (q : M →ₗ[L] N) (s k : Finset M) {n m : ℕ} (hnm : n ≤ m)
    (hk : Submodule.span (T.ring n) (k : Set M) =
      Submodule.span (T.ring n) (s : Set M) ⊓ (q.restrictScalars (T.ring n)).ker) :
    T.stage s m ≤ T.stage k m + T.stage (s.image q) n := by
  let R := T.ring n
  let S := T.ring m
  let : Algebra R S := (Subring.inclusion (T.mono hnm)).toAlgebra
  let : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsLocalHom (algebraMap R S) := T.local_inclusion n m hnm
  let : Module.Flat R S := T.flat n m hnm
  let X₀ := Submodule.span R (s : Set M)
  let X₁ := Submodule.span S (s : Set M)
  let U := Submodule.span S (k : Set M)
  let F : X₀ →ₗ[R] N := (q.restrictScalars R).domRestrict X₀
  let G : X₁ →ₗ[S] M ⧸ U := U.mkQ.domRestrict X₁
  have hu : U ≤ X₁ := by
    apply Submodule.span_le.mpr
    intro x hx
    have hx' : x ∈ Submodule.span R (k : Set M) := Submodule.subset_span hx
    rw [hk] at hx'
    exact T.span_mono_stage hnm hx'.1
  let L₀ : X₀ →ₗ[R] M ⧸ U := (U.mkQ.restrictScalars R).comp X₀.subtype
  have hvanish : F.ker ≤ L₀.ker := by
    intro x hx
    change U.mkQ (x : M) = 0
    apply (Submodule.Quotient.mk_eq_zero U).mpr
    apply T.span_mono_stage hnm
    rw [hk]
    exact ⟨x.property, hx⟩
  let H : (X₀ ⧸ F.ker) →ₗ[R] M ⧸ U := F.ker.liftQ L₀ hvanish
  let B : S ⊗[R] (X₀ ⧸ F.ker) →ₗ[S] M ⧸ U := H.liftBaseChange S
  have hB : B.range = G.range := by
    change (H.liftBaseChange S).range = G.range
    rw [LinearMap.range_liftBaseChange]
    change Submodule.span S (F.ker.liftQ L₀ hvanish).range = G.range
    rw [Submodule.range_liftQ]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro y ⟨x, rfl⟩
      exact ⟨⟨x, T.span_mono_stage hnm x.property⟩, rfl⟩
    · rw [LinearMap.range_domRestrict, Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      intro x hx
      exact Submodule.subset_span ⟨⟨x, Submodule.subset_span hx⟩, rfl⟩
  have htarget : Module.length S G.range ≤ Module.length S (S ⊗[R] (X₀ ⧸ F.ker)) := by
    rw [← hB]
    exact Module.length_le_of_surjective B.rangeRestrict B.surjective_rangeRestrict
  have hF : F.range = Submodule.span R (s.image q : Set N) := by
    rw [LinearMap.range_domRestrict, Submodule.map_span]
    simp
  have hquot : Module.length R (X₀ ⧸ F.ker) =
      Module.length R (Submodule.span R (s.image q : Set N)) := by
    rw [F.quotKerEquivRange.length_eq, hF]
  let ι : U →ₗ[S] X₁ := Submodule.inclusion hu
  have he : Function.Exact ι G.rangeRestrict := by
    rw [LinearMap.exact_iff, Submodule.range_inclusion, LinearMap.ker_rangeRestrict]
    ext x
    simp [G, LinearMap.mem_ker]
  have hadd : Module.length S X₁ = Module.length S U + Module.length S G.range :=
    Module.length_eq_add_of_exact ι G.rangeRestrict (Submodule.inclusion_injective hu)
      G.surjective_rangeRestrict he
  have hlen : Module.length S X₁ ≤ Module.length S U +
      Module.length R (Submodule.span R (s.image q : Set N)) *
      Module.length S (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
    rw [hadd]
    apply add_le_add_right
    convert htarget using 1
    all_goals try with_reducible_and_instances rfl
    rw [IsLocalRing.length_baseChange, hquot]
  have hh := mul_le_mul_right (ENat.toENNReal_mono hlen) (T.weight m)
  rw [ENat.toENNReal_add, ENat.toENNReal_mul, mul_add] at hh
  have hw : T.weight m *
      (Module.length S (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))).toENNReal =
      T.weight n := T.weight_mul_fiber n m hnm
  rw [mul_left_comm (T.weight m) _ _, hw, mul_comm _ (T.weight n)] at hh
  exact hh

lemma finiteLength_le_length_of_subset (s : Finset M) (Q : Submodule L M)
    (hs : (s : Set M) ⊆ Q) : T.finiteLength s ≤ T.length Q := by
  let t : Finset Q := s.attach.image (fun x : {x // x ∈ s} => (⟨x.1, hs x.2⟩ : Q))
  have ht : t.image Q.subtype = s := by
    ext x
    simp only [t, Finset.mem_image, Finset.mem_attach, true_and]
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact z.property
    · intro hx
      exact ⟨⟨x, hs hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  rw [← ht, T.finiteLength_image_eq Q.subtype Q.subtype_injective]
  exact T.finiteLength_le_length t

 
lemma finiteLength_le_length_kernel_add_stage (q : M →ₗ[L] N) (s : Finset M) (n : ℕ) :
    T.finiteLength s ≤ T.length q.ker + T.stage (s.image q) n := by
  have hfg : (Submodule.span (T.ring n) (s : Set M) ⊓
      (q.restrictScalars (T.ring n)).ker).FG :=
    (Submodule.fg_span s.finite_toSet).of_le inf_le_left
  obtain ⟨k, hk⟩ := hfg
  have hf : T.finiteLength s ≤ T.finiteLength k + T.stage (s.image q) n := by
    change T.finiteLength s ≤ (⨅ m, T.stage k m) + T.stage (s.image q) n
    rw [ENNReal.iInf_add]
    apply le_iInf
    intro m
    calc
      T.finiteLength s ≤ T.stage s (max n m) := T.finiteLength_le_stage _ _
      _ ≤ T.stage k (max n m) + T.stage (s.image q) n :=
        T.stage_le_add_kernel q s k (le_max_left n m) hk
      _ ≤ T.stage k m + T.stage (s.image q) n :=
        add_le_add_left (T.stage_antitone k (le_max_right n m)) _
  have hker : T.finiteLength k ≤ T.length q.ker := by
    apply T.finiteLength_le_length_of_subset k q.ker
    intro x hx
    have hx' := Submodule.subset_span (R := T.ring n) (s := (k : Set M)) hx
    rw [hk] at hx'
    exact hx'.2
  exact hf.trans (add_le_add_left hker _)

lemma length_le_kernel_add (q : M →ₗ[L] N) : T.length M ≤ T.length q.ker + T.length N := by
  apply iSup_le
  intro s
  have hs : T.finiteLength s ≤ T.length q.ker + T.finiteLength (s.image q) := by
    change T.finiteLength s ≤ T.length q.ker + (⨅ n, T.stage (s.image q) n)
    rw [ENNReal.add_iInf]
    exact le_iInf fun n => T.finiteLength_le_length_kernel_add_stage q s n
  exact hs.trans (add_le_add_right (T.finiteLength_le_length _) _)

 
theorem length_eq_kernel_add (q : M →ₗ[L] N) (hq : Function.Surjective q) :
    T.length M = T.length q.ker + T.length N := by
  apply le_antisymm (T.length_le_kernel_add q)
  exact T.length_add_le q.ker.subtype q q.ker.subtype_injective hq (fun x => x.property)

lemma length_eq_add_of_exact (f : P →ₗ[L] M) (q : M →ₗ[L] N)
    (hf : Function.Injective f) (hq : Function.Surjective q) (he : Function.Exact f q) :
    T.length M = T.length P + T.length N := by
  rw [T.length_eq_kernel_add q hq, LinearMap.exact_iff.mp he]
  congr 1
  exact (T.length_eq_of_equiv (LinearEquiv.ofInjective f hf)).symm

lemma length_prod : T.length (M × N) = T.length M + T.length N := by
  apply T.length_eq_add_of_exact (LinearMap.inl L M N) (LinearMap.snd L M N)
  · exact fun x y h => congrArg Prod.fst h
  · exact fun y => ⟨(0, y), rfl⟩
  · rw [LinearMap.exact_iff]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.snd_apply, LinearMap.mem_range,
      LinearMap.inl_apply]
    constructor
    · intro h
      exact ⟨x.1, Prod.ext rfl h.symm⟩
    · rintro ⟨y, rfl⟩
      rfl

lemma length_sup_le (U V : Submodule L M) :
    T.length (U ⊔ V : Submodule L M) ≤ T.length U + T.length V := by
  let f : U × V →ₗ[L] M := U.subtype.comp (LinearMap.fst L U V) +
    V.subtype.comp (LinearMap.snd L U V)
  have hf : f.range = U ⊔ V := by
    ext x
    simp only [LinearMap.mem_range, Submodule.mem_sup]
    constructor
    · rintro ⟨⟨u, v⟩, rfl⟩
      exact ⟨u, u.property, v, v.property, rfl⟩
    · rintro ⟨u, hu, v, hv, rfl⟩
      exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
  rw [← hf, ← T.length_prod]
  exact T.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict

lemma finite_subset_directed {ι : Type*} [Nonempty ι]
    (U : ι → Submodule L M) (hd : Directed (· ≤ ·) U)
    (hc : ∀ x : M, ∃ i, x ∈ U i) (s : Finset M) :
    ∃ i, (s : Set M) ⊆ U i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | @insert a s _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := hc a
    obtain ⟨k, hik, hjk⟩ := hd i j
    refine ⟨k, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hjk hj
    · exact hik (hi hx)

 
lemma length_eq_iSup_of_directed {ι : Type*} [Nonempty ι]
    (U : ι → Submodule L M) (hd : Directed (· ≤ ·) U)
    (hc : ∀ x : M, ∃ i, x ∈ U i) :
    T.length M = ⨆ i, T.length (U i) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    obtain ⟨i, hi⟩ := finite_subset_directed U hd hc s
    exact le_iSup_of_le i (T.finiteLength_le_length_of_subset s (U i) hi)
  · exact iSup_le fun i => T.length_le_of_injective (U i).subtype (U i).subtype_injective

lemma length_range_le (f : M →ₗ[L] N) : T.length f.range ≤ T.length M :=
  T.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict

lemma length_directed_iSup {ι : Type*} [Nonempty ι]
    (U : ι → Submodule L M) (hd : Directed (· ≤ ·) U) :
    T.length (⨆ i, U i : Submodule L M) = ⨆ i, T.length (U i) := by
  let W := ⨆ i, U i
  let V := fun i => (U i).comap W.subtype
  have hd' : Directed (· ≤ ·) V := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, Submodule.comap_mono hik, Submodule.comap_mono hjk⟩
  have hc : ∀ x : W, ∃ i, x ∈ V i := by
    intro x
    exact (Submodule.mem_iSup_of_directed U hd).mp x.property
  rw [T.length_eq_iSup_of_directed V hd' hc]
  apply iSup_congr
  intro i
  exact T.length_eq_of_equiv (Submodule.comapSubtypeEquivOfLe (le_iSup U i))

lemma length_bot : T.length (⊥ : Submodule L M) = 0 := T.length_zero

lemma length_top : T.length (⊤ : Submodule L M) = T.length M :=
  T.length_eq_of_equiv Submodule.topEquiv

 
theorem length_iSup_eq_zero {ι : Type*} (U : ι → Submodule L M)
    (hU : ∀ i, T.length (U i) = 0) : T.length (⨆ i, U i : Submodule L M) = 0 := by
  let V : Finset ι → Submodule L M := fun s => s.sup U
  have hd : Directed (· ≤ ·) V := fun s t =>
    ⟨s ∪ t, Finset.sup_mono Finset.subset_union_left,
      Finset.sup_mono Finset.subset_union_right⟩
  have hz : ∀ s, T.length (V s) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact T.length_bot
    | @insert a s _ ih =>
      change T.length ((insert a s).sup U : Submodule L M) = 0
      rw [Finset.sup_insert]
      apply le_antisymm _ bot_le
      calc
        T.length (U a ⊔ s.sup U : Submodule L M) ≤
            T.length (U a) + T.length (s.sup U : Submodule L M) := T.length_sup_le _ _
        _ = 0 := by rw [hU a, show T.length (s.sup U : Submodule L M) = 0 from ih, add_zero]
  have heq : (⨆ s, V s) = ⨆ i, U i := by
    apply le_antisymm
    · exact iSup_le fun s => Finset.sup_le fun i _ => le_iSup U i
    · refine iSup_le fun i => ?_
      have hi : V {i} = U i := by simp [V]
      rw [← hi]
      exact le_iSup V {i}
  rw [← heq, T.length_directed_iSup V hd]
  simp only [hz, iSup_const]


end Tower
end Lech.NormalizedLength
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechFactorizationMap
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
open scoped BigOperators
open scoped Classical


namespace Lech.UnitSection
open scoped TensorProduct
universe u v w
variable {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  [Module.FaithfullyFlat R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

def map (m : M) : R →ₗ[R] M := (LinearMap.id : R →ₗ[R] R).smulRight m

omit [Module.FaithfullyFlat R S] in
lemma compat (m : M) (e : S ⊗[R] M ≃ₗ[S] S) (u : Sˣ)
    (he : e (1 ⊗ₜ[R] m)=(u:S)) :
    e.toLinearMap.comp ((map m).baseChange S)=
      ((TensorProduct.AlgebraTensorModule.rid R S S) ≪≫ₗ LinearEquiv.smulOfUnit u).toLinearMap := by
  ext
  change e (1 ⊗ₜ[R] ((1:R) • m))=(u:S)*((1:R) • (1:S))
  simp only [one_smul, mul_one, he]

end Lech.UnitSection


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedLineBasisHasBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.LineBasisExtension
open scoped TensorProduct
universe u v w x y
variable {R : Type u} [CommRing R] {L : Type v} [CommRing L] [Algebra R L]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable (C : Type x) [CommRing C] [Algebra R C] [Algebra L C] [IsScalarTower R L C]
variable {S : Type y} [CommRing S] [Algebra R S]
 
def extend (e : L ≃ₗ[L] L ⊗[R] M) : C ≃ₗ[C] C ⊗[R] M :=
  (TensorProduct.AlgebraTensorModule.rid L C C).symm ≪≫ₗ TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) e ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R L C C M

 

def coefficients : L ⊗[R] S →ₐ[R] C ⊗[R] S :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom R L C) (AlgHom.id R S)
lemma coefficients_tmul (l : L) (s : S) : coefficients (R := R) (L := L) C (l ⊗ₜ[R] s)=
    algebraMap L C l ⊗ₜ[R] s := rfl

variable {N : Type w} [AddCommGroup N] [Module L N]
def transition (e f : L ≃ₗ[L] N) : Lˣ where
  val := e.symm (f 1)
  inv := f.symm (e 1)
  val_inv := by
    have he (r : L) : e r=r • e 1 := by simpa only [smul_eq_mul,mul_one] using e.map_smul r 1
    have hf (r : L) : f r=r • f 1 := by simpa only [smul_eq_mul,mul_one] using f.map_smul r 1
    apply e.injective
    rw [mul_comm,he,mul_smul,←he, e.apply_symm_apply,←hf,f.apply_symm_apply]
  inv_val := by
    have he (r : L) : e r=r • e 1 := by simpa only [smul_eq_mul,mul_one] using e.map_smul r 1
    have hf (r : L) : f r=r • f 1 := by simpa only [smul_eq_mul,mul_one] using f.map_smul r 1
    apply f.injective
    rw [mul_comm,hf,mul_smul,←hf,f.apply_symm_apply,←he,e.apply_symm_apply]
lemma transition_apply (e f : L ≃ₗ[L] N) (r : L) :
    e (r*(transition e f:L))=f r := by
  change e (r*e.symm (f 1))=f r
  rw [←smul_eq_mul,e.map_smul,e.apply_symm_apply,←f.map_smul,smul_eq_mul,mul_one]
end Lech.LineBasisExtension


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechSignedUnit
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
open scoped BigOperators
open scoped Classical


namespace Lech.LineBasisExtension
open scoped TensorProduct
universe u v w x
variable {R : Type u} [CommRing R] {L : Type v} [CommRing L] [Algebra R L]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable (C : Type x) [CommRing C] [Algebra R C] [Algebra L C] [IsScalarTower R L C]
def included : L ⊗[R] M →ₗ[R] C ⊗[R] M :=
  TensorProduct.map (IsScalarTower.toAlgHom R L C).toLinearMap (LinearMap.id : M →ₗ[R] M)
lemma included_tmul (l : L) (m : M) : included C (l ⊗ₜ[R] m)=algebraMap L C l ⊗ₜ[R] m := rfl
def coordinates (e : C ≃ₗ[C] C ⊗[R] M) : C ⊗[R] M →ₗ[R] C :=
  e.symm.toLinearMap.restrictScalars R
end Lech.LineBasisExtension


namespace Lech.LocalizationImageCover
open scoped TensorProduct
universe u v w
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {C : Type w} [CommRing C] [Algebra R C]
variable {ι : Type*} [Fintype ι] (q : ι → R)
def localMap (i : ι) (φ : Localization.Away (q i) →ₐ[R] C) :
    Localization.Away (q i) ⊗[R] M →ₗ[R] C ⊗[R] M :=
  TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[R] M)
omit [Fintype ι] in
lemma localMap_from (i : ι) (φ : Localization.Away (q i) →ₐ[R] C) (m : M) :
    localMap q i φ (1 ⊗ₜ[R] m)=1 ⊗ₜ[R] m := by
  change φ 1 ⊗ₜ[R] m=1 ⊗ₜ[R] m
  rw [map_one]
omit [Fintype ι] in
lemma localMap_clear (i : ι) (φ : Localization.Away (q i) →ₐ[R] C)
    (z : Localization.Away (q i) ⊗[R] M) :
    ∃ N : ℕ,∃ m : M,1 ⊗ₜ[R] m=(q i)^N • localMap q i φ z := by
  obtain ⟨⟨m,s⟩,h⟩ := IsLocalizedModule.surj (Submonoid.powers (q i))
    (TensorProduct.mk R (Localization.Away (q i)) M 1) z
  obtain ⟨N,hN⟩ := s.property
  refine ⟨N,m,?_⟩
  have hh := congrArg (localMap q i φ) h.symm
  change localMap q i φ (1 ⊗ₜ[R] m)=localMap q i φ ((s:R) • z) at hh
  rw [localMap_from,map_smul,←hN] at hh
  exact hh


omit [Fintype ι] in
lemma global_injective [Module.Flat R M] (h : Function.Injective (algebraMap R C)) :
    Function.Injective (TensorProduct.mk R C M 1) := by
  have hi := Module.Flat.rTensor_preserves_injective_linearMap (M := M) (Algebra.linearMap R C) h
  have he := hi.comp (TensorProduct.lid R M).symm.injective
  intro x y hxy
  apply he
  change algebraMap R C 1 ⊗ₜ[R] x=algebraMap R C 1 ⊗ₜ[R] y
  rw [map_one]
  exact hxy
end Lech.LocalizationImageCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootChartAtlasGlobalCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.PrimitiveRootModule
open Polynomial
open scoped TensorProduct
universe u
variable {A : Type u} [CommRing A]

abbrev chart (f : A[X]) := Localization.Away f

def coordinate (f : A[X]) : chart f := algebraMap A[X] (chart f) X

lemma eval_coordinate (f : A[X]) : (f.map (algebraMap A (chart f))).eval (coordinate f)=
    algebraMap A[X] (chart f) f := by
  rw [Polynomial.eval_map]
  have he : eval₂RingHom (algebraMap A (chart f)) (coordinate f)=algebraMap A[X] (chart f) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [coe_eval₂RingHom,eval₂_C]
      exact IsScalarTower.algebraMap_apply A A[X] (chart f) a
    · simp [coordinate]
  exact DFunLike.congr_fun he f

def valueUnit (f : A[X]) : (chart f)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := chart f) f).unit

lemma valueUnit_val (f : A[X]) : ((valueUnit f):chart f)=algebraMap A[X] (chart f) f :=
  (IsLocalization.Away.algebraMap_isUnit (S := chart f) f).unit_spec

lemma eval_valueUnit (f : A[X]) : (f.map (algebraMap A (chart f))).eval (coordinate f)=(valueUnit f:chart f) :=
  (eval_coordinate f).trans (valueUnit_val f).symm

end Lech.PrimitiveRootModule


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulHomologyMap
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


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex
universe u v
variable {R : Type u} [CommRing R]


noncomputable def scalarPowerHomotopy
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (r : R) (t d : ℕ) (htd : t ≤ d)
    (H : Homotopy (r^t • 𝟙 F) 0) : Homotopy (r^d • 𝟙 F) 0 := by
  simpa only [smul_zero, smul_smul, ← pow_add, Nat.sub_add_cancel htd] using H.smul (r^(d-t))



end Lech.Koszul
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechNatTrans
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


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex HomologicalComplex
universe u v
variable {R : Type u} [CommRing R]



lemma scalarCone_boundary_range (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (r : R) (n : ℤ) :
    LinearMap.range (((mappingCone.snd (r • 𝟙 F)).v n n (by omega)).hom.comp
      ((mappingCone (r • 𝟙 F)).d (n-1) n).hom) =
      LinearMap.range (r • (LinearMap.id : F.X n →ₗ[R] F.X n)) ⊔
        LinearMap.range (F.d (n-1) n).hom := by
  apply le_antisymm
  · rintro y ⟨x,rfl⟩
    have he := mappingCone.d_snd_v (r • 𝟙 F) (n-1) n (by omega)
    have hx := congrArg (fun f => f.hom x) he
    simp only [ModuleCat.hom_comp, ModuleCat.hom_add, LinearMap.add_apply,
      LinearMap.comp_apply] at hx
    change ((mappingCone.snd (r • 𝟙 F)).v n n (by omega)).hom
      (((mappingCone (r • 𝟙 F)).d (n-1) n).hom x) ∈ _
    rw [hx]
    exact Submodule.add_mem_sup
      ⟨_,rfl⟩ ⟨_,rfl⟩
  · apply sup_le
    · rintro y ⟨x,rfl⟩
      refine ⟨((mappingCone.inl (r • 𝟙 F)).v n (n-1) (by omega)).hom x, ?_⟩
      have he := mappingCone.inl_v_d (r • 𝟙 F) n (n-1) (n+1) (by omega) (by omega)
      have he' := congrArg (fun f => (f ≫ (mappingCone.snd (r • 𝟙 F)).v n n (by omega)).hom x) he
      simpa only [Preadditive.sub_comp, Category.assoc,
        mappingCone.inl_v_snd_v, mappingCone.inr_f_snd_v, comp_zero,
        sub_zero, Category.comp_id, ModuleCat.hom_comp, LinearMap.comp_apply,
        HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, ModuleCat.hom_smul,
        ModuleCat.hom_id, LinearMap.smul_apply] using he'
    · rintro y ⟨x,rfl⟩
      refine ⟨((mappingCone.inr (r • 𝟙 F)).f (n-1)).hom x, ?_⟩
      have he := mappingCone.inr_f_d (r • 𝟙 F) (n-1) n
      have he' := congrArg (fun f => (f ≫ (mappingCone.snd (r • 𝟙 F)).v n n (by omega)).hom x) he
      simpa only [Category.assoc, mappingCone.inr_f_snd_v, Category.comp_id,
        ModuleCat.hom_comp, LinearMap.comp_apply] using he'



lemma scalar_range_eq_ideal_smul (M : ModuleCat.{v} R) (r : R) :
    LinearMap.range (r • (LinearMap.id : M →ₗ[R] M)) =
      (Ideal.span {r}) • (⊤ : Submodule R M) := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_def,
    Submodule.map_top]
  rfl



lemma shortComplex_homologyMap_iso_of_augmentation
    {C : Type*} [Category C] [Abelian C] {S T : ShortComplex C} (φ : S ⟶ T)
    (hSg : S.g = 0) (hTf : T.f = 0) (hTg : T.g = 0)
    (he : (ShortComplex.mk S.f φ.τ₂ (by rw [← φ.comm₁₂, hTf, comp_zero])).Exact)
    [Epi φ.τ₂] : IsIso (ShortComplex.homologyMap φ) := by
  let hS := ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork S hSg
    (CokernelCofork.ofπ φ.τ₂ (by rw [← φ.comm₁₂, hTf, comp_zero])) he.gIsCokernel
  let hT := ShortComplex.LeftHomologyData.ofZeros T hTf hTg
  let γ : ShortComplex.LeftHomologyMapData φ hS hT :=
    { φK := φ.τ₂
      φH := 𝟙 _
      commi := by change φ.τ₂ ≫ 𝟙 _ = 𝟙 _ ≫ φ.τ₂; simp
      commf' := by
        exact φ.comm₁₂.symm.trans (congrArg (φ.τ₁ ≫ ·)
          (hTf.trans (ShortComplex.LeftHomologyData.ofZeros_f' T hTf hTg).symm))
      commπ := by rfl }
  apply (ShortComplex.quasiIso_iff φ).mp
  exact γ.quasiIso_iff.mpr (by change IsIso (𝟙 T.X₂); infer_instance)



end Lech.Koszul


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
variable {A B : Type*} [CommRing A] [IsReduced A] [CommRing B] [IsReduced B]
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

lemma rootMap_pow (n : ℕ) (a : A) :
    (rootMap A p n a)^(p^n) = PerfectClosure.of A p a := by
  exact (iterate_frobenius p n _).symm.trans
    (PerfectClosure.iterate_frobenius_mk A p n a)

end Lech.RootTower


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PerfectDomainStagesTensorTo
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


namespace Lech.PerfectDomainStages
open Lech.RootTower
open scoped ENNReal TensorProduct
variable (σ k D : Type*) [Fintype σ] [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [Algebra (MvPowerSeries σ k) D] [IsLocalHom (algebraMap (MvPowerSeries σ k) D)]
  [Module.Finite (MvPowerSeries σ k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]

local instance tensorToStagePowerSeriesIsDomain : IsDomain (MvPowerSeries σ k) :=
  NoZeroDivisors.to_isDomain _

end Lech.PerfectDomainStages


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SubalgebraStageFromBase
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


namespace Lech.PowerSeries
open MvPowerSeries
variable {σ R : Type*} [Fintype σ] [CommRing R]

lemma exists_positive {d : σ →₀ ℕ} (hd : d ≠ 0) : ∃ i, 0 < d i := by
  by_contra h
  push Not at h
  apply hd
  ext i
  exact Nat.eq_zero_of_le_zero (h i)

def pick (d : σ →₀ ℕ) : Option σ :=
  if h : d = 0 then none else some (Classical.choose (exists_positive h))

def divide (f : MvPowerSeries σ R) (i : σ) : MvPowerSeries σ R :=
  fun d => if pick (d + Finsupp.single i 1) = some i then coeff (d + Finsupp.single i 1) f else 0

end Lech.PowerSeries


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PowerSeriesFlatVariables
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






















namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open RingTheory.Sequence
universe u v
variable {R : Type u} [CommRing R]

noncomputable def singleModule (M : ModuleCat.{v} R) : CochainComplex (ModuleCat.{v} R) ℤ :=
  (single _ (.up ℤ) 0).obj M

end Lech.Koszul
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulConeFunctor
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
namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
variable {R : Type*} [CommRing R] {C : Type*} [Category C] [Abelian C]
  [CategoryTheory.Linear R C]

instance single_linear (j : ℤ) : Functor.Linear R (single C (.up ℤ) j) where
  map_smul f r := by
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : i = j
    · subst i
      simp [single_map_f_self]
    · apply (isZero_single_obj_X (.up ℤ) j _ i hi).eq_of_src

end Lech.Koszul


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

lemma restrictScalars_map_scalar (f : R →+* S) (a : R)
    (F : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map (f a • 𝟙 F) =
      a • 𝟙 (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj F) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  rfl



noncomputable def restrictScalarsHomologyIso (f : R →+* S)
    (F : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj F).homology i ≅
      (ModuleCat.restrictScalars f).obj (F.homology i) :=
  (F.sc i).mapHomologyIso (ModuleCat.restrictScalars f)


end Lech.Koszul


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
universe u
variable {R : Type u} [CommRing R]


def nullScalarIdeal (F : CochainComplex (ModuleCat.{u} R) ℤ) : Ideal R where
  carrier := {a | Nonempty (Homotopy (a • 𝟙 F) 0)}
  zero_mem' := by simpa using (show Nonempty (Homotopy (0 : F ⟶ F) 0) from ⟨Homotopy.refl _⟩)
  add_mem' := by
    rintro a b ⟨ha⟩ ⟨hb⟩
    change Nonempty (Homotopy ((a+b) • 𝟙 F) 0)
    simpa only [add_smul,add_zero] using (show Nonempty (Homotopy _ _) from ⟨ha.add hb⟩)
  smul_mem' := by
    rintro r a ⟨ha⟩
    change Nonempty (Homotopy ((r*a) • 𝟙 F) 0)
    simpa only [smul_eq_mul,mul_smul,smul_zero] using
      (show Nonempty (Homotopy _ _) from ⟨ha.smul r⟩)

end Lech.Koszul


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedLengthPiece
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


namespace Lech.Primary
open Filter
open scoped Topology
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

noncomputable def colength (I : Ideal R) (N : ℕ) : ℕ :=
  (Module.length R (R ⧸ I ^ N)).toNat

noncomputable def normalizedColength (I : Ideal R) (N : ℕ) : ℝ :=
  (Nat.factorial (Lech.dimension R) : ℝ) * (colength I N : ℝ) / (N : ℝ) ^ Lech.dimension R

noncomputable def multiplicity (I : Ideal R) : ℝ :=
  Filter.limUnder atTop (normalizedColength I)

end Lech.Primary


open CategoryTheory
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TowerRestrictedLength
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
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory
attribute [local instance] Classical.propDecidable
namespace Lech.NormalizedLength.Tower
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
universe u v
variable {P C : Type u} [CommRing P] [CommRing C]
  (T : Tower P) (f : P →+* C)

 

lemma restrictedLength_zero_of_ranges {ι : Type v} {M : ModuleCat.{u} C}
    (G : ι → ModuleCat.{u} C) (φ : ∀ i, G i ⟶ M)
    (hG : ∀ i, T.length ((ModuleCat.restrictScalars f).obj (G i)) = 0)
    (hspan : (⨆ i, ((ModuleCat.restrictScalars f).map (φ i)).hom.range) = ⊤) :
    T.length ((ModuleCat.restrictScalars f).obj M) = 0 := by
  classical
  let U := fun i => ((ModuleCat.restrictScalars f).map (φ i)).hom.range
  have hU : ∀ i, T.length (U i) = 0 := fun i =>
    le_antisymm ((T.length_range_le _).trans_eq (hG i)) bot_le
  have ht := T.length_iSup_eq_zero U hU
  rw [show (⨆ i, U i) = ⊤ from hspan,T.length_top] at ht
  exact ht

lemma restrictedLength_directSum_zero {ι : Type u}
    (G : ι → Type u) [∀ i, AddCommGroup (G i)] [∀ i, Module C (G i)]
    (hG : ∀ i, T.length ((ModuleCat.restrictScalars f).obj (ModuleCat.of C (G i))) = 0) :
    T.length ((ModuleCat.restrictScalars f).obj (ModuleCat.of C (⨁ i, G i))) = 0 := by
  classical
  apply T.restrictedLength_zero_of_ranges f (fun i => ModuleCat.of C (G i))
    (fun i => ModuleCat.ofHom (DirectSum.lof C ι G i)) hG
  apply Submodule.eq_top_iff'.mpr
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact Submodule.zero_mem _
  | of i x => exact Submodule.mem_iSup_of_mem i ⟨x,rfl⟩
  | add x y hx hy => exact Submodule.add_mem _ hx hy

lemma restrictedLength_directLimit_zero {ι : Type u} [Preorder ι]
    [Nonempty ι] [IsDirectedOrder ι]
    (G : ι → Type u) [∀ i, AddCommGroup (G i)] [∀ i, Module C (G i)]
    (g : ∀ i j, i ≤ j → G i →ₗ[C] G j)
    (hG : ∀ i, T.length ((ModuleCat.restrictScalars f).obj (ModuleCat.of C (G i))) = 0) :
    T.length ((ModuleCat.restrictScalars f).obj
      (ModuleCat.of C (Module.DirectLimit G g))) = 0 := by
  classical
  apply T.restrictedLength_zero_of_ranges f (fun i => ModuleCat.of C (G i))
    (fun i => ModuleCat.ofHom (Module.DirectLimit.of C ι G g i)) hG
  apply Submodule.eq_top_iff'.mpr
  intro x
  obtain ⟨i,y,hy⟩ := Module.DirectLimit.exists_of (show Module.DirectLimit G g from x)
  exact Submodule.mem_iSup_of_mem i ⟨y,hy⟩

lemma restrictedLength_iSup_zero {ι : Type v} {M : Type u}
    [AddCommGroup M] [Module C M] (U : ι → Submodule C M)
    (hU : ∀ i, T.length ((ModuleCat.restrictScalars f).obj (ModuleCat.of C (U i))) = 0) :
    T.length ((ModuleCat.restrictScalars f).obj
      (ModuleCat.of C (⨆ i, U i : Submodule C M))) = 0 := by
  classical
  let : Algebra P C := f.toAlgebra
  let : Module P M := Module.compHom M f
  let : IsScalarTower P C M := ⟨fun a b x => by
    change (f a*b) • x = f a • b • x
    exact mul_smul _ _ _⟩
  have hz := T.length_iSup_eq_zero (fun i => (U i).restrictScalars P) (by
    intro i
    exact hU i)
  rw [← Submodule.restrictScalars_iSup P U] at hz
  exact hz
end Lech.NormalizedLength.Tower


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusTensorStage
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
open TensorProduct
namespace Lech.PerfectDomainStages
open Lech.RootTower CategoryTheory
universe u
variable (σ : Type) (k D : Type u) [Fintype σ] [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [Algebra (MvPowerSeries σ k) D] [IsLocalHom (algebraMap (MvPowerSeries σ k) D)]
  [Module.Finite (MvPowerSeries σ k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
local instance instIsDomainMvPowerSeries_solutions : IsDomain (MvPowerSeries σ k) := NoZeroDivisors.to_isDomain _

end Lech.PerfectDomainStages

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

namespace Lech.PerfectDomainStages
open Lech.RootTower
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
local instance frobeniusComplexStagePowerSeriesIsDomain : IsDomain (MvPowerSeries (Fin h) k) :=
  NoZeroDivisors.to_isDomain _

end Lech.PerfectDomainStages

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LinearNormalization
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace Lech.LinearNormalization
universe u v
variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]


def linearChange {N : ℕ} (a : Fin (N+1) → k) :
    MvPolynomial (Fin (N+1)) k →ₐ[k] MvPolynomial (Fin (N+1)) k :=
  aeval (Fin.cons (C (a 0)*X 0) (fun i => X i.succ + C (a i.succ)*X 0))

end Lech.LinearNormalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NumericalSupport
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Lech.Numerical
open Polynomial

noncomputable def H (h : ℕ) : Polynomial ℝ :=
  ∏ i ∈ Finset.range h, (X + C ((i : ℝ) + 1))

lemma H_eval_zero_at (h i : ℕ) (hi : i < h) : (H h).eval (-((i : ℝ) + 1)) = 0 := by
  unfold H
  rw [eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hi) (by simp)

lemma derivative_root_exists (n : ℕ) (j : Fin n) :
    ∃ ρ : ℝ, -((j.val : ℝ) + 2) < ρ ∧ ρ < -((j.val : ℝ) + 1) ∧
      (H (n + 1)).derivative.eval ρ = 0 := by
  have hleft : (H (n + 1)).eval (-((j.val : ℝ) + 2)) = 0 := by
    have h := H_eval_zero_at (n + 1) (j.val + 1) (by omega)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    push_cast
    ring
  have hright := H_eval_zero_at (n + 1) j.val (by omega)
  obtain ⟨ρ, hρ, hd⟩ := exists_deriv_eq_zero (f := (H (n+1)).eval)
    (show -((j.val : ℝ) + 2) < -((j.val : ℝ) + 1) by linarith)
    (H (n+1)).continuous.continuousOn (hleft.trans hright.symm)
  exact ⟨ρ, hρ.1, hρ.2, by simpa only [Polynomial.deriv] using hd⟩

noncomputable def ρ (n : ℕ) (j : Fin n) : ℝ :=
  (derivative_root_exists n j).choose

noncomputable def roundedRoot (n s : ℕ) (j : Fin n) : ℤ :=
  ⌊(s : ℝ) * ρ n j⌋

noncomputable def P (n : ℕ) (x : ℝ) : ℝ := ∏ j : Fin n, (x - ρ n j)

noncomputable def bound (n : ℕ) : ℝ := (2 * (n : ℝ) + 4) ^ n

noncomputable def Ps (n s : ℕ) (x : ℝ) : ℝ :=
  ∏ j : Fin n, (x - (roundedRoot n s j : ℝ) / s)

noncomputable def normalizedLayer (n i s : ℕ) : ℝ :=
  (1 / s) * ∑ k ∈ Finset.range (i*s), Ps n s (-(i : ℝ) + k / s)


noncomputable def layer (n i s : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (i*s), ∏ j : Fin n,
    ((k : ℝ) - (i : ℝ)*(s : ℝ) - (roundedRoot n s j : ℝ))

end Lech.Numerical

namespace Lech.Numerical
 
def GoodRoots (n s : ℕ) : Prop := ∀ j : Fin n,
  -((j.val:ℝ)+2)*s  <  (roundedRoot n s j:ℝ) ∧
    (roundedRoot n s j:ℝ)  <  -((j.val:ℝ)+1)*s



end Lech.Numerical

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrimeFiltrationSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.PrimeFiltration
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
 
inductive Above : Submodule R M → Prop
  | top : Above ⊤
  | cons (I J : Submodule R M) (hIJ : I ≤ J) (p : Ideal R) (hp : p.IsPrime)
      (e : Nonempty ((J.map I.mkQ) ≃ₗ[R] R ⧸ p)) (tail : Above J) : Above I

end Lech.PrimeFiltration

namespace Lech.PrimeFiltration
open Filter IsLocalRing
open scoped Topology
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
local instance quotient_local (p : Ideal R) [p.IsPrime] : IsLocalRing (R ⧸ p) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective

noncomputable def contribution (I p : Ideal R) : ℝ := by
  classical
  exact if hp : p.IsPrime then
    letI : p.IsPrime := hp
    if Lech.dimension (R ⧸ p) = Lech.dimension R then
      Lech.Primary.multiplicity (I.map (Ideal.Quotient.mk p)) /
        ((Lech.dimension R).factorial : ℝ) else 0
  else 0

end Lech.PrimeFiltration

namespace Lech.PrimeFiltration
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
inductive Factors : Submodule R M → List (Ideal R) → Prop
  | top : Factors ⊤ []
  | cons (N J : Submodule R M) (hNJ : N ≤ J) (p : Ideal R) (hp : p.IsPrime)
      (e : Nonempty ((J.map N.mkQ) ≃ₗ[R] R ⧸ p)) {ps : List (Ideal R)}
      (tail : Factors J ps) : Factors N (p::ps)

open scoped TensorProduct

open Filter IsLocalRing
open scoped Topology
end Lech.PrimeFiltration

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootLayers
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.LocalPrincipal
universe u v w
variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
  {M : Type w} [AddCommGroup M] [Module B M] [Module R M] [IsScalarTower R B M]
  (I : Ideal R) {ι : Type*} (z : ι → R) (hz : Ideal.span (Set.range z)=I)
  (k : ι) (q : ι → B) (hq : ∀ j, algebraMap R B (z k)*q j=algebraMap R B (z j))

include hz hq in
lemma smul_top_eq_range :
    I • (⊤ : Submodule R M) = ((z k) • (LinearMap.id : M →ₗ[R] M)).range := by
  apply le_antisymm
  · apply Submodule.smul_le.mpr
    intro a ha x _
    rw [←hz] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨j,rfl⟩ := ha
        refine ⟨q j • x,?_⟩
        change z k • (q j • x) = z j • x
        rw [←IsScalarTower.algebraMap_smul B (z k),←mul_smul,hq,IsScalarTower.algebraMap_smul]
    | zero => simpa only [zero_smul] using (LinearMap.range ((z k) • (LinearMap.id : M →ₗ[R] M))).zero_mem
    | add a b ha hb ia ib =>
        rw [add_smul]
        exact Submodule.add_mem _ ia ib
    | smul a b hb ib =>
        rw [smul_eq_mul,mul_smul]
        exact Submodule.smul_mem _ a ib
  · rintro _ ⟨x,rfl⟩
    exact Submodule.smul_mem_smul (hz ▸ Ideal.subset_span ⟨k,rfl⟩) Submodule.mem_top
end Lech.LocalPrincipal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootStageQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ENNReal
namespace Lech.PerfectDomainStages
open Lech.RootTower
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
local instance rootStageQuotientPowerSeriesIsDomain : IsDomain (MvPowerSeries (Fin h) k) :=
  NoZeroDivisors.to_isDomain _

end Lech.PerfectDomainStages

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootUlrichModule
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace Lech.ModuleDescent
universe u v w w' z
variable {A : Type u} {B : Type v} {M : Type w} {L : Type w'} {ι : Type z}
  [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]
  [AddCommGroup L] [Module B L] [Module.FaithfullyFlat A B]

lemma exists_basis_of_baseChange (g : ι → M) (E : B ⊗[A] M ≃ₗ[B] L)
    (b : Module.Basis ι B L) (hb : ∀ i,E (1 ⊗ₜ[A] g i)=b i) :
    ∃ c : Module.Basis ι A M, ∀ i,c i=g i := by
  classical
  let q := Finsupp.linearCombination A g
  let b₀ : Module.Basis ι A (ι →₀ A) := Finsupp.basisSingleOne
  have he : E.toLinearMap.comp (q.baseChange B)=
      ((b₀.baseChange B).equiv b (Equiv.refl ι)).toLinearMap := by
    apply (b₀.baseChange B).ext
    intro i
    change E ((q.baseChange B) ((b₀.baseChange B) i))=
      ((b₀.baseChange B).equiv b (Equiv.refl ι)) ((b₀.baseChange B) i)
    rw [Module.Basis.equiv_apply,Module.Basis.baseChange_apply,LinearMap.baseChange_tmul]
    simpa [q,b₀] using hb i
  have hqB : Function.Bijective (q.baseChange B) := by
    have hh' : Function.Bijective (E.toLinearMap.comp (q.baseChange B)) := by
      rw [he]
      exact ((b₀.baseChange B).equiv b (Equiv.refl ι)).bijective
    exact (Function.Bijective.of_comp_iff' E.bijective (q.baseChange B)).mp hh'
  have hq : Function.Bijective q :=
    (Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B q).mp hqB
  let c : Module.Basis ι A M := Module.Basis.ofRepr (LinearEquiv.ofBijective q hq).symm
  refine ⟨c,fun i => ?_⟩
  change q (Finsupp.single i 1)=g i
  simp [q]
end Lech.ModuleDescent

end

end OAI
end


