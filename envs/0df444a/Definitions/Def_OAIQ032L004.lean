-- Prove2me | Definitions.Def_OAIQ032L004
-- name    : OAIQ032L004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:43:23.773625+00:00
-- url     : https://prove2.me/theorems/94954656-ee7e-4207-b229-b741ecfffed9
-- title:
--   Definitions bundle OAIQ032L004 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 83 declarations of OpenAI's Lean: 45 definitions, 7 instances and 31 theorems. The definitions and types are `OAI.Lech.FrobeniusGrowth.powerIdeal`, `OAI.Lech.FrobeniusIntermediate.frobeniusComplex_order_iso`, `OAI.Lech.FrobeniusIntermediate.frobeniusModule_order_iso`, `OAI.Lech.FrobeniusIntermediate.powerMap`, `OAI.Lech.FrobeniusModule`, `OAI.Lech.GradedLineBasis.HasBasis`, `OAI.Lech.GradedLineBasis.cast`, `OAI.Lech.GradedLineBasis.subgroup`, `OAI.Lech.Grading.MonomialIndex`, `OAI.Lech.Grading.homogeneousEquiv`, `OAI.Lech.Grading.indexEquiv`, `OAI.Lech.Grading.projection`, `OAI.Lech.Grading.step`, `OAI.Lech.Grading.subDecompose`, `OAI.Lech.Grading.subDecomposition`, `OAI.Lech.Grading.subPiece`, `OAI.Lech.Grading.subPieceMap`, `OAI.Lech.Homogeneous.awayAddCommGroup`, `OAI.Lech.HomogeneousEval.evaluate`, `OAI.Lech.IdealFiltered.order`, `OAI.Lech.IdealFiltered.subcomplex`, `OAI.Lech.IdealFiltered.subcomplexMap`, `OAI.Lech.IdealFiltered.tensorComplex`, `OAI.Lech.IdealFiltered.tensorMap`, `OAI.Lech.IdealFiltered.term`, `OAI.Lech.IdealFiltration.Piece`, `OAI.Lech.IdealFiltration.level`, `OAI.Lech.IdealFiltration.next`, `OAI.Lech.IdealFiltration.transition`, `OAI.Lech.IdealGraded.evaluate`, `OAI.Lech.ProductSourceCover.projectiveRemainder`, `OAI.Lech.ProjectiveCoefficientChart.Ambient`, `OAI.Lech.ProjectiveCoefficientChart.Chart`, `OAI.Lech.ProjectiveCoefficientChart.coordinate`, `OAI.Lech.ProjectiveCoefficientChart.dehomogenize`, `OAI.Lech.ProjectiveCoefficientChart.evaluate`, `OAI.Lech.ProjectiveCoefficientChart.grading`, `OAI.Lech.ProjectiveRoot.Ring`, `OAI.Lech.ProjectiveRoot.chartAlgebra`, `OAI.Lech.ProjectiveRoot.chartMap` and 5 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_AlternatingCechPost`, `Multiplicity_FrobeniusIntermediatePowerMap`, `Multiplicity_FrobeniusModule`, `Multiplicity_FrobeniusOrderTransfer`, `Multiplicity_GradedLineBasisHasBasis`, `Multiplicity_HomogeneousEval`, `Multiplicity_IdealFilteredComplex`, `Multiplicity_IdealFilteredHomotopy`, `Multiplicity_IdealGradedRing`, `Multiplicity_IdealQuotientFunctor`, `Multiplicity_IntermediateTensorLength`, `Multiplicity_LechBoundedEquiv`, `Multiplicity_LechHomogeneousEval`, `Multiplicity_LechLengthLe`, `Multiplicity_LechLevel`, `Multiplicity_ProductSourceCoverRootSigned`, `Multiplicity_RestrictedPolynomialImageCechComparisonHomology`, `Multiplicity_RobertsOrderTransfer`, `Multiplicity_RootChartAtlasGlobalCoefficient`, `Multiplicity_RootOverlap`, `Multiplicity_RootRestriction`, `Multiplicity_RootTowerLengthEq`, `Multiplicity_RootTowerRemainderExponent`, `Multiplicity_ScalarCechComparison`, `Multiplicity_ScalarExtensionHomotopy`, `Multiplicity_SeparableOrderNormalizedLength`, `Multiplicity_TraceConductorPerfectOrder`.
--
--   **Imports.** It imports the published bundle `Def_DuttaDomain`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L012`, `OAIQ032L013`, `OAIQ032L014`, `OAIQ032L015`, `OAIQ032L016` and `OAIQ032L018`; the statements `OAI.Lech.CharP.dutta_limit_from_perfection`, `OAI.Lech.CharP.perfection_complex_value`, `OAI.Lech.CharP.real_frobeniusModule_limit`, `OAI.Lech.FrobeniusIntermediate.exists_positive_module_rank_transfer`, `OAI.Lech.FrobeniusIntermediate.frobenius_homology_order_transfer`, `OAI_Lech_complex_estimate_basis`, `OAI.Lech.exists_frobenius_tensor_transfer`, `OAI.Lech.exists_scalar_extension_homology_bound`, `OAI.Lech.finiteHomology_extendScalars` and `OAI.Lech.frobeniusModule_finiteLength`; the proofs of `OAI.Lech.CharP.dutta_lower_bound_infinite_perfect`, `OAI.Lech.CharP.real_frobeniusModule_limit`, `OAI.Lech.FrobeniusGrowth.frobenius_error_tendstoENNReal`, `OAI.Lech.FrobeniusIntermediate.exists_positive_module_rank_transfer`, `OAI.Lech.dutta_dimension_zero`, `OAI.Lech.exists_frobenius_tensor_transfer` and `OAI.Lech.frobeniusModule_finiteLength`.
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
namespace Lech
universe u
variable {R : Type u} [CommRing R]
namespace IdealFiltration

def level (I J : Ideal R) (n : ℕ) : Ideal R := I ^ n ⊔ J

def next (I J : Ideal R) (n : ℕ) : Submodule R (level I J n) :=
  Submodule.comap (level I J n).subtype (level I J (n + 1))

abbrev Piece (I J : Ideal R) (n : ℕ) := level I J n ⧸ next I J n

lemma level_succ_le (I J : Ideal R) (n : ℕ) : level I J (n + 1) ≤ level I J n :=
  sup_le_sup_right (Ideal.pow_le_pow_right (Nat.le_succ n)) _

def transition (I J : Ideal R) (n : ℕ) :
    (R ⧸ level I J (n + 1)) →ₗ[R] R ⧸ level I J n :=
  (level I J (n + 1)).mapQ (level I J n) LinearMap.id (level_succ_le I J n)

end IdealFiltration
end Lech

open CategoryTheory
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


namespace Lech.Grading
open DirectSum
variable {R M N ι : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [DecidableEq ι]
variable (G : ι → Submodule R M) [Decomposition G]
variable (f : M →ₗ[R] N)

variable (P : Submodule R M)

def subPiece (i : ι) : Submodule R P := Submodule.comap P.subtype (G i)

def subPieceMap (i : ι) : subPiece G P i →ₗ[R] G i :=
  { toFun := fun x => ⟨x.val.val, x.property⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

def subDecompose (hP : P.IsHomogeneous G) : P →ₗ[R] ⨁ i, subPiece G P i where
  toFun x :=
    { toFun := fun i => ⟨⟨decompose G x i, hP i x.property⟩, (decompose G x i).property⟩
      support' := (decompose G x).support'.map fun s =>
        ⟨s.val, fun i => (s.property i).imp id (fun hz => by
          apply Subtype.ext
          apply Subtype.ext
          change (decompose G x i : M) = 0
          exact congrArg (fun y : G i => (y : M)) hz)⟩ }
  map_add' x y := by
    apply DFinsupp.ext
    intro i
    apply Subtype.ext
    apply Subtype.ext
    change (decompose G ((x : M) + (y : M)) i : M) =
      (decompose G x i : M) + (decompose G y i : M)
    exact congrArg (fun z : G i => (z : M)) (DFunLike.congr_fun (map_add (decomposeAddEquiv G) (x : M) (y : M)) i)
  map_smul' a x := by
    apply DFinsupp.ext
    intro i
    apply Subtype.ext
    apply Subtype.ext
    change (decompose G (a • (x : M)) i : M) = a • (decompose G x i : M)
    exact congrArg (fun z : G i => (z : M)) (DFunLike.congr_fun (decompose_smul G a x) i)

@[simp] lemma subDecompose_lmap (hP : P.IsHomogeneous G) (x : P) :
    DirectSum.lmap (subPieceMap G P) (subDecompose G P hP x) = decompose G x := by
  apply DFinsupp.ext
  intro i
  rfl

omit [Decomposition G] in
lemma sub_lmap_recompose :
    P.subtype.comp (DirectSum.coeLinearMap (subPiece G P)) =
      (DirectSum.coeLinearMap G).comp (DirectSum.lmap (subPieceMap G P)) := by
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, DirectSum.lmap_lof]
  rfl

@[instance_reducible]
noncomputable def subDecomposition (hP : P.IsHomogeneous G) :
    Decomposition (subPiece G P) :=
  Decomposition.ofLinearMap (subPiece G P) (subDecompose G P hP)
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have h := DFunLike.congr_fun (sub_lmap_recompose G P) (subDecompose G P hP x)
      simp only [LinearMap.comp_apply, subDecompose_lmap] at h
      exact h.trans ((decompose G).symm_apply_apply x))
    (by
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
      apply DFinsupp.ext
      intro j
      apply Subtype.ext
      apply Subtype.ext
      change (decompose G (x.val : M) j : M) = ((DirectSum.of (fun i => ↥(subPiece G P i)) i x) j : M)
      have hx : ((x : P) : M) ∈ G i := x.property
      rw [decompose_of_mem G hx]
      by_cases hij : i = j
      · subst j
        simp
      · simp [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij)])


end Lech.Grading


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedRing
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


namespace Lech.Homogeneous


open HomogeneousLocalization SetLike Graded
open CategoryTheory CategoryTheory.Limits
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) (H : ℕ → Submodule R B)
  [GradedAlgebra G] [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)
  {f : A} {d : ℕ} (hf : f ∈ G d)

local instance awayAddCommGroup (f : A) : AddCommGroup (Away G f) :=
  (inferInstance : CommRing (Away G f)).toAddCommGroup


end Lech.Homogeneous


namespace Lech.Grading
open MvPolynomial
variable (S : Type*) [CommRing S]
def MonomialIndex (h n : ℕ) := {d : Fin h →₀ ℕ // d.degree = n}
noncomputable def indexEquiv (h n : ℕ) : MonomialIndex h n ≃ Sym (Fin h) n :=
  (Sym.equivNatSum (Fin h) n).symm
noncomputable instance indexFintype (h n : ℕ) : Fintype (MonomialIndex h n) :=
  Fintype.ofEquiv (Sym (Fin h) n) (indexEquiv h n).symm

noncomputable def homogeneousEquiv (h n : ℕ) :
    homogeneousSubmodule (Fin h) S n ≃ₗ[S] (MonomialIndex h n → S) :=
  (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported (Fin h) S n)).trans
    ((AddMonoidAlgebra.supportedEquivFinsupp (R := S) (S := S) {d : Fin h →₀ ℕ | d.degree=n}).trans
      (Finsupp.linearEquivFunOnFinite S S (MonomialIndex h n)))
end Lech.Grading

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RestrictedPolynomialImageCechComparisonHomology
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


namespace Lech.IdealGraded
open Polynomial DirectSum
variable {R : Type*} [CommRing R] (I : Ideal R)


def evaluate : reesAlgebra I →ₐ[R] R :=
  (Polynomial.aeval (1:R)).comp (reesAlgebra I).val

end Lech.IdealGraded


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
namespace Lech.UniversalCoefficientChart
open Polynomial
universe u v
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
 
abbrev Ring := MvPolynomial {j : Fin (n+1) // j ≠ k} R

def coefficient (j : Fin (n+1)) : Ring R n k := if h : j=k then 1 else MvPolynomial.X ⟨j,h⟩

lemma coefficient_self : coefficient R n k k=1 := by simp [coefficient]
lemma coefficient_other (j : {j : Fin (n+1) // j ≠ k}) :
    coefficient R n k j=MvPolynomial.X j := by simp [coefficient,j.property]
end Lech.UniversalCoefficientChart


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverRootSigned
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


namespace Lech.ProjectiveCoefficientChart
open MvPolynomial HomogeneousLocalization
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
attribute [local instance] MvPolynomial.gradedAlgebra
abbrev grading := homogeneousSubmodule (Fin (n+1)) R
abbrev Chart := Away (grading R n) (X k)
abbrev Ambient := Localization.Away (X (R:=R) k)
def coordinate (j : Fin (n+1)) : Chart R n k :=
  Away.mk (grading R n) (isHomogeneous_X R k) 1 (X j) (by simpa using isHomogeneous_X R j)
def evaluate : MvPolynomial (Fin (n+1)) R →ₐ[R] UniversalCoefficientChart.Ring R n k :=
  MvPolynomial.aeval (UniversalCoefficientChart.coefficient R n k)
def dehomogenize : Ambient R n k →ₐ[R] UniversalCoefficientChart.Ring R n k :=
  IsLocalization.Away.liftAlgHom (X k) (f:=evaluate R n k)
    (by simp [evaluate,UniversalCoefficientChart.coefficient_self])
lemma coordinate_val (j : Fin (n+1)) :
    (coordinate R n k j).val=Localization.mk (X j) ⟨X k,by exact ⟨1,by simp⟩⟩ := by
  change Localization.mk (X j) ⟨X k ^ 1,by exact ⟨1,rfl⟩⟩ = _
  simp only [pow_one]
end Lech.ProjectiveCoefficientChart

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechHomogeneousEval
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
namespace Lech
open MvPolynomial
open scoped BigOperators
universe u v w
variable {R : Type u} [CommSemiring R] {S : Type v} [CommSemiring S] {ι : Type w}
lemma homogeneous_eval_scale (f : R →+* S) (g : ι → S) (t : S)
    {p : MvPolynomial ι R} {n : ℕ} (hp : p.IsHomogeneous n) :
    eval₂ f (fun i => t*g i) p=t^n*eval₂ f g p := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [eval₂_add,ihp,ihq,mul_add]
  | monomial d r hd =>
    simp only [eval₂_monomial,mul_pow,Finsupp.prod,Finset.prod_mul_distrib]
    have hd' : ∑ i ∈ d.support,d i=n := by
      simpa only [Finsupp.weight_apply,Finsupp.sum,Pi.one_apply,smul_eq_mul,mul_one] using hd
    rw [Finset.prod_pow_eq_pow_sum,hd']
    ring
end Lech


namespace Lech.ProjectiveCoefficientChart

section
open MvPolynomial HomogeneousLocalization
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
attribute [local instance] MvPolynomial.gradedAlgebra
lemma coordinate_self : coordinate R n k k=1 := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (X k))
  rw [coordinate_val,HomogeneousLocalization.val_one,Localization.mk_eq_mk']
  exact IsLocalization.mk'_self' (Ambient R n k)
lemma coordinate_mul (j : Fin (n+1)) :
    algebraMap (MvPolynomial (Fin (n+1)) R) (Ambient R n k) (X k)*
      (coordinate R n k j).val=algebraMap (MvPolynomial (Fin (n+1)) R) (Ambient R n k) (X j) := by
  rw [coordinate_val,Localization.mk_eq_mk']
  exact IsLocalization.mk'_spec' (Ambient R n k) (X j) (⟨X k,⟨1,by simp⟩⟩ : Submonoid.powers (X (R:=R) k))
end


open MvPolynomial HomogeneousLocalization
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
end Lech.ProjectiveCoefficientChart


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

instance powerSeriesCharP (p : ℕ) [CharP R p] : CharP (MvPowerSeries σ R) p :=
  charP_of_injective_ringHom (C_injective (σ := σ) (R := R)) p

end Lech.RootTower

open scoped TensorProduct
open IsLocalRing

open MvPowerSeries IsLocalRing
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedLineBasisHasBasis
attribute [-instance] _root_.OAI.Lech.RootTower.powerSeriesCharP
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
namespace Lech.GradedLineBasis
open scoped TensorProduct
universe u v w z
variable {G : Type u} [AddCommGroup G]
variable {R : Type v} [CommRing R] {S : Type w} [CommRing S] [Algebra R S]
variable (M : G → Type z) [∀ g,AddCommGroup (M g)] [∀ g,Module R (M g)]
variable (val : ∀ g,M g →ₗ[R] S)
variable (mul : ∀ g h,M g ⊗[R] M h ≃ₗ[R] M (g+h))
variable (hmul : ∀ g h (x : M g) (y : M h),val (g+h) (mul g h (x ⊗ₜ[R] y))=val g x*val h y)
variable (unit : R ≃ₗ[R] M 0) (hunit : val 0 (unit 1)=1)
variable (u : G → Sˣ) (hu0 : u 0=1) (huadd : ∀ g h,u (g+h)=u g*u h)

def HasBasis (g : G) : Prop := ∃ e : R ≃ₗ[R] M g,val g (e 1)=(u g:S)

include hunit hu0 in
lemma zero : HasBasis M val u 0 := ⟨unit,by rw [hunit,hu0];rfl⟩

include hmul huadd in
lemma add {g h : G} (hg : HasBasis M val u g) (hh : HasBasis M val u h) :
    HasBasis M val u (g+h) := by
  obtain ⟨eg,heg⟩ := hg
  obtain ⟨eh,heh⟩ := hh
  refine ⟨(TensorProduct.lid R R).symm ≪≫ₗ TensorProduct.congr eg eh ≪≫ₗ mul g h,?_⟩
  change val (g+h) (mul g h (eg 1 ⊗ₜ[R] eh 1))=(u (g+h):S)
  rw [hmul,heg,heh,huadd,Units.val_mul]

def cast {g h : G} (e : g=h) : M g ≃ₗ[R] M h := by subst h;exact LinearEquiv.refl R _
omit [AddCommGroup G] in
lemma val_cast {g h : G} (e : g=h) (x : M g) : val h (cast (R := R) M e x)=val g x := by subst h;rfl

include hmul hunit hu0 huadd in
 

lemma neg {g : G} (hg : HasBasis M val u g) : HasBasis M val u (-g) := by
  obtain ⟨eg,heg⟩ := hg
  let pair : M g ⊗[R] M (-g) ≃ₗ[R] R :=
    mul g (-g) ≪≫ₗ cast (R := R) M (add_neg_cancel g) ≪≫ₗ unit.symm
  let e : M (-g) ≃ₗ[R] R :=
    (TensorProduct.lid R (M (-g))).symm ≪≫ₗ
      (TensorProduct.congr eg (LinearEquiv.refl R (M (-g)))) ≪≫ₗ pair
  refine ⟨e.symm,?_⟩
  have hp : pair (eg 1 ⊗ₜ[R] e.symm 1)=1 := e.apply_symm_apply 1
  have hv : val g (eg 1)*val (-g) (e.symm 1)=1 := by
    rw [←hmul]
    rw [←val_cast (R := R) M val (add_neg_cancel g)]
    have he : cast (R := R) M (add_neg_cancel g) (mul g (-g) (eg 1 ⊗ₜ[R] e.symm 1))=unit 1 := by
      apply unit.symm.injective
      exact hp.trans (unit.symm_apply_apply 1).symm
    rw [he,hunit]
  have hu : (u g:S)*(u (-g):S)=1 := by
    rw [←Units.val_mul,←huadd,add_neg_cancel,hu0,Units.val_one]
  rw [heg] at hv
  exact (u g).isUnit.mul_left_cancel (hv.trans hu.symm)

 
def subgroup : AddSubgroup G where
  carrier := HasBasis M val u
  zero_mem' := zero M val unit hunit u hu0
  add_mem' := add M val mul hmul u huadd
  neg_mem' := neg M val mul hmul unit hunit u hu0 huadd

 

lemma all_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : (ι → ℤ) → Type z) [∀ g,AddCommGroup (M g)] [∀ g,Module R (M g)]
    (val : ∀ g,M g →ₗ[R] S)
    (mul : ∀ g h,M g ⊗[R] M h ≃ₗ[R] M (g+h))
    (hmul : ∀ g h (x : M g) (y : M h),val (g+h) (mul g h (x ⊗ₜ[R] y))=val g x*val h y)
    (unit : R ≃ₗ[R] M 0) (hunit : val 0 (unit 1)=1)
    (u : (ι → ℤ) → Sˣ) (hu0 : u 0=1) (huadd : ∀ g h,u (g+h)=u g*u h)
    (hgen : ∀ i,HasBasis M val u (Pi.single i 1)) (g : ι → ℤ) : HasBasis M val u g := by
  let H := subgroup M val mul hmul unit hunit u hu0 huadd
  have h (i : ι) : g i • Pi.single i (1:ℤ) ∈ H := H.zsmul_mem (hgen i) (g i)
  have he : ∑ i : ι,g i • Pi.single i (1:ℤ)=g := by
    ext j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp
  rw [←he]
  exact H.sum_mem (fun i _ => h i)
end Lech.GradedLineBasis


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootChartAtlasGlobalCoefficient
attribute [-instance] _root_.OAI.Lech.RootTower.powerSeriesCharP
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


namespace Lech.ProductSourceCover
open MvPolynomial HomogeneousLocalization
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1)) (s : Finset (Fin (n+1)))
attribute [local instance] MvPolynomial.gradedAlgebra
def projectiveRemainder : MvPolynomial (Fin (n+1)) R := ∏ j∈s.erase k,X j
lemma projectiveRemainder_homogeneous :
    projectiveRemainder R n k s∈ProjectiveCoefficientChart.grading R n (s.erase k).card := by
  simpa [projectiveRemainder] using IsHomogeneous.prod (s.erase k) (fun j => X (R:=R) j)
    (fun _ => 1) (fun j _ => isHomogeneous_X R j)
lemma projectiveRemainder_product (hk : k∈s) :
    X k*projectiveRemainder R n k s=∏ j∈s,X (R:=R) j := by
  exact Finset.mul_prod_erase s (fun j => X (R:=R) j) hk
end Lech.ProductSourceCover
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
variable {A B : Type*} [CommRing A] [IsReduced A] [CommRing B] [IsReduced B]
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

def perfectMap (f : A →+* B) : PerfectClosure A p →+* PerfectClosure B p :=
  PerfectRing.lift (PerfectClosure.of A p) ((PerfectClosure.of B p).comp f) p

end Lech.RootTower


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsDomain A] (p : ℕ) [Fact p.Prime] [CharP A p]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [CharP K p]

instance perfectAlgebra : Algebra A (PerfectClosure A p) := (PerfectClosure.of A p).toAlgebra

end Lech.RootTower


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TraceConductorPerfectOrder
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


namespace Lech.PerfectDomainStages
open Lech.RootTower
open scoped TensorProduct
variable (A D : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Algebra A D] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p]

instance domainAlgebra : Algebra (PerfectClosure A p) (PerfectClosure D p) :=
  (perfectMap p (algebraMap A D)).toAlgebra

end Lech.PerfectDomainStages
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechLengthLe
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


namespace Lech.FrobeniusGrowth
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R]

 
def powerIdeal (H : Ideal R) (q : ℕ) : Ideal R :=
  Ideal.span ((fun x : R => x^q) '' (H : Set R))

open Filter
open scoped Topology


end Lech.FrobeniusGrowth


end
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
namespace Lech.FrobeniusIntermediate
variable {D : Type*} [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
    (B : Subring D) (e : ℕ) (he : ∀ x : D, x^(p^e) ∈ B)

def powerMap : D →+* B :=
  (iterateFrobenius D p e).codRestrict B (by intro x; simpa only [iterateFrobenius_def] using he x)

instance instIsLocalHomSubtypeMemSubringRingHomPowerMapOfIsLocalRing [IsLocalRing D] [IsLocalRing B] : IsLocalHom (powerMap p B e he) where
  map_nonunit x hx := by
    have hu := hx.map B.subtype
    change IsUnit (x^(p^e)) at hu
    exact (isUnit_pow_iff (pow_ne_zero e (Fact.out : p.Prime).ne_zero)).mp hu

instance instCharPSubtypeMemSubring_solutions : CharP B p := B.subtype.charP Subtype.val_injective p

end Lech.FrobeniusIntermediate


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusModule
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open scoped TensorProduct


def FrobeniusModule (D : Type*) [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
    (n : ℕ) (M : ModuleCat D) : ModuleCat D :=
  (ModuleCat.extendScalars (iterateFrobenius D p n)).obj M

end Lech

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


namespace Lech.Grading
open DirectSum
variable {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]
variable (G : ℕ → Submodule R M) (H : ℕ → Submodule R N)
  [Decomposition G] [Decomposition H]

def projection (i : ℕ) : M →ₗ[R] M :=
  (G i).subtype.comp ((DirectSum.component R ℕ (fun i => ↥(G i)) i).comp
    (decomposeLinearEquiv G).toLinearMap)

@[simp] lemma projection_apply (i : ℕ) (x : M) :
    projection G i x = (decompose G x i : M) := rfl

variable (f : M →ₗ[R] N)
variable (hf : ∀ i, (G i).map f ≤ H (i + 1))
include hf

def step (i : ℕ) : G i →ₗ[R] H (i + 1) :=
  (f.comp (G i).subtype).codRestrict _ fun x =>
    hf i (Submodule.mem_map_of_mem x.property)

omit [Decomposition G] [Decomposition H] in
@[simp] lemma step_apply (i : ℕ) (x : G i) :
    (step G H f hf i x : N) = f (x : M) := rfl

end Lech.Grading


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusOrderTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal Topology
open Filter CategoryTheory
namespace Lech.FrobeniusIntermediate
universe u
variable {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
  (p : ℕ) [Fact p.Prime] [CharP D p]
  (B : Subring D) [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom B.subtype]
  [Module.Finite B D]

def frobeniusModule_order_iso (e : ℕ) (he : ∀ x : D, x^(p^e) ∈ B)
    (M : ModuleCat.{u} D) (n : ℕ) :
    (ModuleCat.extendScalars B.subtype).obj
      (Lech.FrobeniusModule B p n ((ModuleCat.extendScalars (powerMap p B e he)).obj M)) ≅
      Lech.FrobeniusModule D p (e+n) M := by
  let f := powerMap p B e he
  let g := iterateFrobenius B p n
  have hx : B.subtype.comp (g.comp f) = iterateFrobenius D p (e+n) := by
    ext x
    change (x^(p^e))^(p^n) = x^(p^(e+n))
    rw [← pow_mul,← pow_add]
  let u := (ModuleCat.extendScalars B.subtype).mapIso
    ((ModuleCat.extendScalarsComp f g).app M).symm
  let v := ((ModuleCat.extendScalarsComp (g.comp f) B.subtype).app M).symm
  have q := u ≪≫ v
  rw [hx] at q
  exact q



end Lech.FrobeniusIntermediate

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_HomogeneousEval
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.HomogeneousEval
open HomogeneousLocalization
universe u v w
variable {A : Type u} {B : Type v} {σ : Type w}
variable [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
variable (G : ℕ → σ) [GradedRing G]
variable (φ : A →+* B) {f g x : A}

 

def evaluate (f : A) (hf : IsUnit (φ f)) : Away G f →+* B :=
  (Localization.awayLift φ f hf).comp
    (algebraMap (Away G f) (Localization.Away f))

lemma evaluate_mk {d : ℕ} (hf : f ∈ G d) (hu : IsUnit (φ f))
    (v : B) (hv : φ f * v = 1) (j : ℕ) (a : A) (ha : a ∈ G (j • d)) :
    evaluate G φ f hu (Away.mk G hf j a ha) = φ a * v ^ j := by
  exact Localization.awayLift_mk φ f a v hv j

 

lemma evaluate_awayMap {e : ℕ} (hg : g ∈ G e) (hx : x = f * g)
    (hf : IsUnit (φ f)) (hxx : IsUnit (φ x)) (a : Away G f) :
    evaluate G φ x hxx (awayMap G hg hx a) = evaluate G φ f hf a := by
  change Localization.awayLift φ x hxx (awayMap G hg hx a).val = _
  rw [val_awayMap]
  have hcomp : (Localization.awayLift φ x hxx).comp
      (Localization.awayLift (algebraMap A (Localization.Away x)) f
        (isUnit_of_dvd_unit (map_dvd _ ⟨g, hx⟩)
          (IsLocalization.Away.algebraMap_isUnit x))) =
      Localization.awayLift φ f hf := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext r
    simp only [RingHom.coe_comp, Function.comp_apply, IsLocalization.Away.lift_eq]
  exact DFunLike.congr_fun hcomp a.val

 

lemma awayMap_comp {d e c : ℕ} {h y : A}
    (hf : f ∈ G d) (hg : g ∈ G e) (hh : h ∈ G c)
    (hx : x = f * g) (hy : y = x * h) (hz : y = f * (g * h))
    (a : Away G f) :
    awayMap G hh hy (awayMap G hg hx a) =
      awayMap G (SetLike.mul_mem_graded hg hh) hz a := by
  obtain ⟨j,b,hb,rfl⟩ := Away.mk_surjective G hf a
  rw [awayMap_mk, awayMap_mk, awayMap_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, mul_pow, mul_assoc]

lemma awayMap_one {d : ℕ} (hf : f ∈ G d) (hx : f = f * 1) (a : Away G f) :
    awayMap G (show (1 : A) ∈ G 0 from SetLike.one_mem_graded G) hx a = a := by
  obtain ⟨j,b,hb,rfl⟩ := Away.mk_surjective G hf a
  rw [awayMap_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, one_pow, mul_one]

end Lech.HomogeneousEval

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealFilteredComplex
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

section Linear
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N) (s : ℕ) (hf : f.range ≤ I^s • (⊤ : Submodule R N))

include hf in
lemma map_power_le (a : ℕ) :
    (I^a • (⊤ : Submodule R M)).map f ≤ I^(a+s) • (⊤ : Submodule R N) := by
  rw [Submodule.map_smul'',Submodule.map_top,pow_add,Submodule.mul_smul]
  exact Submodule.smul_mono le_rfl hf

end Linear

 

def subcomplex {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{u} R) c)
    (P : ∀ p, Submodule R (K.X p)) (hP : ∀ p q, P p ≤ (P q).comap (K.d p q).hom) :
    HomologicalComplex (ModuleCat.{u} R) c where
  X p := ModuleCat.of R (P p)
  d p q := ModuleCat.ofHom (((K.d p q).hom.comp (P p).subtype).codRestrict (P q)
    (fun x => hP p q x.property))
  shape p q hpq := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (K.d p q).hom x.val=0
    rw [K.shape p q hpq]
    rfl
  d_comp_d' p q r _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (K.d q r).hom ((K.d p q).hom x.val)=0
    exact congrArg (fun f : K.X p ⟶ K.X r => f.hom x.val) (K.d_comp_d p q r)

 
def subcomplexMap {ι : Type*} {c : ComplexShape ι}
    (K L : HomologicalComplex (ModuleCat.{u} R) c)
    (P : ∀ p, Submodule R (K.X p)) (T : ∀ p, Submodule R (L.X p))
    (hP : ∀ p q, P p ≤ (P q).comap (K.d p q).hom)
    (hT : ∀ p q, T p ≤ (T q).comap (L.d p q).hom)
    (f : K ⟶ L) (hf : ∀ p, P p ≤ (T p).comap (f.f p).hom) :
    subcomplex K P hP ⟶ subcomplex L T hT where
  f p := ModuleCat.ofHom (((f.f p).hom.comp (P p).subtype).codRestrict (T p)
    (fun x => hf p x.property))
  comm' p q _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun g : K.X p ⟶ L.X q => g.hom x.val) (f.comm p q)

 

def order (h s : ℕ) (p : ℤ) : ℕ := (p+(h:ℤ)).toNat*s

lemma order_step (h s : ℕ) (p : ℤ) : order h s (p+1) ≤ order h s p+s := by
  have hh : (p+1+(h:ℤ)).toNat ≤ (p+(h:ℤ)).toNat+1 := by omega
  exact (Nat.mul_le_mul_right s hh).trans_eq (by rw [Nat.add_mul,one_mul]; rfl)

variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (Q : ModuleCat.{u} R)

abbrev tensorComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  (((curriedTensor (ModuleCat.{u} R)).flip.obj Q).mapHomologicalComplex (.up ℤ)).obj F

def term (p : ℤ) : Submodule R ((tensorComplex F Q).X p) :=
  I^(order h s p) • ⊤


def tensorMap {Q Q' : ModuleCat.{u} R} (f : Q ⟶ Q') : tensorComplex F Q ⟶ tensorComplex F Q' :=
  ((curriedTensor (ModuleCat.{u} R)).flip.map f).mapHomologicalComplex (.up ℤ) |>.app F



end Lech.IdealFiltered

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealFilteredHomotopy
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R]


variable (I : Ideal R)
lemma linear_decreases {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) {a b : ℕ} (hab : b ≤ a) :
    I^a • (⊤ : Submodule R M) ≤ (I^b • (⊤ : Submodule R N)).comap f :=
  (Submodule.smul_top_le_comap_smul_top (I^a) f).trans
    (Submodule.comap_mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)))

end Lech.IdealFiltered

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealQuotientFunctor
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)


def quotientPiEquiv {ι : Type*} [Fintype ι] (M : ι → Type u)
    [∀ i,AddCommGroup (M i)] [∀ i,Module R (M i)] :
    ((∀ i,M i) ⧸ (I • (⊤ : Submodule R (∀ i,M i)))) ≃ₗ[R]
      (∀ i, M i ⧸ (I • (⊤ : Submodule R (M i)))) := by
  classical
  exact (TensorProduct.quotTensorEquivQuotSMul (∀ i,M i) I).symm ≪≫ₗ
    TensorProduct.piRight R R (R ⧸ I) M ≪≫ₗ
      LinearEquiv.piCongrRight (fun i => TensorProduct.quotTensorEquivQuotSMul (M i) I)

lemma quotientPiEquiv_mk {ι : Type*} [Fintype ι] (M : ι → Type u)
    [∀ i,AddCommGroup (M i)] [∀ i,Module R (M i)] (x : ∀ i,M i) :
    quotientPiEquiv I M (Submodule.Quotient.mk x) = fun i => Submodule.Quotient.mk (x i) := by
  classical
  unfold quotientPiEquiv
  simp only [LinearEquiv.trans_apply,TensorProduct.quotTensorEquivQuotSMul_symm_mk,
    TensorProduct.piRight_apply,TensorProduct.piRightHom_tmul]
  funext i
  change TensorProduct.quotTensorEquivQuotSMul (M i) I (1 ⊗ₜ[R] x i)=_
  exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I (x i)


end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IntermediateTensorLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
open CategoryTheory
namespace Lech.FrobeniusIntermediate
open Lech.RootTower Lech.PerfectDomainStages
universe u
variable (σ : Type) (k D : Type u) [Fintype σ] [Field k] [CommRing D] [IsDomain D]
    [Algebra (MvPowerSeries σ k) D]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
    (B : Subalgebra (MvPowerSeries σ k) D)
    (e : ℕ) (he : ∀ x : D, x^(p^e) ∈ B)
local instance instCharPSubtypeMemSubalgebraMvPowerSeries_solutions_1 : CharP B p := B.val.toRingHom.charP Subtype.val_injective p
local instance instSMulCommClassSubtypeMemSubalgebraMvPowerSeriesPerfectClosure_solutions : SMulCommClass B (PerfectClosure (MvPowerSeries σ k) p) (PerfectClosure B p) where
  smul_comm b r c := by
    simp only [Algebra.smul_def]
    exact mul_left_comm _ _ _


end Lech.FrobeniusIntermediate

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

instance extendScalars_additive (φ : R →+* S) : (ModuleCat.extendScalars φ).Additive where
  map_add := by
    intros M N f g
    let := φ.toAlgebra
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_add _ _

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RobertsOrderTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
namespace Lech.FrobeniusIntermediate
universe u
variable {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
  (p : ℕ) [Fact p.Prime] [CharP D p]
  (B : Subring D) [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom B.subtype]
  [Module.Finite B D]

def frobeniusComplex_order_iso (e : ℕ) (he : ∀ x : D,x^(p^e) ∈ B)
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (n : ℕ) :
    (((ModuleCat.extendScalars B.subtype).mapHomologicalComplex _).obj
      (frobeniusComplex B p n
        (((ModuleCat.extendScalars (powerMap p B e he)).mapHomologicalComplex _).obj F))) ≅
      frobeniusComplex D p (e+n) F := by
  let f := powerMap p B e he
  let g := iterateFrobenius B p n
  have hx : B.subtype.comp (g.comp f) = iterateFrobenius D p (e+n) := by
    ext x
    change (x^(p^e))^(p^n) = x^(p^(e+n))
    rw [← pow_mul,← pow_add]
  let u := ((ModuleCat.extendScalars B.subtype).mapHomologicalComplex (.up ℤ)).mapIso
    (((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (.up ℤ)).app F).symm)
  let v := ((NatIso.mapHomologicalComplex
    (ModuleCat.extendScalarsComp (g.comp f) B.subtype) (.up ℤ)).app F).symm
  have q := u ≪≫ v
  rw [hx] at q
  exact q



end Lech.FrobeniusIntermediate

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootOverlap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ProjectiveRoot

open MvPolynomial HomogeneousLocalization ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

 
def product (s : Finset (Fin (n+1))) : MvPolynomial (Fin (n+1)) R :=
  ∏ j ∈ s, X j

abbrev Ring (s : Finset (Fin (n+1))) :=
  Away (ProjectiveCoefficientChart.grading R n) (product R n s)


variable (k : Fin (n+1)) (s : Finset (Fin (n+1))) (hk : k ∈ s)
include hk in
lemma product_eq : product R n s = X k * projectiveRemainder R n k s :=
  (projectiveRemainder_product R n k s hk).symm

 
def chartMap : ProjectiveCoefficientChart.Chart R n k →+* Ring R n s :=
  awayMap (ProjectiveCoefficientChart.grading R n)
    (projectiveRemainder_homogeneous R n k s) (product_eq R n k s hk)

@[instance_reducible] def chartAlgebra :
    Algebra (ProjectiveCoefficientChart.Chart R n k) (Ring R n s) :=
  (chartMap R n k s hk).toAlgebra


end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootRestriction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.HomogeneousEval
open HomogeneousLocalization
universe u v
variable {A : Type u} [CommRing A] {σ : Type v}
  [SetLike σ A] [AddSubgroupClass σ A] (G : ℕ → σ) [GradedRing G]
 

lemma awayMap_same {f g h x : A} {e d : ℕ} (hg : g ∈ G e) (hh : h ∈ G d)
    (hx : x = f * g) (hy : x = f * h) (a : Away G f) :
    awayMap G hg hx a = awayMap G hh hy a := by
  apply HomogeneousLocalization.val_injective
  rw [val_awayMap, val_awayMap]
end Lech.HomogeneousEval

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarCechComparison
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory HomologicalComplex
universe u
variable {R : Type u}
  [CommRing R]
  {ι : Type}
  [Fintype ι]
  [LinearOrder ι]
omit [Fintype ι] [LinearOrder ι] in
lemma nonempty_card {q : ℕ} (s : Set.powersetCard ι (q+1)) : s.val.Nonempty :=
  Finset.card_pos.mp (by rw [s.property]; omega)

end Lech.FiniteModuleCech

end

end OAI
end


