-- Prove2me | Definitions.Def_Q223SES001
-- name    : Q223SES001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:47:25.606475+00:00
-- url     : https://prove2.me/theorems/fd7d4c8e-8479-4436-b764-547ff6605f42
-- title:
--   Definitions bundle Q223SES001 of the split of OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 247 declarations of OpenAI's Lean: 104 definitions, 1 inductive type or structure, 22 instances and 120 theorems. The definitions and types are `OAI.MaximalSeshadri.AffineCohomology.schemeGlobalHomEquiv`, `OAI.MaximalSeshadri.AffineCohomology.structureSheafUnit`, `OAI.MaximalSeshadri.AffineDenominators.Aux`, `OAI.MaximalSeshadri.AffineDenominators.basicOpen`, `OAI.MaximalSeshadri.AffineDenominators.res`, `OAI.MaximalSeshadri.AffineSchemeCohomology.restrictionEquivalence`, `OAI.MaximalSeshadri.AlgebraicJets.JetAlgebra`, `OAI.MaximalSeshadri.AlgebraicJets.JetIndex`, `OAI.MaximalSeshadri.AlgebraicJets.augmentedDerivative`, `OAI.MaximalSeshadri.AlgebraicJets.augmentedDerivativeEquiv`, `OAI.MaximalSeshadri.AlgebraicJets.augmentedLinear`, `OAI.MaximalSeshadri.AlgebraicJets.augmentedPolynomial`, `OAI.MaximalSeshadri.AlgebraicJets.kernelPoint`, `OAI.MaximalSeshadri.AlgebraicJets.polynomialDifferential`, `OAI.MaximalSeshadri.AlgebraicJets.polynomialJetCoeffs`, `OAI.MaximalSeshadri.AlgebraicJets.polynomialJetCoeffsAt`, `OAI.MaximalSeshadri.AlgebraicJets.polynomialTranslate`, `OAI.MaximalSeshadri.AlgebraicJets.presentationPoint`, `OAI.MaximalSeshadri.AlgebraicJets.quotientBaseMap`, `OAI.MaximalSeshadri.AlgebraicJets.rationalLocalMap`, `OAI.MaximalSeshadri.AlgebraicJets.rationalPointTopology`, `OAI.MaximalSeshadri.AnalyticNode.nodeLinear`, `OAI.MaximalSeshadri.AnalyticNode.shearLinear`, `OAI.MaximalSeshadri.BertiniIntegral.chartDifference`, `OAI.MaximalSeshadri.BertiniIntegral.coordinateDifference`, `OAI.MaximalSeshadri.BertiniIntegral.coordinateSum`, `OAI.MaximalSeshadri.BertiniIntegral.doubleBaseChange`, `OAI.MaximalSeshadri.BertiniIntegral.doubledBaseChangeEquiv`, `OAI.MaximalSeshadri.BertiniIntegral.etaleCotangentCoordinate`, `OAI.MaximalSeshadri.BertiniIntegral.homogeneousLinearForm`, `OAI.MaximalSeshadri.BertiniIntegral.hyperplaneFamilyAlgebra`, `OAI.MaximalSeshadri.BertiniIntegral.hyperplaneVariable`, `OAI.MaximalSeshadri.BertiniIntegral.mvPolynomialMapOver`, `OAI.MaximalSeshadri.BertiniIntegral.mvPolynomialTensorCoeff`, `OAI.MaximalSeshadri.BertiniIntegral.mvPolynomialTensorEquiv`, `OAI.MaximalSeshadri.BertiniIntegral.mvPolynomialTensorFrom`, `OAI.MaximalSeshadri.BertiniIntegral.mvPolynomialTensorTo`, `OAI.MaximalSeshadri.BertiniIntegral.permuteHyperplaneHom`, `OAI.MaximalSeshadri.BertiniIntegral.polynomialQuotientBaseChange`, `OAI.MaximalSeshadri.BertiniIntegral.projectiveHyperplane` and 65 more.
--
--   **Sources.** They come from these modules of lean/OAI/AlgebraicGeometry, in whole or in part: `Seshadri_Analytic_FormalSeries`, `Seshadri_Analytic_PointCharts`, `Seshadri_Analytic_PolynomialCharts`, `Seshadri_Bertini_CountableSpecialization`, `Seshadri_Bertini_Derivations`, `Seshadri_Bertini_Descent`, `Seshadri_Bertini_EtaleCoordinates`, `Seshadri_Bertini_GenericHyperplanes`, `Seshadri_Bertini_GenericSmoothness`, `Seshadri_Bertini_GeometricDomains`, `Seshadri_Bertini_HyperplaneFamilies`, `Seshadri_Bertini_LinearForms`, `Seshadri_Bertini_SimultaneousHyperplanes`, `Seshadri_Blowup_BlowupIntegral`, `Seshadri_Blowup_FiniteCenters`, `Seshadri_Blowup_Gluing`, `Seshadri_Blowup_PrincipalCharts`, `Seshadri_Blowup_ReesCharts`, `Seshadri_Blowup_Uniqueness`, `Seshadri_Cohomology_AffineDenominators`, `Seshadri_Cohomology_AffineVanishing`, `Seshadri_Cohomology_ClosedPushforwardCohomology`, `Seshadri_Cohomology_ExtCokernel`, `Seshadri_Cohomology_FiniteCover`, `Seshadri_Cohomology_Injectives`, `Seshadri_Cohomology_RestrictionComparison`, `Seshadri_Cohomology_SheafExactness`, `Seshadri_Geometry_GeneralQuadraticNumerics`, `Seshadri_Interpolation_ConvergentSeries`, `Seshadri_Intersection_EulerExact`, `Seshadri_Intersection_LocalSectionDegree`, `Seshadri_Jets_AnalyticNode`, `Seshadri_Jets_BinaryJetDimension`, `Seshadri_Jets_FormalEtale`, `Seshadri_Jets_JetOpenness`, `Seshadri_Jets_PolynomialJets`, `Seshadri_Nodal_NodalIntersection`, `Seshadri_Projective_PolynomialCharts`, `Seshadri_Sheaves_ClosedPushforwardEuler`, `Seshadri_Sheaves_ClosedPushforwardExact`, `Seshadri_Sheaves_Frames`, `Seshadri_Sheaves_Sections`, `Seshadri_Sheaves_TensorFrames`.
--
--   **Imports.** It imports the published bundle `Def_MaximalSeshadriConstants`.
--
--   **Imported by** (directly, in this split): the bundles `Q223SES004`, `Q223SES005` and `Q223SES006`; the statements `OAI_MaximalSeshadri_FinitePointBlowup_finite_point_power_contraction`, `OAI.MaximalSeshadri.FinitePointBlowup.finite_point_power_contraction_s01`, `OAI_MaximalSeshadri_Geometry_PointBlowup_total_ideal_degree` and `OAI.MaximalSeshadri.Geometry.PointBlowup.total_ideal_degree_s01`.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/AlgebraicGeometry at commit adc7f12

import Mathlib
import Definitions.Def_MaximalSeshadriConstants

section
-- module Solutions.Q223_SES.Compat
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
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
end OAICompat434

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_FormalSeries
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section

namespace MaximalSeshadri.FormalCoordinates
noncomputable section
open PowerSeries

variable {F A B : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]

def powerSeriesMapEquiv (e : A ≃ₐ[F] B) : PowerSeries A ≃ₐ[F] PowerSeries B :=
  AlgEquiv.ofAlgHom (PowerSeries.mapAlgHom e.toAlgHom)
    (PowerSeries.mapAlgHom e.symm.toAlgHom)
    (by ext f n; simp [PowerSeries.mapAlgHom_apply])
    (by ext f n; simp [PowerSeries.mapAlgHom_apply])

@[simp] lemma powerSeriesMapEquiv_coeff (e : A ≃ₐ[F] B) (f : PowerSeries A) (n : ℕ) :
    coeff n (powerSeriesMapEquiv e f) = e (coeff n f) := by
  change coeff n (PowerSeries.map e.toRingHom f) = _
  exact coeff_map ..

def binaryEquiv (F : Type*) [CommRing F] :
    MvPowerSeries (Fin 2) F ≃ₐ[F] PowerSeries (PowerSeries F) :=
  (MvPowerSeries.finSuccEquiv F 1).trans (powerSeriesMapEquiv
    ((MvPowerSeries.finSuccEquiv F 0).trans
      (powerSeriesMapEquiv (MvPowerSeries.isEmptyEquiv (Fin 0) F))))

@[simp] lemma binaryEquiv_X_zero :
    binaryEquiv F (MvPowerSeries.X 0) = (PowerSeries.X : PowerSeries (PowerSeries F)) := by
  simp [binaryEquiv, powerSeriesMapEquiv, PowerSeries.mapAlgHom_apply]

@[simp] lemma binaryEquiv_X_one :
    binaryEquiv F (MvPowerSeries.X 1) = PowerSeries.C (PowerSeries.X : PowerSeries F) := by
  unfold binaryEquiv
  rw [AlgEquiv.trans_apply]
  have hx : MvPowerSeries.finSuccEquiv F 1 (MvPowerSeries.X 1) =
      PowerSeries.C (MvPowerSeries.X 0) :=
    MvPowerSeries.finSuccEquiv_X_succ (R := F) (0 : Fin 1)
  rw [hx]
  simp [powerSeriesMapEquiv, PowerSeries.mapAlgHom_apply]

end
end MaximalSeshadri.FormalCoordinates


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_PolynomialCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial
open scoped BigOperators
variable {𝕜 ι E : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def polynomialDifferential (L : ι → E →L[𝕜] 𝕜) (p : MvPolynomial ι 𝕜) (x : E) :
    E →L[𝕜] 𝕜 := ∑ i, eval (fun i => L i x) (pderiv i p) • L i

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped BigOperators Matrix
variable {F ι σ : Type*} [Field F] [Fintype ι] [Fintype σ] [DecidableEq ι] [DecidableEq σ]

def augmentedLinear (j : σ → ι) (J : Matrix σ ι F) :
    (ι → F) →ₗ[F] ((σ → F) × ({i : ι // i ∉ Set.range j} → F)) :=
  (Matrix.toLin' J).prod (LinearMap.pi fun i => LinearMap.proj i.val)

theorem augmentedLinear_bijective (j : σ → ι) (hj : Function.Injective j)
    (J : Matrix σ ι F) (hJ : IsUnit (J.submatrix id j).det) :
    Function.Bijective (augmentedLinear j J) := by
  classical
  have hinj : Function.Injective (augmentedLinear j J) := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have hfree (i : ι) (hi : i ∉ Set.range j) : v i = 0 := by
      exact congrFun (congrArg Prod.snd hv) ⟨i, hi⟩
    have hsel : (J.submatrix id j).mulVec (v ∘ j) = 0 := by
      ext i
      calc
        _ = (J.mulVec v) i := Fintype.sum_of_injective j hj
          (fun k => J i (j k) * v (j k)) (fun k => J i k * v k)
          (fun k hk => by rw [hfree k hk, mul_zero]) (fun _ => rfl)
        _ = 0 := congrFun (congrArg Prod.fst hv) i
    have hm : v ∘ j = 0 := by
      apply (Matrix.mulVec_injective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr hJ))
      simpa using hsel
    ext i
    by_cases hi : i ∈ Set.range j
    · obtain ⟨k, rfl⟩ := hi
      exact congrFun hm k
    · exact hfree i hi
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  rw [Module.finrank_pi, Module.finrank_prod, Module.finrank_pi, Module.finrank_pi]
  have hc := Fintype.card_congr (Equiv.ofInjective j hj)
  have hd := Fintype.card_congr (Equiv.Set.sumCompl (Set.range j))
  rw [Fintype.card_sum] at hd
  have he : Fintype.card {i : ι // i ∉ Set.range j} =
      Fintype.card ↥(Set.range j)ᶜ := Fintype.card_congr (Equiv.refl _)
  omega

variable {S : Type*} [CommRing S] [Algebra F S]

omit [Fintype ι] [DecidableEq ι] in
                                                                               
theorem submersive_jacobian_at_point
    (P : Algebra.SubmersivePresentation F S ι σ) (ρ : S →ₐ[F] F) :
    IsUnit (Matrix.det (Matrix.of fun i k : σ => MvPolynomial.eval (fun a => ρ (P.val a))
      (MvPolynomial.pderiv (P.map k) (P.relation i)))) := by
  classical
  have h := P.jacobian_isUnit.map ρ.toRingHom
  rw [P.jacobian_eq_jacobiMatrix_det] at h
  have he (f : MvPolynomial ι F) :
      ρ (MvPolynomial.aeval P.val f) =
        MvPolynomial.eval (fun a => ρ (P.val a)) f := by
    change (ρ.comp (MvPolynomial.aeval P.val)) f = _
    rw [MvPolynomial.comp_aeval]
    rfl
  rw [P.algebraMap_apply] at h
  change IsUnit (ρ (MvPolynomial.aeval P.val P.jacobiMatrix.det)) at h
  rw [he, RingHom.map_det] at h
  have heq : (MvPolynomial.eval (fun a => ρ (P.val a))).mapMatrix P.jacobiMatrix =
      (Matrix.of fun i k : σ => MvPolynomial.eval (fun a => ρ (P.val a))
        (MvPolynomial.pderiv (P.map k) (P.relation i)))ᵀ := by
    ext i k
    simp [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, Matrix.transpose_apply]
  rw [heq, Matrix.det_transpose] at h
  exact h

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped BigOperators Matrix ContDiff
open MvPolynomial
variable {F ι σ S : Type*} [RCLike F] [Fintype ι] [Fintype σ]
  [DecidableEq ι] [DecidableEq σ] [CommRing S] [Algebra F S]

def augmentedPolynomial (P : Algebra.SubmersivePresentation F S ι σ) (x : ι → F) :
    (σ → F) × ({i : ι // i ∉ Set.range P.map} → F) :=
  ((fun a => eval x (P.relation a)), fun i => x i.val)

def augmentedDerivative (P : Algebra.SubmersivePresentation F S ι σ) (x : ι → F) :
    (ι → F) →L[F] ((σ → F) × ({i : ι // i ∉ Set.range P.map} → F)) :=
  (augmentedLinear P.map (Matrix.of fun i a => eval x (pderiv a (P.relation i)))).toContinuousLinearMap

def augmentedDerivativeEquiv (P : Algebra.SubmersivePresentation F S ι σ)
    (ρ : S →ₐ[F] F) :
    (ι → F) ≃L[F] ((σ → F) × ({i : ι // i ∉ Set.range P.map} → F)) :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofBijective
    (augmentedLinear P.map (Matrix.of fun i a => eval (fun a => ρ (P.val a))
      (pderiv a (P.relation i))))
    (augmentedLinear_bijective P.map P.map_inj _ (submersive_jacobian_at_point P ρ)))

end
end MaximalSeshadri.AlgebraicJets


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_PointCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial
variable {F S ι σ : Type*} [CommRing F] [CommRing S] [Algebra F S]

def presentationPoint (P : Algebra.Presentation F S ι σ)
    (x : ι → F) (hx : ∀ i, eval x (P.relation i) = 0) : S →ₐ[F] F :=
  (Ideal.Quotient.liftₐ P.ker (aeval x) (by
    change P.ker ≤ RingHom.ker (aeval x).toRingHom
    rw [← P.span_range_relation_eq_ker]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change aeval x (P.relation i) = 0
    simpa using hx i)).comp (P.quotientEquiv.restrictScalars F).symm.toAlgHom

lemma evaluation_relations (P : Algebra.Presentation F S ι σ) (ρ : S →ₐ[F] F) (i : σ) :
    eval (fun a => ρ (P.val a)) (P.relation i) = 0 := by
  have he : aeval (fun a => ρ (P.val a)) = ρ.comp (aeval P.val) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp
  change aeval (fun a => ρ (P.val a)) (P.relation i) = 0
  rw [he]
  simp

end

end MaximalSeshadri.AlgebraicJets


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_LinearForms
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MaximalSeshadri.BertiniIntegral

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped nonZeroDivisors
open MvPolynomial
variable {R σ : Type*} [CommRing R] [Fintype σ]

def homogeneousLinearForm (v : σ → R) : MvPolynomial σ R :=
  ∑ i, C (v i) * X i

def separateLinearVariable (i : σ) :
    MvPolynomial σ R ≃ₐ[R] Polynomial (MvPolynomial {j : σ // j ≠ i} R) := by
  classical
  exact (renameEquiv R (Equiv.optionSubtypeNe i).symm).trans (optionEquivLeft R _)

end
end MaximalSeshadri.BertiniIntegral


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_GenericHyperplanes
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {R A B σ : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

def mvPolynomialMapOver (f : A →ₐ[R] B) : (MvPolynomial σ A) →ₐ[(MvPolynomial σ R)] (MvPolynomial σ B) where
  __ := MvPolynomial.map f.toRingHom
  commutes' p := by
    change MvPolynomial.map f.toRingHom (MvPolynomial.map (algebraMap R A) p) =
      MvPolynomial.map (algebraMap R B) p
    rw [MvPolynomial.map_map]
    have hf : f.toRingHom.comp (algebraMap R A) = algebraMap R B := by
      ext z
      exact f.commutes z
    rw [hf]

@[simp] lemma mvPolynomialMapOver_C (f : A →ₐ[R] B) (a : A) :
    mvPolynomialMapOver (σ := σ) f (C a) = C (f a) := map_C f.toRingHom a
@[simp] lemma mvPolynomialMapOver_X (f : A →ₐ[R] B) (i : σ) :
    mvPolynomialMapOver f (X i) = X i := map_X f.toRingHom i

def mvPolynomialTensorTo : ((MvPolynomial σ A) ⊗[(MvPolynomial σ R)] (MvPolynomial σ B)) →ₐ[(MvPolynomial σ R)] (MvPolynomial σ (A ⊗[R] B)) :=
  Algebra.TensorProduct.lift (mvPolynomialMapOver Algebra.TensorProduct.includeLeft)
    (mvPolynomialMapOver Algebra.TensorProduct.includeRight) (fun _ _ => Commute.all _ _)

abbrev mvPolynomialTensorCoeff : (A ⊗[R] B) →ₐ[R] ((MvPolynomial σ A) ⊗[(MvPolynomial σ R)] (MvPolynomial σ B)) :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : (MvPolynomial σ A) →ₐ[(MvPolynomial σ R)] _).restrictScalars R).comp (IsScalarTower.toAlgHom R A (MvPolynomial σ A)))
    (((Algebra.TensorProduct.includeRight : (MvPolynomial σ B) →ₐ[(MvPolynomial σ R)] _).restrictScalars R).comp (IsScalarTower.toAlgHom R B (MvPolynomial σ B)))
    (fun _ _ => Commute.all _ _)

def mvPolynomialTensorFrom : (MvPolynomial σ (A ⊗[R] B)) →ₐ[R]
    (MvPolynomial σ A ⊗[MvPolynomial σ R] MvPolynomial σ B) where
  __ := MvPolynomial.eval₂Hom mvPolynomialTensorCoeff.toRingHom
    (fun i => (X i : MvPolynomial σ A) ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ B))
  commutes' r := by
    change MvPolynomial.eval₂Hom mvPolynomialTensorCoeff.toRingHom _
      (C (algebraMap R (A ⊗[R] B) r)) = _
    rw [eval₂Hom_C]
    exact mvPolynomialTensorCoeff.commutes r

lemma mvPolynomialTensorTo_left (p : (MvPolynomial σ A)) :
    mvPolynomialTensorTo (p ⊗ₜ[(MvPolynomial σ R)] (1 : (MvPolynomial σ B))) =
      mvPolynomialMapOver (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) p := by
  simp [mvPolynomialTensorTo]

@[simp] lemma mvPolynomialTensorFrom_C_tmul (a : A) (b : B) :
    mvPolynomialTensorFrom (C (a ⊗ₜ[R] b)) = (C a) ⊗ₜ[(MvPolynomial σ R)] (C b) := by
  simp [mvPolynomialTensorFrom, mvPolynomialTensorCoeff]

@[simp] lemma mvPolynomialTensorFrom_X (i : σ) :
    mvPolynomialTensorFrom (R := R) (A := A) (B := B) (X i) =
      (X i : MvPolynomial σ A) ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ B) := by
  simp [mvPolynomialTensorFrom]

lemma mvPolynomialTensorTo_tmul (p : MvPolynomial σ A) (q : MvPolynomial σ B) :
    mvPolynomialTensorTo (R := R) (p ⊗ₜ[MvPolynomial σ R] q) =
      mvPolynomialMapOver (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) p *
      mvPolynomialMapOver (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) q :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

lemma mvPolynomialTensorFrom_left :
    mvPolynomialTensorFrom.comp ((mvPolynomialMapOver
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)).restrictScalars R) =
      (Algebra.TensorProduct.includeLeft : (MvPolynomial σ A) →ₐ[(MvPolynomial σ R)] (MvPolynomial σ A) ⊗[(MvPolynomial σ R)] (MvPolynomial σ B)).restrictScalars R := by
  apply MvPolynomial.algHom_ext'
  · apply AlgHom.ext
    intro a
    change mvPolynomialTensorFrom
      (mvPolynomialMapOver Algebra.TensorProduct.includeLeft (C a)) =
      (C a) ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ B)
    rw [mvPolynomialMapOver_C]
    change mvPolynomialTensorFrom (C (a ⊗ₜ[R] (1 : B))) = _
    simp
  · intro i
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, mvPolynomialMapOver_X]
    change mvPolynomialTensorFrom (X i) = X i ⊗ₜ[(MvPolynomial σ R)] (1 : (MvPolynomial σ B))
    simp [mvPolynomialTensorFrom]

lemma mvPolynomialTensorFrom_right :
    mvPolynomialTensorFrom.comp ((mvPolynomialMapOver
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)).restrictScalars R) =
      (Algebra.TensorProduct.includeRight : (MvPolynomial σ B) →ₐ[(MvPolynomial σ R)] (MvPolynomial σ A) ⊗[(MvPolynomial σ R)] (MvPolynomial σ B)).restrictScalars R := by
  apply MvPolynomial.algHom_ext'
  · apply AlgHom.ext
    intro b
    change mvPolynomialTensorFrom
      (mvPolynomialMapOver Algebra.TensorProduct.includeRight (C b)) =
      (1 : MvPolynomial σ A) ⊗ₜ[MvPolynomial σ R] (C b)
    rw [mvPolynomialMapOver_C]
    change mvPolynomialTensorFrom (C ((1 : A) ⊗ₜ[R] b)) = _
    simp
  · intro i
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, mvPolynomialMapOver_X]
    change mvPolynomialTensorFrom (X i) = (1 : (MvPolynomial σ A)) ⊗ₜ[(MvPolynomial σ R)] (X i)
    rw [show mvPolynomialTensorFrom (X i) = (X i : (MvPolynomial σ A)) ⊗ₜ[(MvPolynomial σ R)] (1 : (MvPolynomial σ B)) by
      simp [mvPolynomialTensorFrom]]
    have h := Algebra.TensorProduct.algebraMap_apply'
      (R := (MvPolynomial σ R)) (A := (MvPolynomial σ A)) (B := (MvPolynomial σ B)) (X i)
    simpa using h

lemma mvPolynomialTensorFrom_to :
    mvPolynomialTensorFrom.comp (mvPolynomialTensorTo.restrictScalars R) =
      AlgHom.id R ((MvPolynomial σ A) ⊗[(MvPolynomial σ R)] (MvPolynomial σ B)) := by
  apply AlgHom.ext
  intro t
  change mvPolynomialTensorFrom (mvPolynomialTensorTo t) = t
  induction t using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p q =>
    rw [mvPolynomialTensorTo_tmul, map_mul]
    have hl := DFunLike.congr_fun (mvPolynomialTensorFrom_left (R := R) (A := A) (B := B)) p
    have hr := DFunLike.congr_fun (mvPolynomialTensorFrom_right (R := R) (A := A) (B := B)) q
    change mvPolynomialTensorFrom (mvPolynomialMapOver Algebra.TensorProduct.includeLeft p) =
      p ⊗ₜ[(MvPolynomial σ R)] (1 : (MvPolynomial σ B)) at hl
    change mvPolynomialTensorFrom (mvPolynomialMapOver Algebra.TensorProduct.includeRight q) =
      (1 : (MvPolynomial σ A)) ⊗ₜ[(MvPolynomial σ R)] q at hr
    rw [hl, hr]
    simp

lemma mvPolynomialTensorTo_from :
    (mvPolynomialTensorTo.restrictScalars R).comp mvPolynomialTensorFrom =
      AlgHom.id R (MvPolynomial σ (A ⊗[R] B)) := by
  apply MvPolynomial.algHom_ext'
  · apply AlgHom.ext
    intro t
    change mvPolynomialTensorTo (mvPolynomialTensorFrom (C t)) = C t
    induction t using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      rw [mvPolynomialTensorFrom_C_tmul]
      rw [mvPolynomialTensorTo, Algebra.TensorProduct.lift_tmul]
      rw [mvPolynomialMapOver_C, mvPolynomialMapOver_C, ← C_mul]
      change C ((a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b)) = C (a ⊗ₜ[R] b)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  · intro i
    change mvPolynomialTensorTo (R := R) (A := A) (B := B)
      (mvPolynomialTensorFrom (R := R) (A := A) (B := B) (X i)) = X i
    rw [mvPolynomialTensorFrom_X, mvPolynomialTensorTo_left, mvPolynomialMapOver_X]

def mvPolynomialTensorEquiv : ((MvPolynomial σ A) ⊗[(MvPolynomial σ R)] (MvPolynomial σ B)) ≃ₐ[R] (MvPolynomial σ (A ⊗[R] B)) :=
  AlgEquiv.ofAlgHom (mvPolynomialTensorTo.restrictScalars R) mvPolynomialTensorFrom
    mvPolynomialTensorTo_from mvPolynomialTensorFrom_to

@[simp] lemma mvPolynomialTensorEquiv_left (p : (MvPolynomial σ A)) :
    mvPolynomialTensorEquiv (p ⊗ₜ[(MvPolynomial σ R)] (1 : (MvPolynomial σ B))) =
      mvPolynomialMapOver (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) p :=
  mvPolynomialTensorTo_left p

end
end MaximalSeshadri.BertiniIntegral

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_Derivations
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

def doubledBaseChangeEquiv {P F B : Type*} [CommRing P] [CommRing F]
    [CommRing B] [Algebra P F] [Algebra P B] :
    ((F ⊗[P] B) ⊗[F] (F ⊗[P] B)) ≃ₐ[F] F ⊗[P] (B ⊗[P] B) :=
  (Algebra.TensorProduct.tensorTensorTensorComm P P F F F B F B).trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.lid F F) (AlgEquiv.refl :
      (B ⊗[P] B) ≃ₐ[P] B ⊗[P] B))

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_GeometricDomains
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial

def rootBaseChangeEquiv {K F : Type*} [Field K] [Field F] [Algebra K F]
    (p : K[X]) : F ⊗[K] AdjoinRoot p ≃ₐ[F] AdjoinRoot (p.map (algebraMap K F)) := by
  let p' : (F ⊗[K] K)[X] := p.map Algebra.TensorProduct.includeRight.toRingHom
  refine (AdjoinRoot.tensorAlgEquiv p p' rfl).trans
    (AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid K F F) p'
      (p.map (algebraMap K F)) ?_)
  apply Associated.of_eq
  dsimp [p']
  rw [Polynomial.map_map]
  congr 1
  ext x
  simp [Algebra.smul_def]

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_HyperplaneFamilies
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial

@[instance_reducible] def hyperplaneFamilyAlgebra {K A σ : Type*} [CommRing K] [CommRing A]
    [Algebra K A] [Fintype σ] (v : σ → A) :
    Algebra (MvPolynomial σ K)[X] (MvPolynomial σ A) :=
  (Polynomial.aeval (homogeneousLinearForm v) :
    (MvPolynomial σ K)[X] →ₐ[MvPolynomial σ K] MvPolynomial σ A).toRingHom.toAlgebra

instance hyperplaneFamilyAlgebra_tower {K A σ : Type*} [CommRing K] [CommRing A]
    [Algebra K A] [Fintype σ] (v : σ → A) :
    let := hyperplaneFamilyAlgebra (K := K) v
    IsScalarTower (MvPolynomial σ K) (MvPolynomial σ K)[X] (MvPolynomial σ A) := by
  let := hyperplaneFamilyAlgebra (K := K) v
  apply IsScalarTower.of_algebraMap_eq
  intro p
  change algebraMap (MvPolynomial σ K) (MvPolynomial σ A) p =
    Polynomial.aeval (homogeneousLinearForm v) (Polynomial.C p)
  rw [Polynomial.aeval_C]

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_EtaleCoordinates
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open MvPolynomial
open scoped TensorProduct
variable {K σ : Type*} [CommRing K]

abbrev coordinateDifference : MvPolynomial σ K →ₐ[K]
    MvPolynomial σ K ⊗[K] MvPolynomial σ K :=
  aeval fun i => (X i : MvPolynomial σ K) ⊗ₜ[K] (1 : MvPolynomial σ K) -
    (1 : MvPolynomial σ K) ⊗ₜ[K] (X i : MvPolynomial σ K)

abbrev coordinateSum : MvPolynomial σ K →ₐ[K]
    MvPolynomial σ K ⊗[K] MvPolynomial σ K :=
  aeval fun i => (X i : MvPolynomial σ K) ⊗ₜ[K] (1 : MvPolynomial σ K) +
    (1 : MvPolynomial σ K) ⊗ₜ[K] (X i : MvPolynomial σ K)

abbrev shearMinus : (MvPolynomial σ K ⊗[K] MvPolynomial σ K) →ₐ[K]
    MvPolynomial σ K ⊗[K] MvPolynomial σ K :=
  Algebra.TensorProduct.lift coordinateDifference Algebra.TensorProduct.includeRight
    (fun _ _ => Commute.all _ _)

abbrev shearPlus : (MvPolynomial σ K ⊗[K] MvPolynomial σ K) →ₐ[K]
    MvPolynomial σ K ⊗[K] MvPolynomial σ K :=
  Algebra.TensorProduct.lift coordinateSum Algebra.TensorProduct.includeRight
    (fun _ _ => Commute.all _ _)

lemma shearMinus_plus : (shearMinus (K := K) (σ := σ)).comp shearPlus = .id _ _ := by
  apply Algebra.TensorProduct.ext
  · apply MvPolynomial.algHom_ext
    intro i
    simp [AlgHom.comp_apply, shearMinus, shearPlus, coordinateSum, coordinateDifference,
      ← Algebra.TensorProduct.one_def]
  · apply MvPolynomial.algHom_ext
    intro i
    simp [AlgHom.comp_apply, shearMinus, shearPlus, coordinateSum, coordinateDifference]

lemma shearPlus_minus : (shearPlus (K := K) (σ := σ)).comp shearMinus = .id _ _ := by
  apply Algebra.TensorProduct.ext
  · apply MvPolynomial.algHom_ext
    intro i
    simp [AlgHom.comp_apply, shearMinus, shearPlus, coordinateSum, coordinateDifference,
      ← Algebra.TensorProduct.one_def]
  · apply MvPolynomial.algHom_ext
    intro i
    simp [AlgHom.comp_apply, shearMinus, shearPlus, coordinateSum, coordinateDifference]

def shearEquiv : (MvPolynomial σ K ⊗[K] MvPolynomial σ K) ≃ₐ[K]
    MvPolynomial σ K ⊗[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom shearMinus shearPlus shearMinus_plus shearPlus_minus

def chartDifference {A : Type*} [CommRing A] [Algebra K A]
    (φ : MvPolynomial σ K →ₐ[K] A) : MvPolynomial σ K →ₐ[K] A ⊗[K] A :=
  (Algebra.TensorProduct.map φ φ).comp coordinateDifference

@[simp] lemma chartDifference_X {A : Type*} [CommRing A] [Algebra K A]
    (φ : MvPolynomial σ K →ₐ[K] A) (i : σ) :
    chartDifference φ (X i) = φ (X i) ⊗ₜ[K] (1 : A) -
      (1 : A) ⊗ₜ[K] φ (X i) := by
  simp [chartDifference]

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open KaehlerDifferential
open scoped TensorProduct

variable {K A σ : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [Algebra (MvPolynomial σ K) A] [IsScalarTower K (MvPolynomial σ K) A]
  [Algebra.FormallyEtale (MvPolynomial σ K) A]

def etaleCotangentCoordinate (j : σ) : Ω[A⁄K] →ₗ[A] A :=
  (((mvPolynomialBasis K σ).baseChange A).coord j).comp
    (tensorKaehlerEquivOfFormallyEtale K (MvPolynomial σ K) A).symm.toLinearMap

@[simp] theorem etaleCotangentCoordinate_X [DecidableEq σ] (i j : σ) :
    etaleCotangentCoordinate (K := K) (A := A) j
      (D K A (algebraMap (MvPolynomial σ K) A (MvPolynomial.X i))) =
        if i = j then 1 else 0 := by
  rw [etaleCotangentCoordinate, LinearMap.comp_apply, LinearEquiv.coe_coe,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  rw [← mvPolynomialBasis_apply, ← Module.Basis.baseChange_apply]
  simp [Module.Basis.coord_apply, Finsupp.single_apply]
end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_CountableSpecialization
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

def polynomialQuotientBaseChange {R K n : Type*} [CommRing R] [CommRing K]
    [Algebra R K] (I : Ideal (MvPolynomial n R)) :
    (K ⊗[R] (MvPolynomial n R ⧸ I)) ≃ₐ[K]
      MvPolynomial n K ⧸ I.map (MvPolynomial.map (algebraMap R K)) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := n) R K
  refine (Algebra.TensorProduct.tensorQuotientEquiv K (MvPolynomial n R) K I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change I.map (MvPolynomial.map (algebraMap R K)) =
    (I.map (Algebra.TensorProduct.includeRight : MvPolynomial n R →ₐ[R]
      K ⊗[R] MvPolynomial n R).toRingHom).map e.toRingHom
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  change MvPolynomial.map (algebraMap R K) p = e (1 ⊗ₜ[R] p)
  simp [e]

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_Descent
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

def doubleBaseChange {R K A : Type*} [CommRing R] [CommRing K] [CommRing A]
    [Algebra R K] [Algebra R A] :
    (K ⊗[R] (A ⊗[R] A)) ≃ₐ[K] ((K ⊗[R] A) ⊗[K] (K ⊗[R] A)) :=
  (Algebra.TensorProduct.assoc R R K K A A).symm.trans
    (Algebra.TensorProduct.cancelBaseChange R K K (K ⊗[R] A) A).symm

@[simp] lemma doubleBaseChange_tmul {R K A : Type*} [CommRing R] [CommRing K] [CommRing A]
    [Algebra R K] [Algebra R A] (k : K) (a b : A) :
    (doubleBaseChange (R := R) (K := K) (A := A)) (k ⊗ₜ[R] (a ⊗ₜ[R] b)) =
      (k ⊗ₜ[R] a) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] b) := by
  simp [doubleBaseChange]

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_SimultaneousHyperplanes
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra
variable {K σ : Type} [Field K]

def restrictHyperplaneHom {S T : Subfield K} (h : S ≤ T)
    (f : (MvPolynomial σ T)[X] →ₐ[T] K) : (MvPolynomial σ S)[X] →ₐ[S] K where
  toRingHom := f.toRingHom.comp (Polynomial.mapRingHom (MvPolynomial.map (Subfield.inclusion h)))
  commutes' s := by
    change f (Polynomial.map (MvPolynomial.map (Subfield.inclusion h))
      (C (MvPolynomial.C s))) = (s : K)
    simp only [map_C, MvPolynomial.map_C]
    exact f.commutes (Subfield.inclusion h s)

@[simp] lemma restrictHyperplaneHom_X {S T : Subfield K} (h : S ≤ T)
    (f : (MvPolynomial σ T)[X] →ₐ[T] K) : restrictHyperplaneHom h f X = f X := by
  change f (Polynomial.map _ X) = f X
  rw [Polynomial.map_X]

@[simp] lemma restrictHyperplaneHom_CX {S T : Subfield K} (h : S ≤ T)
    (f : (MvPolynomial σ T)[X] →ₐ[T] K) (i : σ) :
    restrictHyperplaneHom h f (C (MvPolynomial.X i)) = f (C (MvPolynomial.X i)) := by
  change f (Polynomial.map _ (C (MvPolynomial.X i))) = f (C (MvPolynomial.X i))
  simp only [map_C, MvPolynomial.map_X]

end

end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_GenericSmoothness
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral

noncomputable section
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra
variable {K S σ : Type*} [Field K] [CommRing S] [Algebra S K]

def hyperplaneVariable (o : Option σ) : (MvPolynomial σ S)[X] :=
  o.elim X (fun i => C (MvPolynomial.X i))

def permuteHyperplaneHom (e : Option σ ≃ Option σ)
    (f : (MvPolynomial σ S)[X] →ₐ[S] K) : (MvPolynomial σ S)[X] →ₐ[S] K :=
  f.comp (((MvPolynomial.optionEquivLeft S σ).symm.trans
    ((MvPolynomial.renameEquiv S e).trans (MvPolynomial.optionEquivLeft S σ))).toAlgHom)

@[simp] lemma permuteHyperplaneHom_variable (e : Option σ ≃ Option σ)
    (f : (MvPolynomial σ S)[X] →ₐ[S] K) (o : Option σ) :
    permuteHyperplaneHom e f (hyperplaneVariable o) =
      f (hyperplaneVariable (e o)) := by
  have hv (a : Option σ) : MvPolynomial.optionEquivLeft S σ (MvPolynomial.X a) =
      hyperplaneVariable a := by cases a <;> simp [hyperplaneVariable]
  rw [← hv o]
  simp only [permuteHyperplaneHom, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, hv]

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_AffineDenominators
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
noncomputable section
universe u
open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
open PrimeSpectrum
namespace MaximalSeshadri.AffineDenominators
variable {R : CommRingCat.{u}} (M : (Spec R).Modules)

def basicOpen (element : R) : (Spec R).Opens := PrimeSpectrum.basicOpen element

lemma basicOpen_mul (left right : R) :
    basicOpen (left * right) = basicOpen left ⊓ basicOpen right :=
  PrimeSpectrum.basicOpen_mul left right

lemma basicOpen_mul_le_left (left right : R) :
    basicOpen (left * right) ≤ basicOpen left :=
  PrimeSpectrum.basicOpen_mul_le_left left right

lemma basicOpen_mul_le_right (left right : R) :
    basicOpen (left * right) ≤ basicOpen right :=
  PrimeSpectrum.basicOpen_mul_le_right left right

lemma moduleIsSheaf :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology (Spec R)) M.presheaf :=
  M.isSheaf

/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel, Jujian Zhang, Weihong Xu,
  Andrew Yang, Brian Nugent

The auxiliary denominator construction below is adapted from Mathlib.AlgebraicGeometry.Modules.Tilde.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/AlgebraicGeometry/Modules/Tilde.lean

This code has been modified.
-/

structure Aux (V : (Spec R).Opens) where
  existence (f : R) (hf : basicOpen f ≤ V) (s : Γ(M, basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, V)), M.presheaf.map (homOfLE hf).op t = f ^ n • s
  uniqueness (f : R) (hf : basicOpen f ≤ V) (t : Γ(M, V)) :
    M.presheaf.map (.op <| homOfLE hf) t = (0 : Γ(M, basicOpen f)) →
    ∃ (n : ℕ), f ^ n • t = 0

lemma Aux.of_le {M : (Spec R).Modules} {V : (Spec R).Opens} (g : R) (hg : basicOpen g ≤ V)
    (hV : Aux M V) :
    Aux M (basicOpen g) where
  existence f hfg s := by
    obtain ⟨n, t, ht⟩ := hV.existence f (le_trans hfg hg) s
    use n, M.presheaf.map (homOfLE hg).op t
    simp [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, ht]
  uniqueness f hfg t ht := by
    obtain ⟨n, t', ht'⟩ := hV.existence g hg t
    obtain ⟨m, hm⟩ := hV.uniqueness _ (le_trans hfg hg) t' <| by
      rw [← homOfLE_comp hfg hg, op_comp, M.presheaf.map_comp_apply, ht', M.map_smul_Spec, ht]
      simp
    refine ⟨m, ((M.isSMulRegular_of_le_basicOpen (U := basicOpen g) (f := g)
      le_rfl).pow n).right_eq_zero_of_smul ?_⟩
    simp [smul_comm, ← ht', ← M.map_smul_Spec, hm]

lemma Aux.of_eq_iSup_basicOpen {M : (Spec R).Modules} (V : (Spec R).Opens)
    {ι : Type*} [Finite ι] (g : ι → R) (hg : V = ⨆ i, basicOpen (g i))
    (h₁ : ∀ (i : ι), Aux M (basicOpen (g i))) :
    Aux M V := by
  have h₂ (i j : ι) : Aux M (basicOpen (g i * g j)) :=
    .of_le _ (basicOpen_mul_le_left _ _) (h₁ i)
  have hgle (i : ι) : basicOpen (g i) ≤ V := by rw [hg]; exact le_iSup_of_le _ le_rfl
  have hug (i : ι) (m : ℕ) :
      IsUnit (algebraMap R (Module.End R Γ(M, basicOpen (g i))) (g i ^ m)) := by
    rw [map_pow]
    exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (g i) le_rfl).pow m
                                                 
  refine ⟨fun f hf s ↦ ?_, fun f hf t hs ↦ ?_⟩
  · have hfgi (i : ι) : basicOpen (f * g i) ≤ basicOpen (g i) := basicOpen_mul_le_right f (g i)
    let s' (i : ι) : Γ(M, basicOpen (f * g i)) :=
      M.presheaf.map (homOfLE <| basicOpen_mul_le_left f (g i)).op s

    obtain ⟨N, t, ht⟩ : ∃ (N : ℕ) (t : ∀ i, Γ(M, basicOpen (g i))),
        ∀ i, f ^ N • s' i = M.presheaf.map (homOfLE (basicOpen_mul_le_right f (g i))).op (t i) := by
      have (i : ι) : ∃ (n : ℕ) (t : Γ(M, basicOpen (g i))),
          f ^ n • s' i = M.presheaf.map (homOfLE (hfgi i)).op t := by
        obtain ⟨n, t', ht'⟩ := (h₁ i).existence (f * g i) (hfgi i) (s' i)
        rw [mul_pow, mul_smul, smul_comm] at ht'
        obtain ⟨ψ, hψ⟩ := IsUnit.exists_right_inv (hug i n)
        use n, ψ t'
        apply (M.isSMulRegular_of_le_basicOpen (U := basicOpen (f * g i))
          (basicOpen_mul_le_right f (g i))).pow n
        dsimp
        rw [← ht', ← Scheme.Modules.map_smul_Spec]
        congr 1
        exact congr($hψ t').symm
      choose n t' ht' using this
      have (i : ι) : n i ≤ ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have hN (i : ι) : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by grind
      refine ⟨⨆ i, n i, fun i ↦ f ^ ((⨆ i, n i) - n i) • t' i, fun i ↦ ?_⟩
      conv_lhs => rw [hN i]
      rw [pow_add, mul_smul, ht', M.map_smul_Spec]

    obtain ⟨K, hK⟩ : ∃ (K : ℕ), ∀ (i j : ι),
        M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (f ^ K • t i) =
          M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (f ^ K • t j) := by
      have (i j : ι) : ∃ (m : ℕ),
          M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (f ^ m • t i) =
            M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (f ^ m • t j) := by
        have := (h₂ i j).uniqueness (f * (g i * g j)) (basicOpen_mul_le_right _ _)
          (M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (t i) -
            M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (t j)) ?_
        · obtain ⟨m, hm⟩ := this
          use m
          apply (M.isSMulRegular_of_le_basicOpen (U := basicOpen (g i * g j))
            (f := g i * g j) le_rfl).pow m
          simpa [M.map_smul_Spec _ (f ^ m), ← mul_smul, ← mul_smul, ← mul_pow, ← mul_comm f,
            smul_sub, sub_eq_zero] using hm
        · have hfgigi : basicOpen (f * (g i * g j)) ≤ basicOpen (f * g i) := by
            rw [← mul_assoc]
            exact basicOpen_mul_le_left _ _
          have hfgigj : basicOpen (f * (g i * g j)) ≤ basicOpen (f * g j) := by
            rw [mul_comm (g i) (g j), ← mul_assoc]
            exact basicOpen_mul_le_left _ _
          rw [map_sub, ← M.presheaf.map_comp_apply, ← op_comp, ← M.presheaf.map_comp_apply,
            ← op_comp, homOfLE_comp, homOfLE_comp, ← homOfLE_comp hfgigi (hfgi i),
            ← homOfLE_comp hfgigj (hfgi j), op_comp, M.presheaf.map_comp_apply, ← ht i,
            M.map_smul_Spec, ← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, op_comp,
            M.presheaf.map_comp_apply, ← ht j, M.map_smul_Spec, ← M.presheaf.map_comp_apply,
            ← op_comp, homOfLE_comp]
          simp
      choose m hm using this
      let K := ⨆ i, ⨆ j, m i j
      refine ⟨K, fun i j ↦ ?_⟩
      have : m i j ≤ K :=
        le_ciSup_of_le (Finite.bddAbove_range _) i (le_ciSup (Finite.bddAbove_range _) _)
      have : K = (K - m i j) + m i j := by lia
      rw [this, pow_add, mul_smul, mul_smul, M.map_smul_Spec, M.map_smul_Spec _ (f ^ (K - m i j)),
        hm i j]
                                                         
    refine ⟨N + K, ?_⟩
    have := TopCat.Sheaf.existsUnique_gluing' ⟨_, moduleIsSheaf M⟩ (fun i ↦ basicOpen (g i)) V
      (fun i ↦ homOfLE (by rw [hg]; exact le_iSup_of_le _ le_rfl)) (by simp [hg])
      (fun i ↦ f ^ K • t i) ?_
    · obtain ⟨a, ha, -⟩ := this
      use a
      refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, moduleIsSheaf M⟩ (fun i ↦ basicOpen (f * g i)) _
          (fun i ↦ homOfLE (basicOpen_mul_le_left f (g i))) ?_ _ _ ?_
      · rw [left_eq_inf.mpr hf, hg, inf_iSup_eq]
        simp_rw [basicOpen_mul]
        exact le_rfl
      · intro i
        rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp (basicOpen_mul_le_right _ _) (hgle i), op_comp, M.presheaf.map_comp_apply,
          M.map_smul_Spec, ha, M.map_smul_Spec, pow_add, mul_smul, smul_comm, ht i]
    · intro i j
      have : Function.Injective (M.presheaf.map (eqToHom <| (basicOpen_mul (g i) (g j))).op) :=
        ConcreteCategory.injective_of_mono_of_preservesPullback _
      apply this
      dsimp [Opens.infLELeft, Opens.infLERight]
      simp_rw [← M.presheaf.map_comp_apply, ← op_comp, eqToHom_comp_homOfLE]
      exact hK i j
  · have (i : ι) : ∃ (n : ℕ), M.presheaf.map (homOfLE (hgle i)).op (f ^ n • t) = 0 := by
      have := (h₁ i).uniqueness (f * g i) (basicOpen_mul_le_right f (g i))
        (M.presheaf.map (homOfLE (hgle i)).op t) ?_
      · obtain ⟨n, hn⟩ := this
        use n
        rw [mul_pow, mul_comm, mul_smul, ← Scheme.Modules.map_smul_Spec] at hn
        exact ((M.isSMulRegular_of_le_basicOpen (U := basicOpen (g i))
          (f := g i) le_rfl).pow n).right_eq_zero_of_smul hn
      · rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp ((basicOpen_mul_le_left f (g i))) hf, op_comp, M.presheaf.map_comp_apply]
        simp [hs]
    choose n hn using this
    use ⨆ i, n i
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, moduleIsSheaf M⟩ (fun i ↦ basicOpen (g i)) _
      (fun i ↦ homOfLE (by rw [hg]; exact le_iSup_of_le _ le_rfl))
    · simp [hg]
    · intro i
      have : n i ≤ ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by lia
      rw [this, pow_add, mul_smul, Scheme.Modules.map_smul_Spec, hn i]
      simp

lemma isLocalizing_iff_aux (M : (Spec R).Modules) :
    IsLocalizing (modulesSpecToSheaf.obj M) ↔ Aux M ⊤ := by
  let φ (f : R) := ((modulesSpecToSheaf.obj M).obj.map (basicOpen f).leTop.op).hom
  refine ⟨fun h ↦ ?_, fun h f ↦ IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_⟩
  · have hf (f : R) : IsLocalizedModule.Away f (φ f) := h f
    refine ⟨fun f hle s ↦ ?_, fun f hle s hs ↦ ?_⟩
    · obtain ⟨n, y, hy⟩ := (hf f).surj _ _ s
      use n, y, hy.symm
    · obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers f) (φ f)).mp hs
      use n, hn
  · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl
  · intro x
    obtain ⟨n, t, ht⟩ := h.existence f le_top x
    use n, t, ht.symm
  · intro x hx
    obtain ⟨n, hn⟩ := h.uniqueness _ _ _ hx
    use n, hn

theorem aux_of_isCompact (V : (Spec R).Opens) (hV : IsCompact (V : Set (Spec R)))
    (h : IsLocalizing (modulesSpecToSheaf.obj M)) : Aux M V := by
  obtain ⟨ι, hι, g, hg⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact V hV
  let := hι
  exact Aux.of_eq_iSup_basicOpen V g hg (fun i =>
    Aux.of_le (g i) le_top ((isLocalizing_iff_aux M).mp h))

variable {M}

def res (U V : (Spec R).Opens) (h : U ≤ V) : Γ(M,V) →ₗ[R] Γ(M,U) :=
  ((modulesSpecToSheaf.obj M).obj.map (homOfLE h).op).hom

lemma res_comp {U V W : (Spec R).Opens} (h : U ≤ V) (k : V ≤ W) (s : Γ(M,W)) :
    res U V h (M := M) (res V W k s) = res U W (h.trans k) s := by
  exact (M.presheaf.map_comp_apply (homOfLE k).op (homOfLE h).op s).symm

lemma eq_zero_of_cover {ι : Type*} (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, basicOpen (g i)) (s : Γ(M,U))
    (h : ∀ i, res (basicOpen (g i)) U (hU ▸ le_iSup_of_le i le_rfl) s = 0) : s = 0 := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, moduleIsSheaf M⟩ (fun i => basicOpen (g i)) U
    (fun i => homOfLE (hU ▸ le_iSup_of_le i le_rfl)) (by rw [hU])
  intro i
  change res (basicOpen (g i)) U _ s = res (basicOpen (g i)) U _ 0
  rw [map_zero]
  exact h i

lemma power_in_ideal_of_generator_powers {ι : Type*} [Finite ι]
    (g : ι → R) (J : Ideal R) (h : ∀ i, ∃ n : ℕ, g i ^ n ∈ J) :
    ∃ n : ℕ, Ideal.span (Set.range g) ^ n ≤ J := by
  apply Ideal.exists_pow_le_of_le_radical_of_fg
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact h i
  · exact Submodule.fg_span (Set.finite_range g)

lemma kernel_is_torsion {ι : Type*} [Finite ι] (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, basicOpen (g i))
    (hloc : IsLocalizing (modulesSpecToSheaf.obj M)) (s : Γ(M,⊤))
    (hs : res U ⊤ le_top s = 0) :
    ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n, a • s = 0 := by
  let J : Ideal R := (LinearMap.toSpanSingleton R Γ(M,⊤) s).ker
  have hgen : ∀ i, ∃ n : ℕ, g i ^ n ∈ J := by
    intro i
    apply ((isLocalizing_iff_aux M).mp hloc).uniqueness (g i) le_top s
    change res (basicOpen (g i)) ⊤ le_top s = 0
    rw [← res_comp (hU ▸ le_iSup_of_le i le_rfl) le_top, hs, map_zero]
  obtain ⟨n,hn⟩ := power_in_ideal_of_generator_powers g J hgen
  exact ⟨n,fun a ha => hn ha⟩

lemma torsion_free {ι : Type*} (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, basicOpen (g i)) (s : Γ(M,U))
    (hs : ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n, a • s = 0) : s = 0 := by
  obtain ⟨n,hn⟩ := hs
  apply eq_zero_of_cover g U hU s
  intro i
  have hm : g i ^ n ∈ Ideal.span (Set.range g) ^ n :=
    Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) n
  have h := congrArg (res (basicOpen (g i)) U (hU ▸ le_iSup_of_le i le_rfl)) (hn _ hm)
  rw [map_smul, map_zero] at h
  exact ((M.isSMulRegular_of_le_basicOpen (U := basicOpen (g i))
    (f := g i) le_rfl).pow n).right_eq_zero_of_smul h

lemma torsion_in_kernel {ι : Type*} (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, basicOpen (g i)) (s : Γ(M,⊤))
    (hs : ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n, a • s = 0) :
    res U ⊤ le_top s = 0 := by
  apply torsion_free g U hU
  obtain ⟨n,hn⟩ := hs
  refine ⟨n,fun a ha => ?_⟩
  rw [← map_smul, hn a ha, map_zero]

lemma cokernel_is_torsion {ι : Type*} [Finite ι] (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, basicOpen (g i)) (hU' : IsCompact (U : Set (Spec R)))
    (hloc : IsLocalizing (modulesSpecToSheaf.obj M)) (s : Γ(M,U)) :
    ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n,
      a • s ∈ (res U ⊤ le_top (M := M)).range := by
  let J : Ideal R := (res U ⊤ le_top (M := M)).range.comap
    (LinearMap.toSpanSingleton R Γ(M,U) s)
  have hgen : ∀ i, ∃ n : ℕ, g i ^ n ∈ J := by
    intro i
    let hgi : basicOpen (g i) ≤ U := hU ▸ le_iSup_of_le i le_rfl
    obtain ⟨m,t,ht⟩ := ((isLocalizing_iff_aux M).mp hloc).existence (g i) le_top
      (res (basicOpen (g i)) U hgi s)
    have hzero : res (basicOpen (g i)) U hgi (res U ⊤ le_top t - g i ^ m • s) = 0 := by
      rw [map_sub, map_smul, res_comp]
      exact sub_eq_zero.mpr ht
    obtain ⟨n,hn⟩ := (aux_of_isCompact M U hU' hloc).uniqueness (g i) hgi _ hzero
    refine ⟨n+m, ?_⟩
    change g i ^ (n+m) • s ∈ (res U ⊤ le_top (M := M)).range
    refine ⟨g i ^ n • t, ?_⟩
    rw [map_smul, pow_add, mul_smul]
    exact sub_eq_zero.mp (by simpa only [smul_sub] using hn)
  obtain ⟨n,hn⟩ := power_in_ideal_of_generator_powers g J hgen
  exact ⟨n,fun a ha => hn ha⟩

end MaximalSeshadri.AffineDenominators

end


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_Injectives
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.InjectiveRange
noncomputable section
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Small.{v} R]
variable {N : Type w} [AddCommGroup N] [Module R N] [Small.{w} R]

omit [Small.{w} R] in
                                                            
lemma injective_of_retract [Module.Injective R M]
    (i : N →ₗ[R] M) (p : M →ₗ[R] N) (h : p.comp i = LinearMap.id) :
    Module.Injective R N := by
  apply Module.Baer.injective
  intro J g
  obtain ⟨f, hf⟩ := Module.Baer.of_injective (R := R) (Q := M) inferInstance J (i.comp g)
  refine ⟨p.comp f, fun x hx => ?_⟩
  change p (f x) = g ⟨x,hx⟩
  rw [hf x hx]
  exact LinearMap.congr_fun h (g ⟨x,hx⟩)

omit [Small.{w} R] in
lemma range_injective (r : M →ₗ[R] N) [Module.Injective R M]
    [Module.Injective R r.ker] : Module.Injective R r.range := by
  obtain ⟨p, hp⟩ := Module.Injective.extension_property R r.ker r.ker M
    r.ker.subtype Subtype.val_injective LinearMap.id
  let f : M →ₗ[R] M := LinearMap.id - r.ker.subtype.comp p
  have hf : r.ker ≤ f.ker := by
    intro x hx
    change x - (p x : M) = 0
    have hpx := LinearMap.congr_fun hp ⟨x,hx⟩
    exact sub_eq_zero.mpr (congrArg Subtype.val hpx).symm
  let i : r.range →ₗ[R] M := (r.ker.liftQ f hf).comp r.quotKerEquivRange.symm.toLinearMap
  apply injective_of_retract i r.rangeRestrict
  ext y
  rcases y with ⟨y,hy⟩
  obtain ⟨x,rfl⟩ := hy
  change r ((r.ker.liftQ f hf) (r.quotKerEquivRange.symm ⟨r x, LinearMap.mem_range_self r x⟩)) = r x
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  change r (x - (p x : M)) = r x
  rw [map_sub, (p x).property, sub_zero]

lemma surjective_of_torsion_cokernel (I : Ideal R) (r : M →ₗ[R] N)
    [Module.Injective R M] [Module.Injective R r.ker]
    (hc : ∀ y : N, ∃ n : ℕ, ∀ a ∈ I ^ n, a • y ∈ r.range)
    (ht : ∀ y : N, (∃ n : ℕ, ∀ a ∈ I ^ n, a • y = 0) → y = 0) :
    Function.Surjective r := by
  let : Module.Injective R r.range := range_injective r
  obtain ⟨p, hp⟩ := Module.Injective.extension_property R r.range r.range N
    r.range.subtype Subtype.val_injective LinearMap.id
  intro y
  suffices h : y = (p y : N) from h ▸ (p y).property
  apply sub_eq_zero.mp
  apply ht
  obtain ⟨n, hn⟩ := hc y
  refine ⟨n, fun a ha => ?_⟩
  rw [smul_sub]
  have h := congrArg Subtype.val (LinearMap.congr_fun hp ⟨a • y, hn a ha⟩)
  change (p (a • y) : N) = a • y at h
  rw [map_smul] at h
  exact sub_eq_zero.mpr h.symm

end
end MaximalSeshadri.InjectiveRange

end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SheafExactness
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section

namespace MaximalSeshadri.TildeExact
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {R : CommRingCat.{u}}

instance map_mono {M N : ModuleCat.{u} R} (f : M ⟶ N) [Mono f] : Mono (tilde.map f) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U s t h
  apply Subtype.ext
  funext x
  haveI : x.1.asIdeal.IsPrime := x.1.isPrime
  apply LocalizedModule.map_injective x.1.asIdeal.primeCompl f.hom
    ((ModuleCat.mono_iff_injective f).mp inferInstance)
  exact congrFun (congrArg Subtype.val h) x

instance preservesMonomorphisms : (tilde.functor R).PreservesMonomorphisms where
  preserves f _ := map_mono f

instance preservesHomology : (tilde.functor R).PreservesHomology :=
  (tilde.functor R).preservesHomology_of_preservesMonos_and_cokernels

end
end MaximalSeshadri.TildeExact

namespace MaximalSeshadri.ModuleGrothendieck
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
variable {C : Type u} [Category.{u} C] (R₀ : Cᵒᵖ ⥤ RingCat.{u})

instance presheafAB5 : AB5 (PresheafOfModules.{u} R₀) where
  ofShape J _ _ := HasExactColimitsOfShape.domain_of_functor J
    (PresheafOfModules.toPresheaf R₀)

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}]

instance sheafAB5 : AB5 (SheafOfModules.{u} R) where
  ofShape K _ _ :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K

lemma freeSheafSeparating :
    ObjectProperty.IsSeparating (.ofObj (fun U : C =>
      (PresheafOfModules.sheafification (𝟙 R.obj)).obj
        ((PresheafOfModules.free R.obj).obj (yoneda.obj U)))) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  intro M N f g h
  apply (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map_injective
  apply PresheafOfModules.freeYoneda.isSeparating R.obj
  intro P hP a
  obtain ⟨U⟩ := hP
  obtain ⟨b, rfl⟩ := (adj.homEquiv _ _).surjective a
  rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_right]
  exact congrArg (adj.homEquiv _ _) (h _ ⟨U⟩ b)

instance sheafHasSeparator : HasSeparator (SheafOfModules.{u} R) :=
  ⟨⟨∐ (fun U : C => (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj (yoneda.obj U))),
    (freeSheafSeparating R).isSeparator_coproduct⟩⟩

instance sheafGrothendieck : IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) where

theorem enoughInjectives : EnoughInjectives (SheafOfModules.{u} R) := inferInstance

end
end MaximalSeshadri.ModuleGrothendieck

namespace MaximalSeshadri.ModuleFlasque
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

abbrev freeOpen (U : Opens X) : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj (yoneda.obj U))

abbrev freeOpenMap {U V : Opens X} (i : U ⟶ V) : freeOpen R U ⟶ freeOpen R V :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((PresheafOfModules.free R.obj).map (yoneda.map i))

lemma freeMap_mono {F G : (Opens X)ᵒᵖ ⥤ Type u} (f : F ⟶ G) [Mono f] :
    Mono ((PresheafOfModules.free R.obj).map f) := by
  apply PresheafOfModules.mono_of_injective
  intro W
  change Function.Injective (Finsupp.mapDomain (f.app W))
  exact Finsupp.mapDomain_injective ((CategoryTheory.mono_iff_injective (f.app W)).mp
    inferInstance)

instance freeOpenMap_mono {U V : Opens X} (i : U ⟶ V) : Mono (freeOpenMap R i) := by
  let := freeMap_mono R (yoneda.map i)
  dsimp [freeOpenMap]
  infer_instance

def freeOpenEquiv (M : SheafOfModules.{u} R) (U : Opens X) :
    (freeOpen R U ⟶ M) ≃ M.val.obj (op U) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
    PresheafOfModules.freeYonedaEquiv

lemma freeYoneda_naturality {M : PresheafOfModules.{u} R.obj} {U V : Opens X}
    (i : U ⟶ V) (f : (PresheafOfModules.free R.obj).obj (yoneda.obj V) ⟶ M) :
    PresheafOfModules.freeYonedaEquiv
      ((PresheafOfModules.free R.obj).map (yoneda.map i) ≫ f) =
      M.map i.op (PresheafOfModules.freeYonedaEquiv f) := by
  have h := (PresheafOfModules.freeAdjunction R.obj).homEquiv_naturality_left
    (yoneda.map i) f
  simp only [PresheafOfModules.freeAdjunction_homEquiv] at h
  exact (congrArg yonedaEquiv h).trans
    (yonedaEquiv_naturality (PresheafOfModules.freeHomEquiv f) i).symm

lemma freeOpenEquiv_naturality (M : SheafOfModules.{u} R) {U V : Opens X}
    (i : U ⟶ V) (f : freeOpen R V ⟶ M) :
    freeOpenEquiv R M U (freeOpenMap R i ≫ f) =
      M.val.map i.op (freeOpenEquiv R M V f) := by
  unfold freeOpenEquiv
  dsimp only [Equiv.trans_apply]
  change PresheafOfModules.freeYonedaEquiv
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _ (_ ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact freeYoneda_naturality R i
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)) f)

theorem restriction_surjective (M : SheafOfModules.{u} R) [Injective M]
    {U V : Opens X} (i : U ⟶ V) : Function.Surjective (M.val.map i.op) := by
  intro s
  let f := (freeOpenEquiv R M U).symm s
  obtain ⟨g, hg⟩ := Injective.factors f (freeOpenMap R i)
  refine ⟨freeOpenEquiv R M V g, ?_⟩
  rw [← freeOpenEquiv_naturality, hg]
  exact (freeOpenEquiv R M U).apply_symm_apply s

instance injective_isFlasque (M : SheafOfModules.{u} R) [Injective M] :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M) where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    exact restriction_surjective R M i.unop

end
end MaximalSeshadri.ModuleFlasque

namespace MaximalSeshadri.ModuleSheafExact
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]

instance toSheafPreservesColimit {K : Type u} [Category.{u} K]
    (D : K ⥤ SheafOfModules.{u} R) : PreservesColimit D (SheafOfModules.toSheaf R) := by
  let F := PresheafOfModules.sheafification (𝟙 R.obj)
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let H := SheafOfModules.toSheaf R
  let adj : F ⊣ G := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  have : PreservesColimitsOfSize.{u,u} (F ⋙ H) :=
    inferInstanceAs (PreservesColimitsOfSize.{u,u}
      (PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat))
  have : PreservesColimit (D ⋙ G ⋙ F) H :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves F (colimit.isColimit (D ⋙ G)))
      (isColimitOfPreserves (F ⋙ H) (colimit.isColimit (D ⋙ G)))
  exact preservesColimit_of_iso_diagram H
    ((Functor.isoWhiskerLeft D (asIso adj.counit)) ≪≫ D.rightUnitor)

instance toSheafPreservesColimits :
    PreservesColimitsOfSize.{u,u} (SheafOfModules.toSheaf.{u} R) where
  preservesColimitsOfShape := ⟨fun {_} => inferInstance⟩

theorem shortExact_map {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact) :
    (S.map (SheafOfModules.toSheaf R)).ShortExact := hS.map_of_exact _

end
end MaximalSeshadri.ModuleSheafExact


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_AffineVanishing
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.FlasqueCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Abelian
universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def sectionsTopEquiv (M : SheafOfModules.{u} R) : M.sections ≃ M.val.obj (op ⊤) where
  toFun s := s.val (op ⊤)
  invFun t := PresheafOfModules.sectionsMk
    (fun U => M.val.map (homOfLE le_top).op t)
    (by
      intro U V i
      rw [← M.val.map_comp_apply]
      exact M.val.congr_map_apply (Subsingleton.elim _ _) t)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE le_top).op
  right_inv t := by
    change M.val.map (𝟙 (op ⊤)) t = t
    rw [M.val.map_id]
    rfl

def globalHomEquiv (M : SheafOfModules.{u} R) :
    (SheafOfModules.unit R ⟶ M) ≃ M.val.obj (op ⊤) :=
  M.unitHomEquiv.trans (sectionsTopEquiv R M)

lemma globalHomEquiv_comp {M N : SheafOfModules.{u} R}
    (f : SheafOfModules.unit R ⟶ M) (g : M ⟶ N) :
    globalHomEquiv R N (f ≫ g) = g.val.app (op ⊤) (globalHomEquiv R M f) := rfl

theorem globalHom_surjective {S : ShortComplex (SheafOfModules.{u} R)}
    (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₁)] :
    Function.Surjective (fun f : SheafOfModules.unit R ⟶ S.X₂ => f ≫ S.g) := by
  have h := ModuleSheafExact.shortExact_map R hS
  let : TopCat.Sheaf.IsFlasque ((S.map (SheafOfModules.toSheaf R)).X₁) :=
    ‹TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₁)›
  have he := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := ⊤) h
  have hs := (AddCommGrpCat.epi_iff_surjective
    (((SheafOfModules.toSheaf R).map S.g).hom.app (op ⊤))).mp he
  intro f
  obtain ⟨t, ht⟩ := hs (globalHomEquiv R S.X₃ f)
  let t' : S.X₂.val.obj (op ⊤) := t
  have ht' : S.g.val.app (op ⊤) t' = globalHomEquiv R S.X₃ f := ht
  refine ⟨(globalHomEquiv R S.X₂).symm t', ?_⟩
  apply (globalHomEquiv R S.X₃).injective
  rw [globalHomEquiv_comp, Equiv.apply_symm_apply]
  exact ht'

instance moduleSheafHasExt : HasExt.{u+1} (SheafOfModules.{u} R) :=
  HasExt.standard _

theorem flasque_ext_zero (n : ℕ) (M : SheafOfModules.{u} R)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M)]
    (x : Ext.{u+1} (SheafOfModules.unit R) M (n+1)) : x = 0 := by
  induction n generalizing M with
  | zero =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (SheafOfModules.unit R) hS x
      (Ext.eq_zero_of_injective _) rfl
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
    obtain ⟨g, rfl⟩ := globalHom_surjective R hS f
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      hS.comp_extClass, Ext.comp_zero] at hy
    exact hy.symm
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let : TopCat.Sheaf.IsFlasque ((S.map (SheafOfModules.toSheaf R)).X₁) :=
      ‹TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M)›
    let : TopCat.Sheaf.IsFlasque ((S.map (SheafOfModules.toSheaf R)).X₂) :=
      ModuleFlasque.injective_isFlasque R (Injective.under M)
    have : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₃) :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
        (ModuleSheafExact.shortExact_map R hS)
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (SheafOfModules.unit R) hS x
      (Ext.eq_zero_of_injective _) rfl
    rw [ih S.X₃ y, Ext.zero_comp] at hy
    exact hy.symm

end
end MaximalSeshadri.FlasqueCohomology

namespace MaximalSeshadri.AffineCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Abelian
open FlasqueCohomology
universe u
variable {R : CommRingCat.{u}}

def structureSheafUnit (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

def schemeGlobalHomEquiv (X : Scheme.{u}) (M : X.Modules) :
    (structureSheafUnit X ⟶ M) ≃ (Scheme.Modules.presheaf M).obj (op ⊤) :=
  globalHomEquiv X.ringCatSheaf M

lemma globalHom_tilde_surjective {M N : ModuleCat.{u} R} (g : M ⟶ N) [Epi g] :
    Function.Surjective (fun f : structureSheafUnit (Spec R) ⟶ tilde M =>
      f ≫ tilde.map g) := by
  intro f
  obtain ⟨q,hq⟩ := (ConcreteCategory.bijective_of_isIso (tilde.toOpen N ⊤)).surjective
    (schemeGlobalHomEquiv (Spec R) (tilde N) f)
  obtain ⟨p,hp⟩ := (ModuleCat.epi_iff_surjective g).mp inferInstance q
  let lifted : (Scheme.Modules.presheaf (tilde M)).obj (op ⊤) := tilde.toOpen M ⊤ p
  refine ⟨(schemeGlobalHomEquiv (Spec R) (tilde M)).symm lifted, ?_⟩
  apply (schemeGlobalHomEquiv (Spec R) (tilde N)).injective
  change ((tilde.map g).app ⊤)
    ((schemeGlobalHomEquiv (Spec R) (tilde M))
      ((schemeGlobalHomEquiv (Spec R) (tilde M)).symm lifted)) = _
  rw [Equiv.apply_symm_apply]
  change ((modulesSpecToSheaf.map (tilde.map g)).hom.app (op ⊤)) (tilde.toOpen M ⊤ p) = _
  have h := CategoryTheory.congr_fun (tilde.toOpen_map_app g ⊤) p
  exact h.trans (by change tilde.toOpen N ⊤ (g p) = _; rw [hp, hq])

local instance affineHasExt : HasExt.{u+1} (Spec R).Modules := HasExt.standard _

end
end MaximalSeshadri.AffineCohomology

namespace MaximalSeshadri.RestrictionExact
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

instance restriction_additive : (Scheme.Modules.restrictFunctor f).Additive where
  map_add := by intros; ext; rfl

instance restriction_flasque (M : Y.Modules)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M)] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj (M.restrict f)) where
  epi {U V} i := by
    change Epi (((SheafOfModules.toSheaf Y.ringCatSheaf).obj M).obj.map
      (f.opensFunctor.map i.unop).op)
    exact TopCat.Presheaf.IsFlasque.epi _

end
end MaximalSeshadri.RestrictionExact

namespace MaximalSeshadri.AffineSchemeCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open Scheme.Modules
universe u

def restrictionEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (restrictFunctor e.hom) (restrictFunctor e.inv)
    ((restrictFunctorId (X := Y)).symm ≪≫ (restrictFunctorCongr e.inv_hom_id).symm ≪≫
      restrictFunctorComp e.inv e.hom)
    ((restrictFunctorComp e.hom e.inv).symm ≪≫ restrictFunctorCongr e.hom_inv_id ≪≫
      restrictFunctorId (X := X))

local instance hasExtScheme (X : Scheme.{u}) : HasExt.{u+1} X.Modules := HasExt.standard _

end
end MaximalSeshadri.AffineSchemeCohomology


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_ReesCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial HomogeneousLocalization
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)
variable {B : Type v} [CommRing B] (f : R →+* B)

lemma coeff_power_dvd (hI : I.map f ≤ Ideal.span {f a.val})
    (n : ℕ) {r : R} (hr : r ∈ I ^ n) : (f a.val) ^ n ∣ f r := by
  have hm : f r ∈ (I.map f) ^ n := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f hr
  have hm' := pow_le_pow_left' hI n hm
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm'
  exact hm'

lemma localizationMap_injective (hfa : IsRegular (f a.val)) :
    Function.Injective (algebraMap B (Localization.Away (f a.val))) :=
  IsLocalization.injective _ (Submonoid.powers_le.mpr
    (isRegular_iff_mem_nonZeroDivisors.mp hfa))

end

end MaximalSeshadri.ReesGrading


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_PrincipalCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.ProjBase
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

lemma basicOpenToSpec_eq (f : A) :
    Scheme.forgetToLocallyRingedSpace.map (Proj.basicOpenToSpec 𝒜 f) =
      ProjectiveSpectrum.Proj.toSpec 𝒜 f := by
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

lemma basicOpenToSpec_mem (f : A) (x : Proj.basicOpen 𝒜 f)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    HomogeneousLocalization.mk z ∈ ((Proj.basicOpenToSpec 𝒜 f) x).asIdeal ↔
      z.num.val ∈ x.val.asHomogeneousIdeal := by
  have he := congr($(basicOpenToSpec_eq 𝒜 f).base x)
  change (Proj.basicOpenToSpec 𝒜 f) x = (ProjectiveSpectrum.Proj.toSpec 𝒜 f).base x at he
  rw [he]
  exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 x z

lemma toSpecZero_mem (x : Proj 𝒜) (a : 𝒜 0) :
    a ∈ ((Proj.toSpecZero 𝒜) x).asIdeal ↔ a.val ∈ x.asHomogeneousIdeal := by
  simp only [Proj.toSpecZero, Scheme.Hom.comp_apply, Spec.map_apply]
  change HomogeneousLocalization.fromZeroRingHom 𝒜 (.powers (1 : A)) a ∈
    ((Proj.basicOpenToSpec 𝒜 1) _).asIdeal ↔ _
  refine (basicOpenToSpec_mem 𝒜 (1 : A) _ ⟨0, a, 1, one_mem _⟩).trans ?_
  change a.val ∈ ((Proj.basicOpen 𝒜 (1 : A)).ι
    (((Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv ((Proj 𝒜).topIso.inv x))).asHomogeneousIdeal ↔ _
  rw [← Scheme.Hom.comp_apply, Scheme.isoOfEq_inv_ι, ← Scheme.Hom.comp_apply]
  rw [Scheme.toIso_inv_ι]; rfl

end
end MaximalSeshadri.ProjBase


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_Uniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.SpecMaps
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}

lemma isUnit_of_basicOpen_eq_top (a : Γ(X, ⊤)) (h : X.basicOpen a = ⊤) : IsUnit a := by
  apply RingedSpace.isUnit_of_isUnit_germ X.toLocallyRingedSpace.toRingedSpace ⊤ a
  intro x hx
  apply (Scheme.mem_basicOpen X a x hx).mp
  rw [h]
  trivial

end
end MaximalSeshadri.SpecMaps

namespace MaximalSeshadri.SchematicExt
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
variable {W X Y Z : Scheme.{u}}

lemma ext_of_ker_eq_bot_of_isSeparated {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) (hι : ι.ker = ⊥) (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  let l : U' ⟶ equalizer f' g' := equalizer.lift ι' (by ext1; exact hU)
  have hl : l.left ≫ (equalizer.ι f' g').left = ι := by
    change (l ≫ equalizer.ι f' g').left = ι
    exact congrArg (fun k : U' ⟶ X' => k.left) (equalizer.lift_ι ι' _)
  have hk : (equalizer.ι f' g').left.ker = ⊥ := by
    apply bot_unique
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := l.left.le_ker_comp _
         _ = ⊥ := by rw [hl, hι]
  have : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

lemma basicOpen_ker_eq_bot [IsAffine X] (r : Γ(X, ⊤)) (hr : IsRegular r) :
    (X.basicOpen r).ι.ker = ⊥ := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  apply bot_unique
  apply ((X.basicOpen r).ι.ideal_ker_le ⟨⊤, isAffineOpen_top X⟩).trans
  apply le_of_eq
  rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  have hinj : Function.Injective (algebraMap Γ(X, ⊤) Γ(X.basicOpen r, ⊤)) :=
    IsLocalization.injective (Γ(X.basicOpen r, ⊤))
      (Submonoid.powers_le.mpr (isRegular_iff_mem_nonZeroDivisors.mp hr))
  apply hinj
  change (algebraMap Γ(X, ⊤) Γ(X.basicOpen r, ⊤)) x = 0 at hx
  simpa only [map_zero] using hx

end
end MaximalSeshadri.SchematicExt


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_Frames
attribute [-instance] _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y Z : Scheme.{u}}
def O (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

def endValue (f : O X ⟶ O X) : Γ(X, ⊤) := f.app ⊤ (1 : Γ(X, ⊤))

@[simp] lemma endValue_id : endValue (𝟙 (O X)) = 1 := rfl

def coefficient {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) : Γ(X, ⊤) :=
  endValue (s ≫ e.hom)

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}}

def scalarEnd (r : Γ(X, ⊤)) : O X ⟶ O X where
  val.app U := by
    let S := X.ringCatSheaf.obj.obj U
    letI : CommRing S := inferInstanceAs (CommRing Γ(X, U.unop))
    exact ModuleCat.ofHom (LinearMap.mulLeft S
      ((X.presheaf.map (homOfLE le_top).op) r))
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change Γ(X, U.unop) at a
    change (X.presheaf.map (homOfLE le_top).op r) * (X.presheaf.map i a) =
      X.presheaf.map i (X.presheaf.map (homOfLE le_top).op r * a)
    rw [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

@[simp] lemma endValue_scalarEnd (r : Γ(X, ⊤)) : endValue (scalarEnd r) = r := by
  change X.presheaf.map (𝟙 _) r * 1 = r
  simp

end
end MaximalSeshadri.Frames

end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorFrames
attribute [-instance] _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

@[simp] lemma coefficient_scalarEnd {M : X.Modules} (e : M ≅ O X) (a : Γ(X, ⊤)) :
    coefficient e (scalarEnd a ≫ e.inv) = a := by
  simp only [coefficient, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    endValue_scalarEnd]

end
end MaximalSeshadri.Frames


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_Sections
attribute [-instance] _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped AlgebraicGeometry
variable {X : Scheme}

def moduleSectionsTopEquiv {T : TopCat} (R : Sheaf (Opens.grothendieckTopology T) RingCat)
    (M : SheafOfModules R) : M.sections ≃ M.val.obj (op ⊤) where
  toFun s := s.val (op ⊤)
  invFun t := PresheafOfModules.sectionsMk
    (fun U => M.val.map (homOfLE le_top).op t)
    (by
      intro U V i
      rw [← M.val.map_comp_apply]
      exact M.val.congr_map_apply (Subsingleton.elim _ _) t)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE le_top).op
  right_inv t := by
    change M.val.map (𝟙 (op ⊤)) t = t
    rw [M.val.map_id]
    rfl

def moduleSectionEquiv (M : X.Modules) : (O X ⟶ M) ≃ Γ(M, ⊤) :=
  M.unitHomEquiv.trans (moduleSectionsTopEquiv X.ringCatSheaf M)

@[simp] lemma moduleSectionEquiv_apply (M : X.Modules) (s : O X ⟶ M) :
    moduleSectionEquiv M s = s.app ⊤ (1 : Γ(X, ⊤)) := rfl

end
end MaximalSeshadri.Frames


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_Gluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.BlowupGluing
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MaximalSeshadri.Geometry

variable {X : Scheme.{0}} (I : X.IdealSheafData)

abbrev baseCover (_I : X.IdealSheafData) : X.OpenCover := Scheme.AffineZariskiSite.directedCover X

local instance localAffine (U : X.AffineZariskiSite) : IsAffine U.toOpens.toScheme := U.2

abbrev localCentre (U : X.AffineZariskiSite) : U.toOpens.toScheme.IdealSheafData := I.comap U.toOpens.ι

lemma centre_transition {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    (localCentre I V).comap ((baseCover I).trans h) = localCentre I U := by
  rw [localCentre, ← Scheme.IdealSheafData.comap_comp]
  change I.comap ((baseCover I).trans h ≫ (baseCover I).f V) = _
  rw [Scheme.Cover.trans_map]

end

end MaximalSeshadri.BlowupGluing


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_PolynomialJets
attribute [-instance] _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial

variable {σ R : Type*} [CommRing R]

abbrev JetIndex (σ : Type*) (n : ℕ) := {d : σ →₀ ℕ // d.degree < n}

instance jetIndexFinite [Finite σ] (n : ℕ) : Finite (JetIndex σ n) :=
  (Finsupp.finite_of_degree_lt n).to_subtype

def polynomialJetCoeffs (n : ℕ) : MvPolynomial σ R →ₗ[R] (JetIndex σ n → R) where
  toFun polynomial index := polynomial.coeff index.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

lemma polynomialJetCoeffs_ker (n : ℕ) :
    (polynomialJetCoeffs (σ := σ) (R := R) n).ker =
      ((idealOfVars σ R) ^ n).restrictScalars R := by
  ext p
  rw [LinearMap.mem_ker, funext_iff]
  change (∀ index : JetIndex σ n, p.coeff index.val = 0) ↔ _
  rw [Submodule.restrictScalars_mem, mem_pow_idealOfVars_iff']
  exact ⟨fun h d hd => h ⟨d, hd⟩, fun h d => h d.val d.property⟩

def polynomialTranslate (x : σ → R) : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (aeval (fun i => X i + C (x i)))
    (aeval (fun i => X i - C (x i)))
    (by ext i; simp)
    (by ext i; simp)

lemma polynomialTranslate_constantCoeff (x : σ → R) (p : MvPolynomial σ R) :
    constantCoeff (polynomialTranslate x p) = eval x p := by
  have h : (constantCoeff : MvPolynomial σ R →+* R).comp
      (polynomialTranslate x).toRingHom = eval x := by
    apply ringHom_ext
    · intro c; simp [polynomialTranslate]
    · intro i; simp [polynomialTranslate]
  exact RingHom.congr_fun h p

lemma idealOfVars_eq_ker_constantCoeff :
    idealOfVars σ R = RingHom.ker (constantCoeff : MvPolynomial σ R →+* R) := by
  ext p
  rw [← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff']
  change (∀ index, index.degree < 1 → p.coeff index = 0) ↔ p.coeff 0 = 0
  constructor
  · exact fun h => h 0 (by simp)
  · intro h d hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    simpa [hd0] using h

theorem mem_rationalPoint_pow_iff (x : σ → R) (n : ℕ) (p : MvPolynomial σ R) :
    p ∈ (RingHom.ker (eval x)) ^ n ↔
      ∀ index : σ →₀ ℕ, index.degree < n → (polynomialTranslate x p).coeff index = 0 := by
  have heq : RingHom.ker (eval x) =
      (idealOfVars σ R).map (polynomialTranslate x).symm.toRingHom := by
    simp only [RingEquiv.toRingHom_eq_coe]
    rw [Ideal.map_comap_of_equiv ((polynomialTranslate x).symm.toRingEquiv)]
    ext f
    change eval x f = 0 ↔ polynomialTranslate x f ∈ idealOfVars σ R
    rw [idealOfVars_eq_ker_constantCoeff]
    change eval x f = 0 ↔ constantCoeff (polynomialTranslate x f) = 0
    rw [polynomialTranslate_constantCoeff]
  rw [heq, ← Ideal.map_pow]
  simp only [RingEquiv.toRingHom_eq_coe]
  rw [Ideal.map_comap_of_equiv ((polynomialTranslate x).symm.toRingEquiv)]
  change polynomialTranslate x p ∈ (idealOfVars σ R) ^ n ↔ _
  exact mem_pow_idealOfVars_iff' n _

end

noncomputable section
open MvPolynomial
variable {σ R : Type*} [CommRing R]

def polynomialJetCoeffsAt (x : σ → R) (n : ℕ) :
    MvPolynomial σ R →ₗ[R] (JetIndex σ n → R) :=
  (polynomialJetCoeffs n).comp (polynomialTranslate x).toLinearMap

lemma polynomialJetCoeffsAt_ker (x : σ → R) (n : ℕ) :
    (polynomialJetCoeffsAt x n).ker =
      ((RingHom.ker (eval x)) ^ n).restrictScalars R := by
  ext p
  rw [LinearMap.mem_ker, funext_iff]
  change (∀ index : JetIndex σ n, (polynomialTranslate x p).coeff index.val = 0) ↔ _
  rw [Submodule.restrictScalars_mem, mem_rationalPoint_pow_iff]
  exact ⟨fun h d hd => h ⟨d, hd⟩, fun h d => h d.val d.property⟩

end

noncomputable section
open MvPolynomial

variable {σ R : Type*} [CommRing R]

abbrev JetAlgebra (σ R : Type*) [CommRing R] (n : ℕ) :=
  MvPolynomial σ R ⧸ (idealOfVars σ R) ^ n

end

noncomputable section
open MvPolynomial

variable {σ F R S : Type*} [CommRing F] [CommRing R] [CommRing S]
  [Algebra F R] [Algebra F S]

lemma map_idealOfVars (φ : R →ₐ[F] S) :
    (idealOfVars σ R).map (MvPolynomial.map φ.toRingHom) = idealOfVars σ S := by
  rw [idealOfVars, Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (MvPolynomial.map_X φ.toRingHom i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨X i, ⟨i, rfl⟩, MvPolynomial.map_X φ.toRingHom i⟩

end
end MaximalSeshadri.AlgebraicJets


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_PolynomialCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MvPolynomial HomogeneousLocalization
attribute [local instance] Classical.propDecidable

variable {R σ : Type*} [CommRing R] (i : σ)
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev PolyGrade (R σ : Type*) [CommRing R] := MvPolynomial.homogeneousSubmodule σ R
lemma poly_X_mem : X (R := R) i ∈ PolyGrade R σ 1 := isHomogeneous_X R i

abbrev PolyChart := HomogeneousLocalization.Away (PolyGrade R σ) (X i)
abbrev ChartVariables := {j : σ // j ≠ i}

def chartConstants : R →+* PolyChart (R := R) i :=
  (HomogeneousLocalization.fromZeroRingHom _ _).comp
    { toFun := fun r => ⟨C r, isHomogeneous_C _ _⟩
      map_one' := Subtype.ext C_1
      map_mul' := fun _ _ => Subtype.ext C_mul
      map_zero' := Subtype.ext C_0
      map_add' := fun _ _ => Subtype.ext C_add }

def chartCoordinate (j : σ) : PolyChart (R := R) i :=
  Away.mk _ (poly_X_mem (R := R) i) 1 (X j) (by simpa using poly_X_mem (R := R) j)

def dehomogenize : MvPolynomial σ R →+* MvPolynomial (ChartVariables i) R :=
  eval₂Hom C (fun j => if h : j = i then 1 else X ⟨j, h⟩)

@[simp] lemma dehomogenize_X_self : dehomogenize (R := R) i (X i) = 1 := by
  classical
  simp [dehomogenize]

def chartToPoly : PolyChart (R := R) i →+* MvPolynomial (ChartVariables i) R :=
  (Localization.awayLift (dehomogenize i) (X i) (by simp)).comp (algebraMap _ _)

@[simp] lemma chartToPoly_mk (n : ℕ) (p : MvPolynomial σ R)
    (hp : p ∈ PolyGrade R σ (n • 1)) :
    chartToPoly i (Away.mk _ (poly_X_mem (R := R) i) n p hp) = dehomogenize i p := by
  have h := Localization.awayLift_mk (dehomogenize (R := R) i) (X i) p 1
    (by simp) n
  simpa only [chartToPoly, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk, one_pow, mul_one] using h

@[simp] lemma chartToPoly_constants (r : R) :
    chartToPoly i (chartConstants i r) = C r := by
  exact (chartToPoly_mk i 0 (C r) (by simp)).trans
    (by simp [dehomogenize])

@[simp] lemma chartToPoly_coordinate (j : σ) :
    chartToPoly (R := R) i (chartCoordinate i j) =
      if h : j = i then 1 else X ⟨j, h⟩ := by
  rw [chartCoordinate, chartToPoly_mk]
  simp [dehomogenize]

end

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R σ : Type*} [CommRing R] [Fintype σ]

def linearEquation (t : σ → R) : MvPolynomial σ R := ∑ i, C (t i) * X i

end

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {R σ : Type u} [CommRing R] [Fintype σ]

omit [Fintype σ] in
                                                     
def projectiveConstants : R →+* PolyGrade R σ 0 :=
  { toFun := fun r => ⟨C r, isHomogeneous_C _ _⟩
    map_one' := Subtype.ext C_1
    map_mul' := fun _ _ => Subtype.ext C_mul
    map_zero' := Subtype.ext C_0
    map_add' := fun _ _ => Subtype.ext C_add }

omit [Fintype σ] in
def projectiveToSpec : Proj (PolyGrade R σ) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom projectiveConstants)

omit [Fintype σ] in
@[reassoc]
lemma chart_toSpec (i : σ) :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ≫ projectiveToSpec =
      Spec.map (CommRingCat.ofHom (chartConstants i)) := by
  rw [projectiveToSpec, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open AlgebraicGeometry TopologicalSpace CategoryTheory
open MaximalSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

def projectiveHyperplane {K : Type} [Field K] {n : ℕ} {X : Scheme}
    (h : X ⟶ Proj (PolyGrade K (Option (Fin n)))) (t : Option (Fin n) → K) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (h ⁻¹ᵁ Proj.basicOpen (PolyGrade K (Option (Fin n))) (linearEquation t)).compl

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.ProjectiveGeometry
noncomputable section
open AlgebraicGeometry
universe u v
variable {A : Type u} {σ : Type v} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

instance homogeneous_isReduced (S : Submonoid A) [_root_.IsReduced A] :
    _root_.IsReduced (HomogeneousLocalization 𝒜 S) :=
  isReduced_of_injective (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S))
    (HomogeneousLocalization.val_injective S)

instance proj_isReduced [_root_.IsReduced A] : IsReduced (Proj 𝒜) := by
  have (x : Proj 𝒜) : _root_.IsReduced ((Proj 𝒜).presheaf.stalk x) :=
    isReduced_of_injective (Proj.stalkIso' 𝒜 x) (Proj.stalkIso' 𝒜 x).injective
  exact isReduced_of_isReduced_stalk _

end
end MaximalSeshadri.ProjectiveGeometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_FiniteCenters
attribute [-instance] _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.FinitePointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme.{0}}

variable {α : Type} [Fintype α]
variable (p : α → (Spec (.of K) ⟶ X))

def pointCentre : X.IdealSheafData := ∏ i, (p i).ker

def pointOpen (i : α) : X.Opens :=
  (⨆ j : {j : α // j ≠ i}, (p j).ker.support).compl

def outsideOpen : X.Opens := (pointCentre p).support.compl

lemma mem_finite_iSup_closed {β : Type} [Finite β] (C : β → Closeds X) (x : X) :
    x ∈ (⨆ i, C i) ↔ ∃ i, x ∈ C i := by
  let D : Closeds X := ⟨⋃ i, (C i : Set X), isClosed_iUnion_of_finite fun i => (C i).isClosed⟩
  have he : (⨆ i, C i) = D := by
    apply le_antisymm
    · exact iSup_le (fun i y hy => Set.mem_iUnion.mpr ⟨i, hy⟩)
    · intro y hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      exact (le_iSup C i) hi
  rw [he]
  exact Set.mem_iUnion

lemma mem_centre_support (x : X) :
    x ∈ (pointCentre p).support ↔ ∃ i, x ∈ (p i).ker.support := by
  classical
  suffices h : ∀ s : Finset α, x ∈ (∏ i ∈ s, (p i).ker).support ↔
      ∃ i ∈ s, x ∈ (p i).ker.support by
    simpa only [Finset.mem_univ, true_and, pointCentre] using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    change False ↔ ∃ i ∈ (∅ : Finset α), x ∈ (p i).ker.support
    simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.IdealSheafData.support_mul]
    change (x ∈ (p a).ker.support ∨ x ∈ (∏ i ∈ s, (p i).ker).support) ↔ _
    rw [ih]
    constructor
    · rintro (h | ⟨i, hi, hx⟩)
      · exact ⟨a, Finset.mem_insert_self .., h⟩
      · exact ⟨i, Finset.mem_insert_of_mem hi, hx⟩
    · rintro ⟨i, hi, hx⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Or.inl hx
      · exact Or.inr ⟨i, hi, hx⟩

end
end MaximalSeshadri.FinitePointBlowup

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_ClosedPushforwardExact
attribute [-instance] _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section

namespace MaximalSeshadri.ClosedPushforward
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

lemma sections_empty (M : X.Modules) (U : X.Opens) (hU : U = ⊥) :
    Subsingleton (M.val.obj (op U)) := by
  exact AddCommGrpCat.subsingleton_of_isZero
    (TopCat.Sheaf.isTerminalOfEqEmpty ((SheafOfModules.toSheaf.{0} X.ringCatSheaf).obj M) hU).isZero

lemma map_epi (f : X ⟶ Y) [IsClosedImmersion f] {M N : X.Modules}
    (φ : M ⟶ N) [Epi φ] : Epi ((Scheme.Modules.pushforward f).map φ) := by
  let FX := SheafOfModules.toSheaf.{0} X.ringCatSheaf
  let FY := SheafOfModules.toSheaf.{0} Y.ringCatSheaf
  let S := ShortComplex.mk _ _ (kernel.condition φ)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel φ }
  have hEpi : Epi (FX.map φ) := (ModuleSheafExact.shortExact_map X.ringCatSheaf hS).epi_g
  have hφ : TopCat.Presheaf.IsLocallySurjective (FX.map φ).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mpr hEpi
  have hloc : TopCat.Presheaf.IsLocallySurjective
      (FY.map ((Scheme.Modules.pushforward f).map φ)).hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro U t y hy
    by_cases him : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := him
      obtain ⟨W,hWU,⟨s,hs⟩,hxW⟩ :=
        (TopCat.Presheaf.isLocallySurjective_iff _).mp hφ (f ⁻¹ᵁ U) t x hy
      obtain ⟨V',hV',hpre⟩ := f.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp W.isOpen
      let V : Y.Opens := ⟨V', hV'⟩ ⊓ U
      have hV : f ⁻¹ᵁ V = W := by
        ext z
        change (f z ∈ V' ∧ f z ∈ U) ↔ z ∈ W
        have hh : f z ∈ V' ↔ z ∈ W := Set.ext_iff.mp hpre z
        exact ⟨fun h => hh.mp h.1, fun h => ⟨hh.mpr h,hWU h⟩⟩
      refine ⟨V,inf_le_right,?_,?_,⟩
      · change ∃ s, (φ.val.app (op (f ⁻¹ᵁ V))) s =
          N.val.map ((Opens.map f.base).map (homOfLE inf_le_right)).op t
        subst W
        exact ⟨s,hs⟩
      · exact ⟨(Set.ext_iff.mp hpre x).mpr hxW,hy⟩
    · let V : Y.Opens := U ⊓ ⟨(Set.range f)ᶜ, f.isClosedEmbedding.isClosed_range.isOpen_compl⟩
      have hV : f ⁻¹ᵁ V = ⊥ := by
        ext x
        change (f x ∈ U ∧ f x ∉ Set.range f) ↔ False
        simp
      refine ⟨V,inf_le_left,⟨0,?_⟩,⟨hy,him⟩⟩
      exact @Subsingleton.elim (N.val.obj (op (f ⁻¹ᵁ V))) (sections_empty N _ hV) _ _
  let : Epi (FY.map ((Scheme.Modules.pushforward f).map φ)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hloc
  exact FY.epi_of_epi_map inferInstance

instance preservesEpis (f : X ⟶ Y) [IsClosedImmersion f] :
    (Scheme.Modules.pushforward f).PreservesEpimorphisms where
  preserves φ _ := map_epi f φ

instance preservesHomology (f : X ⟶ Y) [IsClosedImmersion f] :
    (Scheme.Modules.pushforward f).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

instance preservesFiniteColimits (f : X ⟶ Y) [IsClosedImmersion f] :
    PreservesFiniteColimits (Scheme.Modules.pushforward f) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end
end MaximalSeshadri.ClosedPushforward

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ClosedPushforwardCohomology
attribute [-instance] _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                     
section

namespace MaximalSeshadri.ClosedPushforward
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.FlasqueCohomology MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
local instance instHasExtModules_solutions_r84e5cc_1 : HasExt.{1} X.Modules := schemeHasExt
local instance instHasExtModules_solutions_1 : HasExt.{1} Y.Modules := schemeHasExt
local instance instEnoughInjectivesModules_solutions : EnoughInjectives X.Modules := ModuleGrothendieck.enoughInjectives X.ringCatSheaf

omit [IsClosedImmersion f] in
lemma pushforward_flasque (M : X.Modules)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf.{0} X.ringCatSheaf).obj M)] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf.{0} Y.ringCatSheaf).obj ((Scheme.Modules.pushforward f).obj M)) := by
  exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque
    ((SheafOfModules.toSheaf.{0} X.ringCatSheaf).obj M) f.base

end
end MaximalSeshadri.ClosedPushforward

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ExtCokernel
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                     
section

namespace MaximalSeshadri.ExtCokernel
noncomputable section
open CategoryTheory CategoryTheory.Abelian
universe w v u t
variable {K : Type t} [CommRing K] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear K C] [HasExt.{w} C] {S : ShortComplex C}

def quotientEquiv (hS : S.ShortExact) (M : C)
    (hvan : ∀ x : Ext S.X₂ M 1, x = 0) :
    ((S.X₁ ⟶ M) ⧸ (LinearMap.range
      (Linear.leftComp K M S.f))) ≃ₗ[K] Ext S.X₃ M 1 := by
  let d : (S.X₁ ⟶ M) →ₗ[K] Ext S.X₃ M 1 :=
    (hS.extClass.precompOfLinear K M (add_zero 1)).comp Ext.linearEquiv₀.symm.toLinearMap
  have hd : Function.Surjective d := by
    intro x
    obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ hS M x (hvan _) (n₀ := 0) rfl
    refine ⟨Ext.linearEquiv₀ (R := K) y, ?_⟩
    change hS.extClass.comp (Ext.mk₀ (Ext.linearEquiv₀ (R := K) y)) (add_zero 1) = x
    rwa [Ext.mk₀_linearEquiv₀_apply]
  have hk : LinearMap.range (Linear.leftComp K M S.f) = d.ker := by
    ext f
    constructor
    · rintro ⟨g,rfl⟩
      change hS.extClass.comp (Ext.mk₀ (S.f ≫ g)) (add_zero 1) = 0
      rw [← Ext.mk₀_comp_mk₀]
      exact ShortComplex.ShortExact.extClass_comp_assoc hS _
    · intro hf
      change hS.extClass.comp (Ext.mk₀ f) (add_zero 1) = 0 at hf
      obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₁ hS M (Ext.mk₀ f) rfl hf
      refine ⟨Ext.linearEquiv₀ (R := K) y, ?_⟩
      apply (Ext.linearEquiv₀ (R := K)).symm.injective
      change Ext.mk₀ (S.f ≫ Ext.linearEquiv₀ (R := K) y) = Ext.mk₀ f
      simpa only [← Ext.mk₀_comp_mk₀,
        Ext.mk₀_linearEquiv₀_apply] using hy
  exact (Submodule.quotEquivOfEq _ _ hk).trans (d.quotKerEquivOfSurjective hd)

end
end MaximalSeshadri.ExtCokernel
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_RestrictionComparison
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.ExtSectionComparison
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe w w' v v' u u'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasExt.{w} C] [HasExt.{w'} D] {A : C} {B : D} (e : B ⟶ F.obj A)

def mapFrom (Y : C) (n : ℕ) : Ext.{w} A Y n →+ Ext.{w'} B (F.obj Y) n :=
  ((Ext.mk₀ e).precomp (F.obj Y) (zero_add n)).comp (F.mapExtAddHom A Y n)

lemma mapFrom_apply (Y : C) (n : ℕ) (x : Ext.{w} A Y n) :
    mapFrom F e Y n x = (Ext.mk₀ e).comp (x.mapExactFunctor F) (zero_add n) := rfl

@[simp] lemma mapFrom_mk₀ {Y : C} (f : A ⟶ Y) :
    mapFrom F e Y 0 (Ext.mk₀ f) = Ext.mk₀ (e ≫ F.map f) := by
  simp only [mapFrom_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

lemma mapFrom_comp {Y Z : C} {n m k : ℕ} (x : Ext.{w} A Y n)
    (y : Ext.{w} Y Z m) (h : n+m=k) :
    mapFrom F e Z k (x.comp y h) =
      (mapFrom F e Y n x).comp (y.mapExactFunctor F) h := by
  simp only [mapFrom_apply, Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add _) h (by omega)).symm

theorem mapFrom_bijective [EnoughInjectives C]
    (hhom : ∀ Y : C, Function.Bijective (fun f : A ⟶ Y => e ≫ F.map f))
    (hacyclic : ∀ (I : C) [Injective I] (n : ℕ)
      (x : Ext.{w'} B (F.obj I) (n+1)), x = 0)
    (Y : C) (n : ℕ) : Function.Bijective (mapFrom F e Y n) := by
  induction n generalizing Y with
  | zero =>
    constructor
    · intro x y h
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
      obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
      rw [mapFrom_mk₀, mapFrom_mk₀] at h
      exact congrArg Ext.mk₀ ((hhom Y).injective ((Ext.mk₀_bijective _ _).injective h))
    · intro x
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
      obtain ⟨g, rfl⟩ := (hhom Y).surjective f
      exact ⟨Ext.mk₀ g, mapFrom_mk₀ F e g⟩
  | succ n ih =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    let : Injective S.X₂ := I.injective
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (mapFrom F e S.X₂ n) (mapFrom F e S.X₃ n) (mapFrom F e S.X₁ (n+1))
      ?_ ?_
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A hS n (n+1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' B (hS.map F) n (n+1) rfl))
      (ih _).surjective (ih _)
      (fun x => Ext.covariant_sequence_exact₁ A hS x (Ext.eq_zero_of_injective _) rfl)
      (fun x => Ext.covariant_sequence_exact₁ B (hS.map F) x (hacyclic S.X₂ n _) rfl)
    · ext x
      symm
      change mapFrom F e _ _ (x.comp (Ext.mk₀ S.g) (add_zero n)) =
        (mapFrom F e _ _ x).comp (Ext.mk₀ (F.map S.g)) (add_zero n)
      rw [mapFrom_comp, Ext.mapExactFunctor_mk₀]
    · ext x
      symm
      change mapFrom F e _ _ (x.comp hS.extClass rfl) =
        (mapFrom F e _ _ x).comp (hS.map F).extClass rfl
      rw [mapFrom_comp, Ext.mapExactFunctor_extClass]
      rfl

end
end MaximalSeshadri.ExtSectionComparison

namespace MaximalSeshadri.RestrictionCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Abelian
open ModuleFlasque FlasqueCohomology
universe u
variable {X : Scheme.{u}} (U : X.Opens)

local instance hasExtScheme (Y : Scheme.{u}) : HasExt.{u+1} Y.Modules := HasExt.standard _

def restrictionSectionsIso (M : X.Modules) : Γ(M.restrict U.ι,⊤) ≅ Γ(M,U) :=
  M.restrictAppIso U.ι ⊤ ≪≫ M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

def restrictionHomEquiv (M : X.Modules) :
    (freeOpen X.ringCatSheaf U ⟶ M) ≃
      (SheafOfModules.unit U.toScheme.ringCatSheaf ⟶ M.restrict U.ι) :=
  (freeOpenEquiv X.ringCatSheaf M U).trans
    ((restrictionSectionsIso U M).addCommGroupIsoToAddEquiv.toEquiv.symm.trans
      (globalHomEquiv U.toScheme.ringCatSheaf (M.restrict U.ι)).symm)

lemma restrictionHomEquiv_comp {M N : X.Modules}
    (f : freeOpen X.ringCatSheaf U ⟶ M) (g : M ⟶ N) :
    restrictionHomEquiv U N (f ≫ g) =
      restrictionHomEquiv U M f ≫ (Scheme.Modules.restrictFunctor U.ι).map g := by
  apply (globalHomEquiv U.toScheme.ringCatSheaf (N.restrict U.ι)).injective
  change (globalHomEquiv U.toScheme.ringCatSheaf (N.restrict U.ι))
      ((globalHomEquiv U.toScheme.ringCatSheaf (N.restrict U.ι)).symm
        ((restrictionSectionsIso U N).inv
          (g.val.app (op U) (freeOpenEquiv X.ringCatSheaf M U f)))) =
    (globalHomEquiv U.toScheme.ringCatSheaf (N.restrict U.ι))
      ((globalHomEquiv U.toScheme.ringCatSheaf (M.restrict U.ι)).symm
          ((restrictionSectionsIso U M).inv (freeOpenEquiv X.ringCatSheaf M U f)) ≫
        ((Scheme.Modules.restrictFunctor U.ι).map g : SheafOfModules.Hom _ _))
  erw [Equiv.apply_symm_apply, globalHomEquiv_comp, Equiv.apply_symm_apply]
  change (restrictionSectionsIso U N).inv (g.val.app (op U)
    (freeOpenEquiv X.ringCatSheaf M U f)) =
    ((Scheme.Modules.restrictFunctor U.ι).map g).val.app (op ⊤)
      ((restrictionSectionsIso U M).inv (freeOpenEquiv X.ringCatSheaf M U f))
  exact (CategoryTheory.congr_fun (g.mapPresheaf.naturality
    (eqToHom U.ι_image_top).op) _).symm

def restrictionGenerator : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
    (Scheme.Modules.restrictFunctor U.ι).obj (freeOpen X.ringCatSheaf U) :=
  restrictionHomEquiv U _ (𝟙 _)

lemma restrictionGenerator_comp {M : X.Modules}
    (f : freeOpen X.ringCatSheaf U ⟶ M) :
    restrictionGenerator U ≫ (Scheme.Modules.restrictFunctor U.ι).map f =
      restrictionHomEquiv U M f := by
  exact (restrictionHomEquiv_comp U (𝟙 _) f).symm.trans
    (congrArg (restrictionHomEquiv U M) (Category.id_comp f))

end
end MaximalSeshadri.RestrictionCohomology


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_FiniteCover
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.FiniteCoverCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open ModuleFlasque
universe u
variable {X : Scheme.{u}} [IsNoetherian X]

local instance hasExtScheme (Y : Scheme.{u}) : HasExt.{u+1} Y.Modules := HasExt.standard _

def freeOpenModule (U : X.Opens) : X.Modules :=
  freeOpen (X := X.carrier) X.ringCatSheaf U

end
end MaximalSeshadri.FiniteCoverCohomology

namespace MaximalSeshadri.FiniteCoverCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open ModuleFlasque
universe u
variable {X : Scheme.{u}} [IsNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

local instance hasExtScheme' (Y : Scheme.{u}) : HasExt.{u+1} Y.Modules := HasExt.standard _

end
end MaximalSeshadri.FiniteCoverCohomology

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_GeneralQuadraticNumerics
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section
namespace MaximalSeshadri.EulerNumerics

def Quadratic (f : ℕ → ℤ) : Prop := ∀ n : ℕ,
  2*f n = (n : ℤ)*((n : ℤ)-1)*(f 2-2*f 1+f 0) +
    2*(n : ℤ)*(f 1-f 0)+2*f 0

end MaximalSeshadri.EulerNumerics

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_ConvergentSeries
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set
abbrev Exponent := ℕ × ℕ


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_EulerExact
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                    
section

namespace MaximalSeshadri.Cohomology
noncomputable section
open CategoryTheory CategoryTheory.Abelian

def alternatingTrunc (a : ℕ → ℤ) (d : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (d+1), (-1 : ℤ)^i * a i

universe w v u t
variable {K : Type t} [Field K] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear K C] [HasExt.{w} C]

def extEuler (E M : C) (d : ℕ) : ℤ :=
  alternatingTrunc (fun n => Module.finrank K (Ext E M n)) d

variable (E : C) {S : ShortComplex C} (hS : S.ShortExact)

def cohomologyMap₁ (n : ℕ) : Ext E S.X₁ n →ₗ[K] Ext E S.X₂ n :=
  (Ext.mk₀ S.f).postcompOfLinear K E (add_zero n)

def cohomologyMap₂ (n : ℕ) : Ext E S.X₂ n →ₗ[K] Ext E S.X₃ n :=
  (Ext.mk₀ S.g).postcompOfLinear K E (add_zero n)

def cohomologyBoundary (n : ℕ) : Ext E S.X₃ n →ₗ[K] Ext E S.X₁ (n+1) :=
  hS.extClass.postcompOfLinear K E rfl

end
end MaximalSeshadri.Cohomology

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open scoped AlgebraicGeometry
variable {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℂ))

@[instance_reducible]
def sheafComplexLinear : Linear ℂ X.Modules where
  homModule M N := Module.compHom _ (baseScalars f)
  smul_comp M N P r g h := by
    change ((baseScalars f r) • g) ≫ h = (baseScalars f r) • (g ≫ h)
    exact Linear.smul_comp _ _ _ _ _ _
  comp_smul M N P g r h := by
    change g ≫ ((baseScalars f r) • h) = (baseScalars f r) • (g ≫ h)
    exact Linear.comp_smul _ _ _ _ _ _

@[instance_reducible]
def complexExtModule (M : X.Modules) (n : ℕ) : Module ℂ (cohomology M n) :=
  letI := sheafComplexLinear f
  inferInstance

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_LocalSectionDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X Y : Scheme.{0}}

lemma baseScalars_comp_actual (f : Y ⟶ X) (g : X ⟶ Spec (CommRingCat.of ℂ)) :
    baseScalars (f ≫ g) = f.appTop.hom.comp (baseScalars g) := by
  ext c
  simp only [baseScalars, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_AnalyticNode
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.AnalyticNode
noncomputable section

open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def nodeLinear (a b d : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  ((2*a) • ContinuousLinearMap.fst ℂ ℂ ℂ +
    (b+d) • ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    ((2*a) • ContinuousLinearMap.fst ℂ ℂ ℂ +
      (b-d) • ContinuousLinearMap.snd ℂ ℂ ℂ)

def shearLinear (t : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).prod
    (t • ContinuousLinearMap.fst ℂ ℂ ℂ + ContinuousLinearMap.snd ℂ ℂ ℂ)

end
end MaximalSeshadri.AnalyticNode

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_BinaryJetDimension
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped BigOperators

lemma binary_degree (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  rw [Finsupp.degree_eq_sum,Fin.sum_univ_two]

end
end MaximalSeshadri.AlgebraicJets

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_FormalEtale
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AlgebraicJets
noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

def quotientBaseMap (I : Ideal R) :
    R ⧸ I →ₐ[R] S ⧸ I.map (algebraMap R S) :=
  Ideal.quotientMapₐ _ (Algebra.ofId R S) Ideal.le_comap_map

@[simp] lemma quotientBaseMap_mk (I : Ideal R) (x : R) :
    quotientBaseMap (S := S) I (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S x) := rfl

end

noncomputable section
open IsLocalRing

variable {F R S : Type*} [Field F] [CommRing R] [CommRing S]
  [Algebra F R] [Algebra F S] [Algebra R S] [IsScalarTower F R S]

instance rationalKer_isMaximal (ρ : S →ₐ[F] F) : (RingHom.ker ρ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective ρ
    (fun c => ⟨algebraMap F S c, by simp⟩)

def rationalLocalMap (ρ : S →ₐ[F] F) :
    Localization.AtPrime (RingHom.ker ρ) →ₐ[F] F :=
  IsLocalization.liftAlgHom (f := ρ) fun u : (RingHom.ker ρ).primeCompl =>
    isUnit_iff_ne_zero.mpr (fun h => u.2 h)

end

end MaximalSeshadri.AlgebraicJets
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_JetOpenness
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped BigOperators
open Set

variable (K R : Type*) [Field K] [CommRing R] [Algebra K R]

def kernelPoint (p : R →ₐ[K] K) : PrimeSpectrum R :=
  ⟨RingHom.ker p, RingHom.ker_isPrime p⟩

@[instance_reducible] def rationalPointTopology : TopologicalSpace (R →ₐ[K] K) :=
  TopologicalSpace.induced (kernelPoint K R) inferInstance

end
end MaximalSeshadri.AlgebraicJets

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Nodal_NodalIntersection
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri
namespace NodalLocal

open PowerSeries

noncomputable section

variable (K : Type*) [Field K]

def multiples {A : Type*} [CommRing A] [Algebra K A] (f : A) : Submodule K A :=
  LinearMap.range (LinearMap.mulLeft K f)

@[simp] theorem mem_multiples {A : Type*} [CommRing A] [Algebra K A] (f g : A) :
    g ∈ multiples K f ↔ f ∣ g := by
  simp only [multiples, LinearMap.mem_range, LinearMap.mulLeft_apply, dvd_def]
  exact exists_congr (fun _ => eq_comm)

def nodeAlgebra : Subalgebra K (PowerSeries K × PowerSeries K) where
  carrier := {p | constantCoeff p.1 = constantCoeff p.2}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' {a b} (ha : constantCoeff a.1 = constantCoeff a.2)
      (hb : constantCoeff b.1 = constantCoeff b.2) := by
    change constantCoeff (a.1 + b.1) = constantCoeff (a.2 + b.2)
    simp only [map_add, ha, hb]
  mul_mem' {a b} (ha : constantCoeff a.1 = constantCoeff a.2)
      (hb : constantCoeff b.1 = constantCoeff b.2) := by
    change constantCoeff (a.1 * b.1) = constantCoeff (a.2 * b.2)
    simp only [map_mul, ha, hb]
  algebraMap_mem' := by intro a; rfl

abbrev Node := nodeAlgebra K

def branchX : Node K →ₐ[K] PowerSeries K where
  toFun := fun f => f.val.1
  map_zero' := rfl
  map_one' := rfl
  map_add' := by intros; rfl
  map_mul' := by intros; rfl
  commutes' := by intros; rfl

def branchZ : Node K →ₐ[K] PowerSeries K where
  toFun := fun f => f.val.2
  map_zero' := rfl
  map_one' := rfl
  map_add' := by intros; rfl
  map_mul' := by intros; rfl
  commutes' := by intros; rfl

@[ext] theorem node_ext {f g : Node K}
    (hx : branchX K f = branchX K g) (hz : branchZ K f = branchZ K g) : f = g :=
  Subtype.ext (Prod.ext hx hz)

def includeX : PowerSeries K →ₗ[K] Node K where
  toFun := fun f => ⟨(X * f, 0), by change constantCoeff (X * f) = constantCoeff 0; simp⟩
  map_add' := by intro f g; apply Subtype.ext; ext <;> simp [mul_add]
  map_smul' := by intro a f; apply Subtype.ext; ext <;> simp

@[simp] theorem branchX_includeX (f : PowerSeries K) :
    branchX K (includeX K f) = X * f := rfl
@[simp] theorem branchZ_includeX (f : PowerSeries K) :
    branchZ K (includeX K f) = 0 := rfl

def liftZ : PowerSeries K →ₗ[K] Node K where
  toFun := fun f => ⟨(C (constantCoeff f), f), by
    change constantCoeff (C (constantCoeff f)) = constantCoeff f
    simp⟩
  map_add' := by intro f g; apply Subtype.ext; ext <;> simp
  map_smul' := by
    intro a f
    apply Subtype.ext
    change (C (constantCoeff (a • f)), a • f) = (a • C (constantCoeff f), a • f)
    congr 1
    simp only [Algebra.smul_def, map_mul, PowerSeries.algebraMap_apply,
      constantCoeff_C]

@[simp] theorem branchX_liftZ (f : PowerSeries K) :
    branchX K (liftZ K f) = C (constantCoeff f) := rfl
@[simp] theorem branchZ_liftZ (f : PowerSeries K) :
    branchZ K (liftZ K f) = f := rfl

lemma includeX_mul (f : Node K) (g : PowerSeries K) :
    includeX K (branchX K f * g) = f * includeX K g := by
  apply node_ext <;> simp [mul_left_comm]

def coefficientJet (n : ℕ) : PowerSeries K →ₗ[K] (Fin n → K) :=
  LinearMap.pi (fun i => coeff i.val)

@[simp] lemma coefficientJet_apply (n : ℕ) (f : PowerSeries K) (i : Fin n) :
    coefficientJet K n f i = coeff i.val f := rfl

def quotientZ (f : Node K) :
    (Node K ⧸ multiples K f) →ₗ[K]
      (PowerSeries K ⧸ multiples K (branchZ K f)) :=
  (multiples K f).liftQ
    ((multiples K (branchZ K f)).mkQ.comp (branchZ K).toLinearMap) (by
      rintro y ⟨a, rfl⟩
      change (Submodule.Quotient.mk (branchZ K (f * a)) :
        PowerSeries K ⧸ multiples K (branchZ K f)) = 0
      simp only [map_mul, Submodule.Quotient.mk_eq_zero, mem_multiples]
      exact dvd_mul_right _ _)

@[simp] lemma quotientZ_mk (f g : Node K) :
    quotientZ K f (Submodule.Quotient.mk g) = Submodule.Quotient.mk (branchZ K g) := rfl

def quotientX (f : Node K) :
    (PowerSeries K ⧸ multiples K (branchX K f)) →ₗ[K]
      (Node K ⧸ multiples K f) :=
  (multiples K (branchX K f)).liftQ
    ((multiples K f).mkQ.comp (includeX K)) (by
      rintro y ⟨a, rfl⟩
      change (Submodule.Quotient.mk (includeX K (branchX K f * a)) :
        Node K ⧸ multiples K f) = 0
      rw [includeX_mul, Submodule.Quotient.mk_eq_zero, mem_multiples]
      exact dvd_mul_right _ _)

@[simp] lemma quotientX_mk (f : Node K) (g : PowerSeries K) :
    quotientX K f (Submodule.Quotient.mk g) = Submodule.Quotient.mk (includeX K g) := rfl

abbrev Bivariate := PowerSeries (PowerSeries K)

def constAlg : PowerSeries K →ₐ[K] K where
  toRingHom := constantCoeff
  commutes' := by intro a; simp

def restrictX : Bivariate K →ₐ[K] PowerSeries K where
  toRingHom := constantCoeff
  commutes' := by intro a; simp [PowerSeries.algebraMap_apply]

def restrictZ : Bivariate K →ₐ[K] PowerSeries K :=
  PowerSeries.mapAlgHom (constAlg K)

@[simp] lemma restrictX_apply (f : Bivariate K) : restrictX K f = constantCoeff f := rfl
@[simp] lemma restrictZ_apply (f : Bivariate K) :
    restrictZ K f = PowerSeries.map constantCoeff f := rfl

lemma restrict_constants (f : Bivariate K) :
    constantCoeff (restrictX K f) = constantCoeff (restrictZ K f) := by
  simp only [restrictX_apply, restrictZ_apply, ← coeff_zero_eq_constantCoeff_apply,
    coeff_map]

def toNode : Bivariate K →ₐ[K] Node K where
  toFun f := ⟨(restrictX K f, restrictZ K f), restrict_constants K f⟩
  map_zero' := by
    apply Subtype.ext
    exact Prod.ext (map_zero (restrictX K)) (map_zero (restrictZ K))
  map_one' := by
    apply Subtype.ext
    exact Prod.ext (map_one (restrictX K)) (map_one (restrictZ K))
  map_add' := by intro f g; apply node_ext <;> simp
  map_mul' := by intro f g; apply node_ext <;> simp
  commutes' := by
    intro a
    apply Subtype.ext
    exact Prod.ext ((restrictX K).commutes a) ((restrictZ K).commutes a)

@[simp] lemma branchX_toNode (f : Bivariate K) :
    branchX K (toNode K f) = restrictX K f := rfl
@[simp] lemma branchZ_toNode (f : Bivariate K) :
    branchZ K (toNode K f) = restrictZ K f := rfl

def nodeEquation : Bivariate K := C (X : PowerSeries K) * X

@[simp] lemma toNode_nodeEquation : toNode K (nodeEquation K) = 0 := by
  apply node_ext <;> simp [nodeEquation]

end

end NodalLocal
end MaximalSeshadri

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_ClosedPushforwardEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section

namespace MaximalSeshadri.ClosedPushforward
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.FlasqueCohomology MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y)
local instance instHasExtModules_solutions_2_r84e5cc_1 : HasExt.{1} X.Modules := schemeHasExt
local instance instHasExtModules_solutions_3 : HasExt.{1} Y.Modules := schemeHasExt

lemma scalar_naturality (p : Y ⟶ Spec (CommRingCat.of ℂ)) (U : Y.Opens) (r : ℂ) :
    restrictScalar X (f ⁻¹ᵁ U) (baseScalars (f ≫ p) r) =
      f.app U (restrictScalar Y U (baseScalars p r)) := by
  rw [baseScalars_comp_actual]
  change X.presheaf.map (homOfLE le_top).op (f.appTop (baseScalars p r)) = _
  exact (CategoryTheory.congr_fun (f.naturality (homOfLE le_top).op) (baseScalars p r)).symm

end
end MaximalSeshadri.ClosedPushforward

end

end OAI
end


