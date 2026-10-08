-- Prove2me | solution 1 for AffineJacobian.isEtaleAt_centered_projection
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-04T15:21:20.229482+00:00
-- url     : https://prove2.me/submissions/2c54f9fd-0911-4ff5-8cf2-e6633f3cc198

import Mathlib

section EtaleProjectionBundle0

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AffineJacobian.EtalePresentation

/-- A square polynomial presentation is étale wherever its Jacobian
determinant does not vanish. -/
theorem isEtaleAt_of_jacobian_not_mem
    {B C ι τ : Type*} [CommRing B] [CommRing C] [Algebra B C]
    [Finite ι] [Finite τ] (P : Algebra.PreSubmersivePresentation B C ι τ)
    (hdim : P.dimension = 0) (q : Ideal C) [q.IsPrime]
    (hq : P.jacobian ∉ q) : Algebra.IsEtaleAt B q := by
  let j := P.jacobian
  let D := Localization.Away j
  let Q := (Algebra.PreSubmersivePresentation.localizationAway D j).comp P
  have hunit : IsUnit Q.jacobian := by
    change IsUnit ((Algebra.PreSubmersivePresentation.localizationAway D j).comp P).jacobian
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.smul_def, Algebra.PreSubmersivePresentation.localizationAway_jacobian]
    exact (IsLocalization.Away.algebraMap_isUnit j).mul
      (IsLocalization.Away.algebraMap_isUnit j)
  let Q' : Algebra.SubmersivePresentation B D (Unit ⊕ ι) (Unit ⊕ τ) :=
    { Q with jacobian_isUnit := hunit }
  have hdim' : Q'.dimension = 0 := by
    change Q.dimension = 0
    rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
    change (Nat.card Unit - Nat.card Unit) + P.dimension = 0
    simpa using hdim
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 B D :=
    Q'.isStandardSmoothOfRelativeDimension hdim'
  letI : Algebra.Etale B D := inferInstance
  have hsub : (PrimeSpectrum.basicOpen j : Set (PrimeSpectrum C)) ⊆
      Algebra.etaleLocus B C :=
    Algebra.basicOpen_subset_etaleLocus_iff.mpr inferInstance
  exact hsub (show (⟨q, inferInstance⟩ : PrimeSpectrum C) ∈ PrimeSpectrum.basicOpen j from hq)

end AffineJacobian.EtalePresentation

end
end EtaleProjectionBundle0

section EtaleProjectionBundle1

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AffineJacobian.EtalePresentation

open MvPolynomial

variable {K σ δ : Type*} [CommRing K]

/-- Evaluate the coefficient variables by a polynomial map, leaving the
outer polynomial variables fixed. -/
def graphSubstitution (f : MvPolynomial δ K →ₐ[K] MvPolynomial σ K) :
    MvPolynomial σ (MvPolynomial δ K) →+* MvPolynomial σ K :=
  eval₂Hom f.toRingHom X

def graphRelation (f : MvPolynomial δ K →ₐ[K] MvPolynomial σ K) (i : δ) :
    MvPolynomial σ (MvPolynomial δ K) :=
  map C (f (X i)) - C (X i)

@[simp] theorem graphSubstitution_C
    (f : MvPolynomial δ K →ₐ[K] MvPolynomial σ K) (b : MvPolynomial δ K) :
    graphSubstitution f (C b) = f b := eval₂Hom_C _ _ _

@[simp] theorem graphSubstitution_X
    (f : MvPolynomial δ K →ₐ[K] MvPolynomial σ K) (i : σ) :
    graphSubstitution f (X i) = X i := eval₂Hom_X' _ _ _

theorem graphSubstitution_map
    (f : MvPolynomial δ K →ₐ[K] MvPolynomial σ K) (P : MvPolynomial σ K) :
    graphSubstitution f (map C P) = P := by
  have h : (graphSubstitution f).comp (map C) = RingHom.id (MvPolynomial σ K) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa only [RingHom.comp_apply, map_C, graphSubstitution_C, RingHom.id_apply,
        MvPolynomial.algebraMap_eq]
        using f.commutes a
    · intro i
      simp only [RingHom.comp_apply, map_X, graphSubstitution_X, RingHom.id_apply]
  exact congrArg (fun g : MvPolynomial σ K →+* MvPolynomial σ K => g P) h

theorem graphSubstitution_surjective
    (f : MvPolynomial δ K →ₐ[K] MvPolynomial σ K) :
    Function.Surjective (graphSubstitution f) :=
  fun P => ⟨map C P, graphSubstitution_map f P⟩

theorem ker_graphSubstitution
    (f : MvPolynomial δ K →ₐ[K] MvPolynomial σ K) :
    RingHom.ker (graphSubstitution f) = Ideal.span (Set.range (graphRelation f)) := by
  apply le_antisymm
  · intro P hP
    have hdiff (P : MvPolynomial σ (MvPolynomial δ K)) :
        map C (graphSubstitution f P) - P ∈ Ideal.span (Set.range (graphRelation f)) := by
      induction P using MvPolynomial.induction_on with
      | add P Q hP hQ =>
        simpa only [map_add, add_sub_add_comm] using Ideal.add_mem _ hP hQ
      | mul_X P i hP =>
        simpa only [map_mul, graphSubstitution_X, map_X, ← sub_mul] using
          (Ideal.span (Set.range (graphRelation f))).mul_mem_right (X i) hP
      | C b =>
        rw [graphSubstitution_C]
        induction b using MvPolynomial.induction_on with
        | C a =>
          have ha : f (C a) = C a := f.commutes a
          simp only [ha, map_C, sub_self, Submodule.zero_mem]
        | add b c hb hc =>
          simpa only [map_add, add_sub_add_comm] using Ideal.add_mem _ hb hc
        | mul_X b i hb =>
          simp only [map_mul]
          exact Ideal.mul_sub_mul_mem _ hb (Ideal.subset_span ⟨i, rfl⟩)
    have h := hdiff P
    have hzero : graphSubstitution f P = 0 := hP
    simpa only [hzero, map_zero, zero_sub, neg_mem_iff] using h
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change graphSubstitution f (graphRelation f i) = 0
    rw [graphRelation, map_sub, graphSubstitution_map, graphSubstitution_C, sub_self]

def graphQuotientHom (f : MvPolynomial δ K →ₐ[K] MvPolynomial σ K)
    (J : Ideal (MvPolynomial σ K)) :
    letI := ((Ideal.Quotient.mk J).comp f.toRingHom).toAlgebra
    MvPolynomial σ (MvPolynomial δ K) →ₐ[MvPolynomial δ K] (MvPolynomial σ K) ⧸ J :=
  letI := ((Ideal.Quotient.mk J).comp f.toRingHom).toAlgebra
  { (Ideal.Quotient.mk J).comp (graphSubstitution f) with
    commutes' := by
      intro b
      change Ideal.Quotient.mk J (graphSubstitution f (C b)) = _
      rw [graphSubstitution_C]
      rfl }

theorem graphQuotientHom_surjective
    (f : MvPolynomial δ K →ₐ[K] MvPolynomial σ K) (J : Ideal (MvPolynomial σ K)) :
    Function.Surjective (graphQuotientHom f J) :=
  Ideal.Quotient.mk_surjective.comp (graphSubstitution_surjective f)

def graphQuotientRelation {η : Type*}
    (f : MvPolynomial δ K →ₐ[K] MvPolynomial σ K) (F : η → MvPolynomial σ K) :
    η ⊕ δ → MvPolynomial σ (MvPolynomial δ K) :=
  Sum.elim (fun i => map C (F i)) (graphRelation f)

theorem ker_graphQuotientHom {η : Type*}
    (f : MvPolynomial δ K →ₐ[K] MvPolynomial σ K) (F : η → MvPolynomial σ K) :
    RingHom.ker ((Ideal.Quotient.mk (Ideal.span (Set.range F))).comp (graphSubstitution f)) =
      Ideal.span (Set.range (graphQuotientRelation f F)) := by
  let I : Ideal (MvPolynomial σ (MvPolynomial δ K)) :=
    Ideal.span (Set.range fun i => map C (F i))
  have hmap : I.map (graphSubstitution f) = Ideal.span (Set.range F) := by
    rw [Ideal.map_span, ← Set.range_comp]
    simp only [Function.comp_def, graphSubstitution_map]
  rw [← RingHom.comap_ker, Ideal.mk_ker]
  rw [← hmap, Ideal.comap_map_of_surjective _ (graphSubstitution_surjective f)]
  change I ⊔ RingHom.ker (graphSubstitution f) = _
  rw [ker_graphSubstitution]
  simp only [graphQuotientRelation, Set.Sum.elim_range, Ideal.span_union, I]

def graphPresentation {η : Type*}
    (f : MvPolynomial δ K →ₐ[K] MvPolynomial σ K) (F : η → MvPolynomial σ K) :
    letI := ((Ideal.Quotient.mk (Ideal.span (Set.range F))).comp f.toRingHom).toAlgebra
    Algebra.Presentation (MvPolynomial δ K)
      ((MvPolynomial σ K) ⧸ Ideal.span (Set.range F)) σ (η ⊕ δ) :=
  letI := ((Ideal.Quotient.mk (Ideal.span (Set.range F))).comp f.toRingHom).toAlgebra
  { Algebra.Generators.ofAlgHom (graphQuotientHom f (Ideal.span (Set.range F)))
      (graphQuotientHom_surjective f _) with
    relation := graphQuotientRelation f F
    span_range_relation_eq_ker := by
      rw [Algebra.Generators.ker_ofAlgHom]
      exact (ker_graphQuotientHom f F).symm }

def preGraphPresentation {η : Type*}
    (f : MvPolynomial δ K →ₐ[K] MvPolynomial σ K) (F : η → MvPolynomial σ K)
    (e : η ⊕ δ ≃ σ) :
    letI := ((Ideal.Quotient.mk (Ideal.span (Set.range F))).comp f.toRingHom).toAlgebra
    Algebra.PreSubmersivePresentation (MvPolynomial δ K)
      ((MvPolynomial σ K) ⧸ Ideal.span (Set.range F)) σ (η ⊕ δ) :=
  letI := ((Ideal.Quotient.mk (Ideal.span (Set.range F))).comp f.toRingHom).toAlgebra
  { graphPresentation f F with map := e, map_inj := e.injective }

end AffineJacobian.EtalePresentation

end
end EtaleProjectionBundle1

section EtaleProjectionBundle2

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AffineJacobian.EtalePresentation
open MvPolynomial

theorem preGraphPresentation_jacobian
    {K σ δ η : Type*} [CommRing K] [Fintype η] [Fintype δ]
    [DecidableEq η] [DecidableEq δ]
    (f : MvPolynomial δ K →ₐ[K] MvPolynomial σ K) (F : η → MvPolynomial σ K)
    (e : η ⊕ δ ≃ σ) :
    letI := ((Ideal.Quotient.mk (Ideal.span (Set.range F))).comp f.toRingHom).toAlgebra
    (preGraphPresentation f F e).jacobian =
      Ideal.Quotient.mk (Ideal.span (Set.range F))
        (Matrix.of (fun i j => pderiv (e i) (Sum.elim F (fun k => f (X k)) j))).det := by
  letI := ((Ideal.Quotient.mk (Ideal.span (Set.range F))).comp f.toRingHom).toAlgebra
  let P := preGraphPresentation f F e
  have halg : algebraMap P.Ring ((MvPolynomial σ K) ⧸ Ideal.span (Set.range F)) =
      (graphQuotientHom f (Ideal.span (Set.range F))).toRingHom := by
    rw [P.algebraMap_eq]
    apply MvPolynomial.ringHom_ext
    · intro b
      change aeval P.val (C b) = graphQuotientHom f (Ideal.span (Set.range F)) (C b)
      rw [aeval_C]
      simpa only [MvPolynomial.algebraMap_eq] using
        ((graphQuotientHom f (Ideal.span (Set.range F))).commutes b).symm
    · intro i
      change aeval P.val (X i) = graphQuotientHom f (Ideal.span (Set.range F)) (X i)
      rw [aeval_X]
      rfl
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, halg]
  change Ideal.Quotient.mk _ (graphSubstitution f P.jacobiMatrix.det) = _
  rw [RingHom.map_det]
  congr 1
  congr 1
  apply Matrix.ext
  intro i j
  change graphSubstitution f (P.jacobiMatrix i j) = _
  rw [P.jacobiMatrix_apply]
  change graphSubstitution f (pderiv (e i) (graphQuotientRelation f F j)) = _
  cases j with
  | inl j =>
    simp only [graphQuotientRelation, Sum.elim_inl, pderiv_map, graphSubstitution_map,
      Matrix.of_apply]
  | inr j =>
    simp only [graphQuotientRelation, Sum.elim_inr, graphRelation, map_sub,
      pderiv_map, pderiv_C, sub_zero, graphSubstitution_map, Matrix.of_apply]

end AffineJacobian.EtalePresentation

end
end EtaleProjectionBundle2

section EtaleProjectionBundle3

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section

open scoped BigOperators
namespace AffineJacobian.EtalePresentation

theorem transpose_det_ne_zero_of_linearEquiv
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ] [DecidableEq τ]
    (L : (σ → K) ≃ₗ[K] (τ → K)) (e : τ ≃ σ)
    (M : Matrix τ σ K) (hL : ∀ v i, L v i = ∑ j, M i j * v j) :
    (Matrix.of (fun i j => M j (e i))).det ≠ 0 := by
  classical
  let E := (LinearEquiv.piCongrLeft' K (fun _ : τ => K) e).trans L
  have hE : E.toLinearMap.toMatrix' = Matrix.of (fun i j => M i (e j)) := by
    ext i j
    change L ((LinearEquiv.piCongrLeft' K (fun _ : τ => K) e) (Pi.single j 1)) i = _
    rw [hL]
    change (∑ k, M i k * (Pi.single j (1 : K) : τ → K) (e.symm k)) = _
    rw [← e.sum_comp]
    simp [Pi.single_apply]
  have hdet : E.toLinearMap.toMatrix'.det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact E.isUnit_det'.ne_zero
  rw [hE] at hdet
  convert hdet using 1
  exact Matrix.det_transpose (Matrix.of (fun i j => M i (e j)))

end AffineJacobian.EtalePresentation

end
end EtaleProjectionBundle3

section EtaleProjectionBundle4

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

open scoped BigOperators
namespace AffineJacobian.EtalePresentation
open MvPolynomial

theorem centered_pderiv {K σ δ : Type*} [CommRing K] [Fintype σ]
    (a : σ → K) (c : δ → σ → K) (i : δ) (j : σ) :
    pderiv j (∑ k, C (c i k) * (X k - C (a k))) = C (c i j) := by
  classical
  simp [pderiv_X, Pi.single_apply]

theorem isEtaleAt_centered_projection
    (K σ : Type*) [Field K] [Fintype σ]
    (r d : ℕ) (F : Fin r → MvPolynomial σ K) (a : σ → K)
    (hF : ∀ i, MvPolynomial.eval a (F i) = 0)
    (c : Fin d → σ → K)
    (L : (σ → K) ≃ₗ[K] ((Fin r → K) × (Fin d → K)))
    (hL : ∀ v, L v =
      ((fun i => ∑ j, MvPolynomial.eval a (MvPolynomial.pderiv j (F i)) * v j),
       (fun i => ∑ j, c i j * v j)))
    (q : Ideal ((MvPolynomial σ K) ⧸ Ideal.span (Set.range F))) [q.IsPrime]
    (hq : q.comap (Ideal.Quotient.mk (Ideal.span (Set.range F))) =
      RingHom.ker (MvPolynomial.eval a)) :
    letI : Algebra (MvPolynomial (Fin d) K)
        ((MvPolynomial σ K) ⧸ Ideal.span (Set.range F)) :=
      ((Ideal.Quotient.mk (Ideal.span (Set.range F))).comp
        (MvPolynomial.aeval (fun i => ∑ j,
          MvPolynomial.C (c i j) * (MvPolynomial.X j - MvPolynomial.C (a j)))).toRingHom).toAlgebra
    Algebra.IsEtaleAt (MvPolynomial (Fin d) K) q := by
  classical
  let f : MvPolynomial (Fin d) K →ₐ[K] MvPolynomial σ K :=
    aeval (fun i => ∑ j, C (c i j) * (X j - C (a j)))
  letI := ((Ideal.Quotient.mk (Ideal.span (Set.range F))).comp f.toRingHom).toAlgebra
  let L' : (σ → K) ≃ₗ[K] (Fin r ⊕ Fin d → K) :=
    L.trans (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin d) K K).symm
  have hcard : Fintype.card (Fin r ⊕ Fin d) = Fintype.card σ := by
    simpa only [Module.finrank_fintype_fun_eq_card] using L'.symm.finrank_eq
  let e : Fin r ⊕ Fin d ≃ σ := Fintype.equivOfCardEq hcard
  let P := preGraphPresentation f F e
  refine isEtaleAt_of_jacobian_not_mem P ?_ q ?_
  · change Nat.card σ - Nat.card (Fin r ⊕ Fin d) = 0
    rw [Nat.card_congr e, Nat.sub_self]
  · rw [preGraphPresentation_jacobian]
    intro hmem
    have hz : (Matrix.of (fun i j => pderiv (e i)
        (Sum.elim F (fun k => f (X k)) j))).det ∈
        q.comap (Ideal.Quotient.mk (Ideal.span (Set.range F))) := hmem
    rw [hq] at hz
    change eval a _ = 0 at hz
    rw [RingHom.map_det] at hz
    let M : Matrix (Fin r ⊕ Fin d) σ K :=
      Sum.elim (fun i j => eval a (pderiv j (F i))) c
    have hM : ∀ v i, L' v i = ∑ j, M i j * v j := by
      intro v i
      change ((LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin d) K K).symm
        (L v)) i = _
      rw [hL]
      cases i <;> rfl
    apply transpose_det_ne_zero_of_linearEquiv L' e M hM
    convert hz using 1
    congr 1
    ext i j
    change M j (e i) = eval a (pderiv (e i) (Sum.elim F (fun k => f (X k)) j))
    cases j with
    | inl j => rfl
    | inr j =>
      change c j (e i) = eval a (pderiv (e i) (f (X j)))
      simp only [f, aeval_X, centered_pderiv, eval_C]

end AffineJacobian.EtalePresentation

end
end EtaleProjectionBundle4

open scoped BigOperators

theorem solution
    (K σ : Type*) [Field K] [Fintype σ]
    (r d : ℕ) (F : Fin r → MvPolynomial σ K) (a : σ → K)
    (hF : ∀ i, MvPolynomial.eval a (F i) = 0)
    (c : Fin d → σ → K)
    (L : (σ → K) ≃ₗ[K] ((Fin r → K) × (Fin d → K)))
    (hL : ∀ v, L v =
      ((fun i => ∑ j, MvPolynomial.eval a (MvPolynomial.pderiv j (F i)) * v j),
       (fun i => ∑ j, c i j * v j)))
    (q : Ideal ((MvPolynomial σ K) ⧸ Ideal.span (Set.range F))) [q.IsPrime]
    (hq : q.comap (Ideal.Quotient.mk (Ideal.span (Set.range F))) =
      RingHom.ker (MvPolynomial.eval a)) :
    letI : Algebra (MvPolynomial (Fin d) K)
        ((MvPolynomial σ K) ⧸ Ideal.span (Set.range F)) :=
      ((Ideal.Quotient.mk (Ideal.span (Set.range F))).comp
        (MvPolynomial.aeval (fun i => ∑ j,
          MvPolynomial.C (c i j) * (MvPolynomial.X j - MvPolynomial.C (a j)))).toRingHom).toAlgebra
    Algebra.IsEtaleAt (MvPolynomial (Fin d) K) q := by
  exact AffineJacobian.EtalePresentation.isEtaleAt_centered_projection
    K σ r d F a hF c L hL q hq
