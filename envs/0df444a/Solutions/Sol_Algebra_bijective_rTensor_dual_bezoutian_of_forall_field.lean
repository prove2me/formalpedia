-- Prove2me | solution 1 for Algebra.bijective_rTensor_dual_bezoutian_of_forall_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/3ee05668-7ca2-574f-ae56-732390d66ea1

import Mathlib
import Theorems.Thm_LinearMap_bijective_of_forall_bijective_baseChange_quotient_maximal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_bijective_rTensor_dual_bezoutian_of_forall_field

set_option autoImplicit false

open scoped TensorProduct

universe u

namespace SchejaStorch

open TensorProduct

section general

variable {R : Type*} [CommRing R] {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
  (a : Fin m → Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
  (S : Type*) [CommRing S] [Algebra R S]

abbrev Q := MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)

noncomputable def theta : Module.Dual R (Q f) →ₗ[R] Q f where
  toFun φ := Algebra.TensorProduct.lid R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))
        (LinearMap.rTensor (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) φ
          (Algebra.TensorProduct.map
              (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
            (Matrix.det (Matrix.of a))))
  map_add' φ ψ := by simp [LinearMap.rTensor_add]
  map_smul' r φ := by simp [LinearMap.rTensor_smul]

noncomputable def mapP : MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) S :=
  MvPolynomial.mapAlgHom (Algebra.ofId R S)

@[scoped simp] lemma mapP_X (j : Fin m) : mapP (m := m) S (MvPolynomial.X j : MvPolynomial (Fin m) R) = MvPolynomial.X j := by
  simp [mapP]

noncomputable def fS : Fin m → MvPolynomial (Fin m) S := fun i => mapP S (f i)

noncomputable def psi : MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R →ₐ[R]
    MvPolynomial (Fin m) S ⊗[S] MvPolynomial (Fin m) S :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft (R := S) (S := R) (A := MvPolynomial (Fin m) S)
      (B := MvPolynomial (Fin m) S)).comp (mapP S))
    (((Algebra.TensorProduct.includeRight (R := S) (A := MvPolynomial (Fin m) S)
      (B := MvPolynomial (Fin m) S)).restrictScalars R).comp (mapP S))
    (fun _ _ => Commute.all _ _)

@[scoped simp] lemma psi_tmul (p q : MvPolynomial (Fin m) R) :
    psi (m := m) S (p ⊗ₜ q) = mapP S p ⊗ₜ mapP S q := by
  simp [psi]

noncomputable def aS : Fin m → Fin m → MvPolynomial (Fin m) S ⊗[S] MvPolynomial (Fin m) S :=
  fun i j => psi S (a i j)

lemma det_aS : Matrix.det (Matrix.of (aS a S)) = psi S (Matrix.det (Matrix.of a)) := by
  rw [AlgHom.map_det]
  rfl

lemma bezout_aS
    (ha : ∀ i, f i ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] f i =
      ∑ j, a i j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j)) :
    ∀ i, fS f S i ⊗ₜ[S] (1 : MvPolynomial (Fin m) S) - (1 : MvPolynomial (Fin m) S) ⊗ₜ[S] fS f S i =
      ∑ j, aS a S i j * (MvPolynomial.X j ⊗ₜ[S] 1 - 1 ⊗ₜ[S] MvPolynomial.X j) := by
  intro i
  have := congrArg (psi S) (ha i)
  simpa [map_sub, map_sum, map_mul, fS, aS] using this

noncomputable def iota : Q f →ₐ[R] Q (fS f S) :=
  Ideal.quotientMapₐ _ (mapP S) (by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨i, rfl⟩)

@[scoped simp] lemma iota_mk (p : MvPolynomial (Fin m) R) :
    iota f S (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (mapP S p) := rfl

noncomputable def deltaFwd : S ⊗[R] Q f →ₐ[S] Q (fS f S) :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (iota f S) (fun _ _ => Commute.all _ _)

@[scoped simp] lemma deltaFwd_tmul (s : S) (x : Q f) : deltaFwd f S (s ⊗ₜ x) = s • iota f S x := by
  simp [deltaFwd, ← Algebra.smul_def]

noncomputable def evalX : MvPolynomial (Fin m) S →ₐ[S] S ⊗[R] Q f :=
  MvPolynomial.aeval fun j => (1 : S) ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPolynomial.X j)

lemma evalX_mapP (p : MvPolynomial (Fin m) R) :
    evalX f S (mapP S p) = (1 : S) ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range f)) p := by
  suffices h : ((evalX f S).restrictScalars R).comp (mapP S) =
      (Algebra.TensorProduct.includeRight).comp (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) from
    congr($h p)
  apply MvPolynomial.algHom_ext
  intro j
  simp [evalX]

noncomputable def deltaInv : Q (fS f S) →ₐ[S] S ⊗[R] Q f :=
  Ideal.Quotient.liftₐ _ (evalX f S) (by
    intro p hp
    have hle : Ideal.span (Set.range (fS f S)) ≤ RingHom.ker (evalX f S) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have h0 : Ideal.Quotient.mk (Ideal.span (Set.range f)) (f i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
      simp [fS, evalX_mapP, h0]
    exact hle hp)

@[scoped simp] lemma deltaInv_mk (p : MvPolynomial (Fin m) S) :
    deltaInv f S (Ideal.Quotient.mk _ p) = evalX f S p := rfl

lemma deltaFwd_comp_deltaInv : (deltaFwd f S).comp (deltaInv f S) = AlgHom.id S _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  simp [evalX]

lemma deltaInv_comp_deltaFwd : (deltaInv f S).comp (deltaFwd f S) = AlgHom.id S _ := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    simp [evalX]

noncomputable def delta : S ⊗[R] Q f ≃ₐ[S] Q (fS f S) :=
  AlgEquiv.ofAlgHom (deltaFwd f S) (deltaInv f S) (deltaFwd_comp_deltaInv f S) (deltaInv_comp_deltaFwd f S)

lemma isBaseChange : IsBaseChange S (iota f S).toLinearMap :=
  IsBaseChange.of_equiv (delta f S).toLinearEquiv fun x => by simp [delta]

lemma finite_baseChange [Module.Finite R (Q f)] : Module.Finite S (Q (fS f S)) :=
  Module.Finite.equiv (delta f S).toLinearEquiv

lemma key (φ : Module.Dual R (Q f)) (φ' : Module.Dual S (Q (fS f S)))
    (h : ∀ p : MvPolynomial (Fin m) R, φ' (Ideal.Quotient.mk _ (mapP S p)) = algebraMap R S (φ (Ideal.Quotient.mk _ p)))
    (z : MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R) :
    Algebra.TensorProduct.lid S (Q (fS f S)) (LinearMap.rTensor (Q (fS f S)) φ'
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ S (Ideal.span (Set.range (fS f S))))
          (Ideal.Quotient.mkₐ S (Ideal.span (Set.range (fS f S)))) (psi S z)))
      = iota f S (Algebra.TensorProduct.lid R (Q f) (LinearMap.rTensor (Q f) φ
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
          (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) z))) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero (psi S), map_zero (Algebra.TensorProduct.map _ _), LinearMap.map_zero, map_zero (Algebra.TensorProduct.lid _ _),
      map_zero (Algebra.TensorProduct.map _ _), LinearMap.map_zero, map_zero (Algebra.TensorProduct.lid _ _), map_zero (iota f S)]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p q =>
    simp [h]

variable [Module.Free R (Q f)] [Module.Finite R (Q f)]

noncomputable def gamma : S ⊗[R] Module.Dual R (Q f) ≃ₗ[S] Module.Dual S (Q (fS f S)) :=
  (isBaseChange f S).toDualBaseChange

lemma gamma_tmul (φ : Module.Dual R (Q f)) (x : Q f) :
    gamma f S (1 ⊗ₜ φ) (iota f S x) = algebraMap R S (φ x) := by
  have := (isBaseChange f S).toDualBaseChange_tmul 1 φ x
  simpa [gamma] using this

lemma square :
    (delta f S).toLinearEquiv.toLinearMap ∘ₗ (theta f a).baseChange S
      = (theta (fS f S) (aS a S)) ∘ₗ (gamma f S).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s φ
  have hk := key f S φ (gamma f S (1 ⊗ₜ φ)) (fun p => gamma_tmul f S φ (Ideal.Quotient.mk _ p))
    (Matrix.det (Matrix.of a))
  have hs : s ⊗ₜ[R] φ = s • ((1 : S) ⊗ₜ[R] φ) := by simp [TensorProduct.smul_tmul']
  rw [hs, map_smul, map_smul]
  congr 1
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.baseChange_tmul,
    AlgEquiv.toLinearEquiv_apply]
  change deltaFwd f S (1 ⊗ₜ theta f a φ) = _
  rw [deltaFwd_tmul, one_smul]
  show iota f S (theta f a φ) = theta (fS f S) (aS a S) (gamma f S (1 ⊗ₜ φ))
  simp only [theta, LinearMap.coe_mk, AddHom.coe_mk]
  rw [det_aS]
  exact hk.symm

lemma bijective_iff :
    Function.Bijective (theta (fS f S) (aS a S)) ↔ Function.Bijective ((theta f a).baseChange S) := by
  have hsq := square f a S
  have hfun : ⇑(theta (fS f S) (aS a S)) = (delta f S).toLinearEquiv ∘ (theta f a).baseChange S ∘ (gamma f S).symm := by
    funext ω
    have := congr($hsq ((gamma f S).symm ω))
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply] at this
    simpa using this.symm
  rw [hfun, EquivLike.comp_bijective, EquivLike.bijective_comp]

end general

lemma bijective_of_bijective_baseChange {k : Type*} (K : Type*) [Field k] [Field K] [Algebra k K]
    {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (T : V →ₗ[k] W)
    (h : Function.Bijective (T.baseChange K)) : Function.Bijective T := by
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective k K T, ← LinearMap.baseChange_eq_ltensor]
  exact h

end SchejaStorch
p2m_reactivate "P2MW.S_Algebra_bijective_rTensor_dual_bezoutian_of_forall_field.SchejaStorch"

open SchejaStorch in
theorem solution
    (R : Type u) [CommRing R] {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    [Module.Finite R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))]
    [Module.Free R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))]
    (a : Fin m → Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : ∀ i, f i ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] f i =
      ∑ j, a i j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j))
    (hfield : ∀ (K : Type u) [Field K] [IsAlgClosed K] (g : Fin m → MvPolynomial (Fin m) K)
      [Module.Finite K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))]
      (b : Fin m → Fin m → MvPolynomial (Fin m) K ⊗[K] MvPolynomial (Fin m) K),
      (∀ i, g i ⊗ₜ[K] (1 : MvPolynomial (Fin m) K) - (1 : MvPolynomial (Fin m) K) ⊗ₜ[K] g i =
        ∑ j, b i j * (MvPolynomial.X j ⊗ₜ[K] 1 - 1 ⊗ₜ[K] MvPolynomial.X j)) →
      Function.Bijective (fun φ : Module.Dual K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) =>
      Algebra.TensorProduct.lid K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))
        (LinearMap.rTensor (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) φ
          (Algebra.TensorProduct.map
              (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g))) (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g)))
            (Matrix.det (Matrix.of b)))))) :
    Function.Bijective (fun φ : Module.Dual R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) =>
      Algebra.TensorProduct.lid R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))
        (LinearMap.rTensor (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) φ
          (Algebra.TensorProduct.map
              (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
            (Matrix.det (Matrix.of a))))) := by
  change Function.Bijective (theta f a)
  apply LinearMap.bijective_of_forall_bijective_baseChange_quotient_maximal
  intro 𝔪 _
  letI := Ideal.Quotient.field 𝔪
  rw [← bijective_iff f a (R ⧸ 𝔪)]
  haveI : Module.Finite (R ⧸ 𝔪) (Q (fS f (R ⧸ 𝔪))) := finite_baseChange f (R ⧸ 𝔪)
  apply bijective_of_bijective_baseChange (AlgebraicClosure (R ⧸ 𝔪))
  rw [← bijective_iff (fS f (R ⧸ 𝔪)) (aS a (R ⧸ 𝔪)) (AlgebraicClosure (R ⧸ 𝔪))]
  haveI : Module.Finite (AlgebraicClosure (R ⧸ 𝔪))
      (Q (fS (fS f (R ⧸ 𝔪)) (AlgebraicClosure (R ⧸ 𝔪)))) := finite_baseChange _ _
  exact hfield (AlgebraicClosure (R ⧸ 𝔪)) (fS (fS f (R ⧸ 𝔪)) (AlgebraicClosure (R ⧸ 𝔪)))
    (aS (aS a (R ⧸ 𝔪)) (AlgebraicClosure (R ⧸ 𝔪)))
    (bezout_aS _ _ _ (bezout_aS f a (R ⧸ 𝔪) ha))

end S_Algebra_bijective_rTensor_dual_bezoutian_of_forall_field
end P2MW
export P2MW.S_Algebra_bijective_rTensor_dual_bezoutian_of_forall_field (solution)
