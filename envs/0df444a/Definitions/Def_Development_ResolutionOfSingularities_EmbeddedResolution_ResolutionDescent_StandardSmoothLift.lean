-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_StandardSmoothLift
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_StandardSmoothLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:52.788801+00:00
-- url     : https://prove2.me/theorems/0219053c-fd2c-4409-893c-6376998329e3
-- title:
--   Standard Smooth Lift
-- statement:
--   Definitions and structural lemmas for Standard Smooth Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/StandardSmoothLift.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped TensorProduct
namespace FunctorialResolution.EmbeddedResolution
namespace StandardSmoothLift
universe u
section
variable {S R B : Type u} [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] {ι σ : Type} [Finite σ]
  (hsurj : Function.Surjective (algebraMap S R))
  (P : Algebra.SubmersivePresentation R B ι σ)
noncomputable def liftedRelation (j : σ) : MvPolynomial ι S :=
  Function.surjInv (MvPolynomial.map_surjective (algebraMap S R) hsurj) (P.relation j)
theorem map_liftedRelation (j : σ) :
    MvPolynomial.map (algebraMap S R) (liftedRelation hsurj P j) = P.relation j :=
  Function.surjInv_eq (MvPolynomial.map_surjective (algebraMap S R) hsurj) (P.relation j)
abbrev LiftedQuotient : Type u :=
  MvPolynomial ι S ⧸ Ideal.span (Set.range (liftedRelation hsurj P))
theorem aeval_mk_X_liftedQuotient_surjective :
    Function.Surjective
      ⇑(MvPolynomial.aeval (fun i : ι =>
          Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) (MvPolynomial.X i)) :
        MvPolynomial ι S →ₐ[S] LiftedQuotient hsurj P) := by
  have hEq : (MvPolynomial.aeval (fun i : ι =>
      Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) (MvPolynomial.X i)) :
        MvPolynomial ι S →ₐ[S] LiftedQuotient hsurj P) =
      Ideal.Quotient.mkₐ S (Ideal.span (Set.range (liftedRelation hsurj P))) :=
    MvPolynomial.algHom_ext (fun i => by simp)
  have h : ∀ q : MvPolynomial ι S,
      (MvPolynomial.aeval (fun i : ι =>
        Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) (MvPolynomial.X i)) :
        MvPolynomial ι S →ₐ[S] LiftedQuotient hsurj P) q =
      Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) q := by
    intro q
    rw [hEq]
    rfl
  intro x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨q, h q⟩
noncomputable def liftedGenerators : Algebra.Generators S (LiftedQuotient hsurj P) ι where
  val i := Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) (MvPolynomial.X i)
  σ' := Function.surjInv (aeval_mk_X_liftedQuotient_surjective hsurj P)
  aeval_val_σ' := Function.surjInv_eq (aeval_mk_X_liftedQuotient_surjective hsurj P)
theorem span_range_liftedRelation_eq_ker :
    Ideal.span (Set.range (liftedRelation hsurj P)) = (liftedGenerators hsurj P).ker := by
  have hval : (liftedGenerators hsurj P).val =
      fun i : ι => Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P)))
        (MvPolynomial.X i) := rfl
  have h : (MvPolynomial.aeval (liftedGenerators hsurj P).val :
        MvPolynomial ι S →ₐ[S] LiftedQuotient hsurj P) =
      Ideal.Quotient.mkₐ S (Ideal.span (Set.range (liftedRelation hsurj P))) :=
    MvPolynomial.algHom_ext fun i => by
      simp [hval]
  have hq : ∀ q : MvPolynomial ι S,
      (MvPolynomial.aeval (liftedGenerators hsurj P).val) q =
        Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) q :=
    fun q => DFunLike.congr_fun h q
  refine Ideal.ext fun q => ?_
  have hmem : q ∈ (liftedGenerators hsurj P).ker ↔
      (MvPolynomial.aeval (liftedGenerators hsurj P).val) q = 0 := Iff.rfl
  rw [hmem, hq q, Ideal.Quotient.eq_zero_iff_mem]
noncomputable def liftedPresentation : Algebra.Presentation S (LiftedQuotient hsurj P) ι σ where
  toGenerators := liftedGenerators hsurj P
  relation := liftedRelation hsurj P
  span_range_relation_eq_ker := span_range_liftedRelation_eq_ker hsurj P
noncomputable def liftedPreSubmersivePresentation :
    Algebra.PreSubmersivePresentation S (LiftedQuotient hsurj P) ι σ where
  toPresentation := liftedPresentation hsurj P
  map := P.map
  map_inj := P.map_inj
@[simp] theorem liftedPreSubmersivePresentation_relation (j : σ) :
    (liftedPreSubmersivePresentation hsurj P).relation j = liftedRelation hsurj P j := rfl
@[simp] theorem liftedPreSubmersivePresentation_map :
    (liftedPreSubmersivePresentation hsurj P).map = P.map := rfl
abbrev LiftedAlgebra : Type u := Localization.Away (liftedPreSubmersivePresentation hsurj P).jacobian
theorem isUnit_jacobian_localizationAway_comp :
    IsUnit (Algebra.PreSubmersivePresentation.comp
      (Algebra.PreSubmersivePresentation.localizationAway (S := LiftedAlgebra hsurj P)
        (liftedPreSubmersivePresentation hsurj P).jacobian) (liftedPreSubmersivePresentation hsurj P)).jacobian := by
  rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.smul_def]
  exact (IsLocalization.Away.algebraMap_isUnit (S := LiftedAlgebra hsurj P)
      (liftedPreSubmersivePresentation hsurj P).jacobian).mul
    (Algebra.SubmersivePresentation.localizationAway (S := LiftedAlgebra hsurj P)
      (liftedPreSubmersivePresentation hsurj P).jacobian).jacobian_isUnit
noncomputable def liftedSubmersivePresentation :
    Algebra.SubmersivePresentation S (LiftedAlgebra hsurj P) (Unit ⊕ ι) (Unit ⊕ σ) where
  toPreSubmersivePresentation :=
    Algebra.PreSubmersivePresentation.comp
      (Algebra.PreSubmersivePresentation.localizationAway (S := LiftedAlgebra hsurj P)
        (liftedPreSubmersivePresentation hsurj P).jacobian) (liftedPreSubmersivePresentation hsurj P)
  jacobian_isUnit := isUnit_jacobian_localizationAway_comp hsurj P
noncomputable def mvPolynomialToBaseChange :
    MvPolynomial ι R →ₐ[R] R ⊗[S] LiftedAlgebra hsurj P :=
  MvPolynomial.aeval fun i : ι =>
    (1 : R) ⊗ₜ[S] (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P)
      (Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) (MvPolynomial.X i)))
theorem mvPolynomialToBaseChange_map (f : MvPolynomial ι S) :
    mvPolynomialToBaseChange hsurj P (MvPolynomial.map (algebraMap S R) f) =
      (1 : R) ⊗ₜ[S] (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P)
        (Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) f)) := by
  induction f using MvPolynomial.induction_on
  next a =>
    have hI : Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P)))
        (MvPolynomial.C a) = algebraMap S (LiftedQuotient hsurj P) a := by
      rw [← MvPolynomial.algebraMap_eq]
      exact (Ideal.Quotient.mkₐ S (Ideal.span (Set.range (liftedRelation hsurj P)))).commutes a
    have hL : mvPolynomialToBaseChange hsurj P (MvPolynomial.map (algebraMap S R) (MvPolynomial.C a))
        = algebraMap S (R ⊗[S] LiftedAlgebra hsurj P) a := by
      rw [MvPolynomial.map_C]
      simp only [mvPolynomialToBaseChange, MvPolynomial.aeval_C]
      rw [← IsScalarTower.algebraMap_apply S R (R ⊗[S] LiftedAlgebra hsurj P) a]
    rw [hL, hI, ← IsScalarTower.algebraMap_apply S (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) a,
      Algebra.algebraMap_eq_smul_one a, Algebra.algebraMap_eq_smul_one a,
      Algebra.TensorProduct.one_def, TensorProduct.tmul_smul]
  next p q hp hq =>
    simp [hp, hq, TensorProduct.tmul_add]
  next p i hp =>
    have hX : mvPolynomialToBaseChange hsurj P (MvPolynomial.X i)
        = (1 : R) ⊗ₜ[S] (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P)
            (Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P)))
              (MvPolynomial.X i))) := by
      simp [mvPolynomialToBaseChange]
    simp [hp, hX, Algebra.TensorProduct.tmul_mul_tmul]
theorem mvPolynomialToBaseChange_relation_eq_zero (j : σ) :
    mvPolynomialToBaseChange hsurj P (P.relation j) = 0 := by
  have hz : Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P)))
      (liftedRelation hsurj P j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j))
  have h := mvPolynomialToBaseChange_map hsurj P (liftedRelation hsurj P j)
  rw [map_liftedRelation hsurj P j, hz] at h
  simpa using h
theorem mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero (q : MvPolynomial ι R)
    (hq : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B) q = 0) :
    mvPolynomialToBaseChange hsurj P q = 0 := by
  have hmem : q ∈ Ideal.span (Set.range P.relation) := by
    rw [P.span_range_relation_eq_ker, Algebra.Generators.ker_eq_ker_aeval_val]
    simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hq
  have hsub : Ideal.span (Set.range P.relation) ≤
      RingHom.ker (mvPolynomialToBaseChange hsurj P : MvPolynomial ι R →+* R ⊗[S] LiftedAlgebra hsurj P) := by
    rw [Ideal.span_le]
    rintro x ⟨j, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.coe_toRingHom]
    exact mvPolynomialToBaseChange_relation_eq_zero hsurj P j
  simpa only [RingHom.mem_ker, AlgHom.coe_toRingHom] using hsub hmem
theorem mvPolynomialToBaseChange_section_one :
    mvPolynomialToBaseChange hsurj P (P.σ' 1) = 1 := by
  have h1 : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B) (P.σ' (1 : B) - 1) = 0 := by
    rw [map_sub, map_one, P.aeval_val_σ' 1, sub_self]
  have h0 := mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero hsurj P _ h1
  rw [map_sub, map_one] at h0
  linear_combination h0
theorem mvPolynomialToBaseChange_section_mul (x y : B) :
    mvPolynomialToBaseChange hsurj P (P.σ' (x * y)) =
      mvPolynomialToBaseChange hsurj P (P.σ' x) * mvPolynomialToBaseChange hsurj P (P.σ' y) := by
  have hker : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B)
      (P.σ' (x * y) - P.σ' x * P.σ' y) = 0 := by
    simp [P.aeval_val_σ']
  have h := mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero hsurj P _ hker
  rw [map_sub, map_mul] at h
  linear_combination h
theorem mvPolynomialToBaseChange_section_zero :
    mvPolynomialToBaseChange hsurj P (P.σ' 0) = 0 := by
  have h0 : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B) (P.σ' (0 : B)) = 0 :=
    P.aeval_val_σ' 0
  exact mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero hsurj P _ h0
theorem mvPolynomialToBaseChange_section_add (x y : B) :
    mvPolynomialToBaseChange hsurj P (P.σ' (x + y)) =
      mvPolynomialToBaseChange hsurj P (P.σ' x) + mvPolynomialToBaseChange hsurj P (P.σ' y) := by
  have h1 : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B)
      (P.σ' (x + y) - (P.σ' x + P.σ' y)) = 0 := by
    rw [map_sub, map_add, P.aeval_val_σ' (x + y), P.aeval_val_σ' x, P.aeval_val_σ' y, sub_self]
  have h0 := mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero hsurj P _ h1
  rw [map_sub, map_add] at h0
  linear_combination h0
theorem mvPolynomialToBaseChange_section_algebraMap (r : R) :
    mvPolynomialToBaseChange hsurj P (P.σ' (algebraMap R B r)) =
      algebraMap R (R ⊗[S] LiftedAlgebra hsurj P) r := by
  have h1 : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B)
      (P.σ' (algebraMap R B r) - MvPolynomial.C r) = 0 := by
    rw [map_sub, P.aeval_val_σ' (algebraMap R B r), MvPolynomial.aeval_C, sub_self]
  have h0 := mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero hsurj P _ h1
  have hC : mvPolynomialToBaseChange hsurj P (MvPolynomial.C r) =
      algebraMap R (R ⊗[S] LiftedAlgebra hsurj P) r := by
    have hcom := (mvPolynomialToBaseChange hsurj P).commutes r
    rwa [MvPolynomial.algebraMap_eq] at hcom
  rw [map_sub, hC] at h0
  linear_combination h0
noncomputable def invBaseChangeHom : B →ₐ[R] R ⊗[S] LiftedAlgebra hsurj P where
  toFun b := mvPolynomialToBaseChange hsurj P (P.σ' b)
  map_one' := mvPolynomialToBaseChange_section_one hsurj P
  map_mul' := mvPolynomialToBaseChange_section_mul hsurj P
  map_zero' := mvPolynomialToBaseChange_section_zero hsurj P
  map_add' := mvPolynomialToBaseChange_section_add hsurj P
  commutes' := mvPolynomialToBaseChange_section_algebraMap hsurj P
theorem invBaseChangeHom_aeval (q : MvPolynomial ι R) :
    invBaseChangeHom hsurj P (MvPolynomial.aeval P.val q) = mvPolynomialToBaseChange hsurj P q := by
  have hker : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B)
      (P.σ' ((MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B) q) - q) = 0 := by
    rw [map_sub, P.aeval_val_σ', sub_self]
  have h := mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero hsurj P _ hker
  rw [map_sub] at h
  have hf : invBaseChangeHom hsurj P ((MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B) q)
      = mvPolynomialToBaseChange hsurj P
          (P.σ' ((MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B) q)) := rfl
  rw [hf]
  linear_combination h
section
variable [Algebra S B] [IsScalarTower S R B]
theorem aeval_eq_zero_of_mem_span_liftedRelation (q : MvPolynomial ι S)
    (hq : q ∈ Ideal.span (Set.range (liftedRelation hsurj P))) :
    (MvPolynomial.aeval P.val : MvPolynomial ι S →ₐ[S] B) q = 0 := by
  have hsub : Ideal.span (Set.range (liftedRelation hsurj P)) ≤
      RingHom.ker (MvPolynomial.aeval P.val : MvPolynomial ι S →ₐ[S] B).toRingHom := by
    rw [Ideal.span_le]
    rintro x ⟨j, rfl⟩
    have hmem : P.relation j ∈ Ideal.span (Set.range P.relation) :=
      Ideal.subset_span ⟨j, rfl⟩
    rw [P.span_range_relation_eq_ker, Algebra.Generators.ker_eq_ker_aeval_val] at hmem
    have h0 : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B) (P.relation j) = 0 := by
      simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hmem
    have h1 : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B)
        (MvPolynomial.map (algebraMap S R) (liftedRelation hsurj P j)) =
          (MvPolynomial.aeval P.val : MvPolynomial ι S →ₐ[S] B) (liftedRelation hsurj P j) := by
      rw [MvPolynomial.aeval_map_algebraMap]
    rw [map_liftedRelation hsurj P j] at h1
    have h2 : (MvPolynomial.aeval P.val : MvPolynomial ι S →ₐ[S] B)
        (liftedRelation hsurj P j) = 0 := by
      rw [← h1]
      exact h0
    simpa only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] using h2
  simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hsub hq
noncomputable def liftedQuotientHom : LiftedQuotient hsurj P →ₐ[S] B :=
  Ideal.Quotient.liftₐ (Ideal.span (Set.range (liftedRelation hsurj P)))
    (MvPolynomial.aeval P.val : MvPolynomial ι S →ₐ[S] B)
    (aeval_eq_zero_of_mem_span_liftedRelation hsurj P)
@[simp] theorem liftedQuotientHom_mk (q : MvPolynomial ι S) :
    liftedQuotientHom hsurj P
        (Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) q) =
      (MvPolynomial.aeval P.val : MvPolynomial ι S →ₐ[S] B) q := rfl
theorem isUnit_liftedQuotientHom_jacobian :
    IsUnit ((liftedQuotientHom hsurj P).toRingHom (liftedPreSubmersivePresentation hsurj P).jacobian) := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  have hval : (liftedPreSubmersivePresentation hsurj P).val =
      fun i : ι => Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P)))
        (MvPolynomial.X i) := rfl
  have hmk : ∀ q : MvPolynomial ι S,
      (MvPolynomial.aeval (liftedPreSubmersivePresentation hsurj P).val) q =
        Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) q := by
    have h : (MvPolynomial.aeval (liftedPreSubmersivePresentation hsurj P).val :
          MvPolynomial ι S →ₐ[S] LiftedQuotient hsurj P) =
        Ideal.Quotient.mkₐ S (Ideal.span (Set.range (liftedRelation hsurj P))) :=
      MvPolynomial.algHom_ext fun i => by simp [hval]
    exact fun q => DFunLike.congr_fun h q
  have hmat : ∀ a b : σ,
      MvPolynomial.map (algebraMap S R) ((liftedPreSubmersivePresentation hsurj P).jacobiMatrix a b)
        = P.jacobiMatrix a b := by
    intro a b
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
      Algebra.PreSubmersivePresentation.jacobiMatrix_apply, liftedPreSubmersivePresentation_map,
      liftedPreSubmersivePresentation_relation, ← MvPolynomial.pderiv_map, map_liftedRelation]
  have h1 : (liftedPreSubmersivePresentation hsurj P).jacobiMatrix.map
      (MvPolynomial.map (algebraMap S R)) = P.jacobiMatrix := by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.map_apply]
    exact hmat a b
  have hdet : MvPolynomial.map (algebraMap S R)
      ((liftedPreSubmersivePresentation hsurj P).jacobiMatrix.det) = P.jacobiMatrix.det := by
    calc MvPolynomial.map (algebraMap S R) ((liftedPreSubmersivePresentation hsurj P).jacobiMatrix.det)
        = ((liftedPreSubmersivePresentation hsurj P).jacobiMatrix.map
            (MvPolynomial.map (algebraMap S R))).det := RingHom.map_det ..
      _ = P.jacobiMatrix.det := by rw [h1]
  have hjS : (liftedPreSubmersivePresentation hsurj P).jacobian =
      Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P)))
        ((liftedPreSubmersivePresentation hsurj P).jacobiMatrix.det) := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    exact hmk _
  have hjR : P.jacobian =
      (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B) P.jacobiMatrix.det := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Algebra.Generators.algebraMap_apply]
  have h2 : IsUnit (liftedQuotientHom hsurj P ((liftedPreSubmersivePresentation hsurj P).jacobian)) := by
    have hkey : liftedQuotientHom hsurj P ((liftedPreSubmersivePresentation hsurj P).jacobian) = P.jacobian := by
      rw [hjS, liftedQuotientHom_mk, hjR, ← hdet]
      simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
      rw [← IsScalarTower.algebraMap_eq S R B]
    rw [hkey]
    exact P.jacobian_isUnit
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using h2
theorem awayLift_jacobian_algebraMap_eq (s : S) :
    ((IsLocalization.Away.lift (liftedPreSubmersivePresentation hsurj P).jacobian
        (isUnit_liftedQuotientHom_jacobian hsurj P) : LiftedAlgebra hsurj P →+* B))
      (algebraMap S (LiftedAlgebra hsurj P) s) = algebraMap S B s := by
  have h : ∀ x : LiftedQuotient hsurj P,
      ((IsLocalization.Away.lift (liftedPreSubmersivePresentation hsurj P).jacobian
          (isUnit_liftedQuotientHom_jacobian hsurj P) : LiftedAlgebra hsurj P →+* B))
        (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) x) =
        (liftedQuotientHom hsurj P).toRingHom x := by
    intro x
    exact IsLocalization.lift_eq ..
  rw [IsScalarTower.algebraMap_apply S (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) s, h]
  exact (liftedQuotientHom hsurj P).commutes s
noncomputable def liftedAlgebraHom : LiftedAlgebra hsurj P →ₐ[S] B :=
  { (IsLocalization.Away.lift (liftedPreSubmersivePresentation hsurj P).jacobian
      (isUnit_liftedQuotientHom_jacobian hsurj P) : LiftedAlgebra hsurj P →+* B) with
    commutes' := awayLift_jacobian_algebraMap_eq hsurj P }
theorem liftedAlgebraHom_algebraMap (x : LiftedQuotient hsurj P) :
    liftedAlgebraHom hsurj P (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) x) =
      liftedQuotientHom hsurj P x := by
  have h : liftedAlgebraHom hsurj P (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) x) =
      (IsLocalization.Away.lift (liftedPreSubmersivePresentation hsurj P).jacobian
        (isUnit_liftedQuotientHom_jacobian hsurj P) : LiftedAlgebra hsurj P →+* B)
        (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) x) := rfl
  rw [h]
  simp only [IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
theorem liftedAlgebraHom_surjective : Function.Surjective (liftedAlgebraHom hsurj P) := by
  intro b
  obtain ⟨p, hp⟩ := MvPolynomial.map_surjective (algebraMap S R) hsurj (P.σ' b)
  have h1 : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B)
      (MvPolynomial.map (algebraMap S R) p) =
        (MvPolynomial.aeval P.val : MvPolynomial ι S →ₐ[S] B) p := by
    rw [MvPolynomial.aeval_map_algebraMap]
  refine ⟨algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P)
    (Ideal.Quotient.mk (Ideal.span (Set.range (liftedRelation hsurj P))) p), ?_⟩
  rw [liftedAlgebraHom_algebraMap, liftedQuotientHom_mk, ← h1, hp]
  exact P.aeval_val_σ' b
noncomputable def baseChangeHom : (R ⊗[S] LiftedAlgebra hsurj P) →ₐ[R] B :=
  Algebra.TensorProduct.lift (Algebra.ofId R B) (liftedAlgebraHom hsurj P)
    (fun _ _ => Commute.all _ _)
theorem invBaseChangeHom_liftedQuotientHom (q : LiftedQuotient hsurj P) :
    invBaseChangeHom hsurj P (liftedQuotientHom hsurj P q) =
      (1 : R) ⊗ₜ[S] (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) q) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  have h1 : (MvPolynomial.aeval P.val : MvPolynomial ι R →ₐ[R] B)
      (MvPolynomial.map (algebraMap S R) p) =
        (MvPolynomial.aeval P.val : MvPolynomial ι S →ₐ[S] B) p := by
    rw [MvPolynomial.aeval_map_algebraMap]
  rw [liftedQuotientHom_mk, ← h1, invBaseChangeHom_aeval]
  exact mvPolynomialToBaseChange_map hsurj P p
theorem invBaseChangeHom_liftedAlgebraHom (x : LiftedAlgebra hsurj P) :
    invBaseChangeHom hsurj P (liftedAlgebraHom hsurj P x) = (1 : R) ⊗ₜ[S] x := by
  have key : (invBaseChangeHom hsurj P).toRingHom.comp (liftedAlgebraHom hsurj P).toRingHom =
      (Algebra.TensorProduct.includeRight :
        LiftedAlgebra hsurj P →ₐ[S] R ⊗[S] LiftedAlgebra hsurj P).toRingHom := by
    refine IsLocalization.ringHom_ext
      (Submonoid.powers (liftedPreSubmersivePresentation hsurj P).jacobian) ?_
    refine RingHom.ext fun q => ?_
    have h := invBaseChangeHom_liftedQuotientHom hsurj P q
    rw [← liftedAlgebraHom_algebraMap hsurj P q] at h
    exact h
  exact DFunLike.congr_fun key x
theorem baseChangeHom_bijective : Function.Bijective (baseChangeHom hsurj P) := by
  constructor
  · have hleft : Function.LeftInverse (invBaseChangeHom hsurj P) (baseChangeHom hsurj P) := by
      intro t
      refine TensorProduct.induction_on t ?_ ?_ ?_
      · simp
      · intro r x
        have h1 : baseChangeHom hsurj P (r ⊗ₜ[S] x)
            = algebraMap R B r * liftedAlgebraHom hsurj P x := by
          simp only [baseChangeHom, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
        have h2 : invBaseChangeHom hsurj P (algebraMap R B r)
            = r ⊗ₜ[S] (1 : LiftedAlgebra hsurj P) := (invBaseChangeHom hsurj P).commutes r
        rw [h1, map_mul, h2, invBaseChangeHom_liftedAlgebraHom,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      · intro a b ha hb
        rw [map_add, map_add, ha, hb]
    exact hleft.injective
  · intro b
    obtain ⟨x, hx⟩ := liftedAlgebraHom_surjective hsurj P b
    refine ⟨(1 : R) ⊗ₜ[S] x, ?_⟩
    rw [← hx]
    simp only [baseChangeHom, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
noncomputable def baseChangeEquiv : (R ⊗[S] LiftedAlgebra hsurj P) ≃ₐ[R] B :=
  AlgEquiv.ofBijective (baseChangeHom hsurj P) (baseChangeHom_bijective hsurj P)
end
end
end StandardSmoothLift
end FunctorialResolution.EmbeddedResolution


