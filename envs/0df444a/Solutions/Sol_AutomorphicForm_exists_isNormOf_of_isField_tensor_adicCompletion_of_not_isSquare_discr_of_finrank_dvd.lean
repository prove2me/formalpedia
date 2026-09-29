-- Prove2me | solution 1 for AutomorphicForm.exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/14c07c56-b727-5bed-9ec1-c51ea2f1f9b9

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_exists_extension_algEquiv_adicCompletion_of_isField_tensor
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_algebraMap_eq_mul_sq_adicCompletion
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_unique_extension_and_algEquiv_adjoinRoot_of_not_isSquare
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_units_prod_tensor_map_iterate_eq_tmul_one_of_finrank_dvd_valuation_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct Polynomial
open scoped TensorProduct.RightActions

namespace InertProof

open AutomorphicForm

theorem Matrix.irreducible_charpoly_of_not_isSquare_trace_sq_sub_four_mul_det
    (F : Type) [Field F] (γ : Matrix (Fin 2) (Fin 2) F)
    (hγ : ¬ IsSquare (Matrix.trace γ ^ 2 - 4 * Matrix.det γ)) :
    Irreducible (Matrix.charpoly γ) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    decide
  · intro r hr
    apply hγ
    refine ⟨2 * r - Matrix.trace γ, ?_⟩
    rw [Matrix.charpoly_fin_two] at hr
    simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C] at hr
    linear_combination (-4 : F) * hr

theorem Matrix.natDegree_charpoly_fin_two (F : Type) [CommRing F] [Nontrivial F]
    (γ : Matrix (Fin 2) (Fin 2) F) :
    (Matrix.charpoly γ).natDegree = 2 := by
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem AdjoinRoot.norm_root_charpoly_eq_det (F : Type) [Field F]
    (γ : Matrix (Fin 2) (Fin 2) F) :
    Algebra.norm F (AdjoinRoot.root (Matrix.charpoly γ)) = Matrix.det γ := by
  have hmon : (Matrix.charpoly γ).Monic := Matrix.charpoly_monic γ
  have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
    (AdjoinRoot.powerBasis (K := F) hmon.ne_zero)
  rw [AdjoinRoot.minpoly_powerBasis_gen_of_monic hmon] at h
  rw [AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim, Matrix.charpoly_natDegree_eq_dim,
    Fintype.card_fin] at h
  rw [h, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin]

theorem Matrix.eval₂_ofId_self_charpoly (F : Type) [CommRing F]
    (γ : Matrix (Fin 2) (Fin 2) F) :
    (Matrix.charpoly γ).eval₂ (Algebra.ofId F (Matrix (Fin 2) (Fin 2) F)) γ = 0 := by
  have h := Matrix.aeval_self_charpoly γ
  rwa [Polynomial.aeval_def] at h

theorem AdjoinRoot.exists_algHom_charpoly_root_eq (F : Type) [CommRing F]
    (γ : Matrix (Fin 2) (Fin 2) F) :
    ∃ ι : AdjoinRoot (Matrix.charpoly γ) →ₐ[F] Matrix (Fin 2) (Fin 2) F,
      ι (AdjoinRoot.root (Matrix.charpoly γ)) = γ := by
  refine ⟨Ideal.Quotient.liftₐ (Ideal.span {Matrix.charpoly γ}) (Polynomial.aeval γ) ?_, ?_⟩
  · intro a ha
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, Matrix.aeval_self_charpoly, mul_zero]
  · change Ideal.Quotient.liftₐ (Ideal.span {Matrix.charpoly γ}) (Polynomial.aeval γ) _
        (Ideal.Quotient.mk _ Polynomial.X) = γ
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    exact Polynomial.aeval_X γ

namespace TorusTransport

variable {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E]
  {M₁ M₂ : Type} [CommRing M₁] [CommRing M₂] [Algebra F M₁] [Algebra F M₂]

theorem congr_map (τ₁ : M₁ →ₐ[F] M₁) (τ₂ : M₂ →ₐ[F] M₂) (φ : M₂ ≃ₐ[F] M₁)
    (hφ : ∀ m, φ (τ₂ m) = τ₁ (φ m)) (z : E ⊗[F] M₂) :
    Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[F] E) φ
        (Algebra.TensorProduct.map (AlgHom.id F E) τ₂ z) =
      Algebra.TensorProduct.map (AlgHom.id F E) τ₁
        (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[F] E) φ z) := by
  induction z with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a m => simp [Algebra.TensorProduct.congr_apply, hφ]

private theorem _root_.InertProof.TorusTransport.exists_units (τ₁ : M₁ →ₐ[F] M₁) (τ₂ : M₂ →ₐ[F] M₂) (φ : M₂ ≃ₐ[F] M₁)
    (hφ : ∀ m, φ (τ₂ m) = τ₁ (φ m))
    (n : ℕ) (x : E) (e : (E ⊗[F] M₂)ˣ)
    (he : ((List.range n).map fun i =>
            (⇑(Algebra.TensorProduct.map (AlgHom.id F E) τ₂))^[i] (e : E ⊗[F] M₂)).prod = x ⊗ₜ[F] (1 : M₂)) :
    ∃ e' : (E ⊗[F] M₁)ˣ,
      ((List.range n).map fun i =>
          (⇑(Algebra.TensorProduct.map (AlgHom.id F E) τ₁))^[i] (e' : E ⊗[F] M₁)).prod = x ⊗ₜ[F] (1 : M₁) := by
  have hsemi : Function.Semiconj (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[F] E) φ)
      (Algebra.TensorProduct.map (AlgHom.id F E) τ₂) (Algebra.TensorProduct.map (AlgHom.id F E) τ₁) :=
    congr_map τ₁ τ₂ φ hφ
  refine ⟨Units.map (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[F] E) φ : E ⊗[F] M₂ →* E ⊗[F] M₁) e, ?_⟩
  have hfun : (fun i => (⇑(Algebra.TensorProduct.map (AlgHom.id F E) τ₁))^[i]
        ((Units.map (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[F] E) φ : E ⊗[F] M₂ →* E ⊗[F] M₁) e :
          (E ⊗[F] M₁)ˣ) : E ⊗[F] M₁)) =
      (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[F] E) φ) ∘
        (fun i => (⇑(Algebra.TensorProduct.map (AlgHom.id F E) τ₂))^[i] (e : E ⊗[F] M₂)) := by
    funext i
    rw [Units.coe_map, MonoidHom.coe_coe]
    exact (hsemi.iterate_right i (e : E ⊗[F] M₂)).symm
  rw [hfun, ← List.map_map, ← map_list_prod, he]
  simp

p2m_export "InertProof.TorusTransport" "exists_units"
end TorusTransport

theorem Algebra.TensorProduct.exists_units_prod_map_iterate_eq_tmul_of_algEquiv
    (F : Type) [Field F] (E : Type) [CommRing E] [Algebra F E]
    (M₁ M₂ : Type) [CommRing M₁] [CommRing M₂] [Algebra F M₁] [Algebra F M₂]
    (τ₁ : M₁ →ₐ[F] M₁) (τ₂ : M₂ →ₐ[F] M₂) (φ : M₂ ≃ₐ[F] M₁) (hφ : ∀ m, φ (τ₂ m) = τ₁ (φ m))
    (n : ℕ) (x : E) (e : (E ⊗[F] M₂)ˣ)
    (he : ((List.range n).map fun i =>
            (⇑(Algebra.TensorProduct.map (AlgHom.id F E) τ₂))^[i] (e : E ⊗[F] M₂)).prod = x ⊗ₜ[F] (1 : M₂)) :
    ∃ e' : (E ⊗[F] M₁)ˣ,
      ((List.range n).map fun i =>
          (⇑(Algebra.TensorProduct.map (AlgHom.id F E) τ₁))^[i] (e' : E ⊗[F] M₁)).prod = x ⊗ₜ[F] (1 : M₁) :=
  TorusTransport.exists_units τ₁ τ₂ φ hφ n x e he

namespace TorusEmbed

variable {F : Type} [CommRing F] {E : Type} [CommRing E] [Algebra F E]
  {M : Type} [CommRing M] [Algebra F M]

noncomputable def phi (ι : E →ₐ[F] Matrix (Fin 2) (Fin 2) F) :
    E ⊗[F] M →ₐ[F] Matrix (Fin 2) (Fin 2) M :=
  Algebra.TensorProduct.lift ((AlgHom.mapMatrix (Algebra.ofId F M)).comp ι)
    ((Algebra.ofId M (Matrix (Fin 2) (Fin 2) M)).restrictScalars F)
    (fun _ b => (Algebra.commutes b _).symm)

theorem phi_tmul (ι : E →ₐ[F] Matrix (Fin 2) (Fin 2) F) (a : E) (m : M) :
    phi (M := M) ι (a ⊗ₜ[F] m) =
      (ι a).map (algebraMap F M) * algebraMap M (Matrix (Fin 2) (Fin 2) M) m := by
  simp [phi, Algebra.TensorProduct.lift_tmul, AlgHom.mapMatrix_apply, Algebra.ofId_apply]
  rfl

theorem map_map_algebraMap (τ : M →ₐ[F] M) (A : Matrix (Fin 2) (Fin 2) F) :
    (A.map (algebraMap F M)).map τ = A.map (algebraMap F M) := by
  rw [Matrix.map_map]
  congr 1
  funext c
  exact τ.commutes c

theorem map_algebraMap (τ : M →ₐ[F] M) (m : M) :
    (algebraMap M (Matrix (Fin 2) (Fin 2) M) m).map τ =
      algebraMap M (Matrix (Fin 2) (Fin 2) M) (τ m) := by
  rw [Matrix.algebraMap_eq_diagonal, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero τ)]
  rfl

theorem phi_map (ι : E →ₐ[F] Matrix (Fin 2) (Fin 2) F) (τ : M →ₐ[F] M) (z : E ⊗[F] M) :
    phi ι (Algebra.TensorProduct.map (AlgHom.id F E) τ z) = (phi ι z).map τ := by
  induction z with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add (phi ι), Matrix.map_add]
    exact map_add τ
  | tmul a m =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, phi_tmul, phi_tmul]
    change _ = (τ.toRingHom.mapMatrix) (_ * _)
    rw [map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, map_map_algebraMap, map_algebraMap]

theorem phi_tmul_one (ι : E →ₐ[F] Matrix (Fin 2) (Fin 2) F) (x : E) :
    phi (M := M) ι (x ⊗ₜ[F] 1) = (ι x).map (algebraMap F M) := by
  rw [phi_tmul, map_one, mul_one]

theorem coe_generalLinearGroup_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (g : GL (Fin 2) R) :
    ((Matrix.GeneralLinearGroup.map (n := Fin 2) f g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
      (g : Matrix (Fin 2) (Fin 2) R).map f := rfl

theorem map_unitsMap_phi (ι : E →ₐ[F] Matrix (Fin 2) (Fin 2) F) (τ : M →ₐ[F] M)
    (u : (E ⊗[F] M)ˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) τ.toRingHom (Units.map (phi ι).toMonoidHom u) =
      Units.map (phi ι).toMonoidHom
        (Units.map (Algebra.TensorProduct.map (AlgHom.id F E) τ).toMonoidHom u) := by
  apply Units.ext
  rw [coe_generalLinearGroup_map, Units.coe_map, Units.coe_map, Units.coe_map]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  exact (phi_map ι τ _).symm

theorem iterate_map_unitsMap_phi (ι : E →ₐ[F] Matrix (Fin 2) (Fin 2) F) (τ : M →ₐ[F] M)
    (u : (E ⊗[F] M)ˣ) (i : ℕ) :
    (⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) τ.toRingHom))^[i]
        (Units.map (phi ι).toMonoidHom u) =
      Units.map (phi ι).toMonoidHom
        ((⇑(Units.map (Algebra.TensorProduct.map (AlgHom.id F E) τ).toMonoidHom))^[i] u) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_unitsMap_phi]

theorem val_iterate_unitsMap (τ : M →ₐ[F] M) (u : (E ⊗[F] M)ˣ) (i : ℕ) :
    (((⇑(Units.map (Algebra.TensorProduct.map (AlgHom.id F E) τ).toMonoidHom))^[i] u : (E ⊗[F] M)ˣ) :
        E ⊗[F] M) =
      (⇑(Algebra.TensorProduct.map (AlgHom.id F E) τ))^[i] (u : E ⊗[F] M) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Units.coe_map, ih]
    rfl

theorem exists_prod_eq (ι : E →ₐ[F] Matrix (Fin 2) (Fin 2) F) (τ : M →ₐ[F] M) (n : ℕ)
    (γ : GL (Fin 2) F) (x : E) (hx : ι x = (γ : Matrix (Fin 2) (Fin 2) F))
    (e : (E ⊗[F] M)ˣ)
    (he : ((List.range n).map fun i =>
            (⇑(Algebra.TensorProduct.map (AlgHom.id F E) τ))^[i] (e : E ⊗[F] M)).prod = x ⊗ₜ[F] (1 : M)) :
    ∃ ε : GL (Fin 2) M,
      ((List.range n).map fun i =>
          (⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) τ.toRingHom))^[i] ε).prod =
        Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap F M) γ := by
  refine ⟨Units.map (phi ι).toMonoidHom e, ?_⟩
  have hfun : (fun i => (⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) τ.toRingHom))^[i]
        (Units.map (phi ι).toMonoidHom e)) =
      (Units.map (phi ι).toMonoidHom) ∘ (fun i =>
        (⇑(Units.map (Algebra.TensorProduct.map (AlgHom.id F E) τ).toMonoidHom))^[i] e) := by
    funext i
    exact iterate_map_unitsMap_phi ι τ e i
  rw [hfun, ← List.map_map, ← map_list_prod]
  apply Units.ext
  rw [Units.coe_map, coe_generalLinearGroup_map]
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← hx, ← phi_tmul_one ι x, ← he]
  congr 1
  rw [← Units.coeHom_apply, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => val_iterate_unitsMap τ e i

end TorusEmbed

namespace AutomorphicForm

namespace TorusDock

theorem exists_isNormOf
    (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L)
    (sA : (L ⊗[K] A) →ₐ[A] (L ⊗[K] A)) (hsA : ∀ t, sA t = sigmaTensor K L A σ t)
    (E : Type) [CommRing E] [Algebra A E] (ι : E →ₐ[A] Matrix (Fin 2) (Fin 2) A)
    (γ : GL (Fin 2) A) (x : E) (hx : ι x = (γ : Matrix (Fin 2) (Fin 2) A))
    (e : (E ⊗[A] (L ⊗[K] A))ˣ)
    (he : ((List.range (Module.finrank K L)).map fun i =>
            (⇑(Algebra.TensorProduct.map (AlgHom.id A E) sA))^[i] (e : E ⊗[A] (L ⊗[K] A))).prod =
          x ⊗ₜ[A] (1 : L ⊗[K] A)) :
    ∃ ε : GL (Fin 2) (L ⊗[K] A), IsNormOf K L A σ γ ε := by
  have hs : sA.toRingHom = sigmaTensor K L A σ := RingHom.ext hsA
  obtain ⟨ε, hε⟩ := TorusEmbed.exists_prod_eq (F := A) (M := L ⊗[K] A) ι sA (Module.finrank K L)
    γ x hx e he
  refine ⟨ε, 1, ?_⟩
  unfold IsNormConjugator
  rw [inv_one, one_mul, mul_one]

  change Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap A (L ⊗[K] A)) γ =
    ((List.range (Module.finrank K L)).map fun i =>
      (⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) (sigmaTensor K L A σ)))^[i] ε).prod
  rw [← hs]
  exact hε.symm

end TorusDock

end AutomorphicForm

namespace QuadModel

variable (K : Type) [Field K] (d : K)

noncomputable abbrev poly : K[X] := Polynomial.X ^ 2 - Polynomial.C d

theorem natDegree_poly : (poly K d).natDegree = 2 := Polynomial.natDegree_X_pow_sub_C

theorem poly_ne_zero : poly K d ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by norm_num) d

theorem irreducible_poly (hd : ¬ IsSquare d) : Irreducible (poly K d) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_poly]; decide
  · intro r hr
    apply hd
    refine ⟨r, ?_⟩
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] at hr
    rw [← hr, sq]

theorem not_isSquare_of_algebraMap {A : Type} [CommRing A] [Algebra K A]
    (h : ¬ IsSquare (algebraMap K A d)) : ¬ IsSquare d := by
  rintro ⟨a, rfl⟩
  exact h ⟨algebraMap K A a, by rw [map_mul]⟩

abbrev Kq : Type := AdjoinRoot (poly K d)

variable [Fact (Irreducible (poly K d))]

noncomputable example : Field (Kq K d) := inferInstance
noncomputable example : Algebra K (Kq K d) := inferInstance

scoped instance finiteDimensional : FiniteDimensional K (Kq K d) :=
  (AdjoinRoot.powerBasis (poly_ne_zero K d)).finite

theorem finrank_eq_two : Module.finrank K (Kq K d) = 2 := by
  rw [(AdjoinRoot.powerBasis (poly_ne_zero K d)).finrank, AdjoinRoot.powerBasis_dim, natDegree_poly]

scoped instance numberField [NumberField K] : NumberField (Kq K d) := NumberField.of_module_finite K (Kq K d)

theorem root_sq : (AdjoinRoot.root (poly K d)) ^ 2 = algebraMap K (Kq K d) d := by
  have h := AdjoinRoot.eval₂_root (poly K d)
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at h
  rw [h, AdjoinRoot.algebraMap_eq]

theorem adjoin_root_eq_top : Algebra.adjoin K {AdjoinRoot.root (poly K d)} = ⊤ :=
  AdjoinRoot.adjoinRoot_eq_top

end QuadModel
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.QuadModel"

section ESide
open Polynomial

namespace QuadAdjoinE1

variable {F : Type} [Field F]

theorem eval₂_X_sq_sub_C {S : Type} [CommRing S] (i : F →+* S) (a : F) (y : S) :
    (X ^ 2 - C a : F[X]).eval₂ i y = y ^ 2 - i a := by
  simp [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]

theorem eval₂_quadratic {S : Type} [CommRing S] (i : F →+* S) (t D : F) (y : S) :
    (X ^ 2 - C t * X + C D : F[X]).eval₂ i y = y ^ 2 - i t * y + i D := by
  simp [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]

private theorem _root_.InertProof.QuadAdjoinE1.root_sq (a : F) : AdjoinRoot.root (X ^ 2 - C a) ^ 2 = AdjoinRoot.of (X ^ 2 - C a) a := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C a : F[X])
  rwa [eval₂_X_sq_sub_C, sub_eq_zero] at h

p2m_export "InertProof.QuadAdjoinE1" "root_sq"

theorem root_quadratic (t D : F) :
    AdjoinRoot.root (X ^ 2 - C t * X + C D) ^ 2 -
        AdjoinRoot.of (X ^ 2 - C t * X + C D) t * AdjoinRoot.root (X ^ 2 - C t * X + C D) +
      AdjoinRoot.of (X ^ 2 - C t * X + C D) D = 0 := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C t * X + C D : F[X])
  rwa [eval₂_quadratic] at h

theorem two_mul_of_inv_two {f : F[X]} (h2 : (2 : F) ≠ 0) :
    (2 : AdjoinRoot f) * AdjoinRoot.of f (2 : F)⁻¹ = 1 := by
  rw [← map_ofNat (AdjoinRoot.of f) 2, ← map_mul, mul_inv_cancel₀ h2, map_one]

section
variable (t D : F)

local notation "p" => (X ^ 2 - C t * X + C D : F[X])
local notation "q" => (X ^ 2 - C (t ^ 2 - 4 * D) : F[X])

omit [Field F] in
theorem map_tsq_sub {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (a b : R) :
    g (a ^ 2 - 4 * b) = g a ^ 2 - 4 * g b := by
  rw [map_sub, map_mul, map_pow, map_ofNat]

theorem root_sq' :
    AdjoinRoot.root q ^ 2 = AdjoinRoot.of q t ^ 2 - 4 * AdjoinRoot.of q D := by
  rw [root_sq]
  exact map_tsq_sub _ t D

noncomputable def toSq (h2 : (2 : F) ≠ 0) : AdjoinRoot p →ₐ[F] AdjoinRoot q :=
  AdjoinRoot.liftAlgHom p (Algebra.ofId F _)
    (AdjoinRoot.of q (2 : F)⁻¹ * (AdjoinRoot.root q + AdjoinRoot.of q t)) (by
      rw [eval₂_quadratic]
      change _ - AdjoinRoot.of q t * _ + AdjoinRoot.of q D = 0
      linear_combination (AdjoinRoot.of q (2 : F)⁻¹) ^ 2 * root_sq' t D +
        (AdjoinRoot.of q (2 : F)⁻¹ * AdjoinRoot.root q * AdjoinRoot.of q t +
            AdjoinRoot.of q (2 : F)⁻¹ * AdjoinRoot.of q t ^ 2 -
          (2 * AdjoinRoot.of q (2 : F)⁻¹ + 1) * AdjoinRoot.of q D) * two_mul_of_inv_two (f := q) h2)

noncomputable def fromSq : AdjoinRoot q →ₐ[F] AdjoinRoot p :=
  AdjoinRoot.liftAlgHom q (Algebra.ofId F _)
    (2 * AdjoinRoot.root p - AdjoinRoot.of p t) (by
      rw [eval₂_X_sq_sub_C]
      change _ - AdjoinRoot.of p (t ^ 2 - 4 * D) = 0
      rw [map_tsq_sub]
      linear_combination (4 : AdjoinRoot p) * root_quadratic t D)

theorem toSq_root (h2 : (2 : F) ≠ 0) :
    toSq t D h2 (AdjoinRoot.root p) =
      AdjoinRoot.of q (2 : F)⁻¹ * (AdjoinRoot.root q + AdjoinRoot.of q t) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem toSq_of (h2 : (2 : F) ≠ 0) (a : F) : toSq t D h2 (AdjoinRoot.of p a) = AdjoinRoot.of q a := by
  rw [toSq, AdjoinRoot.liftAlgHom_of, Algebra.ofId_apply, AdjoinRoot.algebraMap_eq]

theorem fromSq_root : fromSq t D (AdjoinRoot.root q) = 2 * AdjoinRoot.root p - AdjoinRoot.of p t :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem fromSq_of (a : F) : fromSq t D (AdjoinRoot.of q a) = AdjoinRoot.of p a := by
  rw [fromSq, AdjoinRoot.liftAlgHom_of, Algebra.ofId_apply, AdjoinRoot.algebraMap_eq]

noncomputable def sqEquiv (h2 : (2 : F) ≠ 0) : AdjoinRoot p ≃ₐ[F] AdjoinRoot q :=
  AlgEquiv.ofAlgHom (toSq t D h2) (fromSq t D)
    (by
      apply AdjoinRoot.algHom_ext
      rw [AlgHom.comp_apply, fromSq_root, map_sub (toSq t D h2), map_mul (toSq t D h2), map_ofNat,
        toSq_root, toSq_of, AlgHom.id_apply]
      linear_combination (AdjoinRoot.root q + AdjoinRoot.of q t) * two_mul_of_inv_two (f := q) h2)
    (by
      apply AdjoinRoot.algHom_ext
      rw [AlgHom.comp_apply, toSq_root, map_mul (fromSq t D), map_add (fromSq t D), fromSq_root,
        fromSq_of, fromSq_of, AlgHom.id_apply]
      linear_combination AdjoinRoot.root p * two_mul_of_inv_two (f := p) h2)

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.QuadModel"

end QuadAdjoinE1
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.QuadModel"

theorem AdjoinRoot.exists_algEquiv_quadratic_completeSquare
    (F : Type) [Field F] (h2 : (2 : F) ≠ 0) (t D : F) :
    ∃ φ : AdjoinRoot (X ^ 2 - C t * X + C D) ≃ₐ[F] AdjoinRoot (X ^ 2 - C (t ^ 2 - 4 * D)),
      φ (AdjoinRoot.root (X ^ 2 - C t * X + C D)) =
        AdjoinRoot.of (X ^ 2 - C (t ^ 2 - 4 * D)) (2 : F)⁻¹ *
          (AdjoinRoot.root (X ^ 2 - C (t ^ 2 - 4 * D)) + AdjoinRoot.of (X ^ 2 - C (t ^ 2 - 4 * D)) t) :=
  ⟨QuadAdjoinE1.sqEquiv t D h2, QuadAdjoinE1.toSq_root t D h2⟩

namespace QuadAdjoinE2

variable {F : Type} [Field F]

theorem eval₂_X_sq_sub_C {S : Type} [CommRing S] (i : F →+* S) (a : F) (y : S) :
    (X ^ 2 - C a : F[X]).eval₂ i y = y ^ 2 - i a := by
  simp [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]

private theorem _root_.InertProof.QuadAdjoinE2.root_sq (a : F) : AdjoinRoot.root (X ^ 2 - C a) ^ 2 = AdjoinRoot.of (X ^ 2 - C a) a := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C a : F[X])
  rwa [eval₂_X_sq_sub_C, sub_eq_zero] at h

p2m_export "InertProof.QuadAdjoinE2" "root_sq"

noncomputable def rescale (d c : F) :
    AdjoinRoot (X ^ 2 - C (d * c ^ 2)) →ₐ[F] AdjoinRoot (X ^ 2 - C d) :=
  AdjoinRoot.liftAlgHom (X ^ 2 - C (d * c ^ 2)) (Algebra.ofId F _)
    (AdjoinRoot.of (X ^ 2 - C d) c * AdjoinRoot.root (X ^ 2 - C d)) (by
      rw [eval₂_X_sq_sub_C, mul_pow, root_sq]
      change _ - AdjoinRoot.of (X ^ 2 - C d) (d * c ^ 2) = 0
      rw [← map_pow, ← map_mul, ← map_sub, show c ^ 2 * d - d * c ^ 2 = 0 by ring, map_zero])

noncomputable def rescaleInv (d c : F) (hc : c ≠ 0) :
    AdjoinRoot (X ^ 2 - C d) →ₐ[F] AdjoinRoot (X ^ 2 - C (d * c ^ 2)) :=
  AdjoinRoot.liftAlgHom (X ^ 2 - C d) (Algebra.ofId F _)
    (AdjoinRoot.of (X ^ 2 - C (d * c ^ 2)) c⁻¹ * AdjoinRoot.root (X ^ 2 - C (d * c ^ 2))) (by
      rw [eval₂_X_sq_sub_C, mul_pow, root_sq]
      change _ - AdjoinRoot.of (X ^ 2 - C (d * c ^ 2)) d = 0
      rw [← map_pow, ← map_mul, ← map_sub, show c⁻¹ ^ 2 * (d * c ^ 2) - d = 0 by field_simp; ring,
        map_zero])

theorem rescale_root (d c : F) :
    rescale d c (AdjoinRoot.root (X ^ 2 - C (d * c ^ 2))) =
      AdjoinRoot.of (X ^ 2 - C d) c * AdjoinRoot.root (X ^ 2 - C d) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem rescale_of (d c a : F) :
    rescale d c (AdjoinRoot.of (X ^ 2 - C (d * c ^ 2)) a) = AdjoinRoot.of (X ^ 2 - C d) a := by
  rw [rescale, AdjoinRoot.liftAlgHom_of, Algebra.ofId_apply, AdjoinRoot.algebraMap_eq]

theorem rescaleInv_root (d c : F) (hc : c ≠ 0) :
    rescaleInv d c hc (AdjoinRoot.root (X ^ 2 - C d)) =
      AdjoinRoot.of (X ^ 2 - C (d * c ^ 2)) c⁻¹ * AdjoinRoot.root (X ^ 2 - C (d * c ^ 2)) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem rescaleInv_of (d c : F) (hc : c ≠ 0) (a : F) :
    rescaleInv d c hc (AdjoinRoot.of (X ^ 2 - C d) a) = AdjoinRoot.of (X ^ 2 - C (d * c ^ 2)) a := by
  rw [rescaleInv, AdjoinRoot.liftAlgHom_of, Algebra.ofId_apply, AdjoinRoot.algebraMap_eq]

noncomputable def rescaleEquiv (d c : F) (hc : c ≠ 0) :
    AdjoinRoot (X ^ 2 - C (d * c ^ 2)) ≃ₐ[F] AdjoinRoot (X ^ 2 - C d) :=
  AlgEquiv.ofAlgHom (rescale d c) (rescaleInv d c hc)
    (by
      apply AdjoinRoot.algHom_ext
      rw [AlgHom.comp_apply, rescaleInv_root, map_mul (rescale d c), rescale_root, rescale_of,
        AlgHom.id_apply, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul])
    (by
      apply AdjoinRoot.algHom_ext
      rw [AlgHom.comp_apply, rescale_root, map_mul (rescaleInv d c hc), rescaleInv_root, rescaleInv_of,
        AlgHom.id_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul])

end QuadAdjoinE2
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.QuadModel"

theorem AdjoinRoot.exists_algEquiv_X_sq_sub_C_mul_sq
    (F : Type) [Field F] (d c : F) (hc : c ≠ 0) :
    ∃ φ : AdjoinRoot (X ^ 2 - C (d * c ^ 2)) ≃ₐ[F] AdjoinRoot (X ^ 2 - C d),
      φ (AdjoinRoot.root (X ^ 2 - C (d * c ^ 2))) =
        AdjoinRoot.of (X ^ 2 - C d) c * AdjoinRoot.root (X ^ 2 - C d) :=
  ⟨QuadAdjoinE2.rescaleEquiv d c hc, QuadAdjoinE2.rescale_root d c⟩

namespace TorusTransportLeft

variable {F : Type} [CommRing F] {E₁ E₂ : Type} [CommRing E₁] [CommRing E₂] [Algebra F E₁] [Algebra F E₂]
  {M : Type} [CommRing M] [Algebra F M]

theorem congr_map (φ : E₁ ≃ₐ[F] E₂) (τ : M →ₐ[F] M) (z : E₂ ⊗[F] M) :
    Algebra.TensorProduct.congr φ.symm (AlgEquiv.refl : M ≃ₐ[F] M)
        (Algebra.TensorProduct.map (AlgHom.id F E₂) τ z) =
      Algebra.TensorProduct.map (AlgHom.id F E₁) τ
        (Algebra.TensorProduct.congr φ.symm (AlgEquiv.refl : M ≃ₐ[F] M) z) := by
  induction z with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a m => simp [Algebra.TensorProduct.congr_apply]

private theorem _root_.InertProof.TorusTransportLeft.exists_units (φ : E₁ ≃ₐ[F] E₂) (τ : M →ₐ[F] M) (n : ℕ) (x : E₁) (e : (E₂ ⊗[F] M)ˣ)
    (he : ((List.range n).map fun i =>
            (⇑(Algebra.TensorProduct.map (AlgHom.id F E₂) τ))^[i] (e : E₂ ⊗[F] M)).prod =
          φ x ⊗ₜ[F] (1 : M)) :
    ∃ e' : (E₁ ⊗[F] M)ˣ,
      ((List.range n).map fun i =>
          (⇑(Algebra.TensorProduct.map (AlgHom.id F E₁) τ))^[i] (e' : E₁ ⊗[F] M)).prod =
        x ⊗ₜ[F] (1 : M) := by
  have hsemi : Function.Semiconj (Algebra.TensorProduct.congr φ.symm (AlgEquiv.refl : M ≃ₐ[F] M))
      (Algebra.TensorProduct.map (AlgHom.id F E₂) τ) (Algebra.TensorProduct.map (AlgHom.id F E₁) τ) :=
    congr_map φ τ
  refine ⟨Units.map (Algebra.TensorProduct.congr φ.symm (AlgEquiv.refl : M ≃ₐ[F] M) :
      E₂ ⊗[F] M →* E₁ ⊗[F] M) e, ?_⟩
  have hfun : (fun i => (⇑(Algebra.TensorProduct.map (AlgHom.id F E₁) τ))^[i]
        ((Units.map (Algebra.TensorProduct.congr φ.symm (AlgEquiv.refl : M ≃ₐ[F] M) :
            E₂ ⊗[F] M →* E₁ ⊗[F] M) e : (E₁ ⊗[F] M)ˣ) : E₁ ⊗[F] M)) =
      (Algebra.TensorProduct.congr φ.symm (AlgEquiv.refl : M ≃ₐ[F] M)) ∘
        (fun i => (⇑(Algebra.TensorProduct.map (AlgHom.id F E₂) τ))^[i] (e : E₂ ⊗[F] M)) := by
    funext i
    rw [Units.coe_map, MonoidHom.coe_coe]
    exact (hsemi.iterate_right i (e : E₂ ⊗[F] M)).symm
  rw [hfun, ← List.map_map, ← map_list_prod, he]
  simp [Algebra.TensorProduct.congr_apply]

p2m_export "InertProof.TorusTransportLeft" "exists_units"
end TorusTransportLeft
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.QuadModel"

theorem Algebra.TensorProduct.exists_units_prod_map_iterate_eq_tmul_of_algEquiv_left
    (F : Type) [CommRing F] (E₁ E₂ : Type) [CommRing E₁] [CommRing E₂] [Algebra F E₁] [Algebra F E₂]
    (φ : E₁ ≃ₐ[F] E₂)
    (M : Type) [CommRing M] [Algebra F M] (τ : M →ₐ[F] M) (n : ℕ) (x : E₁)
    (e : (E₂ ⊗[F] M)ˣ)
    (he : ((List.range n).map fun i =>
            (⇑(Algebra.TensorProduct.map (AlgHom.id F E₂) τ))^[i] (e : E₂ ⊗[F] M)).prod =
          φ x ⊗ₜ[F] (1 : M)) :
    ∃ e' : (E₁ ⊗[F] M)ˣ,
      ((List.range n).map fun i =>
          (⇑(Algebra.TensorProduct.map (AlgHom.id F E₁) τ))^[i] (e' : E₁ ⊗[F] M)).prod =
        x ⊗ₜ[F] (1 : M) :=
  TorusTransportLeft.exists_units φ τ n x e he

end ESide
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.QuadModel"

theorem Algebra.TensorProduct.exists_unit_prod_iterate_map_eq_tmul_one_of_algEquiv_of_finrank_eq_two
    (F E M : Type*) [Field F] [Field E] [Field M] [Algebra F E] [Algebra F M]
    [FiniteDimensional F M] [IsGalois F M] (hM : Module.finrank F M = 2)
    (τ : M ≃ₐ[F] M) (hτ : ∀ ρ : M ≃ₐ[F] M, ρ ∈ Subgroup.zpowers τ)
    (φ : E ≃ₐ[F] M) (x : E) (hx : x ≠ 0) :
    ∃ e : (E ⊗[F] M)ˣ,
      ((List.range (Module.finrank F M)).map fun i =>
          (⇑(Algebra.TensorProduct.map (AlgHom.id F E) (τ : M →ₐ[F] M)))^[i] (e : E ⊗[F] M)).prod
        = x ⊗ₜ[F] (1 : M) := by
  classical

  have hcardM : Nat.card (M ≃ₐ[F] M) = 2 := (IsGalois.card_aut_eq_finrank F M).trans hM
  have htop : Subgroup.zpowers τ = ⊤ := (Subgroup.eq_top_iff' _).mpr hτ
  have horder : orderOf τ = 2 := by
    rw [← Nat.card_zpowers, htop, Subgroup.card_top, hcardM]
  have hττ : τ * τ = 1 := by rw [← pow_two, ← horder, pow_orderOf_eq_one]
  have hτ1 : τ ≠ 1 := by
    intro h; rw [h, orderOf_one] at horder; exact absurd horder (by norm_num)
  obtain ⟨α, hα⟩ : ∃ α : M, τ α ≠ α := by
    by_contra h
    push Not at h
    exact hτ1 (AlgEquiv.ext h)
  set α' := τ α with hα'
  have hτα' : τ α' = α := by
    rw [hα', ← AlgEquiv.mul_apply, hττ, AlgEquiv.one_apply]
  have hsub : α - α' ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)

  have hfix : ∀ y : M, τ y = y → y ∈ Set.range (algebraMap F M) := by
    intro y hy
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro f
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp ((mem_powers_iff_mem_zpowers).mpr (hτ f))
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hy, ih]
  obtain ⟨tF, htF⟩ : α + α' ∈ Set.range (algebraMap F M) :=
    hfix _ (by rw [map_add, hτα', hα', add_comm])
  obtain ⟨dF, hdF⟩ : α * α' ∈ Set.range (algebraMap F M) :=
    hfix _ (by rw [map_mul, hτα', hα', mul_comm])

  set β : E := φ.symm α with hβ
  have hβroot : β * β - algebraMap F E tF * β + algebraMap F E dF = 0 := by
    apply φ.injective
    rw [map_add, map_sub, map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hβ,
      AlgEquiv.apply_symm_apply, htF, hdF, map_zero]
    ring

  obtain ⟨TE, hTE⟩ : ∃ TE : E, TE = algebraMap F E tF := ⟨_, rfl⟩
  obtain ⟨DE, hDE⟩ : ∃ DE : E, DE = algebraMap F E dF := ⟨_, rfl⟩
  rw [← hTE, ← hDE] at hβroot
  obtain ⟨u, hu⟩ : ∃ u : E ⊗[F] M, u = β ⊗ₜ[F] (1 : M) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : E ⊗[F] M, v = (1 : E) ⊗ₜ[F] α := ⟨_, rfl⟩
  obtain ⟨v', hv'⟩ : ∃ v' : E ⊗[F] M, v' = (1 : E) ⊗ₜ[F] α' := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : E ⊗[F] M, w = (1 : E) ⊗ₜ[F] (α - α')⁻¹ := ⟨_, rfl⟩
  have h2 : (v - v') * w = 1 := by
    rw [hv, hv', hw, ← TensorProduct.tmul_sub, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_inv_cancel₀ hsub, Algebra.TensorProduct.one_def]
  have hvv'add : v + v' = TE ⊗ₜ[F] (1 : M) := by
    rw [hv, hv', ← TensorProduct.tmul_add, ← htF, hTE, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hvv'mul : v * v' = DE ⊗ₜ[F] (1 : M) := by
    rw [hv, hv', Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hdF, hDE,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have huroot : u * u - TE ⊗ₜ[F] (1 : M) * u + DE ⊗ₜ[F] (1 : M) = 0 := by
    rw [hu, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      ← TensorProduct.sub_tmul, ← TensorProduct.add_tmul, hβroot, TensorProduct.zero_tmul]
  have h1 : (u - v') * (u - v) = 0 := by
    have : (u - v') * (u - v) = u * u - (v + v') * u + v * v' := by ring
    rw [this, hvv'add, hvv'mul, huroot]
  obtain ⟨ε, hε⟩ : ∃ ε : E ⊗[F] M, ε = (u - v') * w := ⟨_, rfl⟩
  have hεε : ε * ε = ε := by
    rw [hε]; linear_combination w ^ 2 * h1 + ((u - v') * w) * h2

  obtain ⟨σ, hσ⟩ : ∃ σ : E ⊗[F] M →ₐ[F] E ⊗[F] M,
      σ = Algebra.TensorProduct.map (AlgHom.id F E) (τ : M →ₐ[F] M) := ⟨_, rfl⟩
  have hσu : σ u = u := by
    rw [hσ, hu, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  have hσv' : σ v' = v := by
    rw [hσ, hv', hv, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_algHom, hτα']
  have hσw : σ w = -w := by
    rw [hσ, hw, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_algHom, map_inv₀,
      map_sub, hτα', ← hα', ← neg_sub, inv_neg, TensorProduct.tmul_neg]
  have hσε : σ ε = 1 - ε := by
    rw [hε, map_mul, map_sub, hσu, hσv', hσw]
    linear_combination h2

  obtain ⟨c, hc⟩ : ∃ c : E ⊗[F] M, c = x ⊗ₜ[F] (1 : M) := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c' : E ⊗[F] M, c' = x⁻¹ ⊗ₜ[F] (1 : M) := ⟨_, rfl⟩
  have hcc' : c * c' = 1 := by
    rw [hc, hc', Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hx, one_mul,
      Algebra.TensorProduct.one_def]
  have hσc : σ c = c := by
    rw [hσ, hc, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  obtain ⟨e, he⟩ : ∃ e : E ⊗[F] M, e = c * ε + (1 - ε) := ⟨_, rfl⟩
  obtain ⟨e', he'⟩ : ∃ e' : E ⊗[F] M, e' = c' * ε + (1 - ε) := ⟨_, rfl⟩
  have hee' : e * e' = 1 := by
    rw [he, he']; linear_combination ε * hcc' + (c * c' - c - c' + 1) * hεε
  refine ⟨Units.mkOfMulEqOne e e' hee', ?_⟩
  rw [Units.val_mkOfMulEqOne, hM, ← hσ, ← hc]
  show e * (σ e * 1) = c
  rw [mul_one, he, map_add, map_mul, map_sub, map_one, hσc, hσε]
  linear_combination (-c ^ 2 + 2 * c - 1) * hεε

namespace Compositum

variable (K L : Type) [Field K] [Field L] [Algebra K L] (d : K)
  [Fact (Irreducible (QuadModel.poly K d))] [Fact (Irreducible (QuadModel.poly L (algebraMap K L d)))]

theorem eval₂_poly_root :
    Polynomial.eval₂ (↑(Algebra.ofId K (QuadModel.Kq L (algebraMap K L d))))
      (AdjoinRoot.root (QuadModel.poly L (algebraMap K L d))) (QuadModel.poly K d) = 0 := by
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, QuadModel.root_sq, sub_eq_zero]
  change algebraMap L _ (algebraMap K L d) = algebraMap K _ d
  exact (IsScalarTower.algebraMap_apply K L _ d).symm

noncomputable def toM : QuadModel.Kq K d →ₐ[K] QuadModel.Kq L (algebraMap K L d) :=
  AdjoinRoot.liftAlgHom (QuadModel.poly K d) (Algebra.ofId K _) (AdjoinRoot.root _)
    (eval₂_poly_root K L d)

theorem toM_root : toM K L d (AdjoinRoot.root _) = AdjoinRoot.root _ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

noncomputable scoped instance algebra : Algebra (QuadModel.Kq K d) (QuadModel.Kq L (algebraMap K L d)) :=
  (toM K L d).toRingHom.toAlgebra

private theorem _root_.InertProof.Compositum.algebraMap_apply (y : QuadModel.Kq K d) :
    algebraMap (QuadModel.Kq K d) (QuadModel.Kq L (algebraMap K L d)) y = toM K L d y := rfl

p2m_export "InertProof.Compositum" "algebraMap_apply"
scoped instance isScalarTower : IsScalarTower K (QuadModel.Kq K d) (QuadModel.Kq L (algebraMap K L d)) :=
  IsScalarTower.of_algebraMap_eq fun k => by
    rw [algebraMap_apply]; exact ((toM K L d).commutes k).symm

private theorem _root_.InertProof.Compositum.finrank_eq :
    Module.finrank (QuadModel.Kq K d) (QuadModel.Kq L (algebraMap K L d)) = Module.finrank K L := by
  have h1 := Module.finrank_mul_finrank K L (QuadModel.Kq L (algebraMap K L d))
  have h2 := Module.finrank_mul_finrank K (QuadModel.Kq K d) (QuadModel.Kq L (algebraMap K L d))
  rw [QuadModel.finrank_eq_two] at h1 h2
  omega

p2m_export "InertProof.Compositum" "finrank_eq"

theorem mem_adjoin (y : QuadModel.Kq L (algebraMap K L d)) :
    y ∈ Algebra.adjoin (QuadModel.Kq K d)
      (Set.range (algebraMap L (QuadModel.Kq L (algebraMap K L d)))) := by
  let S := Algebra.adjoin (QuadModel.Kq K d)
      (Set.range (algebraMap L (QuadModel.Kq L (algebraMap K L d))))
  let T : Subalgebra L (QuadModel.Kq L (algebraMap K L d)) :=
    { S.toSubsemiring with
      algebraMap_mem' := fun l => Algebra.subset_adjoin ⟨l, rfl⟩ }
  have hroot : AdjoinRoot.root (QuadModel.poly L (algebraMap K L d)) ∈ T := by
    have h := S.algebraMap_mem (AdjoinRoot.root (QuadModel.poly K d))
    rw [algebraMap_apply, toM_root] at h
    exact h
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← QuadModel.adjoin_root_eq_top L (algebraMap K L d), Algebra.adjoin_le_iff,
      Set.singleton_subset_iff]
    exact hroot
  have hy : y ∈ T := by rw [hT]; exact Algebra.mem_top
  exact hy

end Compositum
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.QuadModel P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.Compositum"

namespace SplitCorner

open scoped IntermediateField in
theorem two_dvd_finrank (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (d : K) (hd : ¬ IsSquare d) (s : L) (hs : algebraMap K L d = s * s) : 2 ∣ Module.finrank K L := by
  have hint : IsIntegral K s := .of_finite K s
  have hmin : QuadModel.poly K d = minpoly K s :=
    minpoly.eq_of_irreducible_of_monic (QuadModel.irreducible_poly K d hd)
      (by rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hs, sq, sub_self])
      (Polynomial.monic_X_pow_sub_C d two_ne_zero)
  have h1 : Module.finrank K K⟮s⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank hint, ← hmin, QuadModel.natDegree_poly]
  have h2 := Module.finrank_mul_finrank K K⟮s⟯ L
  exact ⟨_, by rw [← h2, h1]⟩

end SplitCorner
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.QuadModel P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.Compositum"

namespace InertAssembly

noncomputable scoped instance finite_valuedResidueField
    (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    Finite (Valued.ResidueField (w.adicCompletion L)) :=
  inferInstanceAs (Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers L)))

section Aut

variable (F M : Type) [Field F] [Field M] [Algebra F M] [FiniteDimensional F M]

theorem natCard_algEquiv_dvd_finrank : Nat.card (M ≃ₐ[F] M) ∣ Module.finrank F M := by
  have h1 := IntermediateField.finrank_fixedField_eq_card (⊤ : Subgroup (M ≃ₐ[F] M))
  have h2 := Module.finrank_mul_finrank F
    (IntermediateField.fixedField (⊤ : Subgroup (M ≃ₐ[F] M))) M
  rw [h1, Subgroup.card_top] at h2
  exact ⟨_, h2.symm.trans (mul_comm _ _)⟩

theorem natCard_algEquiv_eq_finrank_of_orderOf_eq (θ : M ≃ₐ[F] M)
    (hθ : orderOf θ = Module.finrank F M) : Nat.card (M ≃ₐ[F] M) = Module.finrank F M := by
  apply Nat.dvd_antisymm (natCard_algEquiv_dvd_finrank F M)
  rw [← hθ]
  exact orderOf_dvd_natCard θ

theorem isGalois_of_orderOf_eq (θ : M ≃ₐ[F] M) (hθ : orderOf θ = Module.finrank F M) :
    IsGalois F M :=
  IsGalois.of_card_aut_eq_finrank F M (natCard_algEquiv_eq_finrank_of_orderOf_eq F M θ hθ)

theorem mem_zpowers_of_orderOf_eq (θ : M ≃ₐ[F] M) (hθ : orderOf θ = Module.finrank F M)
    (ρ : M ≃ₐ[F] M) : ρ ∈ Subgroup.zpowers θ := by
  have : Subgroup.zpowers θ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hθ, natCard_algEquiv_eq_finrank_of_orderOf_eq F M θ hθ]
  rw [this]; exact Subgroup.mem_top ρ

theorem isGalois_of_prime_of_ne_one (hdeg : (Module.finrank F M).Prime) (σ : M ≃ₐ[F] M) (hσ : σ ≠ 1) :
    IsGalois F M := by
  apply IsGalois.of_card_aut_eq_finrank
  rcases (Nat.dvd_prime hdeg).mp (natCard_algEquiv_dvd_finrank F M) with h1 | hn
  · exfalso
    apply hσ
    haveI : Subsingleton (M ≃ₐ[F] M) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Subsingleton.elim _ _
  · exact hn

end Aut
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.QuadModel P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.Compositum"

section Local

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

theorem valued_algebraMap_adicCompletion (x : v.adicCompletion K) :
    Valued.v (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x) =
      Valued.v x ^ Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal :=
  HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L w x

theorem exists_valued_eq_ofAdd (k : ℤ) : ∃ b : v.adicCompletion K,
    Valued.v b = ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.adicCompletion.exists_uniformizer K v
  have hπ0 : (π : v.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  refine ⟨(π : v.adicCompletion K) ^ (-k), ?_⟩
  rw [map_zpow₀, hπ, ← WithZero.coe_zpow, ← ofAdd_zsmul]
  congr 2
  ring

theorem hunr (hv : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (k : ℤ) : ∃ b : v.adicCompletion K,
    Valued.v (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) b) =
      ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  obtain ⟨b, hb⟩ := exists_valued_eq_ofAdd K v k
  exact ⟨b, by rw [valued_algebraMap_adicCompletion, hv, pow_one, hb]⟩

theorem nonempty_extension (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] :
    Nonempty (v.Extension (𝓞 K')) := by
  haveI := v.isMaximal
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K') v.asIdeal
  have hne : Q ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hQover.over, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨⟨Q, hQmax.isPrime, hne⟩, HeightOneSpectrum.ext hQover.over.symm⟩⟩

noncomputable def sA (σ : L ≃ₐ[K] L) :
    (L ⊗[K] v.adicCompletion K) →ₐ[v.adicCompletion K] (L ⊗[K] v.adicCompletion K) :=
  { AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ with
    commutes' := by
      intro a
      show AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ (1 ⊗ₜ a) = 1 ⊗ₜ a
      simp [AutomorphicForm.sigmaTensor] }

theorem sA_apply (σ : L ≃ₐ[K] L) (t : L ⊗[K] v.adicCompletion K) :
    sA K L v σ t = AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ t := rfl

end Local
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.QuadModel P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.Compositum"

section Quadratic

variable (F : Type) [Field F] (γ : Matrix (Fin 2) (Fin 2) F) [Fact (Irreducible (Matrix.charpoly γ))]

theorem charpoly_ne_zero : Matrix.charpoly γ ≠ 0 := (Fact.out : Irreducible (Matrix.charpoly γ)).ne_zero

theorem finrank_adjoinRoot_charpoly : Module.finrank F (AdjoinRoot (Matrix.charpoly γ)) = 2 := by
  rw [(AdjoinRoot.powerBasis (charpoly_ne_zero F γ)).finrank, AdjoinRoot.powerBasis_dim,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

scoped instance : FiniteDimensional F (AdjoinRoot (Matrix.charpoly γ)) :=
  (AdjoinRoot.powerBasis (charpoly_ne_zero F γ)).finite

noncomputable def iota : AdjoinRoot (Matrix.charpoly γ) →ₐ[F] Matrix (Fin 2) (Fin 2) F :=
  Ideal.Quotient.liftₐ (Ideal.span {Matrix.charpoly γ}) (Polynomial.aeval γ) (by
    intro a ha
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, Matrix.aeval_self_charpoly, mul_zero])

theorem iota_root : iota F γ (AdjoinRoot.root (Matrix.charpoly γ)) = γ := by
  change Ideal.Quotient.liftₐ (Ideal.span {Matrix.charpoly γ}) (Polynomial.aeval γ) _
      (Ideal.Quotient.mk _ Polynomial.X) = γ
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  exact Polynomial.aeval_X γ

theorem root_ne_zero (hγ : γ ≠ 0) : AdjoinRoot.root (Matrix.charpoly γ) ≠ 0 := by
  intro h
  apply hγ
  rw [← iota_root F γ, h, map_zero]

end Quadratic
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.QuadModel P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.Compositum"

end InertAssembly
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.QuadModel P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.Compositum P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.InertAssembly"

end InertProof
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.QuadModel P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.Compositum P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof.InertAssembly P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.InertProof"

open AutomorphicForm InertProof.InertAssembly in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hA : IsField (L ⊗[K] v.adicCompletion K))
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : ¬ IsSquare (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
    (hdet : ∃ k : ℤ, Valued.v (Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
      ((Multiplicative.ofAdd ((Module.finrank K L : ℤ) * k) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ∃ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K), IsNormOf K L (v.adicCompletion K) σ γ δ := by
  obtain ⟨w, e, θ, hwuniq, hσθ, heL, hord, hθfix, hfin, -⟩ :=
    AutomorphicForm.exists_extension_algEquiv_adicCompletion_of_isField_tensor K L hdeg σ hσ v hv hA

  haveI : Fact (Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) :=
    ⟨InertProof.Matrix.irreducible_charpoly_of_not_isSquare_trace_sq_sub_four_mul_det _ _ hγ⟩
  have hE := finrank_adjoinRoot_charpoly (v.adicCompletion K) (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
  have hx0 : AdjoinRoot.root (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ≠ 0 :=
    root_ne_zero _ _ (fun h => by
      have := γ.isUnit
      rw [show (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = 0 from h] at this
      exact not_isUnit_zero this)
  have hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime := hfin ▸ hdeg

  have hdisc0 : Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ≠ 0 := fun h =>
    hγ ⟨0, by rw [h, mul_zero]⟩
  obtain ⟨d', c, hc, hd'⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_algebraMap_eq_mul_sq_adicCompletion K v _ hdisc0
  have hd'sq : ¬ IsSquare (algebraMap K (v.adicCompletion K) d') := by
    rintro ⟨a, ha⟩
    apply hγ
    refine ⟨a / c, ?_⟩
    have : Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
        4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        algebraMap K (v.adicCompletion K) d' / c ^ 2 := by
      rw [hd', mul_div_cancel_right₀ _ (pow_ne_zero 2 hc)]
    rw [this, ha]
    field_simp

  haveI : Fact (Irreducible (InertProof.QuadModel.poly K d')) :=
    ⟨InertProof.QuadModel.irreducible_poly K d' (InertProof.QuadModel.not_isSquare_of_algebraMap K d' hd'sq)⟩
  obtain ⟨h𝔳uniq, h𝔳iso⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_unique_extension_and_algEquiv_adjoinRoot_of_not_isSquare
      K (InertProof.QuadModel.Kq K d') (InertProof.QuadModel.finrank_eq_two K d') d' (AdjoinRoot.root _)
      (InertProof.QuadModel.root_sq K d') (InertProof.QuadModel.adjoin_root_eq_top K d') v hd'sq
  obtain ⟨𝔳⟩ := nonempty_extension K v (InertProof.QuadModel.Kq K d')
  obtain ⟨ψ⟩ := h𝔳iso 𝔳

  have h2 : (2 : v.adicCompletion K) ≠ 0 := by
    have := (map_ne_zero (algebraMap K (v.adicCompletion K))).mpr (two_ne_zero : (2 : K) ≠ 0)
    rwa [map_ofNat] at this
  obtain ⟨φ₁, -⟩ := InertProof.AdjoinRoot.exists_algEquiv_quadratic_completeSquare (v.adicCompletion K) h2
    (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
  obtain ⟨φ₂, -⟩ := InertProof.AdjoinRoot.exists_algEquiv_X_sq_sub_C_mul_sq (v.adicCompletion K)
    (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) c hc
  let Φ : AdjoinRoot (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ≃ₐ[v.adicCompletion K]
      𝔳.1.adicCompletion (InertProof.QuadModel.Kq K d') :=
    (AdjoinRoot.algEquivOfEq (v.adicCompletion K) _ _ (Matrix.charpoly_fin_two _)).trans
      (φ₁.trans (φ₂.symm.trans
        ((AdjoinRoot.algEquivOfEq (v.adicCompletion K) _ _ (by rw [hd'])).trans ψ.symm)))
  have h2K' : Module.finrank (v.adicCompletion K) (𝔳.1.adicCompletion (InertProof.QuadModel.Kq K d')) = 2 := by
    rw [← Φ.toLinearEquiv.finrank_eq]; exact hE

  have hx'0 : Φ (AdjoinRoot.root _) ≠ 0 := by
    intro h; exact hx0 (Φ.injective (by rw [h, map_zero]))
  have hdiv : ∃ k : ℤ, Valued.v (Algebra.norm (v.adicCompletion K) (Φ (AdjoinRoot.root _))) =
      ((Multiplicative.ofAdd ((Module.finrank K L : ℤ) * k) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    obtain ⟨k, hk⟩ := hdet
    refine ⟨k, ?_⟩
    rw [Algebra.norm_eq_of_algEquiv, InertProof.AdjoinRoot.norm_root_charpoly_eq_det]
    exact hk

  have hθσ : ∀ y : L, θ (algebraMap L (w.1.adicCompletion L) y) =
      algebraMap L (w.1.adicCompletion L) (σ y) := by
    intro y
    rw [← heL y, ← hσθ,
      show sigmaTensor K L (v.adicCompletion K) σ (y ⊗ₜ[K] (1 : v.adicCompletion K)) = σ y ⊗ₜ 1 by
        simp [sigmaTensor], heL]
  haveI : IsGalois K L := isGalois_of_prime_of_ne_one K L hdeg σ hσ

  have tail : ∀ e₁ : (AdjoinRoot (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⊗[v.adicCompletion K]
        w.1.adicCompletion L)ˣ,
      ((List.range (Module.finrank K L)).map fun i =>
        (⇑(Algebra.TensorProduct.map
          (AlgHom.id (v.adicCompletion K) (AdjoinRoot (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))))
          (θ : w.1.adicCompletion L →ₐ[v.adicCompletion K] w.1.adicCompletion L)))^[i]
        (e₁ : AdjoinRoot (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⊗[v.adicCompletion K]
          w.1.adicCompletion L)).prod =
        AdjoinRoot.root (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⊗ₜ[v.adicCompletion K]
          (1 : w.1.adicCompletion L) →
      ∃ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K), IsNormOf K L (v.adicCompletion K) σ γ δ := by
    intro e₁ he₁
    have hφ : ∀ m, e.symm ((θ : w.1.adicCompletion L →ₐ[v.adicCompletion K] w.1.adicCompletion L) m) =
        sA K L v σ (e.symm m) := by
      intro m
      apply e.injective
      rw [AlgEquiv.apply_symm_apply, sA_apply, hσθ, AlgEquiv.apply_symm_apply, AlgEquiv.coe_algHom]
    obtain ⟨e', he'⟩ :=
      InertProof.Algebra.TensorProduct.exists_units_prod_map_iterate_eq_tmul_of_algEquiv (v.adicCompletion K)
        (AdjoinRoot (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
        (L ⊗[K] v.adicCompletion K) (w.1.adicCompletion L) (sA K L v σ)
        (θ : w.1.adicCompletion L →ₐ[v.adicCompletion K] w.1.adicCompletion L) e.symm hφ
        (Module.finrank K L) _ e₁ he₁
    exact InertProof.AutomorphicForm.TorusDock.exists_isNormOf K L (v.adicCompletion K) σ (sA K L v σ) (sA_apply K L v σ)
      _ (iota _ _) γ _ (iota_root _ _) e' he'
  by_cases hsqL : IsSquare (algebraMap K L d')
  ·

    obtain ⟨s, hs⟩ := hsqL
    haveI : IsGalois (v.adicCompletion K) (w.1.adicCompletion L) :=
      isGalois_of_orderOf_eq _ _ θ (hord.trans hfin.symm)
    have hn2 : Module.finrank K L = 2 := by
      rcases (Nat.dvd_prime hdeg).mp (InertProof.SplitCorner.two_dvd_finrank K L d'
        (InertProof.QuadModel.not_isSquare_of_algebraMap K d' hd'sq) s hs) with h | h
      · norm_num at h
      · exact h.symm

    have key : algebraMap L (w.1.adicCompletion L) (algebraMap K L d') =
        algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (algebraMap K (v.adicCompletion K) d') := by
      rw [← heL, Algebra.algebraMap_eq_smul_one d', TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
        ← e.commutes]
      rfl
    have hc' : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) c ≠ 0 := (map_ne_zero _).mpr hc
    obtain ⟨δ, hδ⟩ : ∃ δ : w.1.adicCompletion L, δ ^ 2 =
        algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ^ 2 -
          4 * algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) := by
      refine ⟨algebraMap L (w.1.adicCompletion L) s / algebraMap (v.adicCompletion K) (w.1.adicCompletion L) c, ?_⟩
      have hmap : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (algebraMap K (v.adicCompletion K) d') =
          (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ^ 2 -
            4 * algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) *
          algebraMap (v.adicCompletion K) (w.1.adicCompletion L) c ^ 2 := by
        rw [hd', map_mul, map_pow, map_sub, map_pow, map_mul, map_ofNat]
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hc'), ← hmap, ← key, hs, map_mul, sq]
    obtain ⟨i2, hi2⟩ : ∃ i2 : w.1.adicCompletion L, 2 * i2 = 1 :=
      ⟨algebraMap (v.adicCompletion K) (w.1.adicCompletion L) 2⁻¹, by
        rw [← map_ofNat (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)) 2, ← map_mul,
          mul_inv_cancel₀ h2, map_one]⟩
    have hr : Polynomial.eval₂ (↑(Algebra.ofId (v.adicCompletion K) (w.1.adicCompletion L)))
        (i2 * (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) + δ))
        (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 0 := by
      rw [Matrix.charpoly_fin_two]
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      change (i2 * (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) + δ)) ^ 2 -
          algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) *
            (i2 * (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) + δ)) +
          algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 0
      linear_combination i2 ^ 2 * hδ +
        (i2 * (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ^ 2 +
          algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) * δ -
          2 * algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) -
          algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) * hi2
    let ιE : AdjoinRoot (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →ₐ[v.adicCompletion K]
        w.1.adicCompletion L :=
      AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) _ hr
    have hιinj : Function.Injective ιE := fun a b h => ιE.toRingHom.injective h
    have hιsurj : Function.Surjective ιE :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := ιE.toLinearMap)
        (by rw [hE, hfin, hn2])).mp hιinj
    obtain ⟨e₁, he₁⟩ :=
      InertProof.Algebra.TensorProduct.exists_unit_prod_iterate_map_eq_tmul_one_of_algEquiv_of_finrank_eq_two
        (v.adicCompletion K) (AdjoinRoot (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
        (w.1.adicCompletion L) (by rw [hfin, hn2]) θ
        (mem_zpowers_of_orderOf_eq _ _ θ (hord.trans hfin.symm)) (AlgEquiv.ofBijective ιE ⟨hιinj, hιsurj⟩)
        (AdjoinRoot.root _) hx0
    rw [hfin] at he₁
    exact tail e₁ he₁
  ·
    haveI : Fact (Irreducible (InertProof.QuadModel.poly L (algebraMap K L d'))) :=
      ⟨InertProof.QuadModel.irreducible_poly L _ hsqL⟩
    obtain ⟨e₀, he₀⟩ :=
      IsDedekindDomain.HeightOneSpectrum.exists_units_prod_tensor_map_iterate_eq_tmul_one_of_finrank_dvd_valuation_norm
        K L (InertProof.QuadModel.Kq K d') (InertProof.QuadModel.Kq L (algebraMap K L d'))
        (InertProof.Compositum.finrank_eq K L d') (InertProof.Compositum.mem_adjoin K L d')
        hdeg (InertProof.QuadModel.finrank_eq_two K d') v hv w hwuniq 𝔳 (fun 𝔳' => h𝔳uniq 𝔳' 𝔳)
        θ hord hθfix hfin σ hσ hθσ _ hx'0 hdiv
    obtain ⟨e₁, he₁⟩ :=
      InertProof.Algebra.TensorProduct.exists_units_prod_map_iterate_eq_tmul_of_algEquiv_left (v.adicCompletion K)
        _ _ Φ (w.1.adicCompletion L)
        (θ : w.1.adicCompletion L →ₐ[v.adicCompletion K] w.1.adicCompletion L) _ _ e₀ he₀
    exact tail e₁ he₁

end S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd
end P2MW
export P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd (solution)
