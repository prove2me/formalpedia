-- Prove2me | solution 1 for AutomorphicForm.finite_sep_exists_apply_inv_mul_globalPoints_mul_sigmaAdelicAct_ne_zero_of_diagonal_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8f7b95c6-e55c-5002-8aeb-dde98064ce01

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_TwistedNormClasses
import Theorems.Thm_LT_TwistedNorm_setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finite_sep_exists_apply_inv_mul_globalPoints_mul_sigmaAdelicAct_ne_zero_of_diagonal_of_hasCompactSupport
p2m_attr_erase "instance" "NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion"

set_option autoImplicit false

noncomputable section

namespace R1DiagFin

open LT.TwistedNorm

section GroupLemmas

variable {G : Type*} [Group G]

theorem sigmaPartialNorm_mul_of_central (σ : G →* G) (a c : G) (hc : ∀ g : G, c * g = g * c) (r : ℕ) :
    sigmaPartialNorm σ (a * c) r = sigmaPartialNorm σ a r * sigmaPartialNorm σ c r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sigmaPartialNorm_succ', sigmaPartialNorm_succ', sigmaPartialNorm_succ', ih, map_mul,
        mul_assoc a c, ← mul_assoc c, hc (σ _)]
      simp only [mul_assoc]

theorem continuous_sigmaPartialNorm [TopologicalSpace G] [ContinuousMul G] (σ : G →* G)
    (hσ : Continuous σ) (r : ℕ) : Continuous fun x => sigmaPartialNorm σ x r := by
  induction r with
  | zero =>
      simp only [sigmaPartialNorm_zero]
      exact continuous_const
  | succ r ih =>
      simp only [sigmaPartialNorm_succ']
      exact continuous_id.mul (hσ.comp ih)

end GroupLemmas

section Diagonal

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

abbrev σG (σ : L ≃ₐ[F] L) : GL (Fin 2) L →* GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.map (σ : L →+* L)

theorem eq_diagonal_of_offdiag (A : Matrix (Fin 2) (Fin 2) L) (h10 : A 1 0 = 0) (h01 : A 0 1 = 0) :
    A = Matrix.diagonal fun i => A i i := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h01]

theorem val_sigmaPartialNorm_diagonal (σ : L ≃ₐ[F] L) (t : GL (Fin 2) L)
    (h10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) (r : ℕ) :
    ((sigmaPartialNorm (σG σ) t r : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      Matrix.diagonal fun i => ∏ k ∈ Finset.range r, (σ ^ k) ((t : Matrix (Fin 2) (Fin 2) L) i i) := by
  induction r with
  | zero =>
      simp only [sigmaPartialNorm_zero, Units.val_one, Finset.range_zero, Finset.prod_empty]
      exact Matrix.diagonal_one.symm
  | succ r ih =>
      have ht : (t : Matrix (Fin 2) (Fin 2) L) = Matrix.diagonal fun i => (t : Matrix (Fin 2) (Fin 2) L) i i :=
        eq_diagonal_of_offdiag _ h10 h01
      rw [sigmaPartialNorm_succ', Units.val_mul]
      conv_lhs => rw [ht]
      rw [coe_generalLinearGroup_map, ih, Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rw [map_prod, Finset.prod_range_succ', pow_zero, AlgEquiv.one_apply,
        mul_comm ((t : Matrix (Fin 2) (Fin 2) L) i i)]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [pow_succ', AlgEquiv.mul_apply]
      rfl

variable [FiniteDimensional F L] [IsGalois F L]

theorem prod_range_pow_apply_eq_algebraMap_norm {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (a : L) :
    ∏ k ∈ Finset.range (Module.finrank F L), (σ ^ k) a = algebraMap F L (Algebra.norm F a) := by
  rw [Algebra.norm_eq_prod_automorphisms, prod_algEquiv_eq_prod_range_of_generator hgen]

theorem val_sigmaNormPow_diagonal {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (t : GL (Fin 2) L)
    (h10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) :
    ((sigmaNormPow (σG σ) (Module.finrank F L) t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      Matrix.diagonal fun i => algebraMap F L (Algebra.norm F ((t : Matrix (Fin 2) (Fin 2) L) i i)) := by
  rw [sigmaNormPow_def, val_sigmaPartialNorm_diagonal σ t h10 h01]
  congr 1
  funext i
  exact prod_range_pow_apply_eq_algebraMap_norm hgen _

theorem trace_sigmaNormPow_diagonal {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (t : GL (Fin 2) L)
    (h10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) :
    Matrix.trace ((sigmaNormPow (σG σ) (Module.finrank F L) t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      algebraMap F L (Algebra.norm F ((t : Matrix (Fin 2) (Fin 2) L) 0 0) +
        Algebra.norm F ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) := by
  rw [val_sigmaNormPow_diagonal hgen t h10 h01, Matrix.trace_diagonal, Fin.sum_univ_two, map_add]

theorem det_sigmaNormPow_diagonal {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (t : GL (Fin 2) L)
    (h10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) :
    Matrix.det ((sigmaNormPow (σG σ) (Module.finrank F L) t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      algebraMap F L (Algebra.norm F ((t : Matrix (Fin 2) (Fin 2) L) 0 0) *
        Algebra.norm F ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) := by
  rw [val_sigmaNormPow_diagonal hgen t h10 h01, Matrix.det_diagonal, Fin.prod_univ_two, map_mul]

omit [FiniteDimensional F L] [IsGalois F L] in

theorem diag_ne_zero (t : GL (Fin 2) L)
    (h10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (t : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
  have h := (Matrix.GeneralLinearGroup.det t).ne_zero
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, mul_zero, sub_zero] at h
  exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

end Diagonal

section Adelic

open NumberField

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

abbrev actU : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _)

theorem centralScalar_comm (w : (AdeleRing (𝓞 L) L)ˣ) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.centralScalar (𝓞 L) L w * y = y * AutomorphicForm.centralScalar (𝓞 L) L w := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (w : AdeleRing (𝓞 L) L) (fun r' => mul_comm _ r')
    (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq i) j

theorem mul_cs (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    g * AutomorphicForm.centralScalar (𝓞 L) L w = AutomorphicForm.centralScalar (𝓞 L) L w * g :=
  (centralScalar_comm L w g).symm

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) =
      AutomorphicForm.centralScalar (𝓞 L) L (actU K L D σ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [AutomorphicForm.sigmaAdelicAct, AutomorphicForm.centralScalar,
    Matrix.GeneralLinearGroup.map_apply]
  change ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom)
      (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) (((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (z : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem val_centralScalar_mul (w : (AdeleRing (𝓞 L) L)ˣ) (A : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    ((AutomorphicForm.centralScalar (𝓞 L) L w * A : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      (w : AdeleRing (𝓞 L) L) • (A : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) := by
  rw [Matrix.GeneralLinearGroup.coe_mul]
  change Matrix.scalar (Fin 2) (w : AdeleRing (𝓞 L) L) * _ = _
  rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]

theorem det_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 L) L z) = z ^ 2 := by
  have h : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      z ^ Fintype.card (Fin 2) := Matrix.GeneralLinearGroup.det_scalar z
  rw [Fintype.card_fin] at h
  exact h

theorem iterate_sigmaAdelicAct (r : ℕ) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    (AutomorphicForm.sigmaAdelicAct K L D σ)^[r] g = AutomorphicForm.sigmaAdelicAct K L D (σ ^ r) g := by
  induction r with
  | zero => rw [Function.iterate_zero, pow_zero, AutomorphicForm.sigmaAdelicAct_one]; rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ', AutomorphicForm.sigmaAdelicAct_mul]; rfl

variable [FiniteDimensional K L] [IsGalois K L]

theorem iterate_sigmaAdelicAct_finrank (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    (AutomorphicForm.sigmaAdelicAct K L D σ)^[Module.finrank K L] g = g := by
  have horder : orderOf σ = Module.finrank K L := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]
  rw [iterate_sigmaAdelicAct, ← horder, pow_orderOf_eq_one, AutomorphicForm.sigmaAdelicAct_one]
  rfl

theorem sigmaNormPow_adelic_sigmaConj (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (x m : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) (Module.finrank K L)
        (x⁻¹ * m * AutomorphicForm.sigmaAdelicAct K L D σ x) =
      x⁻¹ * sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) (Module.finrank K L) m * x :=
  sigmaNormPow_sigmaConjElt _ _ (iterate_sigmaAdelicAct_finrank K L D σ hgen x) m

omit [FiniteDimensional K L] [IsGalois K L] in

theorem sigmaNormPow_adelic_globalPoints (n : ℕ) (δ : GL (Fin 2) L) :
    sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n (AutomorphicForm.globalPoints (𝓞 L) L δ) =
      AutomorphicForm.globalPoints (𝓞 L) L (sigmaNormPow (σG σ) n δ) :=
  (hom_sigmaNormPow (σG σ) (AutomorphicForm.sigmaAdelicAct K L D σ) (AutomorphicForm.globalPoints (𝓞 L) L)
    (fun g => (AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ g).symm) n δ).symm

omit [FiniteDimensional K L] [IsGalois K L] in

theorem sigmaNormPow_adelic_centralScalar (n : ℕ) (w : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n (AutomorphicForm.centralScalar (𝓞 L) L w) =
      AutomorphicForm.centralScalar (𝓞 L) L (sigmaNormPow (actU K L D σ) n w) :=
  (hom_sigmaNormPow (actU K L D σ) (AutomorphicForm.sigmaAdelicAct K L D σ)
    (AutomorphicForm.centralScalar (𝓞 L) L) (fun w => (sigmaAdelicAct_centralScalar K L D σ w).symm) n w).symm

omit [FiniteDimensional K L] [IsGalois K L] in

theorem sigmaNormPow_adelic_mul_centralScalar (n : ℕ) (m : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (w : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n (m * AutomorphicForm.centralScalar (𝓞 L) L w) =
      sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n m *
        sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n (AutomorphicForm.centralScalar (𝓞 L) L w) :=
  sigmaPartialNorm_mul_of_central _ m _ (centralScalar_comm L w) n

omit [FiniteDimensional K L] [IsGalois K L] in
theorem continuous_sigmaNormPow_adelic (n : ℕ) :
    Continuous fun s : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n s :=
  continuous_sigmaPartialNorm _ (AutomorphicForm.continuous_sigmaAdelicAct K L D σ) n

theorem sigmaNormPow_kernelArg (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (t : GL (Fin 2) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) (Module.finrank K L)
        (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) =
      x⁻¹ * (AutomorphicForm.centralScalar (𝓞 L) L
          (sigmaNormPow (actU K L D σ) (Module.finrank K L) (actU K L D σ z)) *
        AutomorphicForm.globalPoints (𝓞 L) L (sigmaNormPow (σG σ) (Module.finrank K L) t)) * x := by
  have harg : x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x) =
      x⁻¹ * (AutomorphicForm.globalPoints (𝓞 L) L t *
        AutomorphicForm.centralScalar (𝓞 L) L (actU K L D σ z)) * AutomorphicForm.sigmaAdelicAct K L D σ x := by
    rw [map_mul, sigmaAdelicAct_centralScalar]
    simp only [mul_assoc]
  rw [harg, sigmaNormPow_adelic_sigmaConj K L D σ hgen, sigmaNormPow_adelic_mul_centralScalar,
    sigmaNormPow_adelic_globalPoints, sigmaNormPow_adelic_centralScalar, mul_cs]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem trace_val_globalPoints (γ : GL (Fin 2) L) :
    Matrix.trace ((AutomorphicForm.globalPoints (𝓞 L) L γ : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      algebraMap L (AdeleRing (𝓞 L) L) (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) L)) :=
  (AddMonoidHom.map_trace (algebraMap L (AdeleRing (𝓞 L) L)) (γ : Matrix (Fin 2) (Fin 2) L)).symm

omit [FiniteDimensional K L] [IsGalois K L] in
theorem det_val_globalPoints (γ : GL (Fin 2) L) :
    Matrix.det ((AutomorphicForm.globalPoints (𝓞 L) L γ : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      algebraMap L (AdeleRing (𝓞 L) L) (Matrix.det (γ : Matrix (Fin 2) (Fin 2) L)) :=
  ((algebraMap L (AdeleRing (𝓞 L) L)).map_det (γ : Matrix (Fin 2) (Fin 2) L)).symm

omit [FiniteDimensional K L] [IsGalois K L] in
theorem trace_val_conj (x g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    Matrix.trace ((x⁻¹ * g * x : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    one_mul]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem det_conj (x g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    Matrix.GeneralLinearGroup.det (x⁻¹ * g * x) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]

end Adelic

section Invariant

open NumberField

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

def inv (n : ℕ) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) : AdeleRing (𝓞 L) L :=
  Matrix.trace ((sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) ^ 2 *
    (((Matrix.GeneralLinearGroup.det (sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n y))⁻¹ :
      (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)

def invL (n : ℕ) (t : GL (Fin 2) L) : L :=
  Matrix.trace ((sigmaNormPow (σG σ) n t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) ^ 2 /
    Matrix.det ((sigmaNormPow (σG σ) n t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)

theorem continuous_inv (n : ℕ) : Continuous (inv K L D σ n) := by
  have hN := continuous_sigmaNormPow_adelic K L D σ n
  have hT : Continuous fun y : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      Matrix.trace ((sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n y :
        AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) :=
    (Units.continuous_val.comp hN).matrix_trace
  have hD : Continuous fun y : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      (((Matrix.GeneralLinearGroup.det (sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n y))⁻¹ :
        (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) := by
    show Continuous fun y : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      Matrix.det (((sigmaNormPow (AutomorphicForm.sigmaAdelicAct K L D σ) n y)⁻¹ :
        AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))
    exact (Units.continuous_coe_inv.comp hN).matrix_det
  exact (hT.pow 2).mul hD

variable [FiniteDimensional K L] [IsGalois K L]

theorem inv_kernelArg (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (t : GL (Fin 2) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    inv K L D σ (Module.finrank K L)
        (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) =
      algebraMap L (AdeleRing (𝓞 L) L) (invL K L σ (Module.finrank K L) t) := by
  set n := Module.finrank K L with hn
  unfold inv invL
  rw [sigmaNormPow_kernelArg K L D σ hgen, trace_val_conj, det_conj, val_centralScalar_mul, Matrix.trace_smul,
    smul_eq_mul, map_mul, det_centralScalar, trace_val_globalPoints]
  set w : (AdeleRing (𝓞 L) L)ˣ := sigmaNormPow (actU K L D σ) n (actU K L D σ z) with hw
  set Nt : GL (Fin 2) L := sigmaNormPow (σG σ) n t with hNt
  set dA : (AdeleRing (𝓞 L) L)ˣ := Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints (𝓞 L) L Nt)
    with hdA

  have hdet_ne : Matrix.det (Nt : Matrix (Fin 2) (Fin 2) L) ≠ 0 := by
    have h := (Matrix.GeneralLinearGroup.det Nt).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at h
  have hdAinv : ((dA⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) =
      algebraMap L (AdeleRing (𝓞 L) L) (Matrix.det (Nt : Matrix (Fin 2) (Fin 2) L))⁻¹ := by
    apply Units.inv_eq_of_mul_eq_one_left
    rw [hdA, Matrix.GeneralLinearGroup.val_det_apply, det_val_globalPoints, ← map_mul,
      inv_mul_cancel₀ hdet_ne, map_one]
  rw [mul_inv, Units.val_mul, hdAinv, div_eq_mul_inv, map_mul, map_pow]
  have hww : ((w : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * (((w ^ 2)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) *
      (w : AdeleRing (𝓞 L) L) = 1 := by
    rw [mul_right_comm, ← Units.val_mul, ← pow_two, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc ((w : AdeleRing (𝓞 L) L) * algebraMap L (AdeleRing (𝓞 L) L) (Matrix.trace (Nt : Matrix (Fin 2) (Fin 2) L))) ^ 2 *
        ((((w ^ 2)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) *
          algebraMap L (AdeleRing (𝓞 L) L) (Matrix.det (Nt : Matrix (Fin 2) (Fin 2) L))⁻¹)
        = ((w : AdeleRing (𝓞 L) L) * (((w ^ 2)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * (w : AdeleRing (𝓞 L) L)) *
          (algebraMap L (AdeleRing (𝓞 L) L) (Matrix.trace (Nt : Matrix (Fin 2) (Fin 2) L)) ^ 2 *
            algebraMap L (AdeleRing (𝓞 L) L) (Matrix.det (Nt : Matrix (Fin 2) (Fin 2) L))⁻¹) := by ring
    _ = _ := by rw [hww, one_mul]

omit [NumberField L] in

theorem invL_diagonal (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (t : GL (Fin 2) L)
    (h10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) :
    invL K L σ (Module.finrank K L) t =
      algebraMap K L
        ((Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) + Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ^ 2 /
          (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1))) := by
  unfold invL
  rw [trace_sigmaNormPow_diagonal hgen t h10 h01, det_sigmaNormPow_diagonal hgen t h10 h01, map_div₀, map_pow]

end Invariant

section Algebra

theorem mul_eq_or_mul_eq_of_invariant_eq {F : Type*} [Field F] {a b a' b' : F}
    (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0) (hb' : b' ≠ 0)
    (h : (a + b) ^ 2 / (a * b) = (a' + b') ^ 2 / (a' * b')) :
    a * b' = a' * b ∨ a * a' = b * b' := by
  rw [div_eq_div_iff (mul_ne_zero ha hb) (mul_ne_zero ha' hb')] at h
  have hfac : (a * b' - a' * b) * (a * a' - b * b') = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (sub_eq_zero.mp h2)

theorem norm_div' {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] (x y : L)
    (hy : y ≠ 0) : Algebra.norm F (x / y) = Algebra.norm F x / Algebra.norm F y := by
  rw [eq_div_iff (Algebra.norm_ne_zero_iff.mpr hy), ← map_mul, div_mul_cancel₀ x hy]

end Algebra

section Main

open NumberField

theorem eq_of_invL_eq (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (Δ : Set (GL (Fin 2) L))
    (hΔd : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hΔdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)})
    {t t' : GL (Fin 2) L} (ht : t ∈ Δ) (ht' : t' ∈ Δ)
    (heq : invL K L σ (Module.finrank K L) t = invL K L σ (Module.finrank K L) t') : t = t' := by
  obtain ⟨h10, h01, -⟩ := hΔd t ht
  obtain ⟨h10', h01', -⟩ := hΔd t' ht'

  set a := Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) with ha
  set b := Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) with hb
  set a' := Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) with ha'
  set b' := Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 1 1) with hb'
  obtain ⟨ht00, ht11⟩ := diag_ne_zero t h10
  obtain ⟨ht00', ht11'⟩ := diag_ne_zero t' h10'
  have ha0 : a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ht00
  have hb0 : b ≠ 0 := Algebra.norm_ne_zero_iff.mpr ht11
  have ha0' : a' ≠ 0 := Algebra.norm_ne_zero_iff.mpr ht00'
  have hb0' : b' ≠ 0 := Algebra.norm_ne_zero_iff.mpr ht11'

  rw [invL_diagonal K L σ hgen t h10 h01, invL_diagonal K L σ hgen t' h10' h01'] at heq
  have heqK := (algebraMap K L).injective heq
  have hcases := mul_eq_or_mul_eq_of_invariant_eq ha0 hb0 ha0' hb0' heqK

  have hpar := (LT.TwistedNorm.setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal
    (K := K) (L := L) hgen).2.2 t t' ⟨h10, h01⟩ ⟨h10', h01'⟩
  have hclass : {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
        t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} =
      {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
        t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} := by
    refine hpar.2.mpr ?_
    rcases hcases with h1 | h2
    ·
      refine ⟨(t' : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 1 1,
        div_ne_zero ht11' ht11, Or.inl ⟨?_, ?_⟩⟩
      · rw [norm_div' _ _ ht11]
        change a' = b' / b * a
        field_simp
        linear_combination h1.symm
      · rw [norm_div' _ _ ht11]
        change b' = b' / b * b
        field_simp
    ·
      refine ⟨(t' : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0,
        div_ne_zero ht11' ht00, Or.inr ⟨?_, ?_⟩⟩
      · rw [norm_div' _ _ ht00]
        change a' = b' / a * b
        field_simp
        linear_combination h2
      · rw [norm_div' _ _ ht00]
        change b' = b' / a * a
        field_simp

  have ht'mem : t' ∈ {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
      t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} :=
    ⟨1, by simp only [inv_one, one_mul, map_one, mul_one, inv_mul_cancel]; exact Subgroup.one_mem _⟩
  have ht'mem2 : t' ∈ {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
      t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} := by
    rw [← hclass]; exact ht'mem
  by_contra hne
  exact Set.disjoint_left.mp (hΔdisj t ht t' ht' hne) ht'mem2 ht'mem

theorem main (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : HasCompactSupport φ)
    (Δ : Set (GL (Fin 2) L))
    (hΔd : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hΔdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) :
    {t ∈ Δ | ∃ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ≠ 0}.Finite := by
  classical
  set n := Module.finrank K L with hn
  have hSc : IsCompact (tsupport φ) := hφc

  have hC : IsCompact (inv K L D σ n '' tsupport φ) := hSc.image (continuous_inv K L D σ n)
  have hfin := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact L hC
  refine Set.Finite.of_finite_image (f := invL K L σ n) (hfin.subset ?_) ?_
  · rintro _ ⟨t, ⟨-, x, z, hne⟩, rfl⟩
    refine ⟨_, subset_tsupport φ (Function.mem_support.mpr hne), ?_⟩
    exact inv_kernelArg K L D σ hgen x t z
  · intro t ht t' ht' heq
    exact eq_of_invL_eq K L σ hgen Δ hΔd hΔdisj ht.1 ht'.1 heq

end Main

end R1DiagFin

end

open NumberField

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : HasCompactSupport φ)
    (Δ : Set (GL (Fin 2) L))
    (hΔd : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hΔdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) :
    {t ∈ Δ | ∃ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ≠ 0}.Finite :=
  R1DiagFin.main K L σ hgen D φ hφc Δ hΔd hΔdisj

end S_AutomorphicForm_finite_sep_exists_apply_inv_mul_globalPoints_mul_sigmaAdelicAct_ne_zero_of_diagonal_of_hasCompactSupport
end P2MW
export P2MW.S_AutomorphicForm_finite_sep_exists_apply_inv_mul_globalPoints_mul_sigmaAdelicAct_ne_zero_of_diagonal_of_hasCompactSupport (solution)
