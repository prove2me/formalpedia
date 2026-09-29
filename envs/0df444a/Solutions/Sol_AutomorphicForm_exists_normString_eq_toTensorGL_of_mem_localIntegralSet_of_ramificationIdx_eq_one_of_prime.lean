-- Prove2me | solution 1 for AutomorphicForm.exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/03548c34-3ba0-57f8-8266-7bf44d947bcb

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers
import Theorems.Thm_IsAdicComplete_of_finite_of_isNoetherianRing
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers
import Theorems.Thm_IsAdicComplete_exists_isUnit_prod_iterate_eq_of_forall_isUnit_exists_sub_mem_span_singleton
import Theorems.Thm_Finite_exists_isUnit_prod_pow_apply_eq_of_isReduced_of_prime
import Theorems.Thm_Finite_exists_sum_pow_apply_eq_of_isReduced_of_prime
import Theorems.Thm_AdjoinRoot_isReduced_of_isReduced_of_isUnit_sq_sub_four_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime

set_option autoImplicit false

open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace KIN

theorem orderOf_eq_finrank_of_prime {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    orderOf σ = Module.finrank K L := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  have hH := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
  rw [Nat.card_zpowers] at hH
  have hdvd : orderOf σ ∣ Module.finrank K L := by
    rw [← Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L, hH]
    exact dvd_mul_left _ _
  rcases (Nat.dvd_prime hdeg).1 hdvd with h1 | h1
  · exact absurd (orderOf_eq_one_iff.1 h1) hσ
  · exact h1

theorem pow_finrank_eq_one_of_prime {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_eq_finrank_of_prime hdeg σ hσ]
  exact pow_orderOf_eq_one σ

theorem isGalois_of_prime {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) : IsGalois K L := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  apply IsGalois.of_card_aut_eq_finrank
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]; exact AlgEquiv.card_le
  · rw [← orderOf_eq_finrank_of_prime hdeg σ hσ, ← Nat.card_zpowers]
    exact Subgroup.card_le_card_group _

theorem eq_one_of_forall_smul_sub_mem {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (w : HeightOneSpectrum (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (g : L ≃ₐ[K] L) (hg : ∀ b : 𝓞 L, g • b - b ∈ w.asIdeal) : g = 1 := by
  set P := w.asIdeal with hP
  set p := (HeightOneSpectrum.under (𝓞 K) w).asIdeal with hp
  haveI : P.IsMaximal := w.isMaximal
  haveI : P.LiesOver p := ⟨rfl⟩
  haveI hpmax : p.IsMaximal := (HeightOneSpectrum.under (𝓞 K) w).isMaximal
  letI : Field (𝓞 K ⧸ p) := Ideal.Quotient.field p
  letI : Field (𝓞 L ⧸ P) := Ideal.Quotient.field P
  haveI : Finite (𝓞 K ⧸ p) := Ideal.finiteQuotientOfFreeOfNeBot p (HeightOneSpectrum.under (𝓞 K) w).ne_bot
  haveI : PerfectField (𝓞 K ⧸ p) := inferInstance
  haveI : Algebra.IsAlgebraic (𝓞 K ⧸ p) (𝓞 L ⧸ P) := inferInstance
  haveI : Algebra.IsSeparable (𝓞 K ⧸ p) (𝓞 L ⧸ P) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) p P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P (L ≃ₐ[K] L),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (p := p) (q := P) (HeightOneSpectrum.under (𝓞 K) w).ne_bot,
    hw, Subgroup.card_eq_one] at hcard
  have hmem : g ∈ P.inertia (L ≃ₐ[K] L) := by
    rw [Ideal.inertia, AddSubgroup.mem_inertia]
    exact hg
  rw [hcard] at hmem
  exact Subgroup.mem_bot.1 hmem

section Setup

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

abbrev Kv := v.adicCompletion K

abbrev Ov := v.adicCompletionIntegers K

abbrev E := L ⊗[K] v.adicCompletion K

abbrev ι := HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v

def Osub : Subalgebra (𝓞 L) (E K L v) := (ι K L v).range

theorem coe_Osub : ((Osub K L v : Subalgebra (𝓞 L) (E K L v)) : Set (E K L v)) =
    AutomorphicForm.semiLocalIntegers K L v := rfl

theorem mem_Osub_iff (x : E K L v) : x ∈ Osub K L v ↔ x ∈ AutomorphicForm.semiLocalIntegers K L v := Iff.rfl

theorem ι_mem_Osub (y : 𝓞 L ⊗[𝓞 K] Ov K v) : ι K L v y ∈ Osub K L v := ⟨y, rfl⟩

theorem tmul_mem_Osub (b : 𝓞 L) (a : Ov K v) : ((b : L) ⊗ₜ[K] (a : Kv K v) : E K L v) ∈ Osub K L v :=
  ⟨b ⊗ₜ a, by simp⟩

def O : Type := ↥(Osub K L v)

scoped instance instCommRingO : CommRing (O K L v) := inferInstanceAs (CommRing ↥(Osub K L v))
scoped instance instAlgebraO : Algebra (𝓞 L) (O K L v) := inferInstanceAs (Algebra (𝓞 L) ↥(Osub K L v))

def Omk (x : E K L v) (hx : x ∈ Osub K L v) : O K L v := ⟨x, hx⟩

def Oval : O K L v →+* E K L v := (Osub K L v).val.toRingHom

@[scoped simp] theorem Oval_Omk (x : E K L v) (hx : x ∈ Osub K L v) : Oval K L v (Omk K L v x hx) = x := rfl

theorem Oval_injective : Function.Injective (Oval K L v) := Subtype.val_injective

theorem Oval_mem (x : O K L v) : Oval K L v x ∈ Osub K L v := Subtype.prop x

theorem O_ext {x y : O K L v} (h : Oval K L v x = Oval K L v y) : x = y := Oval_injective K L v h

theorem Oval_algebraMap (b : 𝓞 L) : Oval K L v (algebraMap (𝓞 L) (O K L v) b) = (b : L) ⊗ₜ[K] (1 : Kv K v) := by
  change algebraMap (𝓞 L) (E K L v) b = _
  rw [IsScalarTower.algebraMap_apply (𝓞 L) L (E K L v), Algebra.TensorProduct.algebraMap_apply]
  rfl

def ιv : Ov K v →+* O K L v where
  toFun a := Omk K L v ((1 : L) ⊗ₜ[K] (a : Kv K v)) (by simpa using tmul_mem_Osub K L v 1 a)
  map_one' := O_ext K L v rfl
  map_mul' a b := O_ext K L v (by simp [Algebra.TensorProduct.tmul_mul_tmul])
  map_zero' := O_ext K L v (by simp)
  map_add' a b := O_ext K L v (by simp [TensorProduct.tmul_add])

@[scoped simp] theorem Oval_ιv (a : Ov K v) : Oval K L v (ιv K L v a) = (1 : L) ⊗ₜ[K] (a : Kv K v) := rfl

theorem Oval_ιv_eq_includeRight (a : Ov K v) :
    Oval K L v (ιv K L v a) = Algebra.TensorProduct.includeRight (a : Kv K v) := rfl

end Setup

section Sigma

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

abbrev sE : E K L v →+* E K L v := AutomorphicForm.sigmaTensor K L (Kv K v) σ

@[scoped simp] theorem sE_tmul (x : L) (y : Kv K v) : sE K L v σ (x ⊗ₜ y) = σ x ⊗ₜ y := by
  simp [sE, AutomorphicForm.sigmaTensor]

theorem coe_smul_ringOfIntegers (b : 𝓞 L) : ((σ • b : 𝓞 L) : L) = σ (b : L) := rfl

theorem sE_mem_Osub {x : E K L v} (hx : x ∈ Osub K L v) : sE K L v σ x ∈ Osub K L v := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b a =>
    change sE K L v σ (ι K L v (b ⊗ₜ a)) ∈ Osub K L v
    rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, sE_tmul]
    exact ⟨(σ • b) ⊗ₜ a, by simp [coe_smul_ringOfIntegers]⟩
  | add y z hy hz =>
    rw [map_add, map_add]
    exact add_mem hy hz

def sO : O K L v →+* O K L v :=
  (sE K L v σ).restrict (Osub K L v).toSubring (Osub K L v).toSubring fun _ hx => sE_mem_Osub K L v σ hx

@[scoped simp] theorem Oval_sO (x : O K L v) : Oval K L v (sO K L v σ x) = sE K L v σ (Oval K L v x) := rfl

theorem sO_ιv (a : Ov K v) : sO K L v σ (ιv K L v a) = ιv K L v a :=
  O_ext K L v (by simp)

theorem sO_algebraMap (b : 𝓞 L) :
    sO K L v σ (algebraMap (𝓞 L) (O K L v) b) = algebraMap (𝓞 L) (O K L v) (σ • b) := by
  apply O_ext
  rw [Oval_sO, Oval_algebraMap, Oval_algebraMap, sE_tmul, coe_smul_ringOfIntegers]

theorem sE_iterate_tmul (i : ℕ) (x : L) (y : Kv K v) :
    (sE K L v σ)^[i] (x ⊗ₜ y) = ((σ ^ i) x) ⊗ₜ y := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, sE_tmul, pow_succ']
    rfl

theorem sE_iterate_eq_self_of_pow_eq_one (n : ℕ) (hσn : σ ^ n = 1) (x : E K L v) :
    (sE K L v σ)^[n] x = x := by
  rw [← RingHom.coe_pow]
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | tmul a b => rw [RingHom.coe_pow, sE_iterate_tmul, hσn]; rfl
  | add y z hy hz => rw [map_add, hy, hz]

theorem sO_iterate_eq_self_of_pow_eq_one (n : ℕ) (hσn : σ ^ n = 1) (x : O K L v) :
    (sO K L v σ)^[n] x = x := by
  apply O_ext
  have : ∀ m : ℕ, Oval K L v ((sO K L v σ)^[m] x) = (sE K L v σ)^[m] (Oval K L v x) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Oval_sO, ih]
  rw [this, sE_iterate_eq_self_of_pow_eq_one K L v σ n hσn]

end Sigma

theorem adjoinRoot_ringHom_ext {R S : Type*} [CommRing R] [Semiring S] {f : R[X]}
    {g₁ g₂ : AdjoinRoot f →+* S} (hC : ∀ a, g₁ (AdjoinRoot.of f a) = g₂ (AdjoinRoot.of f a))
    (hX : g₁ (AdjoinRoot.root f) = g₂ (AdjoinRoot.root f)) : g₁ = g₂ :=
  Ideal.Quotient.ringHom_ext (Polynomial.ringHom_ext (fun a => hC a) hX)

section Quad

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) (t n : Ov K v)

abbrev fO : (O K L v)[X] := X ^ 2 - C (ιv K L v t) * X + C (ιv K L v n)

theorem monic_fO : (fO K L v t n).Monic := by
  nontriviality (O K L v)
  unfold fO
  monicity!

abbrev Dq := AdjoinRoot (fO K L v t n)

theorem map_sO_fO : (fO K L v t n).map (sO K L v σ) = fO K L v t n := by
  simp [fO, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, sO_ιv]

def τ : Dq K L v t n →+* Dq K L v t n :=
  AdjoinRoot.lift ((AdjoinRoot.of _).comp (sO K L v σ)) (AdjoinRoot.root _) (by
    rw [← Polynomial.eval₂_map, map_sO_fO]
    exact AdjoinRoot.eval₂_root _)

@[scoped simp] theorem τ_of (x : O K L v) : τ K L v σ t n (AdjoinRoot.of _ x) = AdjoinRoot.of _ (sO K L v σ x) := by
  rw [τ, AdjoinRoot.lift_of]; rfl

@[scoped simp] theorem τ_root : τ K L v σ t n (AdjoinRoot.root _) = AdjoinRoot.root _ := by
  rw [τ, AdjoinRoot.lift_root]

theorem τ_iterate_of (i : ℕ) (x : O K L v) :
    (τ K L v σ t n)^[i] (AdjoinRoot.of _ x) = AdjoinRoot.of _ ((sO K L v σ)^[i] x) := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, τ_of, ih, Function.iterate_succ_apply]

theorem τ_iterate_root (i : ℕ) : (τ K L v σ t n)^[i] (AdjoinRoot.root _) = AdjoinRoot.root _ := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, τ_root, ih]

theorem τ_pow_eq_one (m : ℕ) (hσm : σ ^ m = 1) : τ K L v σ t n ^ m = 1 := by
  apply adjoinRoot_ringHom_ext
  · intro a
    rw [RingHom.coe_pow, τ_iterate_of, sO_iterate_eq_self_of_pow_eq_one K L v σ m hσm]; rfl
  · rw [RingHom.coe_pow, τ_iterate_root]; rfl

theorem τ_iterate_eq_self (m : ℕ) (hσm : σ ^ m = 1) (z : Dq K L v t n) : (τ K L v σ t n)^[m] z = z := by
  rw [← RingHom.coe_pow, τ_pow_eq_one K L v σ t n m hσm]; rfl

def τEquiv (m : ℕ) (hm : 0 < m) (hσm : σ ^ m = 1) : Dq K L v t n ≃+* Dq K L v t n :=
  RingEquiv.ofRingHom (τ K L v σ t n) (τ K L v σ t n ^ (m - 1))
    (by rw [← RingHom.mul_def, ← pow_succ', Nat.sub_add_cancel hm, τ_pow_eq_one K L v σ t n m hσm]; rfl)
    (by rw [← RingHom.mul_def, ← pow_succ, Nat.sub_add_cancel hm, τ_pow_eq_one K L v σ t n m hσm]; rfl)

@[scoped simp] theorem τEquiv_apply (m : ℕ) (hm : 0 < m) (hσm : σ ^ m = 1) (z : Dq K L v t n) :
    τEquiv K L v σ t n m hm hσm z = τ K L v σ t n z := rfl

theorem τEquiv_pow_apply (m : ℕ) (hm : 0 < m) (hσm : σ ^ m = 1) (i : ℕ) (z : Dq K L v t n) :
    (τEquiv K L v σ t n m hm hσm ^ i) z = (τ K L v σ t n)^[i] z := by
  rw [RingAut.coe_pow]
  induction i generalizing z with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]; rfl

theorem root_mul : AdjoinRoot.root (fO K L v t n) * (AdjoinRoot.of _ (ιv K L v t) - AdjoinRoot.root _) =
    AdjoinRoot.of _ (ιv K L v n) := by
  have h := AdjoinRoot.eval₂_root (fO K L v t n)
  simp only [fO, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C] at h
  linear_combination -h

theorem isUnit_root (hn : IsUnit n) : IsUnit (AdjoinRoot.root (fO K L v t n)) := by
  have h : IsUnit (AdjoinRoot.of (fO K L v t n) (ιv K L v n)) := (hn.map (ιv K L v)).map _
  rw [← root_mul] at h
  exact isUnit_of_mul_isUnit_left h

end Quad
section Matrices

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

theorem cayley_hamilton_two {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    M * M - Matrix.scalar (Fin 2) (Matrix.trace M) * M + Matrix.scalar (Fin 2) (Matrix.det M) = 0 := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] <;> ring

theorem list_prod_range_eq {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]; simp

variable (γ : GL (Fin 2) (Kv K v)) (hγ : γ ∈ AutomorphicForm.localIntegralSet K v)

def γOv : Matrix (Fin 2) (Fin 2) (Ov K v) := fun i j => ⟨(γ : Matrix (Fin 2) (Fin 2) (Kv K v)) i j, hγ.1 i j⟩

def γOvInv : Matrix (Fin 2) (Fin 2) (Ov K v) :=
  fun i j => ⟨((γ⁻¹ : GL (Fin 2) (Kv K v)) : Matrix (Fin 2) (Fin 2) (Kv K v)) i j, hγ.2 i j⟩

abbrev OvVal : Ov K v →+* Kv K v := (v.adicCompletionIntegers K).subtype

theorem mapMatrix_γOv : (OvVal K v).mapMatrix (γOv K v γ hγ) = (γ : Matrix (Fin 2) (Fin 2) (Kv K v)) := by
  ext i j; rfl

theorem mapMatrix_γOvInv :
    (OvVal K v).mapMatrix (γOvInv K v γ hγ) = ((γ⁻¹ : GL (Fin 2) (Kv K v)) : Matrix (Fin 2) (Fin 2) (Kv K v)) := by
  ext i j; rfl

theorem γOv_mul_γOvInv : γOv K v γ hγ * γOvInv K v γ hγ = 1 := by
  have hinj : Function.Injective ((OvVal K v).mapMatrix : Matrix (Fin 2) (Fin 2) (Ov K v) → _) :=
    Matrix.map_injective Subtype.val_injective
  apply hinj
  rw [map_mul, map_one, mapMatrix_γOv, mapMatrix_γOvInv]
  exact γ.mul_inv

abbrev tγ : Ov K v := Matrix.trace (γOv K v γ hγ)
abbrev nγ : Ov K v := Matrix.det (γOv K v γ hγ)

theorem isUnit_nγ : IsUnit (nγ K v γ hγ) :=
  Matrix.isUnit_det_of_right_inverse (γOv_mul_γOvInv K v γ hγ)

theorem coe_tγ : ((tγ K v γ hγ : Ov K v) : Kv K v) = Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (Kv K v)) := by
  rw [← mapMatrix_γOv K v γ hγ, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]; rfl

theorem coe_nγ : ((nγ K v γ hγ : Ov K v) : Kv K v) = Matrix.det (γ : Matrix (Fin 2) (Fin 2) (Kv K v)) := by
  rw [← mapMatrix_γOv K v γ hγ, ← RingHom.map_det]; rfl

theorem isUnit_disc
    (hdisc : Valued.v (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (Kv K v)) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (Kv K v))) = 1) :
    IsUnit (tγ K v γ hγ ^ 2 - 4 * nγ K v γ hγ) := by
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  convert hdisc using 2
  push_cast
  rw [coe_tγ, coe_nγ]
  congr 2

def γO : Matrix (Fin 2) (Fin 2) (O K L v) := (ιv K L v).mapMatrix (γOv K v γ hγ)

theorem γO_map_sO : (sO K L v σ).mapMatrix (γO K L v γ hγ) = γO K L v γ hγ := by
  ext i j
  simp [γO, sO_ιv]

theorem mapMatrix_Oval_γO :
    (Oval K L v).mapMatrix (γO K L v γ hγ) =
      (AutomorphicForm.toTensorGL K L (Kv K v) γ : Matrix (Fin 2) (Fin 2) (E K L v)) := by
  ext i j; rfl

def ev : Dq K L v (tγ K v γ hγ) (nγ K v γ hγ) →+* Matrix (Fin 2) (Fin 2) (O K L v) :=
  Ideal.Quotient.lift _
    (eval₂RingHom' (algebraMap (O K L v) (Matrix (Fin 2) (Fin 2) (O K L v))) (γO K L v γ hγ)
      fun a => Algebra.commute_algebraMap_left a _)
    (by
      intro g hg
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hg
      rw [map_mul]
      suffices h : eval₂RingHom' (algebraMap (O K L v) (Matrix (Fin 2) (Fin 2) (O K L v))) (γO K L v γ hγ)
          (fun a => Algebra.commute_algebraMap_left a _) (fO K L v (tγ K v γ hγ) (nγ K v γ hγ)) = 0 by
        rw [h, mul_zero]
      have hCH := cayley_hamilton_two (γO K L v γ hγ)
      have htr : Matrix.trace (γO K L v γ hγ) = ιv K L v (tγ K v γ hγ) := by
        rw [γO, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]
      have hdet : Matrix.det (γO K L v γ hγ) = ιv K L v (nγ K v γ hγ) := by
        rw [γO, ← RingHom.map_det]
      rw [htr, hdet] at hCH
      rw [show ∀ p, eval₂RingHom' (algebraMap (O K L v) (Matrix (Fin 2) (Fin 2) (O K L v))) (γO K L v γ hγ)
          (fun a => Algebra.commute_algebraMap_left a _) p = eval₂ (algebraMap _ _) (γO K L v γ hγ) p from fun _ => rfl]
      simp only [fO, eval₂_add, eval₂_sub, eval₂_C, Matrix.algebraMap_eq_diagonal]
      simpa [Matrix.scalar_apply, sq, Algebra.algebraMap_self, Matrix.algebraMap_eq_diagonal,
        Pi.algebraMap_def] using hCH)

theorem ev_of (x : O K L v) : ev K L v γ hγ (AdjoinRoot.of _ x) = algebraMap _ _ x := by
  change Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ (C x)) = _
  rw [Ideal.Quotient.lift_mk]; exact eval₂_C _ _

theorem ev_root : ev K L v γ hγ (AdjoinRoot.root _) = γO K L v γ hγ := by
  change Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ X) = _
  rw [Ideal.Quotient.lift_mk]; exact eval₂_X _ _

theorem ev_τ (z : Dq K L v (tγ K v γ hγ) (nγ K v γ hγ)) :
    ev K L v γ hγ (τ K L v σ _ _ z) = (sO K L v σ).mapMatrix (ev K L v γ hγ z) := by
  have h : (ev K L v γ hγ).comp (τ K L v σ _ _) = ((sO K L v σ).mapMatrix).comp (ev K L v γ hγ) := by
    apply adjoinRoot_ringHom_ext
    · intro a
      rw [RingHom.comp_apply, RingHom.comp_apply, τ_of, ev_of, ev_of]
      ext i j
      rw [Matrix.algebraMap_matrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.algebraMap_matrix_apply]
      split_ifs <;> simp [Algebra.algebraMap_self]
    · rw [RingHom.comp_apply, RingHom.comp_apply, τ_root, ev_root, γO_map_sO]
  exact RingHom.congr_fun h z

theorem ev_τ_iterate (i : ℕ) (z : Dq K L v (tγ K v γ hγ) (nγ K v γ hγ)) :
    (Oval K L v).mapMatrix (ev K L v γ hγ ((τ K L v σ _ _)^[i] z)) =
      ((sE K L v σ).mapMatrix)^[i] ((Oval K L v).mapMatrix (ev K L v γ hγ z)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ev_τ, ← ih]
    ext a b
    rfl

theorem exists_delta (u : Dq K L v (tγ K v γ hγ) (nγ K v γ hγ)) (hu : IsUnit u)
    (hN : ∏ i ∈ Finset.range (Module.finrank K L), (τ K L v σ _ _)^[i] u = AdjoinRoot.root _) :
    ∃ δ ∈ AutomorphicForm.semiLocalIntegralSet K L v,
      AutomorphicForm.normString K L (v.adicCompletion K) σ δ =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) γ := by
  let uD : (Dq K L v (tγ K v γ hγ) (nγ K v γ hγ))ˣ := hu.unit
  let δ : GL (Fin 2) (E K L v) :=
    Matrix.GeneralLinearGroup.map (Oval K L v) (Units.map (ev K L v γ hγ).toMonoidHom uD)
  refine ⟨δ, ⟨fun i j => ?_, fun i j => ?_⟩, ?_⟩
  · exact (ev K L v γ hγ u i j).2
  · rw [← map_inv, ← map_inv]
    exact (ev K L v γ hγ (↑uD⁻¹ : Dq K L v (tγ K v γ hγ) (nγ K v γ hγ)) i j).2
  · apply Units.ext

    have hval : ∀ i : ℕ,
        (((AutomorphicForm.sigmaGL K L (Kv K v) σ : GL (Fin 2) (E K L v) → GL (Fin 2) (E K L v))^[i] δ :
          GL (Fin 2) (E K L v)) : Matrix (Fin 2) (Fin 2) (E K L v)) =
        (Oval K L v).mapMatrix (ev K L v γ hγ ((τ K L v σ _ _)^[i] u)) := by
      intro i
      rw [ev_τ_iterate]
      induction i with
      | zero => rfl
      | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl
    let φ : Dq K L v (tγ K v γ hγ) (nγ K v γ hγ) →+* Matrix (Fin 2) (Fin 2) (E K L v) :=
      ((Oval K L v).mapMatrix).comp (ev K L v γ hγ)
    calc ((AutomorphicForm.normString K L (Kv K v) σ δ : GL (Fin 2) (E K L v)) : Matrix (Fin 2) (Fin 2) (E K L v))
        = (((List.range (Module.finrank K L)).map fun i =>
            ((AutomorphicForm.sigmaGL K L (Kv K v) σ)^[i] δ)).map
              (Units.coeHom (Matrix (Fin 2) (Fin 2) (E K L v)))).prod := by
          rw [AutomorphicForm.normString, ← map_list_prod]; rfl
      _ = ((List.range (Module.finrank K L)).map fun i => φ ((τ K L v σ _ _)^[i] u)).prod := by
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact hval i
      _ = φ (∏ i ∈ Finset.range (Module.finrank K L), (τ K L v σ _ _)^[i] u) := by
          rw [← list_prod_range_eq, map_list_prod, List.map_map]; rfl
      _ = (Oval K L v).mapMatrix (γO K L v γ hγ) := by
          rw [hN]; change (Oval K L v).mapMatrix (ev K L v γ hγ (AdjoinRoot.root _)) = _; rw [ev_root]
      _ = _ := mapMatrix_Oval_γO K L v γ hγ

end Matrices

theorem mem_span_pow_smul_top_iff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ϖ : R)
    (n : ℕ) (x : A) :
    x ∈ ((Ideal.span {ϖ}) ^ n • ⊤ : Submodule R A) ↔ ∃ y : A, algebraMap R A ϖ ^ n * y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, rfl⟩
    exact ⟨b, by rw [← map_pow, ← Algebra.smul_def]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, Submodule.mem_top, by rw [← map_pow, ← Algebra.smul_def]⟩

theorem mem_span_algebraMap_pow_smul_top_iff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ϖ : R)
    (n : ℕ) (x : A) :
    x ∈ ((Ideal.span {algebraMap R A ϖ}) ^ n • ⊤ : Submodule A A) ↔ ∃ y : A, algebraMap R A ϖ ^ n * y = x := by
  rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨b, rfl⟩; exact ⟨b, mul_comm _ _⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩

theorem sModEq_span_iff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ϖ : R) (n : ℕ) (x y : A) :
    x ≡ y [SMOD ((Ideal.span {algebraMap R A ϖ}) ^ n • ⊤ : Submodule A A)] ↔
      x ≡ y [SMOD ((Ideal.span {ϖ}) ^ n • ⊤ : Submodule R A)] := by
  rw [SModEq.sub_mem, SModEq.sub_mem, mem_span_algebraMap_pow_smul_top_iff, mem_span_pow_smul_top_iff]

theorem isAdicComplete_span_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ϖ : R)
    [h : IsAdicComplete (Ideal.span {ϖ}) A] : IsAdicComplete (Ideal.span {algebraMap R A ϖ}) A where
  haus' x hx := by
    refine IsHausdorff.haus h.toIsHausdorff x fun n => ?_
    rw [← sModEq_span_iff]; exact hx n
  prec' f hf := by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := f) fun {m n} hmn => by
      rw [← sModEq_span_iff]; exact hf hmn
    exact ⟨L, fun n => by rw [sModEq_span_iff]; exact hL n⟩

section Complete

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) (t n : Ov K v)

scoped instance instAlgebraOvO : Algebra (Ov K v) (O K L v) := (ιv K L v).toAlgebra

theorem algebraMap_Ov_O (a : Ov K v) : algebraMap (Ov K v) (O K L v) a = ιv K L v a := rfl

def ιO (y : 𝓞 L ⊗[𝓞 K] Ov K v) : O K L v := Omk K L v (ι K L v y) (ι_mem_Osub K L v y)

theorem ιO_surjective : Function.Surjective (ιO K L v) := by
  rintro ⟨x, y, rfl⟩; exact ⟨y, rfl⟩

theorem ιO_add (y z : 𝓞 L ⊗[𝓞 K] Ov K v) : ιO K L v (y + z) = ιO K L v y + ιO K L v z :=
  O_ext K L v (by simp [ιO])

theorem ιO_zero : ιO K L v 0 = 0 := O_ext K L v (by simp [ιO])

theorem algebraMap_tmul_one_eq (r : 𝓞 K) :
    (((algebraMap (𝓞 K) (𝓞 L) r : 𝓞 L) : L) ⊗ₜ[K] (1 : Kv K v) : E K L v) =
      (1 : L) ⊗ₜ[K] ((algebraMap (𝓞 K) (Ov K v) r : Ov K v) : Kv K v) := by
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  have h1 : ((algebraMap (𝓞 K) (𝓞 L) r : 𝓞 L) : L) = (r : K) • (1 : L) := by
    rw [← Algebra.algebraMap_eq_smul_one]; rfl
  have h2 : ((algebraMap (𝓞 K) K r : K) : Kv K v) = (r : K) • (1 : Kv K v) := by
    rw [Algebra.smul_def, mul_one]; rfl
  rw [h1, h2, TensorProduct.smul_tmul]

theorem algebraMap_algebraMap_eq_ιv (r : 𝓞 K) :
    algebraMap (𝓞 L) (O K L v) (algebraMap (𝓞 K) (𝓞 L) r) = ιv K L v (algebraMap (𝓞 K) (Ov K v) r) :=
  O_ext K L v (by rw [Oval_algebraMap, Oval_ιv, algebraMap_tmul_one_eq])

theorem ιO_tmul (b : 𝓞 L) (a : Ov K v) :
    ιO K L v (b ⊗ₜ a) = a • algebraMap (𝓞 L) (O K L v) b := by
  apply O_ext
  rw [Algebra.smul_def, map_mul, algebraMap_Ov_O, Oval_ιv, Oval_algebraMap, ιO, Oval_Omk,
    HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

scoped instance moduleFinite_Ov_O : Module.Finite (Ov K v) (O K L v) := by
  classical
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := 𝓞 K) (M := 𝓞 L)
  refine ⟨⟨(Finset.univ.image fun i : Fin m => algebraMap (𝓞 L) (O K L v) (b i)), ?_⟩⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := ιO_surjective K L v x
  induction y using TensorProduct.induction_on with
  | zero => rw [ιO_zero]; exact Submodule.zero_mem _
  | tmul c a =>
    rw [ιO_tmul]
    refine Submodule.smul_mem _ _ ?_
    have hc : c ∈ Submodule.span (𝓞 K) (Set.range b) := by rw [hb]; exact Submodule.mem_top
    obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hc
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_

    have : algebraMap (𝓞 L) (O K L v) (r i • b i) =
        (algebraMap (𝓞 K) (Ov K v) (r i)) • algebraMap (𝓞 L) (O K L v) (b i) := by
      rw [Algebra.smul_def, map_mul, algebraMap_algebraMap_eq_ιv, Algebra.smul_def, algebraMap_Ov_O]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | add y z hy hz => rw [ιO_add]; exact Submodule.add_mem _ hy hz

scoped instance moduleFinite_Ov_Dq : Module.Finite (Ov K v) (Dq K L v t n) :=
  haveI : Module.Finite (O K L v) (Dq K L v t n) := (AdjoinRoot.powerBasis' (monic_fO K L v t n)).finite
  Module.Finite.trans (O K L v) (Dq K L v t n)

variable (ϖ : Ov K v)

abbrev ϖD : Dq K L v t n := algebraMap (Ov K v) (Dq K L v t n) ϖ

theorem ϖD_eq : ϖD K L v t n ϖ = AdjoinRoot.of _ (ιv K L v ϖ) := rfl

theorem τ_ϖD : τ K L v σ t n (ϖD K L v t n ϖ) = ϖD K L v t n ϖ := by
  rw [ϖD_eq, τ_of, sO_ιv]

theorem isAdicComplete_Dq (hϖ : IsLocalRing.maximalIdeal (Ov K v) = Ideal.span {ϖ}) :
    IsAdicComplete (Ideal.span {ϖD K L v t n ϖ}) (Dq K L v t n) := by
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (Ov K v)) (Ov K v) :=
    IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers K v
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (Ov K v)) (Dq K L v t n) :=
    IsAdicComplete.of_finite_of_isNoetherianRing _ _
  haveI : IsAdicComplete (Ideal.span {ϖ}) (Dq K L v t n) := by rwa [← hϖ]
  exact isAdicComplete_span_algebraMap ϖ

theorem ιv_mul_eq_zero {ϖ : Ov K v} (hϖ : ϖ ≠ 0) {x : O K L v} (h : ιv K L v ϖ * x = 0) : x = 0 := by
  apply O_ext
  have h' := congrArg (Oval K L v) h
  rw [map_mul, map_zero, Oval_ιv_eq_includeRight] at h'
  have hu : IsUnit (Algebra.TensorProduct.includeRight (R := K) (A := L) ((ϖ : Ov K v) : Kv K v) : E K L v) := by
    refine (IsUnit.mk0 _ ?_).map _
    exact_mod_cast hϖ
  rw [map_zero]
  exact (hu.mul_right_eq_zero).1 h'

theorem ϖD_mem_nonZeroDivisors (hϖ : ϖ ≠ 0) : ϖD K L v t n ϖ ∈ nonZeroDivisors (Dq K L v t n) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro z hz
  let pb := AdjoinRoot.powerBasis' (monic_fO K L v t n)
  rw [mul_comm] at hz
  have hz' : (ιv K L v ϖ) • z = 0 := by rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq]; exact hz
  have hrepr := congrArg pb.basis.repr hz'
  rw [map_smul, map_zero] at hrepr
  apply pb.basis.repr.injective
  rw [map_zero]
  ext i
  have hi := congrArg (fun f => f i) hrepr
  simp only [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul] at hi
  exact ιv_mul_eq_zero K L v hϖ hi

end Complete
section Residual

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

abbrev β := HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v

theorem β_Oval_mem (x : O K L v) (w : v.Extension (𝓞 L)) :
    β K L v (Oval K L v x) w ∈ w.1.adicCompletionIntegers L := by
  obtain ⟨y, hy⟩ : Oval K L v x ∈ Osub K L v := Oval_mem K L v x
  have hmem : β K L v (Oval K L v x) ∈ Set.range (β K L v ∘ ι K L v) := ⟨y, congrArg (β K L v) hy⟩
  rw [HeightOneSpectrum.range_baseChange_comp_tensorAdicCompletionTo_eq_pi] at hmem
  exact hmem w (Set.mem_univ w)

def ρw (w : v.Extension (𝓞 L)) : O K L v →+* w.1.adicCompletionIntegers L where
  toFun x := ⟨β K L v (Oval K L v x) w, β_Oval_mem K L v x w⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[scoped simp] theorem coe_ρw (w : v.Extension (𝓞 L)) (x : O K L v) :
    ((ρw K L v w x : w.1.adicCompletionIntegers L) : w.1.adicCompletion L) = β K L v (Oval K L v x) w := rfl

theorem coe_ρw_ιv (w : v.Extension (𝓞 L)) (a : Ov K v) :
    ((ρw K L v w (ιv K L v a) : w.1.adicCompletionIntegers L) : w.1.adicCompletion L) =
      HeightOneSpectrum.Extension.adicCompletionSemialgHom K L w (a : Kv K v) := by
  rw [coe_ρw, Oval_ιv, HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, one_mul]
  rfl

theorem exists_ρw_eq (y : ∀ w : v.Extension (𝓞 L), w.1.adicCompletionIntegers L) :
    ∃ x : O K L v, ∀ w, ρw K L v w x = y w := by
  have hmem : ((fun w => ((y w : w.1.adicCompletionIntegers L) : w.1.adicCompletion L)) :
      ∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) ∈ Set.range (β K L v ∘ ι K L v) := by
    rw [HeightOneSpectrum.range_baseChange_comp_tensorAdicCompletionTo_eq_pi]
    exact fun w _ => (y w).2
  obtain ⟨z, hz⟩ := hmem
  refine ⟨ιO K L v z, fun w => Subtype.ext ?_⟩
  rw [coe_ρw]
  have := congrFun hz w
  exact this

theorem eq_of_forall_ρw_eq {x y : O K L v} (h : ∀ w, ρw K L v w x = ρw K L v w y) : x = y := by
  apply O_ext
  apply (HeightOneSpectrum.adicCompletion.baseChange_bijective K L (𝓞 L) v).1
  funext w
  have := congrArg (fun z : w.1.adicCompletionIntegers L => (z : w.1.adicCompletion L)) (h w)
  exact this

variable (ϖ : Ov K v) (hϖ : Valued.v ((ϖ : Ov K v) : Kv K v) = Multiplicative.ofAdd (-1 : ℤ))
  (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
    Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)

include hϖ hv in

theorem valued_ρw_ιv (w : v.Extension (𝓞 L)) :
    Valued.v ((ρw K L v w (ιv K L v ϖ) : w.1.adicCompletionIntegers L) : w.1.adicCompletion L) =
      Multiplicative.ofAdd (-1 : ℤ) := by
  rw [coe_ρw_ιv, HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom, hv w.1 w.2, pow_one, hϖ]

include hϖ hv in
theorem maximalIdeal_eq_span_ρw (w : v.Extension (𝓞 L)) :
    IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers L) = Ideal.span {ρw K L v w (ιv K L v ϖ)} :=
  HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer L w.1 (valued_ρw_ιv K L v ϖ hϖ hv w)

abbrev Obar := O K L v ⧸ Ideal.span {ιv K L v ϖ}

include hϖ hv in
theorem residue_ρw_eq_zero {x : O K L v} (hx : x ∈ Ideal.span {ιv K L v ϖ}) (w : v.Extension (𝓞 L)) :
    IsLocalRing.residue _ (ρw K L v w x) = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [IsLocalRing.residue_eq_zero_iff, map_mul, maximalIdeal_eq_span_ρw K L v ϖ hϖ hv w]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

def ρbar : Obar K L v ϖ →+* ∀ w : v.Extension (𝓞 L), IsLocalRing.ResidueField (w.1.adicCompletionIntegers L) :=
  Ideal.Quotient.lift _ (RingHom.pi fun w => (IsLocalRing.residue _).comp (ρw K L v w)) fun _ hx =>
    funext fun w => residue_ρw_eq_zero K L v ϖ hϖ hv hx w

theorem ρbar_mk (x : O K L v) (w : v.Extension (𝓞 L)) :
    ρbar K L v ϖ hϖ hv (Ideal.Quotient.mk _ x) w = IsLocalRing.residue _ (ρw K L v w x) := rfl

theorem ρbar_injective : Function.Injective (ρbar K L v ϖ hϖ hv) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.eq_zero_iff_mem]

  have hdiv : ∀ w, ∃ y : w.1.adicCompletionIntegers L, ρw K L v w x = ρw K L v w (ιv K L v ϖ) * y := by
    intro w
    have hw := congrFun hx w
    rw [ρbar_mk, Pi.zero_apply, IsLocalRing.residue_eq_zero_iff, maximalIdeal_eq_span_ρw K L v ϖ hϖ hv w,
      Ideal.mem_span_singleton'] at hw
    obtain ⟨y, hy⟩ := hw
    exact ⟨y, by rw [← hy, mul_comm]⟩
  choose y hy using hdiv
  obtain ⟨x', hx'⟩ := exists_ρw_eq K L v y
  have : x = ιv K L v ϖ * x' := by
    apply eq_of_forall_ρw_eq K L v
    intro w
    rw [map_mul, hx', hy]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

include hϖ hv in

theorem isReduced_Obar : IsReduced (Obar K L v ϖ) :=
  isReduced_of_injective (ρbar K L v ϖ hϖ hv) (ρbar_injective K L v ϖ hϖ hv)

end Residual
section Dbar

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) (t n : Ov K v) (ϖ : Ov K v)

abbrev Dbar := Dq K L v t n ⧸ Ideal.span {ϖD K L v t n ϖ}

theorem span_ϖD_eq_map :
    Ideal.span {ϖD K L v t n ϖ} = (Ideal.span {ιv K L v ϖ}).map (AdjoinRoot.of (fO K L v t n)) := by
  rw [Ideal.map_span, Set.image_singleton]; rfl

theorem finite_Dbar (hϖ : IsLocalRing.maximalIdeal (Ov K v) = Ideal.span {ϖ}) : Finite (Dbar K L v t n ϖ) := by
  classical

  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := Ov K v) (M := Dq K L v t n)
  haveI : Finite (IsLocalRing.ResidueField (Ov K v)) :=
    IsDedekindDomain.HeightOneSpectrum.finite_residueField_adicCompletionIntegers K v
  let Φ : (Fin m → IsLocalRing.ResidueField (Ov K v)) → Dbar K L v t n ϖ := fun c =>
    Ideal.Quotient.mk _ (∑ i, (Quotient.out (c i) : Ov K v) • g i)
  refine Finite.of_surjective Φ fun x => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx : x ∈ Submodule.span (Ov K v) (Set.range g) := by rw [hg]; exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (Ov K v)).1 hx
  refine ⟨fun i => IsLocalRing.residue _ (c i), ?_⟩
  simp only [Φ]
  rw [Ideal.Quotient.eq, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← sub_smul]

  have hmem : (Quotient.out (IsLocalRing.residue (Ov K v) (c i)) : Ov K v) - c i ∈ Ideal.span {ϖ} := by
    rw [← hϖ, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact Quotient.out_eq _
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hmem
  rw [← hd, mul_comm, mul_smul, Algebra.smul_def ϖ]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

variable (hϖ : Valued.v ((ϖ : Ov K v) : Kv K v) = Multiplicative.ofAdd (-1 : ℤ))
  (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
    Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)

include hϖ hv in

theorem isReduced_Dbar (hdisc : IsUnit (t ^ 2 - 4 * n)) : IsReduced (Dbar K L v t n ϖ) := by
  haveI := isReduced_Obar K L v ϖ hϖ hv
  let π : O K L v →+* Obar K L v ϖ := Ideal.Quotient.mk _
  have hred : IsReduced (AdjoinRoot (X ^ 2 - C (π (ιv K L v t)) * X + C (π (ιv K L v n)) : (Obar K L v ϖ)[X])) := by
    apply AdjoinRoot.isReduced_of_isReduced_of_isUnit_sq_sub_four_mul
    have := (hdisc.map (ιv K L v)).map π
    simpa [map_ofNat] using this
  have hmap : (fO K L v t n).map π = X ^ 2 - C (π (ιv K L v t)) * X + C (π (ιv K L v n)) := by
    simp [fO, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul]

  let e₁ : Dbar K L v t n ϖ ≃+* Dq K L v t n ⧸ (Ideal.span {ιv K L v ϖ}).map (AdjoinRoot.of (fO K L v t n)) :=
    Ideal.quotEquivOfEq (span_ϖD_eq_map K L v t n ϖ)
  let e₂ := (AdjoinRoot.quotEquivQuotMap (fO K L v t n) (Ideal.span {ιv K L v ϖ})).toRingEquiv
  have e₃ : (Dq K L v t n ⧸ (Ideal.span {ιv K L v ϖ}).map (AdjoinRoot.of (fO K L v t n))) ≃+*
      AdjoinRoot (X ^ 2 - C (π (ιv K L v t)) * X + C (π (ιv K L v n)) : (Obar K L v ϖ)[X]) := by
    rw [← hmap]; exact e₂
  exact isReduced_of_injective (e₃.toRingHom.comp e₁.toRingHom)
    (e₃.injective.comp e₁.injective)

def τbar (m : ℕ) (hm : 0 < m) (hσm : σ ^ m = 1) : Dbar K L v t n ϖ ≃+* Dbar K L v t n ϖ :=
  Ideal.quotientEquiv _ _ (τEquiv K L v σ t n m hm hσm) (by
    rw [Ideal.map_span, Set.image_singleton]
    change _ = Ideal.span {τ K L v σ t n (ϖD K L v t n ϖ)}
    rw [τ_ϖD])

theorem τbar_mk (m : ℕ) (hm : 0 < m) (hσm : σ ^ m = 1) (z : Dq K L v t n) :
    τbar K L v σ t n ϖ m hm hσm (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ (τ K L v σ t n z) :=
  Ideal.quotientEquiv_mk _ _ _ _ z

theorem τbar_pow_mk (m : ℕ) (hm : 0 < m) (hσm : σ ^ m = 1) (i : ℕ) (z : Dq K L v t n) :
    (τbar K L v σ t n ϖ m hm hσm ^ i) (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ ((τ K L v σ t n)^[i] z) := by
  induction i generalizing z with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ, RingAut.mul_apply, τbar_mk, ih, ← Function.iterate_succ_apply]

theorem τbar_pow_eq_one (m : ℕ) (hm : 0 < m) (hσm : σ ^ m = 1) : τbar K L v σ t n ϖ m hm hσm ^ m = 1 := by
  apply RingEquiv.ext
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [τbar_pow_mk, τ_iterate_eq_self K L v σ t n m hσm]
  rfl

def toDbar : 𝓞 L →+* Dbar K L v t n ϖ :=
  ((Ideal.Quotient.mk _).comp (AdjoinRoot.of (fO K L v t n))).comp (algebraMap (𝓞 L) (O K L v))

theorem toDbar_apply (b : 𝓞 L) :
    toDbar K L v t n ϖ b = Ideal.Quotient.mk _ (AdjoinRoot.of (fO K L v t n) (algebraMap (𝓞 L) (O K L v) b)) := rfl

theorem τbar_toDbar (m : ℕ) (hm : 0 < m) (hσm : σ ^ m = 1) (b : 𝓞 L) :
    τbar K L v σ t n ϖ m hm hσm (toDbar K L v t n ϖ b) = toDbar K L v t n ϖ (σ • b) := by
  rw [toDbar_apply, τbar_mk, τ_of, sO_algebraMap]; rfl

theorem toDbar_algebraMap_eq_zero (hϖm : IsLocalRing.maximalIdeal (Ov K v) = Ideal.span {ϖ})
    (r : 𝓞 K) (hr : r ∈ v.asIdeal) : toDbar K L v t n ϖ (algebraMap (𝓞 K) (𝓞 L) r) = 0 := by
  rw [toDbar_apply, algebraMap_algebraMap_eq_ιv, Ideal.Quotient.eq_zero_iff_mem]
  have hr' : algebraMap (𝓞 K) (Ov K v) r ∈ Ideal.span {ϖ} := by
    rw [← hϖm]
    exact (Ideal.mem_of_liesOver (P := v.completionIdeal K) (p := v.asIdeal) r).1 hr
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hr'
  rw [← hc, map_mul, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

include hv in

theorem exists_τbar_sub_notMem (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)
    (hσm : σ ^ Module.finrank K L = 1)
    (hϖm : IsLocalRing.maximalIdeal (Ov K v) = Ideal.span {ϖ})
    (M : Ideal (Dbar K L v t n ϖ)) (hM : M.IsMaximal) :
    ∃ x, τbar K L v σ t n ϖ _ hdeg.pos hσm x - x ∉ M := by
  by_contra hcon
  push Not at hcon
  haveI := hM
  haveI : IsGalois K L := isGalois_of_prime hdeg σ hσ

  let χ : 𝓞 L →+* Dbar K L v t n ϖ ⧸ M := (Ideal.Quotient.mk M).comp (toDbar K L v t n ϖ)
  let P : Ideal (𝓞 L) := RingHom.ker χ
  haveI hPprime : P.IsPrime := RingHom.ker_isPrime χ
  have hvP : ∀ r ∈ v.asIdeal, algebraMap (𝓞 K) (𝓞 L) r ∈ P := fun r hr => by
    change χ _ = 0
    rw [RingHom.comp_apply, toDbar_algebraMap_eq_zero K L v t n ϖ hϖm r hr, map_zero]
  have hPne : P ≠ ⊥ := by
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hP
    have h1 := hvP r hr
    rw [hP, Ideal.mem_bot, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))] at h1
    exact hr0 h1
  let w : HeightOneSpectrum (𝓞 L) := ⟨P, hPprime, hPne⟩
  have hw : HeightOneSpectrum.under (𝓞 K) w = v := by
    apply HeightOneSpectrum.ext
    change P.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal
    refine (v.isMaximal.eq_of_le ?_ fun r hr => hvP r hr).symm
    exact Ideal.comap_ne_top _ hPprime.ne_top

  have hσP : ∀ b : 𝓞 L, σ • b - b ∈ w.asIdeal := by
    intro b
    change χ (σ • b - b) = 0
    rw [map_sub, sub_eq_zero, RingHom.comp_apply, RingHom.comp_apply, ← τbar_toDbar K L v σ t n ϖ _ hdeg.pos hσm,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hcon _
  exact hσ (eq_one_of_forall_smul_sub_mem w (hv w hw) σ hσP)

end Dbar
section Final

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) (t n : Ov K v) (ϖ : Ov K v)
  (hϖ : Valued.v ((ϖ : Ov K v) : Kv K v) = Multiplicative.ofAdd (-1 : ℤ))
  (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
    Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
  (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

include hϖ hv hdeg hσ in

theorem exists_isUnit_prod_iterate_eq (hdisc : IsUnit (t ^ 2 - 4 * n))
    (c : Dq K L v t n) (hc : IsUnit c) (hτc : τ K L v σ t n c = c) :
    ∃ u : Dq K L v t n, IsUnit u ∧ (∏ i ∈ Finset.range (Module.finrank K L), (τ K L v σ t n)^[i] u) = c := by
  have hσm : σ ^ Module.finrank K L = 1 := pow_finrank_eq_one_of_prime hdeg σ hσ
  have hϖm : IsLocalRing.maximalIdeal (Ov K v) = Ideal.span {ϖ} :=
    HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer K v hϖ
  have hϖ0 : ϖ ≠ 0 := HeightOneSpectrum.adicCompletion.uniformizer_ne_zero hϖ
  haveI := isAdicComplete_Dq K L v t n ϖ hϖm
  haveI := finite_Dbar K L v t n ϖ hϖm
  haveI := isReduced_Dbar K L v t n ϖ hϖ hv hdisc
  set ℓ := Module.finrank K L with hℓ
  let τb := τbar K L v σ t n ϖ ℓ hdeg.pos hσm
  have hτbℓ : τb ^ ℓ = 1 := τbar_pow_eq_one K L v σ t n ϖ ℓ hdeg.pos hσm
  have hmax := exists_τbar_sub_notMem K L v σ t n ϖ hv hdeg hσ hσm hϖm
  refine IsAdicComplete.exists_isUnit_prod_iterate_eq_of_forall_isUnit_exists_sub_mem_span_singleton
    (ϖD K L v t n ϖ) (ϖD_mem_nonZeroDivisors K L v t n ϖ hϖ0) (τ K L v σ t n) ℓ
    (τ_iterate_eq_self K L v σ t n ℓ hσm) (τ_ϖD K L v σ t n ϖ) ?_ ?_ c hc hτc
  ·
    obtain ⟨xb, hxb⟩ := Finite.exists_sum_pow_apply_eq_of_isReduced_of_prime τb ℓ hdeg hτbℓ
      (fun M hM _ => hmax M hM) 1 (map_one τb)
    obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective xb
    refine ⟨x₀, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_sum, sub_eq_zero, ← hxb]
    exact Finset.sum_congr rfl fun i _ => (τbar_pow_mk K L v σ t n ϖ ℓ hdeg.pos hσm i x₀).symm
  ·
    intro d hd hτd
    obtain ⟨ub, hub, hNub⟩ := Finite.exists_isUnit_prod_pow_apply_eq_of_isReduced_of_prime τb ℓ hdeg hτbℓ
      (fun M hM _ => hmax M hM) (Ideal.Quotient.mk _ d) (hd.map _)
      (by change τb (Ideal.Quotient.mk _ d) = _; rw [τbar_mk, hτd])
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective ub
    refine ⟨u, ?_, ?_⟩
    ·
      obtain ⟨wb, hwb⟩ := hub.exists_right_inv
      obtain ⟨w', rfl⟩ := Ideal.Quotient.mk_surjective wb
      rw [← map_mul, ← (Ideal.Quotient.mk _).map_one, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hwb
      have hj := IsAdicComplete.le_jacobson_bot (Ideal.span {ϖD K L v t n ϖ}) hwb
      rw [Ideal.mem_jacobson_bot] at hj
      have h1 := hj 1
      rw [mul_one, sub_add_cancel] at h1
      exact isUnit_of_mul_isUnit_left h1
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_prod, ← hNub]
      exact Finset.prod_congr rfl fun i _ => (τbar_pow_mk K L v σ t n ϖ ℓ hdeg.pos hσm i u).symm

end Final

theorem exists_normString_eq_toTensorGL
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : γ ∈ AutomorphicForm.localIntegralSet K v)
    (hdisc : Valued.v (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1) :
    ∃ δ ∈ AutomorphicForm.semiLocalIntegralSet K L v,
      AutomorphicForm.normString K L (v.adicCompletion K) σ δ =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) γ := by
  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.adicCompletion.exists_uniformizer K v
  obtain ⟨u, hu, hN⟩ := exists_isUnit_prod_iterate_eq K L v σ (tγ K v γ hγ) (nγ K v γ hγ) ϖ hϖ hv hdeg hσ
    (isUnit_disc K v γ hγ hdisc) (AdjoinRoot.root _)
    (isUnit_root K L v _ _ (isUnit_nγ K v γ hγ)) (τ_root K L v σ _ _)
  exact exists_delta K L v σ γ hγ u hu hN

end KIN
p2m_reactivate "P2MW.S_AutomorphicForm_exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime.KIN"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime.KIN"

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : γ ∈ AutomorphicForm.localIntegralSet K v)
    (hdisc : Valued.v (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1) :
    ∃ δ ∈ AutomorphicForm.semiLocalIntegralSet K L v,
      AutomorphicForm.normString K L (v.adicCompletion K) σ δ =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) γ :=
  KIN.exists_normString_eq_toTensorGL K L hdeg σ hσ v hv γ hγ hdisc

end S_AutomorphicForm_exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime
end P2MW
export P2MW.S_AutomorphicForm_exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime (solution)
