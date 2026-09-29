-- Prove2me | solution 1 for AutomorphicForm.exists_twistedConj_eq_diagonal_and_norm_eq_of_conj_normString_eq_diagonal_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/888ac4b5-7faa-5715-827a-ce70657d6a75

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_twistedConj_eq_diagonal_and_norm_eq_of_conj_normString_eq_diagonal_of_ne

set_option autoImplicit false

namespace TwistedConjDiag

open Matrix

section General

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem algEquiv_pow_finrank_eq_one (θ : E ≃ₐ[F] E) : θ ^ Module.finrank F E = 1 := by
  rcases Nat.eq_zero_or_pos (Module.finrank F E) with h0 | hpos
  · rw [h0, pow_zero]
  · haveI : FiniteDimensional F E := Module.finite_of_finrank_pos hpos
    apply orderOf_dvd_iff_pow_eq_one.mp
    have h1 : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers θ)) E =
        Nat.card (Subgroup.zpowers θ) := IntermediateField.finrank_fixedField_eq_card _
    have h2 := Module.finrank_mul_finrank F (IntermediateField.fixedField (Subgroup.zpowers θ)) E
    rw [Nat.card_zpowers] at h1
    exact Dvd.intro_left _ (by rw [← h1]; exact h2)

end General

section GroupNorm

variable {G : Type*} [Group G] (φ : G →* G)

def normStr (n : ℕ) (g : G) : G := ((List.range n).map fun i => (⇑φ)^[i] g).prod

theorem normStr_zero (g : G) : normStr φ 0 g = 1 := by simp [normStr]

theorem normStr_succ (n : ℕ) (g : G) : normStr φ (n + 1) g = normStr φ n g * (⇑φ)^[n] g := by
  simp [normStr, List.range_succ]

theorem iterate_map_mul (i : ℕ) (a b : G) : (⇑φ)^[i] (a * b) = (⇑φ)^[i] a * (⇑φ)^[i] b := by
  induction i with
  | zero => simp
  | succ i ih => simp [Function.iterate_succ_apply', ih]

theorem iterate_map_inv (i : ℕ) (a : G) : (⇑φ)^[i] a⁻¹ = ((⇑φ)^[i] a)⁻¹ := by
  induction i with
  | zero => simp
  | succ i ih => simp [Function.iterate_succ_apply', ih]

theorem normStr_twistedConj (n : ℕ) (g x : G) :
    normStr φ n (x⁻¹ * g * φ x) = x⁻¹ * normStr φ n g * (⇑φ)^[n] x := by
  induction n with
  | zero => simp [normStr_zero]
  | succ n ih =>
    rw [normStr_succ, normStr_succ, ih, iterate_map_mul, iterate_map_mul, iterate_map_inv,
      ← Function.iterate_succ_apply (⇑φ) n x]
    group

theorem mul_map_normStr (n : ℕ) (g : G) :
    g * φ (normStr φ n g) = normStr φ n g * (⇑φ)^[n] g := by
  induction n with
  | zero => simp [normStr_zero]
  | succ n ih =>
    rw [normStr_succ, map_mul, ← mul_assoc, ih, ← Function.iterate_succ_apply' (⇑φ) n g]

end GroupNorm

section GLTwo

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem val_glMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin 2) R) :
    ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
      (g : Matrix (Fin 2) (Fin 2) R).map f := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]

theorem map_diag_two {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) R).map f = !![f a, 0; 0, f b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem glMap_pow (θ : E ≃ₐ[F] E) (i : ℕ) (g : GL (Fin 2) E) :
    Matrix.GeneralLinearGroup.map (θ ^ i).toAlgHom.toRingHom g =
      (⇑(Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom))^[i] g := by
  induction i with
  | zero =>
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ← ih]
    ext a b
    simp [Matrix.GeneralLinearGroup.map_apply, pow_succ', AlgEquiv.mul_apply]

theorem normStr_diag_val (θ : E ≃ₐ[F] E) (n : ℕ) (g : GL (Fin 2) E) (a b : E)
    (hg : (g : Matrix (Fin 2) (Fin 2) E) = !![a, 0; 0, b]) :
    ((normStr (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) n g : GL (Fin 2) E) :
        Matrix (Fin 2) (Fin 2) E) =
      !![∏ i ∈ Finset.range n, (θ ^ i) a, 0; 0, ∏ i ∈ Finset.range n, (θ ^ i) b] := by
  induction n with
  | zero =>
    rw [normStr_zero]
    simp [Matrix.one_fin_two]
  | succ n ih =>
    rw [normStr_succ, Units.val_mul, ih, ← glMap_pow, Finset.prod_range_succ,
      Finset.prod_range_succ, val_glMap, hg, map_diag_two]
    simp

theorem main (F E : Type*) [Field F] [Field E] [Algebra F E] (θ : E ≃ₐ[F] E)
    (α β : Fˣ) (hαβ : α ≠ β) (δ y : GL (Fin 2) E)
    (hy : ((y⁻¹ * ((List.range (Module.finrank F E)).map
          fun i : ℕ => Matrix.GeneralLinearGroup.map (θ ^ i).toAlgHom.toRingHom δ).prod * y :
            GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
      !![algebraMap F E (α : F), 0; 0, algebraMap F E (β : F)]) :
    ∃ (x : GL (Fin 2) E) (a b : Eˣ),
      ((x⁻¹ * δ * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x : GL (Fin 2) E) :
          Matrix (Fin 2) (Fin 2) E) = !![(a : E), 0; 0, (b : E)] ∧
      (algebraMap F E (α : F) = ∏ i ∈ Finset.range (Module.finrank F E), (θ ^ i) (a : E)) ∧
      (algebraMap F E (β : F) = ∏ i ∈ Finset.range (Module.finrank F E), (θ ^ i) (b : E)) := by
  classical

  set n := Module.finrank F E with hn
  set φ : GL (Fin 2) E →* GL (Fin 2) E := Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom
    with hφ
  set α' : E := algebraMap F E (α : F) with hα'
  set β' : E := algebraMap F E (β : F) with hβ'
  have hα'β' : α' ≠ β' := fun h => hαβ (Units.ext ((algebraMap F E).injective h))

  have hprod : ((List.range n).map
      fun i : ℕ => Matrix.GeneralLinearGroup.map (θ ^ i).toAlgHom.toRingHom δ).prod =
        normStr φ n δ := by
    unfold normStr
    congr 1
    refine List.map_congr_left fun i _ => ?_
    rw [glMap_pow]
  rw [hprod] at hy

  have hθn : θ ^ n = 1 := algEquiv_pow_finrank_eq_one θ
  have hφn : ∀ g, (⇑φ)^[n] g = g := fun g => by
    rw [hφ, ← glMap_pow, hθn]
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]

  set δ' : GL (Fin 2) E := y⁻¹ * δ * φ y with hδ'
  have hN : normStr φ n δ' = y⁻¹ * normStr φ n δ * y := by
    rw [hδ', normStr_twistedConj, hφn]

  have hND : ((normStr φ n δ' : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) = !![α', 0; 0, β'] := by
    rw [hN]; exact hy

  have hφD : ((φ (normStr φ n δ') : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
      !![α', 0; 0, β'] := by
    rw [hφ, val_glMap, ← hφ, hND, map_diag_two]
    simp [hα', hβ']

  have hcomm : (δ' : Matrix (Fin 2) (Fin 2) E) * !![α', 0; 0, β'] =
      !![α', 0; 0, β'] * (δ' : Matrix (Fin 2) (Fin 2) E) := by
    have h := mul_map_normStr φ n δ'
    rw [hφn] at h
    have h' := congrArg (fun g : GL (Fin 2) E => (g : Matrix (Fin 2) (Fin 2) E)) h
    simp only [Units.val_mul] at h'
    rw [hφD, hND] at h'
    exact h'

  have h01 : (δ' : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 := by
    have h := congrFun (congrFun hcomm 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    have : (β' - α') * (δ' : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hα'β'.symm)
  have h10 : (δ' : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 := by
    have h := congrFun (congrFun hcomm 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    have : (α' - β') * (δ' : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hα'β')

  have hdet : (δ' : Matrix (Fin 2) (Fin 2) E).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp δ'.isUnit).ne_zero
  rw [Matrix.det_fin_two, h01, zero_mul, sub_zero] at hdet
  have ha : (δ' : Matrix (Fin 2) (Fin 2) E) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have hb : (δ' : Matrix (Fin 2) (Fin 2) E) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  have hdiag : (δ' : Matrix (Fin 2) (Fin 2) E) =
      !![(δ' : Matrix (Fin 2) (Fin 2) E) 0 0, 0; 0, (δ' : Matrix (Fin 2) (Fin 2) E) 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [h01, h10]

  refine ⟨y, Units.mk0 _ ha, Units.mk0 _ hb, ?_, ?_⟩
  · rw [Units.val_mk0, Units.val_mk0, ← hdiag]
  · have hv := normStr_diag_val θ n δ' _ _ hdiag
    rw [← hφ, hND] at hv
    have hαv := congrFun (congrFun hv 0) 0
    have hβv := congrFun (congrFun hv 1) 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hαv hβv
    exact ⟨by rw [Units.val_mk0]; exact hαv, by rw [Units.val_mk0]; exact hβv⟩

end GLTwo

end TwistedConjDiag

open NumberField IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (L : Type) [Field L] [NumberField L] [Algebra K L] (w : v.Extension (𝓞 L))
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (α β : (v.adicCompletion K)ˣ) (hαβ : α ≠ β) (δ y : GL (Fin 2) (w.1.adicCompletion L))
    (hy : ((y⁻¹ *
      ((List.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))).map
          fun i : ℕ => Matrix.GeneralLinearGroup.map (θ ^ i).toAlgHom.toRingHom δ).prod *
        y : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      !![algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K), 0;
        0, algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K)]) :
    ∃ (x : GL (Fin 2) (w.1.adicCompletion L)) (a b : (w.1.adicCompletion L)ˣ),
      ((x⁻¹ * δ * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x :
            GL (Fin 2) (w.1.adicCompletion L)) :
          Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
          !![(a : w.1.adicCompletion L), 0; 0, (b : w.1.adicCompletion L)] ∧
        (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (a : w.1.adicCompletion L)) ∧
        (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (b : w.1.adicCompletion L)) :=
  TwistedConjDiag.main (v.adicCompletion K) (w.1.adicCompletion L) θ α β hαβ δ y hy

end S_AutomorphicForm_exists_twistedConj_eq_diagonal_and_norm_eq_of_conj_normString_eq_diagonal_of_ne
end P2MW
export P2MW.S_AutomorphicForm_exists_twistedConj_eq_diagonal_and_norm_eq_of_conj_normString_eq_diagonal_of_ne (solution)
