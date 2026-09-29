-- Prove2me | solution 1 for AutomorphicForm.exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e20d4c51-7a7e-5c6b-8d84-426cbb0dd608

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm

open scoped nonZeroDivisors

noncomputable section

namespace CritSol

variable {F : Type} [Field F] [NumberField F]

private theorem valued_eq_exp_neg (v : HeightOneSpectrum (𝓞 F))
    (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    Valued.v ((δ : FiniteAdeleRing (𝓞 F) F) v) = WithZero.exp (-finIdeleExponentAt F v δ) := by
  have hne : Valued.v ((δ : FiniteAdeleRing (𝓞 F) F) v) ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    intro h
    have : ((δ * δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = 1 := by
      rw [mul_inv_cancel, Units.val_one, coe_one_apply]
    rw [Units.val_mul, coe_mul_apply, h, zero_mul] at this
    exact zero_ne_one this
  rw [finIdeleExponentAt, neg_neg, WithZero.exp_log hne]

private theorem count_spanSingleton_mk' (v : HeightOneSpectrum (𝓞 F)) {n : 𝓞 F} (hn : n ≠ 0)
    (d : (𝓞 F)⁰) :
    FractionalIdeal.count F v (FractionalIdeal.spanSingleton (𝓞 F)⁰ (IsLocalization.mk' F n d)) =
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n} : Ideal (𝓞 F))).factors : ℤ)
        - (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F))).factors := by
  classical
  have hd : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hspan : FractionalIdeal.spanSingleton (𝓞 F)⁰ (IsLocalization.mk' F n d) =
      ((Ideal.span {n} : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) *
        (((Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F))⁻¹ := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_inv, FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsFractionRing.mk'_eq_div, div_eq_mul_inv]
  have hn' : ((Ideal.span {n} : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [ne_eq, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]; exact hn
  have hd' : ((Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [ne_eq, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]; exact hd
  rw [hspan, FractionalIdeal.count_mul F v hn' (inv_ne_zero hd'), FractionalIdeal.count_inv,
    FractionalIdeal.count_coe F v
      (by rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hn :
        (Ideal.span {n} : Ideal (𝓞 F)) ≠ 0),
    FractionalIdeal.count_coe F v
      (by rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd :
        (Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F)) ≠ 0), sub_eq_add_neg]

private theorem valued_algebraMap_mk' (v : HeightOneSpectrum (𝓞 F)) {n : 𝓞 F} (hn : n ≠ 0)
    (d : (𝓞 F)⁰) :
    Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (IsLocalization.mk' F n d)) v) =
      WithZero.exp (-(((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {n} : Ideal (𝓞 F))).factors : ℤ)
        - (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F))).factors)) := by
  have hd : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  rw [FiniteAdeleRing.algebraMap_apply, valuedAdicCompletion_eq_valuation', valuation_of_mk',
    intValuation_if_neg _ hn, intValuation_if_neg _ hd, ← WithZero.exp_sub]
  congr 1
  ring

private theorem exists_eq_algebraMap_mul_of_contentHomFin_eq_one
    (x : (FiniteAdeleRing (𝓞 F) F)ˣ) (hx : contentHomFin F x = 1) :
    ∃ (k : F) (hk : k ≠ 0) (u : (FiniteAdeleRing (𝓞 F) F)ˣ),
      x = Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 k hk) * u ∧
      ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
  classical
  rw [contentHomFin_apply, ClassGroup.mk_eq_one_iff, Units.val_mk0,
    FractionalIdeal.isPrincipal_iff] at hx
  obtain ⟨k, hk⟩ := hx
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hk
    exact finAssocFracIdeal_ne_zero F x hk
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (𝓞 F)⁰ k
  have hn : n ≠ 0 := by
    rintro rfl
    rw [IsLocalization.mk'_zero] at hnd
    exact hk0 hnd.symm
  set kU : (FiniteAdeleRing (𝓞 F) F)ˣ :=
    Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 k hk0) with hkU
  refine ⟨k, hk0, kU⁻¹ * x, by rw [mul_inv_cancel_left], fun v => ?_⟩

  have hex : finIdeleExponentAt F v x =
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n} : Ideal (𝓞 F))).factors : ℤ)
        - (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F))).factors := by
    rw [← count_finAssocFracIdeal, hk, ← hnd, count_spanSingleton_mk' v hn d]
  have hkv : Valued.v (((kU⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) *
      Valued.v ((kU : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
    rw [← map_mul, ← coe_mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      coe_one_apply, map_one]
  have hkval : Valued.v ((kU : FiniteAdeleRing (𝓞 F) F) v) =
      WithZero.exp (-(((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {n} : Ideal (𝓞 F))).factors : ℤ)
        - (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F))).factors)) := by
    rw [hkU]
    show Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) k) v) = _
    rw [← hnd]
    exact valued_algebraMap_mk' v hn d
  rw [Units.val_mul, coe_mul_apply, map_mul, valued_eq_exp_neg v x, hex]
  rw [hkval] at hkv

  set e : ℤ := ((Associates.mk v.asIdeal).count
      (Associates.mk (Ideal.span {n} : Ideal (𝓞 F))).factors : ℤ)
    - (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F))).factors with he
  have hinv : Valued.v (((kU⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) =
      WithZero.exp e := by
    have h2 : WithZero.exp (-e) ≠ (0 : WithZero (Multiplicative ℤ)) := WithZero.exp_ne_zero
    calc Valued.v (((kU⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v)
        = Valued.v (((kU⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) *
            WithZero.exp (-e) * (WithZero.exp (-e))⁻¹ := by rw [mul_inv_cancel_right₀ h2]
      _ = (WithZero.exp (-e))⁻¹ := by rw [hkv, one_mul]
      _ = WithZero.exp e := by rw [WithZero.exp_neg, inv_inv]
  rw [hinv, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

private theorem mem_integers_of_valued_eq_one {u : (FiniteAdeleRing (𝓞 F) F)ˣ}
    (hu : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v) = 1)
    (v : HeightOneSpectrum (𝓞 F)) :
    (u : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F ∧
      ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v
        ∈ v.adicCompletionIntegers F := by
  have hprod : Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v) *
      Valued.v (((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
    rw [← map_mul, ← coe_mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      coe_one_apply, map_one]
  rw [hu v, one_mul] at hprod
  rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers, hu v, hprod]
  exact ⟨le_rfl, le_rfl⟩

private theorem glFin_globalPoints_eq_map (γ : GL (Fin 2) F) :
    glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) =
      Matrix.GeneralLinearGroup.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) γ :=
  Units.ext (Matrix.ext fun i j => AutomorphicForm.SiegelReduction.glFin_globalPoints_apply F γ i j)

private theorem glFin_finIdeleDiag (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    glFin (𝓞 F) F (finIdeleDiag F δ) = diagOne δ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> rfl

private theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal ![(a : A), 1]).det = a
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem mem_integral_of_forall_valued_le {x : FiniteAdeleRing (𝓞 F) F}
    (hx : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (x v) ≤ 1) :
    x ∈ integralFiniteAdeles (𝓞 F) F :=
  fun v => (mem_adicCompletionIntegers _ _ _).mpr (hx v)

private theorem neg_mem_integral {x : FiniteAdeleRing (𝓞 F) F}
    (hx : x ∈ integralFiniteAdeles (𝓞 F) F) : -x ∈ integralFiniteAdeles (𝓞 F) F := by
  have h := sub_mem_integralFiniteAdeles zero_mem_integralFiniteAdeles hx
  rwa [zero_sub] at h

private theorem unit_mem_integral {u : (FiniteAdeleRing (𝓞 F) F)ˣ}
    (hu : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v) = 1) :
    (u : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F :=
  fun v => (mem_integers_of_valued_eq_one hu v).1

private theorem unit_inv_mem_integral {u : (FiniteAdeleRing (𝓞 F) F)ˣ}
    (hu : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v) = 1) :
    ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F :=
  fun v => (mem_integers_of_valued_eq_one hu v).2

private theorem ne_zero_of_valued_eq_one {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F}
    (hx : Valued.v x = 1) : x ≠ 0 := by
  rintro rfl
  rw [map_zero] at hx
  exact zero_ne_one hx

open scoped Classical in
private theorem exists_unimodular_splitting (c₀ d₀ : FiniteAdeleRing (𝓞 F) F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), max (Valued.v (c₀ v)) (Valued.v (d₀ v)) = 1) :
    ∃ σ τ : FiniteAdeleRing (𝓞 F) F, σ ∈ integralFiniteAdeles (𝓞 F) F ∧
      τ ∈ integralFiniteAdeles (𝓞 F) F ∧ σ * c₀ + τ * d₀ = 1 := by

  have hc : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (d₀ v) ≠ 1 → Valued.v (c₀ v) = 1 := by
    intro v hv
    rcases le_total (Valued.v (c₀ v)) (Valued.v (d₀ v)) with hle | hle
    · exact absurd (by rw [← h v, max_eq_right hle]) hv
    · rw [← h v, max_eq_left hle]

  have hσint : ∀ v : HeightOneSpectrum (𝓞 F),
      (if Valued.v (d₀ v) = 1 then (0 : v.adicCompletion F) else (c₀ v)⁻¹)
        ∈ v.adicCompletionIntegers F := by
    intro v
    split_ifs with hv
    · exact zero_mem _
    · rw [mem_adicCompletionIntegers, map_inv₀, hc v hv, inv_one]
  have hτint : ∀ v : HeightOneSpectrum (𝓞 F),
      (if Valued.v (d₀ v) = 1 then (d₀ v)⁻¹ else (0 : v.adicCompletion F))
        ∈ v.adicCompletionIntegers F := by
    intro v
    split_ifs with hv
    · rw [mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
    · exact zero_mem _
  refine ⟨⟨fun v => if Valued.v (d₀ v) = 1 then 0 else (c₀ v)⁻¹,
      Filter.Eventually.of_forall hσint⟩,
    ⟨fun v => if Valued.v (d₀ v) = 1 then (d₀ v)⁻¹ else 0,
      Filter.Eventually.of_forall hτint⟩, hσint, hτint, ?_⟩
  refine Subtype.ext (funext fun v => ?_)
  show (if Valued.v (d₀ v) = 1 then (0 : v.adicCompletion F) else (c₀ v)⁻¹) * c₀ v +
      (if Valued.v (d₀ v) = 1 then (d₀ v)⁻¹ else (0 : v.adicCompletion F)) * d₀ v = 1
  split_ifs with hv
  · rw [zero_mul, zero_add, inv_mul_cancel₀ (ne_zero_of_valued_eq_one hv)]
  · rw [zero_mul, add_zero, inv_mul_cancel₀ (ne_zero_of_valued_eq_one (hc v hv))]

private theorem mem_finiteIntegralGL2_of_coe_eq (n : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    (p q r t : FiniteAdeleRing (𝓞 F) F)
    (hn : (n : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) = !![p, q; r, t])
    (hp : p ∈ integralFiniteAdeles (𝓞 F) F) (hq : q ∈ integralFiniteAdeles (𝓞 F) F)
    (hr : r ∈ integralFiniteAdeles (𝓞 F) F) (ht : t ∈ integralFiniteAdeles (𝓞 F) F)
    (u : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v) = 1)
    (hdet : p * t - q * r = u) : n ∈ finiteIntegralGL2 (𝓞 F) F := by
  have hui := unit_inv_mem_integral hu
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j
    rw [hn]
    fin_cases i <;> fin_cases j
    · simpa using hp
    · simpa using hq
    · simpa using hr
    · simpa using ht
  · intro i j
    rw [Matrix.GeneralLinearGroup.coe_inv, hn, Matrix.inv_def, Matrix.det_fin_two_of, hdet,
      Ring.inverse_unit, Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · simpa using mul_mem_integralFiniteAdeles hui ht
    · simpa using mul_mem_integralFiniteAdeles hui (neg_mem_integral hq)
    · simpa using mul_mem_integralFiniteAdeles hui (neg_mem_integral hr)
    · simpa using mul_mem_integralFiniteAdeles hui hp

omit [NumberField F] in
private theorem coe_mkB (α μ δ : F) (h : Matrix.det !![α, μ; 0, δ] ≠ 0) :
    ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![α, μ; 0, δ] h : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![α, μ; 0, δ] := rfl

private theorem coe_glFin_globalPoints_mkB (α μ δ : F) (h : Matrix.det !![α, μ; 0, δ] ≠ 0) :
    ((glFin (𝓞 F) F (globalPoints (𝓞 F) F
        (Matrix.GeneralLinearGroup.mkOfDetNeZero !![α, μ; 0, δ] h)) :
          GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) =
      !![algebraMap F (FiniteAdeleRing (𝓞 F) F) α, algebraMap F (FiniteAdeleRing (𝓞 F) F) μ;
         0, algebraMap F (FiniteAdeleRing (𝓞 F) F) δ] := by
  refine Matrix.ext fun i j => ?_
  rw [AutomorphicForm.SiegelReduction.glFin_globalPoints_apply, coe_mkB]
  fin_cases i <;> fin_cases j <;> simp

private theorem coe_scalar (s : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) s : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) =
      Matrix.scalar (Fin 2) (s : FiniteAdeleRing (𝓞 F) F) := rfl

private theorem coe_diagOne_inv (a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (((diagOne a)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) =
      Matrix.diagonal ![((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F), 1] := by
  rw [← map_inv]
  exact Matrix.ext fun i j => diagOne_coe_apply _ i j

private theorem coe_assembled (α μ δ : F) (h : Matrix.det !![α, μ; 0, δ] ≠ 0)
    (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) (s a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ((glFin (𝓞 F) F (globalPoints (𝓞 F) F
          (Matrix.GeneralLinearGroup.mkOfDetNeZero !![α, μ; 0, δ] h)) * g *
        Matrix.GeneralLinearGroup.scalar (Fin 2) s * (glFin (𝓞 F) F (finIdeleDiag F a))⁻¹ :
          GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) =
      !![(algebraMap F (FiniteAdeleRing (𝓞 F) F) α *
              (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 +
            algebraMap F (FiniteAdeleRing (𝓞 F) F) μ *
              (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0) *
            (s : FiniteAdeleRing (𝓞 F) F) *
            ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F),
          (algebraMap F (FiniteAdeleRing (𝓞 F) F) α *
              (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1 +
            algebraMap F (FiniteAdeleRing (𝓞 F) F) μ *
              (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1) *
            (s : FiniteAdeleRing (𝓞 F) F);
          algebraMap F (FiniteAdeleRing (𝓞 F) F) δ *
              (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
            (s : FiniteAdeleRing (𝓞 F) F) *
            ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F),
          algebraMap F (FiniteAdeleRing (𝓞 F) F) δ *
              (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
            (s : FiniteAdeleRing (𝓞 F) F)] := by
  rw [glFin_finIdeleDiag, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul, coe_glFin_globalPoints_mkB, coe_scalar, coe_diagOne_inv]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.scalar_apply] <;> ring

private theorem crit (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    (a d : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hd : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v ((d : FiniteAdeleRing (𝓞 F) F) v) =
        max
          (Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
            ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) v))
          (Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1) v)))
    (hcls : contentHomFin F a * contentHomFin F d ^ 2 =
      contentHomFin F (Matrix.GeneralLinearGroup.det g)) :
    ∃ b : GL (Fin 2) F, (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ∃ s : (FiniteAdeleRing (𝓞 F) F)ˣ,
        glFin (𝓞 F) F (globalPoints (𝓞 F) F b) * g * Matrix.GeneralLinearGroup.scalar (Fin 2) s *
          (glFin (𝓞 F) F (finIdeleDiag F a))⁻¹ ∈ finiteIntegralGL2 (𝓞 F) F := by

  obtain ⟨s, hs⟩ := contentHomFin_surjective F (contentHomFin F d)⁻¹

  have h1 : contentHomFin F (s * d) = 1 := by rw [map_mul, hs, inv_mul_cancel]
  obtain ⟨k₂, hk₂, u₂, hsd, hu₂⟩ := exists_eq_algebraMap_mul_of_contentHomFin_eq_one (s * d) h1
  have h2 : contentHomFin F (s * s * Matrix.GeneralLinearGroup.det g * a⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hs, ← hcls, ← sq, inv_pow,
      mul_comm (contentHomFin F a) (contentHomFin F d ^ 2), ← mul_assoc, inv_mul_cancel, one_mul,
      mul_inv_cancel]
  obtain ⟨k₁, hk₁, u₁, hdet, hu₁⟩ :=
    exists_eq_algebraMap_mul_of_contentHomFin_eq_one (s * s * Matrix.GeneralLinearGroup.det g * a⁻¹) h2

  have E1 : (s : FiniteAdeleRing (𝓞 F) F) * d = algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂ * u₂ := by
    have := congrArg Units.val hsd
    simpa using this
  have E2 : (s : FiniteAdeleRing (𝓞 F) F) * s *
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 *
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 -
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1 *
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0) *
      ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) k₁ * u₁ := by
    have := congrArg Units.val hdet
    simpa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] using this

  have hdd : (d : FiniteAdeleRing (𝓞 F) F) *
      ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = 1 := Units.mul_inv d
  have huu : (u₂ : FiniteAdeleRing (𝓞 F) F) *
      ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = 1 := Units.mul_inv u₂
  have hδ' : algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ *
      algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂ = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hk₂, map_one]
  have hαδk : algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) *
      algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ * algebraMap F (FiniteAdeleRing (𝓞 F) F) k₁ = 1 := by
    rw [← map_mul, ← map_mul, show k₂ / k₁ * k₂⁻¹ * k₁ = 1 by field_simp, map_one]

  have hdv : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) =
        (Valued.v ((d : FiniteAdeleRing (𝓞 F) F) v))⁻¹ := by
    intro v
    have hprod : Valued.v ((d : FiniteAdeleRing (𝓞 F) F) v) *
        Valued.v (((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
      rw [← map_mul, ← coe_mul_apply, hdd, coe_one_apply, map_one]
    exact eq_inv_of_mul_eq_one_right hprod
  have hdne : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((d : FiniteAdeleRing (𝓞 F) F) v) ≠ 0 := by
    intro v
    rw [valued_eq_exp_neg]
    exact WithZero.exp_ne_zero
  have hcd : ∀ v : HeightOneSpectrum (𝓞 F),
      max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
            ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
            ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) v))
        (Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
            ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) v)) = 1 := by
    intro v
    have e₁ : Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
          ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
          ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) v) =
        Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
          ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) v) *
          (Valued.v ((d : FiniteAdeleRing (𝓞 F) F) v))⁻¹ := by
      rw [coe_mul_apply, map_mul, hdv v]
    have e₂ : Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
          ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) v) =
        Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1) v) *
          (Valued.v ((d : FiniteAdeleRing (𝓞 F) F) v))⁻¹ := by
      rw [coe_mul_apply, map_mul, hdv v]
    rw [e₁, e₂]
    have hm := hd v
    have hne := hdne v
    rcases le_total
        (Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
          ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) v))
        (Valued.v (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1) v)) with hle | hle
    · rw [max_eq_right hle] at hm
      rw [← hm] at hle ⊢
      rw [mul_inv_cancel₀ hne]
      exact max_eq_right ((mul_le_mul_left hle _).trans_eq (mul_inv_cancel₀ hne))
    · rw [max_eq_left hle] at hm
      rw [← hm] at hle ⊢
      rw [mul_inv_cancel₀ hne]
      exact max_eq_left ((mul_le_mul_left hle _).trans_eq (mul_inv_cancel₀ hne))
  obtain ⟨σ, τ, hσ, hτ, hστ⟩ := exists_unimodular_splitting _ _ hcd
  have hc₀ : (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
      ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
      ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F :=
    mem_integral_of_forall_valued_le fun v => (le_max_left _ _).trans (hcd v).le
  have hd₀ : (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
      ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F :=
    mem_integral_of_forall_valued_le fun v => (le_max_right _ _).trans (hcd v).le

  set c₀ : FiniteAdeleRing (𝓞 F) F := (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
      ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
      ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) with hc₀e
  set d₀ : FiniteAdeleRing (𝓞 F) F := (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
      ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) with hd₀e
  set Y₁ : FiniteAdeleRing (𝓞 F) F := algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) *
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 *
      ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * (s : FiniteAdeleRing (𝓞 F) F) *
      ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) with hY₁e
  set Y₂ : FiniteAdeleRing (𝓞 F) F := algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) *
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1 * (s : FiniteAdeleRing (𝓞 F) F) *
      ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) with hY₂e

  obtain ⟨ν, hν⟩ := NumberField.AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F
    (σ * Y₁ + τ * Y₂)
  have hμ : algebraMap F (FiniteAdeleRing (𝓞 F) F) (ν / k₂) * algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂ =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) ν := by
    rw [← map_mul, div_mul_cancel₀ ν hk₂]
  have hdetB : Matrix.det !![k₂ / k₁, ν / k₂; 0, k₂⁻¹] ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simp [hk₁, hk₂]

  have hdinv' : algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ * (s : FiniteAdeleRing (𝓞 F) F) *
      ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) =
      ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) := by
    linear_combination (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ * (s : FiniteAdeleRing (𝓞 F) F) *
        ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))) * hdd +
      (((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
        ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹) * E1 +
      (((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * (u₂ : FiniteAdeleRing (𝓞 F) F) *
        ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) * hδ' +
      (((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) * huu
  have hu₁' : (u₁ : FiniteAdeleRing (𝓞 F) F) =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) * algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ *
        ((s : FiniteAdeleRing (𝓞 F) F) * s *
          ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 *
              (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 -
            (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1 *
              (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0) *
          ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) := by
    rw [E2]
    linear_combination (-(u₁ : FiniteAdeleRing (𝓞 F) F)) * hαδk
  have hε : Y₁ * d₀ - Y₂ * c₀ = (u₁ : FiniteAdeleRing (𝓞 F) F) *
      ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
      ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) := by
    rw [hu₁', hY₁e, hY₂e, hc₀e, hd₀e]
    linear_combination (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) * (s : FiniteAdeleRing (𝓞 F) F) *
        ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 *
            (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 -
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1 *
            (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0) *
        ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
        ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))) * hdinv'
  have n10 : algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ *
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 * (s : FiniteAdeleRing (𝓞 F) F) *
        ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) =
      (u₂ : FiniteAdeleRing (𝓞 F) F) * c₀ := by
    rw [hc₀e]
    linear_combination (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ *
        ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
          ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) * (s : FiniteAdeleRing (𝓞 F) F))) * hdd +
      (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
          ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) *
        ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹) * E1 +
      (((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
          ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) *
        ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * (u₂ : FiniteAdeleRing (𝓞 F) F)) * hδ'
  have n11 : algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ *
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 * (s : FiniteAdeleRing (𝓞 F) F) =
      (u₂ : FiniteAdeleRing (𝓞 F) F) * d₀ := by
    rw [hd₀e]
    linear_combination (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹ *
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 * (s : FiniteAdeleRing (𝓞 F) F))) * hdd +
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
        ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) k₂⁻¹) * E1 +
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
        ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * (u₂ : FiniteAdeleRing (𝓞 F) F)) * hδ'
  have n00 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) *
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 +
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (ν / k₂) *
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0) *
        (s : FiniteAdeleRing (𝓞 F) F) * ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) =
      (u₂ : FiniteAdeleRing (𝓞 F) F) * (Y₁ + algebraMap F (FiniteAdeleRing (𝓞 F) F) ν * c₀) := by
    rw [hY₁e, hc₀e]
    linear_combination (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) *
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 * (s : FiniteAdeleRing (𝓞 F) F) *
        ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))) * huu +
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
        ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
        ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * (u₂ : FiniteAdeleRing (𝓞 F) F)) * hμ +
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
        ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (ν / k₂) *
        ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) * E1 +
      (-((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 *
        ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (ν / k₂) * (s : FiniteAdeleRing (𝓞 F) F))) * hdd
  have n01 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) *
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1 +
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (ν / k₂) *
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1) * (s : FiniteAdeleRing (𝓞 F) F) =
      (u₂ : FiniteAdeleRing (𝓞 F) F) * (Y₂ + algebraMap F (FiniteAdeleRing (𝓞 F) F) ν * d₀) := by
    rw [hY₂e, hd₀e]
    linear_combination (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) (k₂ / k₁) *
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1 * (s : FiniteAdeleRing (𝓞 F) F))) * huu +
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
        ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * (u₂ : FiniteAdeleRing (𝓞 F) F)) * hμ +
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (ν / k₂) *
        ((d⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) * E1 +
      (-((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (ν / k₂) * (s : FiniteAdeleRing (𝓞 F) F))) * hdd

  have hu₂i := unit_mem_integral hu₂
  have hεi : Y₁ * d₀ - Y₂ * c₀ ∈ integralFiniteAdeles (𝓞 F) F := by
    rw [hε]
    exact mul_mem_integralFiniteAdeles
      (mul_mem_integralFiniteAdeles (unit_mem_integral hu₁) (unit_inv_mem_integral hu₂))
      (unit_inv_mem_integral hu₂)
  have top1 : Y₁ + algebraMap F (FiniteAdeleRing (𝓞 F) F) ν * c₀ =
      τ * (Y₁ * d₀ - Y₂ * c₀) + (algebraMap F (FiniteAdeleRing (𝓞 F) F) ν + (σ * Y₁ + τ * Y₂)) * c₀ := by
    linear_combination (-Y₁) * hστ
  have top2 : Y₂ + algebraMap F (FiniteAdeleRing (𝓞 F) F) ν * d₀ =
      (-σ) * (Y₁ * d₀ - Y₂ * c₀) + (algebraMap F (FiniteAdeleRing (𝓞 F) F) ν + (σ * Y₁ + τ * Y₂)) * d₀ := by
    linear_combination (-Y₂) * hστ
  have h00 : Y₁ + algebraMap F (FiniteAdeleRing (𝓞 F) F) ν * c₀ ∈ integralFiniteAdeles (𝓞 F) F := by
    rw [top1]
    exact add_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles hτ hεi)
      (mul_mem_integralFiniteAdeles hν hc₀)
  have h01 : Y₂ + algebraMap F (FiniteAdeleRing (𝓞 F) F) ν * d₀ ∈ integralFiniteAdeles (𝓞 F) F := by
    rw [top2]
    exact add_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (neg_mem_integral hσ) hεi)
      (mul_mem_integralFiniteAdeles hν hd₀)
  have hdetL : (u₂ : FiniteAdeleRing (𝓞 F) F) * (Y₁ + algebraMap F (FiniteAdeleRing (𝓞 F) F) ν * c₀) *
        ((u₂ : FiniteAdeleRing (𝓞 F) F) * d₀) -
      (u₂ : FiniteAdeleRing (𝓞 F) F) * (Y₂ + algebraMap F (FiniteAdeleRing (𝓞 F) F) ν * d₀) *
        ((u₂ : FiniteAdeleRing (𝓞 F) F) * c₀) = u₁ := by
    linear_combination ((u₂ : FiniteAdeleRing (𝓞 F) F) * u₂) * hε +
      ((u₁ : FiniteAdeleRing (𝓞 F) F) * ((u₂ : FiniteAdeleRing (𝓞 F) F) *
        ((u₂⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) + 1)) * huu

  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![k₂ / k₁, ν / k₂; 0, k₂⁻¹] hdetB, rfl, s, ?_⟩
  refine mem_finiteIntegralGL2_of_coe_eq _ _ _ _ _ ?_ (mul_mem_integralFiniteAdeles hu₂i h00)
    (mul_mem_integralFiniteAdeles hu₂i h01) (mul_mem_integralFiniteAdeles hu₂i hc₀)
    (mul_mem_integralFiniteAdeles hu₂i hd₀) u₁ hu₁ hdetL
  rw [coe_assembled, n00, n01, n10, n11]

end CritSol

end

theorem solution
    (F : Type) [Field F] [NumberField F]
    (g : Matrix.GeneralLinearGroup (Fin 2)
      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))
    (a d : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ)
    (hd : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      Valued.v ((d : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) v) =
        max
          (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 0 *
              ((a⁻¹ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ) :
                IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v))
          (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 1) v)))
    (hcls : AutomorphicForm.contentHomFin F a * AutomorphicForm.contentHomFin F d ^ 2 =
      AutomorphicForm.contentHomFin F (Matrix.GeneralLinearGroup.det g)) :
    ∃ b : Matrix.GeneralLinearGroup (Fin 2) F, (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ∃ s : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ,
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers F) F
              (AutomorphicForm.globalPoints (NumberField.RingOfIntegers F) F b) * g *
            Matrix.GeneralLinearGroup.scalar (Fin 2) s *
          (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers F) F
            (AutomorphicForm.finIdeleDiag F a))⁻¹
        ∈ NumberField.AdelicLevel.finiteIntegralGL2 (NumberField.RingOfIntegers F) F :=
  CritSol.crit g a d hd hcls

end S_AutomorphicForm_exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2
end P2MW
export P2MW.S_AutomorphicForm_exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2 (solution)
