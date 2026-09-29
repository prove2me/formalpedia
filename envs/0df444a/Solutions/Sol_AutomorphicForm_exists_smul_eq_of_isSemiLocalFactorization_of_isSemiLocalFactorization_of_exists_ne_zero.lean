-- Prove2me | solution 1 for AutomorphicForm.exists_smul_eq_of_isSemiLocalFactorization_of_isSemiLocalFactorization_of_exists_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/63c78305-895e-5d5b-b090-ac44fcc2dac6

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_smul_eq_of_isSemiLocalFactorization_of_isSemiLocalFactorization_of_exists_ne_zero

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

noncomputable section

namespace K51FUL

open AdelicDock

section Arch

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [NumberField K] [Algebra R K]
  [IsFractionRing R K]

def archMat (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing R K) :=
  Matrix.of fun i j => ((g i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j) : AdeleRing R K)

theorem mapMatrix_arch_archMat (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :
    (AdelicLevel.adeleArch R K).mapMatrix (archMat R K g) = g := by
  ext i j
  simp [archMat, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply]

theorem mapMatrix_fin_archMat (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :
    (AdelicLevel.adeleFin R K).mapMatrix (archMat R K g) = 1 := by
  ext i j
  simp [archMat, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply]

theorem archMat_one : archMat R K 1 = 1 :=
  matrix_eq_of_mapMatrix_arch_fin_eq R K (by rw [mapMatrix_arch_archMat, map_one])
    (by rw [mapMatrix_fin_archMat, map_one])

theorem archMat_mul (g h : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :
    archMat R K (g * h) = archMat R K g * archMat R K h :=
  matrix_eq_of_mapMatrix_arch_fin_eq R K
    (by rw [map_mul, mapMatrix_arch_archMat, mapMatrix_arch_archMat, mapMatrix_arch_archMat])
    (by rw [map_mul, mapMatrix_fin_archMat, mapMatrix_fin_archMat, mapMatrix_fin_archMat, mul_one])

def archEmbed : GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) (AdeleRing R K) where
  toFun g :=
    { val := archMat R K g
      inv := archMat R K ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix _ _ _)
      val_inv := by rw [← archMat_mul, Units.mul_inv, archMat_one]
      inv_val := by rw [← archMat_mul, Units.inv_mul, archMat_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact archMat_one R K)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact archMat_mul R K _ _)

theorem coe_archEmbed (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    ((archEmbed R K g : GL (Fin 2) (AdeleRing R K)) : Matrix _ _ _) = archMat R K g := rfl

theorem glArch_archEmbed (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    AdelicLevel.glArch R K (archEmbed R K g) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glArch_apply, coe_archEmbed]
  rfl

theorem glFin_archEmbed (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    AdelicLevel.glFin R K (archEmbed R K g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glFin_apply, coe_archEmbed, Units.val_one]
  rfl

def splice2 (a : GL (Fin 2) (InfiniteAdeleRing K)) (h : GL (Fin 2) (FiniteAdeleRing R K)) :
    GL (Fin 2) (AdeleRing R K) :=
  archEmbed R K a * finEmbed R K h

theorem glArch_splice2 (a : GL (Fin 2) (InfiniteAdeleRing K)) (h : GL (Fin 2) (FiniteAdeleRing R K)) :
    AdelicLevel.glArch R K (splice2 R K a h) = a := by
  rw [splice2, map_mul, glArch_archEmbed, glArch_finEmbed, mul_one]

theorem glFin_splice2 (a : GL (Fin 2) (InfiniteAdeleRing K)) (h : GL (Fin 2) (FiniteAdeleRing R K)) :
    AdelicLevel.glFin R K (splice2 R K a h) = h := by
  rw [splice2, map_mul, glFin_archEmbed, glFin_finEmbed, one_mul]

end Arch

section SemiLocal

open scoped TensorProduct Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem semiLocalEval_apply (v' : HeightOneSpectrum (𝓞 K)) (a : FiniteAdeleRing (𝓞 L) L) :
    AutomorphicForm.semiLocalEval K L v' a =
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v').symm
        (fun w : v'.Extension (𝓞 L) => a w.1) :=
  rfl

theorem eq_of_forall_semiLocalEval_eq {a b : FiniteAdeleRing (𝓞 L) L}
    (h : ∀ v' : HeightOneSpectrum (𝓞 K), AutomorphicForm.semiLocalEval K L v' a = AutomorphicForm.semiLocalEval K L v' b) :
    a = b := by
  refine RestrictedProduct.ext _ _ fun w' => ?_
  have hw := h (HeightOneSpectrum.under (𝓞 K) w')
  rw [semiLocalEval_apply, semiLocalEval_apply] at hw
  have hinj := (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L)
    (HeightOneSpectrum.under (𝓞 K) w')).symm.injective hw
  exact congrFun hinj (⟨w', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w').Extension (𝓞 L))

theorem matrix_eq_of_forall_mapMatrix_semiLocalEval_eq {M N : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (h : ∀ v' : HeightOneSpectrum (𝓞 K),
      (AutomorphicForm.semiLocalEval K L v').mapMatrix M = (AutomorphicForm.semiLocalEval K L v').mapMatrix N) :
    M = N := by
  refine Matrix.ext fun i j => ?_
  refine eq_of_forall_semiLocalEval_eq K L fun v' => ?_
  have hw := congrFun (congrFun (h v') i) j
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using hw

def spliceAbove (a : FiniteAdeleRing (𝓞 L) L) (y : Π w : v.Extension (𝓞 L), w.1.adicCompletion L) :
    FiniteAdeleRing (𝓞 L) L :=
  ⟨fun w' => if h : HeightOneSpectrum.under (𝓞 K) w' = v then (y ⟨w', h⟩ : w'.adicCompletion L) else a w',
    by
      haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
      refine Filter.eventually_cofinite.mpr ?_
      refine ((Set.finite_range fun w : v.Extension (𝓞 L) => (w.1 : HeightOneSpectrum (𝓞 L))).union
        (Filter.eventually_cofinite.mp a.2)).subset ?_
      intro w' hw'
      by_cases h : HeightOneSpectrum.under (𝓞 K) w' = v
      · exact Or.inl ⟨⟨w', h⟩, rfl⟩
      · right
        simp only [Set.mem_setOf_eq, dif_neg h] at hw' ⊢
        exact hw'⟩

theorem spliceAbove_apply_of_eq (a : FiniteAdeleRing (𝓞 L) L) (y : Π w : v.Extension (𝓞 L), w.1.adicCompletion L)
    {w' : HeightOneSpectrum (𝓞 L)} (h : HeightOneSpectrum.under (𝓞 K) w' = v) :
    spliceAbove K L v a y w' = y ⟨w', h⟩ := by
  show (if h : HeightOneSpectrum.under (𝓞 K) w' = v then (y ⟨w', h⟩ : w'.adicCompletion L) else a w') = _
  rw [dif_pos h]

theorem spliceAbove_apply_of_ne (a : FiniteAdeleRing (𝓞 L) L) (y : Π w : v.Extension (𝓞 L), w.1.adicCompletion L)
    {w' : HeightOneSpectrum (𝓞 L)} (h : HeightOneSpectrum.under (𝓞 K) w' ≠ v) :
    spliceAbove K L v a y w' = a w' := by
  show (if h : HeightOneSpectrum.under (𝓞 K) w' = v then (y ⟨w', h⟩ : w'.adicCompletion L) else a w') = _
  rw [dif_neg h]

theorem semiLocalEval_spliceAbove_self (a : FiniteAdeleRing (𝓞 L) L)
    (y : Π w : v.Extension (𝓞 L), w.1.adicCompletion L) :
    AutomorphicForm.semiLocalEval K L v (spliceAbove K L v a y) =
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm y := by
  rw [semiLocalEval_apply]
  congr 1
  funext w
  exact spliceAbove_apply_of_eq K L v a y w.2

theorem semiLocalEval_spliceAbove_of_ne (a : FiniteAdeleRing (𝓞 L) L)
    (y : Π w : v.Extension (𝓞 L), w.1.adicCompletion L) {v' : HeightOneSpectrum (𝓞 K)} (hv' : v' ≠ v) :
    AutomorphicForm.semiLocalEval K L v' (spliceAbove K L v a y) = AutomorphicForm.semiLocalEval K L v' a := by
  rw [semiLocalEval_apply, semiLocalEval_apply]
  congr 1
  funext w
  exact spliceAbove_apply_of_ne K L v a y fun h => hv' (w.2.symm.trans h)

def spliceMat (A : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (M : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
  Matrix.of fun i j => spliceAbove K L v (A i j)
    (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v (M i j))

theorem mapMatrix_spliceMat_self (A : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (M : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    (AutomorphicForm.semiLocalEval K L v).mapMatrix (spliceMat K L v A M) = M := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, spliceMat, Matrix.of_apply,
    semiLocalEval_spliceAbove_self, AlgEquiv.symm_apply_apply]

theorem mapMatrix_spliceMat_of_ne (A : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (M : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) {v' : HeightOneSpectrum (𝓞 K)} (hv' : v' ≠ v) :
    (AutomorphicForm.semiLocalEval K L v').mapMatrix (spliceMat K L v A M) =
      (AutomorphicForm.semiLocalEval K L v').mapMatrix A := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, spliceMat, Matrix.of_apply,
    semiLocalEval_spliceAbove_of_ne K L v _ _ hv']

theorem spliceMat_mul (A B : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (M N : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    spliceMat K L v (A * B) (M * N) = spliceMat K L v A M * spliceMat K L v B N := by
  refine matrix_eq_of_forall_mapMatrix_semiLocalEval_eq K L fun v' => ?_
  by_cases hv' : v' = v
  · subst hv'
    rw [map_mul, mapMatrix_spliceMat_self, mapMatrix_spliceMat_self, mapMatrix_spliceMat_self]
  · rw [map_mul, mapMatrix_spliceMat_of_ne K L v _ _ hv', mapMatrix_spliceMat_of_ne K L v _ _ hv',
      mapMatrix_spliceMat_of_ne K L v _ _ hv', map_mul]

theorem spliceMat_one : spliceMat K L v 1 1 = 1 := by
  refine matrix_eq_of_forall_mapMatrix_semiLocalEval_eq K L fun v' => ?_
  by_cases hv' : v' = v
  · subst hv'; rw [mapMatrix_spliceMat_self, map_one]
  · rw [mapMatrix_spliceMat_of_ne K L v _ _ hv']

def spliceGL (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) where
  val := spliceMat K L v h x
  inv := spliceMat K L v ((h⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Matrix _ _ _)
    ((x⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix _ _ _)
  val_inv := by rw [← spliceMat_mul, Units.mul_inv, Units.mul_inv, spliceMat_one]
  inv_val := by rw [← spliceMat_mul, Units.inv_mul, Units.inv_mul, spliceMat_one]

theorem semiLocalComponent_spliceGL_self (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    AutomorphicForm.semiLocalComponent K L v (spliceGL K L v h x) = x := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have := congrFun (congrFun (mapMatrix_spliceMat_self K L v (h : Matrix _ _ _) (x : Matrix _ _ _)) i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at this
  exact this

theorem semiLocalComponent_spliceGL_of_ne (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) {v' : HeightOneSpectrum (𝓞 K)} (hv' : v' ≠ v) :
    AutomorphicForm.semiLocalComponent K L v' (spliceGL K L v h x) = AutomorphicForm.semiLocalComponent K L v' h := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have := congrFun (congrFun (mapMatrix_spliceMat_of_ne K L v (h : Matrix _ _ _) (x : Matrix _ _ _) hv') i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at this
  exact this

end SemiLocal

end K51FUL

end

open K51FUL in
open scoped TensorProduct in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS)
    (φa' : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS' : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ' : AutomorphicForm.IsSemiLocalFactorization K L S φ φa' φf' φS')
    (h0 : ∃ g, φ g ≠ 0) :
    ∃ (ca : ℂ) (c : HeightOneSpectrum (𝓞 K) → ℂ),
      ca ≠ 0 ∧ (∀ v ∈ S, c v ≠ 0) ∧ ca * ∏ v ∈ S, c v = 1 ∧
      φa' = ca • φa ∧ ∀ v ∈ S, φS' v = c v • φS v := by
  classical
  obtain ⟨g₀, hg₀⟩ := h0
  obtain ⟨-, -, -, hprod, hzero, hfg⟩ := hφ
  obtain ⟨-, -, -, hprod', hzero', hfg'⟩ := hφ'

  set a₀ := AdelicLevel.glArch (𝓞 L) L g₀ with ha₀
  set h₀ := AdelicLevel.glFin (𝓞 L) L g₀ with hh₀
  have hne : φa a₀ * φf h₀ ≠ 0 := by rw [← hfg]; exact hg₀
  have hne' : φa' a₀ * φf' h₀ ≠ 0 := by rw [← hfg']; exact hg₀
  have hfa0 : φa a₀ ≠ 0 := left_ne_zero_of_mul hne
  have hff0 : φf h₀ ≠ 0 := right_ne_zero_of_mul hne
  have hfa0' : φa' a₀ ≠ 0 := left_ne_zero_of_mul hne'
  have hff0' : φf' h₀ ≠ 0 := right_ne_zero_of_mul hne'
  have hint : ∀ v ∉ S, AutomorphicForm.semiLocalComponent K L v h₀ ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
    by_contra hcon
    push Not at hcon
    exact hff0 (hzero h₀ hcon)

  have key : ∀ (a : GL (Fin 2) (InfiniteAdeleRing L)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)),
      φa a * φf h = φa' a * φf' h := by
    intro a h
    have h1 := hfg (splice2 (𝓞 L) L a h)
    have h2 := hfg' (splice2 (𝓞 L) L a h)
    rw [glArch_splice2, glFin_splice2] at h1 h2
    rw [← h1, h2]

  set P : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
    ∏ w ∈ S.erase v, φS w (AutomorphicForm.semiLocalComponent K L w h₀) with hP
  set P' : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
    ∏ w ∈ S.erase v, φS' w (AutomorphicForm.semiLocalComponent K L w h₀) with hP'
  have hintx : ∀ v ∈ S, ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      ∀ w ∉ S, AutomorphicForm.semiLocalComponent K L w (spliceGL K L v h₀ x) ∈
        AutomorphicForm.semiLocalIntegralSet K L w := by
    intro v hv x w hw
    have hwv : w ≠ v := fun h => hw (h ▸ hv)
    rw [semiLocalComponent_spliceGL_of_ne K L v h₀ x hwv]
    exact hint w hw
  have hffx : ∀ v ∈ S, ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      φf (spliceGL K L v h₀ x) = φS v x * P v := by
    intro v hv x
    rw [hprod _ (hintx v hv x), ← Finset.mul_prod_erase S _ hv, semiLocalComponent_spliceGL_self]
    congr 1
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [semiLocalComponent_spliceGL_of_ne K L v h₀ x (Finset.ne_of_mem_erase hw)]
  have hffx' : ∀ v ∈ S, ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      φf' (spliceGL K L v h₀ x) = φS' v x * P' v := by
    intro v hv x
    rw [hprod' _ (hintx v hv x), ← Finset.mul_prod_erase S _ hv, semiLocalComponent_spliceGL_self]
    congr 1
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [semiLocalComponent_spliceGL_of_ne K L v h₀ x (Finset.ne_of_mem_erase hw)]
  have hff_h₀ : ∀ v ∈ S, φf h₀ = φS v (AutomorphicForm.semiLocalComponent K L v h₀) * P v := by
    intro v hv
    rw [hprod _ hint, ← Finset.mul_prod_erase S _ hv]
  have hff_h₀' : ∀ v ∈ S, φf' h₀ = φS' v (AutomorphicForm.semiLocalComponent K L v h₀) * P' v := by
    intro v hv
    rw [hprod' _ hint, ← Finset.mul_prod_erase S _ hv]
  have hP0 : ∀ v ∈ S, P v ≠ 0 := fun v hv => right_ne_zero_of_mul (by rw [← hff_h₀ v hv]; exact hff0)
  have hP0' : ∀ v ∈ S, P' v ≠ 0 := fun v hv => right_ne_zero_of_mul (by rw [← hff_h₀' v hv]; exact hff0')

  refine ⟨φf h₀ / φf' h₀, fun v => (φa a₀ * P v) / (φa' a₀ * P' v), div_ne_zero hff0 hff0',
    fun v hv => div_ne_zero (mul_ne_zero hfa0 (hP0 v hv)) (mul_ne_zero hfa0' (hP0' v hv)), ?_, ?_, ?_⟩
  ·
    beta_reduce
    have hfa' : φa' a₀ = φf h₀ / φf' h₀ * φa a₀ := by
      rw [div_mul_eq_mul_div, eq_div_iff hff0']
      linear_combination (key a₀ h₀).symm
    have hloc : ∀ v ∈ S, φS' v (AutomorphicForm.semiLocalComponent K L v h₀) =
        (φa a₀ * P v) / (φa' a₀ * P' v) * φS v (AutomorphicForm.semiLocalComponent K L v h₀) := by
      intro v hv
      rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hfa0' (hP0' v hv))]
      have := key a₀ (spliceGL K L v h₀ (AutomorphicForm.semiLocalComponent K L v h₀))
      rw [hffx v hv, hffx' v hv] at this
      linear_combination this.symm
    have e3 : φa a₀ * ∏ v ∈ S, φS v (AutomorphicForm.semiLocalComponent K L v h₀) =
        φa' a₀ * ∏ v ∈ S, φS' v (AutomorphicForm.semiLocalComponent K L v h₀) := by
      rw [← hprod _ hint, ← hprod' _ hint]; exact key a₀ h₀
    have hPi : φa a₀ * ∏ v ∈ S, φS v (AutomorphicForm.semiLocalComponent K L v h₀) ≠ 0 := by
      rw [← hprod _ hint]; exact hne
    rw [hfa', Finset.prod_congr rfl hloc, Finset.prod_mul_distrib] at e3
    refine mul_right_cancel₀ hPi ?_
    linear_combination e3.symm
  ·
    funext a
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hff0']
    linear_combination (key a h₀).symm
  ·
    intro v hv
    beta_reduce
    funext x
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hfa0' (hP0' v hv))]
    have := key a₀ (spliceGL K L v h₀ x)
    rw [hffx v hv, hffx' v hv] at this
    linear_combination this.symm

end S_AutomorphicForm_exists_smul_eq_of_isSemiLocalFactorization_of_isSemiLocalFactorization_of_exists_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_smul_eq_of_isSemiLocalFactorization_of_isSemiLocalFactorization_of_exists_ne_zero (solution)
