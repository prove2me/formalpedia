-- Prove2me | solution 1 for AutomorphicForm.normString_map_baseChangeEquiv_symm_centralScalar_eq_toTensorGL_centralScalar_idelicNorm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/5a996577-361e-52fb-88c3-54dfa6d9a447

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import Theorems.Thm_AutomorphicForm_map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_normString_map_baseChangeEquiv_symm_centralScalar_eq_toTensorGL_centralScalar_idelicNorm

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

namespace NormProd

theorem map_scalar {n : Type*} [DecidableEq n] [Fintype n] {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar n u) =
      Matrix.GeneralLinearGroup.scalar n (Units.map (f : R →* S) u) := by
  refine Units.ext ?_
  ext i j
  change f ((Matrix.scalar n (u : R)) i j) = (Matrix.scalar n (f u)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero f

theorem list_prod_range_eq_finset_prod {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∀ n : ℕ, ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i
  | 0 => by simp
  | (n + 1) => by rw [List.prod_range_succ, Finset.prod_range_succ, list_prod_range_eq_finset_prod f n]

end NormProd

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (w : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).symm.toRingHom
          (AutomorphicForm.centralScalar (𝓞 L) L w)) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
        (AutomorphicForm.centralScalar (𝓞 K) K ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w)) := by
  classical

  have h876 := AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L
    (M4aHerbrand.GenuineDescent.genuineDescentDatum K L)
  have h1 : ∀ (τ : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)),
      Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).toRingHom
          (AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) τ g) =
        AutomorphicForm.sigmaAdelicAct K L (M4aHerbrand.GenuineDescent.genuineDescentDatum K L) τ
          (Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).toRingHom g) := h876.1
  have h2 : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).toRingHom
          (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) g) =
        Matrix.GeneralLinearGroup.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β g := h876.2.1
  have hprod := (M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
    K L (M4aHerbrand.GenuineDescent.genuineDescentDatum K L)).2.2.2 w

  have hleft : ∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).symm.toRingHom
        (Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).toRingHom g) = g := by
    intro g
    rw [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp,
      RingEquiv.symm_toRingHom_comp_toRingHom, Matrix.GeneralLinearGroup.map_id]
    rfl
  have hright : ∀ g : GL (Fin 2) (AdeleRing (𝓞 L) L),
      Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).toRingHom
        (Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).symm.toRingHom g) = g := by
    intro g
    rw [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp,
      RingEquiv.toRingHom_comp_symm_toRingHom, Matrix.GeneralLinearGroup.map_id]
    rfl
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin 2) (AutomorphicForm.baseChangeEquiv K L).toRingHom) :=
    fun a b h => by rw [← hleft a, ← hleft b, h]
  apply hinj

  have hact : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      AutomorphicForm.sigmaAdelicAct K L (M4aHerbrand.GenuineDescent.genuineDescentDatum K L) σ
          (AutomorphicForm.centralScalar (𝓞 L) L u) =
        AutomorphicForm.centralScalar (𝓞 L) L
          ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).unitsAct σ u) := by
    intro u
    change Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) _
    rw [NormProd.map_scalar]
    congr 1

  have hiter : ∀ i : ℕ,
      Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).toRingHom
          ((⇑(AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ))^[i]
            (Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).symm.toRingHom
              (AutomorphicForm.centralScalar (𝓞 L) L w))) =
        AutomorphicForm.centralScalar (𝓞 L) L
          ((fun u => (M4aHerbrand.GenuineDescent.genuineDescentDatum K L).unitsAct σ u)^[i] w) := by
    intro i
    induction i with
    | zero => exact hright _
    | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h1, ih, hact]
  have hpow : ∀ i : ℕ, (fun u => (M4aHerbrand.GenuineDescent.genuineDescentDatum K L).unitsAct σ u)^[i] w =
      (M4aHerbrand.GenuineDescent.genuineDescentDatum K L).unitsAct (σ ^ i) w := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply', ih, pow_succ', map_mul, MulAut.mul_apply]

  have hL : Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).toRingHom
      (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).symm.toRingHom
          (AutomorphicForm.centralScalar (𝓞 L) L w))) =
      AutomorphicForm.centralScalar (𝓞 L) L
        (∏ τ : L ≃ₐ[K] L, (M4aHerbrand.GenuineDescent.genuineDescentDatum K L).unitsAct τ w) := by
    unfold AutomorphicForm.normString
    rw [map_list_prod, List.map_map]
    have hfun : (⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) (AutomorphicForm.baseChangeEquiv K L).toRingHom) ∘
        fun i => (⇑(AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ))^[i]
          (Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).symm.toRingHom
            (AutomorphicForm.centralScalar (𝓞 L) L w))) =
        (⇑(AutomorphicForm.centralScalar (𝓞 L) L) ∘
          fun i => (M4aHerbrand.GenuineDescent.genuineDescentDatum K L).unitsAct (σ ^ i) w) := by
      funext i
      simp only [Function.comp_apply]
      rw [hiter, hpow]
    rw [hfun, ← List.map_map, ← map_list_prod, NormProd.list_prod_range_eq_finset_prod]
    congr 1

    have hord : orderOf σ = Module.finrank K L :=
      (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (IsGalois.card_aut_eq_finrank K L)
    have himg : Finset.image (fun i => σ ^ i) (Finset.range (Module.finrank K L)) = Finset.univ := by
      refine Finset.eq_univ_iff_forall.2 fun τ => ?_
      rw [← hord]
      exact mem_zpowers_iff_mem_range_orderOf.mp (hgen τ)
    rw [← himg, Finset.prod_image]
    intro i hi j hj hij
    exact pow_injOn_Iio_orderOf (by simpa [hord] using hi) (by simpa [hord] using hj) hij

  have hR : Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).toRingHom
      (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
        (AutomorphicForm.centralScalar (𝓞 K) K ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w))) =
      AutomorphicForm.centralScalar (𝓞 L) L
        (Units.map ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).β : AdeleRing (𝓞 K) K →* AdeleRing (𝓞 L) L)
          ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w)) := by
    rw [h2]
    exact NormProd.map_scalar _ _
  rw [hL, hR, hprod]
  rfl

end S_AutomorphicForm_normString_map_baseChangeEquiv_symm_centralScalar_eq_toTensorGL_centralScalar_idelicNorm
end P2MW
export P2MW.S_AutomorphicForm_normString_map_baseChangeEquiv_symm_centralScalar_eq_toTensorGL_centralScalar_idelicNorm (solution)
