-- Prove2me | solution 1 for Algebra.TensorProduct.bijective_productMap_pi_comp_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c220db40-3d1f-5a00-8007-d693f88e54c7

import Mathlib
import Definitions.Def_Mathlib_RightActionInstances
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_TensorProduct_bijective_productMap_pi_comp_of_isGalois

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

namespace Split

open scoped TensorProduct.RightActions

variable (K L F : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Field F] [Algebra K F] (σ₀ : L →ₐ[K] F)

def Φ : L ⊗[K] F →ₐ[K] ((L ≃ₐ[K] L) → F) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom K (fun _ : L ≃ₐ[K] L => F) (fun τ : L ≃ₐ[K] L => σ₀.comp (τ : L →ₐ[K] L)))
    (Pi.algHom K (fun _ : L ≃ₐ[K] L => F) (fun _ : L ≃ₐ[K] L => AlgHom.id K F))

theorem Φ_tmul (ℓ : L) (f : F) (τ : L ≃ₐ[K] L) : Φ K L F σ₀ (ℓ ⊗ₜ f) τ = σ₀ (τ ℓ) * f := by
  simp [Φ, Algebra.TensorProduct.productMap_apply_tmul]

theorem Φ_algebraMap (f : F) : Φ K L F σ₀ (algebraMap F (L ⊗[K] F) f) = algebraMap F ((L ≃ₐ[K] L) → F) f := by
  funext τ
  rw [show algebraMap F (L ⊗[K] F) f = (1 : L) ⊗ₜ[K] f from rfl, Φ_tmul, map_one, map_one, one_mul,
    Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

def ΦF : (L ⊗[K] F) →ₐ[F] ((L ≃ₐ[K] L) → F) :=
  { toFun := Φ K L F σ₀
    map_one' := map_one _
    map_mul' := map_mul _
    map_zero' := map_zero _
    map_add' := map_add _
    commutes' := fun f => Φ_algebraMap K L F σ₀ f }

theorem ΦF_apply (z : L ⊗[K] F) : ΦF K L F σ₀ z = Φ K L F σ₀ z := rfl

theorem injective_comp : Function.Injective (fun τ : L ≃ₐ[K] L => σ₀.comp (τ : L →ₐ[K] L)) := by
  intro τ τ' h
  apply AlgEquiv.ext
  intro x
  have hx := congrArg (fun φ : L →ₐ[K] F => φ x) h
  exact σ₀.toRingHom.injective hx

theorem main : Function.Bijective (Φ K L F σ₀) := by
  classical
  set n := Module.finrank K L with hn
  let b : Module.Basis (Fin n) K L := Module.finBasis K L
  let bF : Module.Basis (Fin n) F (L ⊗[K] F) := TensorProduct.RightActions.Algebra.TensorProduct.basis F b
  have hbF : ∀ i, bF i = b i ⊗ₜ[K] (1 : F) := by
    intro i
    show ((_root_.Algebra.TensorProduct.basis F b).map (TensorProduct.RightActions.Module.TensorProduct.comm K F L)) i = _
    rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul]

  let M : Matrix (L ≃ₐ[K] L) (Fin n) F := fun τ i => σ₀ (τ (b i))
  have hΦbasis : ∀ i τ, Φ K L F σ₀ (bF i) τ = M τ i := by
    intro i τ
    rw [hbF, Φ_tmul, mul_one]
  have hΦ : ∀ z : L ⊗[K] F, Φ K L F σ₀ z = M.mulVec (fun i => bF.repr z i) := by
    intro z
    conv_lhs => rw [← bF.sum_repr z]
    funext τ
    rw [map_sum, Finset.sum_apply, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Φ K L F σ₀ (bF.repr z i • bF i) = bF.repr z i • Φ K L F σ₀ (bF i) from
      (ΦF K L F σ₀).toLinearMap.map_smul (bF.repr z i) (bF i), Pi.smul_apply, hΦbasis, smul_eq_mul, mul_comm]

  have hrows : LinearIndependent F (fun τ : L ≃ₐ[K] L => M τ) := by
    rw [linearIndependent_iff']
    intro s g hg τ hτ
    have hind := (linearIndependent_toLinearMap K L F).comp _ (injective_comp K L F σ₀)
    rw [linearIndependent_iff'] at hind
    refine hind s g ?_ τ hτ
    apply b.ext
    intro i
    have hi := congrFun hg i
    rw [Finset.sum_apply] at hi
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    rw [LinearMap.zero_apply, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, Function.comp_apply, AlgHom.toLinearMap_apply, AlgHom.coe_comp,
      AlgHom.coe_coe, smul_eq_mul]
    exact hi

  have hcard : Fintype.card (L ≃ₐ[K] L) = n := by
    rw [hn, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  let e : (L ≃ₐ[K] L) ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let M' : Matrix (Fin n) (Fin n) F := fun k i => M (e.symm k) i
  have hrows' : LinearIndependent F M'.row := by
    show LinearIndependent F (fun k : Fin n => M (e.symm k))
    exact hrows.comp e.symm e.symm.injective
  have hU : IsUnit M' := Matrix.linearIndependent_rows_iff_isUnit.mp hrows'
  have hMM' : ∀ c : Fin n → F, M.mulVec c = (M'.mulVec c) ∘ e := by
    intro c; funext τ
    simp only [Function.comp_apply, Matrix.mulVec, dotProduct, M', Equiv.symm_apply_apply]

  have hinj : Function.Injective (Φ K L F σ₀) := by
    intro z₁ z₂ h
    have h' : M'.mulVec (fun i => bF.repr z₁ i) = M'.mulVec (fun i => bF.repr z₂ i) := by
      have h0 : M.mulVec (fun i => bF.repr z₁ i) = M.mulVec (fun i => bF.repr z₂ i) := by rw [← hΦ, ← hΦ, h]
      rw [hMM', hMM'] at h0
      funext k
      have := congrFun h0 (e.symm k)
      simpa using this
    have h'' := Matrix.mulVec_injective_of_isUnit hU h'
    apply bF.repr.injective
    ext i
    exact congrFun h'' i
  refine ⟨hinj, ?_⟩

  have hdim : Module.finrank F (L ⊗[K] F) = Module.finrank F ((L ≃ₐ[K] L) → F) := by
    rw [Module.finrank_eq_card_basis bF, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hn,
      ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  have hsurj : Function.Surjective (ΦF K L F σ₀).toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact hsurj

end Split

end

theorem solution
    (K L F : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Field F] [Algebra K F] (σ₀ : L →ₐ[K] F) :
    Function.Bijective
      (Algebra.TensorProduct.productMap
        (Pi.algHom K (fun _ : L ≃ₐ[K] L => F) (fun τ : L ≃ₐ[K] L => σ₀.comp (τ : L →ₐ[K] L)))
        (Pi.algHom K (fun _ : L ≃ₐ[K] L => F) (fun _ : L ≃ₐ[K] L => AlgHom.id K F))) :=
  Split.main K L F σ₀

end S_Algebra_TensorProduct_bijective_productMap_pi_comp_of_isGalois
end P2MW
export P2MW.S_Algebra_TensorProduct_bijective_productMap_pi_comp_of_isGalois (solution)
