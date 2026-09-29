-- Prove2me | solution 1 for Algebra.TensorProduct.isDirectLimit_map_of_isDirectLimit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5572e27a-4c28-56a2-85e0-daa25e194795

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit

set_option autoImplicit false

open TensorProduct

universe u v w

namespace TensorDL17

theorem map_id_eq_rTensor {R₀ : Type v} [CommRing R₀] {A A' : Type w} [CommRing A] [CommRing A'] [Algebra R₀ A] [Algebra R₀ A']
    (B : Type w) [CommRing B] [Algebra R₀ B] (φ : A →ₐ[R₀] A') (x : A ⊗[R₀] B) :
    Algebra.TensorProduct.map φ (AlgHom.id R₀ B) x = LinearMap.rTensor B φ.toLinearMap x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end TensorDL17

open TensorDL17 in
theorem solution
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (R₀ : Type v) [CommRing R₀]
    (G : ι → Type w) [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
    (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j) [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R] [∀ i, IsScalarTower R₀ (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (B : Type w) [CommRing B] [Algebra R₀ B] :
    ∃ _ : DirectedSystem (fun i => G i ⊗[R₀] B)
        (fun i j h => ⇑(Algebra.TensorProduct.map (f i j h) (AlgHom.id R₀ B))),
      IsDirectLimit (fun i j h => ⇑(Algebra.TensorProduct.map (f i j h) (AlgHom.id R₀ B)))
        (fun i => ⇑(Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B))) := by
  classical

  have hDS : DirectedSystem (fun i => G i ⊗[R₀] B) (fun i j h => ⇑(Algebra.TensorProduct.map (f i j h) (AlgHom.id R₀ B))) := by
    constructor
    · intro i x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rw [Algebra.TensorProduct.map_tmul, DirectedSystem.map_self' (fun i j h => f i j h)]; rfl
      | add x y hx hy => rw [map_add, hx, hy]
    · intro k j i hij hjk x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
          DirectedSystem.map_map' (fun i j h => f i j h)]; rfl
      | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨hDS, ?_⟩

  have hcompat : ∀ i j (hij : i ≤ j) (x : G i ⊗[R₀] B),
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G j) R) (AlgHom.id R₀ B)
          (Algebra.TensorProduct.map (f i j hij) (AlgHom.id R₀ B) x) =
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B) x := by
    intro i j hij x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply]
      rw [hR.compatibility]
    | add x y hx hy => simp only [map_add, hx, hy]

  let fL : ∀ i j : ι, i ≤ j → G i →ₗ[R₀] G j := fun i j h => (f i j h).toLinearMap
  haveI hDSL : DirectedSystem G (fun i j h => ⇑(fL i j h)) := ‹DirectedSystem G fun i j h => ⇑(f i j h)›
  haveI hR' : IsDirectLimit (fun i j h => ⇑(fL i j h)) (fun i => ⇑((IsScalarTower.toAlgHom R₀ (G i) R).toLinearMap)) := hR
  let Φ : Module.DirectLimit G fL ≃ₗ[R₀] R :=
    IsDirectLimit.Module.linearEquiv fL (fun i => Module.DirectLimit.of R₀ ι G fL i)
      (fun i => (IsScalarTower.toAlgHom R₀ (G i) R).toLinearMap)
  let Ψ : R ⊗[R₀] B ≃ₗ[R₀] Module.DirectLimit (fun i => G i ⊗[R₀] B) (fun i j h => LinearMap.rTensor B (fL i j h)) :=
    (TensorProduct.congr Φ.symm (LinearEquiv.refl R₀ B)).trans (TensorProduct.directLimitLeft fL B)
  have hΨ : ∀ i (x : G i ⊗[R₀] B),
      Ψ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B) x) =
        Module.DirectLimit.of R₀ ι (fun i => G i ⊗[R₀] B) (fun i j h => LinearMap.rTensor B (fL i j h)) i x := by
    intro i x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [Ψ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
        LinearEquiv.refl_apply]
      have : Φ.symm ((IsScalarTower.toAlgHom R₀ (G i) R) a) = Module.DirectLimit.of R₀ ι G fL i a :=
        IsDirectLimit.Module.linearEquiv_symm_apply fL _ _ i a
      rw [this, TensorProduct.directLimitLeft_tmul_of]
    | add x y hx hy => simp only [map_add, hx, hy]
  constructor
  ·
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨Classical.arbitrary ι, 0, by simp⟩
    | tmul r b =>
      obtain ⟨i, a, ha⟩ := hR.surj r
      exact ⟨i, a ⊗ₜ b, by simp [Algebra.TensorProduct.map_tmul, ha]⟩
    | add x y hx hy =>
      obtain ⟨i, xi, hxi⟩ := hx
      obtain ⟨j, yj, hyj⟩ := hy
      obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
      refine ⟨k, Algebra.TensorProduct.map (f i k hik) (AlgHom.id R₀ B) xi +
        Algebra.TensorProduct.map (f j k hjk) (AlgHom.id R₀ B) yj, ?_⟩
      rw [map_add, hcompat, hcompat, hxi, hyj]
  ·
    intro i j xi yj h
    have h' := congrArg Ψ h
    rw [hΨ, hΨ] at h'
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    rw [← Module.DirectLimit.of_f (hij := hik), ← Module.DirectLimit.of_f (hij := hjk)] at h'
    obtain ⟨l, hkl, hl⟩ := Module.DirectLimit.exists_eq_of_of_eq h'
    refine ⟨l, hik.trans hkl, hjk.trans hkl, ?_⟩
    rw [← hDS.map_map hik hkl, ← hDS.map_map hjk hkl]
    show Algebra.TensorProduct.map (f k l hkl) (AlgHom.id R₀ B) (Algebra.TensorProduct.map (f i k hik) (AlgHom.id R₀ B) xi) =
      Algebra.TensorProduct.map (f k l hkl) (AlgHom.id R₀ B) (Algebra.TensorProduct.map (f j k hjk) (AlgHom.id R₀ B) yj)
    simp only [map_id_eq_rTensor]
    exact hl
  ·
    intro i j hij x
    exact hcompat i j hij x

end S_Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit
end P2MW
export P2MW.S_Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit (solution)
