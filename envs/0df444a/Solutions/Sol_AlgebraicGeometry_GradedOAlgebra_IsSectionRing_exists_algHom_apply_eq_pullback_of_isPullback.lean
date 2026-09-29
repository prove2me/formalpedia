-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_apply_eq_pullback_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/ee449b8c-59b9-5447-ac9d-0eafbc96e9d2

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_tensorPowAdd_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_unitSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_baseScalar_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_apply_eq_pullback_of_isPullback
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L : X.Modules) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L')
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤)) (hR' : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f' L' R' 𝓡' ι') :
    ∃ (θ : R →ₐ[S] R') (hθdeg : ∀ n, ∀ x ∈ 𝓡 n, θ x ∈ 𝓡' n),
      ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨θ x, hθdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x)) := by
  classical

  let Φ : ∀ n : ℕ, Γ(L.tensorPow n, ⊤) →+ Γ(L'.tensorPow n, ⊤) := fun n =>
    (((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤).hom).comp
      ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤).hom)
  have Φ_add : ∀ (n : ℕ) (s t : Γ(L.tensorPow n, ⊤)), Φ n (s + t) = Φ n s + Φ n t :=
    fun n s t => (Φ n).map_add s t
  have inj : ∀ n : ℕ, Function.Injective (ι' n) := fun n => (hR'.bijective n).1

  let E : ∀ n : ℕ, ↥(𝓡' n) ≃ Γ(L'.tensorPow n, ⊤) := fun n => Equiv.ofBijective (ι' n) (hR'.bijective n)
  let θ₀ : ∀ n : ℕ, ↥(𝓡 n) → ↥(𝓡' n) := fun n x => (E n).symm (Φ n (ι n x))
  have hθ₀ : ∀ (n : ℕ) (x : 𝓡 n), ι' n (θ₀ n x) = Φ n (ι n x) := fun n x =>
    Equiv.ofBijective_apply_symm_apply (ι' n) (hR'.bijective n) (Φ n (ι n x))
  have θ₀_add : ∀ (n : ℕ) (x y : 𝓡 n), θ₀ n (x + y) = θ₀ n x + θ₀ n y := by
    intro n x y
    apply inj n
    rw [hθ₀ n (x + y), hR.map_add, Φ_add, hR'.map_add, hθ₀ n x, hθ₀ n y]
  have θ₀_smul : ∀ (n : ℕ) (a : S) (x : 𝓡 n), θ₀ n (a • x) = algebraMap S S' a • θ₀ n x := by
    intro n a x
    apply inj n
    rw [hθ₀ n (a • x), hR.map_smul, hR'.map_smul, hθ₀ n x]
    exact AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_baseScalar_smul S' f f' c hc L L' e n a (ι n x)
  have θ₀_mul : ∀ (m n : ℕ) (x : 𝓡 m) (y : 𝓡 n),
      (θ₀ (m + n) ⟨(x : R) * y, SetLike.GradedMul.mul_mem x.2 y.2⟩ : R') = (θ₀ m x : R') * θ₀ n y := by
    intro m n x y
    have h : θ₀ (m + n) ⟨(x : R) * y, SetLike.GradedMul.mul_mem x.2 y.2⟩ =
        ⟨(θ₀ m x : R') * θ₀ n y, SetLike.GradedMul.mul_mem (θ₀ m x).2 (θ₀ n y).2⟩ := by
      apply inj (m + n)
      rw [hθ₀ (m + n), hR.map_mul, hR'.map_mul, hθ₀ m x, hθ₀ n y]
      exact AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_tensorPowAdd_tensorSections c L L' e m n (ι m x) (ι n y)
    exact congrArg Subtype.val h
  have θ₀_one : θ₀ 0 ⟨1, SetLike.GradedOne.one_mem⟩ = ⟨1, SetLike.GradedOne.one_mem⟩ := by
    apply inj 0
    rw [hθ₀ 0, hR.map_one, hR'.map_one]
    exact AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_unitSection c L L' e

  let θl : ∀ n : ℕ, ↥(𝓡 n) →ₗ[S] R' := fun n =>
    { toFun := fun x => (θ₀ n x : R')
      map_add' := fun x y => by
        simp only [θ₀_add, Submodule.coe_add]
      map_smul' := fun a x => by
        change (θ₀ n (a • x) : R') = a • (θ₀ n x : R')
        rw [θ₀_smul, Submodule.coe_smul, algebraMap_smul] }
  let θlin : R →ₗ[S] R' :=
    DirectSum.toModule S ℕ R' θl ∘ₗ (DirectSum.decomposeLinearEquiv 𝓡).toLinearMap
  have hθlin : ∀ (n : ℕ) (x : 𝓡 n), θlin (x : R) = (θ₀ n x : R') := by
    intro n x
    show DirectSum.toModule S ℕ R' θl (DirectSum.decomposeLinearEquiv 𝓡 (x : R)) = (θ₀ n x : R')
    rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]
    rfl
  have θlin_one : θlin 1 = 1 := by
    change θlin ((⟨1, SetLike.GradedOne.one_mem⟩ : 𝓡 0) : R) = 1
    rw [hθlin, θ₀_one]
  have θlin_mul : ∀ x y : R, θlin (x * y) = θlin x * θlin y := by
    intro x y
    refine DirectSum.Decomposition.inductionOn 𝓡 ?_ (fun {m} x' => ?_) ?_ x
    · simp only [zero_mul, _root_.map_zero]
    · refine DirectSum.Decomposition.inductionOn 𝓡 ?_ (fun {n} y' => ?_) ?_ y
      · simp only [mul_zero, _root_.map_zero]
      · change θlin ((⟨(x' : R) * y', SetLike.GradedMul.mul_mem x'.2 y'.2⟩ : 𝓡 (m + n)) : R) =
          θlin (x' : R) * θlin (y' : R)
        rw [hθlin, hθlin, hθlin]
        exact θ₀_mul m n x' y'
      · intro y₁ y₂ h₁ h₂
        simp only [mul_add, _root_.map_add, h₁, h₂]
    · intro x₁ x₂ h₁ h₂
      simp only [add_mul, _root_.map_add, h₁, h₂]

  let θ : R →ₐ[S] R' := AlgHom.ofLinearMap θlin θlin_one θlin_mul
  have hθ : ∀ (n : ℕ) (x : 𝓡 n), θ (x : R) = (θ₀ n x : R') := fun n x => hθlin n x
  have hθdeg : ∀ n, ∀ x ∈ 𝓡 n, θ x ∈ 𝓡' n := by
    intro n x hx
    change θ ((⟨x, hx⟩ : 𝓡 n) : R) ∈ 𝓡' n
    rw [hθ]
    exact (θ₀ n ⟨x, hx⟩).2
  refine ⟨θ, hθdeg, fun n x => ?_⟩
  have hx : (⟨θ x, hθdeg n x x.2⟩ : 𝓡' n) = θ₀ n x := Subtype.ext (hθ n x)
  rw [hx]
  exact hθ₀ n x

end S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_apply_eq_pullback_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_algHom_apply_eq_pullback_of_isPullback (solution)
