-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/aeb9846a-cf36-5340-a18c-52bc56a17b22

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

theorem solution
    {A : Type u} [CommRing A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
    {V' : Scheme.{u}} (p : V' ⟶ P)
    (F : ℕ → OModulePresheaf q) (F' : ℕ → OModulePresheaf (p ≫ q))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = (p.appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ p ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U₀.1),
      letI := (p.appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)
    (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U₀.1) (f : Γ(V', V.1)) :
    (∀ x : (F' k).obj (V'.basicOpen f), ∃ (n : ℕ) (y : (F' k).obj V.1),
        (F' k).res (V'.basicOpen_le f) y = (V'.presheaf.map (homOfLE (V'.basicOpen_le f)).op).hom (f ^ n) • x) ∧
    (∀ y : (F' k).obj V.1, (F' k).res (V'.basicOpen_le f) y = 0 → ∃ n : ℕ, (f ^ n : Γ(V', V.1)) • y = 0) := by
  classical

  let D : V'.affineOpens := ⟨V'.basicOpen f, V.2.basicOpen f⟩
  have hDV : D.1 ≤ V.1 := V'.basicOpen_le f
  have h' : D.1 ≤ p ⁻¹ᵁ U₀.1 := hDV.trans h

  letI algRS : Algebra Γ(P, U₀.1) Γ(V', V.1) := (p.appLE U₀.1 V.1 h).hom.toAlgebra
  letI algRT : Algebra Γ(P, U₀.1) Γ(V', D.1) := (p.appLE U₀.1 D.1 h').hom.toAlgebra

  haveI towerRST : IsScalarTower Γ(P, U₀.1) Γ(V', V.1) Γ(V', D.1) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    show (p.appLE U₀.1 D.1 h').hom r
      = (V'.presheaf.map (homOfLE (V'.basicOpen_le f)).op).hom ((p.appLE U₀.1 V.1 h).hom r)
    rw [← CommRingCat.comp_apply (p.appLE U₀.1 V.1 h), Scheme.Hom.appLE_map]
  haveI : IsLocalization.Away f Γ(V', D.1) := V.2.isLocalization_basicOpen f

  let M := (F k).obj U₀.1
  let N := (F' k).obj V.1
  let O := (F' k).obj D.1
  letI modRN : Module Γ(P, U₀.1) N := Module.compHom N (algebraMap Γ(P, U₀.1) Γ(V', V.1))
  haveI towerRSN : IsScalarTower Γ(P, U₀.1) Γ(V', V.1) N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI modSO : Module Γ(V', V.1) O := Module.compHom O (algebraMap Γ(V', V.1) Γ(V', D.1))
  haveI towerSTO : IsScalarTower Γ(V', V.1) Γ(V', D.1) O := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI modRO : Module Γ(P, U₀.1) O := Module.compHom O (algebraMap Γ(P, U₀.1) Γ(V', D.1))
  haveI towerRTO : IsScalarTower Γ(P, U₀.1) Γ(V', D.1) O := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI towerRSO : IsScalarTower Γ(P, U₀.1) Γ(V', V.1) O := by
    refine ⟨fun r s o => ?_⟩
    show algebraMap Γ(V', V.1) Γ(V', D.1) (algebraMap Γ(P, U₀.1) Γ(V', V.1) r * s) • o
      = algebraMap Γ(P, U₀.1) Γ(V', D.1) r • (algebraMap Γ(V', V.1) Γ(V', D.1) s • o)
    rw [map_mul, ← IsScalarTower.algebraMap_apply, mul_smul]

  let ηV : M →ₗ[Γ(P, U₀.1)] N :=
    { toFun := η k U₀ V h, map_add' := fun x y => map_add _ x y, map_smul' := fun r x => hηs k U₀ V h r x }
  let ηD : M →ₗ[Γ(P, U₀.1)] O :=
    { toFun := η k U₀ D h', map_add' := fun x y => map_add _ x y, map_smul' := fun r x => hηs k U₀ D h' r x }
  have hbcV : IsBaseChange Γ(V', V.1) ηV := by
    obtain ⟨β, hβ'⟩ := hβ k U₀ V h
    exact IsBaseChange.of_equiv β fun x => hβ' x
  have hbcD : IsBaseChange Γ(V', D.1) ηD := by
    obtain ⟨β, hβ'⟩ := hβ k U₀ D h'
    exact IsBaseChange.of_equiv β fun x => hβ' x

  let ρ : N →ₗ[Γ(V', V.1)] O :=
    { toFun := (F' k).res hDV, map_add' := fun x y => map_add _ x y
      map_smul' := fun s x => (F' k).res_smul hDV s x }
  have hcomp : (ρ.restrictScalars (↑(P.presheaf.obj (Opposite.op U₀.1)) : Type u)) ∘ₗ ηV = ηD := by
    refine LinearMap.ext fun x => ?_
    exact hηV k U₀ D V h' h hDV x
  have hbcρ : IsBaseChange Γ(V', D.1) ρ := IsBaseChange.of_comp hbcV (by rw [hcomp]; exact hbcD)
  haveI hloc : IsLocalizedModule (Submonoid.powers f) ρ :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) Γ(V', D.1) ρ).mpr hbcρ
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers f) ρ x
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    refine ⟨n, m, ?_⟩
    show ρ m = _
    rw [← hs]
    show (algebraMap Γ(V', V.1) Γ(V', D.1) (s : Γ(V', V.1))) • x = _
    rw [← hn]
    rfl
  · have h0 : ρ y = 0 := hy
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers f) ρ).mp h0
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    refine ⟨n, ?_⟩
    rw [hn]
    exact hs

end S_AlgebraicGeometry_OModulePresheaf_forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct (solution)
