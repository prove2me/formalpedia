-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.isRiemannForm_tensorUnit_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8fa7695d-d9b4-5488-9d04-06ca20eb1ef3

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Theorems.Thm_AlgebraicGeometry_RiemannForm_translation_comp_schemeNsmul_of_nsmul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_isRiemannForm_tensorUnit_zero

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm CategoryTheory.MonoidalCategory"

namespace Law4Unit

open _root_.AlgebraicGeometry.Scheme.Modules in

theorem transport_conj {A : Scheme.{0}} {T g : A ⟶ A} (h : T ≫ g = g) {M M' : A.Modules} (α : M ≅ M') :
    (((Scheme.Modules.pullback g).mapIso α).symm ≪≫ (transportIso h M).symm ≪≫
      (Scheme.Modules.pullback T).mapIso ((Scheme.Modules.pullback g).mapIso α) ≪≫ transportIso h M').hom = 𝟙 _ := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, transportIso, Iso.trans_inv,
    Iso.app_hom, Iso.app_inv, Category.assoc]
  have n1 := (Scheme.Modules.pullbackComp T g).inv.naturality α.hom
  have n2 := (Scheme.Modules.pullbackCongr h).hom.naturality α.hom
  simp only [Functor.comp_map] at n1

  erw [reassoc_of% n1.symm]
  erw [Iso.inv_hom_id_app_assoc]
  erw [n2]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

theorem isConstScalar_id {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (M : A.Modules) : IsConstScalar f (𝟙 M) (1 : k) := by
  intro U s
  simp [map_one, one_smul]

theorem eq_of_isConstScalar {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    {M : A.Modules} {σ τ : M ⟶ M} {c : k} (hσ : IsConstScalar f σ c) (hτ : IsConstScalar f τ c) : σ = τ := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  rw [hσ U s, hτ U s]

theorem eq_id_of_isConstScalar_one {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    {M : A.Modules} {σ : M ⟶ M} (hσ : IsConstScalar f σ 1) : σ = 𝟙 M :=
  eq_of_isConstScalar f hσ (isConstScalar_id f M)

theorem isConstScalar_conj {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    {M N : A.Modules} (e : N ≅ M) {σ : M ⟶ M} {c : k} (hσ : IsConstScalar f σ c) :
    IsConstScalar f (e.hom ≫ σ ≫ e.inv) c := by
  intro U s
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
  rw [hσ U, Scheme.Modules.Hom.app_smul]
  congr 1
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

end Law4Unit

open Law4Unit in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (ζ : ℕ → k) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n) :
    IsRiemannForm f L hc (𝟙_ A.Modules) ℓ ζ 0 := by
  intro n a b
  have hta : (ℓ ^ n) • ((a : ℕ → L.AlgPoints hc k) n) = 0 := by
    have h__af := TateModule.torsion a n
    simp [Nat.cast_smul_eq_nsmul] at h__af
    exact h__af
  have hx := AlgebraicGeometry.RiemannForm.translation_comp_schemeNsmul_of_nsmul_eq_zero k f L hc ((a : ℕ → L.AlgPoints hc k) n) (ℓ ^ n) hta
  have h0 : ζ n ^ ((0 : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) a b).appr n = 1 := by
    have happr : ((0 : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) a b).appr n = 0 := by
      simp only [LinearMap.zero_apply]
      have hz : (((0 : ℤ_[ℓ]).appr n : ℕ) : ZMod (ℓ ^ n)) = 0 := map_zero (PadicInt.toZModPow n)
      have hdvd := (ZMod.natCast_eq_zero_iff _ _).1 hz
      exact Nat.eq_zero_of_dvd_of_lt hdvd (PadicInt.appr_lt _ _)
    rw [happr, pow_zero]
  rw [h0]
  let α : (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint ((b : ℕ → L.AlgPoints hc k) n)))).obj
      (𝟙_ A.Modules) ≅ 𝟙_ A.Modules := Scheme.Modules.pullbackUnitIso _
  refine ⟨hx, (Scheme.Modules.pullback (L.schemeNsmul (ℓ ^ n))).mapIso α, ?_⟩
  rw [transport_conj hx α]
  exact isConstScalar_id f _

end S_AlgebraicGeometry_RiemannForm_isRiemannForm_tensorUnit_zero
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_isRiemannForm_tensorUnit_zero (solution)
