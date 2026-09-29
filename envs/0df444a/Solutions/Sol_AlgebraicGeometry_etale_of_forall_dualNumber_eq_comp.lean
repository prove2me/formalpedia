-- Prove2me | solution 1 for AlgebraicGeometry.etale_of_forall_dualNumber_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/b0c54141-1b27-50f3-b893-8b7430991597

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_etale_of_forall_dualNumber_eq_comp

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_etale_of_forall_dualNumber_eq_comp.AlgebraicGeometry"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_inj IsZariskiLocalAtSource.iff_of_openCover LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Spec.map_surjective IsZariskiLocalAtSource IsOpenImmersion Flat HasRingHomProperty.Spec_iff Etale.of_formallyUnramified_of_flat Etale FormallyUnramified LocallyOfFinitePresentation HasRingHomProperty"
namespace TanCrit
p2m_open "AlgebraicGeometry"

open scoped TensorProduct

section Algebra

variable {κ : Type u} [Field κ] {B : Type u} [CommRing B] [Algebra κ B]

noncomputable def dualNumberHom (x : B →ₐ[κ] κ)
    (d : letI := x.toRingHom.toAlgebra; Derivation κ B κ) : B →ₐ[κ] DualNumber κ :=
  letI := x.toRingHom.toAlgebra
  { toFun := fun b => TrivSqZeroExt.inl (x b) + TrivSqZeroExt.inr (d b)
    map_one' := by
      apply TrivSqZeroExt.ext <;> simp [d.map_one_eq_zero]
    map_mul' := fun a b => by
      have hl : d (a * b) = x a * d b + x b * d a := by
        rw [d.leibniz]
        rfl
      apply TrivSqZeroExt.ext
      · simp
      · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, TrivSqZeroExt.snd_mul,
          TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, smul_eq_mul, hl,
          MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
        ring
    map_zero' := by
      apply TrivSqZeroExt.ext <;> simp
    map_add' := fun a b => by
      apply TrivSqZeroExt.ext <;> simp
    commutes' := fun c => by
      apply TrivSqZeroExt.ext
      · simp [Algebra.algebraMap_eq_smul_one]
      · simp [Algebra.algebraMap_eq_smul_one] }

theorem snd_dualNumberHom (x : B →ₐ[κ] κ) (d : letI := x.toRingHom.toAlgebra; Derivation κ B κ) (b : B) :
    TrivSqZeroExt.snd (dualNumberHom x d b) = d b := by
  simp [dualNumberHom]

theorem derivation_eq_zero (h : ∀ (φ : B →ₐ[κ] DualNumber κ) (b : B), TrivSqZeroExt.snd (φ b) = 0)
    (x : B →ₐ[κ] κ) (d : letI := x.toRingHom.toAlgebra; Derivation κ B κ) : d = 0 := by
  letI := x.toRingHom.toAlgebra
  ext b
  have := h (dualNumberHom x d) b
  rwa [snd_dualNumberHom] at this

theorem linearMap_eq_zero (h : ∀ (φ : B →ₐ[κ] DualNumber κ) (b : B), TrivSqZeroExt.snd (φ b) = 0)
    (x : B →ₐ[κ] κ) :
    letI := x.toRingHom.toAlgebra
    ∀ L : Ω[B⁄κ] →ₗ[B] κ, L = 0 := by
  letI := x.toRingHom.toAlgebra
  haveI : IsScalarTower κ B κ := IsScalarTower.of_algebraMap_eq fun c => (x.commutes c).symm
  intro L
  have hd : KaehlerDifferential.linearMapEquivDerivation κ B L = 0 := derivation_eq_zero h x _
  exact (LinearEquiv.map_eq_zero_iff _).mp hd

theorem ker_smul_top_eq_top (h : ∀ (φ : B →ₐ[κ] DualNumber κ) (b : B), TrivSqZeroExt.snd (φ b) = 0)
    (x : B →ₐ[κ] κ) :
    ((RingHom.ker x.toRingHom) • ⊤ : Submodule B Ω[B⁄κ]) = ⊤ := by
  letI := x.toRingHom.toAlgebra
  set N : Submodule B Ω[B⁄κ] := (RingHom.ker x.toRingHom) • ⊤ with hN
  suffices hv : ∀ v : Ω[B⁄κ] ⧸ N, v = 0 from
    eq_top_iff.mpr fun ω _ => (Submodule.Quotient.mk_eq_zero N).mp (hv _)
  intro v
  refine (Module.forall_dual_apply_eq_zero_iff κ v).mp fun ℓ => ?_

  let L : Ω[B⁄κ] →ₗ[B] κ :=
    { toFun := fun ω => ℓ (N.mkQ ω)
      map_add' := fun a b => by simp
      map_smul' := fun b ω => by
        have hmem : b • ω - algebraMap κ B (x b) • ω ∈ N := by
          rw [← sub_smul]
          refine Submodule.smul_mem_smul ?_ Submodule.mem_top
          rw [RingHom.mem_ker]
          simp
        have hq : N.mkQ (b • ω) = (x b) • N.mkQ ω := by
          rw [← algebraMap_smul B (x b) (N.mkQ ω), ← map_smul]
          exact (Submodule.Quotient.eq N).mpr hmem
        show ℓ (N.mkQ (b • ω)) = x b * ℓ (N.mkQ ω)
        rw [hq, map_smul, smul_eq_mul] }
  have hL : L = 0 := linearMap_eq_zero h x L
  obtain ⟨ω, rfl⟩ := N.mkQ_surjective v
  exact congrArg (fun f : Ω[B⁄κ] →ₗ[B] κ => f ω) hL

theorem exists_algHom_ker_eq [IsAlgClosed κ] [Algebra.FiniteType κ B] (𝔪 : Ideal B) [𝔪.IsMaximal] :
    ∃ x : B →ₐ[κ] κ, RingHom.ker x.toRingHom = 𝔪 := by
  letI : Field (B ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Algebra.FiniteType κ (B ⧸ 𝔪) := inferInstance
  haveI : Module.Finite κ (B ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing κ (B ⧸ 𝔪)
  haveI : Algebra.IsIntegral κ (B ⧸ 𝔪) := inferInstance
  have hbij : Function.Bijective (algebraMap κ (B ⧸ 𝔪)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : κ ≃ₐ[κ] B ⧸ 𝔪 := AlgEquiv.ofBijective (Algebra.ofId κ (B ⧸ 𝔪)) hbij
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ κ 𝔪), ?_⟩
  ext b
  rw [RingHom.mem_ker]
  change e.symm (Ideal.Quotient.mk 𝔪 b) = 0 ↔ b ∈ 𝔪
  rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

theorem subsingleton_kaehlerDifferential [IsAlgClosed κ] [Algebra.FiniteType κ B]
    (h : ∀ (φ : B →ₐ[κ] DualNumber κ) (b : B), TrivSqZeroExt.snd (φ b) = 0) :
    Subsingleton Ω[B⁄κ] := by
  refine ⟨fun ω ω' => ?_⟩
  suffices hz : ∀ ω : Ω[B⁄κ], ω = 0 by rw [hz ω, hz ω']
  intro ω

  by_contra hω
  have htop : Ideal.torsionOf B Ω[B⁄κ] ω ≠ ⊤ := by
    intro ht
    apply hω
    have h1 : (1 : B) ∈ Ideal.torsionOf B Ω[B⁄κ] ω := by rw [ht]; trivial
    rw [Ideal.mem_torsionOf_iff, one_smul] at h1
    exact h1
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ htop
  obtain ⟨x, hx⟩ := exists_algHom_ker_eq (κ := κ) 𝔪
  have hsmul := ker_smul_top_eq_top h x
  rw [hx] at hsmul
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 (⊤ : Submodule B Ω[B⁄κ])
    Module.Finite.fg_top (by rw [hsmul])
  have hrmem : r ∈ Ideal.torsionOf B Ω[B⁄κ] ω := (Ideal.mem_torsionOf_iff _ _).mpr (hr ω Submodule.mem_top)
  have hr𝔪 : r ∈ 𝔪 := hle hrmem
  have h1 : (1 : B) ∈ 𝔪 := by
    have := 𝔪.sub_mem hr𝔪 hr1
    rwa [sub_sub_cancel] at this
  exact h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end Algebra

theorem main {κ : Type u} [Field κ] [IsAlgClosed κ] {K : Scheme.{u}} (fK : K ⟶ Spec (CommRingCat.of κ))
    [LocallyOfFiniteType fK]
    (h : ∀ v : Spec (CommRingCat.of (DualNumber κ)) ⟶ K,
      v ≫ fK = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) →
      v = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) ≫
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ v) :
    Etale fK := by
  haveI : Flat fK := inferInstance
  haveI : LocallyOfFinitePresentation fK := inferInstance
  haveI : FormallyUnramified fK := by
    refine (IsZariskiLocalAtSource.iff_of_openCover (P := @FormallyUnramified) K.affineCover).mpr fun i => ?_
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (K.affineCover.f i ≫ fK)
    haveI : IsOpenImmersion (K.affineCover.f i) := K.affineCover.map_prop i
    have hloft : LocallyOfFiniteType (K.affineCover.f i ≫ fK) :=
      MorphismProperty.comp_mem _ _ _ (inferInstance : LocallyOfFiniteType (K.affineCover.f i)) inferInstance
    have hφ' : K.affineCover.f i ≫ fK = Spec.map φ := hφ.symm
    rw [hφ'] at hloft ⊢
    have hft : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp hloft
    refine (HasRingHomProperty.Spec_iff (P := @FormallyUnramified) (φ := φ)).mpr ?_
    algebraize [φ.hom]
    refine ⟨subsingleton_kaehlerDifferential fun ψ b => ?_⟩

    let v : Spec (CommRingCat.of (DualNumber κ)) ⟶ K := Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ K.affineCover.f i
    have hv : v ≫ fK = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) := by
      simp only [v, Category.assoc, ← hφ, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun c => ψ.commutes c)
    have hh := h v hv
    have hmono : Spec.map (CommRingCat.ofHom ψ.toRingHom) =
        Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) ≫
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
      exact (cancel_mono (K.affineCover.f i)).mp (by simp only [v, Category.assoc] at hh; exact hh)
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at hmono
    have hb := congrArg (fun g : CommRingCat.of _ ⟶ CommRingCat.of (DualNumber κ) => g.hom b) hmono

    have := congrArg TrivSqZeroExt.snd hb
    simp at this
    exact this
  exact Etale.of_formallyUnramified_of_flat fK

end AlgebraicGeometry.TanCrit

theorem solution
    {κ : Type u} [Field κ] [IsAlgClosed κ] {K : Scheme.{u}} (fK : K ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType fK]
    (h : ∀ v : Spec (CommRingCat.of (DualNumber κ)) ⟶ K,
      v ≫ fK = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) →
      v = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) ≫
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ v) :
    Etale fK :=
  AlgebraicGeometry.TanCrit.main fK h

end S_AlgebraicGeometry_etale_of_forall_dualNumber_eq_comp
end P2MW
export P2MW.S_AlgebraicGeometry_etale_of_forall_dualNumber_eq_comp (solution)
