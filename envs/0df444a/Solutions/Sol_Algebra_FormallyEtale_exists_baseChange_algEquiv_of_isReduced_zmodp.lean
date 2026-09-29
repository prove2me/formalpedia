-- Prove2me | solution 1 for Algebra.FormallyEtale.exists_baseChange_algEquiv_of_isReduced_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/08f14545-6a4c-5a13-affa-777b19984bb7

import Mathlib
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallyEtale_exists_baseChange_algEquiv_of_isReduced_zmodp

set_option autoImplicit false

open Polynomial
open scoped TensorProduct

universe u v

namespace EtqaLift

section Field

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]

private theorem exists_map_eq (q : (ZMod p)[X]) : ∃ Q : 𝓞[X], Q.map (algebraMap 𝓞 (ZMod p)) = q :=
  Polynomial.map_surjective _ (ZMod.ringHom_surjective _) q

private theorem isUnit_mk_of_map_eq_one
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (f g : 𝓞[X]) [IsAdicComplete (Ideal.span {(p : AdjoinRoot f)}) (AdjoinRoot f)]
    (hg : g.map (algebraMap 𝓞 (ZMod p)) = 1) : IsUnit (AdjoinRoot.mk f g) := by
  have h1 : g - 1 ∈ (Ideal.span {(p : 𝓞)}).map (C : 𝓞 →+* 𝓞[X]) := by
    rw [Ideal.mem_map_C_iff]
    intro n
    rw [← hker, RingHom.mem_ker, ← Polynomial.coeff_map, Polynomial.map_sub, hg,
      Polynomial.map_one, sub_self, coeff_zero]
  have h2 : AdjoinRoot.mk f (g - 1) ∈ Ideal.span {(p : AdjoinRoot f)} := by
    have h3 := Ideal.mem_map_of_mem (AdjoinRoot.mk f) h1
    rw [Ideal.map_map, Ideal.map_span, Set.image_singleton, RingHom.comp_apply,
      AdjoinRoot.mk_C, map_natCast] at h3
    exact h3
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp h2
  rw [map_sub, map_one] at he
  have hj : (p : AdjoinRoot f) ∈ (⊥ : Ideal (AdjoinRoot f)).jacobson :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {(p : AdjoinRoot f)}) (Ideal.mem_span_singleton_self _)
  have hu := Ideal.mem_jacobson_bot.mp hj e
  rwa [mul_comm, he, sub_add_cancel] at hu

private theorem field_case
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (k : Type v) [Field k] [Algebra (ZMod p) k] [Module.Finite (ZMod p) k] :
    ∃ f : 𝓞[X], f.Monic ∧ Algebra.FormallyEtale 𝓞 (AdjoinRoot f) ∧
      Nonempty ((ZMod p) ⊗[𝓞] AdjoinRoot f ≃ₐ[ZMod p] k) := by

  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ZMod p) k
  have hint : IsIntegral (ZMod p) α := Algebra.IsIntegral.isIntegral α
  have hgm : (minpoly (ZMod p) α).Monic := minpoly.monic hint
  have hgs : (minpoly (ZMod p) α).Separable := Algebra.IsSeparable.isSeparable (ZMod p) α
  have eK : AdjoinRoot (minpoly (ZMod p) α) ≃ₐ[ZMod p] k :=
    (IntermediateField.adjoinRootEquivAdjoin (ZMod p) hint).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)

  obtain ⟨f, hfmap, -, hfm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (ZMod.ringHom_surjective (algebraMap 𝓞 (ZMod p))) _) hgm
  haveI : Module.Free 𝓞 (AdjoinRoot f) := .of_basis (AdjoinRoot.powerBasis' hfm).basis
  haveI : Module.Finite 𝓞 (AdjoinRoot f) := .of_basis (AdjoinRoot.powerBasis' hfm).basis
  haveI : IsAdicComplete (Ideal.span {(p : AdjoinRoot f)}) (AdjoinRoot f) :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (AdjoinRoot f)
  refine ⟨f, hfm, ?_, ⟨?_⟩⟩
  ·
    obtain ⟨a, b, hab⟩ := hgs
    obtain ⟨A, hA⟩ := exists_map_eq (𝓞 := 𝓞) p a
    obtain ⟨B, hB⟩ := exists_map_eq (𝓞 := 𝓞) p b
    have hgmap : (derivative f * B + f * A).map (algebraMap 𝓞 (ZMod p)) = 1 := by
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
        hfmap, hA, hB, ← hab]
      ring
    have hunit : IsUnit (AdjoinRoot.mk f (derivative f * B + f * A)) :=
      isUnit_mk_of_map_eq_one p hker f _ hgmap
    let P : StandardEtalePair 𝓞 :=
      { f := f
        monic_f := hfm
        g := derivative f * B + f * A
        cond := ⟨B, A, 1, (pow_one _).symm⟩ }
    have e1 : P.Ring ≃ₐ[𝓞] Localization.Away (AdjoinRoot.mk f (derivative f * B + f * A)) :=
      P.equivAwayAdjoinRoot
    have e2 : AdjoinRoot f ≃ₐ[AdjoinRoot f]
        Localization.Away (AdjoinRoot.mk f (derivative f * B + f * A)) :=
      IsLocalization.atUnits (AdjoinRoot f)
        (Submonoid.powers (AdjoinRoot.mk f (derivative f * B + f * A)))
        (by
          rintro _ ⟨n, rfl⟩
          exact (hunit.pow n))
    exact Algebra.FormallyEtale.of_equiv (e1.trans (e2.restrictScalars 𝓞).symm)
  ·
    let C := AdjoinRoot (minpoly (ZMod p) α)
    have hφ : (minpoly (ZMod p) α).eval₂ (algebraMap (ZMod p) ((ZMod p) ⊗[𝓞] AdjoinRoot f))
        ((1 : ZMod p) ⊗ₜ[𝓞] AdjoinRoot.root f) = 0 := by
      rw [← hfmap, Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq,
        ← Polynomial.aeval_def, ← Algebra.TensorProduct.includeRight_apply,
        Polynomial.aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
    let φ : C →ₐ[ZMod p] (ZMod p) ⊗[𝓞] AdjoinRoot f :=
      AdjoinRoot.liftAlgHom (minpoly (ZMod p) α) (Algebra.ofId (ZMod p) _) _ hφ
    have hψ : f.eval₂ (algebraMap 𝓞 C) (AdjoinRoot.root (minpoly (ZMod p) α)) = 0 := by
      rw [IsScalarTower.algebraMap_eq 𝓞 (ZMod p) C, ← Polynomial.eval₂_map, hfmap,
        ← Polynomial.aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    let ψ₀ : AdjoinRoot f →ₐ[𝓞] C := AdjoinRoot.liftAlgHom f (Algebra.ofId 𝓞 C) _ hψ
    let ψ : (ZMod p) ⊗[𝓞] AdjoinRoot f →ₐ[ZMod p] C :=
      Algebra.TensorProduct.lift (Algebra.ofId (ZMod p) C) ψ₀ (fun _ _ => Commute.all _ _)
    have h1 : ψ.comp φ = AlgHom.id (ZMod p) C := by
      apply AdjoinRoot.algHom_ext
      rw [AlgHom.comp_apply, AlgHom.id_apply]
      show ψ (φ (AdjoinRoot.root _)) = _
      rw [AdjoinRoot.liftAlgHom_root, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact AdjoinRoot.liftAlgHom_root f (Algebra.ofId 𝓞 C) _ hψ
    have h2 : φ.comp ψ = AlgHom.id (ZMod p) ((ZMod p) ⊗[𝓞] AdjoinRoot f) := by
      apply Algebra.TensorProduct.ext
      · exact Subsingleton.elim _ _
      · apply AdjoinRoot.algHom_ext
        simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
          Algebra.TensorProduct.includeRight_apply, AlgHom.id_apply]
        show φ (ψ ((1 : ZMod p) ⊗ₜ[𝓞] AdjoinRoot.root f)) = (1 : ZMod p) ⊗ₜ[𝓞] AdjoinRoot.root f
        rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        show φ (ψ₀ (AdjoinRoot.root f)) = _
        rw [AdjoinRoot.liftAlgHom_root f (Algebra.ofId 𝓞 C) _ hψ]
        exact AdjoinRoot.liftAlgHom_root (minpoly (ZMod p) α) (Algebra.ofId (ZMod p) _) _ hφ
    exact (AlgEquiv.ofAlgHom ψ φ h1 h2).trans eK

end Field

end EtqaLift

open EtqaLift in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (Hbar : Type v) [CommRing Hbar] [Algebra (ZMod p) Hbar] [Module.Finite (ZMod p) Hbar] [IsReduced Hbar] :
    ∃ (H : Type u) (_ : CommRing H) (_ : Algebra 𝓞 H) (_ : Module.Free 𝓞 H) (_ : Module.Finite 𝓞 H)
      (_ : Algebra.FormallyEtale 𝓞 H),
      Module.finrank 𝓞 H = Module.finrank (ZMod p) Hbar ∧
      Nonempty ((ZMod p ⊗[𝓞] H) ≃ₐ[ZMod p] Hbar) := by
  classical
  haveI : Nontrivial 𝓞 := RingHom.domain_nontrivial (algebraMap 𝓞 (ZMod p))
  haveI : IsArtinianRing Hbar := IsArtinianRing.of_finite (ZMod p) Hbar
  let ι := MaximalSpectrum Hbar
  haveI : Fintype ι := Fintype.ofFinite ι
  let eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι

  have hfield : ∀ I : ι, ∃ f : Polynomial 𝓞, f.Monic ∧ Algebra.FormallyEtale 𝓞 (AdjoinRoot f) ∧
      Nonempty ((ZMod p) ⊗[𝓞] AdjoinRoot f ≃ₐ[ZMod p] (Hbar ⧸ I.asIdeal)) := fun I => by
    letI : Field (Hbar ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    exact EtqaLift.field_case p hker (Hbar ⧸ I.asIdeal)
  choose f hfm hfet hfiso using hfield
  let E : Fin (Fintype.card ι) → Type u := fun i => AdjoinRoot (f (eι.symm i))
  haveI : ∀ i, Module.Free 𝓞 (E i) := fun i => .of_basis (AdjoinRoot.powerBasis' (hfm _)).basis
  haveI : ∀ i, Module.Finite 𝓞 (E i) := fun i => .of_basis (AdjoinRoot.powerBasis' (hfm _)).basis
  haveI : ∀ i, Algebra.FormallyEtale 𝓞 (E i) := fun i => hfet _

  have eH : (ZMod p ⊗[𝓞] (∀ i, E i)) ≃ₐ[ZMod p] Hbar :=
    (Algebra.TensorProduct.piRight 𝓞 (ZMod p) (ZMod p) E).trans
      ((AlgEquiv.piCongrRight fun i => (hfiso (eι.symm i)).some).trans
        ((AlgEquiv.piCongrLeft' (ZMod p) (fun I : ι => Hbar ⧸ I.asIdeal) eι).symm.trans
          ((IsArtinianRing.equivPi Hbar).restrictScalars (ZMod p)).symm))
  refine ⟨∀ i, E i, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ⟨eH⟩⟩
  rw [← eH.toLinearEquiv.finrank_eq, Module.finrank_baseChange]

end S_Algebra_FormallyEtale_exists_baseChange_algEquiv_of_isReduced_zmodp
end P2MW
export P2MW.S_Algebra_FormallyEtale_exists_baseChange_algEquiv_of_isReduced_zmodp (solution)
