-- Prove2me | solution 1 for Algebra.Etale.exists_free_nonempty_algEquiv_baseChange_residueField_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/04a208dc-d2d4-53ce-8c5f-0a46dbda17d9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_Etale_exists_free_nonempty_algEquiv_baseChange_residueField_of_isLocalRing

set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace H2Aux

open Polynomial

section jacobson

variable {R : Type*} [CommRing R] [IsLocalRing R] {A : Type*} [CommRing A] [Algebra R A] [Module.Finite R A]

theorem map_maximalIdeal_le_of_isMaximal (𝔫 : Ideal A) [𝔫.IsMaximal] :
    (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≤ 𝔫 := by
  haveI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  rw [Ideal.map_le_iff_le_comap]
  haveI : (𝔫.comap (algebraMap R A)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔫
  exact (IsLocalRing.eq_maximalIdeal inferInstance).ge

theorem isUnit_one_add_of_mem_map_maximalIdeal {x : A}
    (hx : x ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) : IsUnit (1 + x) := by
  have hj : x ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro 𝔫 ⟨-, h𝔫⟩
    haveI := h𝔫
    exact map_maximalIdeal_le_of_isMaximal 𝔫 hx
  have := Ideal.mem_jacobson_bot.mp hj 1
  rwa [mul_one, add_comm] at this

end jacobson

section standardEtale

variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem exists_derivative_mul_add_mul_eq_one (p : R[X]) (hp : p.Monic)
    (hsep : (p.map (IsLocalRing.residue R)).Separable) :
    ∃ p₁ p₂ : R[X], derivative p * p₁ + p * p₂ = 1 := by
  obtain ⟨abar, bbar, hab⟩ := hsep
  obtain ⟨a, rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue R) IsLocalRing.residue_surjective abar
  obtain ⟨b, rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue R) IsLocalRing.residue_surjective bbar

  set q : R[X] := a * p + b * derivative p - 1 with hq
  have hqmap : q.map (IsLocalRing.residue R) = 0 := by
    rw [hq, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      ← Polynomial.derivative_map, hab, Polynomial.map_one, sub_self]

  haveI : Module.Finite R (AdjoinRoot p) := (AdjoinRoot.powerBasis' hp).finite
  have hqmem : AdjoinRoot.mk p q ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R (AdjoinRoot p)) := by
    have hC : q ∈ (IsLocalRing.maximalIdeal R).map (Polynomial.C : R →+* R[X]) := by
      rw [Ideal.mem_map_C_iff]
      intro n
      have := congrArg (fun r => r.coeff n) hqmap
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
      exact (IsLocalRing.residue_eq_zero_iff _).mp this
    rw [AdjoinRoot.algebraMap_eq, show (AdjoinRoot.of p) = (AdjoinRoot.mk p).comp Polynomial.C from rfl,
      ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hC
  obtain ⟨u, hu⟩ := isUnit_one_add_of_mem_map_maximalIdeal hqmem

  have hb : AdjoinRoot.mk p (b * derivative p) = 1 + AdjoinRoot.mk p q := by
    simp only [hq, map_sub, map_add, map_mul, map_one, AdjoinRoot.mk_self, mul_zero, zero_add, add_sub_cancel]
  obtain ⟨c, hc⟩ := AdjoinRoot.mk_surjective (AdjoinRoot.mk p b * (↑u⁻¹ : AdjoinRoot p))
  have h1 : AdjoinRoot.mk p (derivative p * c - 1) = 0 := by
    rw [map_sub, map_one, map_mul, hc, ← mul_assoc, mul_comm (AdjoinRoot.mk p (derivative p)) (AdjoinRoot.mk p b),
      ← map_mul, hb, ← hu, Units.mul_inv, sub_self]
  obtain ⟨d, hd⟩ := (AdjoinRoot.mk_eq_zero).mp h1
  exact ⟨c, -d, by linear_combination hd⟩

theorem etale_adjoinRoot (p : R[X]) (hp : p.Monic)
    (hsep : (p.map (IsLocalRing.residue R)).Separable) : Algebra.Etale R (AdjoinRoot p) := by
  obtain ⟨p₁, p₂, h⟩ := exists_derivative_mul_add_mul_eq_one p hp hsep
  let P : StandardEtalePair R := ⟨p, hp, 1, p₁, p₂, 0, by rw [pow_zero, h]⟩
  have hunit : Submonoid.powers (AdjoinRoot.mk P.f P.g) ≤ IsUnit.submonoid (AdjoinRoot P.f) := by
    rintro x ⟨n, rfl⟩
    show IsUnit ((AdjoinRoot.mk P.f P.g) ^ n)
    rw [show P.g = 1 from rfl, map_one, one_pow]
    exact isUnit_one
  let e₁ : AdjoinRoot p ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    (IsLocalization.atUnits (AdjoinRoot P.f) (Submonoid.powers (AdjoinRoot.mk P.f P.g)) hunit).restrictScalars R
  let e : P.Ring ≃ₐ[R] AdjoinRoot p := P.equivAwayAdjoinRoot.trans e₁.symm
  haveI : Algebra.IsStandardEtale R (AdjoinRoot p) := Algebra.IsStandardEtale.of_equiv e
  infer_instance

end standardEtale

section baseChange

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] (p : R[X])

noncomputable def bcHom : S ⊗[R] AdjoinRoot p →ₐ[S] AdjoinRoot (p.map (algebraMap R S)) :=
  Algebra.TensorProduct.lift (Algebra.ofId S _)
    (AdjoinRoot.liftAlgHom p (Algebra.ofId R _) (AdjoinRoot.root (p.map (algebraMap R S))) (by
      rw [show ((Algebra.ofId R (AdjoinRoot (p.map (algebraMap R S)))) : R →+* _) =
          (algebraMap S (AdjoinRoot (p.map (algebraMap R S)))).comp (algebraMap R S) from
          (IsScalarTower.algebraMap_eq R S _),
        ← Polynomial.eval₂_map, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root]))
    (fun _ _ => Commute.all _ _)

noncomputable def bcInv : AdjoinRoot (p.map (algebraMap R S)) →ₐ[S] S ⊗[R] AdjoinRoot p :=
  AdjoinRoot.liftAlgHom (p.map (algebraMap R S)) (Algebra.ofId S _) ((1 : S) ⊗ₜ[R] AdjoinRoot.root p) (by
    rw [show ((Algebra.ofId S (S ⊗[R] AdjoinRoot p)) : S →+* _) = algebraMap S (S ⊗[R] AdjoinRoot p) from rfl,
      Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq,
      show (1 : S) ⊗ₜ[R] AdjoinRoot.root p = Algebra.TensorProduct.includeRight (AdjoinRoot.root p) from rfl,
      ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero])

theorem bcHom_tmul_one_root :
    bcHom S p ((1 : S) ⊗ₜ[R] AdjoinRoot.root p) = AdjoinRoot.root (p.map (algebraMap R S)) := by
  simp [bcHom, Algebra.TensorProduct.lift_tmul]

theorem bcInv_root :
    bcInv S p (AdjoinRoot.root (p.map (algebraMap R S))) = (1 : S) ⊗ₜ[R] AdjoinRoot.root p := by
  simp [bcInv]

noncomputable def bcEquiv : S ⊗[R] AdjoinRoot p ≃ₐ[S] AdjoinRoot (p.map (algebraMap R S)) :=
  AlgEquiv.ofAlgHom (bcHom S p) (bcInv S p)
    (AdjoinRoot.algHom_ext (by rw [AlgHom.comp_apply, bcInv_root, bcHom_tmul_one_root, AlgHom.id_apply]))
    (Algebra.TensorProduct.ext (by ext) (AdjoinRoot.algHom_ext (by
      simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
        Algebra.TensorProduct.includeRight_apply, AlgHom.id_apply]
      rw [bcHom_tmul_one_root, bcInv_root])))

end baseChange

end H2Aux

open Polynomial in

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R]
    (Ebar : Type v) [CommRing Ebar] [Algebra (IsLocalRing.ResidueField R) Ebar]
    [Module.Finite (IsLocalRing.ResidueField R) Ebar] [Algebra.Etale (IsLocalRing.ResidueField R) Ebar] :
    ∃ (E : Type (max u v)) (_ : CommRing E) (_ : Algebra R E),
      Module.Finite R E ∧ Module.Free R E ∧ Algebra.Etale R E ∧
      Nonempty (IsLocalRing.ResidueField R ⊗[R] E ≃ₐ[IsLocalRing.ResidueField R] Ebar) := by
  classical
  let k := IsLocalRing.ResidueField R

  obtain ⟨I, hI, Ai, hF, hAlg, e, hsep⟩ := (Algebra.Etale.iff_exists_algEquiv_prod k Ebar).mp inferInstance
  haveI := Fintype.ofFinite I
  haveI : ∀ i, Module.Finite k (Ai i) := fun i => (hsep i).1
  haveI : ∀ i, Algebra.IsSeparable k (Ai i) := fun i => (hsep i).2

  let pb : ∀ i, PowerBasis k (Ai i) := fun i => Field.powerBasisOfFiniteOfSeparable k (Ai i)
  have hl : ∀ i, ∃ p : R[X], p.map (IsLocalRing.residue R) = minpoly k (pb i).gen ∧ p.Monic := fun i => by
    obtain ⟨p, hp, -, hm⟩ := Polynomial.lifts_and_degree_eq_and_monic
      (Polynomial.map_surjective (IsLocalRing.residue R) IsLocalRing.residue_surjective _)
      (minpoly.monic (pb i).isIntegral_gen)
    exact ⟨p, hp, hm⟩
  choose p hpmap hpmon using hl
  have hpsep : ∀ i, ((p i).map (IsLocalRing.residue R)).Separable := fun i => by
    rw [hpmap]; exact Algebra.IsSeparable.isSeparable k (pb i).gen

  haveI hfin : ∀ i, Module.Finite R (AdjoinRoot (p i)) := fun i => (AdjoinRoot.powerBasis' (hpmon i)).finite
  haveI hfree : ∀ i, Module.Free R (AdjoinRoot (p i)) := fun i =>
    Module.Free.of_basis (R := R) (M := AdjoinRoot (p i)) (AdjoinRoot.powerBasis' (hpmon i)).basis
  haveI het : ∀ i, Algebra.Etale R (AdjoinRoot (p i)) := fun i => H2Aux.etale_adjoinRoot (p i) (hpmon i) (hpsep i)
  refine ⟨(i : I) → AdjoinRoot (p i), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩

  have hq : ∀ i, (p i).map (algebraMap R k) = minpoly k (pb i).gen := fun i => by
    rw [IsLocalRing.ResidueField.algebraMap_eq]; exact hpmap i
  let f : ∀ i, AdjoinRoot ((p i).map (algebraMap R k)) ≃ₐ[k] Ai i := fun i =>
    (AdjoinRoot.algEquivOfEq k _ _ (hq i)).trans
      ((AdjoinRoot.powerBasis (minpoly.ne_zero (pb i).isIntegral_gen)).equivOfMinpoly (pb i)
        (AdjoinRoot.minpoly_powerBasis_gen_of_monic (minpoly.monic (pb i).isIntegral_gen)))
  exact ((Algebra.TensorProduct.piRight R k k (fun i => AdjoinRoot (p i))).trans
    (AlgEquiv.piCongrRight fun i => (H2Aux.bcEquiv k (p i)).trans (f i))).trans e.symm

end S_Algebra_Etale_exists_free_nonempty_algEquiv_baseChange_residueField_of_isLocalRing
end P2MW
export P2MW.S_Algebra_Etale_exists_free_nonempty_algEquiv_baseChange_residueField_of_isLocalRing (solution)
