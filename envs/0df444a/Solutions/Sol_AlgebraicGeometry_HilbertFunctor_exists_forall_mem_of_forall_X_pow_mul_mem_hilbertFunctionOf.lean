-- Prove2me | solution 1 for AlgebraicGeometry.HilbertFunctor.exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/81a632af-adbf-5f5f-a8ff-9a75baa9a4b3

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_map
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf

set_option autoImplicit false
set_option maxHeartbeats 3200000
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SatHighReduce

variable {A : Type} [CommRing A] {n : ℕ}

def mulX (N d : ℕ) (i : Fin (n + 1)) :
    ↥(homogeneousSubmodule (Fin (n + 1)) A d) →ₗ[A] ↥(homogeneousSubmodule (Fin (n + 1)) A (N + d)) :=
  (LinearMap.mulLeft A (X i ^ N : MvPolynomial (Fin (n + 1)) A)).restrict fun G hG => by
    rw [mem_homogeneousSubmodule] at hG ⊢
    exact (isHomogeneous_X_pow i N).mul hG

theorem mulX_apply_coe (N d : ℕ) (i : Fin (n + 1)) (G : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :
    ((mulX N d i G) : MvPolynomial (Fin (n + 1)) A) = X i ^ N * (G : MvPolynomial (Fin (n + 1)) A) := rfl

def phi (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (N d : ℕ) (i : Fin (n + 1)) :
    piece I d →ₗ[A] piece I (N + d) :=
  Submodule.mapQ _ _ (mulX N d i) fun G hG => by
    simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.restrictScalars_mem] at hG ⊢
    rw [mulX_apply_coe]
    exact Ideal.mul_mem_left _ _ hG

theorem phi_mk (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (N d : ℕ) (i : Fin (n + 1))
    (G : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :
    phi I N d i (Submodule.Quotient.mk G) = Submodule.Quotient.mk (mulX N d i G) := rfl

theorem mk_eq_zero_iff (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (d : ℕ)
    (G : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :
    (Submodule.Quotient.mk G : piece I d) = 0 ↔ (G : MvPolynomial (Fin (n + 1)) A) ∈ I := by
  rw [Submodule.Quotient.mk_eq_zero]
  simp [Submodule.mem_comap]

theorem eq_zero_of_forall_field {M M' : Type} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    [Module.Finite A M] [Module.Projective A M] [Module.Finite A M'] [Module.Flat A M']
    (Φ : M →ₗ[A] M')
    (hfield : ∀ (k : Type) [Field k] [Algebra A k] (z : k ⊗[A] M), Φ.baseChange k z = 0 → z = 0)
    (x : M) (hx : Φ x = 0) : x = 0 := by
  refine Module.eq_zero_of_localization_maximal
    (fun (P : Ideal A) (_ : P.IsMaximal) => Localization.AtPrime P ⊗[A] M)
    (fun (P : Ideal A) (_ : P.IsMaximal) => TensorProduct.mk A (Localization.AtPrime P) M 1) x ?_
  intro P hP
  haveI : Module.Free (Localization.AtPrime P) (Localization.AtPrime P ⊗[A] M) :=
    Module.free_of_flat_of_isLocalRing
  haveI : Module.Free (Localization.AtPrime P) (Localization.AtPrime P ⊗[A] M') :=
    Module.free_of_flat_of_isLocalRing
  have hl : Φ.baseChange (Localization.AtPrime P) ((1 : Localization.AtPrime P) ⊗ₜ[A] x) = 0 := by
    rw [LinearMap.baseChange_tmul, hx, TensorProduct.tmul_zero]

  have hnat : ∀ (v : IsLocalRing.ResidueField (Localization.AtPrime P) ⊗[Localization.AtPrime P]
        (Localization.AtPrime P ⊗[A] M)),
      TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.AtPrime P)
          (IsLocalRing.ResidueField (Localization.AtPrime P)) (IsLocalRing.ResidueField (Localization.AtPrime P)) M'
          (((Φ.baseChange (Localization.AtPrime P)).lTensor (IsLocalRing.ResidueField (Localization.AtPrime P))) v) =
        Φ.baseChange (IsLocalRing.ResidueField (Localization.AtPrime P))
          (TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.AtPrime P)
            (IsLocalRing.ResidueField (Localization.AtPrime P)) (IsLocalRing.ResidueField (Localization.AtPrime P)) M v) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => rw [map_zero, LinearEquiv.map_zero, LinearEquiv.map_zero, map_zero]
    | add u u' hu hu' => rw [map_add, LinearEquiv.map_add, hu, hu', LinearEquiv.map_add, map_add]
    | tmul a y =>
      induction y using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero, map_zero, LinearEquiv.map_zero, LinearEquiv.map_zero, map_zero]
      | add u u' hu hu' =>
        rw [TensorProduct.tmul_add, map_add, LinearEquiv.map_add, hu, hu', LinearEquiv.map_add, map_add]
      | tmul r z =>
        rw [LinearMap.lTensor_tmul, LinearMap.baseChange_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.baseChange_tmul]
  obtain ⟨l', hl'⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective
    (Φ.baseChange (Localization.AtPrime P))).mpr (by
      intro w₁ w₂ hw
      rw [← sub_eq_zero] at hw ⊢
      rw [← map_sub] at hw
      have hcw := hfield (IsLocalRing.ResidueField (Localization.AtPrime P)) _ (by
        rw [← hnat (w₁ - w₂), hw, LinearEquiv.map_zero])
      exact (LinearEquiv.map_eq_zero_iff _).mp hcw)
  have hlinj : Function.Injective (Φ.baseChange (Localization.AtPrime P)) := by
    intro a b hab
    have := congrArg l' hab
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hl', LinearMap.id_apply, LinearMap.id_apply] at this
  change ((1 : Localization.AtPrime P) ⊗ₜ[A] x) = 0
  exact hlinj (by rw [hl, map_zero])

end SatHighReduce

open SatHighReduce in
theorem solution
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ m : ℕ, D₀ ≤ m → ∀ (A : Type) [CommRing A] (p : Point A n (hilbertFunctionOf n P m))
      (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) A), F.IsHomogeneous d →
        (∀ i : Fin (n + 1), ∃ N : ℕ, X i ^ N * F ∈ p.I) → F ∈ p.I := by
  classical
  obtain ⟨D₀, hD₀⟩ := AlgebraicGeometry.HilbertFunctor.exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field n P hP
  refine ⟨D₀, fun m hm A _ p d hd F hF hsat => ?_⟩

  choose Nf hNf using hsat
  set N : ℕ := Finset.univ.sup Nf with hN
  have hN' : ∀ i : Fin (n + 1), X i ^ N * F ∈ p.I := by
    intro i
    have hle : Nf i ≤ N := Finset.le_sup (Finset.mem_univ i)
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
    have : (X i ^ N * F : MvPolynomial (Fin (n + 1)) A) = X i ^ c * (X i ^ Nf i * F) := by rw [hc]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (hNf i)

  let M := piece p.I d
  let G : ↥(homogeneousSubmodule (Fin (n + 1)) A d) := ⟨F, (mem_homogeneousSubmodule d F).mpr hF⟩
  let x : M := Submodule.Quotient.mk G
  suffices hx : x = 0 from (mk_eq_zero_iff p.I d G).mp hx
  have hφx : ∀ i, phi p.I N d i x = 0 := fun i => by
    rw [show x = Submodule.Quotient.mk G from rfl, phi_mk, mk_eq_zero_iff, mulX_apply_coe]; exact hN' i

  haveI hfin : ∀ e, Module.Finite A (piece p.I e) := p.finite_piece
  haveI hproj : ∀ e, Module.Projective A (piece p.I e) := p.projective_piece

  have hfield : ∀ (k : Type) [Field k] [Algebra A k] (z : k ⊗[A] M),
      (∀ i, (phi p.I N d i).baseChange k z = 0) → z = 0 := by
    intro k _ _ z hz

    obtain ⟨q, hq⟩ := AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_map n (hilbertFunctionOf n P m) A k p
    obtain ⟨-, hbc⟩ := AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map n A k p.I p.homogeneous
    obtain ⟨e, he⟩ := hbc d
    obtain ⟨e', he'⟩ := hbc (N + d)

    have hsq : ∀ (i : Fin (n + 1)) (w : k ⊗[A] M),
        e' ((phi p.I N d i).baseChange k w) =
          phi (p.I.map (MvPolynomial.map (algebraMap A k))) N d i (e w) := by
      intro i w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add u v hu hv => simp [map_add, hu, hv]
      | tmul b y =>
        obtain ⟨G', rfl⟩ := Submodule.Quotient.mk_surjective _ y
        have hG' := (mem_homogeneousSubmodule d (G' : MvPolynomial (Fin (n + 1)) A)).mp G'.2
        have h1 : (b ⊗ₜ[A] (Submodule.Quotient.mk G' : M)) = b • ((1 : k) ⊗ₜ[A] (Submodule.Quotient.mk G' : M)) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [h1, map_smul, map_smul, map_smul, map_smul, LinearMap.baseChange_tmul, phi_mk]
        congr 1
        have h2 := he' (mulX N d i G' : MvPolynomial (Fin (n + 1)) A)
          ((mem_homogeneousSubmodule _ _).mp (mulX N d i G').2)
        have h3 := he (G' : MvPolynomial (Fin (n + 1)) A) hG'

        have eG' : (Submodule.Quotient.mk G' : M) = Submodule.Quotient.mk ⟨(G' : MvPolynomial (Fin (n + 1)) A), G'.2⟩ := by
          rfl
        rw [show (Submodule.Quotient.mk (mulX N d i G') : piece p.I (N + d)) =
            Submodule.Quotient.mk ⟨(mulX N d i G' : MvPolynomial (Fin (n + 1)) A),
              (mem_homogeneousSubmodule _ _).mpr ((mem_homogeneousSubmodule _ _).mp (mulX N d i G').2)⟩ from rfl]
        rw [h2]
        rw [show (Submodule.Quotient.mk G' : M) =
            Submodule.Quotient.mk ⟨(G' : MvPolynomial (Fin (n + 1)) A), (mem_homogeneousSubmodule d _).mpr hG'⟩ from rfl, h3, phi_mk]
        apply congrArg
        apply Subtype.ext
        simp [mulX_apply_coe, map_mul, map_pow, MvPolynomial.map_X]

    have hinj : Function.Injective e := e.injective
    apply hinj
    rw [map_zero]
    obtain ⟨G', hG'e⟩ := Submodule.Quotient.mk_surjective _ (e z)
    rw [← hG'e]
    refine (mk_eq_zero_iff _ d G').mpr ?_
    rw [← hq]
    have hG' := (mem_homogeneousSubmodule d (G' : MvPolynomial (Fin (n + 1)) k)).mp G'.2
    refine hD₀ m hm k q d hd (G' : MvPolynomial (Fin (n + 1)) k) hG' fun i => ⟨N, ?_⟩
    rw [hq]
    have := hsq i z
    rw [hz i, map_zero, ← hG'e, phi_mk, eq_comm, mk_eq_zero_iff, mulX_apply_coe] at this
    exact this

  haveI : Module.Flat A ((i : Fin (n + 1)) → piece p.I (N + d)) :=
    Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype A (Fin (n + 1)) (fun _ => piece p.I (N + d))).symm
  refine eq_zero_of_forall_field (LinearMap.pi fun i => phi p.I N d i) ?_ x (by ext i; exact hφx i)
  intro k _ _ z hz
  refine hfield k z fun i => ?_
  have hcomp : phi p.I N d i = (LinearMap.proj i) ∘ₗ (LinearMap.pi fun j => phi p.I N d j) := by ext y; rfl
  rw [hcomp, LinearMap.baseChange_comp, LinearMap.comp_apply, hz, map_zero]

end
end S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf
end P2MW
export P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf (solution)
