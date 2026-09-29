-- Prove2me | solution 1 for AdjoinRoot.exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/e2a69f69-1f2c-5c95-8edf-3cacfbdb9c5e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdjoinRoot_exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map

set_option autoImplicit false

universe u

open Polynomial IsLocalRing

namespace P2mAdjoinRootLocalStep

variable {R : Type u} [CommRing R] [IsLocalRing R] (f : R[X])

noncomputable abbrev J : Ideal (AdjoinRoot f) := (maximalIdeal R).map (AdjoinRoot.of f)

omit [IsLocalRing R] in
theorem algebraMap_eq_of : algebraMap R (AdjoinRoot f) = AdjoinRoot.of f := rfl

theorem isField_quotient_J [Fact (Irreducible (f.map (residue R)))] : IsField (AdjoinRoot f ⧸ J f) := by
  have hK : IsField ((R ⧸ maximalIdeal R)[X] ⧸ Ideal.span {f.map (Ideal.Quotient.mk (maximalIdeal R))}) :=
    Field.toIsField (AdjoinRoot (f.map (residue R)))
  exact MulEquiv.isField hK (AdjoinRoot.quotEquivQuotMap f (maximalIdeal R)).toMulEquiv

theorem isMaximal_J [Fact (Irreducible (f.map (residue R)))] : (J f).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ (isField_quotient_J f)

variable {f}

theorem eq_J_of_isMaximal (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))]
    (N : Ideal (AdjoinRoot f)) (hN : N.IsMaximal) : N = J f := by
  haveI : Module.Finite R (AdjoinRoot f) := Module.Finite.of_basis (AdjoinRoot.powerBasis' hfm).basis
  haveI : Algebra.IsIntegral R (AdjoinRoot f) := Algebra.IsIntegral.of_finite R (AdjoinRoot f)
  have hcomap : (N.comap (algebraMap R (AdjoinRoot f))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal N
  have hcomap' : N.comap (algebraMap R (AdjoinRoot f)) = maximalIdeal R := IsLocalRing.eq_maximalIdeal hcomap
  have hle : J f ≤ N := by
    rw [J, ← algebraMap_eq_of, Ideal.map_le_iff_le_comap, hcomap']
  exact ((isMaximal_J f).eq_of_le hN.ne_top hle).symm

theorem isLocalRing (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))] : IsLocalRing (AdjoinRoot f) :=
  IsLocalRing.of_unique_max_ideal ⟨J f, isMaximal_J f, fun N hN => eq_J_of_isMaximal hfm N hN⟩

theorem maximalIdeal_eq (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))] :
    @maximalIdeal (AdjoinRoot f) _ (isLocalRing hfm) = J f :=
  letI := isLocalRing hfm
  eq_J_of_isMaximal hfm _ (IsLocalRing.maximalIdeal.isMaximal _)

theorem isLocalHom (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))] :
    IsLocalHom (algebraMap R (AdjoinRoot f)) := by
  letI := isLocalRing hfm
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hmem : a ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).2 hna
  have hJmem : algebraMap R (AdjoinRoot f) a ∈ maximalIdeal (AdjoinRoot f) := by
    rw [maximalIdeal_eq hfm]
    exact Ideal.mem_map_of_mem _ hmem
  exact (IsLocalRing.mem_maximalIdeal _).1 hJmem ha

theorem nonempty_residueField_algEquiv (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))] :
    letI := isLocalRing hfm
    letI := isLocalHom hfm
    Nonempty (ResidueField (AdjoinRoot f) ≃ₐ[ResidueField R] AdjoinRoot (f.map (residue R))) := by
  letI := isLocalRing hfm
  letI := isLocalHom hfm

  let e₁ : ResidueField (AdjoinRoot f) ≃ₐ[R] AdjoinRoot f ⧸ J f :=
    Ideal.quotientEquivAlgOfEq R (maximalIdeal_eq hfm)
  let e₂ : (AdjoinRoot f ⧸ J f) ≃ₐ[R] AdjoinRoot (f.map (residue R)) :=
    AdjoinRoot.quotEquivQuotMap f (maximalIdeal R)
  let e : ResidueField (AdjoinRoot f) ≃ₐ[R] AdjoinRoot (f.map (residue R)) := e₁.trans e₂

  refine ⟨AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun c => ?_⟩
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
  have h1 : algebraMap (ResidueField R) (ResidueField (AdjoinRoot f)) (residue R r) =
      algebraMap R (ResidueField (AdjoinRoot f)) r := by
    rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  have h2 : algebraMap (ResidueField R) (AdjoinRoot (f.map (residue R))) (residue R r) =
      algebraMap R (AdjoinRoot (f.map (residue R))) r := by
    rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  rw [h1, h2]
  exact e.commutes r

end P2mAdjoinRootLocalStep

open P2mAdjoinRootLocalStep in

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R]
    (f : R[X]) (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))] :
    ∃ (_ : IsLocalRing (AdjoinRoot f)) (_ : IsLocalHom (algebraMap R (AdjoinRoot f))),
      Module.Finite R (AdjoinRoot f) ∧ Module.Free R (AdjoinRoot f) ∧ Module.FaithfullyFlat R (AdjoinRoot f) ∧
      Ideal.map (algebraMap R (AdjoinRoot f)) (maximalIdeal R) = maximalIdeal (AdjoinRoot f) ∧
      Nonempty (ResidueField (AdjoinRoot f) ≃ₐ[ResidueField R] AdjoinRoot (f.map (residue R))) := by
  letI hloc := isLocalRing hfm
  letI hlh := isLocalHom hfm
  haveI : Module.Free R (AdjoinRoot f) := Module.Free.of_basis (AdjoinRoot.powerBasis' hfm).basis
  haveI : Module.Finite R (AdjoinRoot f) := Module.Finite.of_basis (AdjoinRoot.powerBasis' hfm).basis
  haveI : Module.Flat R (AdjoinRoot f) := Module.Flat.of_free
  refine ⟨hloc, hlh, inferInstance, inferInstance, Module.FaithfullyFlat.of_flat_of_isLocalHom, ?_,
    nonempty_residueField_algEquiv hfm⟩
  rw [algebraMap_eq_of]
  exact (maximalIdeal_eq hfm).symm

end S_AdjoinRoot_exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map
end P2MW
export P2MW.S_AdjoinRoot_exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map (solution)
