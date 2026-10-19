-- Prove2me | Definitions.Def_MazurTransfer_ValuationSubringInertiaRingData
-- name    : MazurTransfer_ValuationSubringInertiaRingData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T04:26:59.571747+00:00
-- url     : https://prove2.me/theorems/264b7edf-7836-447d-8ddc-75fc9458e80a
-- title:
--   Valuation-ring decomposition actions and inertia residue identities
-- statement:
--   Let $K \subseteq \Omega$ be fields and $A$ a valuation subring of $\Omega$. A decomposition-group element acts by a ring endomorphism of $A$; if it lies in inertia, this action induces the identity after reduction to the residue field. An element of the inertia subgroup viewed inside $\operatorname{Aut}_K(\Omega)$ has such a decomposition-group representative.
--
--   For a commutative ring $R$ mapping compatibly to $K$ and $\Omega$, with its image contained in $A$, retain the induced map $R \to A$ and its compatibility with decomposition actions. These ring-level identities support inertia-fixed lifts for proper unramified morphisms.
-- source:
--   MazurTheorem, P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_specMap_comp_eq_self_of_mem_inertiaSubgroupIn_of_isTorsionPoint.lean, complete original declarations (source SHA-256 e6e8e5a6bf15561393b122e9d63da1e70ee0bb7b75e68cc770ec1c432a3861d6), Apache-2.0. Original declaration types and nonproof values checked in full. Official Anthropic FLT interfaces at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

/- Complete official Anthropic FLT mathematical source, Apache-2.0, pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Only routine tooling aliases and generated metadata normalized. Design boundary: inertia actions and uniqueness of local norm lifts on actual local Picard models. Named downstream consumer: inertia fixed norm fibres and unramified Kummer classes for the SAME order-13 integral norm maps. -/
/- Design boundary: the original decomposition action on a valuation ring,
its residue action and the coefficient ring restriction.
Named downstream consumer: inertia-fixed lifts for proper unramified maps. -/
import Mathlib
import Definitions.Def_FLTPrelim_Ramification

noncomputable section
universe u
namespace MazurTransfer.ValuationSubringInertiaRingData
section RingSide

variable {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω]

theorem exists_of_mem_inertiaSubgroupIn (A : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω)
    (hσ : σ ∈ A.inertiaSubgroupIn K) :
    ∃ d : A.decompositionSubgroup K, d ∈ A.inertiaSubgroup K ∧ (d : Ω ≃ₐ[K] Ω) = σ := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hσ
  exact ⟨d, hd, rfl⟩

noncomputable def decompRingHom (A : ValuationSubring Ω) (d : A.decompositionSubgroup K) :
    A →+* A :=
  MulSemiringAction.toRingHom (A.decompositionSubgroup K) A d

theorem residue_comp_decompRingHom (A : ValuationSubring Ω) (d : A.decompositionSubgroup K)
    (hd : d ∈ A.inertiaSubgroup K) :
    (IsLocalRing.residue A).comp (decompRingHom A d) = IsLocalRing.residue A := by
  ext a
  simp only [RingHom.comp_apply, decompRingHom, MulSemiringAction.toRingHom_apply]
  rw [IsLocalRing.ResidueField.residue_smul]
  have h := hd
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at h
  have := congrArg (fun e : RingAut (IsLocalRing.ResidueField A) => e (IsLocalRing.residue A a)) h
  simpa using this

theorem algebraMap_comp_decompRingHom (A : ValuationSubring Ω) (d : A.decompositionSubgroup K) :
    (algebraMap A Ω).comp (decompRingHom A d) =
      ((d : Ω ≃ₐ[K] Ω) : Ω →+* Ω).comp (algebraMap A Ω) := by
  ext a
  rfl

variable {R : Type u} [CommRing R] [Algebra R Ω] [Algebra R K] [IsScalarTower R K Ω]

noncomputable def toValuationSubring (A : ValuationSubring Ω)
    (hA : ∀ r : R, algebraMap R Ω r ∈ A) : R →+* A :=
  (algebraMap R Ω).codRestrict A.toSubring hA

theorem algebraMap_comp_toValuationSubring (A : ValuationSubring Ω)
    (hA : ∀ r : R, algebraMap R Ω r ∈ A) :
    (algebraMap A Ω).comp (toValuationSubring A hA) = algebraMap R Ω := by
  ext r; rfl

theorem decompRingHom_comp_toValuationSubring (A : ValuationSubring Ω)
    (hA : ∀ r : R, algebraMap R Ω r ∈ A) (d : A.decompositionSubgroup K) :
    (decompRingHom A d).comp (toValuationSubring A hA) = toValuationSubring A hA := by
  ext r
  change (d : Ω ≃ₐ[K] Ω) (algebraMap R Ω r) = algebraMap R Ω r
  rw [IsScalarTower.algebraMap_apply R K Ω, AlgEquiv.commutes]

end RingSide
end MazurTransfer.ValuationSubringInertiaRingData
#print axioms MazurTransfer.ValuationSubringInertiaRingData.exists_of_mem_inertiaSubgroupIn
#print axioms MazurTransfer.ValuationSubringInertiaRingData.decompRingHom
#print axioms MazurTransfer.ValuationSubringInertiaRingData.residue_comp_decompRingHom
#print axioms MazurTransfer.ValuationSubringInertiaRingData.algebraMap_comp_decompRingHom
#print axioms MazurTransfer.ValuationSubringInertiaRingData.toValuationSubring
#print axioms MazurTransfer.ValuationSubringInertiaRingData.algebraMap_comp_toValuationSubring
#print axioms MazurTransfer.ValuationSubringInertiaRingData.decompRingHom_comp_toValuationSubring


