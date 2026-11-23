-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:33.233439+00:00
-- url     : https://prove2.me/theorems/9ce6e0af-ece8-4dc1-9ac0-dea7e3cc9d08
-- title:
--   Finite Presentation Of Injective
-- statement:
--   Definitions and structural lemmas for Finite Presentation Of Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinitePresentationOfInjective.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
namespace GlobalTheory.GroupAlg
variable (R : Type*) [CommRing R] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X)
abbrev mapAlgebra : Algebra R[Y] R[X] := (mapDomainRingHom R u).toAlgebra
theorem mapAlgebra_tower : letI := mapAlgebra R u; IsScalarTower R R[Y] R[X] :=
  letI := mapAlgebra R u
  IsScalarTower.of_algebraMap_eq fun a => ((mapDomainAlgHom R R u).commutes a).symm
def cosetComb : letI := mapAlgebra R u; ((X ⧸ u.range) →₀ R[Y]) →ₗ[R[Y]] R[X] :=
  letI := mapAlgebra R u
  Finsupp.linearCombination R[Y] (fun c : X ⧸ u.range => (single c.out 1 : R[X]))
theorem cosetComb_single (c : X ⧸ u.range) (y : Y) (r : R) :
    cosetComb R u (Finsupp.single c (single y r)) = single (u y + c.out) r := by
  letI := mapAlgebra R u
  rw [cosetComb, Finsupp.linearCombination_single, Algebra.smul_def]
  change mapDomain u (single y r) * _ = _
  rw [mapDomain_single, single_mul_single, mul_one]
theorem exists_add_out (x : X) :
    ∃ y, u y + (QuotientAddGroup.mk x : X ⧸ u.range).out = x := by
  obtain ⟨⟨_, y, rfl⟩, h⟩ := QuotientAddGroup.mk_out_eq_mul u.range x
  exact ⟨-y, by rw [h]; simp⟩
theorem cosetComb_surjective : Function.Surjective (cosetComb R u) := by
  intro p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add s t hs ht =>
    obtain ⟨a, rfl⟩ := hs
    obtain ⟨b, rfl⟩ := ht
    exact ⟨a + b, map_add _ _ _⟩
  | single x r =>
    obtain ⟨y, hy⟩ := exists_add_out u x
    exact ⟨_, (cosetComb_single R u _ y r).trans (by rw [hy])⟩
theorem coset_bijective (hu : Function.Injective u) :
    Function.Bijective (fun p : (Σ _ : X ⧸ u.range, Y) => u p.2 + p.1.out) := by
  refine ⟨?_, fun x => ?_⟩
  · rintro ⟨c, y⟩ ⟨d, z⟩ h
    dsimp only at h
    have h1 : ∀ (c : X ⧸ u.range) y, (QuotientAddGroup.mk (u y + c.out) : X ⧸ u.range) = c := by
      intro c y
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff (N := u.range) (u y)).2 ⟨y, rfl⟩, zero_add,
        QuotientAddGroup.out_eq']
    obtain rfl : c = d := by rw [← h1 c y, h, h1]
    obtain rfl : y = z := hu (add_right_cancel h)
    rfl
  · obtain ⟨y, hy⟩ := exists_add_out u x
    exact ⟨⟨_, y⟩, hy⟩
theorem cosetComb_injective (hu : Function.Injective u) : Function.Injective (cosetComb R u) := by
  letI := mapAlgebra R u
  haveI := mapAlgebra_tower R u
  let b : Module.Basis (Σ _ : X ⧸ u.range, Y) R ((X ⧸ u.range) →₀ R[Y]) :=
    Finsupp.basis fun _ => AddMonoidAlgebra.basis Y R
  let e := b.equiv (AddMonoidAlgebra.basis X R) (Equiv.ofBijective _ (coset_bijective u hu))
  have : (cosetComb R u).restrictScalars R = e.toLinearMap := by
    refine b.ext fun p => ?_
    obtain ⟨c, y⟩ := p
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
    simp [b, cosetComb_single]
  have h2 : ⇑(cosetComb R u) = e := congrArg DFunLike.coe this
  rw [h2]
  exact e.injective
def cosetBasis (hu : Function.Injective u) :
    letI := mapAlgebra R u; Module.Basis (X ⧸ u.range) R[Y] R[X] :=
  letI := mapAlgebra R u
  .ofRepr (LinearEquiv.ofBijective (cosetComb R u)
    ⟨cosetComb_injective R u hu, cosetComb_surjective R u⟩).symm
end GlobalTheory.GroupAlg


