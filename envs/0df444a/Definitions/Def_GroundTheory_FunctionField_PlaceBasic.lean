-- Prove2me | Definitions.Def_GroundTheory_FunctionField_PlaceBasic
-- name    : GroundTheory_FunctionField_PlaceBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:08.914805+00:00
-- url     : https://prove2.me/theorems/b71766a1-9ef5-4739-a57a-a5251477b723
-- title:
--   Place Basic
-- statement:
--   Definitions and structural lemmas for Place Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBasic.lean

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply


set_option autoImplicit false
namespace GroundTheory.FunctionField
open Polynomial
namespace Place
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
theorem mem_ring_of_isIntegral (v : Place k K) {x : K} (hx : IsIntegral k x) : x ∈ v.ring := by
  have hx' : IsIntegral v.ring x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx'
  rw [← hy]
  exact y.2
theorem mem_ring_of_isAlgebraic (v : Place k K) {x : K} (hx : IsAlgebraic k x) : x ∈ v.ring :=
  v.mem_ring_of_isIntegral hx.isIntegral
theorem exists_valuation_lt_one_of_transcendental {x : K} (hx : Transcendental k x) :
    ∃ v : Place k K, v.ring.valuation x < 1 := by
  let A : Subring K := (Algebra.adjoin k {x}).toSubring
  have hxA : x ∈ A := Algebra.self_mem_adjoin_singleton k x
  let I : Ideal A := Ideal.span {⟨x, hxA⟩}
  have hI : I ≠ ⊤ := by
    intro htop
    rw [Ideal.span_singleton_eq_top] at htop
    obtain ⟨y, hy⟩ := htop.exists_right_inv
    have hyA : (y : K) ∈ Algebra.adjoin k {x} := y.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hyA
    obtain ⟨p, hp⟩ := hyA
    have hxy : x * (y : K) = 1 := congrArg Subtype.val hy
    apply hx
    refine ⟨X * p - 1, ?_, ?_⟩
    · intro h
      have h0 := congrArg (fun q : k[X] => q.coeff 0) h
      simp at h0
    · have hp' : aeval x p = (y : K) := hp
      rw [map_sub, map_mul, aeval_X, map_one, hp', hxy, sub_self]
  obtain ⟨B, hAB, hIB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hxB : x ∈ B.nonunits := hIB ⟨⟨x, hxA⟩, Ideal.subset_span rfl, rfl⟩
  refine ⟨⟨B, ?_, ?_⟩, B.mem_nonunits_iff.1 hxB⟩
  · intro htop
    rcases B.mem_nonunits_iff_or.1 hxB with h | h
    · exact hx (h ▸ isAlgebraic_zero)
    · exact h (htop ▸ ValuationSubring.mem_top x⁻¹)
  · intro c
    exact hAB (Subalgebra.algebraMap_mem (Algebra.adjoin k {x}) c)
theorem nonempty [IsFunctionField k K] : Nonempty (Place k K) := by
  obtain ⟨x, hx, -⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  obtain ⟨v, -⟩ := exists_valuation_lt_one_of_transcendental hx
  exact ⟨v⟩
noncomputable def algebraicClosureToResidueField (v : Place k K) :
    algebraicClosure k K →ₐ[k] v.ResidueField where
  toRingHom := (IsLocalRing.residue v.ring).comp
    (RingHom.codRestrict ((algebraicClosure k K).val : algebraicClosure k K →+* K) v.ring
      fun y => show (y : K) ∈ v.ring from v.mem_ring_of_isAlgebraic (mem_algebraicClosure_iff.1 y.2))
  commutes' _ := rfl
theorem algebraicClosureToResidueField_injective (v : Place k K) :
    Function.Injective v.algebraicClosureToResidueField :=
  v.algebraicClosureToResidueField.toRingHom.injective
instance [IsFunctionField k K] : FiniteDimensional k (algebraicClosure k K) := by
  obtain ⟨v⟩ := Place.nonempty (k := k) (K := K)
  exact FiniteDimensional.of_injective v.algebraicClosureToResidueField.toLinearMap
    v.algebraicClosureToResidueField_injective
end Place
end GroundTheory.FunctionField


