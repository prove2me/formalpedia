-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinitePointSets
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FinitePointSets
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:32:01.386798+00:00
-- url     : https://prove2.me/theorems/4b1a22dc-42f6-4cbb-b93b-8fe1ce7021e6
-- title:
--   Finite Point Sets
-- statement:
--   Definitions and structural lemmas for Finite Point Sets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinitePointSets.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.FinitePointSets
open Formalism.FourierDecayAlt.TB Finset Filter Topology
open scoped ComplexInnerProductSpace ComplexConjugate
theorem finite_pts {E : Type} [Field E] (S : Finset E) (i : ℕ) :
    {p : Pt E | level p = i ∧
      ∀ k (hk : k < p.length), 1 ≤ (p[k]'hk).1 ∧ (p[k]'hk).2 ∈ S}.Finite := by
  classical
  set F : Finset (ℕ × E) := (range (i + 1)) ×ˢ S with hFdef
  refine ((List.finite_length_le F i).image (List.map Subtype.val)).subset ?_
  rintro p ⟨hl, hp⟩
  have hmem : ∀ x ∈ p, 1 ≤ x.1 ∧ x.2 ∈ S := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    exact hp k hk
  unfold level at hl
  have hF : ∀ x ∈ p, x ∈ F := by
    intro x hx
    simp only [hFdef, mem_product, mem_range]
    refine ⟨?_, (hmem x hx).2⟩
    have : x.1 ≤ (p.map Prod.fst).sum := List.le_sum_of_mem (List.mem_map_of_mem hx)
    omega
  refine ⟨p.pmap Subtype.mk hF, ?_, ?_⟩
  · have h1 : (p.map Prod.fst).length ≤ (p.map Prod.fst).sum := by
      refine List.length_le_sum_of_one_le _ fun n hn => ?_
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hn
      exact (hmem x hx).1
    change (p.pmap Subtype.mk hF).length ≤ i
    simpa [hl] using h1
  · simp [List.map_pmap]
noncomputable def tw {E : Type} [Field E] (S : Finset E) (h0 : (0 : E) ∉ S) : Tower E where
  Sg := fun _ _ => S
  X := fun i => (finite_pts S i).toFinset
  isTower := by
    intro i p
    simp
  zero_not_mem := fun _ _ => h0
end Formalism.FourierDecayAlt.P.FinitePointSets
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.TB Finset Filter Topology
open scoped ComplexInnerProductSpace ComplexConjugate
end Formalism.FourierDecayAlt.P


