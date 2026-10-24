-- Prove2me | Definitions.Def_PricingWithTips3DM_9e075f4cfef646bf5f91f622
-- name    : PricingWithTips3DM_9e075f4cfef646bf5f91f622
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:47:37.051916+00:00
-- url     : https://prove2.me/theorems/34b2d0d3-4e90-4524-8f07-b20cf417458c
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Certificate.Semantics
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_b19e116796e7a4e8ef576ba4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Exact semantics of general CLIQUE certificates

The Boolean checker is characterized on every raw input.  The list predicate
is then connected in both directions to the finite-set clique semantics.
-/

namespace CLRS
namespace Chapter34

/-- Exact all-input truth theorem for the Boolean CLIQUE checker. -/
theorem cliqueVerifier_eq_true_iff (certificate input : List CliqueSym) :
    cliqueVerifier certificate input = true ↔
      ∃ I vertices,
        decodeCliqueInstance input = some I ∧
        decodeCliqueCertificate certificate = some vertices ∧
        I.WellFormed ∧ I.ListRepresentsClique vertices := by
  generalize hinput : decodeCliqueInstance input = instanceResult
  generalize hcertificate : decodeCliqueCertificate certificate = certificateResult
  cases instanceResult <;> cases certificateResult <;>
    simp [cliqueVerifier, hinput, hcertificate]

namespace CliqueInstance

/-- A duplicate-free list certificate induces the corresponding finite-set
clique witness. -/
theorem hasClique_of_listRepresentsClique {I : CliqueInstance}
    {vertices : List Nat} (h : I.ListRepresentsClique vertices) : I.HasClique := by
  rcases h with ⟨hnodup, hcard, hbound, hadj⟩
  refine ⟨vertices.toFinset, ?_, ?_, ?_⟩
  · simpa [List.toFinset_card_of_nodup hnodup] using hcard
  · intro v hv
    exact hbound v (List.mem_toFinset.mp hv)
  · intro u hu v hv huv
    exact hadj u (List.mem_toFinset.mp hu) v (List.mem_toFinset.mp hv) huv

/-- Every finite-set clique has a duplicate-free list certificate. -/
theorem exists_listRepresentsClique_of_hasClique {I : CliqueInstance}
    (h : I.HasClique) : ∃ vertices, I.ListRepresentsClique vertices := by
  rcases h with ⟨vertices, hcard, hbound, hadj⟩
  refine ⟨vertices.toList, vertices.nodup_toList, ?_, ?_, ?_⟩
  · simpa using hcard
  · intro v hv
    exact hbound v (Finset.mem_toList.mp hv)
  · intro u hu v hv huv
    exact hadj u (Finset.mem_toList.mp hu) v (Finset.mem_toList.mp hv) huv

/-- List certificates and the mathematical clique predicate are equivalent. -/
theorem hasClique_iff_exists_listRepresentsClique (I : CliqueInstance) :
    I.HasClique ↔ ∃ vertices, I.ListRepresentsClique vertices := by
  constructor
  · exact exists_listRepresentsClique_of_hasClique
  · rintro ⟨vertices, hvertices⟩
    exact hasClique_of_listRepresentsClique hvertices

end CliqueInstance

end Chapter34
end CLRS


