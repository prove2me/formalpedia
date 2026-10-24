-- Prove2me | Definitions.Def_PricingWithTips3DM_faa508aacc996d8da1bc0c3d
-- name    : PricingWithTips3DM_faa508aacc996d8da1bc0c3d
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:55:31.493026+00:00
-- url     : https://prove2.me/theorems/227d56f0-8556-479f-938d-3413c9bbe37f
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.CertificateNodup
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_93af747ed169fcaa7438edb4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# General CLIQUE verifier: duplicate-check elimination

The adjacency relation is irreflexive.  Consequently, the later-pair
adjacency pass already rejects every repeated certificate vertex.  This lets
the concrete verifier reuse the adjacency controller instead of building a
second quadratic duplicate scanner for certificates.
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier

/-- Pairwise graph adjacency forces a certificate list to be duplicate-free. -/
theorem nodup_of_pairwise_adj (I : CliqueInstance) {vertices : List Nat}
    (hpairs : vertices.Pairwise I.Adj) : vertices.Nodup := by
  induction vertices with
  | nil => simp
  | cons vertex rest ih =>
      rw [List.pairwise_cons] at hpairs
      rw [List.nodup_cons]
      refine ⟨?_, ih hpairs.2⟩
      intro hmem
      exact I.not_adj_self vertex (hpairs.1 vertex hmem)

/-- The executable pairwise pass subsumes the separate certificate duplicate
pass. -/
theorem pairwiseAdjacencyBool_implies_nodup
    (I : CliqueInstance) {vertices : List Nat}
    (hpairs : pairwiseAdjacencyBool I vertices = true) :
    natListNodupBool vertices = true := by
  rw [natListNodupBool_eq_true_iff]
  exact nodup_of_pairwise_adj I
    ((pairwiseAdjacencyBool_eq_true_iff I vertices).mp hpairs)

/-- Certificate-side checks with duplicate detection delegated to the
pairwise adjacency pass. -/
def vertexAndPairChecksWithoutNodup
    (I : CliqueInstance) (vertices : List Nat) : Bool :=
  decide (vertices.length = I.targetSize) &&
    verticesWithinBool I.vertexCount vertices &&
    pairwiseAdjacencyBool I vertices

/-- Removing the explicit certificate-Nodup Boolean does not change the
combined verifier result. -/
theorem vertexChecks_pairwise_eq_withoutNodup
    (I : CliqueInstance) (vertices : List Nat) :
    (vertexChecks I vertices && pairwiseAdjacencyBool I vertices) =
      vertexAndPairChecksWithoutNodup I vertices := by
  cases hpairs : pairwiseAdjacencyBool I vertices with
  | false =>
      simp [vertexAndPairChecksWithoutNodup, hpairs]
  | true =>
      have hnodup : natListNodupBool vertices = true :=
        pairwiseAdjacencyBool_implies_nodup I hpairs
      simp [vertexChecks, vertexAndPairChecksWithoutNodup, hpairs, hnodup]

end CLRS.Chapter34.Turing.GeneralCliqueVerifier


