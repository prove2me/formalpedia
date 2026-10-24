-- Prove2me | Definitions.Def_PricingWithTips3DM_93af747ed169fcaa7438edb4
-- name    : PricingWithTips3DM_93af747ed169fcaa7438edb4
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:52:37.048909+00:00
-- url     : https://prove2.me/theorems/35513d6a-4360-480a-a482-84c9ac6264bd
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Semantics
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_fbcae5dce6c2372e1e0c3fd0
import Definitions.Def_PricingWithTips3DM_9e075f4cfef646bf5f91f622
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# General CLIQUE verifier: factored Boolean semantics

The parser, graph checks, vertex checks, and nested adjacency checks are joined
here without changing the already published function `cliqueVerifier`.
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier

/-- The typed verifier split into the passes implemented by the concrete
machine. -/
def typedCliqueChecks (I : CliqueInstance) (vertices : List Nat) : Bool :=
  instanceWellFormedBool I &&
    vertexChecks I vertices &&
    pairwiseAdjacencyBool I vertices

/-- The factored typed checks are exactly the conjunction used by the public
Boolean verifier. -/
theorem typedCliqueChecks_eq_true_iff
    (I : CliqueInstance) (vertices : List Nat) :
    typedCliqueChecks I vertices = true ↔
      I.WellFormed ∧ I.ListRepresentsClique vertices := by
  simp only [typedCliqueChecks, Bool.and_eq_true,
    instanceWellFormedBool_eq_true_iff, vertexChecks_eq_true_iff,
    pairwiseAdjacencyBool_eq_true_iff]
  constructor
  · rintro ⟨⟨hwellFormed, hvertices⟩, hpairs⟩
    rcases hvertices with ⟨hnodup, hlength, hrange⟩
    refine ⟨hwellFormed, hnodup, hlength, hrange, ?_⟩
    exact (pairwise_adj_iff_all_distinct I hnodup).mp hpairs
  · rintro ⟨hwellFormed, hnodup, hlength, hrange, hpairs⟩
    exact ⟨⟨hwellFormed, hnodup, hlength, hrange⟩,
      (pairwise_adj_iff_all_distinct I hnodup).mpr hpairs⟩

/-- Boolean equality with the original typed `decide`, useful for exact
machine-output rewriting. -/
theorem typedCliqueChecks_eq_decide
    (I : CliqueInstance) (vertices : List Nat) :
    typedCliqueChecks I vertices =
      decide (I.WellFormed ∧ I.ListRepresentsClique vertices) := by
  apply Bool.eq_iff_iff.mpr
  simpa using typedCliqueChecks_eq_true_iff I vertices

/-- Raw verifier expressed through the explicit phase decomposition. -/
def factoredCliqueVerifier (certificate input : List CliqueSym) : Bool :=
  match decodeCliqueInstance input, decodeCliqueCertificate certificate with
  | some I, some vertices => typedCliqueChecks I vertices
  | _, _ => false

/-- The phased Boolean specification is definitionally faithful to the
previously fixed public verifier on every raw input. -/
theorem factoredCliqueVerifier_eq_cliqueVerifier
    (certificate input : List CliqueSym) :
    factoredCliqueVerifier certificate input =
      cliqueVerifier certificate input := by
  generalize hinput : decodeCliqueInstance input = instanceResult
  generalize hcertificate : decodeCliqueCertificate certificate =
    certificateResult
  cases instanceResult <;> cases certificateResult <;>
    simp [factoredCliqueVerifier, cliqueVerifier, hinput, hcertificate,
      typedCliqueChecks_eq_decide]

/-- Exact all-input acceptance theorem for the phase decomposition. -/
theorem factoredCliqueVerifier_eq_true_iff
    (certificate input : List CliqueSym) :
    factoredCliqueVerifier certificate input = true ↔
      ∃ I vertices,
        decodeCliqueInstance input = some I ∧
        decodeCliqueCertificate certificate = some vertices ∧
        I.WellFormed ∧ I.ListRepresentsClique vertices := by
  rw [factoredCliqueVerifier_eq_cliqueVerifier]
  exact cliqueVerifier_eq_true_iff certificate input

end CLRS.Chapter34.Turing.GeneralCliqueVerifier


