-- Prove2me | Definitions.Def_APFPaper5_K1_shared_only_witness_Vocabulary
-- name    : APFPaper5_K1_shared_only_witness_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:31:53.649169+00:00
-- url     : https://prove2.me/theorems/82171625-0519-472a-9b90-a54b5f992f48
-- title:
--   Model vocabulary — A shared-record witness for a faithful table
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   The supplied weighted model gives family costs 0,2,2,3 and common-record coefficient 1. The visible theorem concludes bilinearity and a faithful diagonal; its use of the earlier bridge does not establish a physical interface or all eight forms.
--
--   **Supplied data and hypotheses**
--
--   - Every parameter and hypothesis in the exact source declaration remains exposed; no author input is adopted.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Theorems.Thm_APFPaper5_K1_shared_only_witness; Pullbacks v39, SHA-256 53633ba4964f8366d3f1d21114620815acb9905e819c0a8653beb4e660d50445. Theorems.Thm_APFPaper5_K1_shared_only_witness; pullbacks v39; SHA-256 53633ba4964f8366d3f1d21114620815acb9905e819c0a8653beb4e660d50445

import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
import Theorems.Thm_APFB05_support_novel_chain_capacity_bound
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Definitions.Def_APFPaper5_K1_SharedCost
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring
import Definitions.Def_APFPaper5_K1_interface_cost_book_Vocabulary
import Theorems.Thm_APFPaper5_K1_counted_family_satisfies_K1_of_nonneg_shared
import Definitions.Def_APFPaper5_K1_interface_bridge_witness_Vocabulary
import Theorems.Thm_APFPaper5_K1_BridgeWitness_exactly_served
import Theorems.Thm_APFPaper5_K1_weighted_marginal_ge
import Theorems.Thm_APFB05_weighted_record_model_satisfies_floor
import Theorems.Thm_APFPaper5_K1_needs_own_record_of_separates
import Theorems.Thm_APFPaper5_K1_recordModel_supportNovel_of_needs_own_record
import Theorems.Thm_APFPaper5_K1_recordModel_economy_of_separation
/-
APF Foundation Ledger — theorem node. DRAFT for author and cold review. Not gated, not released, not uploaded.
name: APFB05.overfull_chain_not_admissible
title: A family built by more genuinely new tested distinctions than the capacity can pay for is not admissible, and a context with less than one floor of spare capacity cannot take one more
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1781 (ledger admissibility), 1820-1824 (marginal floor and support novelty),
  2625 (support novelty, formal). The consumed nodes cite the same passages by their v9.27 line numbers
  (1763-1782, 1807-1818, 2615-2617). For the reading as a statement about classical record models: v9.28:3724,
  3737 (the defender's admissible record space and charging clause), 6952.
consumes: B05 (encoding MarginalFloor, r2, with its tested guard). B04 enters only as the capacity C in
  familyAdmissible. Uses the uploaded node APFB05.support_novel_chain_capacity_bound.
statement:
  (1) familyAdmissible is inherited by subfamilies.
  (2) If S n is built from S 0 by n tested support-novel insertions and C < n * epsilon, then S n is not admissible.
  (3) Then no admissible family contains S n.
  (4) If S is admissible, d is tested and support-novel over S, and C - familyCost S < epsilon, then insert d S is
      not admissible.
no new definition: every statement is in the existing FamilyCost and B05 vocabulary.
what it does not say: nothing about defenders, Sep, IJC or nonclassicality. Reading (3) or (4) as "no classical
  record model exists" needs a definition tying a defender's record family to familyAdmissible. That definition is
  not on the ledger and is not supplied here.
-/






set_option autoImplicit false
open Classical
open APFPaper1.Source

namespace APFB05

/-- (1) Admissibility passes to subfamilies: the same protocol serves the subfamily, and the infimal bill of a
subfamily is at most that of the family. Ordinary mathematics on source data. -/
theorem familyAdmissible_of_subset {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) {C : ℝ} {S T : Finset D} (hST : S ⊆ T)
    (hT : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C T) :
    familyAdmissible wholeResource calibration maintained sufficient usesToRealize C S := by
  obtain ⟨⟨p, hp⟩, hcost⟩ := hT
  refine ⟨⟨p, fun d hd => hp d (hST hd)⟩, le_trans ?_ hcost⟩
  unfold familyCost
  apply csInf_le_csInf
  · refine ⟨0, fun c hc => ?_⟩
    obtain ⟨q, _, rfl⟩ := hc
    exact NNReal.coe_nonneg _
  · exact ⟨_, p, hp, rfl⟩
  · rintro c ⟨q, hq, rfl⟩
    exact ⟨q, fun d hd => hq d (hST hd), rfl⟩







end APFB05

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_cost_book
title: Every cost on the families of a finite set of distinctions is the cost of a book of records, one record for each set of distinctions and needed by exactly those; the shared cost of two distinctions is the cost of the records both need; and where no record has negative cost and each distinction's own record has positive cost, the table meets K1's typed conditions
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST. 20:26: "The record ledger can be derived - each item in it". 20:31:
 "Yes" (to typing the derivation: the book of a cost function, the identity, and K1 from B05 plus
 nonnegative shared costs). NOTE_record_ledger_can_be_derived_2026-11-14. Builder seat:
 Def_APFPaper5_K1_MarkTable (atomTable), Def_APFPaper5_K1_SharedCost, record_book_table_satisfies_K1.
 The mathematics is inversion over subsets (Moebius inversion on a finite Boolean lattice), stated here
 through its defining recursion.
standing: THEOREMS ABOUT ANY REAL-VALUED FUNCTION OF FINITE FAMILIES. No input is consumed and no reading is
 used. Nothing is assumed of the cost except, in the last theorem, the three stated sign conditions.
what this file says:
 1. bookCost, book: the cost of the record needed by exactly the members of T, defined by the recursion
    "what T adds over the rest, less the costs of the records of the proper subsets of T".
 2. cost_eq_sum_book: the cost of a family is the cost of the empty family plus the costs of the records
    that some member of the family needs. An identity, for every cost function.
 3. book_empty, book_singleton: the record of no distinction costs nothing; the record a distinction needs
    alone costs what that distinction adds over all the others.
 4. sharedCost_eq_atomTable_book: the shared cost of two distinctions is the total cost of the records
    both need, the cost of the empty family being carried on the record that all need.
 5. cost_table_satisfies_K1: if the empty family costs at least nothing, no record has negative cost, and
    each distinction's own record has positive cost, the table of shared costs is bilinear with a
    nonnegative and faithful diagonal under the identity role exchange.
what this file does NOT say:
 - That the record costs are nonnegative. They can be negative; that is a property of the cost function.
 - That the book is the only one (it is, by the same inversion; not typed), or the closed alternating-sum
   formula for a record's cost (not typed), or that nonnegative record costs is the same as the cost being
   completely alternating (classical; not typed).
 - Anything about a single protocol's bill.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/










set_option autoImplicit false

namespace APFPaper5.K1

variable {ι : Type} [DecidableEq ι]



theorem bookCost_eq (g : Finset ι → ℝ) (A : Finset ι) :
    bookCost g A = g A - ∑ T ∈ A.ssubsets, bookCost g T := by
  have h : bookCost g A = g A - ∑ T ∈ A.ssubsets.attach, bookCost g T.1 :=
    Finset.strongInduction_eq (p := fun _ => ℝ) _ A
  rw [h, Finset.sum_attach A.ssubsets (fun T => bookCost g T)]



variable [Fintype ι]

















end APFPaper5.K1

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_shared_only_witness
title: A counted family with no record of negative cost exists: two distinctions with one record both need and one record each, every record costing 1; every premise of the pass-29 K1 statement holds there, and so its conclusion does
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 21:44 HST: "Derive all items stil owed for k1". Item owed since pass 29: a
 typed world in which the last premise of counted_family_satisfies_K1_of_nonneg_shared holds.
 Thm_APFPaper5_K1_cost_book, Thm_APFPaper5_K1_interface_cost_book, Thm_APFPaper5_K1_interface_bridge_witness
 (this seat). Builder seat: familyCost_weighted, APFB05.weighted_record_model_satisfies_floor,
 recordModel_supportNovel_of_needs_own_record.
standing: A WORLD. It shows the pass-29 K1 statement is not empty. It is not a claim about any physical
 interface.
what this file says:
 1. book_univ_two. For two distinctions, the record both need costs what the two cost apart, less what
    they cost together, less what the empty family costs.
 2. pairCost values: the empty family costs 0, each distinction 2, the two together 3.
 3. shared_only_family_meets_K1. In this world B05 holds as declared, the family of the two distinctions
    is counted, no record needed by both has negative cost (it costs 1), and the table of shared costs is
    bilinear with a nonnegative and faithful diagonal.
what this file does NOT say: that the declared inputs force this world. No lane. No claim that the transfer
 is forced, that the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/










set_option autoImplicit false

open APFPaper1.Source

namespace APFPaper5.K1



namespace SharedOnlyWitness

open BridgeWitness

/-- The cost of the sub-families of the two distinctions, in the book with one record both need and one
record each. -/
noncomputable abbrev pairCost : Finset (Fin 2) → ℝ :=
  indexedCost (D := Fin 2) (P := Finset (Option (Fin 2))) (R := Finset (Option (Fin 2)))
    (Record := Option (Fin 2)) (fun p => p) (fun r => ∑ a ∈ r, w a)
    (fun p => (↑p : Set (Option (Fin 2))))
    (fun _ sigma d => (↑(fam d) : Set (Option (Fin 2))) ⊆ sigma) (fun _ _ _ => True)
    (fun i : Fin 2 => i)















end SharedOnlyWitness

end APFPaper5.K1


