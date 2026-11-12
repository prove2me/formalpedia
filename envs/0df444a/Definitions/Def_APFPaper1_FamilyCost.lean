-- Prove2me | Definitions.Def_APFPaper1_FamilyCost
-- name    : APFPaper1_FamilyCost
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-12T02:48:11.375601+00:00
-- url     : https://prove2.me/theorems/89622bc4-a908-4ffb-b537-431eaf28dafd
-- title:
--   Family cost, feasibility, admissibility and support novelty on source data
-- statement:
--   Fix a distinction domain $D$, a protocol class $P$, a record type, a whole-resource map $r:P\to R$ and a nonnegative calibration $\chi:R\to\mathbb R_{\ge0}$. Each protocol has maintained records, a sufficient-support predicate and a relation saying which records it uses to realize each distinction. Let $J(S)$ be the protocols serving every member of a finite family $S$ from their own maintained sufficient support. Define
--
--   $$
--   \kappa(S)=\inf\{\chi(r(p)):p\in J(S)\}.
--   $$
--
--   A family is feasible when $J(S)$ is nonempty and admissible at capacity $C$ when it is feasible and $\kappa(S)\le C$. A distinction $d$ is support-novel over $S$ when some positive near-optimal window excludes sufficient maintained support for $d$ from every $S$-serving protocol whose bill is at most $\kappa(S)+\eta$.
--
--   These four definitions give B03, B05 and the source-to-ledger bridge one shared vocabulary. They introduce no laws on the supplied data. In the canonical ledger, the distinction domain consists of tasks under the context's fixed resolution, perturbations and duration; canonical testedness is always true on that domain.
--
--   **Representation limits.** The formal cost is a real infimum: an empty serving class has value zero, so a physical cost claim requires feasibility. This definition does not establish affordable attainment, zero cost for the empty family, or the physical adequacy of an arbitrary protocol/support/calibration instance.
--
--   **Formalization note.** Consumes Foundation Inputs revision 2026-10-04.1. This is source vocabulary, not a newly adopted physical premise. All reachable proof-valued structure fields belong to the pinned ordinary mathematical library; the local acceptance record enumerates their exact declarations. Independent source review: brook-2026-11-12-cold_fidelity_review. Native auditor readback remains separate.
-- source:
--   Paper 1, The Enforceability of Distinction, Technical Supplement v9.28: def:admissibility-cost; def:tested-distinction; rem:tested-two-senses; rem:ledger-valuation-convention; def:record-support-rank (lines 1753–1791, 2624–2626); FOUNDATION_INPUTS.json revision 2026-10-04.1; author rulings 2026-11-11. Exact reviewed source SHA256 a4e7671f39a3bc1e7621584c1dcc1fb54b31fdf731292d5a0f07066aac764d4e

/-
APF Foundation Ledger — definition node (Batch 1, shared vocabulary)
name: APFPaper1_FamilyCost
title: Family cost, feasibility, admissibility and support novelty on source data
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.27:1744-1757,1763-1782,1851-1862,2188-2221,2615-2617. One shared encoding of the
  source symbols familyCost / familyFeasible / familyAdmissible / supportNovel. B03 retains its predicate body.
  B05 adds the author-approved tested guard; tested := True recovers the canonical ledger scope.
  Both re-registered inputs import this module (author rulings 2026-11-11).
statement: On source protocol, record and whole-account data, familyCost S is the real infimum of the calibrated
  whole-resource bills of the protocols serving S; familyFeasible S says some protocol serves S; familyAdmissible C S
  adds familyCost S ≤ C; supportNovel S d says some positive window eta excludes carried sufficient support for d from
  every S-serving protocol priced within familyCost S + eta.
-/
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Finset.Insert

set_option autoImplicit false
namespace APFPaper1.Source

/-- The infimal calibrated whole-resource bill over the protocols that serve S from their own
maintained sufficient support. Source data only: no law on the data is assumed. -/
noncomputable def familyCost
    {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D) : ℝ :=
  sInf {c : ℝ | ∃ p : P,
    (∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) ∧
    (calibration (wholeResource p) : ℝ) = c}

/-- Some protocol serves every member of S from its own maintained sufficient support. -/
def familyFeasible {D P Record : Type*}
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D) : Prop :=
  ∃ p : P, ∀ d ∈ S, ∃ sigma : Set Record,
    sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma

/-- Feasible and within the context capacity C: ledger admissibility of a family (Supplement 1763-1776;
the alignment-level form at 1851-1862 is stated there to be the same inequality). -/
def familyAdmissible {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (C : ℝ) (S : Finset D) : Prop :=
  familyFeasible maintained sufficient usesToRealize S ∧
  familyCost wholeResource calibration maintained sufficient usesToRealize S ≤ C

/-- Support novelty of d over S in a positive near-optimal window (Supplement 2615-2617). -/
def supportNovel {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D) (d : D) : Prop :=
  ∃ eta : ℝ, 0 < eta ∧ ∀ p : P,
    (∀ e ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma e ∧ usesToRealize p e sigma) →
    (calibration (wholeResource p) : ℝ) ≤
      familyCost wholeResource calibration maintained sufficient usesToRealize S + eta →
    ¬ ∃ sigma : Set Record, sigma ⊆ maintained p ∧ sufficient p sigma d

end APFPaper1.Source


