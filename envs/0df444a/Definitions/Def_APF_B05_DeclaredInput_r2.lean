-- Prove2me | Definitions.Def_APF_B05_DeclaredInput_r2
-- name    : APF_B05_DeclaredInput_r2
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-12T03:15:17.142322+00:00
-- url     : https://prove2.me/theorems/babb6d03-dcf2-43fe-af1b-3bb9d9527995
-- title:
--   Declared input — B05 — Uniform support-novel family marginal floor
-- statement:
--   **Declared input B05.** Genuinely new, support-novel distinctions have a uniform positive marginal cost floor in the stated regime.
--
--   Let $\kappa_\Gamma$ be shared family cost, $C_\Gamma$ capacity and $\varepsilon_\Gamma$ the proposed floor. For every context the predicate requires $\varepsilon_\Gamma>0$. When $d$ is tested, both $S$ and $S\cup\{d\}$ are feasible and cost at most capacity, and $d$ is support-novel over $S$, it requires
--
--   $$\kappa_\Gamma(S\cup\{d\})-\kappa_\Gamma(S)\ge\varepsilon_\Gamma.$$
--
--   The canonical ledger takes every member of its original distinction-task domain as tested. The explicit guard also permits narrower interface instances; such an instance does not establish the whole-domain commitment. An everywhere-false guard can make the guarded condition vacuous. This is a positive lower-bound predicate, not a proof that the proposed floor equals an infimum or a numerical value derived from B03.
--
--   **Encoding.** This re-registration uses the shared FamilyCost vocabulary and the author's November 11 testedness ruling. FOUNDATION_INPUTS revision 2026-10-04.1 is unchanged. It is a declared input, not a proved physical law.
--
--   **Formalization note.** Foundation Inputs revision 2026-10-04.1; independent source review brook-2026-11-12-cold_fidelity_review. Stated hypotheses and representation limits are retained.
-- source:
--   Paper 1 Technical Supplement v9.28 and FOUNDATION_INPUTS.json revision 2026-10-04.1; exact reviewed module Definitions.Def_APF_B05_DeclaredInput_r2; source SHA256 9b4e12a5864d81199cb3b812a9a1fa7a9e4a12b901c1cff9c76e26a827068b6a. See the source header for original v9.27 line references and the November 11 testedness ruling.

/-
APF Foundation Ledger — input node (Batch 1 re-registration of B05; replaces bcfda535-9775-4a4f-b9fc-5a05630ff0a8,
  which is deprecated, not deleted)
name: APF_B05_DeclaredInput_r2   (platform name confirmed by author ruling 2026-11-11; title unchanged)
title: Declared input — B05 — Uniform support-novel family marginal floor
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS.json revision 2026-10-04.1 (sha256 bb3b59f6…); declared input B05. Supplement
  v9.27:1778-1782,1807-1818,2188-2221,2615-2617,2650-2652. Two changes from the deprecated node. (1) Encoding only: the local familyCost /
  familyFeasible / familyAdmissible / supportNovel are replaced by the shared APFPaper1.Source declarations;
  (2) A change of content, a weakening: MarginalFloor
  carries an explicit `tested` guard on the added distinction (author ruling 2026-11-11; Supplement 1811, 2738).
  That ruling is recorded in RULINGS_2026-11-11.md; it is NOT in the hashed FOUNDATION_INPUTS file at revision
  2026-10-04.1, whose B05 wording is unchanged.
statement: Genuinely new, support-novel distinctions have a uniform positive marginal cost floor epsilon > 0 at
  every context: whenever d is tested, S and insert d S are both admissible and d is support-novel over S, the
  family cost rises by at least epsilon. Adopted wording of record (FOUNDATION_INPUTS B05): "Genuinely new,
  support-novel distinctions have a uniform positive marginal cost floor, epsilon_Gamma_star > 0, in the stated regime."
-/
import Definitions.Def_APFPaper1_FamilyCost

/-! B05, revision 2026-10-04.1: the author's ADMISSIBLE-FAMILY-GUARDED
MarginalFloor. Both S and insert d S must be original ledger-admissible.
D/P/R/Record and the data functions are bare types and functions here; that they
are the original source objects is a claim about the instantiation, not the Lean.
No individual-MD substitute, attainment, record-rank law or universal unguarded
floor is asserted.
TESTED GUARD (author rulings 12 and 14, 2026-11-11):
A context g includes its fixed resolution, perturbations and duration. D g is
the tested distinction-task domain, and the canonical ledger instantiation is
tested := True (Supplement v9.28 def:tested-distinction and rem:tested-two-senses).
The predicate parameter also permits a narrower finite-interrogation instance.
Such an instance does not establish the whole-domain ledger commitment.
Every consumer must identify its tested predicate. A claim about a priced
increment requires a tested, support-novel pair with both families admissible.
The generic predicate permits vacuity if the guard is everywhere false.
Taking tested := True recovers the previous predicate over the same source data.
The source marginal-floor quantifier guards the added distinction d; it does
not separately restrict S to the extra finite-interface tested predicate.
Historical source discussion used v9.27, whose cost section did not yet define
testedness. The v9.28 definition and the author's ruling now fix its ledger meaning.
This file and the deprecated Def_APF_B05_DeclaredInput both declare
APFB05.MarginalFloor and cannot be imported into one environment.
Source: Supplement v9.27:1778-1782,1807-1818,2188-2221,2615-2617,2650-2652.
-/
set_option autoImplicit false
namespace APFB05

open APFPaper1.Source

def MarginalFloor
    {Context : Type*} {D P R Record : Context → Type*}
    [∀ g, DecidableEq (D g)]
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (tested : (g : Context) → D g → Prop)
    (C epsilon : Context → ℝ) : Prop :=
  ∀ g, 0 < epsilon g ∧ ∀ (S : Finset (D g)) (d : D g),
    tested g d →
    familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S →
    familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert d S) →
    supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S d →
    epsilon g ≤
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (insert d S) -
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) S

end APFB05


