-- Prove2me | Definitions.Def_APF_B03_DeclaredInput_r2
-- name    : APF_B03_DeclaredInput_r2
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-12T03:11:54.486192+00:00
-- url     : https://prove2.me/theorems/fc16b70f-d6d2-4183-953e-63dfe4e1c451
-- title:
--   Declared input — B03 — Positive admissibility cost
-- statement:
--   **Declared input B03.** Physical distinctions carry positive admissibility cost.
--
--   Fix a context $\Gamma$ with its resolution, perturbations and duration. Its distinction domain consists of the tasks tested under that contract. On the shared protocol, support and calibrated whole-resource data, B03 asserts
--
--   $$\kappa_\Gamma(\{d\})>0\qquad(d\in D_\Gamma).$$
--
--   This is positivity of the singleton task infimum, stronger than positive bills for each individual protocol. It asserts no uniform floor across tasks and no attaining protocol.
--
--   **Encoding.** This re-registration imports the shared FamilyCost definition. The real infimum of an empty serving class is zero; hence positive singleton cost forces feasibility. General physical cost claims retain their feasibility requirement. The definition records an adopted input predicate; it does not prove the predicate for arbitrary supplied data.
--
--   **Formalization note.** Foundation Inputs revision 2026-10-04.1; independent source review brook-2026-11-12-cold_fidelity_review. Stated hypotheses and representation limits are retained.
-- source:
--   Paper 1 Technical Supplement v9.28 and FOUNDATION_INPUTS.json revision 2026-10-04.1; exact reviewed module Definitions.Def_APF_B03_DeclaredInput_r2; source SHA256 40ecd5fc688b926f06a383354530fcde5d51036d83b95f9aca063b7085022f04. See the source header for original v9.27 line references and the November 11 testedness ruling.

/-
APF Foundation Ledger — input node (Batch 1 re-registration of B03; replaces 26802d1d-4792-415f-b557-828dab3bdb4b,
  which is deprecated, not deleted)
name: APF_B03_DeclaredInput_r2   (platform name confirmed by author ruling 2026-11-11; title unchanged)
title: Declared input — B03 — Positive admissibility cost
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS.json revision 2026-10-04.1 (sha256 bb3b59f6…); declared input B03. Supplement
  v9.27:1744-1757,1778-1782,2188-2221,2615-2617. Encoding edit only: the local familyCost is replaced by the
  shared APFPaper1.Source.familyCost; the predicate B03TaskCost is unchanged.
statement: Physical distinctions carry positive admissibility cost: at every context, the family cost of each
  singleton task {d} is strictly positive.
-/
import Definitions.Def_APFPaper1_FamilyCost

/-! B03 is positive SINGLETON TASK INFIMUM, not positive individual bills.
A context g stands for a physical context together with its fixed resolution,
perturbations and duration. D g is its tested distinction domain: the physical
distinctions taken as tasks under that contract (author ruling 2026-11-11;
Supplement v9.28 def:tested-distinction). P g is the admitted finite enforcement
universe at the same contract. The same whole p, original
r(p), original chi, maintained records and actual-use obligations are retained.
Source: Supplement v9.27:1744-1757,1778-1782,2188-2221,2615-2617.
This is a defined input predicate, never a proof of B03 or source instantiation.
-/
set_option autoImplicit false
namespace APFB03

open APFPaper1.Source

def B03TaskCost
    {Context : Type*} {D P R Record : Context → Type*}
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop) : Prop :=
  ∀ g (d : D g),
    0 < familyCost (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) {d}

end APFB03


