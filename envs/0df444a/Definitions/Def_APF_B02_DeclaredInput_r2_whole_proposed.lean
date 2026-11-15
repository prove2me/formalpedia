-- Prove2me | Definitions.Def_APF_B02_DeclaredInput_r2_whole_proposed
-- name    : APF_B02_DeclaredInput_r2_whole_proposed
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T18:21:42.443488+00:00
-- url     : https://prove2.me/theorems/f9a6d749-0b2d-4546-ab2f-a077784e6839
-- title:
--   Declared input — B02 — Enforceable distinctions and finite side combinations
-- statement:
--   **Author-declared input B02 · revision 2026-11-14.1**
--
--   > A distinction is a finite, enforceable separator of continuation profiles. Every combination of sides of every finite family of distinctions is held by some potential state.
--
--   This single definition carries both sentences. The first preserves descent, nonconstancy and finite enforcement; the second requires realization of every finite side assignment in every context.
--
--   **What the new sentence says**
--
--   - The family consists of distinctions in the original physical domain.
--   - A side is assigned once to each distinction; repeated list entries add no separate choice.
--   - The witness is a potential state. The clause does not assert that it is occupied, admitted or reached by an executable procedure.
--   - The empty family requires a potential state in each context. No infinite-family assertion is made.
--
--   The source-vocabulary parameters below retain the original B02 fidelity limits. The older B02 record remains available for historical reference; it is not the current complete input.
--
--   **Meaning and scope**
--
--   The parameters must represent the original contexts, raw states, finite processes, admissible enforcement protocols, distinction domain and maintained-record relations. The resolution, perturbation, lifetime and confidence contract is fixed. An arbitrary model or tested subfamily does not acquire this physical interpretation merely by satisfying the predicate.
-- source:
--   Definitions/Def_APF_B02_DeclaredInput_r2_whole_proposed.lean; Sib v52 / pullbacks v6; SHA-256 b064c38fa785b400e38a226b09b5d5479f610e55891359f5581d9ddd8ff3b2c9. Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex; lines 1224-1243,1276-1332,1741-1771,1833-1885,2601-2680; APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json; revision 2026-11-14.1; input B02; source/Definitions/Def_APF_B02_DeclaredInput_r2_whole_proposed.lean

/-
APF Foundation Ledger — definition node DRAFT, PROPOSED FORM ONLY (session EthanBrooke-01WrrBvu, 2026-11-14;
 not gated, not reviewed, not released, not a live node)
name: APF_B02_DeclaredInput_r2_whole_proposed
title: Proposed declared form of B02 at inputs revision 2026-11-14.1, written whole in one module that imports only Init
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: APF Reconstruction Spine/FOUNDATION_INPUTS.json; revision 2026-11-14.1; SHA-256
 c0fbd55c797afd5a342a5362ceb2cb79efb13186edd487205ef04c5eaa26ffbd; declared input B02, current_wording: "A
 distinction is a finite, enforceable separator of continuation profiles. Every combination of sides of every
 finite family of distinctions is held by some potential state."
standing: a PROPOSAL for the publishing seat, the auditor and the author. It is the alternative to
 Def_APF_B02_DeclaredInput_r2_init_proposed for a re-registration on the pattern of B03 and B05 (one module that
 states the whole input, the old node deprecated and not deleted). It does not import the live B02 module
 (APFB02.B02SourceMeaning, node 2d6854de-b2dd-4db3-8be5-57bbbb64efb6), so the two can sit in one environment.
 The two proposals are proved equivalent in Thm_APFB02_r2_carries_first_sentence (APFB02.r2_whole_iff_r2_init).
statement: B02SourceMeaning_r2_whole has two conjuncts. The first is the body of the live declared form of B02,
 copied without change. The second: in every context, for every finite list of the distinctions of the domain
 and every assignment of a side to each distinction, some raw state holds each listed distinction on its
 assigned side.
fidelity exposure: the second conjunct is said of the domain as the distinctions themselves, each once. A
 reading made from distinctions, placed in the domain beside them, would make it false. The parameters carry
 the same mandatory source vocabulary as in the live B02 module; nothing about them is restated or changed.
-/
import Init

set_option autoImplicit false
universe uG uX uQ uP uR
namespace APFB02

/-- B02 at inputs revision 2026-11-14.1, both sentences, in one definition. -/
def B02SourceMeaning_r2_whole
    {Context : Type uG} {X : Context → Type uX} {Q : Context → Type uQ}
    {P : Context → Type uP} {Record : Context → Type uR}
    (Cont : (g : Context) → X g → Q g → Prop)
    (Delta : (g : Context) → (X g → Bool) → Prop)
    (maintained : (g : Context) → P g → Record g → Prop)
    (sufficient : (g : Context) → P g → (Record g → Prop) →
      {d : X g → Bool // Delta g d} → Prop)
    (usesToRealize : (g : Context) → P g →
      {d : X g → Bool // Delta g d} → (Record g → Prop) → Prop) : Prop :=
  (∀ g (d : {f : X g → Bool // Delta g f}),
    (∀ x y, Cont g x = Cont g y → d.val x = d.val y) ∧
    (∃ x y, d.val x ≠ d.val y) ∧
    ∃ (p : P g) (sigma : Record g → Prop),
      (∀ r, sigma r → maintained g p r) ∧
      sufficient g p sigma d ∧ usesToRealize g p d sigma) ∧
  ∀ (g : Context) (l : List {f : X g → Bool // Delta g f})
    (v : {f : X g → Bool // Delta g f} → Bool),
    ∃ x : X g, ∀ e ∈ l, e.val x = v e

end APFB02


