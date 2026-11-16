-- Prove2me | Definitions.Def_APF_B02_DeclaredInput_r3_whole_proposed
-- name    : APF_B02_DeclaredInput_r3_whole_proposed
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T19:48:09.498122+00:00
-- url     : https://prove2.me/theorems/597dc739-fb1d-40c9-94e3-72a02b8442b2
-- title:
--   Proposed B02 r3 in a whole statement
-- statement:
--   Writes the separator/enforcement clauses, finite distinct-reading side assignments, and an additional profile-separation clause together. PROPOSED, NOT ADOPTED. The final separation conjunct is additional structural content. The live r2 input remains unchanged; list encoding is not authority to install r3.
--
--   **Supplied data and hypotheses**
--
--   - PROPOSED, NOT ADOPTED. The final separation conjunct is additional structural content. The live r2 input remains unchanged; list encoding is not authority to install r3.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions.Def_APF_B02_DeclaredInput_r3_whole_proposed; Sib v66 / pullbacks v22, SHA-256 cb9eb6da20428157b88a22037548d63d2b0eb2e2b303969e87f3cb645d32f555. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Definitions\Def_APF_B02_DeclaredInput_r3_whole_proposed.lean

/-
APF Foundation Ledger — definition node DRAFT, PROPOSED FORM ONLY (session EthanBrooke-01WrrBvu, 2026-11-14;
 not gated, not reviewed, not released, not a live node)
name: APF_B02_DeclaredInput_r3_whole_proposed
title: Proposed declared form of B02 with its list of distinctions complete, written whole in one module that imports only Init
inputs_revision: 2026-11-14.1
proposed_for_inputs_revision: 2026-11-14.2 (PROPOSED_FOUNDATION_INPUTS_rev_2026-11-14.2.json; NOT INSTALLED; the
 author sets the label at install)
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: APF Reconstruction Spine/FOUNDATION_INPUTS.json; revision 2026-11-14.1; SHA-256
 c0fbd55c797afd5a342a5362ceb2cb79efb13186edd487205ef04c5eaa26ffbd; declared input B02, current_wording: "A
 distinction is a finite, enforceable separator of continuation profiles. Every combination of sides of every
 finite family of distinctions is held by some potential state." The wording is NOT changed by this proposal.
 The author, 2026-11-14 HST: 03:12 ("region's distinctions tell its states apart. It's true."), 17:35 ("Told
 apart is in the def of continuation profile"), 17:44 ("I think we should fix bo2"), 17:52 ("Proceed", to
 preparing this as a proposal). Paper 1 Supplement v9.28:1224-1257, 1745-1750.
standing: a PROPOSAL for the author, the publishing seat and the auditor. It is a candidate successor of the
 live B02 node f9a6d749-0b2d-4546-ab2f-a077784e6839 (APF_B02_DeclaredInput_r2_whole_proposed), on the same
 pattern: one module that states the whole input, the earlier node deprecated and not deleted. It does not
 import that module, so the two can sit in one environment. Nothing is installed, released or written to
 the platform by this file.
statement: B02SourceMeaning_r3_whole has three parts. The first two are the body of
 B02SourceMeaning_r2_whole, copied without change. The third: in every context, two raw states that every
 distinction of the domain reads alike have the same continuation profile.
fidelity exposure: the third part is a reading of the first sentence (which distinctions a context has: all
 of them, so that they account for every difference of continuation profile), not a third sentence. It is
 said of the domain as listed. It does not say that a reading made from distinctions is a member of the
 domain, and it does not say that "can go on to do q" has an enforcement protocol. With the second part it
 makes the physical objects of a context correspond one to one with the combinations of sides of its
 distinctions (Thm_APFB02_r3_carries_r2, APFB02.objects_are_the_alignments). The parameters carry the same
 mandatory source vocabulary as in the live B02 module; nothing about them is restated or changed.
-/
import Init

set_option autoImplicit false
universe uG uX uQ uP uR
namespace APFB02

/-- B02 with its list of distinctions complete: both sentences, and the reading that the distinctions of
a context account for every difference of continuation profile. -/
def B02SourceMeaning_r3_whole
    {Context : Type uG} {X : Context → Type uX} {Q : Context → Type uQ}
    {P : Context → Type uP} {Record : Context → Type uR}
    (Cont : (g : Context) → X g → Q g → Prop)
    (Delta : (g : Context) → (X g → Bool) → Prop)
    (maintained : (g : Context) → P g → Record g → Prop)
    (sufficient : (g : Context) → P g → (Record g → Prop) →
      {d : X g → Bool // Delta g d} → Prop)
    (usesToRealize : (g : Context) → P g →
      {d : X g → Bool // Delta g d} → (Record g → Prop) → Prop) : Prop :=
  ((∀ g (d : {f : X g → Bool // Delta g f}),
    (∀ x y, Cont g x = Cont g y → d.val x = d.val y) ∧
    (∃ x y, d.val x ≠ d.val y) ∧
    ∃ (p : P g) (sigma : Record g → Prop),
      (∀ r, sigma r → maintained g p r) ∧
      sufficient g p sigma d ∧ usesToRealize g p d sigma) ∧
  ∀ (g : Context) (l : List {f : X g → Bool // Delta g f})
    (v : {f : X g → Bool // Delta g f} → Bool),
    ∃ x : X g, ∀ e ∈ l, e.val x = v e) ∧
  ∀ (g : Context) (x y : X g),
    (∀ d : {f : X g → Bool // Delta g f}, d.val x = d.val y) → Cont g x = Cont g y

end APFB02


