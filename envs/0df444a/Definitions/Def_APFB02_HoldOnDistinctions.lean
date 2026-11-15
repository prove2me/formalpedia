-- Prove2me | Definitions.Def_APFB02_HoldOnDistinctions
-- name    : APFB02_HoldOnDistinctions
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:26:38.82169+00:00
-- url     : https://prove2.me/theorems/a7e1b93b-3c10-46f1-87a2-e71dba08d138
-- title:
--   A supplied map draws no new coordinate reading
-- statement:
--   Requires each output distinction to equal one input distinction, optionally complemented, uniformly over all states. The domain-membership requirement is a substantive hold hypothesis; the Supplement alone does not identify its distinction domain with this listed coordinate family.
--
--   This is reference mathematics on Boolean records and the exact supplied predicates; it establishes no physical quantum reconstruction, admitted hold or additional foundation input. NothingDrawn and StillHeldAfter remain explicit hypotheses outside installed FOUNDATION_INPUTS revision 2026-11-14.1; ToldApart and the motion clauses also remain unadopted where used.
--
--   **Supplied data and hypotheses**
--
--   - {'declaration': 'APFB02.readsAfter', 'statement_and_binders': 'def readsAfter {X D : Type*} (reads : D → X → Bool) (h : X → X) : D → X → Bool'}
--   - {'declaration': 'APFB02.NothingDrawn', 'statement_and_binders': 'def NothingDrawn {X D : Type*} (reads : D → X → Bool) (h : X → X) : Prop'}
--   - {'declaration': 'APFB02.StillHeldAfter', 'statement_and_binders': 'def StillHeldAfter {X D : Type*} (reads : D → X → Bool) (h : X → X) : Prop'}
--
--   **Limits**
--
--   - H58-01
--   - H58-02
--   - H58-03
--   - H58-04
--   - H58-05
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFB02_HoldOnDistinctions.lean; Sib v58 / pullbacks v9, SHA-256 dee61f105997789de24b92ef59de77b7a98b3c3edcd4534283faa2e2d6f05074. {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1276-1332;2168-2180', 'scope': 'Physical distinction descent and filter pull-back; does not itself supply NothingDrawn on the listed coordinate family.'}; {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1660-1680;1714-1723;2966-3076', 'scope': 'Conditional ledger isometry, connected real-carrier quarter turns, and remaining physical readout obligations.'}; {'path': 'APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json', 'revision': '2026-11-14.1', 'scope': 'B02 finite assignment amendment only; no installed hold or motion reading.'}; {'path': 'frozen/builder/RULING_hold_readings_2026-11-14.md', 'scope': 'Author discussion recorded as readings; explicit theorem hypotheses, not installed input adoption.'}; {'path': 'frozen/builder/TEE_UP_one_opposition_away_2026-11-14.md', 'scope': 'Advice/question only; no ruling selects every-state or occupant-state interpretation.'}; {'path': 'source/Definitions/Def_APFB02_HoldOnDistinctions.lean', 'sha256': 'dee61f105997789de24b92ef59de77b7a98b3c3edcd4534283faa2e2d6f05074'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFB02_HoldOnDistinctions
title: What a map of a region's states does to its distinctions: what they read after it, "nothing is drawn", and B02's second sentence said of the states it leads to
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
ruling: the author, 2026-11-14 11:33 HST, "They are correct", on NothingDrawn and StillHeldAfter as readings of a
 hold (RULING_hold_readings_2026-11-14). From that time both are ADOPTED READINGS. They remain hypotheses of
 the Lean theorems that use them, and FOUNDATION_INPUTS is unchanged. Where this header says they are put to
 the author, that was their standing before the ruling.
source: Paper 1 Supplement v9.28:2168-2172 (a filter is an induced quotient map of contexts; it "may not invent
 distinctions"), 2175-2180 (coarse-graining: every distinction of the image context pulls back to a distinction
 of the source context, (F*d')([x]) = d'(F[x])). FOUNDATION_INPUTS.json revision 2026-11-14.1, declared input
 B02, current_wording, second sentence, and the scope recorded in its amendment block (each distinction counted
 once; a reading made from distinctions is not claimed to be a member of the domain). The author, 2026-11-13
 15:43 HST ("Under a hold, distinctions aren't drawn or erased, just rearranged."), 2026-11-13 23:32 HST
 ("reading is an action, a distinction is a thing"), 2026-11-14 02:51 HST ("There are no new distinctions").
standing: three predicates. They state no input and are not adopted readings. NothingDrawn is this seat's typed
 reading of "aren't drawn" and of the Supplement's pull-back clause on the domain as B02 now scopes it: the
 pull-back of a distinction is a member of the domain, read on one side or the other. A reading made from
 several members does not count. StillHeldAfter is B02's second sentence said of the region after the map, with
 the states of that region taken to be the states the map leads to (the Supplement's quotient map is onto).
 Whether a hold is such a map, and whether the region after a hold is a context of B02 with the same
 distinctions, are put to the author; nothing here settles either.
fidelity exposure: the Supplement's coarse-graining clause asks only that the pull-back be a distinction of the
 source context. Reading "a distinction of the source context" as "a member of the listed domain, either way
 round" is the step that excludes a reading made from several distinctions, and it rests on the amendment's
 scope, not on the Supplement's words.
-/
import Definitions.Def_APFB02_EachTakesBothSides

set_option autoImplicit false
namespace APFB02

/-- What each distinction reads once the map `h` has acted. -/
def readsAfter {X D : Type*} (reads : D → X → Bool) (h : X → X) : D → X → Bool :=
  fun d x => reads d (h x)

/-- Nothing is drawn by `h`: each distinction, read after `h`, is one of the region's distinctions read
before `h`, on one side or the other. -/
def NothingDrawn {X D : Type*} (reads : D → X → Bool) (h : X → X) : Prop :=
  ∀ d : D, ∃ (e : D) (b : Bool), ∀ x : X, reads d (h x) = xor b (reads e x)

/-- B02's second sentence said of the states `h` leads to: every combination of sides of every finite
family of the distinctions is held after `h` by some state. -/
def StillHeldAfter {X D : Type*} (reads : D → X → Bool) (h : X → X) : Prop :=
  EveryCombinationHeld (readsAfter reads h)

end APFB02


