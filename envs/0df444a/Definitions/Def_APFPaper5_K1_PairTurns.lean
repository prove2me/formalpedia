-- Prove2me | Definitions.Def_APFPaper5_K1_PairTurns
-- name    : APFPaper5_K1_PairTurns
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:26:46.141209+00:00
-- url     : https://prove2.me/theorems/53f94c6a-7c87-43cd-91c7-83532e26bab9
-- title:
--   Supplied signed permutations of the second record
-- statement:
--   Defines maps of record pairs that leave the first record fixed and apply an arbitrary coordinate permutation with complements to the second. Physical admission and independent action on one member of a pair are not asserted.
--
--   This is reference mathematics on Boolean records and the exact supplied predicates; it establishes no physical quantum reconstruction, admitted hold or additional foundation input.
--
--   **Supplied data and hypotheses**
--
--   - {'declaration': 'APFPaper5.K1.relOfPair', 'statement_and_binders': 'noncomputable def relOfPair {D : Type*} [Fintype D] (p : (D → Bool) × (D → Bool)) : ℝ'}
--   - {'declaration': 'APFPaper5.K1.pairTurns', 'statement_and_binders': 'def pairTurns (D : Type*) : Set ((D → Bool) × (D → Bool) → (D → Bool) × (D → Bool))'}
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
--   Definitions/Def_APFPaper5_K1_PairTurns.lean; Sib v58 / pullbacks v9, SHA-256 e80ac1e57dac2ceaad7d9d0f523ca2d0489d62670729e086e91948c7484c7cf3. {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1276-1332;2168-2180', 'scope': 'Physical distinction descent and filter pull-back; does not itself supply NothingDrawn on the listed coordinate family.'}; {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1660-1680;1714-1723;2966-3076', 'scope': 'Conditional ledger isometry, connected real-carrier quarter turns, and remaining physical readout obligations.'}; {'path': 'APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json', 'revision': '2026-11-14.1', 'scope': 'B02 finite assignment amendment only; no installed hold or motion reading.'}; {'path': 'frozen/builder/RULING_hold_readings_2026-11-14.md', 'scope': 'Author discussion recorded as readings; explicit theorem hypotheses, not installed input adoption.'}; {'path': 'frozen/builder/TEE_UP_one_opposition_away_2026-11-14.md', 'scope': 'Advice/question only; no ruling selects every-state or occupant-state interpretation.'}; {'path': 'source/Definitions/Def_APFPaper5_K1_PairTurns.lean', 'sha256': 'e80ac1e57dac2ceaad7d9d0f523ca2d0489d62670729e086e91948c7484c7cf3'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFPaper5_K1_PairTurns
title: The relation of two records of a finite region as a fraction of its distinctions, and the turns of a pair of records
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: ordinary mathematics on Def_APFPaper5_K1_AlignmentCount (overlapOn) and Def_APFPaper5_K1_PairParity
 (holdStep). The kind of map in pairTurns is the kind the readings of a hold adopted on 2026-11-14 11:33 HST
 allow (RULING_hold_readings_2026-11-14). FOUNDATION_INPUTS is not consumed.
standing: two definitions. pairTurns is a supplied set of maps. No claim is made here that its members are
 admitted holds of any interface, or that a hold may act on one record of a pair and leave the other.
contents: relOfPair p is the overlap of the two records of p divided by the number of distinctions; it lies
 between -1 and 1. pairTurns D is the set of maps that leave the first record of a pair and act on the second
 by a rearrangement of the distinctions with some turned over.
-/
import Definitions.Def_APFPaper5_K1_PairParity
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
namespace APFPaper5.K1

/-- The relation of two records, as a fraction of the number of distinctions. -/
noncomputable def relOfPair {D : Type*} [Fintype D] (p : (D → Bool) × (D → Bool)) : ℝ :=
  overlapOn Finset.univ p.1 p.2 / (Fintype.card D : ℝ)

/-- Turns of a pair of records: the first is left, the second is rearranged with turn-overs. -/
def pairTurns (D : Type*) : Set ((D → Bool) × (D → Bool) → (D → Bool) × (D → Bool)) :=
  {F | ∃ (f : D → Bool) (sigma : D ≃ D), F = fun p => (p.1, holdStep f sigma p.2)}

end APFPaper5.K1


