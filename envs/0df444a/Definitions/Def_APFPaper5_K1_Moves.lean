-- Prove2me | Definitions.Def_APFPaper5_K1_Moves
-- name    : APFPaper5_K1_Moves
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:26:44.18963+00:00
-- url     : https://prove2.me/theorems/4a7e2d6c-ca9f-47ed-85d1-0b441d0353a5
-- title:
--   Every Boolean record moves one coordinate away
-- statement:
--   Defines universal one-opposition motion: every record has overlap n minus 2 with its image, where n is the finite number of distinctions. This quantifies over every Boolean record, not just the occupied record.
--
--   This is reference mathematics on Boolean records and the exact supplied predicates; it establishes no physical quantum reconstruction, admitted hold or additional foundation input.
--
--   **Supplied data and hypotheses**
--
--   - {'declaration': 'APFPaper5.K1.MovesOneAway', 'statement_and_binders': 'def MovesOneAway {D : Type*} [Fintype D] (g : (D → Bool) → D → Bool) : Prop'}
--   - {'declaration': 'APFPaper5.K1.TwoStepsNotBack', 'statement_and_binders': 'def TwoStepsNotBack {D : Type*} (g : (D → Bool) → D → Bool) : Prop'}
--   - {'declaration': 'APFPaper5.K1.quarterOn', 'statement_and_binders': 'def quarterOn {D : Type*} [DecidableEq D] (d1 d2 : D) : (D → Bool) → D → Bool'}
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
--   Definitions/Def_APFPaper5_K1_Moves.lean; Sib v58 / pullbacks v9, SHA-256 6c59dad96e174f8479d2fd6b81e3057a2c2cf60addf35b8521e4d499ac16653a. {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1276-1332;2168-2180', 'scope': 'Physical distinction descent and filter pull-back; does not itself supply NothingDrawn on the listed coordinate family.'}; {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1660-1680;1714-1723;2966-3076', 'scope': 'Conditional ledger isometry, connected real-carrier quarter turns, and remaining physical readout obligations.'}; {'path': 'APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json', 'revision': '2026-11-14.1', 'scope': 'B02 finite assignment amendment only; no installed hold or motion reading.'}; {'path': 'frozen/builder/RULING_hold_readings_2026-11-14.md', 'scope': 'Author discussion recorded as readings; explicit theorem hypotheses, not installed input adoption.'}; {'path': 'frozen/builder/TEE_UP_one_opposition_away_2026-11-14.md', 'scope': 'Advice/question only; no ruling selects every-state or occupant-state interpretation.'}; {'path': 'source/Definitions/Def_APFPaper5_K1_Moves.lean', 'sha256': '6c59dad96e174f8479d2fd6b81e3057a2c2cf60addf35b8521e4d499ac16653a'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFPaper5_K1_Moves
title: "Something moves" on the records of a finite region, in two parts, and the quarter turn of one pair of distinctions
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: sentence IV of NOTE_derivation_pass_35_2026-11-13 ("a hold takes the record one opposition away and two
 steps on the record is not where it was"), a NAMED hypothesis of the K layer; it is not in FOUNDATION_INPUTS
 at revision 2026-11-14.1 and is not an adopted reading. Paper 5 Supplement v7.33:1565-1583 (a relative loop
 is not the identity when a supplied recombination readout tells two paths apart) and 1720-1723 (a pair
 {I, -I} moves but gives no quarter turn) are the statements it stands in for in the count model.
standing: three definitions. MovesOneAway and TwoStepsNotBack are the two parts of sentence IV, typed on the
 records of a region. quarterOn is a map, not a claim.
contents: MovesOneAway g: every record and its image under g have overlap equal to the number of distinctions
 less two, that is, they are opposed on exactly one distinction. TwoStepsNotBack g: no record is where it was
 after two steps. quarterOn d1 d2: d1 comes to read what d2 read, turned over; d2 comes to read what d1 read;
 every other distinction is left as it was.
-/
import Definitions.Def_APFPaper5_K1_PairParity
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false
namespace APFPaper5.K1

/-- The step takes every record exactly one opposition away. -/
def MovesOneAway {D : Type*} [Fintype D] (g : (D → Bool) → D → Bool) : Prop :=
  ∀ v : D → Bool, overlapOn Finset.univ v (g v) = ((Finset.univ : Finset D).card : ℝ) - 2

/-- Two steps never bring a record back to where it was. -/
def TwoStepsNotBack {D : Type*} (g : (D → Bool) → D → Bool) : Prop :=
  ∀ v : D → Bool, g (g v) ≠ v

/-- The quarter turn of the pair (d1, d2). -/
def quarterOn {D : Type*} [DecidableEq D] (d1 d2 : D) : (D → Bool) → D → Bool :=
  holdStep (Function.update (fun _ => false) d1 true) (Equiv.swap d1 d2)

end APFPaper5.K1


