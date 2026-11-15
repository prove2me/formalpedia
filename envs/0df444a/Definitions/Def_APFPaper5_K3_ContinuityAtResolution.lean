-- Prove2me | Definitions.Def_APFPaper5_K3_ContinuityAtResolution
-- name    : APFPaper5_K3_ContinuityAtResolution
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:26:43.962407+00:00
-- url     : https://prove2.me/theorems/e2456719-b2d6-4e14-a36d-54c72484f51b
-- title:
--   Continuity as finite-resolution hypotheses
-- statement:
--   The encoding matches the recorded rereading as a named hypothesis, with eventual coverage across a growing family. RangesAtResolution has lo<hi and approximate coverage; TurnsReachAtResolution quantifies all states/targets and a supplied Adm; TurnsLoseNothing asserts an Adm-left-inverse for every Adm map. None is an adopted foundation premise.
--
--   **Supplied data and hypotheses**
--
--   - {'declaration': 'APFPaper5.K3.RangesAtResolution', 'statement_and_binders': 'def RangesAtResolution {S : Type u} (rel : S → ℝ) (lo hi delta : ℝ) : Prop'}
--   - {'declaration': 'APFPaper5.K3.TurnsReachAtResolution', 'statement_and_binders': 'def TurnsReachAtResolution {S : Type u} (rel : S → ℝ) (lo hi delta : ℝ) (Adm : Set (S → S)) : Prop'}
--   - {'declaration': 'APFPaper5.K3.ContinuityAtResolution', 'statement_and_binders': 'def ContinuityAtResolution {S : Type u} (rel : S → ℝ) (lo hi delta : ℝ) (Adm : Set (S → S)) : Prop'}
--   - {'declaration': 'APFPaper5.K3.ContinuityToAnyFineness', 'statement_and_binders': 'def ContinuityToAnyFineness (R : ℕ → Type u) (rel : (n : ℕ) → R n → ℝ) (lo hi : ℝ)\n    (Adm : (n : ℕ) → Set (R n → R n)) : Prop'}
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_ContinuityAtResolution.lean; Sib v58 / pullbacks v9, SHA-256 117f0661ce7173d6fe256eaad31b73b54492bc865f736fcf8edcbf15459221ca. {'path': 'source/Definitions/Def_APFPaper5_K3_ContinuityAtResolution.lean', 'sha256': '117f0661ce7173d6fe256eaad31b73b54492bc865f736fcf8edcbf15459221ca', 'line': 43, 'declaration': 'APFPaper5.K3.ContinuityToAnyFineness'}; {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFPaper5_K3_ContinuityAtResolution
title: The continuity clause as re-read by the author on 2026-11-14: to any fineness, in a large enough region
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's ruling of 2026-11-14 12:47 HST, "Yes, reread as proposed"
 (RULING_continuity_reread_2026-11-14), on the clause adopted on 2026-11-12: "the number in a relation
 ranges over an interval, and a turn that changes it is admissible and loses nothing". Paper 5 Supplement
 v7.33:3559-3564 and 3670-3674 (finite calibration certifies only a declared finite-resolution orbit cover;
 the connectedness/continuum gate is open). FOUNDATION_INPUTS is not consumed.
standing: a NAMED HYPOTHESIS of the K layer in its ADOPTED READING. It is not a declared input.
 Def_APFPaper5_K3_Continuity, the clause as first typed (every real value of an interval is taken), is kept
 as the strong form and is no longer the reading of the clause.
reading: "ranges over an interval" at a fineness: every value from lo to hi is no further than delta from the
 relation number of some state. "A turn that changes it is admissible": from every state an admissible turn
 reaches every value from lo to hi, no further than delta from it. "Loses nothing" is unchanged
 (TurnsLoseNothing). "To any fineness, in a large enough region": for a family of regions numbered by size,
 every fineness is met by every region from some size on.
statement: RangesAtResolution, TurnsReachAtResolution, ContinuityAtResolution, ContinuityToAnyFineness.
-/
import Definitions.Def_APFPaper5_K3_Continuity

set_option autoImplicit false
namespace APFPaper5.K3

universe u

/-- Every value from `lo` to `hi` is no further than `delta` from the relation number of some state. -/
def RangesAtResolution {S : Type u} (rel : S → ℝ) (lo hi delta : ℝ) : Prop :=
  lo < hi ∧ ∀ t : ℝ, lo ≤ t → t ≤ hi → ∃ s : S, |rel s - t| ≤ delta

/-- From every state an admissible turn reaches every value from `lo` to `hi`, to the same fineness. -/
def TurnsReachAtResolution {S : Type u} (rel : S → ℝ) (lo hi delta : ℝ) (Adm : Set (S → S)) : Prop :=
  ∀ s : S, ∀ t : ℝ, lo ≤ t → t ≤ hi → ∃ f ∈ Adm, |rel (f s) - t| ≤ delta

/-- The continuity clause at one fineness. -/
def ContinuityAtResolution {S : Type u} (rel : S → ℝ) (lo hi delta : ℝ) (Adm : Set (S → S)) : Prop :=
  RangesAtResolution rel lo hi delta ∧ TurnsReachAtResolution rel lo hi delta Adm ∧
    TurnsLoseNothing Adm

/-- The continuity clause as re-read on 2026-11-14: to any fineness, in a large enough region. -/
def ContinuityToAnyFineness (R : ℕ → Type u) (rel : (n : ℕ) → R n → ℝ) (lo hi : ℝ)
    (Adm : (n : ℕ) → Set (R n → R n)) : Prop :=
  ∀ delta : ℝ, 0 < delta → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ContinuityAtResolution (rel n) lo hi delta (Adm n)

end APFPaper5.K3


