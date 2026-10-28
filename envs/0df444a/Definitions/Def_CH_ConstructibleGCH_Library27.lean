-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library27
-- name    : CH_ConstructibleGCH_Library27
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-25T23:04:45.498987+00:00
-- url     : https://prove2.me/theorems/1ec128f2-651f-4efa-ac1a-f1568ef22023
-- title:
--   Internal injection restriction and power-set image interfaces
-- statement:
--   This library defines the native injection predicates, the formula that restricts a platform injection graph to its domain and codomain, and the formulas for images and power-set image graphs. These interfaces let the separate proofs transport internal cardinal comparisons between the two membership-formula presentations.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: ; Platform semantic adapters by Wentao Li (Victor), with OpenAI Codex assistance; Andrew Marks, Set Theory, Lemma 21.3 and Corollary 21.4, printed pp. 90–91, https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf.

import Definitions.Def_CH_ConstructibleGCH_Library05
import Definitions.Def_CH_ConstructibleGCH_SentenceInterface

import Definitions.Def_CH_ConstructibleGCH_SentenceInterface
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_InternalBridge -/
section GCHSource_Work_CUGCH_InternalBridge
set_option autoImplicit false




/-!
Internal semantic comparison for the two GCH formulations.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

The existing constructible-model interfaces and formalization are by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
-/

namespace ContinuumHypothesis.Constructible.GCHBridge
open _root_.Constructible
open _root_.Constructible.Model
open _root_.Constructible.ContinuumFormula
noncomputable section
open Classical
set_option Elab.async false
set_option maxHeartbeats 1000000













abbrev NativeInjection (f x y : M) : Prop :=
  _root_.Constructible.ContinuumFormula.IsInjection E f x y
abbrev NativeInjects (x y : M) : Prop :=
  _root_.Constructible.ContinuumFormula.Injects E x y
abbrev NativeEquinumerous (x y : M) : Prop :=
  _root_.Constructible.ContinuumFormula.Equinumerous E x y





/-- Restrict a represented relation to the stated source and target sets. -/
def normalizeInjectionFormula : FOFormula 5 :=
  .conj (.mem (3 : Fin 5) (1 : Fin 5))
    (.conj (.mem (4 : Fin 5) (2 : Fin 5))
      (graphValueAt (0 : Fin 5) (3 : Fin 5) (4 : Fin 5)))









end
end ContinuumHypothesis.Constructible.GCHBridge


end GCHSource_Work_CUGCH_InternalBridge


/- Source module: Solutions.Work_CUGCH_PowerBridge -/
section GCHSource_Work_CUGCH_PowerBridge
set_option autoImplicit false



/-!
Transport of internal powersets along internally represented injections.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
Uses the constructible separation and graph interfaces of Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
-/

namespace ContinuumHypothesis.Constructible.GCHBridge
open _root_.Constructible
open _root_.Constructible.Model
open _root_.Constructible.ContinuumFormula
noncomputable section
open Classical
set_option Elab.async false
set_option maxHeartbeats 1000000

def ImageOf (f u v : M) : Prop :=
  ∀ z : M, E z v ↔ ∃ x : M, E x u ∧ GraphValue E f x z

def imageMemberAt {n : Nat} (f u z : Fin n) : FOFormula n :=
  FOFormula.boundedEx u
    (graphValueAt f.castSucc (Fin.last n) z.castSucc)



def imageAt {n : Nat} (f u v : Fin n) : FOFormula n :=
  FOFormula.all
    (FOFormula.biimp (.mem (Fin.last n) v.castSucc)
      (imageMemberAt f.castSucc u.castSucc (Fin.last n)))



def imageMemberFormula : FOFormula 3 := imageMemberAt 0 1 2









def powerImageGraphFormula : FOFormula 5 :=
  .conj (.mem (3 : Fin 5) (1 : Fin 5))
    (.conj (.mem (4 : Fin 5) (2 : Fin 5))
      (imageAt (0 : Fin 5) (3 : Fin 5) (4 : Fin 5)))









end
end ContinuumHypothesis.Constructible.GCHBridge


end GCHSource_Work_CUGCH_PowerBridge


