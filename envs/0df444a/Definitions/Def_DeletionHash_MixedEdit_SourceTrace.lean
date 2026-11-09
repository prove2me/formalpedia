-- Prove2me | Definitions.Def_DeletionHash_MixedEdit_SourceTrace
-- name    : DeletionHash_MixedEdit_SourceTrace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:05.715037+00:00
-- url     : https://prove2.me/theorems/5d2173b3-855d-441e-a2c1-200a521d02d1
-- title:
--   One-edit derivations with original source indices
-- statement:
--   Choose either no edit or a particular valid one-edit derivation from a source word. The resulting word is computed from that choice. Each retained letter carries its original zero-based source index; each replacement letter carries a marker indicating that it is new. The trace is computed by concatenating the original prefix indices, new-letter markers, and original suffix indices. No letter is assigned an arbitrary provenance. This makes the source-position conclusion of Lemma 2.3 a statement about actual derivations, including unchanged words.
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), §2.2, source positions and new letters preceding/in Lemma 2.3, printed p. 6 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Edits

namespace DeletionHash.MixedEdit

universe u

def oneWord {α : Type u} (x : List α) : Option (Edit α) → List α
  | none => x
  | some e => applyEdit e x

def ValidOne {α : Type u} (b : ℕ) (x : List α) : Option (Edit α) → Prop
  | none => True
  | some e => ValidEdit b x e

/-- Original letters carry their actual source indices; newly written letters carry none. -/
def sourceTrace {α : Type u} (x : List α) : Option (Edit α) → List (Option ℕ)
  | none => (List.range x.length).map some
  | some e => (List.range e.position).map some ++ List.replicate e.replacement.length none ++
      (List.range' (e.position + e.removed) (x.length - (e.position + e.removed))).map some

end DeletionHash.MixedEdit


