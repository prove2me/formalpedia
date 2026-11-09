-- Prove2me | Definitions.Def_DeletionHash_MixedEdit_Edits
-- name    : DeletionHash_MixedEdit_Edits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:54.652991+00:00
-- url     : https://prove2.me/theorems/cb1a1cd1-7afd-43fd-9a1c-a547b730dbf6
-- title:
--   Bounded substring edits and sequential records
-- statement:
--   An edit record entry specifies a current-word position $p$, a removed length $u$, and a replacement word $V$. It is valid at word $x$ with bound $b$ exactly when $p+u\le |x|$, $u\le b$, $|V|\le b$, and the removed substring differs from $V$. Applying it replaces that substring, retaining the prefix and suffix. A valid record is a finite list whose entries are valid successively at the words produced by earlier entries. Its target is computed by applying the entries in order. Empty replacements, end gaps, overlapping edits and varying intermediate lengths are allowed. These definitions describe the actual channel rather than an abstract edit metric.
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), §1.3, b-substring edits, printed p. 2 (PDF p. 4); §2.4, valid sequential records, printed p. 8 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Words

namespace DeletionHash.MixedEdit

universe u

/-- An edit specifies the position in the current word, removed length and replacement. -/
structure Edit (α : Type u) where
  position : ℕ
  removed : ℕ
  replacement : List α

def applyEdit {α : Type u} (e : Edit α) (x : List α) : List α :=
  x.take e.position ++ e.replacement ++ x.drop (e.position + e.removed)

def ValidEdit {α : Type u} (b : ℕ) (x : List α) (e : Edit α) : Prop :=
  e.position + e.removed ≤ x.length ∧ e.removed ≤ b ∧ e.replacement.length ≤ b ∧
    window e.removed x e.position ≠ e.replacement

def target {α : Type u} (x : List α) (record : List (Edit α)) : List α :=
  record.foldl (fun y e => applyEdit e y) x

def ValidRecord {α : Type u} (b : ℕ) : List α → List (Edit α) → Prop
  | _, [] => True
  | x, e :: es => ValidEdit b x e ∧ ValidRecord b (applyEdit e x) es

end DeletionHash.MixedEdit


