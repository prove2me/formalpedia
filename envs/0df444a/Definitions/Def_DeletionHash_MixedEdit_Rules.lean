-- Prove2me | Definitions.Def_DeletionHash_MixedEdit_Rules
-- name    : DeletionHash_MixedEdit_Rules
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:57.194123+00:00
-- url     : https://prove2.me/theorems/8e63e092-7a72-4811-8da9-56698a23a91d
-- title:
--   Signed rules, the catalogue and uncancelled supports
-- statement:
--   A rule is the signed integer sum of exactly $2t$ oriented bubbles whose entire vertex sets, including endpoints, are pairwise disjoint. A bubble contributes $R_L(P')-R_L(P)$. The catalogue $K_0$ consists of all vectors representable in this way and depends only on the word, edit and alphabet parameters, not on a hash or starting word. For a finite set $F$ of vectors, $S(F)$ is the union of their nonzero coordinate supports, without cancellation. Its incident vertices are the prefixes and suffixes of those grams. These definitions retain the signed local changes needed for counting and relations.
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Definition 2.5 and following support paragraph, printed p. 8 (PDF p. 10); Definition 4.1, printed p. 11 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Bubbles

namespace DeletionHash.MixedEdit

universe u

/-- The alphabet-independent-of-H catalogue of signed sums of exactly 2t disjoint bubbles. -/
def Catalogue {α : Type u} [DecidableEq α] (k L t b : ℕ) : Set (Spectrum α L) :=
  {w | ∃ B : Fin (2*t) → List α × List α,
    (∀ i, Bubble k L b (B i).1 (B i).2) ∧
    (∀ i j, i ≠ j → Disjoint (bubbleVertices L (B i).1 (B i).2)
      (bubbleVertices L (B j).1 (B j).2)) ∧
    w = ∑ i, (spectrum L (B i).2 - spectrum L (B i).1)}

def supportUnion {α : Type u} {L : ℕ} (F : Finset (Spectrum α L)) : Set (Gram α L) :=
  {g | ∃ w ∈ F, w g ≠ 0}

def incidentVertices {α : Type u} {L : ℕ} (F : Finset (Spectrum α L)) : Set (Gram α (L-1)) :=
  {v | ∃ g ∈ supportUnion F, v = gramPrefix g ∨ v = gramSuffix g}

end DeletionHash.MixedEdit


