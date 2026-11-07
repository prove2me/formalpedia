-- Prove2me | Definitions.Def_BlockSSM_Tracker_Tracks
-- name    : BlockSSM_Tracker_Tracks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:21:07.737903+00:00
-- url     : https://prove2.me/theorems/f00994d9-917b-46f9-8c9e-4475f749e91a
-- title:
--   The decoder of a tracker tracks $G$
-- statement:
--   The decoder of a tracker **tracks** $G$ if
--   $$
--   \mathrm{dec}(F_s(h_0))=\pi(s)
--   $$
--   for every word $s$ over $G$, including the empty word; in particular $\mathrm{dec}(h_0)=1$. No regularity of the decoder is required.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Definition 1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_BlockSSM_Tracker
import Definitions.Def_BlockSSM_wordProd

universe u

namespace BlockSSM

/-- **The decoder tracks `G`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Definition 1, p.2 (PDF p.3): "A decoder dec : ℂⁿ → G tracks G
if dec(F_s(h₀)) = π(s) for every word, including the empty word."

**Formalization Note.** The quantifier runs over all of `List G`, which contains the empty word. -/
def Tracker.Tracks {G : Type u} [Group G] {b : ℕ∞} (T : Tracker G b) : Prop :=
  ∀ s : List G, T.dec (T.wordMap s T.h₀) = wordProd s

end BlockSSM


