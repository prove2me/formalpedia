-- Prove2me | Definitions.Def_PrivLittlestone_rankLayer
-- name    : PrivLittlestone_rankLayer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:31:28.809189+00:00
-- url     : https://prove2.me/theorems/4ae12247-c7a1-4c9b-bb5c-6e97fba02f4f
-- title:
--   Rank layers $F_s$
-- statement:
--   The **rank layers** are $F_0 = U$ and, for $1 \le s \le d$,
--   $$
--   F_s = \{ h \in F_{s-1} : \mathrm{LDim}(H[h, A]) \ge s \text{ whenever } |A| \le d + 1 - s \}.
--   $$
--
--   **Formalization Note** $\mathrm{LDim}$ is the published `UnderstandingML.ldim` in $\mathbb N \cup \{\infty\}$. The recursion is also defined past $d$, where the layers are empty for $\mathrm{LDim}(H) = d$; only $s \le d$ is used.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Appendix A.2.1, p.17

import Mathlib
import Definitions.Def_PrivLittlestone_localUniverse
import Definitions.Def_UnderstandingML_Online

namespace PrivLittlestone

/-- The **rank layers** `F_0 = U` and
`F_s = {h ∈ F_{s−1} : LDim(H[h, A]) ≥ s whenever |A| ≤ d + 1 − s}` for `1 ≤ s ≤ d` (He–He, *Private
Online Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript
(sha256 21480556…c562), Appendix A.2.1, p.17).

**Formalization Note** `LDim` is the published `UnderstandingML.ldim` (in `ℕ∞`). The recursion
continues past `d`; there `|A| ≤ 0` forces `A = ∅` and the layers are empty when `LDim(H) = d`.
Only `s ≤ d` is used (`rankOf`). -/
def rankLayer {X : Type*} (H : Set (X → Bool)) (d : ℕ) : ℕ → Set (X → Bool)
  | 0 => localUniverse H d
  | s + 1 => {h ∈ rankLayer H d s | ∀ A : Finset X, A.card ≤ d + 1 - (s + 1) →
      (((s + 1 : ℕ) : ℕ∞)) ≤ UnderstandingML.ldim (restrictCls H h A)}

end PrivLittlestone


