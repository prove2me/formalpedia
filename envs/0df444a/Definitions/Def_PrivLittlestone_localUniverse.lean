-- Prove2me | Definitions.Def_PrivLittlestone_localUniverse
-- name    : PrivLittlestone_localUniverse
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:30:04.457778+00:00
-- url     : https://prove2.me/theorems/4a7dd758-8a5f-406d-9554-a52b7eb4a477
-- title:
--   Locally realizable universe $U = F_0$
-- statement:
--   For a class $H$ with $\mathrm{LDim}(H) = d$, the **locally realizable universe** is
--   $$
--   U = F_0 = \{ h \in \{0,1\}^X : H[h, A] \neq \emptyset \text{ whenever } |A| \le d + 1 \}.
--   $$
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Appendix A.2.1, p.17

import Mathlib
import Definitions.Def_PrivLittlestone_restrictCls

namespace PrivLittlestone

/-- The **locally realizable universe** `U = F_0 = {h ∈ {0,1}^X : H[h, A] ≠ ∅ whenever |A| ≤ d + 1}`
(He–He, *Private Online Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission
manuscript (sha256 21480556…c562), Appendix A.2.1, p.17). -/
def localUniverse {X : Type*} (H : Set (X → Bool)) (d : ℕ) : Set (X → Bool) :=
  {h | ∀ A : Finset X, A.card ≤ d + 1 → (restrictCls H h A).Nonempty}

end PrivLittlestone


