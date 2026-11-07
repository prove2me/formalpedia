-- Prove2me | Definitions.Def_PrivLittlestone_IsWitnessAssignment
-- name    : PrivLittlestone_IsWitnessAssignment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:38:16.717274+00:00
-- url     : https://prove2.me/theorems/5e49511d-2c24-41ac-968b-bcd9405474d3
-- title:
--   Public witness assignment (as in Lemma A.1)
-- statement:
--   A **public witness assignment** fixes, before observing data, for each $h \in U$ of rank $r$ a finite set $A_h \subseteq X$ with $|A_h| \le d - r$ and $\mathrm{LDim}(H[h, A_h]) = r$ such that $W_h \cap F_r = \{h\}$. Lemma A.1 shows that one exists.
--
--   **Formalization Note** $\mathrm{LDim}(H[h, A_h]) = r$ is stated together with $H[h, A_h] \neq \emptyset$ (the convention $\mathrm{LDim}(\emptyset) = -1$; the published `ldim ∅` is $0$).
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma A.1, p.17; Appendix A.2.1, p.18

import Mathlib
import Definitions.Def_PrivLittlestone_rankOf
import Definitions.Def_PrivLittlestone_witnessSpace

namespace PrivLittlestone

/-- A **public witness assignment** (He–He, *Private Online Learning of Littlestone Classes and
Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), Lemma A.1, p.17, and
p.18: "fix one such `A_h` for each `h`"): for each `h ∈ U` of rank `r`, a finite set `A_h` with
`|A_h| ≤ d − r` and `LDim(H[h, A_h]) = r` such that `W_h ∩ F_r = {h}`.

**Formalization Note** `LDim(H[h, A_h]) = r` includes that `H[h, A_h]` is nonempty (for `r = 0`
this is the paper's convention `LDim(∅) = −1`; `UnderstandingML.ldim ∅ = 0` in `ℕ∞`). -/
def IsWitnessAssignment {X : Type*} (H : Set (X → Bool)) (d : ℕ) (Aw : (X → Bool) → Finset X) :
    Prop :=
  ∀ h ∈ localUniverse H d,
    (Aw h).card ≤ d - rankOf H d h ∧ (restrictCls H h (Aw h)).Nonempty ∧
      UnderstandingML.ldim (restrictCls H h (Aw h)) = (rankOf H d h : ℕ∞) ∧
      witnessSpace H d Aw h ∩ rankLayer H d (rankOf H d h) = {h}

end PrivLittlestone


