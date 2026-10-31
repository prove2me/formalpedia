-- Prove2me | Definitions.Def_DworczakDACC_bestM
-- name    : DworczakDACC_bestM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:19.978781+00:00
-- url     : https://prove2.me/theorems/325466c2-9fb1-4010-8c79-37ce79a3c872
-- title:
--   Best option of a budget set for a man: $\arg\max\{B;\succ\}$ with $\emptyset$ available
-- statement:
--   For a man $d$ and a set $B$ of women, the **best option** of $B$ is
--
--   $$\arg\max\{B\cup\{\emptyset\};\succ\},$$
--
--   the most preferred element of $B$ together with the outside option $\emptyset$ of staying unmatched. It equals $\emptyset$ exactly when no member of $B$ is acceptable.
--
--   This is the paper's $\arg\max\{B_i;\succ^i\}$ (footnote 4), with the convention of p. 5 that the outside option is always available. It is the partner an agent proposes to, and the benchmark of the stopping criterion.
--
--   **Formalization Note** Preferences are injective rank functions (smaller rank is better) from the reused definition `RuralHospitals.Market`, and `none` is $\emptyset$. The minimizer of the rank over the nonempty finite set $\{\emptyset\}\cup B$ is unique by injectivity and is selected with `Finset.choose`.
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), §2, p. 5 and footnote 4

import Mathlib
import Definitions.Def_RuralHospitals_Market

namespace DworczakDACC

open RuralHospitals

/-- **The best option of a budget set: argmax{B; ≻} with the outside option ∅ available.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017), §2, p. 5
and footnote 4: "argmax{A; ≻} is defined as the the most preferred option from the set A with
respect to the order ≻"; a budget set is a subset of the other side "and the outside option ∅
(which is always available to agents)".

`bestM Mk d B` is the element `o` of `{none} ∪ {some x : x ∈ B}` with the least rank
`Mk.docRank d o`, i.e. the most preferred option of man `d` among `B ∪ {∅}`. It is `none` exactly
when no member of `B` is acceptable to `d`.

**Formalization Note.** Smaller rank is better (`RuralHospitals.Market`); `none` is `∅`. The
set is nonempty (it contains `none`) and ranks are injective, so the minimizer is unique and is
selected with `Finset.choose`. -/
def bestM {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H] (Mk : Market D H) (d : D)
    (B : Finset H) : Option H :=
  (insert none (B.image some)).choose
    (fun o => ∀ o' ∈ insert none (B.image some), Mk.docRank d o ≤ Mk.docRank d o')
    (by
      obtain ⟨o, ho, hmin⟩ := Finset.exists_min_image (insert none (B.image some)) (Mk.docRank d)
        ⟨none, Finset.mem_insert_self _ _⟩
      refine ⟨o, ⟨ho, hmin⟩, ?_⟩
      rintro o' ⟨ho', hmin'⟩
      exact Mk.docRank_injective d (le_antisymm (hmin' o ho) (hmin o' ho')))

end DworczakDACC


