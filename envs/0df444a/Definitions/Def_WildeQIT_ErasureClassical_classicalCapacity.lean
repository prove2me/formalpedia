-- Prove2me | Definitions.Def_WildeQIT_ErasureClassical_classicalCapacity
-- name    : WildeQIT_ErasureClassical_classicalCapacity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:50.013357+00:00
-- url     : https://prove2.me/theorems/79f7a5b4-89e4-4e7a-953a-179bc8adb2a9
-- title:
--   Classical capacity $C(\mathcal N)$ of a quantum channel
-- statement:
--   Let $\mathcal N$ be a quantum channel. Its **classical capacity** is
--
--   $$
--   C(\mathcal N)\equiv\sup\{\,C : C\text{ is an achievable rate of classical communication for }\mathcal N\,\}.
--   $$
--
--   This is the operational quantity: the best rate, in bits per channel use, at which classical messages can be sent with vanishing maximal error probability.
--
--   **Formalization Note** The supremum is taken in the extended reals, so it is the least upper bound of the set of achievable rates without any boundedness assumption. For a channel with a nonempty input space every rate $C\le0$ is achievable (one message), so the value is never $-\infty$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §20.2.1, p. 562

import Definitions.Def_WildeQIT_ErasureClassical_IsAchievableRate
import Mathlib.Data.EReal.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §20.2.1, p. 562
(the classical capacity `C(N)` of a quantum channel).
-/

namespace WildeQIT.ErasureClassical

/-- **Classical capacity of a quantum channel** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, §20.2.1, p. 562): "The classical capacity `C(N)` of `N` is equal to
the supremum of all achievable rates for classical communication."

**Formalization Note.** The supremum is taken in the extended reals `EReal`, so that it is the
true least upper bound of the set of achievable rates without any boundedness assumption (an
unbounded set would give `⊤`, an empty one `⊥`, never a junk value). For a channel with a
nonempty input space every rate `R ≤ 0` is achievable (one message), so the supremum is not
`⊥`. -/
noncomputable def classicalCapacity {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) : EReal :=
  ⨆ (R : ℝ) (_ : IsAchievableRate N R), (R : EReal)

end WildeQIT.ErasureClassical


