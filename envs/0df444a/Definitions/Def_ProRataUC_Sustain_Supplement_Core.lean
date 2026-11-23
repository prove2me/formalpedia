-- Prove2me | Definitions.Def_ProRataUC_Sustain_Supplement_Core
-- name    : ProRataUC_Sustain_Supplement_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:23:42.204772+00:00
-- url     : https://prove2.me/theorems/fbde1147-59f2-41d9-bd0c-0fd0d62dc295
-- title:
--   Definition 4 (Core), p. 62 — x is in the core of f if f(J) ≤ Σ_{j∈J} x_j for all J ⊆ M and f(M) = Σ_{j∈M} x_j
-- statement:
--   This is Definition 4 (Core) of Alaei, Makhdoumi, Malekian and Pekeč, Appendix B.1.4.
--
--   Let $f$ be the coalition value of a coalition $J\subseteq\mathcal M$ of artists (the largest total subscription fee $J$ collects on a competing platform). A vector $\mathbf x=(x_j)_{j\in\mathcal M}$ of real payments to the artists **forms the core** for $f$ if
--   $$f(J)\le\sum_{j\in J}x_j\quad\text{for all }J\subseteq\mathcal M,\qquad f(\mathcal M)=\sum_{j\in\mathcal M}x_j.$$
--   The first condition says that no coalition of artists collects more by leaving for a competing platform than it is paid; the second says that the payments exactly distribute the value of the platform offering all artists. The core is **non-empty** when some vector $\mathbf x$ satisfies both conditions.
--
--   In the paper, the platform's monopoly is sustainable exactly when this core is non-empty; Theorem 4 gives a sufficient condition.
--
--   **Formalization Note** `InCore s x` quantifies over every `Finset` $J$ of artists, including $J=\emptyset$ and $J=\mathcal M$. As in the paper, no sign condition is imposed on $\mathbf x$.
-- source:
--   Alaei, Makhdoumi, Malekian & Pekeč, Revenue-sharing allocation strategies for two-sided media platforms: Pro-rata vs. user-centric, submitted manuscript (SSRN 3645521), p. 62, App. B.1.4, Definition 4

import Mathlib
import Definitions.Def_ProRataUC_Sustain_Setting
import Definitions.Def_ProRataUC_Sustain_Supplement_CoalitionValue

namespace ProRataUC.Sustain.Supplement

open ProRataUC.Sustain

variable {M : Type*}

/-- Definition 4 (Core), p. 62: the vector `x = (x_j)_{j∈M}` forms the core for `f` if
`f(J) ≤ Σ_{j∈J} x_j` for every `J ⊆ M` and `f(M) = Σ_{j∈M} x_j`. No sign condition on `x`. -/
def InCore [Fintype M] (s : Setting M) (x : M → ℝ) : Prop :=
  (∀ J : Finset M, coalitionValue s J ≤ ∑ j ∈ J, x j) ∧
    coalitionValue s Finset.univ = ∑ j, x j

end ProRataUC.Sustain.Supplement


