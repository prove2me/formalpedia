-- Prove2me | Definitions.Def_OnlineCRS_Combine_selectProb
-- name    : OnlineCRS_Combine_selectProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:16:22.148074+00:00
-- url     : https://prove2.me/theorems/b36c238a-2abf-4285-85d7-0a4af33d8284
-- title:
--   Probability that $e$ is selectable
-- statement:
--   For a greedy OCRS $\pi$, a point $x$ and an element $e$, the probability that $e$ is selectable is
--   $$\Pr\bigl[I\cup\{e\}\in\mathcal F_x\ \ \forall I\subseteq R(x),\ I\in\mathcal F_x\bigr]=\sum_{\mathcal G}\Pr[\mathcal F_{\pi,x}=\mathcal G]\sum_{A\subseteq N}\Pr[R(x)=A]\,\chi_e(A,\mathcal G,\mathcal G),$$
--   the probability being over $R(x)$ and the random choice of $\mathcal F_x$, which are independent.
--
--   **Formalization Note** The masses of the law of $\mathcal F_{\pi,x}$ are extended non-negative reals in Lean and are converted to reals (they are at most $1$).
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Definition 1.4 and the paragraph after it, p. 3

import Mathlib
import Definitions.Def_OnlineCRS_Combine_activeProb
import Definitions.Def_OnlineCRS_Combine_chi
import Definitions.Def_OnlineCRS_Combine_GreedyOCRS

namespace OnlineCRS.Combine

open Classical in
/-- **Probability that `e` is selectable.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Definition 1.4, p. 3: "`Pr[I ∪ {e} ∈ F_x ∀ I ⊆ R(x), I ∈ F_x]`", and the paragraph after
it: "when the greedy OCRS is randomized, then the probability is over `R(x)` and the random choice
of `F_x`."

`selectProb π x e = ∑_G Pr[F_{π,x} = G] · ∑_A Pr[R(x) = A] · [χ_e(A, G, G)]`.

**Formalization Note.** Reading 2: `F_{π,x}` and `R(x)` are independent, so the joint law is the
product of `π.law x` and `activeProb x`. PMF masses are converted with `ENNReal.toReal` (they are
at most `1`). -/
noncomputable def selectProb {N : Type*} [Fintype N] [DecidableEq N] {F : Finset (Finset N)}
    (π : GreedyOCRS F) (x : N → ℝ) (e : N) : ℝ :=
  ∑ G : Finset (Finset N), ((π.law x) G).toReal *
    ∑ A : Finset N, activeProb x A * (if chi e A G G then 1 else 0)

end OnlineCRS.Combine


