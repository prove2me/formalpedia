-- Prove2me | Definitions.Def_PersistClust_Count_TruncRank
-- name    : PersistClust_Count_TruncRank
-- status  : Definition
-- author  : @fabianroll
-- created : 2026-10-09T13:59:07.505305+00:00
-- url     : https://prove2.me/theorems/1a485a17-d13d-49d7-b829-e5b3091712f4
-- title:
--   truncRank: the truncated rank function of a 0-dimensional persistence module (Eq. 16)
-- statement:
--   For a $0$-dimensional persistence module with rank function $r(s,t)$ (the rank of the structure map $H_0(X_s)\to H_0(X_t)$), the truncation at $\alpha$ replaces the module by the zero module below $\alpha$. In rank language: $\widetilde{r}_\alpha(s,t) = r(s,t)$ if $\alpha \le s$ and $\alpha \le t$, and $0$ otherwise. Keying on both arguments is essential: the truncated module $\widetilde X$ is zero below $\alpha$, so any structure map whose source or target window lies below $\alpha$ has rank $0$. This is Eq. (16) of Appendix A of RR-6968, phrased in the rank-function language of Lemma 4.6.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968 (2009), Appendix A (p. 29), Eq. (16); used throughout the proof of Lemma 4.6 (pp. 20–21) and the corrected statement PersistClust.Count.theorem_4_5_lemma_4_6_corrected

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram

namespace PersistClust.Count

/-! ### The truncated rank function (Eq. 16 of Appendix A in RR-6968, in rank language)

For a $0$-dimensional persistence module whose rank function is $r(s,t)$ (the rank of the
structure map $H_0(X_s)\to H_0(X_t)$), the *truncation at $\alpha$* replaces the module by the
zero module below $\alpha$. In rank language this is
$$\widetilde r_\alpha(s,t) \;=\; \begin{cases} r(s,t) & \text{if } \alpha\le s \text{ and }
\alpha\le t,\\ 0 & \text{otherwise.}\end{cases}$$
Keying on **both** arguments is essential: the truncated module $\widetilde X$ is zero below
$\alpha$, so any structure map whose source or target window lies below $\alpha$ has rank $0$.
This definition is shared by the three decomposition children of `theorem_4_5_lemma_4_6_corrected`
and by their reduction, so that the child statements and the inline proved lemmas of the
reduction all refer to the *same* constant. -/

/-- The truncated rank (Eq. 16 in rank language): `r s t` when both windows are at or above
`α`, and `0` otherwise (the truncated module is `0` below `α`). -/
noncomputable def truncRank (r : ℝ → ℝ → ℕ∞) (a : ℝ) (s t : ℝ) : ℕ∞ :=
  if a ≤ s ∧ a ≤ t then r s t else 0

end PersistClust.Count


