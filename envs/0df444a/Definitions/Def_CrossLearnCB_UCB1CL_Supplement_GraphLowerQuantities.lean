-- Prove2me | Definitions.Def_CrossLearnCB_UCB1CL_Supplement_GraphLowerQuantities
-- name    : CrossLearnCB_UCB1CL_Supplement_GraphLowerQuantities
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:49:10.327906+00:00
-- url     : https://prove2.me/theorems/f78fe985-da28-49d3-a6d5-e8c4324512c1
-- title:
--   Definition 4, p. 13 — the graph quantity ν₂(G)
-- statement:
--   For a finite directed self-looped graph $G$ on $[C]$, let $I(c)=\{d:G(d,c)\}$. Definition 4 is
--   $$\nu_2(G)=\sup_{f\ge0,\ \sum_c f(c)=1}\left(\sum_c\frac{f(c)}{\sqrt{\sum_{d\in I(c)}f(d)}}\right)^2.$$
--   This quantity occurs in the lower bound of Theorem 5.
--
--   **Formalization Note** The supremum is a real `sSup`. For $C>0$ the set is nonempty and, by self-loops and Cauchy–Schwarz, is bounded by $C$: each summand is at most $\sqrt{f(c)}$. A zero numerator contributes zero, including $0/0$. This convention leaves the supremum unchanged: delete zero-weight vertices, or approach the support by positive weights; positive-support terms converge, and all new terms are nonnegative. At $C=0$ the set is empty and its chosen value is zero; Theorem 5 assumes $C>0$, so this value is never used.
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 13, Definition 4

import Mathlib

namespace CrossLearnCB.UCB1CL.Supplement

open Classical in
/-- Definition 4, p. 13. The set is nonempty for C > 0 and bounded by C for self-looped G.
Zero-weight terms are zero, including 0/0. -/
noncomputable def nuTwo {C : ℕ} (G : Fin C → Fin C → Prop) : ℝ :=
  sSup {x : ℝ | ∃ f : Fin C → ℝ, (∀ c, 0 ≤ f c) ∧ (∑ c, f c) = 1 ∧
    x = (∑ c, f c / Real.sqrt (∑ d ∈ Finset.univ.filter (fun d => G d c), f d)) ^ 2}

end CrossLearnCB.UCB1CL.Supplement


