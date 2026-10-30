-- Prove2me | Definitions.Def_OnlineCRS_Combine_chi
-- name    : OnlineCRS_Combine_chi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:15:07.648972+00:00
-- url     : https://prove2.me/theorems/ed148773-802f-4948-b158-a2365fe05de4
-- title:
--   Selectability indicator $\chi_e(A,\mathcal F,\mathcal F')$
-- statement:
--   For an element $e\in N$, a set $A\subseteq N$ and families $\mathcal F,\mathcal F'\subseteq 2^N$, the indicator $\chi_e(A,\mathcal F,\mathcal F')$ holds when
--   $$I\cup\{e\}\in\mathcal F\quad\text{for every } I\subseteq A \text{ with } I\in\mathcal F' .$$
--
--   With $A=R(x)$ and $\mathcal F=\mathcal F'=\mathcal F_x$ this is the event that $e$ is **selectable**: whatever feasible set $I$ of active elements the greedy OCRS has selected before $e$ arrives, $e$ can still be added. It is the event bounded in Definitions 1.4 and 1.5.
--
--   **Formalization Note** $I$ may contain $e$, in which case $I\cup\{e\}=I$.
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, proof of Lemma 2.11 (unnumbered notation), p. 15; selectable elements, p. 3

import Mathlib

namespace OnlineCRS.Combine

/-- **The selectability indicator `χ_e(A, F, F′)`.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, proof of Lemma 2.11, p. 15 (unnumbered): "let us denote by `χ_e(A, F, F′)` an indicator for
the event that `I ∪ {e} ∈ F` for every set `I ⊆ A` obeying `I ∈ F′`."

`chi e A G G'` holds iff `I ∪ {e} ∈ G` for every `I ⊆ A` with `I ∈ G'`. Element `e` is
selectable for the active set `A` and the family `F_x` exactly when `chi e A F_x F_x`
(p. 3, after Definition 1.4).

**Formalization Note.** `I` may contain `e`; then `insert e I = I`, as `I ∪ {e} = I` in the
paper. The indicator is a `Prop`; probabilities use `if chi … then 1 else 0`. -/
def chi {N : Type*} [DecidableEq N] (e : N) (A : Finset N) (G G' : Finset (Finset N)) : Prop :=
  ∀ I ⊆ A, I ∈ G' → insert e I ∈ G

end OnlineCRS.Combine


