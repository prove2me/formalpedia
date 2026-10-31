-- Prove2me | Definitions.Def_KallMayerSLP_RecourseBounds_IsRefinement
-- name    : KallMayerSLP_RecourseBounds_IsRefinement
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:11:49.496465+00:00
-- url     : https://prove2.me/theorems/cae838ab-725d-4ef9-adf7-44d4a0f8eca5
-- title:
--   Refinement of a partition
-- statement:
--   A partition $\mathcal Y=\{\Upsilon_l;\ l=1,\dots,L\}$ of $\Xi$ is a **refinement** of the partition $\mathcal X=\{\Xi_k;\ k=1,\dots,K\}$ if each cell of $\mathcal X$ is the union of one or several cells of $\mathcal Y$:
--   $$
--   \forall k\ \exists S_k\subseteq\{1,\dots,L\}:\qquad \Xi_k=\bigcup_{l\in S_k}\Upsilon_l .
--   $$
--
--   **Formalization Note** $S_k$ is a `Finset (Fin L)`; for a nonempty cell it is automatically nonempty.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, before Corollary 2.3, p.223 (PDF 232)

import Mathlib

namespace KallMayerSLP.RecourseBounds

/-- **Refinement of a partition.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, before Corollary 2.3, printed p.223
(PDF 232): "Let a further partition `Y = {Υ_l; l = 1, ···, L}` of `Ξ` be a refinement of `X`, i.e.
each cell of `X` is the union of one or several cells of `Y`".

`IsRefinement cellX cellY` says that every cell `cellX k` is the union of the cells `cellY l`,
`l ∈ s`, for some finite set `s` of indices.

**Formalization Note.** "One or several" cells: a nonempty cell of `X` forces `s` to be nonempty, so
`s` is not required to be nonempty separately. -/
def IsRefinement {r K L : ℕ} (cellX : Fin K → Set (Fin r → ℝ))
    (cellY : Fin L → Set (Fin r → ℝ)) : Prop :=
  ∀ k, ∃ s : Finset (Fin L), cellX k = ⋃ l ∈ s, cellY l

end KallMayerSLP.RecourseBounds


