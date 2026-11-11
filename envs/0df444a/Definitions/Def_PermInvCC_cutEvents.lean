-- Prove2me | Definitions.Def_PermInvCC_cutEvents
-- name    : PermInvCC_cutEvents
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:22:58.176246+00:00
-- url     : https://prove2.me/theorems/9db1263c-7a47-49ff-ae02-65460dfc49f5
-- title:
--   Cut events $\mathcal E$ of the bipartite symbol graph
-- statement:
--   The **bipartite symbol graph** has row vertices $R_1,\dots,R_q$ and column vertices $K_1,\dots,K_q$; the cell $(a,b)$ is the edge $R_aK_b$. For a bipartition of the $2q$ vertices, the crossing edges form the event
--   $$E=\{(a,b):\alpha(a)\ne\beta(b)\},\qquad \alpha,\beta:[q]\to\{0,1\}. \tag{2.1}$$
--   $\mathcal E$ is the family of the **nonempty** events so obtained.
--
--   These events index the cut separations $h_E$ and the auxiliary distributions $J^E_T$.
--
--   **Formalization Note** $\{0,1\}$ is `Bool`. The normalization $\alpha(1)=0$ used in the count (2.2) is not imposed; complementing both labellings gives the same event, so the family is the same.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), eq. (2.1), p.10

import Mathlib

namespace PermInvCC

/-- The family `𝓔` of **cut events** of the bipartite symbol graph (Y. Huang and Z. Ye,
arXiv:2609.40116, held version sha256 fe1797dd…, eq. (2.1), p.10): the nonempty sets of cells
`E = {(a, b) : α(a) ≠ β(b)}` for labellings `α, β : [q] → {0, 1}` (the crossing edges of a
bipartition of the `2q` vertices `R₁, …, R_q, K₁, …, K_q`).

**Formalization Note.** `{0, 1}` is `Bool`. The normalization `α(1) = 0` used for the count (2.2)
is not imposed: complementing both labellings gives the same set, so `𝓔` is unchanged. -/
def cutEvents (q : ℕ) : Finset (Finset (Fin q × Fin q)) :=
  ((Finset.univ : Finset ((Fin q → Bool) × (Fin q → Bool))).image fun αβ =>
      Finset.univ.filter fun e : Fin q × Fin q => αβ.1 e.1 ≠ αβ.2 e.2).filter
    fun E => E.Nonempty

end PermInvCC


