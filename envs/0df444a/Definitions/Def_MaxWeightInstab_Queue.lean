-- Prove2me | Definitions.Def_MaxWeightInstab_Queue
-- name    : MaxWeightInstab_Queue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:11:53.542829+00:00
-- url     : https://prove2.me/theorems/733f5607-766a-4859-8f7e-251db49c052e
-- title:
--   The queues $\mathcal A_0,\dots,\mathcal A_J,\mathcal B_0,\dots,\mathcal B_J$ of Figure 1
-- statement:
--   The switched network of Figure 1 has $2J+2$ queues, arranged in two **components**: $\mathcal A=\{\mathcal A_0,\mathcal A_1,\dots,\mathcal A_J\}$ and $\mathcal B=\{\mathcal B_0,\mathcal B_1,\dots,\mathcal B_J\}$. Queues $\mathcal A_1,\dots,\mathcal A_J$ and $\mathcal B_1,\dots,\mathcal B_J$ receive jobs from outside the network; $\mathcal A_0$ receives the jobs served at $\mathcal B_1,\dots,\mathcal B_J$, and $\mathcal B_0$ those served at $\mathcal A_1,\dots,\mathcal A_J$.
--
--   **Formalization Note** The queue index set is $\{0,\dots,J\}\sqcup\{0,\dots,J\}$; the left copy is component $\mathcal A$, the right copy component $\mathcal B$, and index $0$ is the internally fed queue.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, Figure 1 and p.3

import Mathlib

namespace MaxWeightInstab

/-- The `2J + 2` queues of the switched network of Figure 1 (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, Figure 1 and p.3):
`Sum.inl i` is queue `𝒜ᵢ` and `Sum.inr i` is queue `ℬᵢ`, for `i = 0, …, J`.

**Formalization Note.** Index `0` is the internal queue (`𝒜₀`, `ℬ₀`); indices `1, …, J` are the
queues fed by external arrivals. Component `𝒜` is the `Sum.inl` block, component `ℬ` the
`Sum.inr` block. -/
abbrev Queue (J : ℕ) : Type := Fin (J + 1) ⊕ Fin (J + 1)

end MaxWeightInstab


