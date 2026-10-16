-- Prove2me | Definitions.Def_StrategicAlloc_CutChoose_ModCutChoose
-- name    : StrategicAlloc_CutChoose_ModCutChoose
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T12:35:29.489975+00:00
-- url     : https://prove2.me/theorems/e6095c9a-ce7d-4beb-a88a-de69cc323b70
-- title:
--   p. 17 — Mechanism 2 (Mod-Cut&Choose) for two agents
-- statement:
--   Mechanism 2, **Mod-Cut&Choose**, takes the bid vectors $\mathbf b_1,\mathbf b_2$ of two agents, writing $\mathbf b_i(S)=\sum_{h\in S}\mathbf b_i(h)$, and runs as follows.
--
--   1. Start with $(E_1,E_2)=(\emptyset,\emptyset)$.
--   2. List the goods as $h_1,\dots,h_m$ in non-increasing order of agent 1's bid $\mathbf b_1$, breaking ties lexicographically (by the index of the good).
--   3. For $i=1,\dots,m$: let $j=\arg\min_{k\in\{1,2\}}\mathbf b_1(E_k)$, ties in favour of $E_1$, and add $h_i$ to $E_j$.
--   4. Let $\ell=\arg\max_{k\in\{1,2\}}\mathbf b_2(E_k)$, ties in favour of $E_1$.
--   5. Return the allocation
--   $$\mathcal A=(M\setminus E_\ell,\ E_\ell):$$
--   agent 2 receives $E_\ell$ and agent 1 the other bundle.
--
--   Steps 1–3 are the "cut" by agent 1 and step 4 the "choice" by agent 2. The tie-breaking rules are part of the mechanism; in particular, if agent 1 bids $0$ on every good, every good goes to $E_1$.
--
--   **Formalization Note** `rank c` is a stable merge sort of $g_1,\dots,g_m$ by non-increasing $c$, which realises the lexicographic tie-breaking; `cut c` is the pair $(E_1,E_2)$ produced by steps 1–3 from agent 1's bid $c$; `modCutChoose b` returns the bundles of agent `0` (agent 1) and agent `1` (agent 2). The page's line 2 says "sorted in decreasing order w.r.t. $v_1$"; a mechanism reads only bids, and the proof of Lemma 4.1 sorts by the declared bids, so the goods are sorted by agent 1's bid $\mathbf b_1$ here. This is a disclosed correction of the page.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 17, Mechanism 2 (Mod-Cut&Choose), lines 1–7

import Mathlib
import Definitions.Def_StrategicAlloc_RRFair_Setting

namespace StrategicAlloc.CutChoose

variable {m : ℕ}

/-- Mechanism 2, lines 1 and 3–5: the cut `(E_1, E_2)` built from agent 1's bid `c`; each good,
in the order `rank c`, goes to the bundle of smaller bid value, ties to `E_1`. -/
noncomputable def cut (c : Fin m → ℝ) : Finset (Fin m) × Finset (Fin m) :=
  (StrategicAlloc.RRFair.rank c).foldl (fun E h => if ∑ g ∈ E.1, c g ≤ ∑ g ∈ E.2, c g
                             then (insert h E.1, E.2) else (E.1, insert h E.2)) (∅, ∅)

/-- Mechanism 2 (Mod-Cut&Choose), lines 6–7, agents `0` = agent 1 and `1` = agent 2: agent 2
receives the bundle `E_ℓ` of larger bid value `b_2(E_ℓ)`, ties to `E_1`, and agent 1 receives
`M \ E_ℓ`. -/
noncomputable def modCutChoose (b : Fin 2 → Fin m → ℝ) : Fin 2 → Finset (Fin m) :=
  let E := cut (b 0)
  let Eℓ := if ∑ g ∈ E.2, b 1 g ≤ ∑ g ∈ E.1, b 1 g then E.1 else E.2
  ![Finset.univ \ Eℓ, Eℓ]

end StrategicAlloc.CutChoose


