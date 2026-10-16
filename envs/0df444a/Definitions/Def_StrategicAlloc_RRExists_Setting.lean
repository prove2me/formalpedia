-- Prove2me | Definitions.Def_StrategicAlloc_RRExists_Setting
-- name    : StrategicAlloc_RRExists_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T12:35:21.773985+00:00
-- url     : https://prove2.me/theorems/bf4a62bd-6ba3-40fb-a116-9c1da09f58cb
-- title:
--   pp. 4–7, 23–24 — additive valuations, bids, best response and PNE, Mechanism 1 (Round-Robin), good- and bundle-level value gaps
-- statement:
--   This file fixes the model of Amanatidis et al. (§2, pp. 4–6) and Round-Robin (Mechanism 1, p. 7).
--
--   1. **Instance.** There are $n \ge 1$ agents $N = \{1,\dots,n\}$ and $m$ goods $M = \{g_1,\dots,g_m\}$. Agent $i$ has a non-negative value $v_i(g)$ for every good $g$, and values bundles additively:
--   $$v_i(S) = \sum_{g \in S} v_i(g), \qquad S \subseteq M.$$
--   2. **Bids.** Each agent $i$ reports a bid vector $\mathbf b_i \in \mathbb R^m_{\ge 0}$; a profile is $\mathbf b = (\mathbf b_1,\dots,\mathbf b_n)$, and $(\mathbf b'_i, \mathbf b_{-i})$ is $\mathbf b$ with agent $i$'s bid replaced by $\mathbf b'_i$.
--   3. **Best response and PNE (Definition 2.7).** For a mechanism $\mathcal M$ mapping bid profiles to allocations, $\mathbf b_i$ is a best response to $\mathbf b_{-i}$ if $v_i(\mathcal M(\mathbf b'_i,\mathbf b_{-i})) \le v_i(\mathcal M(\mathbf b))$ for every $\mathbf b'_i \in \mathbb R^m_{\ge 0}$; $\mathbf b$ is a pure Nash equilibrium (PNE) if it is a bid profile and every $\mathbf b_i$ is a best response. Bundles are judged with the true values $v_i$; the mechanism reads only the bids.
--   4. **Round-Robin (Mechanism 1).** Agents $1, 2, \dots, n, 1, 2, \dots$ take turns; at each turn the active agent receives the available good with the highest bid, ties broken lexicographically: $g \succ_i h$ if $\mathbf b_i(g) > \mathbf b_i(h)$, or $\mathbf b_i(g) = \mathbf b_i(h)$ and $g$ has a lower index than $h$. The mechanism stops when all $m$ goods are allocated. The file defines Round-Robin more generally with an arbitrary first agent $s$ and good set $G$ (agents $s, s+1, \dots, n, 1, \dots$); Mechanism 1 is the case $s = 1$, $G = M$.
--   5. **Value gaps.** For a value vector $w$, the good-level gap is Lemma A.1's
--   $$\varepsilon = \min\{|w(g) - w(h)| : g, h \in M,\ w(g) \neq w(h)\},$$
--   or $\varepsilon = 1$ if there is no positive difference; the bundle-level gap is the same minimum over pairs of bundles $T, T' \subseteq M$ with $w(T) \ne w(T')$, or $1$ if there is none. The bundle-level gap never exceeds the good-level one.
--
--   These objects are the vocabulary of Theorems A.2 and A.3 and of the proof of Theorem A.3.
--
--   **Formalization Note** Agents are `Fin n` with `[NeZero n]` and goods are `Fin m`, both 0-based (the paper's agent 1 is `0`, good $g_j$ is `j - 1`); the index order is the "standard naming of goods" used for tie-breaking. Valuations are per-good real values; additivity is built into `val`. The ranking `rank c` sorts goods by non-increasing bid with the stable `List.mergeSort`, which keeps equal bids in index order. Round-Robin is computed step by step (`allocBefore`, `pick`); `rrFrom s G` runs $|G|$ steps, which is the $\lceil m/n\rceil$ rounds of Mechanism 1 without the empty turns of the last round. `bundleGap` is the repaired $\varepsilon$ of the proof of Theorem A.3 (the page's good-level $\varepsilon$ does not support the step $v_k(A_k) \le v_k(B_k) - \varepsilon_k$).
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, pp. 4–7, §2 (Definition 2.7) and Mechanism 1; p. 23, Lemma A.1 (ε); p. 24, proof of Theorem A.3

import Mathlib
import Definitions.Def_StrategicAlloc_RRFair_Setting

namespace StrategicAlloc.RRExists

variable {n m : ℕ}

/-- The bundle-level gap: the smallest positive difference between the values of two bundles under
`w`, or `1` if there is none. This is the ε of the repaired proof of Theorem A.3 (p. 24). -/
noncomputable def bundleGap (w : Fin m → ℝ) : ℝ :=
  let D := ((Finset.univ.powerset ×ˢ Finset.univ.powerset).filter
      (fun p : Finset (Fin m) × Finset (Fin m) => ∑ g ∈ p.1, w g ≠ ∑ g ∈ p.2, w g)).image
    (fun p => |∑ g ∈ p.1, w g - ∑ g ∈ p.2, w g|)
  if h : D.Nonempty then D.min' h else 1

end StrategicAlloc.RRExists


