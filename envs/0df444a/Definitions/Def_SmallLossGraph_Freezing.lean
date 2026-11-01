-- Prove2me | Definitions.Def_SmallLossGraph_Freezing
-- name    : SmallLossGraph_Freezing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:53:31.78522+00:00
-- url     : https://prove2.me/theorems/7b15b749-3c77-407d-b43c-af12ea4c2a7c
-- title:
--   One round of the Double-Threshold Freezing Algorithm: frozen sets $F_k$, sampling $w$, estimates $\tilde\ell$
-- statement:
--   One round of the **Double-Threshold Freezing Algorithm** (Algorithm 1). The input is a feedback graph $G$, the probability vector $p$ proposed by a full-information algorithm, the true losses $\ell$, a learning parameter $\varepsilon'$ and an upper bound $\alpha$ on the independent sets of $G$. The thresholds are
--
--   $$
--   \gamma=\frac{\varepsilon'}{4\alpha},\qquad \gamma'=\frac{\gamma}{3}.
--   $$
--
--   1. **Initial step:** $F_0=\{i : \sum_{j\in N_i}p_j<\gamma\}$.
--   2. **Propagation steps:** for $k\ge1$, $F_k=\{i\notin\bigcup_{m<k}F_m : \sum_{j\in N_i\setminus\bigcup_{m<k}F_m}p_j<\gamma'\}$, built recursively; the **frozen set** is $F=\bigcup_{k\ge0}F_k$.
--   3. **Sampling distribution:** $w_i=0$ for $i\in F$ and $w_i=p_i/(1-\sum_{j\in F}p_j)$ otherwise.
--   4. **Observation probability:** $W_i=\sum_{j\in N_i}w_j$.
--   5. **Estimated loss**, given the drawn arm $I$: $\tilde\ell_i=\ell_i/W_i$ if $i\in N_I\setminus F$, and $\tilde\ell_i=0$ otherwise.
--
--   The frozen sets are defined for arbitrary thresholds $\gamma,\gamma'$; the algorithm uses the values above.
--
--   **Formalization Note** The union $\bigcup_{k\ge0}F_k$ ranges over all $k\in\mathbb N$ (the steps are eventually empty). When $1-\sum_{j\in F}p_j\le0$, i.e. every arm carrying probability is frozen, the paper's normalization divides by zero; the definition then sets $w=p$. This never happens for $\varepsilon'<1$ (Lemma 3.1). Lean's $x/0=0$ convention is used for $\ell_i/W_i$ and for $\gamma$ at $\alpha=0$; every theorem excludes these cases through its hypotheses.
-- source:
--   Lykouris–Sridharan–Tardos, Small-loss bounds for online learning with partial information, arXiv:1711.03639v5, Algorithm 1 (Double-Threshold Freezing Algorithm), lines 3–7, p.8

import Mathlib
import Definitions.Def_SmallLossGraph_Protocol

open scoped BigOperators

namespace SmallLossGraph

/-- **The freezing threshold `γ = ε′/(4α)`** of Algorithm 1 (arXiv:1711.03639v5, Algorithm 1,
p.8: "freezing thresholds `γ := ε′/(4α)` and `γ′ := γ/3`"). -/
noncomputable def gamma (ε' : ℝ) (α : ℕ) : ℝ := ε' / (4 * (α : ℝ))

/-- **The propagation threshold `γ′ = γ/3`** of Algorithm 1 (arXiv:1711.03639v5, Algorithm 1,
p.8). -/
noncomputable def gammaPrime (ε' : ℝ) (α : ℕ) : ℝ := gamma ε' α / 3

/-- **Initial freezing step `F_0`** (arXiv:1711.03639v5, Algorithm 1, line 3, p.8):
`F_0 = {i : ∑_{j ∈ N_i} p_j < γ}`, the arms whose observation probability under `p` is below `γ`.

**Formalization Note** One round; `p` is the full-information algorithm's vector `p^t`, `G` the
feedback graph `G^t`. -/
noncomputable def frozen0 {d : ℕ} (G : SimpleGraph (Fin d)) (p : Fin d → ℝ) (γ : ℝ) :
    Finset (Fin d) :=
  open scoped Classical in Finset.univ.filter (fun i => ∑ j ∈ closedNbhd G i, p j < γ)

/-- One propagation step (arXiv:1711.03639v5, Algorithm 1, line 4, p.8): given the set `U` of
arms frozen so far, the arms `i ∉ U` whose probability of being observed by not-yet-frozen arms,
`∑_{j ∈ N_i \ U} p_j`, is below `γ′`. -/
noncomputable def propStep {d : ℕ} (G : SimpleGraph (Fin d)) (p : Fin d → ℝ) (γ' : ℝ)
    (U : Finset (Fin d)) : Finset (Fin d) :=
  open scoped Classical in Finset.univ.filter (fun i => i ∉ U ∧ ∑ j ∈ closedNbhd G i \ U, p j < γ')

/-- `frozenBefore G p γ γ' k = ⋃_{m < k} F_m`, the arms frozen in the steps before step `k`
(arXiv:1711.03639v5, Algorithm 1, line 4, p.8), built by the recursion of the algorithm:
`⋃_{m<0} = ∅`, `⋃_{m<1} = F_0`, `⋃_{m<k+2} = ⋃_{m<k+1} ∪ F_{k+1}`. -/
noncomputable def frozenBefore {d : ℕ} (G : SimpleGraph (Fin d)) (p : Fin d → ℝ) (γ γ' : ℝ) :
    ℕ → Finset (Fin d)
  | 0 => ∅
  | 1 => frozen0 G p γ
  | k + 2 => frozenBefore G p γ γ' (k + 1) ∪ propStep G p γ' (frozenBefore G p γ γ' (k + 1))

/-- **The freezing step `F_k`** of Algorithm 1 (arXiv:1711.03639v5, lines 3–4, p.8):
`F_0 = {i : ∑_{j∈N_i} p_j < γ}` and, for `k ≥ 1`,
`F_k = {i ∉ ⋃_{m<k} F_m : ∑_{j ∈ N_i \ ⋃_{m<k} F_m} p_j < γ′}`. -/
noncomputable def frozenStep {d : ℕ} (G : SimpleGraph (Fin d)) (p : Fin d → ℝ) (γ γ' : ℝ) :
    ℕ → Finset (Fin d)
  | 0 => frozen0 G p γ
  | k + 1 => propStep G p γ' (frozenBefore G p γ γ' (k + 1))

/-- **The frozen set `F = ⋃_{k ≥ 0} F_k`** (arXiv:1711.03639v5, Algorithm 1, line 4, p.8).

**Formalization Note** The union is over all `k : ℕ` (the steps are eventually empty). -/
noncomputable def frozen {d : ℕ} (G : SimpleGraph (Fin d)) (p : Fin d → ℝ) (γ γ' : ℝ) :
    Finset (Fin d) :=
  open scoped Classical in Finset.univ.filter (fun i => ∃ k, i ∈ frozenStep G p γ γ' k)

/-- **The arms frozen in the propagation steps, `⋃_{k ≥ 1} F_k`** (arXiv:1711.03639v5,
Claim 3.3, p.9). -/
noncomputable def propFrozen {d : ℕ} (G : SimpleGraph (Fin d)) (p : Fin d → ℝ) (γ γ' : ℝ) :
    Finset (Fin d) :=
  open scoped Classical in Finset.univ.filter (fun i => ∃ k, 1 ≤ k ∧ i ∈ frozenStep G p γ γ' k)

/-- **The sampling distribution `w`** (arXiv:1711.03639v5, Algorithm 1, line 5, p.8):
`w_i = 0` if `i ∈ F`, and `w_i = p_i / (1 − ∑_{j∈F} p_j)` otherwise.

**Formalization Note** When `1 − ∑_{j∈F} p_j ≤ 0` (every arm carrying probability is frozen),
line 5 divides by zero and the paper's algorithm is undefined; the convention here is `w = p`
(play `A`'s distribution unchanged). This case never occurs for `ε′ < 1` (Lemma 3.1); the
convention keeps `w` a probability vector whenever `p` is one. -/
noncomputable def sampling {d : ℕ} (G : SimpleGraph (Fin d)) (p : Fin d → ℝ) (γ γ' : ℝ)
    (i : Fin d) : ℝ :=
  open scoped Classical in
  if 1 - ∑ j ∈ frozen G p γ γ', p j ≤ 0 then p i
  else if i ∈ frozen G p γ γ' then 0 else p i / (1 - ∑ j ∈ frozen G p γ γ', p j)

/-- **Observation probability `W_i = ∑_{j ∈ N_i} w_j`** (arXiv:1711.03639v5, Algorithm 1,
line 7, p.8): the probability that arm `i` is observed when `I ∼ w`. -/
noncomputable def obsProb {d : ℕ} (G : SimpleGraph (Fin d)) (p : Fin d → ℝ) (γ γ' : ℝ)
    (i : Fin d) : ℝ :=
  ∑ j ∈ closedNbhd G i, sampling G p γ γ' j

/-- **The estimated loss `ℓ̃`** (arXiv:1711.03639v5, Algorithm 1, line 7, p.8): given the drawn
arm `I`, `ℓ̃_i = ℓ_i / W_i` if `i ∈ N_I \ F`, and `ℓ̃_i = 0` otherwise. -/
noncomputable def estLoss {d : ℕ} (G : SimpleGraph (Fin d)) (ℓ p : Fin d → ℝ) (γ γ' : ℝ)
    (I : Fin d) (i : Fin d) : ℝ :=
  open scoped Classical in
  if i ∈ closedNbhd G I ∧ i ∉ frozen G p γ γ' then ℓ i / obsProb G p γ γ' i else 0

end SmallLossGraph


