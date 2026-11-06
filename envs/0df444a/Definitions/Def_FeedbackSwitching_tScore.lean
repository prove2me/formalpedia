-- Prove2me | Definitions.Def_FeedbackSwitching_tScore
-- name    : FeedbackSwitching_tScore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:49.848356+00:00
-- url     : https://prove2.me/theorems/788b2bf1-50e4-405e-839a-653c2f183b9c
-- title:
--   Tournament scores $d_t(s,j)$ (Eq. (21)) and score rules (Definition 4)
-- statement:
--   Fix a tournament orientation and a reference chain $P$. On the loss vector $\ell$ of a round, the **one-sided scores** are
--   $$
--   d(s,j)=\begin{cases}\ell(s)-\ell(j),& s\to j,\\ 0,& j\ne s,\ j\to s,\\ -\dfrac{\sum_{i\ne s}P(i\mid s)d(s,i)}{P(s\mid s)},& j=s.\end{cases}
--   $$
--   Two loss vectors have the **same comparisons at $s$** if every difference $\ell(i)-\ell(r)$ with $i,r\in\overline N^+(s)$ agrees.
--
--   A **score rule** for $P$ (with stationary $p$) assigns to each round $t$, current action $s$ and destination $j$ a number $d_t(s,j)$ such that, whenever $\ell_t\in[0,1]^K$: (i) $d_t(s,\cdot)$ is computable from the comparisons observed when $s$ is played; (ii) $\sum_jP(j\mid s)d_t(s,j)=0$; (iii) $|d_t(s,j)|\le1$ for $j\ne s$ and $|d_t(s,s)|\le2(1-P(s\mid s))$; (iv) $\sum_{i,j}p_iP_{ij}d_t(i,j)g_j=-\langle\ell_t,(I-P)g\rangle_p$ for every $g$.
--
--   **Formalization Note** Condition (i) is invariance under loss vectors in $[0,1]^K$ with the same comparisons at $s$. The standing assumptions of Definition 4 ($P$ reversible with respect to a positive $p$, holding probabilities at least $1/2$) are hypotheses of the statements that use score rules.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Eq. (21), p.20 (PDF p.22); Definition 4, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_FeedbackSwitching_IsTournament
import Definitions.Def_FeedbackSwitching_centering
open Matrix

open scoped Classical

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

Two loss vectors give the same comparisons at `s`: every difference `ℓ(i) − ℓ(r)` with
`i, r ∈ N⁺(s)` agrees (p.15: "Playing `s` reveals every difference `ℓ_t(i) − ℓ_t(r)` with
`i, r ∈ N⁺(s)`. Throughout, pairwise comparisons mean these loss differences"). A quantity is
"computable from the comparisons observed when `s` is played" iff it is equal on loss vectors
with the same comparisons at `s`. -/
def sameComparisons {K : ℕ} (A : Fin K → Fin K → Prop) (s : Fin K) (ℓ ℓ' : Fin K → ℝ) : Prop :=
  ∀ i r, closedOut A s i → closedOut A s r → ℓ i - ℓ r = ℓ' i - ℓ' r

/-- **One-sided scores** (Eq. (21), p.20 = PDF p.22) of the tournament `A` for the reference chain
`P`, on the loss vector `ℓ` of the round: `d(s, j) = Δ(s, j) = ℓ(s) − ℓ(j)` if `s → j`;
`0` if `j ≠ s, j → s`; `d(s, s) = −∑_{i≠s} P(i | s) d(s, i) / P(s | s)`. -/
noncomputable def tScore {K : ℕ} (A : Fin K → Fin K → Prop) (P : Matrix (Fin K) (Fin K) ℝ)
    (ℓ : Fin K → ℝ) (s j : Fin K) : ℝ :=
  if j = s then
    -(∑ i ∈ Finset.univ.erase s, P s i * (if A s i then ℓ s - ℓ i else 0)) / P s s
  else if A s j then ℓ s - ℓ j else 0

/-- **Score rule** for `P` (Definition 4, p.28 = PDF p.30). `d t ℓ s j` is the score `d_t(s, j)`
of round `t` when the loss vector of round `t` is `ℓ`. Whenever `ℓ ∈ [0,1]^K`:
(i) `d_t(s, ·)` is computable from the comparisons observed when `s` is played;
(ii) `∑_j P(j | s) d_t(s, j) = 0`; (iii) `|d_t(s, j)| ≤ 1` for `j ≠ s` and
`|d_t(s, s)| ≤ 2(1 − P(s | s))`; (iv) `∑_{i,j} p_i P_ij d_t(i, j) g_j = −⟨ℓ, (I − P)g⟩_p` for every
`g`.

**Formalization Note.** The standing assumptions of Definition 4 (P reversible with respect to a
positive `p`, `P(s | s) ≥ 1/2`) are hypotheses of the statements that use it. Condition (i) is
encoded as invariance under loss vectors in `[0,1]^K` with the same comparisons at `s`. -/
def IsScoreRule {K : ℕ} (A : Fin K → Fin K → Prop) (P : Matrix (Fin K) (Fin K) ℝ)
    (p : Fin K → ℝ) (d : ℕ → (Fin K → ℝ) → Fin K → Fin K → ℝ) : Prop :=
  ∀ t ℓ, InUnitCube ℓ →
    (∀ s ℓ', InUnitCube ℓ' → sameComparisons A s ℓ ℓ' → d t ℓ s = d t ℓ' s) ∧
    (∀ s, ∑ j, P s j * d t ℓ s j = 0) ∧
    (∀ s j, j ≠ s → |d t ℓ s j| ≤ 1) ∧
    (∀ s, |d t ℓ s s| ≤ 2 * (1 - P s s)) ∧
    ∀ g : Fin K → ℝ, ∑ i, ∑ j, p i * P i j * d t ℓ i j * g j = -wInner p ℓ ((1 - P) *ᵥ g)

end FeedbackSwitching


