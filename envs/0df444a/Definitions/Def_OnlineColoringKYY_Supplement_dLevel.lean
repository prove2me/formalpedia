-- Prove2me | Definitions.Def_OnlineColoringKYY_Supplement_dLevel
-- name    : OnlineColoringKYY_Supplement_dLevel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:08:34.138228+00:00
-- url     : https://prove2.me/theorems/fc17124b-16a5-40ac-bdad-81675639e8e5
-- title:
--   Algorithm 2: the $d$-level randomized online coloring algorithm
-- statement:
--   **Algorithm 2** of Section 5.4 has an integer $d \ge 2$ and integer thresholds $\theta_{d-1}, \dots, \theta_1 \ge 1$. For each arriving vertex $v$, with $E_i(v)$ the set of eligible level-$i$ colors (colors used on exactly $i$ earlier vertices, none of them adjacent to $v$):
--
--   1. for $i = d-1, \dots, 2, 1$: if $|E_i(v)| \ge \theta_i$, choose a color of $E_i(v)$ uniformly at random, color $v$ with it, and stop;
--   2. if no $i$ qualifies, color $v$ with a fresh color.
--
--   Equivalently, $v$ receives a uniformly random color of $E_i(v)$ for the largest $i \in \{1, \dots, d-1\}$ with $|E_i(v)| \ge \theta_i$. For $d = 2$ only level $1$ is examined.
--
--   The **run** of Algorithm 2 on a fixed input graph with vertices $0, \dots, n-1$ is the distribution of the list of colors over the algorithm's random choices only (oblivious adversary).
--
--   This is the algorithm of Theorem 5.15.
--
--   **Formalization Note** The thresholds are a function $\theta : \mathbb N \to \mathbb N$ of which only $\theta(1), \dots, \theta(d-1)$ are used. Level $i$ is tested as "$E_i(v)$ nonempty and $\theta_i \le |E_i(v)|$", the same test when $\theta_i \ge 1$.
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 5.4 "General-Level Algorithm" and Algorithm 2, printed pp.17–18 (PDF pp.19–20)

import Mathlib
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_Supplement_Common

set_option autoImplicit false

namespace OnlineColoringKYY.Supplement

open Classical

/-- One step of **Algorithm 2, the `d`-level algorithm** (Kawarabayashi–Yoneda–Yoneda, *Online
Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027
submission (manuscript sha256 3d1eeea6…), Section 5.4 and Algorithm 2, printed pp.17–18 = PDF
pp.19–20), with integer thresholds `θ i ≥ 1` for `i = 1, …, d − 1`: the distribution of the color
of the arriving vertex `v`, given the colors `c` of `0, …, v − 1`.

Take the largest `i ∈ {d − 1, …, 1}` such that at least `θ i` level-`i` colors are eligible for
`v`, and choose one of the eligible level-`i` colors uniformly at random. If no such `i` exists,
assign a fresh color.

**Formalization Note** Only the values `θ 1, …, θ (d − 1)` are used. The test on level `i` is
"`E_i` nonempty and `θ i ≤ |E_i|`"; for `θ i ≥ 1` the first part is implied by the second. -/
noncomputable def dLevelStep (d : ℕ) (θ : ℕ → ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (c : List ℕ) : PMF ℕ :=
  let lv : Finset ℕ := (Finset.Icc 1 (d - 1)).filter
    (fun i => (eligibleLevel G v c i).Nonempty ∧ θ i ≤ (eligibleLevel G v c i).card)
  if h : lv.Nonempty then
    PMF.uniformOfFinset (eligibleLevel G v c (lv.max' h))
      (Finset.mem_filter.1 (lv.max'_mem h)).2.1
  else PMF.pure (freshColor c)

/-- The **run of Algorithm 2** on the first `m` arrivals of `G : SimpleGraph (Fin n)`
(Kawarabayashi–Yoneda–Yoneda, STOC 2027 submission (manuscript sha256 3d1eeea6…), Algorithm 2,
printed p.18 = PDF p.20): the distribution, over the algorithm's coins only, of the list of colors
of `0, …, m − 1` in arrival order, for the fixed input `G` (oblivious adversary). -/
noncomputable def dLevelRun (d : ℕ) (θ : ℕ → ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    (m : ℕ) → m ≤ n → PMF (List ℕ)
  | 0, _ => PMF.pure []
  | m + 1, h =>
    (dLevelRun d θ G m (Nat.le_of_succ_le h)).bind
      (fun c => (dLevelStep d θ G ⟨m, h⟩ c).map (fun x => c ++ [x]))

end OnlineColoringKYY.Supplement


