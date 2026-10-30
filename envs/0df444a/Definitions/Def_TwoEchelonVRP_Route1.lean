-- Prove2me | Definitions.Def_TwoEchelonVRP_Route1
-- name    : TwoEchelonVRP_Route1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:27:25.016684+00:00
-- url     : https://prove2.me/theorems/b77538bd-4d6f-43ef-92a2-7d9229d02b5a
-- title:
--   First-level routes $\mathcal M$ with the copies of $(0,k,0)$, and their costs $g_r$
-- statement:
--   A **first-level route** is a cycle through the depot $0$ and a nonempty set $R_r \subseteq N_S$ of satellites, described by the order $s_0, \dots, s_m$ in which it visits them (canonical orientation, see `InjSeq`): the cycle $0, s_0, \dots, s_m, 0$. The index set $\mathcal M$ contains every such route once, except that it contains
--
--   $$
--   \left\lceil \frac{\min\{m_k Q_2,\ q_{\mathrm{tot}}\}}{Q_1} \right\rceil
--   $$
--
--   copies of each single-satellite route $(0, k, 0)$ (possibly none). The cost of route $r$ is the sum of the modified costs of its traversed edges,
--
--   $$
--   g_r = d'_{0 s_0} + \sum_{j=0}^{m-1} d'_{s_j s_{j+1}} + d'_{s_m 0} .
--   $$
--
--   $\mathcal M_k \subseteq \mathcal M$ denotes the routes visiting satellite $k$.
--
--   **Formalization Note** An element of `Route1 I` is a canonical satellite sequence together with a copy index below `copies I s`; `copies` uses Mathlib's ceiling division `⌈/⌉` on $\mathbb N$ ($Q_1 > Q_2 \ge 0$). The route $(0, k, 0)$ traverses $\{0, k\}$ twice and costs $2 d_{0k} + U_1$. The module declares `copies`, `Route1` with its `Fintype` instance, `satSet` ($R_r$) and `cost1` ($g_r$).
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Operations Research 61(2) (2013) 298–314, doi:10.1287/opre.1120.1153, §2, unnumbered, p. 299 (first-level route through the depot and a subset of satellites; cost = traversed edges + U_1); §2.1, unnumbered, p. 299 (𝓜, 𝓜_k, R_r, E(R_r), g_r, '⌈min{m_k Q_2, q_tot}/Q_1⌉ copies of the single-satellite route (0, k, 0)')

import Mathlib
import Definitions.Def_TwoEchelonVRP_Instance
import Definitions.Def_TwoEchelonVRP_modCost
import Definitions.Def_TwoEchelonVRP_InjSeq

namespace TwoEchelonVRP

/-- **Number of copies of a first-level route in `𝓜`.**
Baldacci et al., *An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem*,
Operations Research 61(2) (2013) 298–314, §2.1, unnumbered, p. 299: "We assume that the route set
𝓜 contains ⌈min{m_k Q_2, q_tot}/Q_1⌉ copies of the single-satellite route (0, k, 0), for each
satellite k ∈ N_S."

A single-satellite sequence `(k)` gets `⌈min{m_k Q_2, q_tot}/Q_1⌉` copies (possibly `0`); every
route through two or more satellites appears once.

**Formalization Note.** `a ⌈/⌉ b` is Mathlib's ceiling division on `ℕ`, equal to `⌈a / b⌉` for
`b > 0`; here `Q_1 > Q_2 ≥ 0`. -/
def copies {ns nc : ℕ} (I : Instance ns nc) (s : InjSeq ns) : ℕ :=
  if s.1.val = 0 then min (I.mSat (s.2 0) * I.Q2) (qtot I) ⌈/⌉ I.Q1 else 1

/-- **First-level routes** `𝓜`.
Baldacci et al., Operations Research 61(2) (2013), §2, p. 299: a first-level vehicle "performs a
route passing through the depot 0 and a subset of satellites"; §2.1, p. 299: "Let 𝓜 be the index
set of all first-level routes", containing `⌈min{m_k Q_2, q_tot}/Q_1⌉` copies of each
single-satellite route `(0, k, 0)` (`copies`).

An element is a pair `⟨s, j⟩`: a nonempty injective sequence of satellites `s 0, …, s m` in
canonical orientation (`InjSeq.IsCanonical`), describing the cycle `0, s 0, …, s m, 0`, and a copy
index `j < copies I s`. The depot is adjacent to every satellite and the satellites are pairwise
adjacent, so every such sequence is a cycle of `G`.

**Formalization Note.** Canonical orientation gives each cycle (set of traversed edges) one index;
only the single-satellite routes are repeated, exactly as the paper assumes. -/
def Route1 {ns nc : ℕ} (I : Instance ns nc) : Type :=
  Σ s : {s : InjSeq ns // s.IsCanonical}, Fin (copies I s.1)

noncomputable instance {ns nc : ℕ} (I : Instance ns nc) : Fintype (Route1 I) := by
  unfold Route1; infer_instance

/-- The set `R_r` of satellites visited by first-level route `r`
(Baldacci et al., Operations Research 61(2) (2013), §2.1, p. 299). -/
def satSet {ns nc : ℕ} {I : Instance ns nc} (r : Route1 I) : Finset (Fin ns) := r.1.1.toFinset

/-- The cost `g_r = Σ_{{i,j} ∈ E(R_r)} d_ij` of first-level route `r`
(Baldacci et al., Operations Research 61(2) (2013), §2.1, p. 299), with the modified costs
`modCost` of p. 299. For the cycle `0, s 0, …, s m, 0` it is
`d'(0, s 0) + Σ_{j < m} d'(s j, s (j+1)) + d'(s m, 0)`.

**Formalization Note.** For a single-satellite route `(0, k, 0)` the edge `{0, k}` is traversed
twice and charged twice, `2 d_0k + U_1`, so the route carries the full fixed cost `U_1`. -/
noncomputable def cost1 {ns nc : ℕ} (I : Instance ns nc) (r : Route1 I) : ℝ :=
  modCost I none (some (Sum.inl (r.1.1.2 0)))
    + ∑ j : Fin r.1.1.1.val, modCost I (some (Sum.inl (r.1.1.2 j.castSucc))) (some (Sum.inl (r.1.1.2 j.succ)))
    + modCost I (some (Sum.inl (r.1.1.2 (Fin.last _)))) none

end TwoEchelonVRP


