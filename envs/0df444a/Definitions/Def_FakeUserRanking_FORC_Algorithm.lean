-- Prove2me | Definitions.Def_FakeUserRanking_FORC_Algorithm
-- name    : FakeUserRanking_FORC_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:59.118149+00:00
-- url     : https://prove2.me/theorems/fa771d79-97c4-407d-aed9-db35e0ce46ef
-- title:
--   Algorithms 2–3, pp. 19, 27 — GraphRankSelect and the FORC algorithm (levels, cross-learning (17)–(18), edge rule (19), elimination)
-- statement:
--   This file defines the ranking rule GraphRankSelect (Algorithm 2) and the FORC algorithm (Algorithm 3).
--
--   **Product-ordering graphs.** A graph is a set of directed edges between products; an edge $(i,j)$ records that product $j$ dominates product $i$.
--
--   **GraphRankSelect$(\eta,G)$.** If $G$ has a directed cycle, it returns an arbitrary ranking. Otherwise, for positions $1,\dots,n$ in turn, it takes a remaining product with no outgoing edge to the remaining set, choosing among those the one with the smallest feedback count $\eta_i$ (ties broken by an unspecified rule), places it, and removes it.
--
--   **FORC.** Let $\delta=1/(n^3T)$ and $L=\lceil\log_2T\rceil$. Each level $\ell\in\{1,\dots,L\}$ keeps feedback counts $\eta^{(\ell)}_i$, click counts (so that the average reward is $r^{(\ell)}_i=\text{clicks}/\eta^{(\ell)}_i$), a graph $G^{(\ell)}$ and an elimination flag. In round $t$:
--   1. **Level.** Draw $\ell_t=\ell$ with probability $2^{-\ell}$ for $\ell\in\{2,\dots,L\}$, and $\ell_t=1$ with probability $1-\sum_{\ell=2}^L2^{-\ell}$.
--   2. **Graph.** Use $G^{(\ell_t)}$ if it is not eliminated, else $G^{(\ell)}$ for the smallest non-eliminated $\ell>\ell_t$.
--   3. **Ranking.** Display $\pi_t=\mathrm{GraphRankSelect}(\eta^{(\ell_t)},G)$.
--   4. **Update.** If $j$ is the last examined position, every product at a position $\le j$ gets one more feedback at level $\ell_t$, and the clicked product one more click.
--   5. **Cross-learning.**
--   $$\hat\eta^{(\ell)}_i=\frac{\sum_{g=1}^{\ell-1}\eta^{(g)}_i}{2^\ell}+\eta^{(\ell)}_i\quad(17),\qquad \hat r^{(\ell)}_i=\frac{\sum_{g=1}^{\ell-1}\eta^{(g)}_ir^{(g)}_i}{2^\ell\hat\eta^{(\ell)}_i}+\frac{\eta^{(\ell)}_i}{\hat\eta^{(\ell)}_i}r^{(\ell)}_i\quad(18).$$
--   6. **Edges.** For every non-eliminated level $\ell$ and products $i,j$ with $\hat\eta^{(\ell)}_i,\hat\eta^{(\ell)}_j>0$ and
--   $$\hat r^{(\ell)}_i+w^{(\ell)}_i<\hat r^{(\ell)}_j-w^{(\ell)}_j\quad(19),\qquad w^{(\ell)}_i=\sqrt{\tfrac32\,\frac{\log(4nT/\delta)}{\hat\eta^{(\ell)}_i}}+\frac{\log(2L/\delta)+4}{\hat\eta^{(\ell)}_i},$$
--   add $(i,j)$ to $G^{(g)}$ for every non-eliminated $g\le\ell$.
--   7. **Elimination.** If some $G^{(\ell)}$ has a cycle, eliminate $G^{(g)}$ for every $g\le\ell$.
--
--   FORC uses neither $F$ nor $\mu$ nor $q$.
--
--   **Formalization Note.** Levels are `Fin L`, 0-based: Lean level $k$ is paper level $k+1$, with probability $2^{-(k+1)}$ and cross-learning weight $1/2^{k+1}$. $L$ is `Nat.clog 2 T` $=\lceil\log_2T\rceil$ (the paper writes $\log_2T$). The average reward is stored as a click count, so Step 8's printed denominator $\eta+1$ in the no-click branch is read as $\eta$ (Step 3 calls $r$ the average reward). (17)–(18) are computed in closed form for every level from the current counts; this equals the incremental update of Step 9. $\hat r=0$ while $\hat\eta=0$ (Step 3). The unspecified choices are parameters: `tb` breaks ties among the products of smallest $\eta$ and `fb` is the "arbitrary ranking" and the ranking used when Step 6 finds no level; both are functions of FORC's past (levels and observations) and the sampled level. GraphRankSelect also returns `fb` if `tb` returns a non-member, which the theorems exclude by hypothesis. Logarithms are natural.
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 19, Algorithm 2; p. 27, Algorithm 3, (17)–(19); pp. 25–26, §6

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model

namespace FakeUserRanking.FORC

open scoped BigOperators

variable {n L : ℕ}

/-! ### GraphRankSelect (Algorithm 2, p. 19)

A product-ordering graph is a finite set of directed edges on products. An edge `(i, k)` records
that product `k` dominates product `i` (p. 16). -/

/-- The graph `G` has a directed cycle. -/
def HasCycle (G : Finset (Fin n × Fin n)) : Prop :=
  ∃ i, Relation.TransGen (fun a b => (a, b) ∈ G) i i

/-- Steps 6–9 of Algorithm 2: fill the next `k` positions from the remaining set `S`. The
candidates are the products of `S` with no outgoing edge into `S`; among those with the smallest
feedback count `η`, the tie-breaking rule `tb` picks one. Returns `none` if the rule's choice is not
such a product (in particular when there is no candidate). -/
def peel (tb : Finset (Fin n) → Fin n) (η : Fin n → ℕ) (G : Finset (Fin n × Fin n)) :
    ℕ → Finset (Fin n) → Option (List (Fin n))
  | 0, _ => some []
  | k + 1, S =>
    let cands := S.filter (fun i => ∀ j ∈ S, (i, j) ∉ G)
    let best := cands.filter (fun i => ∀ j ∈ cands, η i ≤ η j)
    if tb best ∈ best then
      (peel tb η G k (S.erase (tb best))).map (List.cons (tb best))
    else none

/-- The ranking whose position `j` holds the `j`-th entry of a duplicate-free list of all
products. -/
def listPerm (l : List (Fin n)) (nd : l.Nodup) (hall : ∀ x, x ∈ l) (hlen : l.length = n) :
    Equiv.Perm (Fin n) :=
  (finCongr hlen.symm).trans (List.Nodup.getEquivOfForallMemList l nd hall)

open Classical in
/-- `GraphRankSelect(η, G)` (Algorithm 2, p. 19). If `G` has a cycle it returns the "arbitrary
ranking" `fb`; otherwise it places at positions `0, 1, …, n − 1` (paper positions `1, …, n`) the
products chosen by `peel`, ties among the smallest `η` being broken by `tb`. (The final fallback to
`fb` is reached only if `tb` violates its contract.) -/
noncomputable def graphRankSelect (tb : Finset (Fin n) → Fin n) (fb : Equiv.Perm (Fin n))
    (η : Fin n → ℕ) (G : Finset (Fin n × Fin n)) : Equiv.Perm (Fin n) :=
  if HasCycle G then fb else
    match peel tb η G n Finset.univ with
    | some l => if h : l.Nodup ∧ (∀ x, x ∈ l) ∧ l.length = n then listPerm l h.1 h.2.1 h.2.2 else fb
    | none => fb

/-! ### FORC (Algorithm 3, p. 27)

Levels are `Fin L`, 0-based: Lean level `k` is paper level `ℓ = k + 1`. -/

/-- The number of levels `L = ⌈log₂ T⌉` (paper: `L = log₂(T)`). -/
def numLevels (T : ℕ) : ℕ := Nat.clog 2 T

/-- The confidence parameter `δ = 1/(n³T)`. -/
noncomputable def delta (n T : ℕ) : ℝ := 1 / ((n : ℝ) ^ 3 * T)

/-- Step 5: level `ℓ = k + 1 ∈ {2, …, L}` is drawn with probability `2^{−ℓ}`; level `1` (`k = 0`)
gets the remaining probability `1 − ∑_{ℓ=2}^{L} 2^{−ℓ}`. -/
noncomputable def levelW (L : ℕ) (k : Fin L) : ℝ :=
  if (k : ℕ) = 0 then 1 - ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1) else (1 / 2 : ℝ) ^ ((k : ℕ) + 1)

/-- FORC's state at the start of a round: raw feedback counts `η^(ℓ)_i` (`cnt`), click counts
(`clk`, so that the average reward is `r^(ℓ)_i = clk/cnt`), product-ordering graphs `G^(ℓ)`, and
the set of eliminated levels. -/
structure State (n L : ℕ) where
  cnt : Fin L → Fin n → ℕ
  clk : Fin L → Fin n → ℕ
  graph : Fin L → Finset (Fin n × Fin n)
  elim : Finset (Fin L)

/-- Step 3: all counts zero, all graphs empty, nothing eliminated. -/
def State.init : State n L := ⟨fun _ _ => 0, fun _ _ => 0, fun _ => ∅, ∅⟩

/-- The cross-learned feedback count (17): `η̂^(ℓ)_i = ∑_{g<ℓ} η^(g)_i / 2^ℓ + η^(ℓ)_i`. -/
noncomputable def etaHat (st : State n L) (k : Fin L) (i : Fin n) : ℝ :=
  (∑ g ∈ Finset.univ.filter (fun g : Fin L => g < k), (st.cnt g i : ℝ)) / 2 ^ ((k : ℕ) + 1) +
    st.cnt k i

/-- The cross-learned average reward (18) with `η^(g)_i r^(g)_i` = clicks of `i` at level `g`:
`r̂^(ℓ)_i = (∑_{g<ℓ} clk^(g)_i / 2^ℓ + clk^(ℓ)_i) / η̂^(ℓ)_i`, and `0` while `η̂^(ℓ)_i = 0`
(Step 3). -/
noncomputable def rHat (st : State n L) (k : Fin L) (i : Fin n) : ℝ :=
  if etaHat st k i = 0 then 0 else
    ((∑ g ∈ Finset.univ.filter (fun g : Fin L => g < k), (st.clk g i : ℝ)) / 2 ^ ((k : ℕ) + 1) +
      st.clk k i) / etaHat st k i

/-- The window of Step 10: `w^(ℓ)_i = √((3/2) log(4nT/δ) / η̂^(ℓ)_i) + (log(2L/δ) + 4) / η̂^(ℓ)_i`,
with `δ = 1/(n³T)`. It is only used where `η̂^(ℓ)_i > 0`. -/
noncomputable def window (n T : ℕ) (st : State n L) (k : Fin L) (i : Fin n) : ℝ :=
  Real.sqrt ((3 / 2) * Real.log (4 * n * T / delta n T) / etaHat st k i) +
    (Real.log (2 * L / delta n T) + 4) / etaHat st k i

/-- Condition (19) at level `k` for the pair `(i, j)`, including `η̂^(ℓ)_i, η̂^(ℓ)_j > 0`. -/
def edgeCond (n T : ℕ) (st : State n L) (k : Fin L) (i j : Fin n) : Prop :=
  0 < etaHat st k i ∧ 0 < etaHat st k j ∧
    rHat st k i + window n T st k i < rHat st k j - window n T st k j

open Classical in
/-- Steps 8–11 of one round, given the displayed ranking `π`, the sampled level `k` and the
observation `o = (last examined position, clicked?)`.
* Step 8: every product at a position `≤ o.1` gets one more feedback at level `k`; the clicked
  product (if any) one more click.
* Step 9: `η̂`, `r̂` are recomputed in closed form (`etaHat`, `rHat`).
* Step 10: for every non-eliminated level `m` and products `i, j` satisfying (19) at `m`, the edge
  `(i, j)` is added to every non-eliminated level `g ≤ m`.
* Step 11: if some level `m` has a cycle, every level `g ≤ m` is eliminated. -/
noncomputable def State.update (n T : ℕ) (st : State n L) (π : Equiv.Perm (Fin n)) (k : Fin L)
    (o : Obs n) : State n L :=
  let cnt' : Fin L → Fin n → ℕ := fun g i =>
    if g = k ∧ π.symm i ≤ o.1 then st.cnt g i + 1 else st.cnt g i
  let clk' : Fin L → Fin n → ℕ := fun g i =>
    if g = k ∧ o.2 = true ∧ i = π o.1 then st.clk g i + 1 else st.clk g i
  let st1 : State n L := ⟨cnt', clk', st.graph, st.elim⟩
  let graph' : Fin L → Finset (Fin n × Fin n) := fun g =>
    if g ∈ st.elim then st.graph g else
      st.graph g ∪ Finset.univ.filter
        (fun e : Fin n × Fin n => ∃ m : Fin L, g ≤ m ∧ m ∉ st.elim ∧ edgeCond n T st1 m e.1 e.2)
  let elim' : Finset (Fin L) :=
    st.elim ∪ Finset.univ.filter (fun g : Fin L => ∃ m : Fin L, g ≤ m ∧ HasCycle (graph' m))
  ⟨cnt', clk', graph', elim'⟩

/-- Step 6: the graph used in a round with sampled level `k`: `G^(k)` if it is not eliminated,
else the graph of the smallest non-eliminated level above `k`, else `none`. -/
def usedGraph (st : State n L) (k : Fin L) : Option (Finset (Fin n × Fin n)) :=
  if k ∉ st.elim then some (st.graph k) else
    let up := Finset.univ.filter (fun m : Fin L => k < m ∧ m ∉ st.elim)
    if h : up.Nonempty then some (st.graph (up.min' h)) else none

/-- Step 7: `π_t = GraphRankSelect(η^(ℓ_t), G)`. The unspecified choices (ties at the smallest
`η`, the "arbitrary ranking", and Step 6 when no level qualifies) are the parameters `tb` and `fb`,
functions of the algorithm's past `h` and the sampled level. -/
noncomputable def forcRank
    (tb : List (Fin L × Obs n) → Fin L → Finset (Fin n) → Fin n)
    (fb : List (Fin L × Obs n) → Fin L → Equiv.Perm (Fin n))
    (h : List (Fin L × Obs n)) (st : State n L) (k : Fin L) : Equiv.Perm (Fin n) :=
  match usedGraph st k with
  | some G => graphRankSelect (tb h k) (fb h k) (st.cnt k) G
  | none => fb h k

/-- FORC's state after processing its past `h` (levels and observations, oldest first). -/
noncomputable def forcState (n T : ℕ)
    (tb : List (Fin L × Obs n) → Fin L → Finset (Fin n) → Fin n)
    (fb : List (Fin L × Obs n) → Fin L → Equiv.Perm (Fin n))
    (h : List (Fin L × Obs n)) : State n L :=
  (h.foldl (fun (acc : List (Fin L × Obs n) × State n L) (x : Fin L × Obs n) =>
      (acc.1 ++ [x], acc.2.update n T (forcRank tb fb acc.1 acc.2 x.1) x.1 x.2))
    ([], State.init)).2

/-- The FORC algorithm (Algorithm 3, p. 27) for `n` products and horizon `T`, with
`L = ⌈log₂ T⌉` levels. Its inputs are `n`, `T` and the tie-breaking choices only: it does not know
`F`, `μ` or `q`. -/
noncomputable def forc (n T : ℕ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)) :
    Alg n (numLevels T) where
  w := fun _ k => levelW (numLevels T) k
  rank := fun h k => forcRank tb fb h (forcState n T tb fb h) k

end FakeUserRanking.FORC


