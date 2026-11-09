-- Prove2me | Definitions.Def_RGGThreshold_agreeCol
-- name    : RGGThreshold_agreeCol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:58:51.222188+00:00
-- url     : https://prove2.me/theorems/dbd20b1d-1157-4484-bf73-8f90a1e7eb41
-- title:
--   Agreement events: edges at vertex $s$, the induced graph on $\{s+1,\dots,n\}$, and the new column
-- statement:
--   Let $G$ be the random geometric graph of a configuration $x_1,\dots,x_n\in\mathbb S^{d-1}$ (distinct $i,j$ adjacent when $\langle x_i,x_j\rangle\ge\tau$) and $H$ a fixed graph on $[n]$.
--
--   1. The **column agreement event** at vertex $s$: $si\in E(G)\iff si\in E(H)$ for all $i\in\{s+1,\dots,n\}$.
--   2. The **tail agreement event** $G|_{[s+1,n]}=H_s$: $G$ and $H$ induce the same graph on $\{s+1,\dots,n\}$.
--   3. The **new column** $(v_i(s))_{s<i\le n}$ of Gram–Schmidt coordinates.
--
--   These are the events and random vector of the vertex-exposure induction (Lemmas 5.1 and 5.2).
--
--   **Formalization Note** The paper's vertex $s$ in (1) and (3) is the 0-based vertex $v$; in (2) $s$ is the paper's index and $\{s+1,\dots,n\}$ is $\{i: s\le i\}$. The column's entries $i\le v$ are set to $0$, matching the placeholder of Setup (⋆).
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Lemma 5.1, p.14 (PDF p.16); Lemma 5.2, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_RGGDetect_rggLaw
import Definitions.Def_RGGThreshold_gsCoord

namespace RGGThreshold

/-- The event that the random geometric graph `G` agrees with `H` on the edges `si`,
`i ∈ {s+1, …, n}` (Hunter–Milojević–Sudakov, arXiv:2607.22480, held version, sha256 1a398ef9…,
Lemma 5.2 (a), p.15 (PDF p.17)).

**Formalization Note** The paper's vertex `s` is the 0-based vertex `v`, so `{s+1, …, n}` is
`{i | v < i}`. `G` is `RGGDetect.rggGraph τ x`, which joins `i ≠ j` when `τ ≤ ⟨x_i, x_j⟩`. -/
def agreeCol {n : ℕ} (d : ℕ) (τ : ℝ) (H : SimpleGraph (Fin n)) (v : Fin n) :
    Set (RGGDetect.Config n d) :=
  {x | ∀ i : Fin n, v < i → ((RGGDetect.rggGraph τ x).Adj v i ↔ H.Adj v i)}

/-- The event `G(n, d, p)|_{[s+1,n]} = H_s`: the random geometric graph and `H` induce the same
graph on the vertex set `{s+1, …, n}` (arXiv:2607.22480, held version, Lemma 5.1, p.14
(PDF p.16)).

**Formalization Note** `s` is the paper's index (`0 ≤ s ≤ n-1`), and `{s+1, …, n}` is the 0-based
`{i | s ≤ i}`. -/
def agreeTail {n : ℕ} (d : ℕ) (τ : ℝ) (H : SimpleGraph (Fin n)) (s : ℕ) :
    Set (RGGDetect.Config n d) :=
  {x | ∀ i j : Fin n, s ≤ i.val → s ≤ j.val → ((RGGDetect.rggGraph τ x).Adj i j ↔ H.Adj i j)}

/-- The new column `(v_i(s))_{s<i≤n}` of the Gram–Schmidt coordinates, for the paper's
coordinate `s` (arXiv:2607.22480, held version, Lemma 5.2 (b), p.15 (PDF p.17)).

**Formalization Note** The paper's `s` is `v + 1` for the 0-based vertex `v`, so `v_i(s)` is
`gsCoord x i v`. Entries `i ≤ v` are set to `0`, matching the placeholder of `setupStar`. -/
noncomputable def colMap {n d : ℕ} (v : Fin n) (x : RGGDetect.Config n d) : Fin n → ℝ :=
  fun i => if v < i then gsCoord x i v else 0

end RGGThreshold


