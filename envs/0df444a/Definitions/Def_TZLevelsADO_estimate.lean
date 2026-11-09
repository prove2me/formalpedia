-- Prove2me | Definitions.Def_TZLevelsADO_estimate
-- name    : TZLevelsADO_estimate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:27.955888+00:00
-- url     : https://prove2.me/theorems/e4cbd77a-089d-4db3-b61a-5a6e6aeb57bf
-- title:
--   Algorithm 2: the table $H$ and the distance estimate $\hat d(u,v)$
-- statement:
--   Fix a graph, a Thorup–Zwick hierarchy and a pivot choice. Algorithm 2 of the paper first fills a table $H$ on pairs of vertices: for every oriented edge $(x, y)$ of every edge $e$ (both orientations), every level $i \in [k]$ and every $z \in B(y)$, it lowers both $H(p_i(x), z)$ and $H(z, p_i(x))$ to
--   $$h_i(x) + \ell(e) + d(y, z).$$
--   Unset entries are $\infty$, and $H(w, w) = 0$ for every $w$. Thus $H(a, b)$ is $0$ if $a = b$, and otherwise the least such value over all $(x, y)$, $i$, $z$ with $\{a, b\} = \{p_i(x), z\}$ (or $\infty$ if there is none).
--
--   For a pair $\langle u, v \rangle$ the algorithm returns the **estimate**
--   $$\hat d(u, v) = \min\Big( \min_{i \in [k],\, w \in B(v)} \big[d(u, p_i(u)) + H(p_i(u), w) + d(w, v)\big],\ \min_{z \in B(u),\, j \in [k]} \big[d(u, z) + H(z, p_j(v)) + d(p_j(v), v)\big] \Big).$$
--
--   This is the oracle's query procedure; the mission's stretch milestones bound this estimate, and Theorem 1 asks for a machine implementation of it within the stated time and space.
--
--   **Formalization Note** $H$ and $\hat d$ take values in $\mathbb R \cup \{\infty\}$ (`WithTop ℝ`) and are finite minima, so no junk value enters. Every update writes the same value to both entries, so the order of updates in Algorithm 2 does not matter.
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), §5.2, Algorithm 2, p.19 (PDF p.20), prose and footnote 7, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_TZLevelsADO_Hierarchy

namespace TZLevelsADO

/-!
# Algorithm 2: the table `H` and the estimate `d̂(u, v)`

S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), §5.2, Algorithm 2, p.19 (PDF p.20), with the prose on p.18 (PDF p.19):

```
3 foreach oriented edge (x, y) do
4   for i ∈ [k] and z ∈ B(y) do
5     H(p_i(x), z), H(z, p_i(x)) ← min{H(p_i(x), z), h_i(x) + ℓ(x, y) + d(y, z)};
6 foreach ⟨u, v⟩ ∈ I do
7   for i ∈ [k] and w ∈ B(v) do
8     d̂(u, v) ← min{d̂(u, v), d(u, p_i(u)) + H(p_i(u), w) + d(w, v)};
9   for z ∈ B(u) and j ∈ [k] do
10    d̂(u, v) ← min{d̂(u, v), d(u, z) + H(z, p_j(v)) + d(p_j(v), v)};
```

and footnote 7 (p.18): "As in Algorithm 1, H and d̂ return ∞ on unset pairs, and H(w, w) = 0 for every
w."

**Formalization Note.**
* `Htab A P a b` is the value of the table after lines 3–5, as a function into `WithTop ℝ`: `0` if
  `a = b` (footnote 7); otherwise the least value `h_i(x) + ℓ(e) + d(y, z)` over every oriented edge
  `(x, y)` of an edge `e` (both orientations of every edge), every level `i ∈ [k]` and every `z ∈ B(y)`
  with `(a, b) = (p_i(x), z)` or `(a, b) = (z, p_i(x))`; and `⊤ = ∞` if there is none. Every line-5
  update writes the same value to both entries, so the order of the updates does not matter and the
  table is symmetric.
* `estimate A P u v` is `d̂(u, v)` after lines 7–10: the least of the two query families, `⊤` if both
  are empty.
* Both are finite minima (`Finset.inf`), so no junk value of an infinite infimum enters.
* The estimate depends on the hierarchy and on the pivot choice; statements quantify over both.
-/

/-- Algorithm 2, lines 3–5 and footnote 7: the table `H(a, b)`. -/
noncomputable def Htab {G : Graph} {k : ℕ} {A : Hierarchy G k} (P : PivotChoice A)
    (a b : Fin G.n) : WithTop ℝ :=
  if a = b then 0 else
    (Finset.univ : Finset ((Fin G.m × Bool) × Fin k × Fin G.n)).inf fun q =>
      if q.2.2 ∈ bunch A (G.head q.1) ∧
          ((a = P.p q.2.1 (G.tail q.1) ∧ b = q.2.2) ∨ (a = q.2.2 ∧ b = P.p q.2.1 (G.tail q.1)))
      then (((P.h q.2.1 (G.tail q.1) + G.wt q.1.1 + dist G (G.head q.1) q.2.2 : ℝ)) : WithTop ℝ)
      else ⊤

/-- Algorithm 2, lines 7–10: the estimate `d̂(u, v)`. -/
noncomputable def estimate {G : Graph} {k : ℕ} {A : Hierarchy G k} (P : PivotChoice A)
    (u v : Fin G.n) : WithTop ℝ :=
  min
    ((Finset.univ : Finset (Fin k)).inf fun i => (bunch A v).inf fun w =>
      ((dist G u (P.p i u) : ℝ) : WithTop ℝ) + Htab P (P.p i u) w + ((dist G w v : ℝ) : WithTop ℝ))
    ((bunch A u).inf fun z => (Finset.univ : Finset (Fin k)).inf fun j =>
      ((dist G u z : ℝ) : WithTop ℝ) + Htab P z (P.p j v) + ((dist G (P.p j v) v : ℝ) : WithTop ℝ))

end TZLevelsADO


