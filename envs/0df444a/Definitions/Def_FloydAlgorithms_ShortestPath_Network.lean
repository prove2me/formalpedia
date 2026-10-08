-- Prove2me | Definitions.Def_FloydAlgorithms_ShortestPath_Network
-- name    : FloydAlgorithms_ShortestPath_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:48:49.041181+00:00
-- url     : https://prove2.me/theorems/63dfeea1-24c8-4b00-83e3-e1cc2df919af
-- title:
--   Directed network, simple paths, path lengths, and absence of negative cycles
-- statement:
--   Let the network have $n$ numbered points. For each ordered pair $(a,b)$, the direct-link length $w(a,b)$ is a real number, or $\infty$ if no direct link exists. Diagonal entries are unrestricted.
--
--   A path of $L\ge1$ links from $i$ to $j$ is a sequence $p_0=i,p_1,\ldots,p_L=j$ in which $p_0,\ldots,p_{L-1}$ are distinct and $p_1,\ldots,p_L$ are distinct. When $i=j$, this is a simple closed path through $i$. Its length is
--
--   $$
--   \ell_w(p)=\sum_{t=0}^{L-1}w(p_t,p_{t+1}).
--   $$
--
--   The shortest path length $d_w(i,j)$ is the minimum of these lengths over paths with at most $n$ links, or $\infty$ if there is no finite-length path. The condition of no negative cycle means that every simple closed path has nonnegative length.
--
--   These definitions provide an independent path-based benchmark for the procedure, including its diagonal entries and missing links.
--
--   **Formalization Note** Points are `Fin n` indexed from zero; $\infty$ is `⊤ : WithTop ℝ`. A path from a point to itself must use at least one link, since Floyd's procedure does not initialize the diagonal to zero. The minimum is taken over a finite set; no value for an unbounded infimum is needed.
-- source:
--   Floyd, Algorithm 97: Shortest Path, Communications of the ACM 5(6) (1962), p. 345, comment of Algorithm 97; https://doi.org/10.1145/367766.368168

import Mathlib

namespace FloydAlgorithms.ShortestPath

/-- The directed link lengths in Algorithm 97. `⊤` denotes an absent link. -/
abbrev LengthMatrix (n : ℕ) := Fin n → Fin n → WithTop ℝ

/-- A path with at least one link and no repeated vertices except that its endpoints
may coincide. In the latter case this is a simple closed path. -/
def IsPath {n : ℕ} (i j : Fin n) (L : ℕ) (p : Fin (L + 1) → Fin n) : Prop :=
  1 ≤ L ∧ p 0 = i ∧ p (Fin.last L) = j ∧
    (∀ a b : Fin L, a ≠ b → p a.castSucc ≠ p b.castSucc) ∧
    (∀ a b : Fin L, a ≠ b → p a.succ ≠ p b.succ)

/-- The sum of the direct-link lengths along a path. Any missing link makes
the length `⊤`. -/
def pathLength {n L : ℕ} (w : LengthMatrix n)
    (p : Fin (L + 1) → Fin n) : WithTop ℝ :=
  ∑ t : Fin L, w (p t.castSucc) (p t.succ)

/-- The minimum length of a simple path from `i` to `j`. The infimum is over
a finite set, and an empty set has value `⊤`. -/
noncomputable def shortestLength {n : ℕ} (w : LengthMatrix n)
    (i j : Fin n) : WithTop ℝ := by
  classical
  exact (Finset.range (n + 1)).inf (fun L =>
    (Finset.univ.filter (fun p : Fin (L + 1) → Fin n => IsPath i j L p)).inf
      (fun p => pathLength w p))

/-- No simple closed path has negative length. A missing-link path has
length `⊤` and automatically satisfies the inequality. -/
def NoNegativeCycle {n : ℕ} (w : LengthMatrix n) : Prop :=
  ∀ (i : Fin n) (L : ℕ) (p : Fin (L + 1) → Fin n),
    IsPath i i L p → 0 ≤ pathLength w p

end FloydAlgorithms.ShortestPath


