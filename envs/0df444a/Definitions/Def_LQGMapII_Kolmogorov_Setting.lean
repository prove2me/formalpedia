-- Prove2me | Definitions.Def_LQGMapII_Kolmogorov_Setting
-- name    : LQGMapII_Kolmogorov_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:40:31.540986+00:00
-- url     : https://prove2.me/theorems/539bda97-d3c9-4490-a36f-c8635e26ec26
-- title:
--   §2.3, pp. 30–31 — the cube [0,1]^d, the dyadic grid 𝒟_k and its adjacent pairs 𝒟̃_k
-- statement:
--   This file fixes the index set and the dyadic objects of the quantitative Kolmogorov–Čentsov criterion (§2.3 of Miller–Sheffield).
--
--   1. **The cube.** For $d \in \mathbb N$, $[0,1]^d$ is the set of points $u = (u_1,\dots,u_d) \in \mathbb R^d$ with $0 \le u_i \le 1$ for every $i$, equipped with the **Euclidean** distance $|u - v| = \big(\sum_i (u_i - v_i)^2\big)^{1/2}$.
--   2. **The dyadic grid.** For $k \in \mathbb N$ (with $k = 0$ allowed),
--   $$
--   \mathcal D_k = \{\, x \in [0,1]^d : x_i \in 2^{-k}\mathbb Z \text{ for every } i \,\},
--   $$
--   the points of the cube whose coordinates are integer multiples of $2^{-k}$.
--   3. **Adjacent pairs.** Two points $u, v \in \mathcal D_k$ are *adjacent at level $k$* if they agree in every coordinate but one, say $i$, and $|u_i - v_i| = 2^{-k}$; then $|u - v| = 2^{-k}$. The set $\widetilde{\mathcal D}_k$ of the paper consists of the unordered pairs $\{u, v\}$ of adjacent points of $\mathcal D_k$.
--
--   These are the objects over which the chaining argument of the proof of Proposition 2.3 runs: (2.10)–(2.12) bound the increments of a random field along $\widetilde{\mathcal D}_k$, and the closing claim of the proof transfers that bound to all points of $\bigcup_k \mathcal D_k$.
--
--   **Formalization Note** The cube is the subtype of `EuclideanSpace ℝ (Fin d)` cut out by $0 \le u_i \le 1$, so its distance is Euclidean (Mathlib's `Fin d → ℝ` would carry the sup norm). The predicate `IsAdjacentPair d k u v` is the ordered version of $\{u,v\} \in \widetilde{\mathcal D}_k$; it is symmetric in $u, v$, so each unordered pair is counted twice, a factor 2 that every existential constant built on it absorbs. The level $k$ ranges over Lean's $\mathbb N$, which includes $k = 0$ ($\mathcal D_0 = \{0,1\}^d$).
-- source:
--   Miller, Sheffield, Liouville quantum gravity and the Brownian map II, Ann. Probab. (2021), DOI 10.1214/21-AOP1506, accepted manuscript, §2.3: Proposition 2.3, p. 30 (index set [0,1]^d); proof of Proposition 2.3, p. 31, first paragraph (definition of 𝒟_k and 𝒟̃_k)

import Mathlib

namespace LQGMapII.Kolmogorov

/-- The cube `[0,1]^d` with the Euclidean distance (Miller–Sheffield, §2.3, pp. 30–31). -/
abbrev Cube (d : ℕ) : Type := {u : EuclideanSpace ℝ (Fin d) // ∀ i, u i ∈ Set.Icc (0 : ℝ) 1}

/-- `𝒟_k`: the points of the cube whose coordinates are integer multiples of `2^{-k}` (p. 31). -/
def dyadicGrid (d k : ℕ) : Set (Cube d) :=
  {u | ∀ i, ∃ m : ℤ, (u : EuclideanSpace ℝ (Fin d)) i = (m : ℝ) / 2 ^ k}

/-- `(u, v)` is an ordered representative of a pair `{u, v} ∈ 𝒟̃_k` (p. 31): both points lie in
`𝒟_k`, they agree off one coordinate `i`, and `|u_i - v_i| = 2^{-k}` (so `|u - v| = 2^{-k}`). -/
def IsAdjacentPair (d k : ℕ) (u v : Cube d) : Prop :=
  u ∈ dyadicGrid d k ∧ v ∈ dyadicGrid d k ∧
    ∃ i, (∀ j, j ≠ i → (u : EuclideanSpace ℝ (Fin d)) j = (v : EuclideanSpace ℝ (Fin d)) j) ∧
      |(u : EuclideanSpace ℝ (Fin d)) i - (v : EuclideanSpace ℝ (Fin d)) i| = (2 : ℝ)⁻¹ ^ k

end LQGMapII.Kolmogorov


