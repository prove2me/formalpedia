-- Prove2me | Definitions.Def_ClassicalSchurRamsey
-- name    : ClassicalSchurRamsey
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-26T21:18:03.301987+00:00
-- url     : https://prove2.me/theorems/013342a7-1141-4fc9-b329-ce01140ea97a
-- title:
--   Monochromatic triangles and the pigeonhole bound $\rho(k)$ for the Ramsey numbers $R_k(3)$
-- statement:
--   This bundle states the monochromatic-triangle property of Ramsey theory in the form used with block sums, together with the classical pigeonhole upper bound for the multicolour Ramsey numbers of triangles.
--
--   1. For $k, N \in \mathbb{N}$, the property $\mathrm{TR}(k, N)$ (Lean `TriangleRamsey k N`) states: for every finite set $V \subseteq \mathbb{N}$ with $|V| \ge N$, every set $K \subseteq \mathbb{N}$ of at most $k$ colours, and every colouring $c$ that gives each pair $x < y$ of elements of $V$ a colour $c(x, y) \in K$, there is a monochromatic triangle, that is, there are $x < y < z$ in $V$ with $c(x, y) = c(y, z) = c(x, z)$.
--   2. The function $\rho : \mathbb{N} \to \mathbb{N}$ (Lean `ramseyBound`) is defined by the recursion
--
--   $$
--   \rho(0) = 2, \qquad \rho(k+1) = (k+1)\,\bigl(\rho(k) - 1\bigr) + 2 \quad (k \ge 0).
--   $$
--
--   Its first values are $\rho(0), \rho(1), \dots, \rho(5) = 2, 3, 6, 17, 66, 327$.
--
--   Write $R_k(3)$ for the least $N$ such that every colouring of the edges of the complete graph $K_N$ with $k$ colours has a monochromatic triangle. For $k \ge 1$, $\mathrm{TR}(k, N)$ holds when $N \ge R_k(3)$ and fails when $N < R_k(3)$; so it expresses the inequality $R_k(3) \le N$ without naming the Ramsey number. The recursion for $\rho$ is the classical recursive bound $R_{k+1}(3) \le (k+1)(R_k(3) - 1) + 2$, taken with equality at every step and started from $\rho(0) = 2$.
--
--   For $k = 1, 2, 3$ the values $3, 6, 17$ are the Ramsey numbers $R_1(3), R_2(3), R_3(3)$. For $k = 4$ the value $66$ is larger than the upper bound $R_4(3) \le 62$ quoted by Eliahou and Revuelta. In the formalization of $L(4) = 16$ cited in the source field, $\rho(k)$ takes the place of $R_k(3)$ in Theorem 4.1 and Proposition 5.3 of Eliahou and Revuelta; this gives the upper bound $L(4) \le 16$, which is attained, but only $L(5) \le 65$. A theorem that needs a smaller bound on $R_k(3)$ can take $\mathrm{TR}(k, N)$ as a hypothesis, with $N$ smaller than $\rho(k)$.
--
--   **Formalization Note** Colours are natural numbers, and the colouring is a function $c : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ of which only the values $c(x, y)$ for $x < y$ in $V$ are constrained. The vertex set is any finite set of natural numbers, ordered by $<$, in place of the vertex set of $K_N$. In $\rho(k) - 1$ the subtraction is truncated subtraction on $\mathbb{N}$; it is ordinary subtraction because $\rho(k) \ge 2$.
-- source:
--   S. Eliahou and M. P. Revuelta, "The Schur degree of additive sets", Discrete Math. 344(5) (2021) 112332, https://doi.org/10.1016/j.disc.2021.112332 (preprint arXiv:2006.01502), §5, inequality (10) (the recursive bound R_n(3) ≤ n(R_{n−1}(3) − 1) + 2, quoted from Greenwood and Gleason 1955, reference [8], Theorem 6, p. 6); the Ramsey numbers R_n(3) = R(3, …, 3) as in the abstract and §1. A. McKenna, "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49", Zenodo (2026), https://doi.org/10.5281/zenodo.22987189, §7 (the pigeonhole bound ρ(k), ρ(0) = 2, ρ(k+1) = (k+1)(ρ(k) − 1) + 2, in place of R_k(3)). Lean source: https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Ramsey.lean#L25-L36 (release v1.0.1, doi:10.5281/zenodo.22987688).

-- Generated from lean/ClassicalSchur/Ramsey.lean by skeleton
-- subtraction: every declaration except the def-material below is deleted,
-- and project imports are rewritten to their platform Definitions bundles.
import Mathlib

namespace ClassicalSchur



/-- Every colouring with at most `k` colours of the pairs `x < y` of a set
of at least `N` naturals has a monochromatic triangle. -/
def TriangleRamsey (k N : ℕ) : Prop :=
  ∀ (V K : Finset ℕ) (c : ℕ → ℕ → ℕ), K.card ≤ k → N ≤ V.card →
    (∀ x ∈ V, ∀ y ∈ V, x < y → c x y ∈ K) →
    ∃ x ∈ V, ∃ y ∈ V, ∃ z ∈ V, x < y ∧ y < z ∧ c x y = c y z ∧ c x y = c x z

/-- The pigeonhole upper bound for the triangle Ramsey numbers:
`2, 3, 6, 17, 66, …`. -/
def ramseyBound : ℕ → ℕ
  | 0 => 2
  | k + 1 => (k + 1) * (ramseyBound k - 1) + 2

end ClassicalSchur


