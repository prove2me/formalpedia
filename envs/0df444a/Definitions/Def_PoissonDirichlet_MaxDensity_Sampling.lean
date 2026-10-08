-- Prove2me | Definitions.Def_PoissonDirichlet_MaxDensity_Sampling
-- name    : PoissonDirichlet_MaxDensity_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:15.629913+00:00
-- url     : https://prove2.me/theorems/bcd68362-b869-447e-8c57-87729a8355d9
-- title:
--   (113) and §6.1, p. 881 — a sample N from (V_n), deletion of V_N, insertion of v
-- statement:
--   Let $(V_n)$ be a random sequence of frequencies. A **sample** from $(V_n)$, (113), is a random index $N$ with
--   $$P(N = n \mid V_1, V_2, \dots) = V_n \qquad (n = 1, 2, \dots).$$
--   Then $V_N$ is a size-biased pick from $(V_n)$.
--
--   **Deletion.** Given a sequence $(v_n)$ and an index $N$, the sequence obtained by deleting $v_N$ is
--   $$v'_n = v_n\,1(n < N) + v_{n+1}\,1(n \ge N).$$
--
--   **Insertion.** Given a sequence $(v'_n)$ and a number $v > \inf_n v'_n$, let $N - 1 = \sum_{n \ge 1} 1(v'_n > v)$ be the number of terms of $v'$ that strictly exceed $v$. The sequence obtained by inserting $v$ is
--   $$v_n = v'_n\,1(n < N) + v\,1(n = N) + v'_{n-1}\,1(n > N),$$
--   so that $v_N = v$.
--
--   Deletion and insertion are the operations of Propositions 34 and 35, which describe $\mathrm{PD}(\alpha,\theta)$ through a size-biased deletion followed by renormalisation, and the converse.
--
--   **Formalization Note.** Indices are 0-based throughout (`N ω = k` is the paper's $N = k+1$); the deletion formula is unchanged by the shift. The page prints the last term of the insertion formula as $v'_{n+1}1(n > N)$, which would lose $v'_N$; inserting at place $N$ shifts the tail to the right, so the definition uses $v'_{n-1}$. The insertion index counts with `Set.ncard`, which is $0$ on an infinite set; under the page's assumption $v > \inf_n v'_n$ for a decreasing $v'$ the set is finite. `IsSample` requires $V$ and $N$ to be measurable.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 881, (113) and §6.1 (deletion and insertion operations)

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.MaxDensity

/-- A sample from `(Vₙ)`, (113), p. 881: a random index `N` with `P(N = n | V₁, V₂, …) = Vₙ`.
0-based: `N ω = k` means the paper's `N = k + 1`, and `V ω k` is `V_{k+1}`. `V` and `N` are
random variables (measurable). -/
def IsSample {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (V : Ω → ℕ → ℝ) (N : Ω → ℕ) :
    Prop :=
  Measurable V ∧ Measurable N ∧
    ∀ k : ℕ, P[(fun ω => if N ω = k then (1 : ℝ) else 0) | MeasurableSpace.comap V inferInstance]
      =ᵐ[P] fun ω => V ω k

/-- Deletion of `v_N`, §6.1, p. 881: `v'ₙ = vₙ 1(n < N) + v_{n+1} 1(n ≥ N)`. With 0-based `n`
and `N` the formula is the same. -/
def deleteAt (v : ℕ → ℝ) (N : ℕ) (n : ℕ) : ℝ := if n < N then v n else v (n + 1)

/-- The insertion index, §6.1, p. 881, 0-based: the number of terms of `v'` that strictly
exceed `v` (the paper's `N - 1 = ∑ₙ 1(v'ₙ > v)`). The page assumes `v > infₙ v'ₙ` for a
decreasing `v'`, so the set is finite; `Set.ncard` is `0` on an infinite set, which happens
only outside that assumption. -/
noncomputable def insertIndex (v' : ℕ → ℝ) (v : ℝ) : ℕ := {n : ℕ | v < v' n}.ncard

/-- Insertion of `v` into `v'`, §6.1, p. 881, 0-based with `N = insertIndex v' v`:
`vₙ = v'ₙ 1(n < N) + v 1(n = N) + v'_{n-1} 1(n > N)`. The page prints `v'_{n+1}` in the last
term; inserting `v` at place `N` shifts the tail to the right, so the index is `n - 1`
(with `v'_{n+1}` the term `v'_N` would be lost). -/
noncomputable def insertAt (v' : ℕ → ℝ) (v : ℝ) (n : ℕ) : ℝ :=
  if n < insertIndex v' v then v' n
  else if n = insertIndex v' v then v
  else v' (n - 1)

end PoissonDirichlet.MaxDensity


