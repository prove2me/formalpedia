-- Prove2me | Definitions.Def_DurrettProbability_Donsker
-- name    : DurrettProbability_Donsker
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-19T02:12:53.017618+00:00
-- url     : https://prove2.me/theorems/3080c54b-5b5b-4965-9b80-7315bdafe656
-- title:
--   C[0,1] as a measurable space, the polygonal interpolation of a random walk, and its rescaled path
-- statement:
--   The path-space apparatus of section 8.1 of Durrett, *Probability: Theory and Examples*.
--
--   **The space.** $C[0,1]$ is the continuous real functions on $[0,1]$, carrying the topology of
--   uniform convergence — the compact-open topology, which agrees with the uniform one because the
--   domain is compact — and its Borel $\sigma$-algebra. Both the measurable-space structure and the
--   fact that it is the Borel structure of that topology are supplied here; the ambient library has
--   neither for a space of continuous maps.
--
--   **The interpolation.** For a sequence $X_0,X_1,\dots$ of real random variables and $n\in\mathbb N$,
--   $$S(u)\ =\ \sum_{k<n}X_k\cdot\max\bigl(0,\min(1,u-k)\bigr).$$
--   At an integer $u=m\le n$ this is $X_0+\dots+X_{m-1}$, and on $[m,m+1]$ it interpolates linearly
--   between consecutive partial sums, so it is Durrett's $S(u)$. Written this way it is a finite sum
--   of continuous functions of $u$.
--
--   **The rescaled path.** $W_n(t)=S(nt)/\sqrt n$ for $t\in[0,1]$, an element of $C[0,1]$.
--
--   **Restriction of a path.** For $f:[0,\infty)\to\mathbb R$, its restriction to $[0,1]$ as an
--   element of $C[0,1]$ when $f$ is continuous, and the zero path otherwise; applied to a process
--   $B$ this gives the $C[0,1]$-valued random variable $B(\cdot)$.
--
--   **Formalization Note** Indexing runs from zero, so the partial sum $S_m$ is $X_0+\dots+X_{m-1}$
--   and the interpolation of the first $n$ steps is determined on $[0,n]$; beyond $u=n$ it is
--   constant at $S_n$, which is irrelevant because the rescaled path only evaluates it on $[0,n]$.
--   At $n=0$ the rescaling divides by $\sqrt0=0$, which in the reals is $0$; that value plays no
--   role in a limit along $n\to\infty$.
--
--   The restriction map is total, returning the zero path on a discontinuous argument rather than
--   being undefined. Every statement in this mission assumes each path of the process is continuous,
--   so the branch is never taken; this is a formalization convenience, and it is also what makes
--   "the Brownian path as a random element of $C[0,1]$" a well-formed object at all.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), section 8.1, pp. 391-392 (PDF pp. 399-400): the interpolation "Let N be the nonnegative integers and let S(u) = S_k if u = k in N, linear on [k, k+1] for k in N", and Theorem 8.1.4, "Donsker's theorem. Under the hypotheses of Theorem 8.1.2, S(n.)/sqrt(n) => B(.), i.e., the associated measures on C[0,1] converge weakly." sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Brownian

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace DurrettProbability

/-- `C[0,1]`, the paths of Donsker's theorem, with the uniform topology and its Borel σ-algebra.
Durrett, *Probability: Theory and Examples*, Theorem 8.1.4. -/
abbrev PathSpace : Type := C(Set.Icc (0 : ℝ) 1, ℝ)

noncomputable instance : MeasurableSpace PathSpace := borel _

instance : BorelSpace PathSpace := ⟨rfl⟩

variable {Ω : Type*}

/-- The polygonal interpolation `S(u)` of the first `n` steps of the walk `X`: it agrees with
`S_m = X_1 + ⋯ + X_m` at integer times `m ≤ n` and is linear in between. Writing it as
`∑_{k<n} X_k · clamp(u - k)` makes it a finite sum of continuous functions.
Durrett, *Probability: Theory and Examples*, section 8.1. -/
noncomputable def walkInterp (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, X k ω * max 0 (min 1 (u - k))

/-- The rescaled polygonal path `t ↦ S(nt)/√n` on `[0,1]`, the random element of `C[0,1]` whose
laws Donsker's theorem says converge. Durrett, Theorem 8.1.4. -/
noncomputable def walkPath (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : PathSpace :=
  ⟨fun t => walkInterp X n ω (n * (t : ℝ)) / Real.sqrt n, by unfold walkInterp; fun_prop⟩

open Classical in
/-- The restriction of a path `f : [0,∞) → ℝ` to `[0,1]` as an element of `C[0,1]`, and `0` when
`f` is not continuous. The junk branch is never reached in the statements below, which assume
every path of the process is continuous. -/
noncomputable def toPath (f : ℝ≥0 → ℝ) : PathSpace :=
  if h : Continuous f then
    ⟨fun t => f ⟨t, t.2.1⟩, h.comp (by fun_prop)⟩
  else 0

/-- A Brownian motion viewed as a random element of `C[0,1]`. -/
noncomputable def brownianPath (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : PathSpace := toPath (fun t => B t ω)

end DurrettProbability


