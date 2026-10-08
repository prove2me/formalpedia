-- Prove2me | Definitions.Def_ProjSchedTW_NetPresentValue_Objective
-- name    : ProjSchedTW_NetPresentValue_Objective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:07:35.035957+00:00
-- url     : https://prove2.me/theorems/2b27ebaa-0655-4d3b-95f0-4556ee9b568a
-- title:
--   Definition 3.3.2 and Eq. (3.3.1) — binary-monotone and sum-separable objective functions
-- statement:
--   Let $f:\mathbb R^m_{\ge 0}\to\mathbb R$. For a point $S$ and a direction $z$, the (half-)line
--   $$\ell(S,z)=\{S'\in\mathbb R^m_{\ge0}\mid S'=S+\lambda z,\ \lambda\in\mathbb R\}$$
--   has **binary direction** if $z\in\{0,1\}^m$. The function $f$ is **binary-monotone** if it is monotone (nondecreasing or nonincreasing) on every (half-)line in $\mathbb R^m_{\ge0}$ with binary direction. It is **sum-separable** if $f(S)=\sum_i f_i(S_i)$ for some functions $f_i:\mathbb R\to\mathbb R$.
--
--   Binary-monotone objectives form the fourth class of objective functions of Chapter 3; for them an optimal schedule can be sought among the vertices of the feasible region.
--
--   **Formalization Note** The line is parametrized by $\lambda$, and monotonicity is required on the parameter set $\{\lambda\mid S+\lambda z\ge 0\}$, as `MonotoneOn` or `AntitoneOn`. Sum-separability is required on $\mathbb R^m_{\ge0}$, the domain of $f$ in the book.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 224, Definition 3.3.2 (Eq. (3.3.9)); p. 219, Eq. (3.3.1)

import Mathlib

namespace ProjSchedTW.NetPresentValue

/-- Definition 3.3.2 (p. 224): an objective function `f` on `ℝ^m_{≥0}` is binary-monotone if it is
monotone (nondecreasing or nonincreasing) on each (half-)line
`ℓ(S, z) = {S' ∈ ℝ^m_{≥0} | S' = S + λ z, λ ∈ ℝ}` with binary direction `z ∈ {0, 1}^m`. The line
is parametrized by `λ`, restricted to the parameters for which `S + λ z` lies in `ℝ^m_{≥0}`. -/
def IsBinaryMonotone {m : ℕ} (f : (Fin m → ℝ) → ℝ) : Prop :=
  ∀ S z : Fin m → ℝ, (∀ i, z i = 0 ∨ z i = 1) →
    MonotoneOn (fun t : ℝ => f (S + t • z)) {t : ℝ | ∀ i, 0 ≤ S i + t * z i} ∨
      AntitoneOn (fun t : ℝ => f (S + t • z)) {t : ℝ | ∀ i, 0 ≤ S i + t * z i}

/-- Eq. (3.3.1) (p. 219): an objective function `f` on `ℝ^m_{≥0}` is sum-separable if it has the
form `f(S) = ∑_{i} f_i(S_i)` for some functions `f_i : ℝ → ℝ`. -/
def IsSumSeparable {m : ℕ} (f : (Fin m → ℝ) → ℝ) : Prop :=
  ∃ g : Fin m → ℝ → ℝ, ∀ S : Fin m → ℝ, (∀ i, 0 ≤ S i) → f S = ∑ i, g i (S i)

end ProjSchedTW.NetPresentValue


