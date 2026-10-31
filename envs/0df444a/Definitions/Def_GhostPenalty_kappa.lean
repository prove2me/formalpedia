-- Prove2me | Definitions.Def_GhostPenalty_kappa
-- name    : GhostPenalty_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:10.918993+00:00
-- url     : https://prove2.me/theorems/60445570-73b4-45fe-91b9-538f4200e815
-- title:
--   The enlargement $\kappa(x)$, (8)
-- statement:
--   Let $\tilde g_i(d;x)$ be the convex surrogates of the constraints, $\lambda\in(0,1)$ and $\rho\in(0,\beta)$. For $x\in K$,
--   $$\kappa(x)\triangleq(1-\lambda)\max_i\{g_i(x)_+\}+\lambda\min_d\Big\{\max_i\{\tilde g_i(d;x)_+\}\ \Big|\ \|d\|_\infty\le\rho,\ d\in K-x\Big\}. \tag{8}$$
--   $\kappa(x)\ge 0$ enlarges the surrogate constraints $\tilde g(d;x)\le\kappa(x)e$ so that the subproblem $(\mathrm P_x)$ is always feasible; $\kappa(x)=0$ at feasible $x$.
--
--   **Formalization Note** The minimum is the infimum (`sInf`) of the values over $\rho\mathbb B^n_\infty\cap(K-x)$, with $K-x=\{d:\ x+d\in K\}$; for $x\in K$ the set is nonempty and bounded below by $0$, and the paper shows the minimum is attained. $\kappa$ is only used on $K$.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, (8), pp.6–7

import Mathlib
import Definitions.Def_GhostPenalty_posMax
import Definitions.Def_GhostPenalty_box

namespace GhostPenalty

/-- **The enlargement `κ(x)`** of the surrogate constraints, (8).
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §3, (8), pp.6–7: "the quantity `κ(x)` … is defined, for every `x ∈ K`, as follows:
`κ(x) ≜ (1 − λ) max_i{g_i(x)+} + λ min_d { max_i{g̃_i(d;x)+} | ‖d‖∞ ≤ ρ, d ∈ K − x }`, (8)
with `λ ∈ (0,1)` and `ρ ∈ (0,β)`."

Here `g̃_i(d;x)` (`gt i d x`, first argument the direction `d`, second the base point `x`) is
the convex surrogate of `g_i`.

**Formalization Note.** `λ` is `lam`. `K − x` is `{d | x + d ∈ K}` and `‖d‖∞ ≤ ρ` is
`box n ρ`. The minimum is written as `sInf` of the set of values; for `x ∈ K` that set is
nonempty (it contains the value at `d = 0`) and bounded below by `0`, so `sInf` is the
infimum, which the paper shows is attained (p.7). `κ` is only used at points of `K`, where the
paper defines it. -/
noncomputable def kappa {n m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gt : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (lam ρ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 - lam) * posMax g x +
    lam * sInf ((fun d => posMax (fun i u => gt i u x) d) '' (box n ρ ∩ {d | x + d ∈ K}))

end GhostPenalty


