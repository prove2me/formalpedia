-- Prove2me | Definitions.Def_TIESched_SatisfiesVanishingHyps
-- name    : TIESched_SatisfiesVanishingHyps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:44:12.651322+00:00
-- url     : https://prove2.me/theorems/ff6e6341-4afc-41ae-a5ca-46550adf0c6a
-- title:
--   Hypotheses of Lemma 5.8 (vanishing via Laplace transform)
-- statement:
--   Let $J$ be a finite job set, $D=m|J|$, and $f_i:[0,\infty)^D\to\mathbb R$ for $i\in[m]$, the coordinates being $p_{ij}$, $(i,j)\in[m]\times J$. The family satisfies the **hypotheses of Lemma 5.8** if:
--
--   0. each $f_i$ is differentiable along each own-coordinate line $t\mapsto f_i(p|_{p_{ij}=t})$, $t\ge0$, whose other coordinates are strictly positive, with a right derivative at $t=0$;
--   1. *Continuity.* each $f_i$ is continuous on $(0,\infty)^D$;
--   2. *Bounded own-coordinate derivatives.* there is $B<\infty$ with $|\partial f_i(p)/\partial p_{ij}|\le B$ for all $p\in(0,\infty)^D$, $i$, $j$;
--   3. *Zero boundary condition.* $p_{ij}=0\Rightarrow f_i(p)=0$ for $p\in[0,\infty)^D$;
--   4. *Differential conservation law.* $\sum_{i=1}^m\partial f_i(p)/\partial p_{ij}=0$ for every $p\in(0,\infty)^D$ and $j\in J$.
--
--   **Formalization Note.** Functions are total on report matrices; only their values on the closed orthant enter. Line differentiability is differentiability within $[0,\infty)$ at every $t\ge0$; the partial derivative at a strictly positive point is the derivative of the line function.
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Lemma 5.8, p.26

import Mathlib

set_option autoImplicit false

namespace TIESched

/-- The report obtained from `p` by setting the single entry `p_ij` to `t` (the own-coordinate line
through `p` in coordinate `(i, j)`; arXiv:2611.05142, §5.4, p.31: "write `s(t)` for the report
obtained by setting `s_ij = t`, with all other coordinates held fixed"). -/
def updEntry {m : ℕ} {J : Finset ℕ} (p : Fin m → J → ℝ) (i : Fin m) (j : J) (t : ℝ) :
    Fin m → J → ℝ :=
  Function.update p i (Function.update (p i) j t)

/-- **The hypotheses of Lemma 5.8** (arXiv:2611.05142, Lemma 5.8, p.26) on a family
`f_i : [0, ∞)^D → ℝ`, `i ∈ [m]`, `D = m|J|`:

* (0) `f_i` is differentiable along each own-coordinate line `t ↦ f_i(p|_{p_ij = t})`, `t ≥ 0`,
  whose other coordinates are strictly positive, with a right derivative at the zero endpoint;
* (1) *Continuity.* each `f_i` is continuous on `(0, ∞)^D`;
* (2) *Bounded own-coordinate derivatives.* there is `B < ∞` with `|∂f_i(p)/∂p_ij| ≤ B` for all
  `p ∈ (0, ∞)^D`, `i ∈ [m]`, `j ∈ J`;
* (3) *Zero boundary condition.* for every `i`, `j ∈ J` and `p ∈ [0, ∞)^D`, `p_ij = 0 ⇒ f_i(p) = 0`;
* (4) *Differential conservation law* (3): for every `p ∈ (0, ∞)^D`, `Σ_{i=1}^m ∂f_i(p)/∂p_ij = 0`
  for every `j ∈ J`.

**Formalization Note.** `[0, ∞)^D` is the space of reports `Fin m → J → ℝ` with nonnegative entries
(the coordinates `(i, j) ∈ [m] × J`); the functions are total and only their values on the closed
orthant enter. Differentiability along the line is `DifferentiableWithinAt` on `[0, ∞)` at every
`t ≥ 0` (an ordinary derivative at `t > 0`, a right derivative at `t = 0`); the partial derivative
`∂f_i(p)/∂p_ij` at a strictly positive `p` is `deriv` of the line function at `p_ij`. -/
def SatisfiesVanishingHyps {m : ℕ} (J : Finset ℕ) (f : Fin m → (Fin m → J → ℝ) → ℝ) : Prop :=
  (∀ (i : Fin m) (j : J) (p : Fin m → J → ℝ),
      (∀ (i' : Fin m) (j' : J), (i', j') ≠ (i, j) → 0 < p i' j') →
      ∀ t : ℝ, 0 ≤ t → DifferentiableWithinAt ℝ (fun t => f i (updEntry p i j t)) (Set.Ici 0) t) ∧
  (∀ i : Fin m, ContinuousOn (f i) {p | ∀ i' j', 0 < p i' j'}) ∧
  (∃ B : ℝ, ∀ (p : Fin m → J → ℝ), (∀ i' j', 0 < p i' j') → ∀ (i : Fin m) (j : J),
      |deriv (fun t => f i (updEntry p i j t)) (p i j)| ≤ B) ∧
  (∀ (i : Fin m) (j : J) (p : Fin m → J → ℝ), (∀ i' j', 0 ≤ p i' j') → p i j = 0 → f i p = 0) ∧
  (∀ (p : Fin m → J → ℝ), (∀ i' j', 0 < p i' j') → ∀ j : J,
      ∑ i, deriv (fun t => f i (updEntry p i j t)) (p i j) = 0)

end TIESched


