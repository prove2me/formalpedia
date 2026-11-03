-- Prove2me | Definitions.Def_PertComp_primalSet
-- name    : PertComp_primalSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:03.120504+00:00
-- url     : https://prove2.me/theorems/a9dcd927-39cf-4c8f-bf07-9219855ec7e8
-- title:
--   Primal objective (1.2) and its solution set $\mathscr P$
-- statement:
--   In the setting of Problem 1.1 the primal objective is
--   $$x\mapsto(\varphi\circ f)(x)+(g\,\Box\,\ell)(Lx)+h(x),$$
--   and $\mathscr P$ is its set of minimizers, $\operatorname{Argmin}$ of this function.
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, (1.2), p.2

import Mathlib
import Definitions.Def_PerspEpi_postComp
import Definitions.Def_PertComp_infConv
import Definitions.Def_RockafellianRelax_argmin

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, (1.2), p.2: the primal objective
`x ↦ (φ ∘ f)(x) + (g □ ℓ)(Lx) + h(x)` of Problem 1.1.

**Formalization Note.** `φ ∘ f` of (1.1) is the published `PerspEpi.postComp φ f`
(`φ(f(x))` on `dom f`, `+∞` off it); when `x ∈ dom f` but `f(x) ∉ dom φ` its value `φ(f(x))` is
already `+∞`, as (1.1) prescribes. -/
noncomputable def objective {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (φ : ℝ → EReal) (f : X → EReal)
    (g ℓ : Y → EReal) (L : X →L[ℝ] Y) (h : X → EReal) (x : X) : EReal :=
  PerspEpi.postComp φ f x + infConv g ℓ (L x) + h x

/-- Problem 1.1, p.2: `𝒫`, the set of solutions of (1.2), i.e. `Argmin` of the objective
(the published `RockafellianRelax.argmin`: `{x ∈ dom F | F x ≤ inf F}`, minimizers inside the
domain as on p.5). -/
def primalSet {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (φ : ℝ → EReal) (f : X → EReal)
    (g ℓ : Y → EReal) (L : X →L[ℝ] Y) (h : X → EReal) : Set X :=
  RockafellianRelax.argmin (objective φ f g ℓ L h)

end PertComp


