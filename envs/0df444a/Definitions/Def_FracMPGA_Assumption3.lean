-- Prove2me | Definitions.Def_FracMPGA_Assumption3
-- name    : FracMPGA_Assumption3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:41:44.542979+00:00
-- url     : https://prove2.me/theorems/ea75404f-5f0d-4abe-9d44-37e0c1faab98
-- title:
--   Assumption 3: $f$ locally Lipschitz on $\mathcal X$
-- statement:
--   **Assumption 3.** The function $f$ is locally Lipschitz continuous on $\mathcal X=\{x:F(x)\le F(x^{(0)})\}$: every $\bar x\in\mathcal X$ has a neighbourhood $U$ and a constant $L$ with
--   $$
--   |f(u)-f(v)|\le L\|u-v\|_2\qquad\text{for all } u,v\in U\cap\mathcal X.
--   $$
--
--   It is used for the Lipschitz-type estimate of $Q$ along the iterates (Lemma 6.2).
--
--   **Formalization Note** Lipschitz continuity is relative to $\mathcal X$. The paper states that the assumption holds automatically for its sparse-recovery models (2) and (3), whose $f$ contains the indicator of a box and is $+\infty$ just outside it; Lipschitz continuity on full neighbourhoods would exclude them.
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §6.1, p.26, Assumption 3

import Mathlib
import Definitions.Def_FracMPGA_setS

open Topology

namespace FracMPGA

/-- **Assumption 3** of Zhou, Zhang, Li, arXiv:2311.00957v2, p.26: "The function `f` is locally
Lipschitz continuous on `X`", with `X = {x : F(x) ≤ F(x⁽⁰⁾)}` the level set of Assumption 2.

**Formalization Note** Read as local Lipschitz continuity *relative to* `X`: every `x̄ ∈ X` has a
neighbourhood `U` and a constant `L` with `|f(u) − f(v)| ≤ L‖u − v‖₂` for `u, v ∈ U ∩ X`. The
paper says the assumption holds "automatically" for its models (2) and (3) (p.29), whose `f`
contains the indicator of a box and so is `+∞` just outside it; Lipschitz continuity on full
neighbourhoods would exclude them. The absolute value is written as one inequality in `EReal`
for all ordered pairs `u, v`. -/
def Assumption3 {n N : ℕ} (P : Problem n N) (x0 : Vec n) : Prop :=
  ∀ xbar ∈ P.levelX x0, ∃ U ∈ 𝓝 xbar, ∃ L : ℝ, ∀ u ∈ U ∩ P.levelX x0, ∀ v ∈ U ∩ P.levelX x0,
    P.f u ≤ P.f v + ((L * ‖u - v‖ : ℝ) : EReal)

end FracMPGA


