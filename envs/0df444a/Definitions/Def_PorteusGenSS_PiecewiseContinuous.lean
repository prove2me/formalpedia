-- Prove2me | Definitions.Def_PorteusGenSS_PiecewiseContinuous
-- name    : PorteusGenSS_PiecewiseContinuous
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:08:10.370239+00:00
-- url     : https://prove2.me/theorems/e20ead1c-aebc-4de3-bb74-8d3bab117964
-- title:
--   Piecewise continuous function on $\mathbb R$
-- statement:
--   A function $f:\mathbb R\to\mathbb R$ is **piecewise continuous** if there is a finite set $A\subset\mathbb R$ such that
--
--   1. $f$ is continuous at every point of $\mathbb R\setminus A$, and
--   2. at every point $a\in A$ both one-sided limits $\lim_{x\uparrow a}f(x)$ and $\lim_{x\downarrow a}f(x)$ exist as real numbers.
--
--   **Formalization Note** The paper defines the notion on a general interval $I$ but uses it only for $I=\mathbb R$, which is fixed here.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §X Summary of Terminology, pp. 425–426

import Mathlib

open Filter Topology

namespace PorteusGenSS

/-- **Piecewise continuous function on ℝ (§X).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §X Summary of Terminology, pp. 425–426: "A function f is piecewise continuous … on an
interval I if there exists a finite subset of I, say A, such that (i) f is continuous … on
I − A = {x; x ∈ I, x ∉ A} and (ii) one-sided limits of f … exist, whenever they are defined,
at points in A."

`PiecewiseContinuous f` says there is a finite set `A ⊆ ℝ` such that `f` is continuous on
`ℝ ∖ A` and, at every point `a ∈ A`, both one-sided limits of `f` exist as real numbers.

**Formalization Note.** Only the interval `I = ℝ` is used in the paper (Definition 2, A5,
Lemmas 3, 6, 9), so `I` is fixed to `ℝ`; at a point of `ℝ` both one-sided limits are defined.
"Exist" means "is a real number" (§X: "We say x exists if x ∈ R"), hence `Tendsto … (𝓝 l)`
with `l : ℝ`. `ℝ ∖ A` is open, so `ContinuousOn` there is continuity at each of its points. -/
def PiecewiseContinuous (f : ℝ → ℝ) : Prop :=
  ∃ A : Finset ℝ, ContinuousOn f (↑A : Set ℝ)ᶜ ∧
    ∀ a ∈ A, (∃ l : ℝ, Tendsto f (𝓝[<] a) (𝓝 l)) ∧ (∃ l : ℝ, Tendsto f (𝓝[>] a) (𝓝 l))

end PorteusGenSS


