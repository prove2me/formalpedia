-- Prove2me | Definitions.Def_DetComplexityPowerSum_Quadratic_PolarSlice
-- name    : DetComplexityPowerSum_Quadratic_PolarSlice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:24:23.297014+00:00
-- url     : https://prove2.me/theorems/4f5b133a-83d9-4a82-9248-d42de3cd2217
-- title:
--   Definition 2.2 — the power sum $F_n$ and the polar slice $S$
-- statement:
--   Let $n\ge 2$ and let
--   $$F_n=\sum_{i=1}^n x_i^n\in\mathbb C[x_1,\dots,x_n]$$
--   be the power sum, whose number of variables and degree are both $n$. The **polar slice** $S\subseteq\mathbb C^n$ is the set of all solutions of the system
--
--   1. $F_n(x)=0$,
--   2. $x_{n-1}=1$,
--   3. $\dfrac{\partial F_n}{\partial x_i}=\dfrac{\partial F_n}{\partial x_{n-1}}$ for every $i\le n-2$.
--
--   The set $S$ depends only on $n$. It is the original system whose size is compared with the proxy systems built from a determinantal representation.
--
--   **Formalization Note** Coordinates are `Fin n`, so $x_{n-1}$ is the index $n-2$ (predicate `IsPenultimate`) and the range $i\le n-2$ is the indices $0,\dots,n-3$ (predicate `IsEarly`). For $n\ge 2$ exactly one index is penultimate, and for $n=2$ no index is early, so the third group is empty. The partial derivatives are the formal derivatives `MvPolynomial.pderiv` evaluated at the point. The definition is total in $n$; every conclusion about $S$ uses $n\ge 2$, the standing domain of §3.
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 4, Definition 2.2

import Mathlib

namespace DetComplexityPowerSum.Quadratic

open MvPolynomial

/-- The power sum `F_n = ∑ᵢ Xᵢⁿ` in `ℂ[X₁, …, Xₙ]`: `n` variables, every exponent equal to `n`. -/
noncomputable def powerSum (n : ℕ) : MvPolynomial (Fin n) ℂ :=
  ∑ i : Fin n, X i ^ n

/-- The source's coordinate `x_{n-1}`. Source coordinates are 1-based and `Fin n` is 0-based, so
`x_{n-1}` is the index `n - 2`. For `n ≥ 2` exactly one index satisfies this. -/
def IsPenultimate {n : ℕ} (i : Fin n) : Prop :=
  i.val + 2 = n

/-- The source's range `i ≤ n - 2` of 1-based coordinates, that is the 0-based indices
`0, …, n - 3`. The final coordinate `x_n` and the coordinate `x_{n-1}` are not in this range. -/
def IsEarly {n : ℕ} (i : Fin n) : Prop :=
  i.val + 2 < n

/-- Definition 2.2: the set `S ⊆ ℂⁿ` of all solutions of `F(x) = 0`, `x_{n-1} = 1`, and
`∂F/∂xᵢ = ∂F/∂x_{n-1}` for every `i ≤ n - 2`. The derivatives are formal partial derivatives of
the polynomial `F`, evaluated at the point. -/
def polarSlice (n : ℕ) : Set (Fin n → ℂ) :=
  {a | eval a (powerSum n) = 0 ∧
    (∀ j : Fin n, IsPenultimate j → a j = 1) ∧
    ∀ i j : Fin n, IsEarly i → IsPenultimate j →
      eval a (pderiv i (powerSum n)) = eval a (pderiv j (powerSum n))}

end DetComplexityPowerSum.Quadratic


