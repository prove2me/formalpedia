-- Prove2me | Definitions.Def_PorteusGenSS_IsTangentPair
-- name    : PorteusGenSS_IsTangentPair
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:15:14.902879+00:00
-- url     : https://prove2.me/theorems/98592e9b-9bb1-426b-b739-69d133e616d7
-- title:
--   A slope $c\in C$ with its intercept $K_c$
-- statement:
--   The paper sets $C=\{a\in\mathbb R:(a,K)\in C_2(z)\text{ for some }K\ge0,\ z>0\}$ and, for $a\in C$, $K_a$ the intercept with $(a,K_a)\in C_2(z)$ for some $z>0$. The predicate says that $(a,K)$ is such a pair: $K\ge0$ and $(a,K)\in C_2(z)$ for some $z>0$. Then $c(y)\le K_a+a y$ for $y\ge0$, and $c(z)=\min_{a\in C}(K_a+az)$ for $z>0$.
--
--   **Formalization Note** Every statement "for $c\in C$" involving $K_c$ is written as a universal statement over all such pairs; for a given slope the intercept is unique, so this ranges exactly over $C$.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §II, p. 412

import Mathlib
import Definitions.Def_PorteusGenSS_C2

namespace PorteusGenSS

/-- **A slope c ∈ C together with its intercept K_c (§II).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §II, p. 412: "C = {c ∈ R; (c, K) ∈ C2(z) for some K ≥ 0 and z > 0}. … Let Kc, for
c ∈ C, be the real number which satisfies (c, Kc) ∈ C2(x) for some x > 0."

`IsTangentPair c a K` says `K ≥ 0` and `(a, K) ∈ C₂(z)` for some `z > 0`; that is, `a ∈ C` and
`K = K_a`.

**Formalization Note.** Every statement of the paper "… for c ∈ C" involving `K_c` is written
`∀ a K, IsTangentPair c a K → …`. Two pairs `(a, K) ∈ C₂(z₁)` and `(a, K') ∈ C₂(z₂)` with the
same slope have the same intercept (each line lies above `c` on `[0, ∞)` and touches `c` at
`z₁` resp. `z₂`, so `K ≤ K'` and `K' ≤ K`); hence this quantifier ranges exactly over `c ∈ C`
together with its `K_c`. -/
def IsTangentPair (c : ℝ → ℝ) (a K : ℝ) : Prop :=
  0 ≤ K ∧ ∃ z : ℝ, 0 < z ∧ (a, K) ∈ C2 c z

end PorteusGenSS


