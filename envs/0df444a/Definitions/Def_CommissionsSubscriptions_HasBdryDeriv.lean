-- Prove2me | Definitions.Def_CommissionsSubscriptions_HasBdryDeriv
-- name    : CommissionsSubscriptions_HasBdryDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:33:27.722264+00:00
-- url     : https://prove2.me/theorems/164e8f47-431c-4c69-9acd-861e1e7e7d1b
-- title:
--   Finite derivative on $[L,R]$ with one-sided limits at the end points
-- statement:
--   For $g:\mathbb R\to\mathbb R$, an interval $[L,R]$, a point $q$ and a real number $d$, we say that **$g'(q)=d$ in the sense of footnote 22** if either $q\in(L,R)$ and $g$ has derivative $d$ at $q$, or $q=L$ and $g'(t)\to d$ as $t\downarrow L$, or $q=R$ and $g'(t)\to d$ as $t\uparrow R$.
--
--   This is the paper's convention $g'_j(0)=\lim_{q\downarrow0}g'_j(q)$, $g'_j(b_j)=\lim_{q\uparrow b_j}g'_j(q)$, used in the optimality conditions (EC.3).
--
--   **Formalization Note** $d$ is a real number, so the derivative is finite, as Proposition EC.1(iii) asserts.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), footnote 22, p. ec2

import Mathlib

open Filter Topology

namespace CommissionsSubscriptions

/-- **A finite derivative of `g` on `[L, R]` in the sense of footnote 22.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), footnote 22, p. ec2: `g′(q)` is the derivative at
`q ∈ (L, R)`, and at the end points "`g′(L) = lim_{q↓L} g′(q)` and `g′(R) = lim_{q↑R} g′(q)`".

`HasBdryDeriv g L R q d` says that `q ∈ [L, R]` and `g′(q) = d` in this sense, with `d` a finite
real number: either `q ∈ (L, R)` and `g` has derivative `d` at `q`, or `q` is an end point and
`deriv g` tends to `d` from inside the interval.

**Formalization Note (Reading 8).** The finiteness of `g′(q)` that Proposition EC.1(iii)
asserts ("have finite values") is built in: `d : ℝ`. -/
def HasBdryDeriv (g : ℝ → ℝ) (L R q d : ℝ) : Prop :=
  (q ∈ Set.Ioo L R ∧ HasDerivAt g d q) ∨
    (q = L ∧ Tendsto (deriv g) (𝓝[>] L) (𝓝 d)) ∨
    (q = R ∧ Tendsto (deriv g) (𝓝[<] R) (𝓝 d))

end CommissionsSubscriptions


