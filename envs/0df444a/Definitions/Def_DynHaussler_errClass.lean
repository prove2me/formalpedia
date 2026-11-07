-- Prove2me | Definitions.Def_DynHaussler_errClass
-- name    : DynHaussler_errClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:39.0562+00:00
-- url     : https://prove2.me/theorems/eda3fe3f-73ac-450f-a191-24cc4302ba28
-- title:
--   Partial error classes $A^{\pm}=\{\phi^{\pm}_f:f\in H\}$ of Eq. (39)
-- statement:
--   Let $\eta>0$ and $H\subseteq[0,1]^X$. For $f\in H$ and a pair $(x,a)$ define the partial labels
--   $$
--   \phi^+_f(x,a)=\begin{cases}0,& f(x)-a\le\eta,\\ 1,& f(x)-a\ge2\eta,\\ *,&\eta<f(x)-a<2\eta,\end{cases}\qquad
--   \phi^-_f(x,a)=\begin{cases}0,& a-f(x)\le\eta,\\ 1,& a-f(x)\ge2\eta,\\ *,&\eta<a-f(x)<2\eta,\end{cases}
--   $$
--   and the **partial error classes** $A^{\pm}=\{\phi^{\pm}_f:f\in H\}$. A definite one records a one-sided error of size at least $2\eta$; a nonzero value, including $*$, records an error strictly greater than $\eta$ in that direction.
--
--   **Formalization Note** One definition covers both classes: `plus = true` is $A^+$, `plus = false` is $A^-$. Partial labels are `Option Bool` (`none` is $*$). The paper's domain is $Z=X\times[0,1]$; here the second coordinate ranges over $\mathbb R$, with the same formula (the paper's classes are the restrictions to $X\times[0,1]$).
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Eq. (39), p.22 (PDF p.24)

import Mathlib

set_option autoImplicit false

namespace DynHaussler

/-- The **partial error classes** `A^± = {ϕ^±_f : f ∈ H}` of Eq. (39): for `f ∈ H` and a pair
`(x, a)`,
`ϕ^+_f(x, a) = 0` if `f(x) − a ≤ η`, `1` if `f(x) − a ≥ 2η`, `∗` if `η < f(x) − a < 2η`, and
`ϕ^−_f(x, a)` is the same with `a − f(x)` in place of `f(x) − a`.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Eq. (39), p.22 (PDF p.24).

**Formalization Note** `plus = true` gives `A^+`, `plus = false` gives `A^−`. Partial labels are
`Option Bool` (`none` is `∗`). The paper's domain is `Z = X × [0,1]`; here the second coordinate
ranges over `ℝ` (the defining formula is the same, and the paper's classes are the restrictions to
`X × [0,1]`). For `η > 0` the three cases are disjoint, as on the page. -/
noncomputable def errClass {X : Type*} (η : ℝ) (H : Set (X → ℝ)) (plus : Bool) :
    Set (X × ℝ → Option Bool) :=
  {ϕ | ∃ f ∈ H, ϕ = fun z =>
    let e := if plus then f z.1 - z.2 else z.2 - f z.1
    if e ≤ η then some false else if 2 * η ≤ e then some true else none}

end DynHaussler


