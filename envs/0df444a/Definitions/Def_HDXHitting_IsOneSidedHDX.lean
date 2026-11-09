-- Prove2me | Definitions.Def_HDXHitting_IsOneSidedHDX
-- name    : HDXHitting_IsOneSidedHDX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:44.362587+00:00
-- url     : https://prove2.me/theorems/f71d1a15-2792-46bf-aef6-8f2a0c4117b4
-- title:
--   $\lambda$-one-sided high-dimensional expander
-- statement:
--   A $d$-dimensional complex with top distribution $p$ is a **$\lambda$-one-sided HDX** if for every face $\tau$ of codimension $\operatorname{codim}\tau = d-|\tau|\ge 2$, the induced graph $(X_\tau(1),X_\tau(2))$ of the link of $\tau$, with edge weights $W_\tau$, has second eigenvalue at most $\lambda$, in the Rayleigh form of the published predicate HDXConc.SecondEigLE (over all vertices): every $g$ with $\sum_u\deg_\tau(u)g(u)=0$ satisfies $\sum_{u,w}W_\tau(u,w)g(u)g(w)\le\lambda\sum_u\deg_\tau(u)g(u)^2$, equivalent to $\lambda_2(D^{-1}W_\tau)\le\lambda$ by the Courant–Fischer theorem.
--
--   The case $\tau=\emptyset$ is the induced graph $(X(1),X(2))$ of the complex itself.
--
--   **Formalization Note** Codimension at least $2$ is $|\tau|+2\le d$. The condition is imposed on all vertex sets $\tau$; for a set that is not a face all link weights vanish and the condition holds trivially.
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Definition 2.2, p.13

import Mathlib
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXConc_SecondEigLE

namespace HDXHitting

/-- Definition 2.2 (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), p.13), one-sided part: a `d`-dimensional complex is a
**`λ`-one-sided HDX** if for every face `τ` of codimension `codim τ = d − |τ| ≥ 2` the induced
graph `(X_τ(1), X_τ(2))` of its link has second eigenvalue at most `λ`.

**Formalization Note** `codim τ ≥ 2` is `τ.card + 2 ≤ d` (dimension = number of vertices),
including `τ = ∅`, whose link is the complex itself. The quantifier runs over all sets `τ`;
for a non-face all link weights vanish and the condition holds trivially. "Second eigenvalue
`≤ λ`" is the published Rayleigh-form predicate `HDXConc.SecondEigLE` on the whole vertex type
(for symmetric weights equivalent to `λ₂(D⁻¹W) ≤ λ` by Courant–Fischer). -/
def IsOneSidedHDX {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (p : Finset V → ℝ)
    (lam : ℝ) : Prop :=
  ∀ τ : Finset V, τ.card + 2 ≤ d → HDXConc.SecondEigLE Finset.univ (linkWeight p τ) lam

end HDXHitting


