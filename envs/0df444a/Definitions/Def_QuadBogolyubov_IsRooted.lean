-- Prove2me | Definitions.Def_QuadBogolyubov_IsRooted
-- name    : QuadBogolyubov_IsRooted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:04:19.040201+00:00
-- url     : https://prove2.me/theorems/c38c12f2-5e17-4f97-b1e5-08db26ac18cd
-- title:
--   Varieties as in (28) and the bilinear variety $B$ of (29)
-- statement:
--   A quadratic variety is **as in (28)** when it has complexity $(0,d)$ and is written
--   $$W=\{x\in G:\ q(x)=0\},\qquad q=(q_1,\dots,q_d),\quad q_j(0)=0,$$
--   with $G=\mathbb F_2^n$; it then contains $0$. Its **bilinear variety** is
--   $$B=\{(x,y)\in G^2:\ \beta_j(x,y)=0\text{ for all }j\},\qquad \beta_j=\beta_{q_j}.$$
--   Appendix D works with these normalized varieties throughout.
--
--   **Formalization Note** The conditions are $d_1=0$, all $b_j=0$ and all $q_j(0)=0$.
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), App. D.1, pp.52–53, eqs. (28), (29)

import Mathlib
import Definitions.Def_QuadBogolyubov_HasRankAtLeast

set_option autoImplicit false

namespace QuadBogolyubov

/-- A quadratic variety **as in (28)**: complexity `(0, d)` containing `0`, written
`W = {x ∈ G : q(x) = 0}` with `q = (q₁, …, q_d)` and `qⱼ(0) = 0`; that is, `d₁ = 0`, every
`bⱼ = 0` and every `qⱼ(0) = 0`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), App. D.1,
p.52: "Throughout this section, we shall consider a quadratic variety W of complexity (0, d)
containing 0. After adding the value at 0 to each defining quadratic function, we may and shall
write (28) W = {x ∈ G : q(x) = 0}, q = (q1, . . . , qd) : G → F₂ᵈ, qj(0) = 0."

**Formalization Note.** `G = 𝔽₂ⁿ`; `d` is `W.d2`. These conditions imply `0 ∈ W`. -/
def IsRooted {n : ℕ} (W : QuadVariety n) : Prop :=
  W.d1 = 0 ∧ (∀ j, W.b j = 0) ∧ ∀ j, W.q j 0 = 0

open Classical in
/-- The **bilinear variety** `B = {(x, y) ∈ G² : β(x, y) = 0}` with
`β = (β_{q₁}, …, β_{q_d})` the bilinear forms of the defining quadratics.

App. D.1, p.53, eq. (29): "Write βj = βqj, set β(x, y) = (β1(x, y), . . . , βd(x, y)), and define
the associated bilinear variety B by (29) B = {(x, y) ∈ G² : β(x, y) = 0}." -/
noncomputable def bilinVar {n : ℕ} (W : QuadVariety n) :
    Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
  Finset.univ.filter (fun p => ∀ j, bilin (W.q j) p.1 p.2 = 0)

end QuadBogolyubov


