-- Prove2me | Definitions.Def_WildeQIT_Wiretap_wiretapJoint
-- name    : WildeQIT_Wiretap_wiretapJoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:27:35.539268+00:00
-- url     : https://prove2.me/theorems/a2b4514b-f2a6-4292-a42b-9088f674bf40
-- title:
--   Joint distribution of $(U,Y,Z)$ for an auxiliary input $U$
-- statement:
--   Let $N\equiv p_{Y,Z|X}$ be a wiretap channel. Alice picks an auxiliary random variable $U$ with a finite alphabet and then $X$ given $U$, according to a joint distribution $p_{U,X}(u,x)$, and sends $X$ through the channel. Since $U\to X\to(Y,Z)$, the triple $(U,Y,Z)$ has the joint distribution
--
--   $$
--   p_{U,Y,Z}(u,y,z)=\sum_{x} p_{U,X}(u,x)\,p_{Y,Z|X}(y,z|x).
--   $$
--
--   Its marginals on $(U,Y)$ and $(U,Z)$ are the distributions with respect to which $I(U;Y)$ and $I(U;Z)$ in the private information are computed.
--
--   **Formalization Note** Alphabets are finite types (the book's setting) and information is measured in bits ($\log_2$). Distributions are the published `WildeQIT.FinDist`, channels the published `WildeQIT.Channel`, and $I(\cdot\,;\cdot)$ is the published `WildeQIT.mutualInfo` of a joint distribution (first component against second).
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Section 13.2, eq. (13.56), p. 396

import Definitions.Def_WildeQIT_Wiretap_WiretapChannel

namespace WildeQIT.Wiretap

open WildeQIT

/-- **Joint distribution of `(U, Y, Z)` for an auxiliary input `U`.**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.2, (13.56), p. 396:
Alice picks an auxiliary random variable `U` and then `X` given `U`, with joint density
`p_{U,X}(u, x)`, and sends `X` through the wiretap channel `p_{Y,Z|X}`. `U → X → (Y, Z)`, so

`p_{U,Y,Z}(u, y, z) = ∑ₓ p_{U,X}(u, x) p_{Y,Z|X}(y, z|x)`.

`wiretapJoint p N` is this distribution on `υ × β × γ` (`U` first, Bob's `Y` second, Eve's `Z`
third); its marginals `margXY` and `margXZ` are the pairs `(U, Y)` and `(U, Z)`. -/
noncomputable def wiretapJoint {υ α β γ : Type} [Fintype υ] [Fintype α] [Fintype β] [Fintype γ]
    (p : FinDist (υ × α)) (N : WiretapChannel α β γ) : FinDist (υ × β × γ) where
  prob t := ∑ x, p.prob (t.1, x) * (N x).prob t.2
  nonneg t := Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg (t.1, x)) ((N x).nonneg t.2)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl fun u _ => Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (N _).sum_eq_one, mul_one]
    rw [← Fintype.sum_prod_type (f := fun ux : υ × α => p.prob ux)]
    exact p.sum_eq_one

end WildeQIT.Wiretap


