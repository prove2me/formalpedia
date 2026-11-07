-- Prove2me | Definitions.Def_SetMultCost_IsSetMultilinearOn
-- name    : SetMultCost_IsSetMultilinearOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:53.552205+00:00
-- url     : https://prove2.me/theorems/8229b77f-fe6e-45f3-8632-b0955fb173ed
-- title:
--   Set-multilinear polynomials and products
-- statement:
--   Suppose the variables are partitioned into parts by a map $\mathrm{part}$. A polynomial $Q$ is **set-multilinear on a set $T$ of parts** when every monomial of $Q$ has degree exactly $1$ in the variables of each part in $T$ and degree $0$ in the variables of every other part. For $T$ the whole set of parts this is the paper's notion: every monomial involves exactly one variable from each part.
--
--   A list of polynomials $G_1,\dots,G_r$ is a **set-multilinear product on $T$** when each $G_j$ is set-multilinear on a set $T_j$, the $T_j$ are pairwise disjoint, and their union is $T$.
--
--   **Formalization Note** The zero polynomial is set-multilinear on every $T$.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), §2, p.8; Lemma 2.2(2), p.9

import Mathlib

namespace SetMultCost

/-- **Set-multilinear polynomial.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), §2, p.8: "A polynomial P(X(1), . . . , X(d)) is said to
be set-multilinear with respect to the above partition of variables if every monomial involves
exactly one variable from each part."

**Formalization Note.** `part x` is the part of the variable `x`. The polynomial is set-multilinear
on the set `T` of parts when every monomial in its support has total degree `1` in each part in
`T` and degree `0` in the others. The zero polynomial is set-multilinear on every `T`. A polynomial
set-multilinear for the whole partition is the case `T = Finset.univ`. -/
def IsSetMultilinearOn {σ ι F : Type*} [CommSemiring F] [DecidableEq ι] (part : σ → ι)
    (T : Finset ι) (Q : MvPolynomial σ F) : Prop :=
  ∀ m ∈ Q.support, ∀ i : ι, (m.sum fun x e => if part x = i then e else 0) = if i ∈ T then 1 else 0

/-- A **set-multilinear product** on `T` (Lemma 2.2(2), p.9; Lemma 4.4, p.15): the factors are
set-multilinear on pairwise disjoint sets of parts with union `T`. -/
def IsSetMultilinearProduct {σ ι F : Type*} [CommSemiring F] [DecidableEq ι] (part : σ → ι)
    (T : Finset ι) (G : List (MvPolynomial σ F)) : Prop :=
  ∃ Ts : Fin G.length → Finset ι, (∀ j, IsSetMultilinearOn part (Ts j) (G.get j)) ∧
    (∀ j j', j ≠ j' → Disjoint (Ts j) (Ts j')) ∧ Finset.univ.biUnion Ts = T

end SetMultCost


