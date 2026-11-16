-- Prove2me | Definitions.Def_QGraphColl_Supplement_C1
-- name    : QGraphColl_Supplement_C1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:31:27.392343+00:00
-- url     : https://prove2.me/theorems/3c3b14c0-6a70-44dd-bad4-a539087474e8
-- title:
--   Positive certificates and positive certificate complexity $C_1(f)$ of a partial function over an alphabet
-- statement:
--   Let $\Sigma$ be a finite alphabet, $n\ge1$, $D\subseteq\Sigma^n$, and let $f:D\to\{0,1\}$ be a (partial) function. An input $x\in D$ is **positive** when $f(x)=1$.
--
--   1. A **positive certificate** of a positive input $x$ is a set $S\subseteq[n]$ of coordinates such that the partial assignment $x|_S$ forces the value $1$ among inputs in $D$:
--   $$\forall y\in D:\quad y|_S=x|_S\ \Longrightarrow\ f(y)=1.$$
--   2. The **positive certificate complexity** $C_1(f)$ is the least nonnegative integer $k$ such that every positive input $x\in D$ has a positive certificate of size at most $k$.
--
--   Functions with $C_1(f)\le2$ include graph collision ($f=\mathrm{gc}_G$, certified by the two marked endpoints of an edge) and element distinctness; Section 5 reduces every such function over an alphabet of size $q$ to graph collision on $nq$ vertices.
--
--   **Formalization Note** $C_1(f)$ is an infimum of natural numbers; the set is never empty ($k=n$ always works, checked in the verification file), so the infimum is attained. Values of $f$ outside $D$ are never read.
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), §5, p.31 (positive certificate, C1(f))

import Mathlib

namespace QGraphColl.Supplement

/-- §5, p.31 of A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou,
*Breaking the quantum barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026,
sha256 21da7ff0…): "A positive certificate is a partial assignment that forces the value 1 among
inputs in `D`." The set `S` of coordinates is a positive certificate of the input `x` for the
partial function `f : D → {0,1}` (`D ⊆ Σⁿ`) when every input `y ∈ D` that agrees with `x` on `S`
has `f y = 1`. Values of `f` outside `D` are never read. -/
def IsPosCert {ι α : Type*} (D : Finset (ι → α)) (f : (ι → α) → Bool)
    (x : ι → α) (S : Finset ι) : Prop :=
  ∀ y ∈ D, (∀ i ∈ S, y i = x i) → f y = true

/-- §5, p.31 (Cornelissen et al., arXiv:2611.05356, version of October 2026, sha256 21da7ff0…):
the positive certificate complexity `C₁(f)` of a partial function `f : D → {0,1}`, `D ⊆ Σⁿ`:
"the least nonnegative integer such that every positive input has a positive certificate of size at
most `C₁(f)`". A positive input is an `x ∈ D` with `f x = 1`, and its certificate is a set of
coordinates on which it is fixed (`IsPosCert`).

**Formalization Note.** `sInf` in `ℕ`. The set is never empty (`k = |ι|` works: fixing every
coordinate of a positive `x ∈ D` leaves only `x` itself in `D`), so `sInf` is the least such
`k`, and `C₁(f) = 0` exactly when every positive input is certified by the empty assignment. -/
noncomputable def C1 {ι α : Type*} [Fintype ι] (D : Finset (ι → α))
    (f : (ι → α) → Bool) : ℕ :=
  sInf {k : ℕ | ∀ x ∈ D, f x = true → ∃ S : Finset ι, S.card ≤ k ∧ IsPosCert D f x S}

end QGraphColl.Supplement


