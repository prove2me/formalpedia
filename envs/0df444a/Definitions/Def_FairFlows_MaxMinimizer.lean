-- Prove2me | Definitions.Def_FairFlows_MaxMinimizer
-- name    : FairFlows_MaxMinimizer
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:57.094553+00:00
-- url     : https://prove2.me/theorems/62c03061-9b63-4fba-adce-35a725f95acd
-- title:
--   $\beta_F$ (2.4) and the capped upper bound
-- statement:
--   Let $F$ be a finite edge set.
--
--   1. $\max_F h$ is the largest value of an integer function $h$ on $F$.
--   2. $\beta_F:=\min\{\max\{z(a): a\in F\}: z\in Q⃛(f,g;m)\}$ (2.4) is the smallest possible largest component on $F$ of an integral $(f,g)$-bounded $m$-flow (the value of an $F$-max minimizer).
--   3. For an integer $\beta$, $g^\beta$ arises from $g$ by decreasing $g(e)$ to $\beta$ for each $e\in F$ with $g(e)>\beta$, i.e. $g^\beta(e)=\min(g(e),\beta)$ on $F$ and $g^\beta=g$ off $F$.
--
--   These are the objects of the capping reduction of §2.2, which makes the largest upper bound on $F$ equal to $\beta_F$.
--
--   **Formalization Note** $\max_F$ returns $0$ on $F=\emptyset$ and $\beta_F$ is `sInf` in $\mathbb Z$; every use has $F$ non-empty, $f$ finite on $F$ and Q⃛$(f,g;m)\neq\emptyset$, where the set of values is non-empty and bounded below, so the infimum is the minimum.
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, §2.2 p.7 (F-max minimizer, (2.4) β_F, decreasing g(e) to β_F)

import Mathlib
import Definitions.Def_FairFlows_Network

set_option autoImplicit false

namespace FairFlows

variable {V A : Type}

/-- The largest value `max{h(a) : a ∈ F}` of an integer function `h` on a finite edge set `F`.

**Formalization Note** Every use has `F` non-empty; the value `0` on `F = ∅` is never read. -/
def maxOn (F : Finset A) (h : A → ℤ) : ℤ :=
  if hF : F.Nonempty then F.sup' hF h else 0

/-- `β_F := min{max{z(a) : a ∈ F} : z ∈ Q⃛(f, g; m)}`, the smallest largest component on `F`
of an integral `(f, g)`-bounded `m`-flow (Frank, Murota, *Fair integral network flows*,
arXiv:1907.02673v5, §2.2, (2.4), p.7).

**Formalization Note** The minimum is `sInf` in `ℤ`. When `F` is non-empty, `f` is finite on
`F` and `Q⃛(f, g; m)` is non-empty, the set of values is non-empty and bounded below (by the
least `f`-value on `F`), so `sInf` is attained and is the minimum; every use of `betaF` has
these hypotheses. -/
noncomputable def betaF [Fintype A] [DecidableEq V] (D : Digraph V A) (f : A → WithBot ℤ)
    (g : A → WithTop ℤ) (m : V → ℤ) (F : Finset A) : ℤ :=
  sInf ((fun z => maxOn F z) '' intFlows D f g m)

/-- The upper bound `g` decreased to `β` on every edge `e ∈ F` with `g(e) > β`
(arXiv:1907.02673v5, §2.2, p.7): `min(g(e), β)` on `F`, `g(e)` off `F`. -/
def capOn [DecidableEq A] (g : A → WithTop ℤ) (F : Finset A) (β : ℤ) : A → WithTop ℤ :=
  fun e => if e ∈ F then min (g e) (β : WithTop ℤ) else g e

end FairFlows


