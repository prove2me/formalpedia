-- Prove2me | Definitions.Def_ConstrainedTrading_linSet
-- name    : ConstrainedTrading_linSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:44.738395+00:00
-- url     : https://prove2.me/theorems/9cee6a1b-96e5-4d47-ba64-c848378c9955
-- title:
--   The set $B_f(x)$ on which $\hat f$ is linear near $x$
-- statement:
--   For $f:\mathbb Z^E\to\mathbb R\cup\{-\infty\}$ and $x\in\mathbb R^E$, the set $B_f(x)$ consists of the points $z\in N(x)$ for which there are a finite set $S\subseteq N(x)$ containing $z$ and weights $\lambda>0$ on $S$ with
--   $$
--   \sum_{w\in S}\lambda_w=1,\qquad \sum_{w\in S}\lambda_w w=x,\qquad \sum_{w\in S}\lambda_w f(w)=\hat f(x).
--   $$
--   In words, $B_f(x)$ collects the points of the unit hypercube that carry positive weight in some optimal convex representation of $x$; the paper describes it as "the maximal set that contains $x$ such that convex extension is linear".
--
--   **Formalization Note** The printed Definition 2.10 does not link the point $z$ to the weights. It is read with the weights supported in $N(x)$ and $\lambda_z>0$, which the proof of Lemma 2.2 uses ("$\lambda_{x_1}>0$ and $\lambda_{x_2}>0$"). $\hat f$ is `concaveExt f`.
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, Definition 2.10, p.6

import Mathlib
import Definitions.Def_ConstrainedTrading_IsConvexRep
import Definitions.Def_ConstrainedTrading_repValue
import Definitions.Def_ConstrainedTrading_concaveExt
import Definitions.Def_ConstrainedTrading_unitBox

namespace ConstrainedTrading

/-- The set `B_f(x)` (Kizilkale–Vohra, *Constrained Trading Networks*, arXiv:2008.09757v1,
Definition 2.10, p.6): the points `z ∈ N(x)` that carry positive weight in some optimal convex
representation of `x` by points of `N(x)`, i.e. some finite `S ⊆ N(x)` and weights `λ > 0` on
`S` with `z ∈ S`, `Σ_{w∈S} λ_w = 1`, `Σ_{w∈S} λ_w w = x` and `Σ_{w∈S} λ_w f(w) = f̂(x)`.

**Formalization Note** The printed Definition 2.10 is garbled
(`{z ∈ N(x) ‖ ∃λ, Σλ_z = 1, Σλ_z z = x, Σλ_z f(z) = f̂(x)}`, with no link between `z` and
`λ`). It is read (reading R4) with `λ` supported in `N(x)` and `λ_z > 0`, as the proof of
Lemma 2.2 requires ("λ_{x₁} > 0 and λ_{x₂} > 0"); without `λ_z > 0` the set would be all of
`N(x)` or empty. `f̂` is `concaveExt f` (the page writes "convex extension", meaning the concave
extension of Definition 2.9, as in §2.2). -/
def linSet {E : Type*} (f : (E → ℤ) → WithBot ℝ) (x : E → ℝ) : Set (E → ℤ) :=
  {z | z ∈ unitBox x ∧ ∃ (S : Finset (E → ℤ)) (wt : (E → ℤ) → ℝ),
    (↑S : Set (E → ℤ)) ⊆ unitBox x ∧ z ∈ S ∧ IsConvexRep x S wt ∧
      repValue f S wt = concaveExt f x}

end ConstrainedTrading


