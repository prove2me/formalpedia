-- Prove2me | Definitions.Def_TIESched_interaction
-- name    : TIESched_interaction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:45:55.929384+00:00
-- url     : https://prove2.me/theorems/b86db9f8-d39f-45a4-95e1-e9e10d385248
-- title:
--   Job allocation interaction $G^J_{ij}$ and interaction order (Definition 3.1)
-- statement:
--   For a report $p$ on a finite job set $J$ and $S\subseteq J$, let $p_S$ be the submatrix of the columns in $S$; $x^S(p_S)$ is the mechanism run on the smaller instance. For $j\in J$ and a machine $i$, the **job allocation interaction coefficient** is the Möbius coefficient
--   $$G^J_{ij}(p_J)=\sum_{\substack{S\subseteq J\\ j\in S}}(-1)^{|J|-|S|}\,x^S_{ij}(p_S).$$
--   An allocation family has **interaction order at most $d$** if $G^J_{ij}(p_J)=0$ for every finite $J$ with $|J|>d$, every nonnegative $p_J$, every $j\in J$ and every $i$.
--
--   Interaction order at most $m-1$ is the structural property that the reduction of §5 produces and the hard instances of §4 exploit.
--
--   **Formalization Note.** The sum runs over all $S\subseteq J$ of the function equal to $x^S_{ij}(p_S)$ when $j\in S$ and $0$ otherwise, as on p.9. `restrictReport p S` is $p_S$ (it pads columns outside $J$ with $0$, which never occur for $S\subseteq J$).
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Definition 3.1, p.9

import Mathlib
import Definitions.Def_TIESched_FracMech

set_option autoImplicit false

namespace TIESched

/-- **Restriction** `p_S` of a report `p` on job set `J` to the columns of a job set `S`
(arXiv:2611.05142, §3.1, p.9: "let `p_S` denote the submatrix consisting of the columns in
`S ⊆ [n]`").

**Formalization Note.** For `S ⊆ J` this is exactly the submatrix. To avoid membership proofs the
definition is total: a column of `S` outside `J` is filled with `0`; it is only ever applied with
`S ⊆ J` (the sums below range over `J.powerset`). -/
def restrictReport {m : ℕ} {J : Finset ℕ} (p : Fin m → J → ℝ) (S : Finset ℕ) : Fin m → S → ℝ :=
  fun i j => if h : (j : ℕ) ∈ J then p i ⟨j, h⟩ else 0

/-- **Job allocation interaction coefficient** (arXiv:2611.05142, Definition 3.1, p.9): for a finite
job set `J`, a job `j ∈ J` and a machine `i`,
`G^J_ij(p_J) = Σ_{S ⊆ J, j ∈ S} (−1)^{|J|−|S|} x^S_ij(p_S)`,
where `x^S(p_S)` is the mechanism run on the smaller instance `p_S`.

**Formalization Note.** The sum is written over all `S ⊆ J` of "the set function that takes the
value `x^S_ij(p_S)` when `j ∈ S` and zero otherwise" (p.9), which is the same sum. -/
noncomputable def interaction {m : ℕ} (x : AllocFamily m) (J : Finset ℕ) (p : Fin m → J → ℝ)
    (i : Fin m) (j : J) : ℝ :=
  ∑ S ∈ J.powerset, (-1 : ℝ) ^ (J.card - S.card) *
    (if h : (j : ℕ) ∈ S then x S (restrictReport p S) i ⟨j, h⟩ else 0)

/-- **Interaction order at most `d`** (arXiv:2611.05142, §3.1, p.9): for any finite job set `J`
with `|J| > d` and any nonnegative report `p_J`, `G^J_ij(p_J) = 0` for all `j ∈ J` and `i ∈ [m]`. -/
def HasInteractionOrderLE {m : ℕ} (x : AllocFamily m) (d : ℕ) : Prop :=
  ∀ (J : Finset ℕ) (p : Fin m → J → ℝ), d < J.card → IsNonneg p →
    ∀ (i : Fin m) (j : J), interaction x J p i j = 0

end TIESched


