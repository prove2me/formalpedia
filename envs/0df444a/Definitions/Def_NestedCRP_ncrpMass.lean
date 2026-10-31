-- Prove2me | Definitions.Def_NestedCRP_ncrpMass
-- name    : NestedCRP_ncrpMass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:27:45.208396+00:00
-- url     : https://prove2.me/theorems/0bd21230-dc4f-4c87-aa91-ab934c52af47
-- title:
--   Nested CRP mass of a tree
-- statement:
--   Given a tree $T$, a tourist $d$, a level $\ell$ and a set $A$ of tourists already seated, let $n$ be the number of tourists of $A$ in the restaurant of $d$ at level $\ell$ and $n'$ the number of them at the table of $d$ there. The seating factor of Eq. (1) is
--
--   $$
--   \mathrm{seat}(T,d,\ell,A)=\begin{cases} n'/(\gamma+n) & n'>0,\\ \gamma/(\gamma+n) & n'=0.\end{cases}
--   $$
--
--   The mass of a tree under the nested Chinese restaurant process, with tourists arriving in the order $0,1,\dots$, is
--
--   $$
--   \mathrm{ncrp}(T)=\prod_{d}\prod_{\ell<L}\mathrm{seat}\bigl(T,d,\ell,\{e<d\}\bigr),
--   $$
--
--   where $L$ is the first level at which all tourists are separated. The mass of the path of $d$ as the last arrival is $\prod_{\ell<L}\mathrm{seat}(T,d,\ell,\{e\ne d\})$; this is the prior on paths $p(c_d\mid c_{-d},\gamma)$.
--
--   **Formalization Note** The restaurant of $d$ at level $\ell$ is its block in $\mathcal P_\ell$, and its tables are the blocks of $\mathcal P_{\ell+1}$ inside. The $n$ here is the paper's $n-1$. Below level $L$ a tourist is alone, so $n=n'=0$ and the factor is $\gamma/\gamma=1$ for $\gamma>0$: the finite product loses nothing.
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, Eq. (1), p.7:6; §3, p.7:9; §5.2, p.7:17

import Mathlib
import Definitions.Def_NestedCRP_Tree

namespace NestedCRP

open Classical in
/-- The factor of Eq. (1) for tourist `d` at level `ℓ`, with the tourists of `A` already seated:
with `n` of them in `d`'s restaurant and `n'` at `d`'s table, it is `n' / (γ + n)` when `n' > 0`
(an occupied table) and `γ / (γ + n)` otherwise (the next unoccupied table).
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), Eq. (1), p.7:6, and §3, p.7:9.

**Formalization Note** The restaurant of `d` at level `ℓ` is its block in `T.part ℓ`, and its tables
are the blocks of `T.part (ℓ + 1)` inside. The `n` here is the paper's `n − 1`. -/
noncomputable def seat {D : ℕ} (γ : ℝ) (T : Tree D) (d : Fin D) (ℓ : ℕ) (A : Finset (Fin D)) : ℝ :=
  let n := (A.filter fun e => T.Rel ℓ e d).card
  let n' := (A.filter fun e => T.Rel (ℓ + 1) e d).card
  (if 0 < n' then (n' : ℝ) else γ) / (γ + n)

/-- The nCRP mass of a tree: tourists `0, 1, …` arrive in order, and each picks its table at each
level by Eq. (1). Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §3, p.7:9.

**Formalization Note** The product runs to `T.sepLevel`, since a tourist alone in its restaurant
has `n = n' = 0`, so `seat = γ/γ = 1` at all deeper levels (for `γ > 0`). -/
noncomputable def ncrpMass {D : ℕ} (γ : ℝ) (T : Tree D) : ℝ :=
  ∏ d : Fin D, ∏ ℓ ∈ Finset.range T.sepLevel, seat γ T d ℓ (Finset.univ.filter fun e => e < d)

/-- The mass of `d`'s path under the nCRP when `d` is the last tourist to arrive:
`p(c_d | c_{-d}, γ)`, "the prior on paths implied by the nested CRP".
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.2, p.7:17. -/
noncomputable def lastMass {D : ℕ} (γ : ℝ) (T : Tree D) (d : Fin D) : ℝ :=
  ∏ ℓ ∈ Finset.range T.sepLevel, seat γ T d ℓ (Finset.univ.erase d)

end NestedCRP


