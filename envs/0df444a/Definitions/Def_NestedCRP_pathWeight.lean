-- Prove2me | Definitions.Def_NestedCRP_pathWeight
-- name    : NestedCRP_pathWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:38.913984+00:00
-- url     : https://prove2.me/theorems/fd6a313e-1af6-4c84-8260-c1e0e3439f4a
-- title:
--   Path weight of Eq. (4)
-- statement:
--   Fix level allocations, a document $d$ and a tree $T'$. Let $N(v)$ count the words of all documents with level $\ell$, in the node of $d$ at level $\ell$ under $T'$, equal to $v$, and let $N^-(v)$ do the same leaving out the words of $d$. The factor of level $\ell$ is
--
--   $$
--   R_\ell=\frac{\Gamma\bigl(\sum_v N^-(v)+V\eta\bigr)}{\prod_v\Gamma\bigl(N^-(v)+\eta\bigr)}\cdot\frac{\prod_v\Gamma\bigl(N(v)+\eta\bigr)}{\Gamma\bigl(\sum_v N(v)+V\eta\bigr)},
--   $$
--
--   and the weight of $T'$ in Eq. (4) is the mass of the path of $d$ as the last arrival times $\prod_{\ell\le\max(z_d)}R_\ell$.
--
--   **Formalization Note** Levels are 0-based, so the paper's $\ell=1,\dots,\max(z_d)$ becomes $\ell=0,\dots,\max(z_d)$; for $N_d=0$ the maximum of nothing is 0 and the one factor equals 1. The prior is that of the whole tree $T'$, because the state keeps the whole tree and nothing has to be extended when a level rises past that length. `NestedCRP.path_conditional_truncated` gives the printed truncated form. All Gamma arguments are positive since $\eta>0$ and $V\ge1$.
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, Eq. (4) and §5.2, second display, p.7:17

import Mathlib
import Definitions.Def_NestedCRP_Hyper
import Definitions.Def_NestedCRP_ncrpMass
import Definitions.Def_NestedCRP_Corpus

namespace NestedCRP

variable {V D : ℕ}

open Classical in
/-- `N(v)` of Eq. (4): the words of all documents with level `ℓ`, in `d`'s node of level `ℓ` under
`T`, and equal to `v`: `#[z = ℓ, c_ℓ = c_{d,ℓ}, w = v]`.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.2, second display, p.7:17. -/
noncomputable def nodeCount (C : Corpus V D) (z : C.Levels) (T : Tree D) (d : Fin D) (ℓ : ℕ)
    (v : Fin V) : ℕ :=
  (Finset.univ.filter fun s : C.Site =>
    z s.1 s.2 = ℓ ∧ T.Rel ℓ s.1 d ∧ C.word s = v).card

open Classical in
/-- `N⁻(v)` of Eq. (4): as `nodeCount`, leaving out the words of `d`:
`#[z_{-d} = ℓ, c_{-d,ℓ} = c_{d,ℓ}, w_{-d} = v]`.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.2, second display, p.7:17. -/
noncomputable def nodeCountOff (C : Corpus V D) (z : C.Levels) (T : Tree D) (d : Fin D) (ℓ : ℕ)
    (v : Fin V) : ℕ :=
  (Finset.univ.filter fun s : C.Site =>
    s.1 ≠ d ∧ z s.1 s.2 = ℓ ∧ T.Rel ℓ s.1 d ∧ C.word s = v).card

/-- The factor of level `ℓ` in the word likelihood of §5.2:
`[Γ(∑_v N⁻(v) + Vη) / ∏_v Γ(N⁻(v) + η)] · [∏_v Γ(N(v) + η) / Γ(∑_v N(v) + Vη)]`.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.2, second display, p.7:17. -/
noncomputable def levelRatio (η : ℝ) (C : Corpus V D) (z : C.Levels) (T : Tree D) (d : Fin D)
    (ℓ : ℕ) : ℝ :=
  Real.Gamma ((∑ v, (nodeCountOff C z T d ℓ v : ℝ)) + V * η) /
      (∏ v, Real.Gamma ((nodeCountOff C z T d ℓ v : ℝ) + η)) *
    ((∏ v, Real.Gamma ((nodeCount C z T d ℓ v : ℝ) + η)) /
      Real.Gamma ((∑ v, (nodeCount C z T d ℓ v : ℝ)) + V * η))

/-- The Eq. (4) weight of a tree `T'` for document `d`: the prior on paths times the word likelihood,
`p(c_d | c_{-d}, γ) · ∏_{ℓ ≤ max(z_d)} (…)`. Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), Eq. (4) and §5.2, second display, p.7:17.

**Formalization Note** Levels are 0-based, so the paper's `ℓ = 1, …, max(z_d)` becomes
`ℓ = 0, …, max(z_d)`. For `N d = 0`, `max` of nothing is 0 and the single factor is 1. The prior is
for the whole tree `T'`, not for a path of length `max(z_d)`: the state keeps the whole tree, so
nothing has to be extended when a level rises past that length. Summing the tails gives the
printed truncated form (`path_conditional_truncated`). -/
noncomputable def pathWeight (H : Hyper) (C : Corpus V D) (z : C.Levels) (d : Fin D) (T' : Tree D) :
    ℝ :=
  lastMass H.gamma T' d *
    ∏ ℓ ∈ Finset.range (Finset.univ.sup (z d) + 1), levelRatio H.eta C z T' d ℓ

end NestedCRP


