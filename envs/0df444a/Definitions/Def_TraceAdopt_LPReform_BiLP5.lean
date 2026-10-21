-- Prove2me | Definitions.Def_TraceAdopt_LPReform_BiLP5
-- name    : TraceAdopt_LPReform_BiLP5
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:07.154998+00:00
-- url     : https://prove2.me/theorems/b6c217ee-9750-4f86-80cf-665293ff7740
-- title:
--   Formulation (5), p. 16 — the tree-decomposition-dependent binary program
-- statement:
--   Let $\mathcal T'=(T',\{X'_z\}_{z\in T'})$ be a family of bags of vertices of the auxiliary graph $G'$, whose vertex set is $N'=N_F\cup N_{SC}$. The second binary linear program has a seed indicator $s_i$ for every firm and an orientation variable $\ell_{pq}$ for every ordered pair $p,q$ of vertices of $N'$ lying in a common bag. All variables take values in $\{0,1\}$. Its constraints are
--
--   $$\sum_{j:\,i\in e_j}r_{ji}\ell_{ji}\ge c_i(1-s_i)\quad(i\in N_F),\qquad \sum_{i\in e_j}\ell_{ij}\ge\theta_j-1\quad(j\in N_{SC}),$$
--
--   $$\ell_{pq}+\ell_{qp}=1,\qquad \ell_{pq}+\ell_{qx}+\ell_{xp}\le2\qquad(p,q,x\in X'_z\text{ distinct},\ z\in T').$$
--
--   When the bags form a tree decomposition of $G'$, every firm–supply-chain pair $(i,j)$ with $i\in e_j$ lies in a common bag, so the first two constraints only use declared variables. This is the feasible region of formulation (5), whose objective is $\sum_iw_is_i$. Unlike formulation (4), it constrains only pairs and triples inside a bag.
--
--   **Formalization Note** The orientation variables are a function on all ordered pairs of $N'$; values on pairs that share no bag occur in no constraint. The constraints (5c) and (5d) are stated for distinct, respectively pairwise distinct, vertices of a bag: as printed with $i=j$, (5c) would read $2\ell_{ii}=1$ and make (5) infeasible. The first inequality is written as $c_i\le\sum_jr_{ji}\ell_{ji}+c_is_i$ to avoid natural-number subtraction; for binary $s_i$ it is the displayed inequality (5a).
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 16, equations (5a)–(5d)

import Definitions.Def_TraceAdopt_LPReform_Model

namespace TraceAdopt.LPReform

/-- Binary feasibility for the paper's second formulation (5), p. 16, built on a
family of bags `X'` of the auxiliary graph `G′`. The orientation variable `ℓ u v`
is read only for pairs `u, v` that share a bag (the only pairs (5) declares);
(5c) and (5d) range over distinct, respectively pairwise distinct, vertices of a
bag. The adoption inequality (5a) is rearranged to avoid truncated subtraction. -/
def BiLP5Feasible (I : Instance) {T : Type} (X' : T → Finset (Fin I.n ⊕ Fin I.m))
    (s : Fin I.n → ℕ) (ℓ : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ) : Prop :=
  (∀ i, s i ≤ 1) ∧
  (∀ z, ∀ u ∈ X' z, ∀ v ∈ X' z, ℓ u v ≤ 1) ∧
  (∀ i, I.c i ≤
    (∑ j ∈ Finset.univ.filter (fun j => i ∈ I.e j),
      I.r j i * ℓ (Sum.inr j) (Sum.inl i)) + I.c i * s i) ∧
  (∀ j, I.θ j - 1 ≤
    ∑ i ∈ Finset.univ.filter (fun i => i ∈ I.e j), ℓ (Sum.inl i) (Sum.inr j)) ∧
  (∀ z, ∀ u ∈ X' z, ∀ v ∈ X' z, u ≠ v → ℓ u v + ℓ v u = 1) ∧
  (∀ z, ∀ u ∈ X' z, ∀ v ∈ X' z, ∀ x ∈ X' z, u ≠ v → v ≠ x → u ≠ x →
    ℓ u v + ℓ v x + ℓ x u ≤ 2)

end TraceAdopt.LPReform


