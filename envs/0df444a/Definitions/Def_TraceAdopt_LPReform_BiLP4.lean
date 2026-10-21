-- Prove2me | Definitions.Def_TraceAdopt_LPReform_BiLP4
-- name    : TraceAdopt_LPReform_BiLP4
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:07.11851+00:00
-- url     : https://prove2.me/theorems/fa7ae113-4629-4bf3-bd6b-0065fbcfdba7
-- title:
--   Proposition 5 — first binary linear programming formulation (4)
-- statement:
--   The first binary linear program uses a seed indicator $s_i$ and two orientation variables $\ell_{ij},\ell_{ji}$ for every firm–supply-chain pair. All take values in $\{0,1\}$. It requires
--
--   $$\sum_{j:i\in e_j}r_{ji}\ell_{ji}\ge c_i(1-s_i),\qquad \sum_{i\in e_j}\ell_{ij}\ge\theta_j-1,$$
--
--   $$\ell_{ij}+\ell_{ji}=1,\qquad \ell_{i_1j_1}+\ell_{j_1i_2}+\ell_{i_2j_2}+\ell_{j_2i_1}\le3.$$
--
--   The last two constraints range over all pairs and quadruples of the indicated types, as printed in (4c)–(4d). This is the feasible region of formulation (4), whose objective is $\sum_i w_i s_i$.
--
--   **Formalization Note** The first inequality is written as $c_i\le\sum_jr_{ji}\ell_{ji}+c_i s_i$ to avoid natural-number subtraction; the binary restriction makes it equivalent to the displayed inequality.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 15, Proposition 5, equations (4a)–(4d)

import Definitions.Def_TraceAdopt_LPReform_Model

namespace TraceAdopt.LPReform

/-- Binary feasibility for the paper's formulation (4), p. 15.
The adoption inequality is rearranged to avoid truncated natural subtraction. -/
def BiLP4Feasible (I : Instance)
    (s : Fin I.n → ℕ) (lFS : Fin I.n → Fin I.m → ℕ)
    (lSF : Fin I.m → Fin I.n → ℕ) : Prop :=
  (∀ i, s i ≤ 1) ∧
  (∀ i j, lFS i j ≤ 1 ∧ lSF j i ≤ 1) ∧
  (∀ i, I.c i ≤
    (∑ j ∈ Finset.univ.filter (fun j => i ∈ I.e j), I.r j i * lSF j i) +
      I.c i * s i) ∧
  (∀ j, I.θ j - 1 ≤
    ∑ i ∈ Finset.univ.filter (fun i => i ∈ I.e j), lFS i j) ∧
  (∀ i j, lFS i j + lSF j i = 1) ∧
  (∀ i₁ i₂ j₁ j₂,
    lFS i₁ j₁ + lSF j₁ i₂ + lFS i₂ j₂ + lSF j₂ i₁ ≤ 3)

end TraceAdopt.LPReform


