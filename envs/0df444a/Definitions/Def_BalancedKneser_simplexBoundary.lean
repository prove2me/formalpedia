-- Prove2me | Definitions.Def_BalancedKneser_simplexBoundary
-- name    : BalancedKneser_simplexBoundary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:12.186017+00:00
-- url     : https://prove2.me/theorems/859851bd-b09e-4438-ae60-aef0417f4727
-- title:
--   Boundary $\partial\Delta^{q-1}$ of the simplex on $q$ colors
-- statement:
--   For $q\ge 1$, let $\Delta^{q-1}$ be the simplex on the vertex set $[q]$ (the colors). Its **boundary** $\partial\Delta^{q-1}$ is the simplicial complex whose faces are the nonempty proper subsets of $[q]$:
--   $$
--   \partial\Delta^{q-1}=\{\tau\subseteq[q]:\ \tau\neq\emptyset,\ \tau\neq[q]\}.
--   $$
--   Its realization is a sphere of dimension $q-2$; Lemma 3.1 uses $q=d+2$, where $\partial\Delta^{d+1}\cong S^d$.
--
--   **Formalization Note** The colors are $\mathrm{Fin}\,q$.
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, §3.1, p.5 (PDF p.7): ∂∆⁴ and its faces; Lemma 3.1, p.6 (PDF p.8): ∂∆^{d+1}

import Mathlib

namespace BalancedKneser

/-- **Boundary of a simplex** `∂∆^{q-1}` on the vertex set `[q]` (Alipour–Jafari,
arXiv:2611.04486v1, §3.1, p.5 (PDF p.7): "∆4 is the simplex on the five colors; its boundary
consists of all proper subsets of those colors"): the nonempty proper subsets of `Fin q`. Its
realization is a sphere of dimension `q - 2`; Lemma 3.1 uses `q = d + 2`, i.e. `∂∆^{d+1}`. -/
def simplexBoundary (q : ℕ) : Set (Finset (Fin q)) :=
  {τ | τ.Nonempty ∧ τ ≠ Finset.univ}

end BalancedKneser


