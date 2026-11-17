-- Prove2me | Definitions.Def_SharpConsist_Supplement_HasCurvatureAtMost
-- name    : SharpConsist_Supplement_HasCurvatureAtMost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:21:35.410277+00:00
-- url     : https://prove2.me/theorems/33d35c8e-0a2b-47b4-a112-d368dc7b84a4
-- title:
--   Total curvature at most $\vartheta$
-- statement:
--   A set function $f$ on a finite ground set $V$ has **total curvature at most $\vartheta$** if
--   $$f(S\cup\{i\})-f(S)\ \ge\ (1-\vartheta)\,f(\{i\})\qquad(S\subseteq V,\ i\in V\setminus S).\tag{8.1}$$
--   For monotone $f$ the bound $\vartheta=1$ imposes no restriction, while $\vartheta=0$ makes $f$ modular. The paper's curvature results use $\vartheta\in[0,1]$, known to the algorithm, with the bound holding on the entire stream including its final element.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §1.1, p.3; §8, Eq. (8.1), p.24

import Mathlib

namespace SharpConsist.Supplement

/-- **Total curvature at most `ϑ`** [Conforti–Cornuéjols]. Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §1.1, p.3 and
Eq. (8.1), p.24: `f(i | S) ≥ (1 − ϑ) f({i})` for all `S ⊆ V` and `i ∈ V \ S`.

**Formalization Note.** The ground set `V` is the finite type; the bound is imposed on every subset
and every element of `V` ("over the entire stream", including the final element). The range
`ϑ ∈ [0, 1]` is a hypothesis of the theorems that use the predicate, not part of it. -/
def HasCurvatureAtMost {V : Type} [Fintype V] [DecidableEq V] (ϑ : ℝ) (f : Finset V → ℝ) :
    Prop :=
  ∀ (S : Finset V) (i : V), i ∉ S → (1 - ϑ) * f {i} ≤ f (insert i S) - f S

end SharpConsist.Supplement


