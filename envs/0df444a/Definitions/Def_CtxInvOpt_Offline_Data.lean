-- Prove2me | Definitions.Def_CtxInvOpt_Offline_Data
-- name    : CtxInvOpt_Offline_Data
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:52.065961+00:00
-- url     : https://prove2.me/theorems/6c6a453f-e6c5-4ac5-8614-7d92f6551af8
-- title:
--   (2), p. 8 — the set C(D) of unit cost vectors consistent with an offline data set
-- statement:
--   An offline data set is a finite list $\mathcal D=\{(\mathcal X_i,f_i,x^\star_i)\}_{i=1,\dots,N}$ of past feasible sets $\mathcal X_i\subseteq\mathbb R^n$, context functions $f_i:\mathbb R^n\to\mathbb R^d$ and observed actions $x^\star_i\in\mathbb R^n$. The set of cost vectors consistent with $\mathcal D$ is
--   $$C(\mathcal D)=\{c\in S^d:\ c'f_i(x^\star_i)\le c'f_i(x)\ \ \forall x\in\mathcal X_i,\ i=1,\dots,N\},$$
--   the unit costs under which every observed action is optimal for its own problem.
--
--   $C(\mathcal D)$ is the knowledge set of the offline problem: the true cost is known only to lie in it, and the regret guarantees of the paper are expressed through its uncertainty angle $\alpha(C(\mathcal D))$.
--
--   **Formalization Note** Observations are indexed by `Fin N`, i.e. $0,\dots,N-1$ for the paper's $1,\dots,N$. The definition does not require the data to be realizable; the theorems that use it state that hypothesis separately.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, pp. 7–8, §2.1, (2)

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry

namespace CtxInvOpt.Offline

/-- **(2), §2.1, p. 8.** The set of cost vectors consistent with the offline data set
`D = {(X_i, f_i, x⋆_i)}`:
`C(D) = {c ∈ S^d : c′f_i(x⋆_i) ≤ c′f_i(x), ∀ x ∈ X_i, i = 1, …, N}`.
The observations are indexed by `Fin N`, i.e. `0, …, N − 1` (the paper's `1, …, N`). -/
def consistentSet {n d N : ℕ} (Xs : Fin N → Set (EuclideanSpace ℝ (Fin n)))
    (fs : Fin N → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
    (xs : Fin N → EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {c | c ∈ unitSphere d ∧ ∀ i, ∀ x ∈ Xs i, inner ℝ c (fs i (xs i)) ≤ inner ℝ c (fs i x)}

end CtxInvOpt.Offline


