-- Prove2me | Definitions.Def_MultiThinkCoT_hboost
-- name    : MultiThinkCoT_hboost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:42:13.215306+00:00
-- url     : https://prove2.me/theorems/b46acb26-5d4a-45d9-8eb3-83ca844ebd89
-- title:
--   The class $H_{\mathrm{boost}}(K)$ of weighted majorities
-- statement:
--   For $K\in\mathbb N$, the class of **weighted majorities** of $K$ end-to-end maps is
--
--   $$
--   H_{\mathrm{boost}}(K)=\Big\{x\mapsto\arg\max_{b\in\{0,1\}}\sum_{k=1}^K\alpha_k\,\mathbf 1\big[f_k^{\mathrm{e2e}\text{-}T}(x)=b\big]\ :\ f_1,\dots,f_K\in\mathcal F,\ \alpha_1,\dots,\alpha_K>0\Big\},
--   $$
--
--   with ties broken in favour of $1$. The output of Algorithm 1 lies in this class, and uniform convergence over it (Lemma F.4) turns zero training error into small population error.
--
--   **Formalization Note** The argmax with ties to $1$ is $1$ exactly when the weight voting for $1$ is at least the weight voting for $0$. For $K=0$ the class contains only the constant $1$.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Appendix F, eq. (26), p.55, ties p.56 (PDF pp.55–56)

import Mathlib
import Definitions.Def_MultiThinkCoT_e2e

namespace MultiThinkCoT

/-!
# The class `H_boost(K)` of weighted majorities (26)

N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers*,
arXiv:2604.24737 (held version, sha256 e663a640…), Appendix F, eq. (26), p.55, ties p.56
(PDF pp.55–56).

`H_boost(K) = {x ↦ argmax_{b ∈ {0,1}} Σ_{k=1}^K α_k 1[f_k^{e2e-T}(x) = b] : f_1, …, f_K ∈ F,
α_1, …, α_K ∈ ℝ_{>0}}`, "with breaking ties in favor +1".

**Formalization Note.** The argmax with ties to `1` is `true` exactly when the weight voting for
`1` is at least the weight voting for `0`. Members are functions on the domain `X`. For `K = 0`
the class is the single constant-`1` function.
-/

/-- (26) Weighted majorities of `K` end-to-end maps of members of `F`, positive weights, ties to 1. -/
def hboost (F : Set Gen) (T : ℕ) (X : Set (List Bool)) (K : ℕ) : Set (X → Bool) :=
  {h | ∃ (f : Fin K → Gen) (α : Fin K → ℝ), (∀ k, f k ∈ F) ∧ (∀ k, 0 < α k) ∧
    ∀ x : X, h x = decide ((∑ k, if e2e (f k) T x = false then α k else 0) ≤
      ∑ k, if e2e (f k) T x = true then α k else 0)}

end MultiThinkCoT


