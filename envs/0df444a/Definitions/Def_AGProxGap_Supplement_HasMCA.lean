-- Prove2me | Definitions.Def_AGProxGap_Supplement_HasMCA
-- name    : AGProxGap_Supplement_HasMCA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:15:23.741207+00:00
-- url     : https://prove2.me/theorems/a3dc004c-a75d-4141-8e2d-b9da57d106cc
-- title:
--   Mutual correlated agreement $(\ell,e,\sigma)$-MCA
-- statement:
--   A code $C\subseteq\mathbb F_q^n$ has **$(\ell,e,\sigma)$-MCA** (mutual correlated agreement) if for all $u_0,\dots,u_\ell\in\mathbb F_q^n$,
--   $$\Pr_{z\in\mathbb F_q}\Bigl[\exists A\subseteq[n],\ |A|\ge n-e:\ r(z)|_A\in C|_A\ \text{and}\ [u_0,\dots,u_\ell]|_A\notin C^{\ell+1}|_A\Bigr]\le\sigma,$$
--   where $r(z)=\sum_{j}z^ju_j$ and $z$ is uniform on $\mathbb F_q$. Equivalently, the set of parameters with an MCA-bad $e$ agreement witness has at most $\sigma q$ elements.
--
--   MCA implies correlated agreement without slack (Remark 2.5); Theorem 4.1 proves it for one-point AG codes up to the Johnson radius.
--
--   **Formalization Note** The probability is $|S|/q$ with $S$ the set of MCA-bad parameters and $q=|\mathbb F_q|$; the inequality is $\le\sigma$, as in Definition 2.4.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Definition 2.4, p.14

import Mathlib
import Definitions.Def_AGProxGap_Supplement_mcaBadSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AGProxGap.Supplement

/-- **Mutual correlated agreement** `(ℓ, e, σ)`-MCA (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), Definition 2.4, p.14: "We say that C
has (ℓ, e, σ)-MCA if, for every u_0, . . . , u_ℓ ∈ F_q^n,
Pr_{z∈F_q}[∃A ⊆ [n], |A| ≥ n − e : r(z)|_A ∈ C|_A and [u_0, . . . , u_ℓ]|_A ∉ C^{ℓ+1}|_A] ≤ σ").

**Formalization Note** The probability is over the uniform distribution on all of `F_q`
(§2.2, p.13), so it is `|mcaBadSet C u e| / q` with `q = Fintype.card K`. The inequality is
`≤ σ` (Definition 2.4), not the strict `> σ` hypothesis of correlated agreement. `σ` is real
and its range `0 ≤ σ ≤ 1` is not built in. -/
def HasMCA {K : Type*} [Field K] [Fintype K] {n : ℕ} (C : Set (Fin n → K)) (ℓ e : ℕ)
    (σ : ℝ) : Prop :=
  ∀ u : Fin (ℓ + 1) → Fin n → K,
    ((mcaBadSet C u e).card : ℝ) / (Fintype.card K : ℝ) ≤ σ

end AGProxGap.Supplement


