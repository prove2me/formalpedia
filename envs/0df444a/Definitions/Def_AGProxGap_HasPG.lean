-- Prove2me | Definitions.Def_AGProxGap_HasPG
-- name    : AGProxGap_HasPG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:38:36.981142+00:00
-- url     : https://prove2.me/theorems/69d17748-9a40-42aa-8284-b3061a3a60ca
-- title:
--   $(\ell,e,\sigma,\varepsilon)$-proximity gap
-- statement:
--   Let $C\subseteq\mathbb F_q^n$, $\ell\ge 1$, $e\ge 0$, $\sigma$ and $\varepsilon\ge 0$ be as for correlated agreement. The code has an **$(\ell,e,\sigma,\varepsilon)$-proximity gap (PG)** if for all $u_0,\dots,u_\ell\in\mathbb F_q^n$,
--   $$
--   \Pr_{z\in\mathbb F_q}\bigl[d(r(z),C)\le e\bigr]>\sigma
--   \;\Longrightarrow\;
--   d(r(z),C)\le(1+\varepsilon)e\ \text{ for every } z\in\mathbb F_q .
--   $$
--   Thus either every point of the curve is within distance $(1+\varepsilon)e$ of the code, or at most a $\sigma$ fraction of the parameters are $e$-close. Correlated agreement implies the proximity gap with the same parameters.
--
--   **Formalization Note** As for `HasCA`: probability $|S|/q$ over all of $\mathbb F_q$, strict inequality, real bound $(1+\varepsilon)e$.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Definition 2.1, p.13

import Mathlib
import Definitions.Def_AGProxGap_closeSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Classical

namespace AGProxGap

/-- **Proximity gap** `(ℓ, e, σ, ε)`-PG (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), Definition 2.1, p.13): "We say that C has
(ℓ, e, σ, ε)-PG if, for every u_0, . . . , u_ℓ ∈ F_q^n, the inequality Pr_z[d(r(z), C) ≤ e] > σ
implies that d(r(z), C) ≤ (1+ε)e for every z ∈ F_q."

**Formalization Note** As in `HasCA`: `Pr_z = |S| / q` over all of `F_q`, strict inequality; the
conclusion `d(r(z), C) ≤ (1 + ε)e` is the existence of a codeword at Hamming distance at most
the real number `(1 + ε)e`, for every `z ∈ F_q`. -/
def HasPG {K : Type*} [Field K] [Fintype K] {n : ℕ} (C : Set (Fin n → K)) (ℓ e : ℕ)
    (σ ε : ℝ) : Prop :=
  ∀ u : Fin (ℓ + 1) → Fin n → K,
    σ < ((closeSet C u e).card : ℝ) / (Fintype.card K : ℝ) →
      ∀ z : K, ∃ c ∈ C, (hammingDist (curve u z) c : ℝ) ≤ (1 + ε) * e

end AGProxGap


