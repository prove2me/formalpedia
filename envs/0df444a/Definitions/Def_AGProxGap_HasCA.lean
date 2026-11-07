-- Prove2me | Definitions.Def_AGProxGap_HasCA
-- name    : AGProxGap_HasCA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:38:35.283471+00:00
-- url     : https://prove2.me/theorems/68cb575f-a985-44d6-b5da-580da2b0abaf
-- title:
--   $(\ell,e,\sigma,\varepsilon)$-correlated agreement
-- statement:
--   Let $C\subseteq\mathbb F_q^n$ be a code, $\ell\ge 1$ and $e\ge 0$ integers, $\sigma$ a soundness parameter and $\varepsilon\ge 0$ a multiplicative slack. The code has **$(\ell,e,\sigma,\varepsilon)$-correlated agreement (CA)** if for all $u_0,\dots,u_\ell\in\mathbb F_q^n$,
--   $$
--   \Pr_{z\in\mathbb F_q}\bigl[d(r(z),C)\le e\bigr]>\sigma
--   \;\Longrightarrow\;
--   d\bigl([u_0,\dots,u_\ell],C^{\ell+1}\bigr)\le(1+\varepsilon)e ,
--   $$
--   where $r(z)=\sum_j u_jz^j$, the probability is for $z$ uniform on $\mathbb F_q$, and $C^{\ell+1}=\{[c_0,\dots,c_\ell]: c_j\in C\}$. In words: if more than a $\sigma$ fraction of the points of the curve are $e$-close to $C$, the words themselves agree with codewords $c_0,\dots,c_\ell$ on one common set of at least $n-(1+\varepsilon)e$ coordinates.
--
--   This is the property that FRI-, STIR- and WHIR-type proximity tests use to batch claims; $\sigma$ bounds their soundness error.
--
--   **Formalization Note** The probability is $|S|/q$ with $S$ = `closeSet`, $q$ = `Fintype.card`, and the inequality is strict. $d([u],C^{\ell+1})\le(1+\varepsilon)e$ is the existence of codewords at interleaved distance at most the real number $(1+\varepsilon)e$. The ranges $0\le\sigma\le 1$, $\varepsilon\ge 0$ of §2.2 are not built in; for $\sigma\ge 1$ the property holds vacuously.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Definition 2.2, p.13

import Mathlib
import Definitions.Def_AGProxGap_closeSet
import Definitions.Def_AGProxGap_interDist

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Classical

namespace AGProxGap

/-- **Correlated agreement** `(ℓ, e, σ, ε)`-CA (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), Definition 2.2, p.13): "We say that C has
(ℓ, e, σ, ε)-CA if, for every u_0, . . . , u_ℓ ∈ F_q^n, the inequality Pr_z[d(r(z), C) ≤ e] > σ
implies that d([u_0, . . . , u_ℓ], C^{ℓ+1}) ≤ (1 + ε)e."

**Formalization Note** `Pr_z` is uniform over all `z ∈ F_q` ("All probabilities over z ∈ F_q use
the uniform distribution on parameters", p.13), so `Pr_z[d(r(z), C) ≤ e] = |S| / q` with
`S = closeSet C u e` and `q = Fintype.card K`; the inequality is strict. The conclusion
`d([u], C^{ℓ+1}) ≤ (1 + ε)e` is stated as the existence of codewords `c_0, …, c_ℓ ∈ C` with
interleaved distance at most `(1 + ε)e`, a real bound. `σ` and `ε` are real; the ranges
`0 ≤ σ ≤ 1`, `ε ≥ 0` of §2.2 are not built in (the predicate is vacuous for `σ ≥ 1`). -/
def HasCA {K : Type*} [Field K] [Fintype K] {n : ℕ} (C : Set (Fin n → K)) (ℓ e : ℕ)
    (σ ε : ℝ) : Prop :=
  ∀ u : Fin (ℓ + 1) → Fin n → K,
    σ < ((closeSet C u e).card : ℝ) / (Fintype.card K : ℝ) →
      ∃ c : Fin (ℓ + 1) → Fin n → K, (∀ j, c j ∈ C) ∧ (interDist u c : ℝ) ≤ (1 + ε) * e

end AGProxGap


