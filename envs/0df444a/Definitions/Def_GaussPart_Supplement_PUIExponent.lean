-- Prove2me | Definitions.Def_GaussPart_Supplement_PUIExponent
-- name    : GaussPart_Supplement_PUIExponent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:02:48.576964+00:00
-- url     : https://prove2.me/theorems/8420976f-4ade-41f0-9b17-923a7992a007
-- title:
--   The Gaussian PUI learning exponent $m^*(\epsilon,\Delta,\sigma,q)$
-- statement:
--   Let $\mathcal F$ be a class of Boolean functions on $\mathbb R^d$ and $D=\mathcal N(0,I_d)$. The **Gaussian PUI learning exponent** $m^*(\epsilon,\Delta,\sigma,q)\in\mathbb N\cup\{\infty\}$ is the least integer $k\ge1$ such that for every $f\in\mathcal F$ and every distribution $D^*$ that is $(q,\sigma)$-smooth with respect to $D$ with
--   $$
--   D^*(f=-1)\ge\epsilon\quad\text{and}\quad D^*(f=1)>0,
--   $$
--   the positive conditional $D^*_+=D^*\mid\{f=1\}$ does **not** match the first $k$ directional moments of $\mathcal N(0,I_d)$ with slack $\Delta$ (Definition 2.2: for every unit $v\in\mathbb R^d$ and $1\le i\le k$, $|\mathbb E_{D^*_+}[(v\cdot x)^i]-\mathbb E_{\mathcal N(0,I_d)}[(v\cdot x)^i]|\le\Delta$). If no such $k$ exists, $m^*=\infty$.
--
--   The exponent governs the dimension dependence $d^{m^*}$ of PUI learning (Theorem 5.3) and of reliable learning (Theorem 6.2).
--
--   **Formalization Note** Moment matching is the published `MatchesMoments` with $W=\mathbb R^d$; $D^*_+$ is Mathlib's conditional measure, a probability measure because $D^*(f=1)>0$.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Definition 5.2, p.44 (PDF p.46); Definition 2.2, p.13

import Mathlib
import Definitions.Def_GaussPart_Cell
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_MatchesMoments

open MeasureTheory ProbabilityTheory

namespace GaussPart

namespace Supplement

/-- **Definition 5.2** (Gaussian PUI learning exponent), arXiv:2611.05264 (sha256 7e0ca6d4…), p.44
(PDF p.46): `m∗(ϵ, Δ, σ, q)` is the minimum integer `k ∈ ℤ₊` such that, for every `f ∈ F` and every
distribution `D∗` that is `(q, σ)`-smooth with respect to `N(0, I_d)` with `D∗(f = −1) ≥ ϵ` and
`D∗(f = 1) > 0`, the positive conditional `D∗₊ := D∗ | {f = 1}` does not match the first `k` moments
of `N(0, I_d)` with slack `Δ` (Definition 2.2); `m∗ = ∞` if no such integer exists.

**Formalization Note.** The value is in `ℕ∞` (`sInf ∅ = ⊤`). Moment matching is the published
`MatchesMoments` with `W = ⊤` (every unit `v ∈ ℝᵈ`, degrees `1, …, k`), and `D∗₊` is
`ProbabilityTheory.cond`, a probability measure because `D∗(f = 1) > 0`. -/
noncomputable def mStar {d : ℕ} (F : Set (Vec d → ℝ)) (ε Δ σ q : ℝ) : ℕ∞ :=
  sInf ((fun m : ℕ => (m : ℕ∞)) '' {m : ℕ | 1 ≤ m ∧ ∀ f ∈ F, ∀ Ds : Measure (Vec d),
    IsProbabilityMeasure Ds → IsSmooth (stdGaussian (Vec d)) Ds q σ →
    ENNReal.ofReal ε ≤ Ds {x | f x = -1} → 0 < Ds {x | f x = 1} →
    ¬ MatchesMoments (stdGaussian (Vec d)) (cond Ds {x | f x = 1}) ⊤ m Δ})

end Supplement

end GaussPart


