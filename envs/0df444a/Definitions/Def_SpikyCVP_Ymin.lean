-- Prove2me | Definitions.Def_SpikyCVP_Ymin
-- name    : SpikyCVP_Ymin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:42:20.595405+00:00
-- url     : https://prove2.me/theorems/fddbfdf4-995b-48c3-867a-08f45402fbcd
-- title:
--   Minimizer set $Y(s)$, gap $\Delta_{j,r}(s)$ and the constant $C_p$
-- statement:
--   Let $\mathcal L=\mathcal L(B)$, let $t$ be a target and $v^\ast$ a closest vector, and let $M=2\mathcal L+v^\ast-t$. For widths $s$, $Y(s)\subseteq M$ is the **set of minimizers** of $\sum_k y_k^2/s_k^2$ over $y\in M$. For $u\in\mathbb R$ (in the paper $u=v^\ast_j-t_j$), $r>0$ and $s>0$,
--
--   $$\Delta_{j,r}(s)=\frac{\pi r^p u^2}{s^2}+\Big(1-\frac p2\Big)\Big(\frac{p s^2}{2\pi r^p}\Big)^{p/(2-p)}-|u|^p,$$
--
--   the gap between the quadratic majorant of $|z|^p$ at $z=u$ and $|u|^p$. Finally
--
--   $$C_p=2\Big(\frac{2048}{p-1}\Big)^{2/p}.$$
--
--   $Y(s)$ is what one call of the Euclidean subroutine returns in the sampled metric; $C_p$ is the exponent of the success probability $2^{-C_pn}$ of one sample.
--
--   **Formalization Note** For a width vector with a zero coordinate Lean's $y_k^2/0$ is $0$; such widths lie outside the support of every posterior.
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), §4, pp.18–19 (PDF pp.20–21)

import Mathlib
import Definitions.Def_SpikyCVP_latt

open Real

namespace SpikyCVP

/-- `Y(s) ⊆ M`, the set of minimizers of `Σ_k y_k²/s_k²` over the coset `M := 2L + v∗ − t`. Aggarwal,
Morolia, *How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem*,
STOC 2027 submission (manuscript sha256 535c3bcc…), §4, p.18–19 (PDF pp.20–21).

**Formalization Note.** `v` plays the role of `v∗`; every statement using `Ymin` assumes `v` is a closest
vector. For a width vector with a zero coordinate, Lean's `y_k²/0 = 0`; such `s` lie outside the support
of every posterior. -/
def Ymin {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (v t s : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | y ∈ twoLPlus B (v - t) ∧
    ∀ y' ∈ twoLPlus B (v - t), ∑ k, y k ^ 2 / s k ^ 2 ≤ ∑ k, y' k ^ 2 / s k ^ 2}

/-- `∆j,r(s) := πr^p u²/s² + (1 − p/2)(ps²/(2πr^p))^{p/(2−p)} − |u|^p`, with `u = v∗_j − t_j` (proof of
Lemma 4.2, p.19). -/
noncomputable def Delta (p r u s : ℝ) : ℝ :=
  π * r ^ p * u ^ 2 / s ^ 2 + (1 - p / 2) * (p * s ^ 2 / (2 * π * r ^ p)) ^ (p / (2 - p)) - |u| ^ p

/-- `Cp := 2(2048/(p − 1))^{2/p}` (§4, p.18). -/
noncomputable def Cp (p : ℝ) : ℝ := 2 * (2048 / (p - 1)) ^ (2 / p)

end SpikyCVP


