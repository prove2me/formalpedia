-- Prove2me | Definitions.Def_MaskingHardness_constraintR
-- name    : MaskingHardness_constraintR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:49:27.576611+00:00
-- url     : https://prove2.me/theorems/4c1331e2-54ef-45ea-910b-5314961a8a10
-- title:
--   Indistinguishability constraint functional $R(a)$ (Definition 3.1)
-- statement:
--   Let $\mathcal D$ be a distribution over $\mathcal X\times\mathcal Y$, $\mathcal C=\{c_i\}$ a finite collection of functions $\mathcal X\to\mathbb R^k$ and $\varepsilon\ge0$. For $a:\mathcal X\times\mathcal Y\to\mathbb R^k$,
--
--   $$
--   R(a)=\inf_{\lambda\in\mathbb R^{\mathcal C}}\ \varepsilon\|\lambda\|_1\quad\text{such that}\quad \Pr_{\mathcal D}\Bigl[a(x,y)=\sum_i\lambda_i c_i(x)\Bigr]=1 ,
--   $$
--
--   with $R(a)=+\infty$ when no such $\lambda$ exists, i.e. when $a\notin\mathrm{span}(\mathcal C)$ up to $\mathcal D$-null pairs. $R$ is the convex functional of the indistinguishability constraint.
--
--   **Formalization Note** The infimum is `sInf` of a set of extended reals, so the empty infimum is $+\infty$. "$\Pr[\dots]=1$" is "for every $(x,y)$ with $\mathcal D(x,y)>0$". $\|\lambda\|_1=\sum_i|\lambda_i|$.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 3.1, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_MaskingHardness_combo

namespace MaskingHardness

/-- **The indistinguishability constraint functional `R`** (Gopalan–Prabhakaran–Tankala,
*Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d,
Definition 3.1, printed p.20 = PDF p.22): for `a : X × Y → ℝᵏ`,
`R(a) = inf_{λ ∈ ℝ^C} ε ‖λ‖₁ such that Pr[a(x, y) = ∑ᵢ λᵢ cᵢ(x)] = 1`,
with `R(a) = +∞` when no such `λ` exists.

**Formalization Note** The infimum is `sInf` in `EReal` (so the empty infimum is `+∞`);
"`Pr[…] = 1`" is "for every `(x, y)` with `D(x, y) > 0`"; `‖λ‖₁ = ∑ᵢ |λᵢ|`. -/
noncomputable def constraintR {X Y ι : Type*} [Fintype ι] {k : ℕ} (D : X → Y → ℝ)
    (c : ι → X → Fin k → ℝ) (ε : ℝ) (a : X → Y → Fin k → ℝ) : EReal :=
  sInf {v : EReal | ∃ lam : ι → ℝ, (∀ x y, 0 < D x y → a x y = combo c lam x) ∧
    v = ((ε * ∑ i, |lam i| : ℝ) : EReal)}

end MaskingHardness


