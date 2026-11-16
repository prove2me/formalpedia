-- Prove2me | Definitions.Def_MaskingHardness_Supplement_lossEntropy
-- name    : MaskingHardness_Supplement_lossEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:29:20.225404+00:00
-- url     : https://prove2.me/theorems/c250306b-baa8-4329-844d-60c12826e28b
-- title:
--   Entropy $h(p)=\inf_a\mathbb E_{y\sim p}[\ell(y,a)]$ of a loss (Definition 1.15)
-- statement:
--   Given a finite label set $\mathcal Y$, an action set $\mathcal A$ and a loss $\ell:\mathcal Y\times\mathcal A\to\mathbb R$, the **entropy** of $\ell$ is the concave function $h:\Delta(\mathcal Y)\to\overline{\mathbb R}$,
--
--   $$
--   h(p)=\inf_{a\in\mathcal A}\ \mathbb E_{y\sim p}\big[\ell(y,a)\big]=\inf_{a\in\mathcal A}\sum_{y}p_y\,\ell(y,a).
--   $$
--
--   It is the least expected loss achievable against a label drawn from $p$, and it decides surrogacy (Theorem 1.16).
--
--   **Formalization Note** $\overline{\mathbb R}$ is `EReal`; the infimum is taken there, so $h(p)=+\infty$ when $\mathcal A=\emptyset$ and $h(p)=-\infty$ is possible.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 1.15, p.9 (PDF p.11)

import Mathlib

namespace MaskingHardness.Supplement

/-- **Entropy of a loss** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 1.15, printed p.9 = PDF p.11): for a loss
`ℓ : Y × A → ℝ` and `p ∈ Δ(Y)`, `h(p) = inf_{a ∈ A} E_{y ∼ p}[ℓ(y, a)]`, a value in `ℝ̄`.

**Formalization Note** ℝ̄ is `EReal`: the infimum is taken in `EReal`, so it is `+∞` when `A` is
empty and may be `−∞`; `E_{y∼p}[ℓ(y, a)] = ∑_y p_y ℓ(y, a)` for `Y` finite. The definition is
used for `p ∈ stdSimplex ℝ Y`. -/
noncomputable def lossEntropy {Y A : Type*} [Fintype Y] (ℓ : Y → A → ℝ) (p : Y → ℝ) : EReal :=
  ⨅ a : A, (((∑ y, p y * ℓ y a : ℝ)) : EReal)

end MaskingHardness.Supplement


