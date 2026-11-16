-- Prove2me | Definitions.Def_MaskingHardness_Supplement_IsSurrogate
-- name    : MaskingHardness_Supplement_IsSurrogate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:29:03.219833+00:00
-- url     : https://prove2.me/theorems/48af21aa-4898-4092-8886-5fcc09fb8950
-- title:
--   $\beta$-surrogate loss (Definition 1.14)
-- statement:
--   Let $\mathcal Y$ and $\mathcal A$ be sets, $\mathcal B$ a finite set and $\beta\ge0$. A loss $\ell_{\mathcal A}:\mathcal Y\times\mathcal A\to\mathbb R$ is a **$\beta$-surrogate** for a loss $\ell_{\mathcal B}:\mathcal Y\times\mathcal B\to\mathbb R$ if there is a rounding function $R:\mathcal A\to\Delta(\mathcal B)$ such that for all $y\in\mathcal Y$ and $a\in\mathcal A$,
--
--   $$
--   \ell_{\mathcal A}(y,a)\ \ge\ \beta\cdot\mathbb E_{b\sim R(a)}\big[\ell_{\mathcal B}(y,b)\big].
--   $$
--
--   A surrogate transfers hardness: if $\ell_{\mathcal B}$ is hard to minimize, so is $\ell_{\mathcal A}$, up to the factor $\beta$.
--
--   **Formalization Note** $\Delta(\mathcal B)$ is `stdSimplex ℝ B`, the expectation is $\sum_b R(a)_b\,\ell_{\mathcal B}(y,b)$; the finiteness of $\mathcal B$ is a `Fintype` instance.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 1.14, p.8 (PDF p.10)

import Mathlib

namespace MaskingHardness.Supplement

/-- **`β`-surrogate loss** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 1.14, printed p.8 = PDF p.10): a loss
`ℓA : Y × A → ℝ` is a `β`-surrogate for a loss `ℓB : Y × B → ℝ` (with `B` finite) if there is
a rounding function `R : A → Δ(B)` such that for all `y ∈ Y` and `a ∈ A`,
`ℓA(y, a) ≥ β · E_{b ∼ R(a)}[ℓB(y, b)]`.

**Formalization Note** `Δ(B)` is `stdSimplex ℝ B` (nonnegative weights summing to `1`) and
`E_{b ∼ R(a)}[ℓB(y, b)] = ∑_b R(a)_b ℓB(y, b)`. The finiteness of `B` is the instance
`[Fintype B]`. -/
def IsSurrogate {Y A B : Type*} [Fintype B] (β : ℝ) (ℓA : Y → A → ℝ) (ℓB : Y → B → ℝ) : Prop :=
  ∃ R : A → B → ℝ, (∀ a, R a ∈ stdSimplex ℝ B) ∧
    ∀ y a, β * ∑ b, R a b * ℓB y b ≤ ℓA y a

end MaskingHardness.Supplement


