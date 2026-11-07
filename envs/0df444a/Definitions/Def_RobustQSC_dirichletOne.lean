-- Prove2me | Definitions.Def_RobustQSC_dirichletOne
-- name    : RobustQSC_dirichletOne
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:34.940188+00:00
-- url     : https://prove2.me/theorems/98cd6c17-d444-44d0-9482-9c5e80360c24
-- title:
--   The Porter–Thomas law $\mathrm{Dirichlet}(\vec 1)$ in the normalized exponential model
-- statement:
--   On a finite set $\iota$, the flat Dirichlet law $\mathrm{Dirichlet}(\vec1)$ is the law of
--
--   $$
--   \mu(x)=\frac{Z_x}{\sum_y Z_y},\qquad (Z_x)_{x\in\iota}\ \text{i.i.d. }\mathrm{Exp}(1).
--   $$
--
--   For $\iota=\{0,1\}^n$ this is the law $\boldsymbol\mu$ of $\mu_f$ for a Haar-random $f$, written $\mu\sim\boldsymbol\mu$ in the paper.
--
--   **Formalization Note** The instance $\alpha\equiv1$ of the published `NestedCRP.dirichletMeasure` (normalized independent $\mathrm{Gamma}(\alpha_i,1)$ variables), with $\mathrm{Gamma}(1,1)=\mathrm{Exp}(1)$. It is a law on functions $\iota\to\mathbb R$; the normalization is undefined only on a null event.
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Lemma 1, p.19; proof of Proposition 13, p.49 (normalized exponential model)

import Definitions.Def_NestedCRP_dirichletMeasure

namespace RobustQSC

open MeasureTheory

/-- The flat Dirichlet law `Dirichlet(1⃗)` on the probability simplex of a finite set `ι`, in the
normalized exponential model: `μ(x) = Z_x / Σ_y Z_y` with `(Z_x)_{x ∈ ι}` i.i.d. `Exp(1)`.

For `ι = {0,1}ⁿ` this is the law `𝛍` of the measure `μ_f(x) = |f(x)|²` of a Haar-random unit
vector `f` (the Porter–Thomas measure), written `μ ∼ 𝛍` in the paper.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles
for total influence*, arXiv:2607.27184 (sha256 09d2692e…), Lemma 1, p.19 ("Let µ be
Dirichlet(⃗1) on N = 2^n coordinates"), proof of Proposition 13, p.49 ("Let us use a normalized
exponential model for µ. That is, define Z_x … iid Exp(1) and let µ(x) = Z_x/(Σ_y Z_y)"),
Proposition 19, p.79.

**Formalization Note.** The instance `α ≡ 1` of the published `NestedCRP.dirichletMeasure`, the
law of the normalized independent `Gamma(α_i, 1)` vector; `Gamma(1, 1)` is `Exp(1)` (Mathlib's
`expMeasure 1` is by definition `gammaMeasure 1 1`). A law on functions `ι → ℝ`. The normalization
is undefined only on the null event `Σ_y Z_y = 0` (Lean value `0`). -/
noncomputable def dirichletOne (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  NestedCRP.dirichletMeasure fun _ : ι => 1

/-! ### Sanity tests -/

/-- `dirichletOne` is literally the normalized exponential model of p.49. -/
example (ι : Type*) [Fintype ι] :
    dirichletOne ι =
      (Measure.pi fun _ : ι => ProbabilityTheory.expMeasure 1).map fun Z x => Z x / ∑ y, Z y :=
  rfl

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (dirichletOne ι) := by
  have : IsProbabilityMeasure (ProbabilityTheory.gammaMeasure 1 1) :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure one_pos one_pos
  unfold dirichletOne NestedCRP.dirichletMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

end RobustQSC


