-- Prove2me | Definitions.Def_BartlettBousquetMendelson_LocalRad_rademacherAvg
-- name    : BartlettBousquetMendelson_LocalRad_rademacherAvg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:57:14.495904+00:00
-- url     : https://prove2.me/theorems/023c080d-ae21-4126-be3e-cd03c9d7ff81
-- title:
--   Rademacher average $\mathbb E R_n\mathcal G$
-- statement:
--   For a class $\mathcal G$, the **Rademacher average** is the expectation over both an iid sample $X_1,\dots,X_n\sim P$ and the signs:
--
--   $$
--   \mathbb ER_n\mathcal G=\mathbb E\Big[\sup_{g\in\mathcal G}\frac1n\sum_{i=1}^n\sigma_ig(X_i)\Big]=\mathbb E_{X_1,\dots,X_n\sim P}\big[\mathbb E_\sigma R_n\mathcal G\big].
--   $$
--
--   Applied to a local subclass $\{g:T(g)\le r\}$ it is the **local Rademacher average**, the complexity term of the paper's bounds.
--
--   **Formalization Note** The outer expectation is a Bochner integral over `Fin n → X` with the product measure; it is $0$ when the integrand is not integrable, so statements that assume a bound on a Rademacher average also assume the integrand measurable.
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), §1, p. 3 (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_empRademacher

open MeasureTheory

namespace BartlettBousquetMendelson.LocalRad

/-- **Rademacher average `E Rₙ G`.**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), §1, p. 3: "Let X1,...,Xn be independent random variables distributed according to P. …
The Rademacher average of F is ERnF".

`rademacherAvg P n G` is the expectation, over an iid sample `ω = (X₁, …, Xₙ)` with law
`Pⁿ = Measure.pi (fun _ => P)`, of the empirical Rademacher average `E_σ Rₙ G`
(`empRademacher`). Since `E Rₙ G = E[E_σ Rₙ G]`, this is the expectation over both the sample
and the signs.

**Formalization Note.** The expectation is the Bochner integral, which is `0` when the integrand
is not integrable; statements that put `rademacherAvg` in a hypothesis assume the integrand
measurable (Reading M), and the classes concerned are bounded, so the integrand is integrable. -/
noncomputable def rademacherAvg {X : Type*} [MeasurableSpace X] (P : Measure X) (n : ℕ)
    (G : Set (X → ℝ)) : ℝ :=
  ∫ ω, empRademacher n G ω ∂(Measure.pi fun _ : Fin n => P)

end BartlettBousquetMendelson.LocalRad


