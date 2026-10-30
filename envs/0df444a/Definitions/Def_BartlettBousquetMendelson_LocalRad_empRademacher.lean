-- Prove2me | Definitions.Def_BartlettBousquetMendelson_LocalRad_empRademacher
-- name    : BartlettBousquetMendelson_LocalRad_empRademacher
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:56:43.488428+00:00
-- url     : https://prove2.me/theorems/5dd7e686-f336-4467-974c-f7a7c8964b33
-- title:
--   Empirical Rademacher average $\mathbb E_\sigma R_n\mathcal G$
-- statement:
--   Let $\sigma_1,\dots,\sigma_n$ be independent **Rademacher** signs, $\Pr(\sigma_i=1)=\Pr(\sigma_i=-1)=1/2$, independent of the sample. For a class $\mathcal G$ of functions and a sample $X_1,\dots,X_n$, write $R_ng=\frac1n\sum_i\sigma_ig(X_i)$ and $R_n\mathcal G=\sup_{g\in\mathcal G}R_ng$. The **empirical (conditional) Rademacher average** is the expectation over the signs only:
--
--   $$
--   \mathbb E_\sigma R_n\mathcal G=\frac1n\,\mathbb E\Big(\sup_{g\in\mathcal G}\sum_{i=1}^n\sigma_ig(X_i)\,\Big|\,X_1,\dots,X_n\Big)=\frac1{2^n}\sum_{s\in\{\pm1\}^n}\ \sup_{g\in\mathcal G}\frac1n\sum_{i=1}^n s_ig(X_i).
--   $$
--
--   It measures how well the class correlates with random signs on the observed sample, and it can be computed from the data.
--
--   **Formalization Note** Sign vectors are `Fin n → Bool` (`true` ↦ $+1$, `false` ↦ $-1$), averaged exactly. The supremum is Lean's real supremum: it is the paper's for classes bounded on the sample (all classes used are), and $0$ for the empty class, where the paper's supremum is $-\infty$.
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), §1, p. 3 (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib

namespace BartlettBousquetMendelson.LocalRad

/-- **Empirical (conditional) Rademacher average `E_σ Rₙ G`.**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), §1, p. 3: "Rnf = (1/n) Σ_{i=1}^n σif(Xi). For a class F, set RnF = sup_{f∈F} Rnf. Define Eσ
to be the expectation with respect to the random variables σ1,...,σn, conditioned on all of the
other random variables. … the empirical (or conditional) Rademacher averages of F are
EσRnF = (1/n) E(sup_{f∈F} Σ_{i=1}^n σif(Xi) | X1,...,Xn)."

For a sample `ω : Fin n → X`, `empRademacher n G ω` averages over all `2ⁿ` sign vectors
`s : Fin n → Bool` (sign `σᵢ = +1` if `s i`, `−1` otherwise, each vector with probability
`2⁻ⁿ`) the supremum over `g ∈ G` of `(1/n) Σᵢ σᵢ g(ω i)`.

**Formalization Note.** The Rademacher variables are independent and uniform on `{−1, +1}`, so
`E_σ` is exactly the uniform average over `Fin n → Bool`. The supremum is Lean's real `⨆`:
it equals the paper's supremum when the family is bounded above (every class of the mission is
bounded, or boundedness is assumed); it is `0` for the empty class, where the paper's supremum
is `−∞`. -/
noncomputable def empRademacher {X : Type*} (n : ℕ) (G : Set (X → ℝ)) (ω : Fin n → X) : ℝ :=
  (1 / 2 ^ n : ℝ) * ∑ s : Fin n → Bool,
    ⨆ g : G, (1 / (n : ℝ)) * ∑ i, (if s i then (1 : ℝ) else -1) * g.1 (ω i)

end BartlettBousquetMendelson.LocalRad


