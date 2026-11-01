-- Prove2me | Definitions.Def_LowRankMEG_IsLowRankUpdate
-- name    : LowRankMEG_IsLowRankUpdate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:44.270274+00:00
-- url     : https://prove2.me/theorems/2131ec0f-baef-4ce2-8318-247b1c5d60ef
-- title:
--   The low-rank MEG update (9), Definition 2
-- statement:
--   Let $Y:=\exp(\log(X)-\eta D)$, and let $Y^r=V^r\Lambda^r{V^r}^\top$ collect its top $r$ eigenpairs, with $a:=\sum_{i=1}^r\lambda_i(Y)$ its trace. The **low-rank MEG update** is
--   $$
--   X_+:=(1-\varepsilon)\frac{Y^r}{a}+\frac{\varepsilon}{n-r}\bigl(I-V^r{V^r}^\top\bigr).
--   $$
--   It keeps the top $r$ eigenpairs of the exact step and flattens the rest to one small value, so that one rank-$r$ eigen-computation suffices.
--
--   **Formalization Note** The proposition holds of $X_+$ for some $V^r\in\mathbb R^{n\times r}$ with orthonormal columns that are eigenvectors of $Y$ for $\lambda_1(Y),\dots,\lambda_r(Y)$ in this order, so that any valid choice at a tie $\lambda_r(Y)=\lambda_{r+1}(Y)$ is covered. Definition 2 has $D=\nabla f(X)$; (9) is also used with $D=\widehat\nabla$.
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Definition 2, Eq. (9), p.8

import Mathlib
import Definitions.Def_LowRankMEG_lam
import Definitions.Def_LowRankMEG_mlog
import Definitions.Def_LowRankMEG_mexp
open Matrix

namespace LowRankMEG

/-- **The low-rank MEG update, Definition 2**: `Xp` is
`X₊ := (1 − ε) Yʳ/a + (ε/(n−r)) (I − VʳVʳᵀ)` for `Y := exp(log(X) − ηD)`, its top-`r` eigenpairs
`Yʳ = VʳΛʳVʳᵀ`, and `a := ∑_{i=1}^r λ_i(Y)`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Definition 2, Eq. (9), p.8. Definition 2 has `D = ∇f(X)`; Lemma 2 also applies (9) with
`D = ∇̂`, as in Algorithm 2, p.9.

**Formalization Note.** `Vʳ` is any `n × r` matrix with orthonormal columns that are eigenvectors of
`Y` for `λ_1(Y), …, λ_r(Y)` in this order, so at a tie `λ_r(Y) = λ_{r+1}(Y)` every valid choice is
allowed. The index `i : Fin r` is 0-based, hence `lam Y (i + 1)`. `n − r` is computed in `ℝ`. The
constraints on `X`, `η`, `ε`, `r` are hypotheses of the statements. -/
def IsLowRankUpdate {n : ℕ} (X D : Matrix (Fin n) (Fin n) ℝ) (η ε : ℝ) (r : ℕ)
    (Xp : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  let Y := mexp (mlog X - η • D)
  ∃ V : Matrix (Fin n) (Fin r) ℝ,
    Vᵀ * V = 1 ∧
    Y * V = V * diagonal (fun i : Fin r => lam Y ((i : ℕ) + 1)) ∧
    Xp = (1 - ε) • ((∑ i ∈ Finset.Icc 1 r, lam Y i)⁻¹ •
          (V * diagonal (fun i : Fin r => lam Y ((i : ℕ) + 1)) * Vᵀ))
        + (ε / ((n : ℝ) - r)) • (1 - V * Vᵀ)

end LowRankMEG


