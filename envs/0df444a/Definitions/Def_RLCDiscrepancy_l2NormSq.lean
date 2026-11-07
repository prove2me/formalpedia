-- Prove2me | Definitions.Def_RLCDiscrepancy_l2NormSq
-- name    : RLCDiscrepancy_l2NormSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:15.706589+00:00
-- url     : https://prove2.me/theorems/08e72bf7-79ec-4de8-ac10-8a01511043bb
-- title:
--   Squared $\ell^2$ norm $\|f\|_2^2$ (expectation measure)
-- statement:
--   For $f:\mathbb F_q^n\to\mathbb R$, with the expectation measure on $\mathbb F_q^n$,
--
--   $$
--   \|f\|_2^2=q^{-n}\sum_{x\in\mathbb F_q^n} f(x)^2 .
--   $$
--
--   It is the variance proxy in the second-moment bound of Lemma 4.4.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), §2.1, p.13

import Mathlib

namespace RLCDiscrepancy

/-- **Squared ℓ²-norm ∥f∥²_2** with the expectation measure. Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), §2.1, p.13:
"∥f∥_r = (q^{−n} ∑_{x∈F^n_q} |f(x)|^r)^{1/r}", here with r = 2 and squared:
∥f∥²_2 = q^{−n} ∑_x f(x)². -/
noncomputable def l2NormSq {F : Type*} [Field F] [Fintype F] {n : ℕ} (f : (Fin n → F) → ℝ) : ℝ :=
  (∑ x, f x ^ 2) / (Fintype.card F : ℝ) ^ n

end RLCDiscrepancy


