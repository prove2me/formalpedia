-- Prove2me | Definitions.Def_LowRankMEG_megStep
-- name    : LowRankMEG_megStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:30.473389+00:00
-- url     : https://prove2.me/theorems/0ae45cc8-d70f-4052-b3e6-78ff8fb87a2e
-- title:
--   The exact MEG update $Z_+$
-- statement:
--   For a positive definite $Z\in\mathcal S_n$, a symmetric $D$ and a step size $\eta>0$, the **Matrix Exponentiated Gradient update** is
--   $$
--   Z_+=\frac1b\exp\bigl(\log(Z)-\eta D\bigr),\qquad b:=\operatorname{Tr}\bigl(\exp(\log(Z)-\eta D)\bigr).
--   $$
--   Eq. (6) is the case $D=\nabla f(Z)$, and Eq. (7) the case $D=\widehat\nabla$. This is the step that the low-rank method approximates.
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Eqs. (6), (7), p.6

import Mathlib
import Definitions.Def_LowRankMEG_mlog
import Definitions.Def_LowRankMEG_mexp

namespace LowRankMEG

/-- **The exact MEG update** `Z₊ = (1/b) exp(log(Z) − ηD)`, `b := Tr(exp(log(Z) − ηD))`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Eqs. (6) and (7), p.6: Eq. (6) is `D = ∇f(Z)`, Eq. (7) is `D = ∇̂`.

**Formalization Note.** `D` is any matrix here; every statement takes it symmetric. -/
noncomputable def megStep {n : ℕ} (Z D : Matrix (Fin n) (Fin n) ℝ) (η : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (mexp (mlog Z - η • D)).trace⁻¹ • mexp (mlog Z - η • D)

end LowRankMEG


