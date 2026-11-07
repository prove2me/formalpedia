-- Prove2me | Definitions.Def_CalibeatBandit_fixedPointSol
-- name    : CalibeatBandit_fixedPointSol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:32.690142+00:00
-- url     : https://prove2.me/theorems/07624057-be4b-4492-9b7e-35ae28de92c0
-- title:
--   The solution $x=(1-\lambda)(I-\lambda M^{\mathrm{SR}})^{-1}M^{\mathrm{Rec}}e_J$ of (3.1)
-- statement:
--   For a mixing weight $\lambda$, post-processing matrices $M^{\mathrm{SR}},M^{\mathrm{Rec}}$ and a recommended action $J$, the fixed-point equation (3.1) reads
--   $$(I-\lambda M^{\mathrm{SR}})\,x=(1-\lambda)\,M^{\mathrm{Rec}}e_J ,$$
--   where $e_J$ is the $J$-th standard basis vector. This definition is its explicit solution $x=(1-\lambda)(I-\lambda M^{\mathrm{SR}})^{-1}M^{\mathrm{Rec}}e_J$.
--
--   When $0\le\lambda<1$ and $M^{\mathrm{SR}}$, $M^{\mathrm{Rec}}$ are column-stochastic, $I-\lambda M^{\mathrm{SR}}$ is invertible, so this is the unique solution of (3.1), and it is a probability vector. The algorithm's $\lambda_t$ always lies in $(0,1)$.
--
--   **Formalization Note** `Matrix.inv` is used; the explicit formula makes the algorithm a concrete function of its history (no choice of a solution).
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §3, eq. (3.1), p.9 (PDF 9); §3.2 item 1, p.10 (PDF 10)

import Mathlib

set_option autoImplicit false

namespace CalibeatBandit

open Matrix

/-- **The solution of the fixed-point equation (3.1).** For a mixing weight `λ`, post-processing
matrices `M^SR`, `M^Rec` and a recommended action `J`, equation (3.1) reads
`(I − λ M^SR) x = (1 − λ) M^Rec e_J`. This is its explicit solution
`x = (1 − λ) (I − λ M^SR)⁻¹ M^Rec e_J`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §3 "Choosing a
mixed strategy", eq. (3.1), p.9, and §3.2 item 1, p.10 ("Denote the mixed strategy solving
Equation (3.1) by x_t").

**Formalization Note.** `e_J` is `Pi.single J 1`, `⁻¹` is `Matrix.inv`. When `0 ≤ λ < 1` and
`M^SR` is column-stochastic, `I − λ M^SR` is invertible, so this is the unique solution of (3.1)
and it lies in the simplex; the algorithm's `λ_t` always lies in `(0, 1)`. Choosing the explicit
formula (instead of an arbitrary choice of solution) makes the algorithm a concrete measurable
function of the history. -/
noncomputable def fixedPointSol {K : ℕ} (lam : ℝ) (MSR MRec : Matrix (Fin K) (Fin K) ℝ)
    (J : Fin K) : Fin K → ℝ :=
  (1 - lam) • ((1 - lam • MSR)⁻¹ *ᵥ (MRec *ᵥ Pi.single J 1))

end CalibeatBandit


