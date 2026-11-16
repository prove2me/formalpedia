-- Prove2me | Definitions.Def_AlgoPFR_Supplement_gowersU3
-- name    : AlgoPFR_Supplement_gowersU3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:35:16.782498+00:00
-- url     : https://prove2.me/theorems/7cc07c79-360b-4991-a637-724ec4c71775
-- title:
--   The Gowers $U^3$ norm of $f:\mathbb F_2^n\to\mathbb R$
-- statement:
--   For $f:\mathbb F_2^n\to\mathbb R$, the **Gowers $U^3$ norm** is defined by
--
--   $$\|f\|_{U^3}^8=\mathbb E_{y,x_1,x_2,x_3}\prod_{\omega\in\{0,1\}^3}f(y+\omega_1x_1+\omega_2x_2+\omega_3x_3),$$
--
--   the average over independent uniform $y,x_1,x_2,x_3\in\mathbb F_2^n$, and $\|f\|_{U^3}$ is the nonnegative eighth root.
--
--   A large $U^3$ norm is the hypothesis of the inverse theorem behind quadratic Goldreich–Levin (Theorem 7.1): it says that $f$ correlates with some quadratic phase.
--
--   **Formalization Note** For real $f$ the cube average is nonnegative (it equals $\mathbb E_x\sum_\xi\hat f_x(\xi)^4$), so the real power $1/8$ is the paper's norm.
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), §3, p.16 (the Gowers U³ norm)

import Mathlib
import Definitions.Def_AlgoPFR_rd

set_option autoImplicit false

namespace AlgoPFR

namespace Supplement

noncomputable section

/-- The **Gowers cube average** of order 3 of `f : F₂ⁿ → ℝ`, p.16 of Arunachalam, Dutt, Grewal,
Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…):
`‖f‖_{U³}^8 = E_{y, x₁, x₂, x₃} ∏_{ω ∈ {0,1}³} f(y + ω₁x₁ + ω₂x₂ + ω₃x₃)`, the average over
independent uniform `y, x₁, x₂, x₃ ∈ F₂ⁿ`. -/
def cubeAvgU3 {n : ℕ} (f : Vec n → ℝ) : ℝ :=
  (∑ y : Vec n, ∑ x₁ : Vec n, ∑ x₂ : Vec n, ∑ x₃ : Vec n,
      ∏ ω : Fin 3 → Bool,
        f (y + (if ω 0 then x₁ else 0) + (if ω 1 then x₂ else 0) + (if ω 2 then x₃ else 0))) /
    (Fintype.card (Vec n) : ℝ) ^ 4

/-- The **Gowers `U³` norm** `‖f‖_{U³} = (‖f‖_{U³}^8)^{1/8}`, p.16 of arXiv:2609.20771 (sha256
60e45066…).

**Formalization Note.** For real `f` the cube average is a nonnegative number (it equals
`E_x ∑_ξ f̂_x(ξ)^4`, p.16), so the real eighth root `Real.rpow · (1/8)` is the paper's norm. -/
def gowersU3 {n : ℕ} (f : Vec n → ℝ) : ℝ :=
  cubeAvgU3 f ^ ((1 : ℝ) / 8)

end

end Supplement

end AlgoPFR


