-- Prove2me | Definitions.Def_RLCDiscrepancy_capacity
-- name    : RLCDiscrepancy_capacity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:13.825887+00:00
-- url     : https://prove2.me/theorems/87024bc6-009d-4aba-80aa-d5a96b61ceee
-- title:
--   Sup norm $\|f\|_\infty$ and capacity parameter $\beta$
-- statement:
--   For $f:\mathbb F_q^n\to\mathbb R$, the **sup norm** is $\|f\|_\infty=\max_{x\in\mathbb F_q^n}|f(x)|$, and the **capacity parameter** of $f$ is
--
--   $$
--   \beta=\frac1n\log_q\|f\|_\infty .
--   $$
--
--   For a normalized indicator $f_B$ one gets $\beta=1-\frac1n\log_q|B|$; rate $R=\beta$ is the threshold at which a code of rate $R$ meets a random translate of $B$ in one point on average, and Theorem 2.4 works at rate $\beta+\eta$.
--
--   **Formalization Note** $\log_q$ is `Real.logb q`. At $n=0$ Lean's division by zero gives $\beta=0$; the theorems using $\beta$ are vacuous there.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), §2.2.1, p.14

import Mathlib

namespace RLCDiscrepancy

/-- **Sup norm ∥f∥∞** = max over x ∈ F^n_q of |f(x)| (Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), used in §2.2.1, p.14).

**Formalization Note.** The maximum of `|f x|` over the finite, nonempty space `Fin n → F`
(nonempty for every `n`, including `n = 0`), as `Finset.sup'`. -/
noncomputable def supNorm {F : Type*} [Field F] [Fintype F] {n : ℕ} (f : (Fin n → F) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun x => |f x|

/-- **Capacity parameter β** of a normalized function. Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), §2.2.1, p.14: "For a normalized
function f, define its capacity parameter by β := (1/n) log_q ∥f∥∞."

**Formalization Note.** `Real.logb q` is log_q with q = `Fintype.card F` ≥ 2. At `n = 0`
Lean's division gives β = 0. -/
noncomputable def capacity {F : Type*} [Field F] [Fintype F] {n : ℕ} (f : (Fin n → F) → ℝ) : ℝ :=
  Real.logb (Fintype.card F) (supNorm f) / n

end RLCDiscrepancy


