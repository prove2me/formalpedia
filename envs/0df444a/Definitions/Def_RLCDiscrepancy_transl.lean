-- Prove2me | Definitions.Def_RLCDiscrepancy_transl
-- name    : RLCDiscrepancy_transl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:14.002371+00:00
-- url     : https://prove2.me/theorems/e2dae729-c49d-4582-a96e-34bf01974503
-- title:
--   Translation $f_z$
-- statement:
--   For $f:\mathbb F_q^n\to\mathbb R$ and $z\in\mathbb F_q^n$, the **translation** of $f$ by $z$ is the function
--
--   $$
--   f_z(x)=f(x+z).
--   $$
--
--   The family $\{f_z : z\in\mathbb F_q^n\}$ is the test family of Theorem 2.4. Translation preserves normalization and the sup norm.
--
--   **Formalization Note** The paper defines translation for complex-valued $f$; every function it translates is real valued, so the definition is for real $f$.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 2.3, p.14

import Mathlib

namespace RLCDiscrepancy

/-- **Translation f_z** (Definition 2.3). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 2.3, p.14: "For a function
f : F^n_q → C and a vector z ∈ F^n_q, define the translation f_z : F^n_q → C by f_z(x) = f(x + z)."

**Formalization Note.** Real-valued `f`, which is every function the paper translates. -/
def transl {F : Type*} [Field F] [Fintype F] {n : ℕ} (f : (Fin n → F) → ℝ) (z : Fin n → F) : (Fin n → F) → ℝ :=
  fun x => f (x + z)

end RLCDiscrepancy


