-- Prove2me | Definitions.Def_RLCDiscrepancy_Supplement_hammingBall
-- name    : RLCDiscrepancy_Supplement_hammingBall
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:47:08.206798+00:00
-- url     : https://prove2.me/theorems/3db6bc13-3c33-41ba-9a50-b42f1b7b3764
-- title:
--   Hamming ball $B_\rho(z)$
-- statement:
--   For a finite field $\mathbb F_q$, a radius parameter $\rho\in\mathbb R$ and a centre $z\in\mathbb F_q^n$, the **Hamming ball** is
--   $$
--   B_\rho(z)=\{\,y\in\mathbb F_q^n:\ |\{i\in[n]: y_i\neq z_i\}|\le \rho n\,\}.
--   $$
--   Its size $|B_\rho(0)|$ enters the list-decoding capacity $1-\frac1n\log_q|B_\rho(0)|$ and Theorem 2.9.
--
--   **Formalization Note** The comparison with $\rho n$ is made in $\mathbb R$, since $\rho n$ need not be an integer.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), p.3, footnote 1

import Mathlib

namespace RLCDiscrepancy.Supplement

/-- **Hamming ball B_ρ(z).** Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), p.3, footnote 1:
"B_ρ(z) consists of all y ∈ F^n_q at Hamming distance at most ρn from z, i.e., all y such that
|{i : y_i ≠ z_i}| ≤ ρn."

**Formalization Note.** F^n_q is `Fin n → F`; the comparison |{i : y_i ≠ z_i}| ≤ ρn is taken in ℝ
(ρn need not be an integer). |B_ρ(0)| is `(hammingBall ρ 0).card`. -/
noncomputable def hammingBall {F : Type*} [Fintype F] {n : ℕ} (ρ : ℝ) (z : Fin n → F) :
    Finset (Fin n → F) := by
  classical
  exact Finset.univ.filter (fun y : Fin n → F =>
    ((Finset.univ.filter (fun i => y i ≠ z i)).card : ℝ) ≤ ρ * n)

end RLCDiscrepancy.Supplement


