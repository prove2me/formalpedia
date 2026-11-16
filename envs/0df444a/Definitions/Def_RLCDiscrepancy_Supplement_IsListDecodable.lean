-- Prove2me | Definitions.Def_RLCDiscrepancy_Supplement_IsListDecodable
-- name    : RLCDiscrepancy_Supplement_IsListDecodable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:47:40.387193+00:00
-- url     : https://prove2.me/theorems/c1438f6f-a276-4506-a1d0-a0af6e2d4eee
-- title:
--   $(\rho,L)$-list-decodable code
-- statement:
--   A code $C\subseteq\mathbb F_q^n$ is **$(\rho,L)$-list-decodable** if every Hamming ball of radius $\rho n$ contains at most $L$ codewords:
--   $$
--   |B_\rho(z)\cap C|\le L\qquad\text{for every } z\in\mathbb F_q^n.
--   $$
--   This is the list-decoding notion of Theorem 2.9.
--
--   **Formalization Note** A code is a finite set of vectors; a linear code enters through its set of codewords.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 2.8, p.16

import Mathlib
import Definitions.Def_RLCDiscrepancy_Supplement_hammingBall

namespace RLCDiscrepancy.Supplement

/-- **(ρ, L)-list-decodable code** (Definition 2.8). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 2.8, p.16:
"A code C ⊆ F^n_q is (ρ, L)-list-decodable if, for every z ∈ F^n_q, |B_ρ(z) ∩ C| ≤ L."

**Formalization Note.** A code is a finite set of vectors, a `Finset (Fin n → F)`; a linear code
`C` enters as `RLCDiscrepancy.codeFinset C`. -/
def IsListDecodable {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} (C : Finset (Fin n → F))
    (ρ : ℝ) (L : ℕ) : Prop :=
  ∀ z : Fin n → F, (hammingBall ρ z ∩ C).card ≤ L

end RLCDiscrepancy.Supplement


