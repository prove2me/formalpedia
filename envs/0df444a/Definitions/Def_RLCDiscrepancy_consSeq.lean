-- Prove2me | Definitions.Def_RLCDiscrepancy_consSeq
-- name    : RLCDiscrepancy_consSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:15.196794+00:00
-- url     : https://prove2.me/theorems/64a0c949-998a-427a-954f-1350324f0407
-- title:
--   Construction sequence $C_0,\dots,C_k$
-- statement:
--   Given vectors $u_1,\dots,u_k\in\mathbb F_q^n$, the **construction sequence** is $C_0=\{0\}$ and $C_i=C_{i-1}+\operatorname{span}\{u_i\}$, i.e.
--
--   $$
--   C_i=\operatorname{span}\{u_1,\dots,u_i\},\qquad 0\le i\le k .
--   $$
--
--   When $u_1,\dots,u_k$ are independent and uniform it is a **random construction sequence**, and $C_k$ is a random linear code (the image of the matrix with columns $u_1,\dots,u_k$).
--
--   **Formalization Note** The vectors are `u : Fin k → (Fin n → F)`, 0-indexed; `consSeq u i` is the span of the `u j` with `j < i`, and equals $C_k$ for $i\ge k$.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 4.1, p.25

import Mathlib

namespace RLCDiscrepancy

/-- **Construction sequence** C_0, …, C_k (Definition 4.1). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 4.1, p.25:
"A construction sequence is a sequence of codes C_0, …, C_k ⊆ F^n_q where
C_i = C_{i−1} + span{u_i} for some vector u_i ∈ F^n_q. When u_1, …, u_k are chosen uniformly at
random, we say that this is a random construction sequence".

**Formalization Note.** With C_0 = {0} (pp.8, 20), C_i = span{u_1, …, u_i}. The vectors are
`u : Fin k → (Fin n → F)` (0-indexed, so the paper's u_j is `u ⟨j−1, _⟩`), and `consSeq u i` is
the span of the `u j` with `j < i`. For `i ≥ k` it is C_k. -/
noncomputable def consSeq {F : Type*} [Field F] [Fintype F] {n k : ℕ} (u : Fin k → Fin n → F) (i : ℕ) :
    Submodule F (Fin n → F) :=
  Submodule.span F (u '' {j | (j : ℕ) < i})

end RLCDiscrepancy


