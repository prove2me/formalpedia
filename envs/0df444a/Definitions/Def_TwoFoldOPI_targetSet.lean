-- Prove2me | Definitions.Def_TwoFoldOPI_targetSet
-- name    : TwoFoldOPI_targetSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:21.847201+00:00
-- url     : https://prove2.me/theorems/25a39ce9-85e1-4c0f-ad70-f4443710be58
-- title:
--   The target set $A=\prod_i(\mathbb F_q\setminus\{\beta_i\})$
-- statement:
--   For forbidden values $\beta_1,\dots,\beta_m\in\mathbb F_q$, let $A_i=\mathbb F_q\setminus\{\beta_i\}$ and
--   $$A=A_1\times\cdots\times A_m=\{x\in\mathbb F_q^m: x_i\neq\beta_i\ \text{for every } i\}.$$
--   Theorem 7.4 finds a codeword of $C$ in $A$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7, Definition 7.1, p. 37

import Mathlib

namespace TwoFoldOPI

/-- **The target set `A = ∏ᵢ (F_q ∖ {βᵢ})`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7, Definition 7.1, p.37: "let β_1, …, β_m ∈ F_q be arbitrary and let A_i = F_q∖{β_i}. Let
A = A_1 × ⋯ × A_m ⊆ F_q^m". -/
def targetSet {K : Type*} [Fintype K] [DecidableEq K] {m : ℕ} (β : Fin m → K) :
    Finset (Fin m → K) :=
  Finset.univ.filter fun x => ∀ i, x i ≠ β i

end TwoFoldOPI


