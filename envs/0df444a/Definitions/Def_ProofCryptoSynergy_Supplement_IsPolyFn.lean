-- Prove2me | Definitions.Def_ProofCryptoSynergy_Supplement_IsPolyFn
-- name    : ProofCryptoSynergy_Supplement_IsPolyFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:44:10.520183+00:00
-- url     : https://prove2.me/theorems/8801857a-2be7-454c-8240-c53a46d50c51
-- title:
--   Polynomial functions $n\mapsto\lfloor n^c\rfloor$, $c\ge1$
-- statement:
--   A function $p:\mathbb N\to\mathbb N$ is a **polynomial function** if there is a real constant $c\ge1$ with
--   $$p(n)=\lfloor n^c\rfloor\quad\text{for all }n.$$
--
--   The paper defines a polynomial function as $p(n)=n^c$ with $c\ge1$ a constant, and its size, gap and accuracy parameters $s,g,\varepsilon^{-1}$ are functions $\mathbb N\to\mathbb N$. This definition is used for the polynomial sizes $s,s'$, gaps $g,G$ and accuracies $\varepsilon^{-1}$ of Theorems 2, 38, 46, 56, 59, 64, 71, 72 and 74.
--
--   **Formalization Note** The floor makes the function natural-valued; since circuit sizes are natural numbers, $|C|\le\lfloor n^c\rfloor$ is the same condition as $|C|\le n^c$.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), §2.1, p.16 (PDF 18)

import Mathlib

namespace ProofCryptoSynergy.Supplement

/-- A **polynomial function** `p(n) = n^c` for a constant `c ≥ 1` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), §2.1, p.16 (PDF 18):
"A polynomial function is a function `p(n) = n^c` where `c ≥ 1` is a constant").

**Formalization Note** The paper's size, gap and accuracy parameters are functions `ℕ → ℕ`
(Definitions 21, 23, 25, 27, 73), so the polynomial is `n ↦ ⌊n^c⌋` with a real exponent `c ≥ 1`.
Circuit sizes are natural numbers, so `|C| ≤ ⌊n^c⌋` is the same condition as `|C| ≤ n^c`. -/
def IsPolyFn (p : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ n : ℕ, p n = ⌊(n : ℝ) ^ c⌋₊

end ProofCryptoSynergy.Supplement


