-- Prove2me | Definitions.Def_RouzeFranca_LearnGibbs_IsKLocal
-- name    : RouzeFranca_LearnGibbs_IsKLocal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:46:36.782756+00:00
-- url     : https://prove2.me/theorems/38d923de-b03c-457c-b8d8-d347534f3dc5
-- title:
--   $k$-local operators on $n$ qubits
-- statement:
--   An operator $A$ on $n$ qubits is **$k$-local** if there is a set $S\subseteq\{1,\dots,n\}$ of at most $k$ sites such that
--   $$
--   A=A_S\otimes I_{S^c}
--   $$
--   for some operator $A_S$ on the qubits in $S$; that is, $A$ acts nontrivially on at most $k$ qubits. Equivalently, $A$ is a linear combination of Pauli strings supported in $S$.
--
--   The observables $E_i$ defining the Gibbs family are assumed $k$-local; the sample complexity of the paper grows as $4^k$.
--
--   **Formalization Note** Stated entrywise in the computational basis: $A_{xy}=0$ unless $x$ and $y$ agree outside $S$, and when they do, $A_{xy}$ depends only on the restrictions $x|_S,y|_S$. The case $k=0$ is allowed (multiples of the identity).
-- source:
--   Rouzé, Stilck França, Learning quantum many-body systems from a few copies, arXiv:2107.03333v4, §1.3, p. 4; Theorem C.1 (Fast learning of Gibbs states), p. 26

import Mathlib
import Definitions.Def_RouzeFranca_LearnGibbs_gibbs

namespace RouzeFranca.LearnGibbs

/-- An operator `A` on `n` qubits is **`k`-local** if it acts nontrivially on at most `k` qubits:
there is a set `S` of at most `k` sites with `A = A_S ⊗ I_{Sᶜ}`.

Rouzé, Stilck França, arXiv:2107.03333v4, §1.3, p. 4, and Theorem C.1 (Fast learning of Gibbs
states), p. 26 ("a set of k-local operators").

**Formalization Note.** Stated entrywise in the computational basis: `A x y = 0` unless `x` and
`y` agree off `S`, and when they do, `A x y` depends only on the restrictions `x|_S`, `y|_S`.
Equivalently, `A` is a linear combination of Pauli strings supported in `S`. `k = 0` is allowed
(then `A` is a multiple of the identity). -/
def IsKLocal {n : ℕ} (k : ℕ) (A : Mat n) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ k ∧
    (∀ x y : QAlgorithms.Qubits n, (∃ j ∉ S, x j ≠ y j) → A x y = 0) ∧
    (∀ x y x' y' : QAlgorithms.Qubits n, (∀ j ∉ S, x j = y j) → (∀ j ∉ S, x' j = y' j) →
      (∀ j ∈ S, x j = x' j ∧ y j = y' j) → A x y = A x' y')

end RouzeFranca.LearnGibbs


