-- Prove2me | Definitions.Def_FullForesight_Randomized_Coverage
-- name    : FullForesight_Randomized_Coverage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:16:03.887289+00:00
-- url     : https://prove2.me/theorems/f6606515-56ac-4025-9d34-e2fcdb6d47f9
-- title:
--   Unweighted coverage functions (Maximum Coverage, §2.1 and App. A.2)
-- statement:
--   In **Maximum Coverage** the arriving elements are sets $s_0, \dots, s_{n-1}$ of a finite universe, and the value of a selection $S \subseteq \{0, \dots, n-1\}$ is the number of universe elements it covers:
--   $$\mathrm{cov}_s(S) = \Big|\bigcup_{i \in S} s_i\Big|.$$
--   This function is nonnegative, monotone and submodular with $\mathrm{cov}_s(\emptyset) = 0$. It is unweighted: every universe element counts once (the paper removes the weights of its first construction in App. A.2).
--
--   **Formalization Note** The universe is encoded as a finite set of natural numbers (`s : Fin n → Finset ℕ`); every finite universe relabels into $\mathbb N$, so this loses no instance.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…), p. 5, §2.1; p. 21, App. A.2 (Removing the weights)

import Mathlib

/-!
# Unweighted coverage functions (Maximum Coverage)

Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, *Consistent
Submodular Maximization with Full Foresight*, STOC 2027 submission, p. 5 (§2.1), p. 21
(Appendix A.2, "Removing the weights").

The `n` arriving elements are sets `s 0, …, s (n−1)` of a finite universe (encoded as finite
sets of natural numbers), and `coverage s S = |⋃_{i ∈ S} s i|`.
-/

namespace FullForesight.Randomized

/-- The unweighted coverage function of the sets `s i ⊆ ℕ`: `S ↦ |⋃_{i ∈ S} s i|`. -/
def coverage {n : ℕ} (s : Fin n → Finset ℕ) (S : Finset (Fin n)) : ℝ :=
  ((S.biUnion s).card : ℝ)

end FullForesight.Randomized


