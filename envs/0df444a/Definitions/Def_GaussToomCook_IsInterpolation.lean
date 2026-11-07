-- Prove2me | Definitions.Def_GaussToomCook_IsInterpolation
-- name    : GaussToomCook_IsInterpolation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:46:04.208691+00:00
-- url     : https://prove2.me/theorems/bdef589e-0d95-43ec-a313-e828c3b80b92
-- title:
--   A successful interpolation phase and its division count
-- statement:
--   Let $S$ be evaluation points for Gaussian Toom–Cook-$k$. A list of steps is a **successful interpolation phase** on $S$ if, started from the list $\mathcal W_0$ of the row vectors of $V(S)$, every step is defined and the final list $\mathcal W_N$ contains every standard basis vector:
--   $$q_j\in\mathcal W_N\qquad (j=0,\dots,2k-2).$$
--   This is the paper's description of solving $V(S)\,[q_j]_j=[Q(x,y)]_{(x,y)\in S}$ for the coefficients $q_j$ of $Q=P_1P_2$; Gaussian elimination is one such sequence.
--
--   For a property $P$ of Gaussian integers, $\mathrm{numDiv}_P$ of a list of steps is the number of its divisions (steps of type (ii)) whose divisor $\lambda$ satisfies $P$. With $P(\lambda)=(p\mid\lambda)$ it is the number of divisions by multiples of $p$.
--
--   **Formalization Note** Divisions are counted as steps, with multiplicity. A successful list may contain further steps after the last $q_j$ appears; such steps can only increase the counts.
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §9.1, p. 30 (PDF p. 32); Theorem 9.3, p. 31 (PDF p. 33)

import Mathlib
import Definitions.Def_GaussToomCook_vandMatrix
import Definitions.Def_GaussToomCook_Step

namespace GaussToomCook

/-- **A successful interpolation phase (V)**, Spiizer, Steiner, *Rational and Gaussian long integer multiplication*, manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §9.1, p. 30 (PDF 32):
"We start with the set W₀ ⊆ W containing the row vectors of V(S) … This procedure ends when the vectors
q_j, for j = 0, …, 2k − 2, have been added. That is q_j ∈ W_N for j = 0, …, 2k − 2 and some N ∈ ℤ≥0."

`IsInterpolation k S prog` holds when every step of `prog` is valid, starting from the list of rows of
`V(S)` (in the order of `S`), and every standard basis vector `q_c = Pi.single c 1` occurs in the final list.

**Formalization Note.** The program may contain further steps after the last `q_c` is reached; such
steps can only add divisions, so every count below is at least that of the shortest successful prefix. -/
def IsInterpolation (k : ℕ) (S : Fin (2 * k - 1) → GaussianInt × GaussianInt)
    (prog : List Step) : Prop :=
  ∃ W, run (List.ofFn (vandRow k S)) prog = some W ∧
    ∀ c : Fin (2 * k - 1), (Pi.single c 1 : Fin (2 * k - 1) → ℂ) ∈ W

/-- **The number of divisions whose divisor satisfies `P`**, Spiizer, Steiner, *Rational and Gaussian long integer multiplication*, manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §9.1, p. 30:
the number of steps of type (ii) in `prog` whose divisor `λ` satisfies `P`. With `P = (p ∣ ·)` this is
"the number of divisions by multiples of `p`" (Theorem 9.3).

**Formalization Note.** Steps are counted with multiplicity, as steps of the sequence. -/
noncomputable def numDiv (P : GaussianInt → Prop) (prog : List Step) : ℕ := by
  classical
  exact ((prog.filterMap Step.divisor?).filter (fun l => decide (P l))).length

end GaussToomCook


