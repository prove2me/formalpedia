-- Prove2me | Definitions.Def_AsymSpecConn_ALength
-- name    : AsymSpecConn_ALength
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:59.637194+00:00
-- url     : https://prove2.me/theorems/767aba28-0f76-4215-ac2d-ba36a7ee5f39
-- title:
--   $\mathcal A$-decompositions, $\mathcal A$-length and asymptotic $\mathcal A$-length
-- statement:
--   Let $\mathcal A\subseteq\mathcal S\setminus\{0\}$ and $s\in\mathcal S$. An **$\mathcal A$-decomposition** of $s$ is a list $a_1,\dots,a_q$ of elements of $\mathcal A$, with $q\in\mathbb N$ and possibly with repetitions, such that $a_j\le s$ for every $j$ and $s\le a_1+\dots+a_q$. Its length is $q$.
--
--   The **$\mathcal A$-length** $L_{\mathcal A}(s)$ is the smallest length of an $\mathcal A$-decomposition of $s$, and $L_{\mathcal A}(s)=\infty$ if there is none. The **asymptotic $\mathcal A$-length** is
--   $$\widetilde L_{\mathcal A}(s)=\inf_{n\ge1}L_{\mathcal A}(s^n)^{1/n}.$$
--
--   These quantities measure how many elements of $\mathcal A$ are needed to sandwich the powers of $s$.
--
--   **Formalization Note** A list is a family $b:\mathrm{Fin}\,q\to\mathcal S$. $L_{\mathcal A}$ takes values in $\mathbb N\cup\{\infty\}$ and is an infimum there, so the empty infimum is $\infty$. $\widetilde L_{\mathcal A}$ is computed in $[0,\infty]$, and it is the infimum over $n\ge1$, not a limit.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), §2.1, p.13

import Mathlib

set_option autoImplicit false

open scoped ENNReal

namespace AsymSpecConn

variable {S : Type*} [CommSemiring S]

/-- **A-decomposition** (§2.1, p.13 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): a list
`a₁, …, a_q` of elements of `A` (possibly with repetitions, `q ∈ ℕ`, here given as
`b : Fin q → S`) with `a_j ≤ s` for every `j` and `s ≤ a₁ + ⋯ + a_q`. Its length is `q`. -/
def IsADecomposition (P : Preorder S) (A : Set S) (s : S) (q : ℕ) (b : Fin q → S) : Prop :=
  (∀ j, b j ∈ A ∧ P.le (b j) s) ∧ P.le s (∑ j, b j)

/-- **A-length** `L_A(s)` (§2.1, p.13 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): the smallest length of an
A-decomposition of `s`, and `∞` (`⊤`) if `s` has none (the infimum over the empty set in
`ℕ∞` is `⊤`). -/
noncomputable def ALength (P : Preorder S) (A : Set S) (s : S) : ℕ∞ :=
  ⨅ (q : ℕ) (b : Fin q → S) (_ : IsADecomposition P A s q b), (q : ℕ∞)

/-- **Asymptotic A-length** `L̃_A(s) := inf_{n ≥ 1} L_A(sⁿ)^{1/n}` (§2.1, p.13 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)).

**Formalization Note** Computed in `[0, ∞]` (`ℝ≥0∞`), so `L_A(sⁿ) = ∞` gives `∞^{1/n} = ∞`.
It is the infimum over `n ≥ 1`, not a limit (the limit is eq. (2), a consequence). -/
noncomputable def asymALength (P : Preorder S) (A : Set S) (s : S) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (_ : 1 ≤ n), ((ALength P A (s ^ n) : ℕ∞) : ℝ≥0∞) ^ ((1 : ℝ) / n)

end AsymSpecConn


