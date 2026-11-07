-- Prove2me | Definitions.Def_HypercliqueFalse_tInput
-- name    : HypercliqueFalse_tInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:52.366603+00:00
-- url     : https://prove2.me/theorems/4f3902e9-eb8c-4ddd-b686-d0bb0d906a9f
-- title:
--   The input encoding of the arrays of $T_h$
-- statement:
--   The **input encoding** of arrays $A, B, C, D, E$ of size $(N, M, a, b, c)$ is the list of integers consisting of the header $N, M, a, b, c, n$ followed by all entries of $A$, then $B$, $C$, $D$, and then $E_5, \dots, E_{h+1}$. Each array is listed in lexicographic order of its arguments as they appear in `TData` (the variables first, then the matrix indices).
--
--   Its length is the **input size** of Lemma 4.1 ("we can compute in linear time"); it is also the input of the evaluation problem of Lemma 4.3 and, after the quotient $N/q$ or $M/q$, of the recursive step.
--
--   **Formalization Note** Tuples $(x_5,\dots)$ are listed in the mixed-radix order of `finFunctionFinEquiv` (coordinate $0$ least significant).
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 4, pp.9–10; Lemma 4.1, p.10

import Mathlib
import Definitions.Def_HypercliqueFalse_TData

set_option autoImplicit false

namespace HypercliqueFalse

/-- **The fixed input encoding of the arrays of `T_h`.** Fischer, *The Hyperclique Hypothesis is
False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 4, pp.9–10 (the arrays) and
Lemma 4.1, p.10 ("in linear time"): the list of integers a word-RAM program reads.

The list is the header `N, M, a, b, c, n` followed by all entries of `A`, `B`, `C`, `D` and then
`E₅, …, E_{h+1}`, each array in lexicographic order of its arguments as they appear in `TData`
(variables first, then the matrix indices).

**Formalization Note.** Tuples `(x₅, …)` are listed in the order of `finFunctionFinEquiv.symm`
(coordinate `0` least significant). The length of the list is the input size of Lemma 4.1. -/
def tInput {h N M a b c n : ℕ} (T : TData h N M a b c n) : List ℤ :=
  let R := List.ofFn fun r : Fin (n ^ (h - 3)) => (finFunctionFinEquiv.symm r : Fin (h - 3) → Fin n)
  let R' := List.ofFn fun r : Fin (n ^ (h - 4)) => (finFunctionFinEquiv.symm r : Fin (h - 4) → Fin n)
  [(N : ℤ), M, a, b, c, n] ++
  ((List.finRange M).flatMap fun x₁ => (List.finRange N).flatMap fun x₂ =>
    (List.finRange N).flatMap fun x₃ => R.flatMap fun r =>
    (List.finRange a).flatMap fun α => (List.finRange c).map fun κ => T.A x₁ x₂ x₃ r α κ) ++
  ((List.finRange M).flatMap fun x₁ => (List.finRange N).flatMap fun x₂ =>
    (List.finRange M).flatMap fun x₄ => R.flatMap fun r =>
    (List.finRange c).flatMap fun κ => (List.finRange b).map fun β => T.B x₁ x₂ x₄ r κ β) ++
  ((List.finRange M).flatMap fun x₁ => (List.finRange N).flatMap fun x₃ =>
    (List.finRange M).flatMap fun x₄ => R.flatMap fun r =>
    (List.finRange b).flatMap fun β => (List.finRange c).map fun γ => T.C x₁ x₃ x₄ r β γ) ++
  ((List.finRange N).flatMap fun x₂ => (List.finRange N).flatMap fun x₃ =>
    (List.finRange M).flatMap fun x₄ => R.flatMap fun r =>
    (List.finRange c).flatMap fun γ => (List.finRange a).map fun α => T.D x₂ x₃ x₄ r γ α) ++
  ((List.finRange (h - 3)).flatMap fun ℓ =>
    (List.finRange M).flatMap fun x₁ => (List.finRange N).flatMap fun x₂ =>
    (List.finRange N).flatMap fun x₃ => (List.finRange M).flatMap fun x₄ => R'.flatMap fun r =>
    (List.finRange a).flatMap fun α => (List.finRange b).flatMap fun β =>
    (List.finRange c).map fun γ => T.E ℓ x₁ x₂ x₃ x₄ r α β γ)

end HypercliqueFalse


