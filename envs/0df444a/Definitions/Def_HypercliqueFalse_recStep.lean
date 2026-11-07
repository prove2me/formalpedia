-- Prove2me | Definitions.Def_HypercliqueFalse_recStep
-- name    : HypercliqueFalse_recStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:32:05.029603+00:00
-- url     : https://prove2.me/theorems/bf36e090-2270-41a8-b2c4-798378825297
-- title:
--   Computing the children of Lemma 4.1 (word RAM problem)
-- statement:
--   The problem of **computing the children of the recursive step** on the published word RAM, for a fixed $h$ and $q$ and one of the two reductions.
--
--   1. First reduction: an instance at scale $s$ consists of dimensions $N', M, a, b, c, n$ with $N'q, M, a, b, c, n \le s$ and arrays of $T_h$ of size $(N'q, M, a, b, c)$. The input is $N'$ followed by the encoding `tInput`. After it, the machine must write the encodings of the main children $(\bar A^g, \dots, \bar E^g)$ for $g = 1,\dots,q$, followed by those of the correction children $(\bar A^{ij},\dots,\bar E^{ij})$ for the pairs $i < j$ in lexicographic order.
--   2. Second reduction: the same for arrays of size $(N, M'q, a, b, c)$, the input $M'$ followed by `tInput`, and the children of the second reduction.
--
--   This is the computational content of "we can compute in linear time new arrays" in Lemma 4.1.
--
--   **Formalization Note** The dimension bounds by the scale make the input size polynomial in $s$, so that addresses fit into the $\Theta(\log s)$-bit words. The quotient $N'$ (resp. $M'$) is a cell of the input because the published machine has no division or shift: when the arrays are empty (say $M = 0$) `tInput` is only its header, and no add/subtract/multiply program gets $N'$ from $N'q$ in a constant number of steps, yet $N'$ is the first cell of the output.
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Lemma 4.1, p.10

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_HypercliqueFalse_tInput
import Definitions.Def_HypercliqueFalse_firstMain
import Definitions.Def_HypercliqueFalse_firstCorr
import Definitions.Def_HypercliqueFalse_secondMain
import Definitions.Def_HypercliqueFalse_secondCorr

set_option autoImplicit false

open TrulySubcubicAPSP

namespace HypercliqueFalse

/-- **Computing the children of Lemma 4.1**, as a problem of the published word RAM. Fischer, *The
Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Lemma 4.1,
p.10: "we can compute in linear time new arrays Ā^g, B̄^g, C̄^g, D̄^g, Ē^g for all g ∈ [q] and Ā^{ij},
B̄^{ij}, C̄^{ij}, D̄^{ij}, Ē^{ij} for all 1 ≤ i < j ≤ q".

`recStep h q true` is the first reduction: an instance at scale `s` is
`⟨N', M, a, b, c, n, _, T⟩` with arrays `T` of size `(N'q, M, a, b, c)` and `N'q, M, a, b, c, n ≤ s`;
the input is `N'` followed by `tInput T`, and the program must write after it the encodings `tInput` of the main children
`firstMain T g` for `g = 0, …, q − 1`, followed by those of the correction children
`firstCorr T i j` for the pairs `i < j` in lexicographic order. `recStep h q false` is the same for
the second reduction (arrays of size `(N, M'q, a, b, c)`, input `M'` followed by `tInput T`,
children `secondMain`, `secondCorr`).

**Formalization Note.** The dimension bounds by the scale `s` make the input size polynomial in
`s`, so that addresses fit in the `Θ(log s)`-bit words of `SolvedWithin`. The quotient `N'` (resp.
`M'`) is a cell of the input because the published machine has no division or shift: when the arrays
are empty (say `M = 0`) `tInput T` is only its header, and no add/subtract/multiply program gets
`N'` from `N'q` in a constant number of steps, yet `N'` is the first cell of the output. -/
def recStep (h q : ℕ) : Bool → Problem
  | true =>
    { Instance := fun s => Σ' (N' M a b c n : ℕ)
        (_ : N' * q ≤ s ∧ M ≤ s ∧ a ≤ s ∧ b ≤ s ∧ c ≤ s ∧ n ≤ s), TData h (N' * q) M a b c n
      input := fun x => (x.1 : ℤ) :: tInput x.2.2.2.2.2.2.2
      output := fun x f =>
        let T := x.2.2.2.2.2.2.2
        let L := (List.finRange q).flatMap (fun g => tInput (firstMain T g)) ++
          (List.finRange q).flatMap fun i =>
            ((List.finRange q).filter fun j => i < j).flatMap fun j => tInput (firstCorr T i j)
        (List.range L.length).map f = L }
  | false =>
    { Instance := fun s => Σ' (N M' a b c n : ℕ)
        (_ : N ≤ s ∧ M' * q ≤ s ∧ a ≤ s ∧ b ≤ s ∧ c ≤ s ∧ n ≤ s), TData h N (M' * q) a b c n
      input := fun x => (x.2.1 : ℤ) :: tInput x.2.2.2.2.2.2.2
      output := fun x f =>
        let T := x.2.2.2.2.2.2.2
        let L := (List.finRange q).flatMap (fun g => tInput (secondMain T g)) ++
          (List.finRange q).flatMap fun i =>
            ((List.finRange q).filter fun j => i < j).flatMap fun j => tInput (secondCorr T i j)
        (List.range L.length).map f = L }

end HypercliqueFalse


