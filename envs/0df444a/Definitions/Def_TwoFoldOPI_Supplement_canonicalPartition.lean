-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_canonicalPartition
-- name    : TwoFoldOPI_Supplement_canonicalPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:52:11.066203+00:00
-- url     : https://prove2.me/theorems/15cb7cf5-4351-449e-b67f-b42f0350aaf9
-- title:
--   The consecutive partition $S_1,\dots,S_R$ of $[n]$ of Definition 11.2
-- statement:
--   Given weights $\alpha_1,\dots,\alpha_R$, the partition of $[n]$ of Definition 11.2 puts the first $\lfloor\alpha_1n\rfloor$ symbols in $S_1$, the next $\lfloor\alpha_2n\rfloor$ in $S_2$, and so on up to $S_{R-1}$; $S_R$ holds the remaining symbols. This definition returns the class of each symbol.
--
--   It is the partition of the oracle instances $\mathcal D_\lambda$ (Theorems 11.3, 11.9).
--
--   **Formalization Note** Symbols and classes are $0$-based: class $r$ (the paper's $S_{r+1}$) is the interval $[c_{r-1},c_r)$ with $c_r=\lfloor\alpha_0n\rfloor+\dots+\lfloor\alpha_rn\rfloor$, and the last class takes the rest.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §11, Definition 11.2, p. 57

import Mathlib

namespace TwoFoldOPI

namespace Supplement

/-- **The partition of `[n]` into consecutive classes `S_1, …, S_R` of Definition 11.2.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §11, Definition 11.2, p.57: "define S_1 to consist of the first ⌊α_1 n⌋ elements of [n],
S_2 the next ⌊α_2 n⌋ elements, and so on until S_{R−1}, and then let S_R consist of the remaining
elements of [n]."

`canonicalPartition α n a` is the class of the symbol `a ∈ [n] = {0, …, n−1}`: with
`c_r = ⌊α_0 n⌋ + ⋯ + ⌊α_r n⌋`, symbol `a` is in class `#{r < R − 1 : c_r ≤ a}` (0-based), so class
`r < R − 1` is `[c_{r−1}, c_r)` and class `R − 1` holds the rest.

**Formalization Note.** Classes are 0-based (`Fin R`: the paper's `S_{r+1}` is class `r`); `R ≥ 1`
(`NeZero R`). The `min` with `R − 1` only makes the value a `Fin R` and never binds. -/
noncomputable def canonicalPartition {R : ℕ} [NeZero R] (α : Fin R → ℝ) (n : ℕ) (a : Fin n) :
    Fin R :=
  ⟨min (Finset.univ.filter fun r : Fin R =>
      r.val + 1 < R ∧ ∑ r' ∈ Finset.univ.filter (fun r' : Fin R => r' ≤ r), ⌊α r' * n⌋₊ ≤ a.val).card
    (R - 1), by have := NeZero.pos R; omega⟩

end Supplement

end TwoFoldOPI


