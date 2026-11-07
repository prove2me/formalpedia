-- Prove2me | Definitions.Def_DynSort_cost
-- name    : DynSort_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:18.56596+00:00
-- url     : https://prove2.me/theorems/ce1e5f0b-a9b5-4344-b486-c812cfd964df
-- title:
--   Cost $\mathrm{cost}(S)$ and offline optimum $\mathrm{OPT}(S)$ of a sequence
-- statement:
--   Let $S=(x_1,\dots,x_k)$ be a finite sequence of reals, the elements stored in an array read from left to right with empty cells ignored. Its **cost** is the sum of the absolute differences of consecutive elements, and its **offline optimum** is the cost of the sorted arrangement:
--   $$\mathrm{cost}(S)=\sum_{j=1}^{k-1}|x_{j+1}-x_j|,\qquad \mathrm{OPT}(S)=\max S-\min S .$$
--   Both are $0$ for a sequence with at most one element.
--
--   These are the two quantities compared by the competitive ratio of an online sorting algorithm.
--
--   **Formalization Note** A sequence is a list of reals; the empty list has $\mathrm{OPT}=0$.
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), §2, p.6 (PDF p.8)

import Mathlib

namespace DynSort

/-! # The cost of a sequence and the offline optimum

Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §2, p.6 (PDF p.8).

For the stored elements `S = (x₁, …, x_k)`, read left to right ignoring empty cells,
`cost(S) = ∑_{j=1}^{k-1} |x_{j+1} − x_j|` and `OPT(S) = max S − min S`; both are zero for a
sequence with at most one element.

**Formalization Note.** A sequence is a `List ℝ`. `cost` sums `|x_{j+1} − x_j|` over the adjacent
pairs `S.zip S.tail`, so it is `0` on `[]` and on singletons. `opt S` is `S.max? − S.min?`, read as
`0 − 0` on `[]` and `x − x = 0` on `[x]`, exactly the paper's convention.
-/

/-- **The cost of a sequence** (§2, p.6): the sum of absolute differences of consecutive
elements, `cost(S) = ∑_{j=1}^{k−1} |x_{j+1} − x_j|`, and `0` for at most one element. -/
noncomputable def cost (S : List ℝ) : ℝ :=
  ((S.zip S.tail).map (fun p => |p.2 - p.1|)).sum

/-- **The offline optimum** (§2, p.6): `OPT(S) = max S − min S`, and `0` on the empty sequence. -/
noncomputable def opt (S : List ℝ) : ℝ :=
  S.max?.getD 0 - S.min?.getD 0

end DynSort


