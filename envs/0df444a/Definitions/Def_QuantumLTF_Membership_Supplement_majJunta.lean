-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_majJunta
-- name    : QuantumLTF_Membership_Supplement_majJunta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:31:55.375821+00:00
-- url     : https://prove2.me/theorems/7554eeb5-52db-4d49-9a69-ca469a736538
-- title:
--   Majority junta $f_A$
-- statement:
--   For a hidden set $A\subseteq[n]$ and a query point $x\in\{-1,1\}^n$, identified with the set $S=\{i: x_i=1\}$, the **Majority junta** is
--   $$f_A(S)=\mathrm{MAJORITY}_{|A|}(x_A)=\begin{cases}1,&|A\cap S|\ge |A|/2,\\-1,&\text{otherwise.}\end{cases}$$
--   Ties go to $+1$, so $f_A(x)=\mathrm{sign}(\langle \mathbf 1_A,x\rangle)$ with $\mathrm{sign}(0)=+1$: learning $f_A$ from Boolean membership queries is learning an equal-weight homogeneous halfspace.
--
--   **Formalization Note** The condition is written $|A|\le 2|A\cap S|$, with no division. The function is defined for every $A$; the theorems' promises require $A\neq\emptyset$ (footnote 6).
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Definition 2.1, p. 16 (PDF p. 17); §4, p. 39 (PDF p. 40)

import Mathlib

namespace QuantumLTF.Membership.Supplement

/-- **The Majority junta `f_A`.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Definition 2.1, p. 16 (PDF p. 17), and §4, p. 39
(PDF p. 40): for a hidden set `A ⊆ [n]` and a query point `x ∈ {−1,1}ⁿ`, identified with
`S = {i : x_i = 1}`, `f_A(S) = MAJORITY_{|A|}(x_A)`, which is `1` if `|x_A| ≥ |A|/2` (the number
of `+1` entries of `x` on `A`) and `−1` otherwise.

**Formalization Note.** `|x_A| ≥ |A|/2` is written `|A| ≤ 2 |A ∩ S|` (no division); ties go to `+1`,
which is `sign(⟨1_A, x⟩)` with `sign(0) = +1` (p. 39: `f_w(x) = sign(⟨w, x⟩) = MAJORITY_{|A|}(x_A)`).
Defined for every `A`; the promises of the theorems require `A` nonempty (footnote 6). -/
def majJunta {n : ℕ} (A S : Finset (Fin n)) : ℤ :=
  if A.card ≤ 2 * (A ∩ S).card then 1 else -1

end QuantumLTF.Membership.Supplement


