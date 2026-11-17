-- Prove2me | Definitions.Def_SubspaceConv_Supplement_incidence
-- name    : SubspaceConv_Supplement_incidence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:45:20.150661+00:00
-- url     : https://prove2.me/theorems/4f14718e-08ee-4c81-8144-ca2cba48d13d
-- title:
--   Incidence transform $I_n^{a,b}$ and its transpose
-- statement:
--   Let $R$ be a commutative ring and $0 \le a \le b \le n$. The **incidence transform** sends a table $f : \mathrm{Gr}_q(n,a) \to R$ to the table on $\mathrm{Gr}_q(n,b)$ given by
--
--   $$(I_n^{a,b} f)(W) = \sum_{U \le W,\ \dim U = a} f(U), \qquad W \in \mathrm{Gr}_q(n,b).$$
--
--   Its **transpose** sends $g : \mathrm{Gr}_q(n,b) \to R$ to $(I^{\mathsf T} g)(U) = \sum_{W \ge U,\ \dim W = b} g(W)$ for $U \in \mathrm{Gr}_q(n,a)$.
--
--   For $a = 1$, $b = n-1$ this sums weights on projective points over every hyperplane. The transform is the object of Theorem 2 (fast algorithm) and Theorem 7 (matching lower bound).
--
--   **Formalization Note** The formulas are written for all $a, b$; the theorems impose $a \le b \le n$.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4e583122875209a3e25ee95aa3a7af933526e165d47c274634e604ab2), §1.1 "Low-Rank Summation", p.2 (PDF p.3)

import Mathlib
import Definitions.Def_SubspaceConv_Supplement_Gr

set_option autoImplicit false

open Classical

namespace SubspaceConv.Supplement

variable {F : Type*} [Field F] [Fintype F] {n : ℕ}

/-- The **incidence transform** `I_n^{a,b}` (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §1.1 "Low-Rank Summation", p.2 (PDF p.3)):
for `f : Gr_q(n, a) → R` and `W ∈ Gr_q(n, b)`,
`(I_n^{a,b} f)(W) = ∑_{U ≤ W, dim U = a} f(U)`.

**Formalization Note** The paper defines it for `0 ≤ a ≤ b ≤ n`; the formula is written for all
`a, b` (the theorems impose `a ≤ b ≤ n`). Values lie in any commutative ring `A`. -/
noncomputable def incidence {A : Type*} [CommRing A] (a b : ℕ) (f : Gr F n a → A)
    (W : Gr F n b) : A :=
  ∑ U ∈ Finset.univ.filter (fun U : Gr F n a => U.1 ≤ W.1), f U

/-- The **transpose** of the incidence transform (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), p.2 (PDF p.3): "The transpose sends
weights on b-dimensional subspaces to sums over those containing each a-dimensional subspace"):
for `g : Gr_q(n, b) → R` and `U ∈ Gr_q(n, a)`, `(I^T g)(U) = ∑_{W ≥ U, dim W = b} g(W)`. -/
noncomputable def incidenceT {A : Type*} [CommRing A] (a b : ℕ) (g : Gr F n b → A)
    (U : Gr F n a) : A :=
  ∑ W ∈ Finset.univ.filter (fun W : Gr F n b => U.1 ≤ W.1), g W

end SubspaceConv.Supplement


