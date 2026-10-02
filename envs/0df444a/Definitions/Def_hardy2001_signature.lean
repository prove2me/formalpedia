-- Prove2me | Definitions.Def_hardy2001_signature
-- name    : hardy2001_signature
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-02T05:25:14.914996+00:00
-- url     : https://prove2.me/theorems/47a1a9c9-cf90-4004-9c06-f70cbb006514
-- title:
--   Degrees of freedom $K$ from a signature $x=(x_1,x_2,\dots)$
-- statement:
--   For a list of natural numbers $x=(x_1,\dots,x_L)$, the **signature** of a probability theory, and a dimension $N\in\mathbb N$, the number of degrees of freedom is
--
--   $$K_x(N)=Nx_1+\frac1{2!}N(N-1)x_2+\frac1{3!}N(N-1)(N-2)x_3+\cdots=\sum_{k=1}^{L}\binom Nk\,x_k .$$
--
--   Hardy counts one degree of freedom $x_1$ for each one-dimensional subspace spanned by basis states, $x_2$ further degrees of freedom for each two-dimensional subspace, $x_3$ for each three-dimensional subspace, and so on. Classical probability theory has signature $(1,0,0,\dots)$ and complex quantum theory has $(1,2,0,\dots)$.
--
--   **Formalization Note** The signature is a finite list `[x₁, …, x_L]`, and all later entries are understood to be $0$. The coefficient $\frac1{k!}N(N-1)\cdots(N-k+1)$ is written as the binomial coefficient $\binom Nk$. It is equal to it for every natural $N$, including $N<k$, where both vanish.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, p. 8, Section 5, Eq. (28)

import Mathlib

namespace HardyFiveAxioms

/-- Number of degrees of freedom `K` determined by a signature `x = (x₁, x₂, …)` for a system
of dimension `N` (Hardy 2001, Eq. (28)):
`K = N x₁ + (1/2!) N(N-1) x₂ + (1/3!) N(N-1)(N-2) x₃ + ⋯ = ∑ₖ (N choose k) xₖ`.
The signature is given as the finite list `[x₁, x₂, …, x_L]`; entries beyond `L` are zero. -/
def dofOfSignature (x : List ℕ) (N : ℕ) : ℕ :=
  ∑ i : Fin x.length, N.choose (i.val + 1) * x.get i

end HardyFiveAxioms


