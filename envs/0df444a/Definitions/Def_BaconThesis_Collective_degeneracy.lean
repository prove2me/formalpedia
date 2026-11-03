-- Prove2me | Definitions.Def_BaconThesis_Collective_degeneracy
-- name    : BaconThesis_Collective_degeneracy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:10.914098+00:00
-- url     : https://prove2.me/theorems/1392411e-99b9-4e48-9f5a-fc74c395538b
-- title:
--   Degeneracy $n_J=\frac{(2J+1)\,n!}{(n/2+J+1)!\,(n/2-J)!}$
-- statement:
--   For $n$ qubits and total angular momentum $J=n/2-r$ ($0\le r\le n/2$), the number
--   $$
--   n_J=\frac{(2J+1)\,n!}{(n/2+J+1)!\,(n/2-J)!}=\frac{(n-2r+1)\,n!}{(n-r+1)!\,r!},
--   $$
--   the right-hand side using $2J+1=n-2r+1$, $n/2+J+1=n-r+1$ and $n/2-J=r$. By (8.42) it is the degeneracy of the spin-$J$ irrep of $n$ qubits. For $n=2$: $n_1=n_0=1$; for $n=3$: $n_{3/2}=1$, $n_{1/2}=2$.
--
--   **Formalization Note** Computed in $\mathbb Q$ (no truncating division); the natural-number subtractions are exact on the range $2r\le n$ where it is used.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, (8.42), §8.6, p.118 (PDF p.135)

import Mathlib

open scoped Matrix

namespace BaconThesis.Collective

/-- **The degeneracy `n_J = (2J+1) n! / ((n/2 + J + 1)! (n/2 − J)!)`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, (8.42), §8.6, p.118 (PDF p.135).

With `J = n/2 − r` (`0 ≤ r ≤ n/2`) one has `2J + 1 = n − 2r + 1`, `n/2 + J + 1 = n − r + 1` and
`n/2 − J = r`, so
`degeneracy n r = (n − 2r + 1) · n! / ((n − r + 1)! · r!)`, computed in `ℚ`.

**Formalization Note.** Rational division, so no truncation is hidden. The natural-number
subtractions `n − 2r` and `n − r` are exact on the range `2r ≤ n` where the definition is used. -/
def degeneracy (n r : ℕ) : ℚ :=
  (((n - 2 * r + 1) * n.factorial : ℕ) : ℚ) / (((n - r + 1).factorial * r.factorial : ℕ) : ℚ)

end BaconThesis.Collective


