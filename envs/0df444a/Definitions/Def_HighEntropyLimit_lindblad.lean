-- Prove2me | Definitions.Def_HighEntropyLimit_lindblad
-- name    : HighEntropyLimit_lindblad
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T21:53:10.070999+00:00
-- url     : https://prove2.me/theorems/cf8c0822-b3a8-413e-a8b9-b58463e26242
-- title:
--   Heisenberg-picture Lindblad generator
-- statement:
--   Let $\mathcal A$ be a $\mathbb C$-algebra of observables. For a Hamiltonian $H$ and jump channels $(\gamma_i, L_i, L_i^\dagger)$, the Heisenberg-picture Lindblad generator (Eq. 26) is
--   $$\mathcal L(X) = \frac{i}{\hbar}[H,X] + \sum_i \gamma_i\Big(L_i^\dagger X L_i - \frac12\{L_i^\dagger L_i, X\}\Big),$$
--   where $[A,B] = AB-BA$ and $\{A,B\} = AB+BA$.
--
--   **Formalization Note** The ladder operators of the paper are unbounded, so we work in an abstract `ℂ`-algebra and supply each adjoint $L_i^\dagger$ explicitly as part of its channel.
-- source:
--   Carcassi, Landini, Aidala, Classical mechanics as the high-entropy limit of quantum mechanics, arXiv:2411.00972v3 (1 Feb 2026), https://arxiv.org/abs/2411.00972, p. 9 Eq. (26)

import Mathlib

namespace HighEntropyLimit

/-- Right-hand side of the Lindblad master equation in the Heisenberg picture, Eq. (26):
`dX/dt = (i/ħ)[H, X] + ∑ᵢ γᵢ (Lᵢ† X Lᵢ - ½ {Lᵢ† Lᵢ, X})`.
Each jump channel is a triple `(γᵢ, Lᵢ, Lᵢ†)`; the adjoint `Lᵢ†` is supplied explicitly
because the ladder operators are unbounded and are modelled as elements of an abstract
`ℂ`-algebra. -/
noncomputable def lindbladHeisenberg {A : Type*} [Ring A] [Algebra ℂ A]
    (hbar : ℝ) (H : A) (jumps : List (ℝ × A × A)) (X : A) : A :=
  (Complex.I / (hbar : ℂ)) • (H * X - X * H) +
    (jumps.map fun j =>
      ((j.1 : ℂ)) • (j.2.2 * X * j.2.1 - (1 / 2 : ℂ) • (j.2.2 * j.2.1 * X + X * (j.2.2 * j.2.1)))).sum

end HighEntropyLimit


