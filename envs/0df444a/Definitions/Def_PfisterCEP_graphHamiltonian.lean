-- Prove2me | Definitions.Def_PfisterCEP_graphHamiltonian
-- name    : PfisterCEP_graphHamiltonian
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:25:59.043081+00:00
-- url     : https://prove2.me/theorems/39079b9f-1273-4de9-94b5-d4f8f67c9865
-- title:
--   Two-mode-squeezing Hamiltonian $H_G$ of a weighted graph
-- statement:
--   Let $G=(G_{np})$ be a real $N\times N$ matrix, read as the adjacency matrix of a weighted graph on the $N$ modes (diagonal entries are self-loops), and let $\hbar,\kappa$ be real. The **graph Hamiltonian** is
--
--   $$H_G=\frac{i\hbar\kappa}{2}\sum_{n=1}^N\sum_{p=1}^N G_{np}\,a_n^\dagger a_p^\dagger+\mathrm{H.c.},\qquad \mathrm{H.c.}=-\frac{i\hbar\kappa}{2}\sum_{n,p}G_{np}\,a_p a_n .$$
--
--   Each edge $\{n,p\}$ is a two-mode squeezing interaction and each self-loop a single-mode one. The Hamiltonians (1), (3) and (4) of the paper are of this form, with $G$ equal to $J-I$, a weighted loop graph, and $J$ (the all-ones matrix) respectively.
--
--   **Formalization Note** "H.c." is written out: the conjugate of $\tfrac{i\hbar\kappa}{2}G_{np}a_n^\dagger a_p^\dagger$ is $-\tfrac{i\hbar\kappa}{2}G_{np}a_pa_n$ (reversed product, conjugate coefficient, $G_{np}$ real).
-- source:
--   Pfister, Graph states and carrier-envelope phase squeezing, arXiv:quant-ph/0701104v2, Sec. b, pp.1–2, eqs. (1), (3), (4)

import Mathlib

namespace PfisterCEP

/-- **Two-mode-squeezing Hamiltonian of a weighted graph.**
O. Pfister, *Graph states and carrier-envelope phase squeezing*, arXiv:quant-ph/0701104v2, Sec. b, pp.1–2, eqs. (1), (3), (4) and "the matrix describing this system of coupled
differential equations is proportional to the adjacency matrix [1] of the graph so defined".

For a real matrix `G` (the adjacency matrix, self-loops on the diagonal),

  `H_G = (iħκ/2) ∑ₙ ∑ₚ Gₙₚ a†ₙ a†ₚ + H.c.,   H.c. = −(iħκ/2) ∑ₙ ∑ₚ Gₙₚ aₚ aₙ.`

**Formalization Note** "H.c." is spelled out: the conjugate of `(iħκ/2) Gₙₚ a†ₙa†ₚ` is
`−(iħκ/2) Gₙₚ aₚaₙ` (reversed product, conjugated coefficient, `Gₙₚ` real). `ħ`, `κ` are real.
`ad` plays `a†`. -/
noncomputable def graphHamiltonian {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ} (ħ κ : ℝ)
    (G : Matrix (Fin N) (Fin N) ℝ) (a ad : Fin N → A) : A :=
  (Complex.I * ħ * κ / 2 : ℂ) • ∑ n, ∑ p, (G n p : ℂ) • (ad n * ad p) +
    (-(Complex.I * ħ * κ / 2) : ℂ) • ∑ n, ∑ p, (G n p : ℂ) • (a p * a n)

end PfisterCEP


