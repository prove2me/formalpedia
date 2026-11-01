-- Prove2me | Definitions.Def_PfisterCEP_H3
-- name    : PfisterCEP_H3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:05.477333+00:00
-- url     : https://prove2.me/theorems/1243dc1a-64a6-49cb-87f0-8c802dc11da6
-- title:
--   The Hamiltonian $H_3$ of eq. (4)
-- statement:
--   For modes $a_n,a_n^\dagger$ ($n=1,\dots,N$) and real $\hbar,\kappa$, the Hamiltonian of eq. (4) is
--
--   $$H_3=i\hbar\kappa\Big(\sum_{n<p}a_n^\dagger a_p^\dagger+\sum_n\frac{a_n^{\dagger 2}}{2}\Big)+\mathrm{H.c.}$$
--
--   It is the GHZ Hamiltonian (1) with self-loops of the same sign added at every vertex (Fig. 3), and describes a degenerate OPO pumped by a mode-locked pulse train (Sec. c).
--
--   **Formalization Note** The definition is the printed form, with H.c. written out as $-i\hbar\kappa\big(\sum_{n<p}a_pa_n+\sum_n a_n^2/2\big)$. Its identification with the graph Hamiltonian of the all-ones matrix is a separate theorem.
-- source:
--   Pfister, Graph states and carrier-envelope phase squeezing, arXiv:quant-ph/0701104v2, Sec. b, p.2, right column, eq. (4)

import Mathlib

namespace PfisterCEP

/-- **The Hamiltonian `H₃` of eq. (4).**
O. Pfister, *Graph states and carrier-envelope phase squeezing*, arXiv:quant-ph/0701104v2, Sec. b, p.2, right column, eq. (4):

  `H₃ = iħκ ( ∑_{n<p} a†ₙ a†ₚ + ∑ₙ a†ₙ²/2 ) + H.c.`

**Formalization Note** Stated exactly as printed; "H.c." is spelled out as
`−iħκ ( ∑_{n<p} aₚ aₙ + ∑ₙ aₙ²/2 )` (reversed products, conjugated coefficient). `ħ`, `κ`
real; `ad` plays `a†`. The identification with the graph Hamiltonian of the all-ones matrix is a
separate statement (`H3_eq_graphHamiltonian`). -/
noncomputable def H3 {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ} (ħ κ : ℝ) (a ad : Fin N → A) : A :=
  (Complex.I * ħ * κ : ℂ) • (∑ n, ∑ p ∈ Finset.univ.filter (n < ·), ad n * ad p +
      ∑ n, (1 / 2 : ℂ) • (ad n * ad n)) +
    (-(Complex.I * ħ * κ) : ℂ) • (∑ n, ∑ p ∈ Finset.univ.filter (n < ·), a p * a n +
      ∑ n, (1 / 2 : ℂ) • (a n * a n))

end PfisterCEP


