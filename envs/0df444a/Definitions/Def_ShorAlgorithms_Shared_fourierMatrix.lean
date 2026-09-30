-- Prove2me | Definitions.Def_ShorAlgorithms_Shared_fourierMatrix
-- name    : ShorAlgorithms_Shared_fourierMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T08:56:03.627822+00:00
-- url     : https://prove2.me/theorems/e2ddc6a8-71d1-4fd6-be16-adcf493b1de4
-- title:
--   The Fourier matrix $A_q$, with $(a, c)$ entry $q^{-1/2}\exp(2\pi iac/q)$
-- statement:
--   Let $q \ge 1$ and index the basis states of a register holding a number $0 \le a < q$ by $|0\rangle, \dots, |q-1\rangle$. The **Fourier matrix** $A_q$ is the $q \times q$ complex matrix with entries
--
--   $$
--   (A_q)_{a,c} = \frac{1}{q^{1/2}} \exp(2\pi i a c / q), \qquad 0 \le a, c < q.
--   $$
--
--   Following the paper's convention that rows are input basis vectors and columns output basis vectors, $A_q$ takes $|a\rangle$ to $q^{-1/2} \sum_{c=0}^{q-1} \exp(2\pi i a c / q)\,|c\rangle$.
--
--   It serves two missions of the series: `03-order-finding` (§5, p. 1499, eqs. (5.3)–(5.4), where $A_q$ is applied to the first register of the state (5.2)) and `04-discrete-log` (§6, p. 1502, eqs. (6.2)–(6.3), where $A_q$ is applied to each of the first two registers of the state (6.1)). Both use the definition of §4, eq. (4.1), p. 1495. It is reviewed once for both.
--
--   **Formalization Note** `fourierMatrix q : Matrix (Fin q) (Fin q) ℂ`, with `a` and `c` cast through `ℕ` to `ℂ`, the normalization `((Real.sqrt q : ℝ) : ℂ)⁻¹` and the phase `Complex.exp (2 * π * I * a * c / q)` (positive sign). For `q = 0` the matrix is empty. The platform's `FastFourierTransform.dft` has the opposite sign and no normalization and is not used.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1495, §4, eq. (4.1); row/column convention p. 1489, §2; used p. 1499, §5, eqs. (5.3)–(5.4) and p. 1502, §6, eqs. (6.2)–(6.3)

import Mathlib

namespace ShorAlgorithms.Shared

/-- Shor (1997), §4, eq. (4.1), p. 1495: the Fourier matrix `A_q`, the unitary matrix on the
basis `|0⟩, …, |q-1⟩` whose `(a, c)` entry is `q^{-1/2} exp(2πiac/q)`. Rows are input basis
vectors and columns output basis vectors (§2, p. 1489), so `A_q` sends `|a⟩` to
`q^{-1/2} ∑_c exp(2πiac/q) |c⟩`. -/
noncomputable def fourierMatrix (q : ℕ) : Matrix (Fin q) (Fin q) ℂ :=
  fun a c => ((Real.sqrt q : ℝ) : ℂ)⁻¹ *
    Complex.exp (2 * Real.pi * Complex.I * ((a : ℕ) : ℂ) * ((c : ℕ) : ℂ) / (q : ℂ))

end ShorAlgorithms.Shared


